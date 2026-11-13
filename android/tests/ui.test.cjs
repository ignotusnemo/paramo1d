/* Browser checks exercise the Android view contract. Native cryptography is tested in Rust. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const http = require('node:http');
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');

const assets = path.resolve(__dirname, '../app/src/main/assets');
const output = path.resolve(__dirname, '../../target/courier-preview');
const server = http.createServer(async (request, response) => {
  try {
    const filename = path.join(assets, request.url === '/' ? 'index.html' : request.url.split('?')[0]);
    if (!filename.startsWith(assets + path.sep)) throw new Error('Invalid path');
    const type = { '.html': 'text/html', '.css': 'text/css', '.js': 'application/javascript', '.svg': 'image/svg+xml', '.woff2': 'font/woff2' }[path.extname(filename)];
    response.setHeader('Content-Type', type || 'application/octet-stream'); response.end(await fs.readFile(filename));
  } catch { response.writeHead(404); response.end(); }
});

async function bridge(page) {
  await page.addInitScript(() => {
    const now = Date.now();
    const alice = { id: '11'.repeat(32), box_key: 'aa'.repeat(32), name: 'Alice', address: 'o1fixture-alice' };
    const bob = { id: '22'.repeat(32), box_key: 'bb'.repeat(32), name: 'Bob', address: 'o1fixture-bob' };
    const txid = 'ab'.repeat(32);
    const state = { profile: alice, invite: 'paramo1d://contact/test-view-fixture', contacts: [bob], rooms: ['parano1d'], settings: { relays: ['https://relay.example'], rpc: 'https://node.example/rpc' }, chain: {}, security: { available: true, enabled: true }, paranoid_mode:true,background_delivery:true,delivery_running:true,backup_saved: false, connection: { online: true }, receipts: [], observations: [], messages: [] };
    state.messages.push({ id: 'hello', chat: 'g:parano1d', sender: bob, message: { type: 'text', text: 'Good morning, everyone. Who is building today?' }, created_ms: now - 180000, status: 'received' });
    state.messages.push({ id: 'payment', chat: 'g:parano1d', sender: alice, message: { type: 'transaction', intent_hex: '00' }, payment: { txid }, created_ms: now - 120000, status: 'sent' });
    state.observations.push({ id: 'status', chat: 'g:parano1d', sender: bob, message: { type: 'relay_update', txid, stage: 'included', receipt_hex: '00' }, created_ms: now - 60000 });
    state.messages.push({ id: 'invoice', chat: 'd:' + bob.id, sender: bob, message: { type: 'invoice', invoice_id: '01'.repeat(16), address: bob.address, amount: '2.500000', memo: 'Coffee and a good conversation.' }, created_ms: now - 50000, status: 'received' });
    window.testState = state; window.testCalls = [];
    window.Paramo1d = { request(id, encoded) {
      const request = JSON.parse(encoded); window.testCalls.push(request);
      if (request.op === 'send' && window.testSendStorageFull) { queueMicrotask(() => window.paramo1dReply(id, { ok: false, error: 'App storage is full. Open Settings to clear local chat history.' })); return; }
      let result = state;
      if (request.op === 'sync' && window.testDeferSync) { window.testSyncRequest = id; return; }
      if (request.op === 'theme') state.settings.theme = request.value;
      if (request.op === 'create_identity') state.profile = { ...alice, name: request.name };
      if (request.op === 'app_lock') state.security.enabled = request.enabled;
      if (request.op === 'allow_screenshots') state.allow_screenshots = request.enabled;
      if (request.op === 'scan_qr') {
        result = { opening: true };
        if (window.testScanResult) queueMicrotask(() => window.paramo1dScanResult({ ...window.testScanResult, scan_id: request.scan_id }));
      }
      if (request.op === 'paranoid_mode') state.paranoid_mode=request.enabled;
      if (request.op === 'mark_read') { state.unread = state.unread || {}; state.unread[request.chat] = 0; }
      if (request.op === 'chat_storage') {
        if (window.testStorageError) { queueMicrotask(() => window.paramo1dReply(id, { ok: false, error: 'Storage unavailable' })); return; }
        const scopes = new Map([['g:parano1d', { id: 'g:parano1d', name: 'Community', messages: 0, clearable: 0, queued: 0, bytes: 0, clearable_bytes: 0 }]]);
        for (const message of state.messages) {
          if (!scopes.has(message.chat)) scopes.set(message.chat, { id: message.chat, name: state.contacts.find(c => 'd:' + c.id === message.chat)?.name || message.sender.name, messages: 0, clearable: 0, queued: 0, bytes: 0, clearable_bytes: 0 });
          const row = scopes.get(message.chat); row.messages++; row.bytes += 1024;
          if (message.status === 'queued') row.queued++; else { row.clearable++; row.clearable_bytes += 1024; }
        }
        result = { messages: state.messages.length, message_limit: 5000, used_bytes: state.messages.length * 1024, byte_limit: 24 * 1024 * 1024, full: !!state.storage_full, chats: [...scopes.values()] };
      }
      if (request.op === 'clear_history') {
        state.messages = state.messages.filter(message => !request.chats.includes(message.chat) || message.status === 'queued');
        for (const scope of request.chats) if (state.unread) delete state.unread[scope];
        state.storage_full = false;
      }
      if (request.op === 'delete_conversation') {
        if (window.testDeleteError) { queueMicrotask(() => window.paramo1dReply(id, { ok: false, error: 'Chat could not be deleted. Try again.' })); return; }
        state.messages = state.messages.filter(message => message.chat !== request.chat);
        state.contacts = state.contacts.filter(contact => 'd:' + contact.id !== request.chat);
        if (state.drafts) delete state.drafts[request.chat];
        if (state.unread) delete state.unread[request.chat];
        state.storage_full = false;
      }
      if (request.op === 'protection_enable') { state.protection = { enabled: true, connected: true }; state.background_delivery = true; }
      if (request.op === 'protection_disable') state.protection = { enabled: false };
      if (request.op === 'nearby_start') state.nearby = { enabled: true, peers: [], devices: [] };
      if (request.op === 'nearby_stop') state.nearby = { enabled: false, peers: [] };
      if (request.op === 'background_enable') state.background_delivery = true;
      if (request.op === 'background_disable') state.background_delivery = false;
      if (request.op === 'send') state.messages.push({ id: 'sent-' + window.testCalls.length, chat: request.chat, sender: alice, message: request.message, created_ms: Date.now(), status: 'queued' });
      if (request.op === 'save_draft') {
        if (request.chat.startsWith('d:') && !state.contacts.some(contact => 'd:' + contact.id === request.chat)) { queueMicrotask(() => window.paramo1dReply(id, { ok: false, error: 'Add this contact first' })); return; }
        state.drafts ||= {};
        if (request.text || request.reply_to) state.drafts[request.chat] = { text: request.text, reply_to: request.reply_to };
        else delete state.drafts[request.chat];
        result = { saved: true };
      }
      if (request.op === 'preview_contact') {
        const contact = window.testContactLinks?.[request.uri];
        if (!contact) { queueMicrotask(() => window.paramo1dReply(id, { ok: false, error: 'Invalid contact signature' })); return; }
        result = { contact };
      }
      if (request.op === 'import_contact') {
        const contact = window.testContactLinks?.[request.uri];
        if (contact && !state.contacts.some(c => c.id === contact.id)) state.contacts.push(contact);
      }
      if (request.op === 'broadcast_preview') result = { txid: request.txid || window.testBroadcastTxid || txid, outputs: [{ address: bob.address, amount_micronoid: '10000' }], fee: '0.009000' };
      if (request.op === 'broadcast_send' && window.testBroadcastError) {
        const message = state.messages.find(m => m.id === request.message_id);
        if (message) message.broadcast_error = window.testBroadcastError;
        queueMicrotask(() => { window.paramo1dUpdate(JSON.parse(JSON.stringify(state))); window.paramo1dReply(id, { ok: false, error: window.testBroadcastError }); }); return;
      }
      if (request.op === 'receipt_verify') {
        const receipt = { verified: true, txid, height: 300000, confirmations: 4, finalized: false, message_id: request.message_id };
        state.receipts.push(receipt); result = { state, receipt };
      }
      if (request.op === 'payment_preview') result = { review_id: 'review-fixture', to: request.address, amount: request.amount, fee: '0.010000', total: '2.510000', height: 300000, valid_through_height: 300096, using_saved_state: request.use_cached };
      if (request.op === 'payment_send') result = { state, txid, submitted: false };
      queueMicrotask(() => window.paramo1dReply(id, { ok: true, result: JSON.parse(JSON.stringify(result)) }));
    } };
  });
}

async function main() {
  await fs.mkdir(output, { recursive: true });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  const browser = await chromium.launch({ executablePath: process.env.CHROME || '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox'] });
  const errors = [];
  try {
    const page = await browser.newPage({ viewport: { width: 390, height: 844 }, deviceScaleFactor: 1 });
    page.on('pageerror', (error) => errors.push(error.message)); await bridge(page);
    await page.goto(`http://127.0.0.1:${server.address().port}/`);
    await page.getByText('Payment found · ready to check', { exact: true }).waitFor();
    assert.equal(await page.locator('.brand-logo').first().evaluate((img) => img.complete && img.naturalWidth > 0), true, 'The brand mark must load');
    assert(await page.locator('#settings-button use').evaluate((use) => use.getBBox().width > 0), 'Navigation SVG symbols must render');
    assert.equal(await page.locator('.transaction-card.verified').count(), 0, 'A helper report must not become local verification');
    assert.equal(await page.locator('body').evaluate((body) => body.scrollWidth <= window.innerWidth), true, 'Mobile view must fit the viewport');
    await page.screenshot({ path: path.join(output, 'community-mobile.png') });
    await page.getByRole('button', { name: 'Check payment' }).click();
    await page.getByText('Payment verified.', { exact: true }).waitFor();
    assert.equal(await page.locator('.transaction-card.verified').count(), 1);
    assert.equal(await page.evaluate(() => window.testCalls.find((r) => r.op === 'receipt_verify').expected_txid), 'ab'.repeat(32));
    await page.locator('#close-modal').click();
    await page.locator('#compose').fill('A queued community message.'); await page.getByRole('button', { name: 'Send message', exact: true }).click();
    await page.locator('#messages').getByText('A queued community message.', { exact: true }).waitFor();
    await page.locator('.mobile-tabs [data-tab="direct"]').click(); await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
    await page.locator('.payment-card .amount').filter({ hasText: '2.500000' }).waitFor(); await page.screenshot({ path: path.join(output, 'direct-mobile.png') });
    await page.getByRole('button', { name: 'Review payment' }).click(); await page.getByRole('button', { name: 'Send payment' }).click();
    await page.getByText('Payment saved on this phone', { exact: true }).waitFor();
    assert(!await page.locator('#modal').innerText().then((s) => s.includes('Payment submitted')), 'A prepared packet must not be reported as submitted');
    await page.locator('#close-modal').click(); await page.locator('#back-button').click(); await page.locator('.mobile-tabs [data-tab="wallet"]').click();
    assert.equal(await page.locator('#balance').innerText(), '—', 'An unsynchronized balance must remain unknown');
    await page.screenshot({ path: path.join(output, 'wallet-mobile.png') });
    await page.evaluate(() => {
      const peer = window.testState.contacts[0];
      window.testState.messages.push({ id: 'wallet-unread', chat: 'd:' + peer.id, sender: peer, message: { type: 'text', text: 'A message while the wallet is open.' }, created_ms: Date.now(), status: 'received' });
      window.testState.unread = { ['d:' + peer.id]: 2 };
      window.paramo1dUpdate(JSON.parse(JSON.stringify(window.testState)));
    });
    await page.locator('.mobile-tabs [data-tab="direct"] .tab-unread').getByText('2', { exact: true }).waitFor();
    assert.equal(await page.evaluate(() => window.testCalls.filter(r => r.op === 'view_chat').at(-1).chat), '', 'A wallet screen must not suppress a private-message notification');
    assert.equal(await page.evaluate(() => window.testCalls.some(r => r.op === 'mark_read' && r.message_id === 'wallet-unread')), false);
    await page.locator('.mobile-tabs [data-tab="direct"]').click();
    await page.locator('.conversation-row').filter({ hasText: 'Bob' }).getByText('2', { exact: true }).waitFor();
    await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
    await page.waitForFunction(() => window.testCalls.some(r => r.op === 'mark_read' && r.message_id === 'wallet-unread'));
    await page.getByRole('button', { name: 'Settings', exact: true }).click();
    await page.evaluate(() => {
      const peer = window.testState.contacts[0];
      window.testState.messages.push({ id: 'settings-unread', chat: 'd:' + peer.id, sender: peer, message: { type: 'text', text: 'A message behind settings.' }, created_ms: Date.now(), status: 'received' });
      window.testState.unread = { ['d:' + peer.id]: 1 };
      window.paramo1dUpdate(JSON.parse(JSON.stringify(window.testState)));
    });
    assert.equal(await page.evaluate(() => window.testCalls.filter(r => r.op === 'view_chat').at(-1).chat), '', 'An open dialog must not report a visible conversation');
    assert.equal(await page.evaluate(() => window.testCalls.some(r => r.op === 'mark_read' && r.message_id === 'settings-unread')), false);
    await page.locator('#close-modal').click();
    await page.waitForFunction(() => window.testCalls.some(r => r.op === 'mark_read' && r.message_id === 'settings-unread'));
    await page.locator('#back-button').click();
    await page.evaluate(async () => { window.testState.messages[0].message.text = '<img src=x onerror="window.injected=true">'; await poll(); });
    await page.locator('.mobile-tabs [data-tab="groups"]').click();
    await page.locator('#messages').getByText('<img src=x onerror="window.injected=true">', { exact: true }).waitFor();
    assert.equal(await page.evaluate(() => window.injected), undefined); assert.equal(await page.locator('#messages .message-text img').count(), 0);
    await page.evaluate(async () => { window.testState.messages[0].message.text = 'Good morning, everyone. Who is building today?'; await poll(); });
    await page.setViewportSize({ width: 1280, height: 900 }); await page.locator('.desktop-tabs [data-tab="groups"]').click();
    await page.screenshot({ path: path.join(output, 'community-desktop.png') });
    await page.setViewportSize({ width: 360, height: 780 });
    assert(await page.locator('#connection').innerText().then(s => s.includes('Connect')), 'The connection action needs a visible label');
    await page.locator('#connection').click();
    await page.getByText('You are online', { exact: true }).waitFor();
    const vpn = page.getByRole('switch', { name: 'App VPN', exact: true });
    assert.equal(await vpn.getAttribute('aria-checked'), 'false');
    await vpn.click(); await page.getByText('On · connected', { exact: true }).waitFor();
    assert.equal(await vpn.getAttribute('aria-checked'), 'true');
    await vpn.click(); await page.getByText('Off · using your normal connection', { exact: true }).waitFor();
    const bt = page.getByRole('switch', { name: 'Bluetooth messaging', exact: true });
    await bt.click(); await page.getByText('On · no phone connected yet', { exact: true }).waitFor();
    assert.equal(await bt.getAttribute('aria-checked'), 'true');
    await page.getByRole('button', { name: 'Find a phone', exact: true }).waitFor();
    await page.screenshot({ path: path.join(output, 'connections-mobile.png') });
    await bt.click();
    assert.equal(await page.evaluate(() => window.paramo1dBack()), true, 'Back closes the connection panel');
    await page.getByRole('button', { name: 'Settings', exact: true }).click();
    await page.getByLabel('Appearance').selectOption('dark');
    await page.waitForFunction(() => document.documentElement.dataset.theme === 'dark');
    assert.equal(await page.locator('body').evaluate(e => getComputedStyle(e).backgroundColor), 'rgb(16, 20, 19)');
    await page.locator('#close-modal').click();
    await page.screenshot({ path: path.join(output, 'community-dark-mobile.png') });
    assert.equal(await page.locator('body').evaluate(e => e.scrollWidth <= innerWidth), true);
    await page.getByRole('button', { name: 'Settings', exact: true }).click();
    assert.equal(await page.getByLabel('Appearance').inputValue(), 'dark');
    await page.getByLabel('Appearance').selectOption('light');
    await page.waitForFunction(() => document.documentElement.dataset.theme === 'light');
    await page.locator('#close-modal').click();

    for (const theme of ['light', 'dark']) {
      const colors = new Set();
      for (const status of ['online', 'offline', 'nearby', 'connecting']) {
        await page.evaluate(async ({ theme, status }) => {
          window.testState.settings.theme = theme;
          window.testState.connection = { online: status === 'online' };
          window.testState.nearby = { peers: status === 'nearby' ? [{ id: 'fixture' }] : [] };
          window.testState.protection = { checking: status === 'connecting' };
          await poll();
        }, { theme, status });
        assert.equal(await page.locator('#connection-status').innerText(), { online: 'Online', offline: 'Offline', nearby: 'Bluetooth only', connecting: 'Connecting…' }[status]);
        const color = await page.locator('#connection i').evaluate(e => getComputedStyle(e).backgroundColor);
        assert(!['rgb(255, 255, 255)', 'rgba(0, 0, 0, 0)'].includes(color), 'The indicator must have a visible state color');
        colors.add(color);
      }
      assert.equal(colors.size, 4, 'Online, offline, nearby and connecting need distinct indicator colors in both themes');
    }
    await page.setViewportSize({ width: 320, height: 720 });
    assert.equal(await page.locator('body').evaluate(e => e.scrollWidth <= innerWidth), true, 'The connection controls must fit a small phone');
    await page.locator('#connection').click();
    await page.screenshot({ path: path.join(output, 'connections-dark-small.png') });
    await page.locator('#close-modal').click();
    await page.evaluate(() => {
      window.testState.profile = null; window.testState.contacts = []; window.testState.messages = []; window.testState.receipts = []; window.testState.observations = []; window.testState.chain = {}; window.testState.connection = { online: false }; window.testState.protection = { enabled: false }; window.testState.nearby = { enabled: false, peers: [] };
      window.paramo1dUpdate(JSON.parse(JSON.stringify(window.testState)));
    });
    await page.getByRole('button', { name: 'Restore from a backup', exact: true }).click();
    await page.getByRole('button', { name: 'Choose a backup file' }).waitFor();
    assert.equal(await page.getByPlaceholder('Paste your encrypted backup JSON').isVisible(), false, 'Manual backup data must stay behind the advanced choice');
    await page.locator('#close-modal').click();
    await page.locator('#display-name').fill('First time user');
    await page.screenshot({ path: path.join(output, 'first-launch-small.png') });
    await page.getByRole('button', { name: 'Create my profile' }).click();
    await page.waitForFunction(() => document.getElementById('onboarding').hidden);
    await page.getByRole('button', { name: 'Conversation actions' }).click();
    await page.getByRole('button', { name: 'Help send a saved payment' }).click();
    await page.getByText('No payments waiting to send.', { exact: true }).waitFor();
    assert.equal(await page.getByPlaceholder('Paste exported payment data').isVisible(), false, 'Community help must start with saved payments, not hexadecimal input');
    await page.locator('#close-modal').click();
    await page.locator('.mobile-tabs [data-tab="wallet"]').click();
    await page.getByRole('button', { name: 'Receive', exact: true }).click();
    await page.getByRole('button', { name: 'Copy address', exact: true }).click();
    assert.equal(await page.evaluate(() => window.testCalls.filter(r => r.op === 'copy').at(-1).text), 'o1fixture-alice');
    await page.locator('#close-modal').click();
    await page.locator('.mobile-tabs [data-tab="groups"]').click();
    await page.getByRole('button', { name: 'Conversation actions' }).click();
    await page.getByRole('button', { name: 'Share my contact' }).click();
    await page.getByRole('button', { name: 'Copy contact link', exact: true }).click();
    assert.equal(await page.evaluate(() => window.testCalls.filter(r => r.op === 'copy').at(-1).text), 'paramo1d://contact/test-view-fixture', 'The messaging contact and payment address have separate share actions');
    await page.locator('#close-modal').click();
    await page.getByRole('button', { name: 'Settings', exact: true }).click();
    await page.getByRole('switch', { name: 'App lock', exact: true }).waitFor();
    assert.equal(await page.getByRole('switch',{name:'Paranoid mode',exact:true}).count(),0);
    await page.getByText('Automatic wallet updates',{exact:true}).waitFor();
    assert.equal(await page.getByRole('switch',{name:'Receive with screen off',exact:true}).getAttribute('aria-checked'),'true');
    assert.equal(await page.getByText('Delivery relays · one HTTPS address per line', { exact: true }).isVisible(), false);
    await page.screenshot({ path: path.join(output, 'settings-small.png') });

    await page.locator('#close-modal').click();
    await page.locator('.mobile-tabs [data-tab="wallet"]').click();
    await page.evaluate(()=>{testState.chain={height:100,balance:'1.000000',running:true,automatic:true};testState.node={phase:'following'};paramo1dUpdate(JSON.parse(JSON.stringify(testState)));});
    assert.equal(await page.locator('#node-status').innerText(),'Saved balance');
    assert.equal(await page.locator('#sync-button').isDisabled(),false);
    await page.evaluate(()=>{testState.node={phase:'verifying'};paramo1dUpdate(JSON.parse(JSON.stringify(testState)));});
    assert.equal(await page.locator('#node-status').innerText(),'Checking a balance change…');
    assert.equal(await page.locator('#balance').innerText(),'1.000000');
    await page.evaluate(()=>{testState.node={phase:'following'};testDeferSync=true;paramo1dUpdate(JSON.parse(JSON.stringify(testState)));});
    await page.locator('#sync-button').click();
    await page.getByText('Checking for payments…',{exact:true}).waitFor();
    assert.equal(await page.locator('#balance').innerText(),'1.000000','The verified balance stays visible during a refresh');
    assert.equal(await page.locator('#sync-button').isDisabled(),true);
    await page.evaluate(()=>{testState.chain.running=false;testState.chain.automatic=false;paramo1dReply(testSyncRequest,{ok:true,result:JSON.parse(JSON.stringify(testState))});});
    await page.getByText('No new payments.',{exact:true}).waitFor();
    assert.equal(await page.locator('#sync-button').isDisabled(),false);
    assert.equal(await page.locator('#balance').innerText(),'1.000000');
    assert.equal(await page.evaluate(()=>state.chain.height),100,'An unchanged refresh preserves the verified checkpoint');
    await page.locator('#sync-button').click();
    await page.getByText('Checking for payments…',{exact:true}).waitFor();
    await page.evaluate(()=>{paramo1dReply(testSyncRequest,{ok:false,error:'Network unavailable. Please try again.'});});
    await page.getByText('Network unavailable. Please try again.',{exact:true}).waitFor();
    assert.equal(await page.locator('#sync-button').isDisabled(),false,'A failed refresh releases the button');
    assert.equal(await page.locator('#balance').innerText(),'1.000000');
    await page.evaluate(()=>{testState.chain.running=true;testState.chain.automatic=true;testState.connection.online=true;testState.node={phase:'verifying',renewing_authorization:true};paramo1dUpdate(JSON.parse(JSON.stringify(testState)));});
    await page.getByText('Keeping payments ready in the background.',{exact:true}).waitFor();
    assert.equal(await page.locator('#balance').innerText(),'1.000000');
    assert.equal(await page.locator('#sync-button').isDisabled(),false,'Background epoch renewal keeps the balance controls available');
    await page.locator('#sync-button').click();
    await page.getByText('Checking for payments…',{exact:true}).waitFor();
    await page.evaluate(()=>{paramo1dReply(testSyncRequest,{ok:true,result:JSON.parse(JSON.stringify(testState))});});
    await page.getByText('Your wallet is updating in the background.',{exact:true}).waitFor();
    assert.equal(await page.locator('#sync-button').isDisabled(),false,'Refreshing the balance must not wait for the background epoch renewal');
    assert.equal(await page.locator('#balance').innerText(),'1.000000');
    await page.evaluate(()=>{testDeferSync=false;});
    await page.setViewportSize({width:1280,height:800});
    await page.evaluate(()=>{testState.settings.theme='dark';paramo1dUpdate(JSON.parse(JSON.stringify(testState)));selectTab('direct');});
    await page.locator('#new-button').hover();
    const buttonColors=await page.locator('#new-button').evaluate(e=>({background:getComputedStyle(e).backgroundColor,text:getComputedStyle(e).color}));
    assert.deepEqual(buttonColors,{background:'rgb(0, 255, 128)',text:'rgb(7, 18, 13)'});

    await page.evaluate(async()=>{
      const invoiceId='03'.repeat(16),peer={id:'22'.repeat(32),box_key:'bb'.repeat(32),name:'Bob',address:'o1fixture-bob'};
      testState.contacts=[peer];
      testState.messages.push({id:'outgoing-request',chat:'d:'+peer.id,sender:testState.profile,message:{type:'invoice',invoice_id:invoiceId,address:testState.profile.address,amount:'0.010000',memo:'Receipt status check'},created_ms:Date.now(),status:'sent'});
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));await openChat('d:'+peer.id);
    });
    const requestCard=page.locator('[data-invoice-id="'+ '03'.repeat(16)+'"]');
    await requestCard.getByText('Waiting for a payment receipt.',{exact:true}).waitFor();
    await page.evaluate(()=>{
      testState.messages.push({id:'incoming-receipt',chat:'d:'+testState.contacts[0].id,sender:testState.contacts[0],message:{type:'receipt',invoice_id:'03'.repeat(16),receipt_hex:'00'},created_ms:Date.now(),status:'received'});
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    });
    await requestCard.getByText('Receipt received. Check it below.',{exact:true}).waitFor();
    assert.equal(await requestCard.getByText('PAYMENT CHECKED',{exact:true}).count(),0);
    await page.evaluate(()=>{
      testState.receipts.push({txid:'cd'.repeat(32),message_id:'incoming-receipt',invoice_id:'03'.repeat(16),verified:true,amount:'0.010000',height:100,confirmations:4,finalized:false});
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    });
    await requestCard.getByText('PAYMENT CHECKED',{exact:true}).waitFor();
    assert.equal(await requestCard.getByText('Waiting for a payment receipt.',{exact:true}).count(),0);
    await requestCard.getByRole('button',{name:/View receipt/}).click();
    await page.getByRole('heading',{name:'Payment verified.',exact:true}).waitFor();

    assert.deepEqual(errors, []); console.log('PASS: mobile layout, local receipt status, queued delivery, payment review, unsent packet handling, unknown balance and safe message text.');
  } finally { await browser.close(); server.close(); }
}

module.exports = { bridge, server, output };
if (require.main === module) main().catch((error) => { console.error(error); process.exitCode = 1; server.close(); });
