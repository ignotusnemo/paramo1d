const assert = require('node:assert/strict');
const path = require('node:path');
const fs = require('node:fs/promises');
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');
const { bridge, server, output } = require('./ui.test.cjs');

(async () => {
  await fs.mkdir(output, { recursive: true });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const browser = await chromium.launch({ executablePath: process.env.CHROME || '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox'] });
  const failures = [];
  try {
    const page = await browser.newPage({ viewport: { width: 390, height: 844 } });
    page.on('pageerror', error => failures.push(error.message));
    await bridge(page); await page.goto(`http://127.0.0.1:${server.address().port}/`);
    await page.locator('#messages .message').first().waitFor();
    const originalId = '34'.repeat(32), contactId = '56'.repeat(32), uri = 'paramo1d://contact/fixture-charlie';
    await page.evaluate(({ originalId, contactId, uri }) => {
      testContactLinks = { [uri]: { id: contactId, box_key: '78'.repeat(32), name: 'Charlie', address: 'o1fixture-charlie' } };
      testState.messages.push({ id: originalId, chat: 'g:parano1d', sender: testState.contacts[0], message: { type: 'text', text: 'The message we are replying to.' }, created_ms: Date.now() - 1000, status: 'received' });
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    }, { originalId, contactId, uri });
    const original = page.locator(`[data-message-id="${originalId}"]`);
    await original.getByRole('button', { name: /Message options/ }).click();
    await page.getByRole('button', { name: 'Copy text', exact: true }).click();
    assert.equal(await page.evaluate(() => testCalls.filter(c => c.op === 'copy').at(-1).text), 'The message we are replying to.');

    await original.getByRole('button', { name: /Message options/ }).click();
    await page.getByRole('button', { name: 'Reply', exact: true }).click();
    await page.locator('#reply-preview-author').getByText('Replying to Bob').waitFor();
    await page.locator('#compose').fill('A proper threaded reply.');
    await page.getByRole('button', { name: 'Send message', exact: true }).click();
    await page.locator('.message-text').getByText('A proper threaded reply.', { exact: true }).waitFor();
    const reply = page.locator('.message').filter({ hasText: 'A proper threaded reply.' }).last();
    assert.equal(await reply.locator('.message-quote strong').innerText(), 'Bob');
    await reply.getByRole('button', { name: 'Go to original message' }).click();
    await original.locator('.message-body').waitFor();
    assert.equal(await original.evaluate(node => node.classList.contains('message-highlight')), true);
    const wire = await page.evaluate(() => testCalls.filter(c => c.op === 'send').at(-1).message);
    assert.deepEqual(Object.keys(wire).sort(), ['text', 'type'], 'Replies must preserve the released text envelope format');
    assert(wire.text.includes(`paramo1d://message/${originalId}`));

    if (await page.locator('#latest-messages').isVisible()) await page.locator('#latest-messages').click();
    await page.locator('#compose').fill('Emoji ');
    await page.getByRole('button', { name: 'Choose emoji', exact: true }).click();
    await page.getByRole('button', { name: 'Insert 😀', exact: true }).click();
    assert.equal(await page.locator('#compose').inputValue(), 'Emoji 😀');
    await page.getByRole('button', { name: 'Choose emoji', exact: true }).click();
    await page.getByRole('button', { name: 'Send message', exact: true }).click();
    await page.locator('.message-text').getByText('Emoji 😀', { exact: true }).waitFor();

    await original.getByRole('button', { name: /Message options/ }).click();
    await page.getByRole('button', { name: 'React 👍', exact: true }).click();
    await original.getByRole('button', { name: '👍, 1 reactions', exact: true }).waitFor();
    await original.getByRole('button', { name: '👍, 1 reactions', exact: true }).click();
    await page.waitForFunction(id => !document.getElementById('message-' + id).querySelector('.reaction-chip'), originalId);

    await page.locator('#compose').fill('A draft kept for the community.');
    await page.locator('.mobile-tabs [data-tab="direct"]').click();
    await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
    assert.equal(await page.locator('#compose').inputValue(), '');
    await page.locator('#compose').fill('A separate private draft.');
    await page.locator('#back-button').click();
    await page.locator('.mobile-tabs [data-tab="groups"]').click();
    assert.equal(await page.locator('#compose').inputValue(), 'A draft kept for the community.');
    await page.locator('#compose').fill(uri);
    await page.getByRole('button', { name: 'Send message', exact: true }).click();
    const card = page.locator('.contact-card').filter({ hasText: 'Charlie' });
    await card.getByText('Charlie', { exact: true }).waitFor();
    assert.equal(await card.locator('.selectable-contact-link').isVisible(), false);
    await card.getByRole('button', { name: 'Copy contact link' }).click();
    assert.equal(await page.evaluate(() => testCalls.filter(c => c.op === 'copy').at(-1).text), uri);
    assert.equal(await page.evaluate(id => testState.contacts.some(c => c.id === id), contactId), false, 'Rendering a card must not add a contact');
    await card.getByRole('button', { name: 'Add contact', exact: true }).click();
    assert.equal(await page.evaluate(id => testState.contacts.some(c => c.id === id), contactId), true);
    await card.getByRole('button', { name: 'Message', exact: true }).first().click();
    await page.locator('#chat-name').getByText('Charlie', { exact: true }).waitFor();
    const headerAvatar = await page.locator('#chat-avatar img').getAttribute('src');
    assert.equal(headerAvatar, await page.evaluate(id => WarriorAvatar.source(id), contactId));
    await page.evaluate(() => { window.avatarBeforeUpdate = document.querySelector('#chat-avatar img'); paramo1dUpdate(JSON.parse(JSON.stringify(testState))); });
    assert.equal(await page.evaluate(() => window.avatarBeforeUpdate === document.querySelector('#chat-avatar img')), true, 'An unchanged update must retain the loaded avatar');
    assert.notEqual(headerAvatar, await page.evaluate(() => WarriorAvatar.source(testState.profile.id)));
    await page.locator('#back-button').click(); await page.locator('.mobile-tabs [data-tab="groups"]').click();

    const invalidUri = 'paramo1d://contact/invalid-fixture';
    await page.locator('#compose').fill(invalidUri);
    await page.getByRole('button', { name: 'Send message', exact: true }).click();
    const invalidCard = page.locator('.contact-card').filter({ hasText: 'Could not check this contact.' });
    await invalidCard.getByRole('button', { name: 'Try again', exact: true }).waitFor();
    assert.equal(await invalidCard.getByRole('button', { name: 'Add contact', exact: true }).count(), 0, 'Unchecked contact data must not enable adding a contact');
    await page.evaluate(({ uri, contactId }) => { testContactLinks[uri] = { id: contactId, box_key: '78'.repeat(32), name: 'Charlie', address: 'o1fixture-charlie' }; }, { uri: invalidUri, contactId });
    await invalidCard.getByRole('button', { name: 'Try again', exact: true }).click();
    await page.locator('.contact-card').filter({ hasText: 'Charlie' }).last().getByRole('button', { name: 'Message', exact: true }).waitFor();

    await page.getByRole('button', { name: 'Search this conversation', exact: true }).click();
    await page.getByRole('searchbox', { name: 'Search messages', exact: true }).fill('proper threaded');
    await page.locator('#chat-search-count').getByText('1 / 1', { exact: true }).waitFor();
    await page.getByRole('button', { name: 'Close message search' }).click();

    await page.locator('#compose').fill('😀'.repeat(1100));
    assert.equal(await page.getByRole('button', { name: 'Send message', exact: true }).isDisabled(), true);
    await page.locator('#compose').fill('');

    const expiredTxid = '9a'.repeat(32);
    await page.evaluate(txid => {
      testState.messages.push({ id: 'expired-payment', chat: 'g:parano1d', sender: testState.contacts[0], message: { type: 'transaction', intent_hex: '00' }, payment: { txid }, created_ms: Date.now(), status: 'received', via_nearby: true });
      testBroadcastTxid = txid; testBroadcastError = 'node RPC error: {"code":-32000,"message":"consensus: BadEpochAnchor"}';
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    }, expiredTxid);
    const expired = page.locator(`[data-txid="${expiredTxid}"]`);
    if (await page.locator('#latest-messages').isVisible()) await page.locator('#latest-messages').click();
    await expired.getByRole('button', { name: 'Help send this payment' }).click();
    await page.getByRole('button', { name: 'Send to the network' }).click();
    await expired.getByText('Payment expired', { exact: true }).waitFor();
    await expired.getByText('Ask the sender to connect, update their wallet and send a new payment.', { exact: true }).waitFor();
    assert.equal(await page.locator('#toast').innerText().then(text => text.includes('BadEpochAnchor')), false, 'The user must receive an actionable explanation instead of an RPC error');
    await page.locator('#close-modal').click();
    await page.evaluate(txid => {
      delete testBroadcastError;
      testState.prepared_payments = [{ txid, to: testState.contacts[0].address, amount: '0.010000', chat: 'd:' + testState.contacts[0].id, delivery_error: 'consensus: BadEpochAnchor' }];
      testState.messages.find(m => m.id === 'expired-payment').sender = testState.profile;
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    }, expiredTxid);
    await expired.getByRole('button', { name: 'Review fresh payment' }).click();
    const freshReview = await page.evaluate(() => testCalls.filter(call => call.op === 'payment_preview').at(-1));
    assert.equal(freshReview.use_cached, false, 'A replacement must refresh the wallet before its review');
    assert.equal(freshReview.replaces_txid, expiredTxid);
    assert.equal(await page.evaluate(() => testCalls.some(call => call.op === 'payment_send')), false, 'A replacement must require the owner to review and approve it');
    await page.locator('#close-modal').click();

    await page.evaluate(() => {
      const now = Date.now(), peer = testState.contacts[0];
      testState.messages = Array.from({ length: 300 }, (_, i) => ({ id: i.toString(16).padStart(64, '0'), chat: 'g:parano1d', sender: peer, message: { type: 'text', text: `Stable scroll message ${i}. Some readable conversation text.` }, created_ms: now - (300 - i) * 1000, status: 'received' }));
      testState.receipts = []; testState.observations = [];
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    });
    await page.locator('.mobile-tabs [data-tab="direct"]').click();
    await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
    await page.locator('#back-button').click();
    await page.locator('.mobile-tabs [data-tab="groups"]').click();
    assert(await page.locator('#messages .message').count() <= 240, 'The initial chat window must be bounded');
    assert.equal(await page.locator('#messages .message').last().innerText().then(text => text.includes('message 299')), true, 'Opening a conversation must show its latest message');
    await page.waitForFunction(() => { const s = document.getElementById('message-scroll'); return s.scrollHeight - s.scrollTop - s.clientHeight < 2; });
    await page.locator('#messages').evaluate(messages => { messages.style.paddingTop = '180px'; });
    await page.waitForFunction(() => { const s = document.getElementById('message-scroll'); return s.scrollHeight - s.scrollTop - s.clientHeight < 2; });
    assert.equal(await page.locator('#messages .message').last().innerText().then(text => text.includes('message 299')), true, 'Late layout changes must keep the latest message visible');
    await page.locator('#message-scroll').evaluate(scroller => { scroller.scrollTop = Math.max(1, scroller.scrollHeight / 2); });
    await page.waitForTimeout(100);
    const stable = await page.locator('#message-scroll').evaluate(scroller => ({ top: scroller.scrollTop, node: scroller.querySelector('.message').dataset.messageId }));
    await page.evaluate(() => paramo1dUpdate(JSON.parse(JSON.stringify(testState))));
    assert(Math.abs(await page.locator('#message-scroll').evaluate(s => s.scrollTop) - stable.top) < 2, 'An unchanged update must preserve scroll');
    await page.evaluate(() => {
      testState.messages.push({ id: 'ef'.repeat(32), chat: 'g:parano1d', sender: testState.contacts[0], message: { type: 'text', text: 'A new message while reading history.' }, created_ms: Date.now(), status: 'received' });
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    });
    assert(Math.abs(await page.locator('#message-scroll').evaluate(s => s.scrollTop) - stable.top) < 2, 'Incoming messages must not move a reader through history');
    await page.getByRole('button', { name: 'Go to latest messages' }).click();
    await page.locator('.message-text').getByText('A new message while reading history.', { exact: true }).waitFor();

    await page.evaluate(() => {
      const now = Date.now(), alice = testState.profile, bob = testState.contacts[0], charlie = testState.contacts[1];
      const conversation = [
        [bob, 'Morning! Who is testing nearby messages today?'],
        [charlie, 'I am. My phone has no connection here.'],
        [charlie, 'Bluetooth is on 👍'],
        [alice, 'Send it over. I can help it reach the network.'],
        [bob, 'A messenger and your own node. That is the idea.'],
        [alice, 'Your voice. Your money. 💚'],
      ];
      testState.messages = conversation.map(([sender, text], index) => ({ id: (index + 1000).toString(16).padStart(64, '0'), chat: 'g:parano1d', sender, message: { type: 'text', text }, created_ms: now - (conversation.length - index) * 60000, status: sender.id === alice.id ? 'sent' : 'received' }));
      testState.prepared_payments = []; testState.connection = { online: true };
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
      document.getElementById('toast').hidden = true;
    });
    for (const theme of ['light', 'dark']) for (const width of [320, 390, 768, 1280]) {
      await page.setViewportSize({ width, height: 844 });
      await page.evaluate(theme => { testState.settings.theme = theme; paramo1dUpdate(JSON.parse(JSON.stringify(testState))); }, theme);
      assert.equal(await page.locator('body').evaluate(body => body.scrollWidth <= window.innerWidth), true, `${theme} ${width}px must fit horizontally`);
      if (width === 390) {
        await page.screenshot({ path: path.join(output, `chat-${theme}.png`) });
        await page.locator('#connection').click();
        await page.screenshot({ path: path.join(output, `connections-${theme}.png`) });
        await page.locator('#close-modal').click();
        await page.getByRole('button', { name: 'Settings', exact: true }).click();
        await page.screenshot({ path: path.join(output, `settings-${theme}.png`) });
        await page.locator('#close-modal').click();
      }
    }
    assert.deepEqual(failures, []);
    console.log('PASS: replies, copy, emoji, reactions, drafts, verified contact cards, pixel avatars, expired payment recovery, message search, UTF-8 limits, bounded history, stable scrolling and responsive themes.');
  } finally { await browser.close(); server.close(); }
})().catch(error => { console.error(error); process.exitCode = 1; server.close(); });
