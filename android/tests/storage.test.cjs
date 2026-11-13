const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');
const { bridge, server, output } = require('./ui.test.cjs');

(async () => {
  await fs.mkdir(output, { recursive: true });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const browser = await chromium.launch({ executablePath: process.env.CHROME || '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox'] });
  const errors = [], checks = [];
  try {
    for (const width of [320, 390, 1280]) {
      const page = await browser.newPage({ viewport: { width, height: width < 700 ? 844 : 1000 } });
      page.on('pageerror', error => errors.push(error.message)); await bridge(page);
      await page.goto(`http://127.0.0.1:${server.address().port}/`);
      await page.locator('#messages .message').first().waitFor();
      await page.evaluate(() => {
        const eve = { id: '33'.repeat(32), name: 'Eve', address: 'o1fixture-eve' };
        testState.contacts.push(eve);
        testState.messages.push({ id: 'eve-message', chat: 'd:' + eve.id, sender: eve, message: { type: 'text', text: 'Keep this private conversation.' }, created_ms: Date.now(), status: 'received' });
        testState.messages.push({ id: 'queued-community', chat: 'g:parano1d', sender: testState.profile, message: { type: 'text', text: 'Keep this unsent message.' }, created_ms: Date.now(), status: 'queued' });
        testState.receipts.push({ txid: 'cd'.repeat(32), verified: true, receipt_hex: 'saved-receipt' });
        paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
      });
      await page.locator('#settings-button').click();
      assert.equal(await page.getByRole('button', { name: 'Chat storage', exact: true }).isVisible(), true);
      const storageBounds = await page.getByRole('button', { name: 'Chat storage', exact: true }).boundingBox(), settingsBounds = await page.locator('#modal').boundingBox();
      assert.ok(storageBounds.y >= settingsBounds.y && storageBounds.y + storageBounds.height <= settingsBounds.y + settingsBounds.height, 'Chat storage must be visible without scrolling Settings');
      assert.equal(await page.locator('.advanced-settings').first().getAttribute('open'), null);
      await page.getByRole('button', { name: 'Chat storage', exact: true }).click();
      await page.getByRole('checkbox', { name: 'Community', exact: true }).waitFor();
      assert.equal(await page.getByRole('button', { name: 'Clear selected history', exact: true }).isDisabled(), true);
      assert.equal(await page.getByRole('checkbox').count(), 3);
      await page.getByRole('checkbox', { name: 'Community', exact: true }).check();
      assert.equal(await page.getByRole('checkbox', { name: 'Bob', exact: true }).isChecked(), false);
      await page.getByRole('button', { name: 'Clear selected history', exact: true }).click();
      await page.locator('#modal').waitFor({ state: 'hidden' });
      let result = await page.evaluate(() => ({ ids: testState.messages.map(x => x.id), call: testCalls.filter(x => x.op === 'clear_history').at(-1), receipts: testState.receipts.length, contacts: testState.contacts.length }));
      assert.deepEqual(result.call.chats, ['g:parano1d']);
      assert.deepEqual(result.ids.sort(), ['eve-message', 'invoice', 'queued-community']);
      assert.equal(result.receipts, 1); assert.equal(result.contacts, 2);
      checks.push({ width, check: 'Community clears separately and preserves private chats, queued messages and saved receipts' });

      if (width < 761) { await page.locator('#back-button').evaluate(button => { if (!button.hidden) button.click(); }); await page.locator('.mobile-tabs [data-tab="direct"]').click(); }
      else await page.locator('[data-tab="direct"]').first().click();
      await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
      await page.locator('#chat-options-button').click(); await page.getByRole('button', { name: 'Clear history', exact: true }).click();
      await page.getByRole('checkbox', { name: 'Bob', exact: true }).waitFor();
      assert.equal(await page.getByRole('checkbox', { name: 'Bob', exact: true }).isChecked(), true);
      assert.equal(await page.getByRole('checkbox', { name: 'Community', exact: true }).isDisabled(), true);
      await page.getByRole('button', { name: 'Clear selected history', exact: true }).click();
      await page.locator('#modal').waitFor({ state: 'hidden' });
      result = await page.evaluate(() => ({ ids: testState.messages.map(x => x.id), call: testCalls.filter(x => x.op === 'clear_history').at(-1) }));
      assert.deepEqual(result.call.chats, ['d:' + '22'.repeat(32)]);
      assert.deepEqual(result.ids.sort(), ['eve-message', 'queued-community']);
      checks.push({ width, check: 'A selected private chat clears without touching another private chat' });

      await page.evaluate(() => { testState.storage_full = true; paramo1dUpdate(JSON.parse(JSON.stringify(testState))); });
      await page.getByRole('heading', { name: 'Chat storage', exact: true }).waitFor();
      await page.getByRole('checkbox', { name: 'Eve', exact: true }).waitFor();
      assert.equal(await page.locator('.storage-warning').isVisible(), true);
      const requests = await page.evaluate(() => testCalls.filter(x => x.op === 'chat_storage').length);
      await page.evaluate(() => { paramo1dUpdate(JSON.parse(JSON.stringify(testState))); paramo1dUpdate(JSON.parse(JSON.stringify(testState))); });
      assert.equal(await page.evaluate(() => testCalls.filter(x => x.op === 'chat_storage').length), requests);
      await page.screenshot({ path: path.join(output, `storage-full-${width}.png`) });
      await page.locator('#close-modal').click(); assert.equal(await page.locator('#storage-alert').isVisible(), true);
      await page.locator('#storage-manage').click(); await page.getByRole('checkbox', { name: 'Eve', exact: true }).check();
      await page.getByRole('button', { name: 'Clear selected history', exact: true }).click();
      await page.locator('#modal').waitFor({ state: 'hidden' }); assert.equal(await page.locator('#storage-alert').isVisible(), false);
      checks.push({ width, check: 'Full storage opens the chooser once, leaves a visible reminder and resumes after cleanup' });
      const layout = await page.evaluate(() => ({ width: innerWidth, scroll: document.documentElement.scrollWidth }));
      assert.ok(layout.scroll <= width + 1, JSON.stringify(layout));
      await page.close();
    }
    const page = await browser.newPage({ viewport: { width: 390, height: 844 } }); await bridge(page);
    page.on('pageerror', error => errors.push(error.message)); await page.goto(`http://127.0.0.1:${server.address().port}/`);
    await page.locator('#messages .message').first().waitFor();
    await page.evaluate(() => {
      for (let i = 0; i < 75; i++) {
        const id = (100 + i).toString(16).padStart(64, '0'), peer = { id, name: 'Chat ' + String(i).padStart(2, '0'), address: 'o1fixture' };
        testState.contacts.push(peer); testState.messages.push({ id: 'private-' + i, chat: 'd:' + id, sender: peer, message: { type: 'text', text: 'Private history' }, created_ms: Date.now(), status: 'received' });
      }
      paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
    });
    await page.locator('#settings-button').click(); await page.getByRole('button', { name: 'Chat storage', exact: true }).click();
    await page.getByRole('button', { name: 'Show more chats', exact: true }).waitFor();
    assert.equal(await page.locator('.storage-chat').count(), 51);
    await page.getByRole('searchbox', { name: 'Find a chat', exact: true }).fill('Chat 74'); assert.equal(await page.locator('.storage-chat').count(), 1);
    await page.getByRole('checkbox', { name: 'Chat 74', exact: true }).check();
    await page.getByRole('searchbox', { name: 'Find a chat', exact: true }).fill('');
    await page.getByRole('button', { name: 'Select all', exact: true }).click();
    await page.getByRole('button', { name: 'Clear selected history', exact: true }).click();
    await page.locator('#modal').waitFor({ state: 'hidden' });
    assert.equal(await page.evaluate(() => testCalls.filter(x => x.op === 'clear_history').at(-1).chats.length), 77);
    checks.push({ check: 'Large chat lists have bounded rendering, search and multi-selection including unloaded rows' });
    await page.locator('#settings-button').click(); await page.evaluate(() => { testStorageError = true; });
    await page.getByRole('button', { name: 'Chat storage', exact: true }).click(); await page.getByRole('button', { name: 'Try again', exact: true }).waitFor();
    await page.evaluate(() => { testStorageError = false; }); await page.getByRole('button', { name: 'Try again', exact: true }).click();
    await page.getByRole('checkbox', { name: 'Community', exact: true }).waitFor(); assert.equal(await page.getByRole('button', { name: 'Clear selected history', exact: true }).isDisabled(), true);
    checks.push({ check: 'Storage read failure is recoverable and empty history cannot be cleared accidentally' });
    await page.close();
    const dark = await browser.newPage({ viewport: { width: 390, height: 844 } }); await bridge(dark);
    dark.on('pageerror', error => errors.push(error.message)); await dark.goto(`http://127.0.0.1:${server.address().port}/`);
    await dark.locator('#messages .message').first().waitFor();
    await dark.evaluate(() => { testState.settings.theme = 'dark'; testSendStorageFull = true; paramo1dUpdate(JSON.parse(JSON.stringify(testState))); });
    await dark.locator('#compose').fill('Keep this draft if storage is full.');
    await dark.getByRole('button', { name: 'Send message', exact: true }).click();
    await dark.getByRole('heading', { name: 'Chat storage', exact: true }).waitFor();
    await dark.getByRole('checkbox', { name: 'Community', exact: true }).check();
    const color = await dark.getByRole('button', { name: 'Clear selected history', exact: true }).evaluate(el => ({ color: getComputedStyle(el).color, background: getComputedStyle(el).backgroundColor }));
    assert.notEqual(color.color, 'rgb(255, 255, 255)');
    await dark.screenshot({ path: path.join(output, 'storage-dark.png') });
    assert.equal(await dark.locator('#compose').inputValue(), 'Keep this draft if storage is full.');
    checks.push({ check: 'A send rejected for full storage opens the chooser, preserves the draft and has readable dark-theme controls', color });
    await dark.close(); assert.deepEqual(errors, []);
    await fs.writeFile(path.join(output, 'storage-result.json'), JSON.stringify({ ok: true, checks, errors }, null, 2));
    console.log(`Storage UI: ${checks.length} checks passed.`);
  } finally { await browser.close(); server.close(); }
})().catch(error => { console.error(error); process.exitCode = 1; server.close(); });
