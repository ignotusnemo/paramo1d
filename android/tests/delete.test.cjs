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
      await page.evaluate(width => {
        const eve = { id: '33'.repeat(32), name: 'Eve', address: 'o1fixture-eve' };
        testState.contacts.push(eve);
        testState.messages.push({ id: 'eve-private', chat: 'd:' + eve.id, sender: eve, message: { type: 'text', text: 'Keep this conversation.' }, created_ms: Date.now(), status: 'received' });
        testState.receipts.push({ txid: 'cd'.repeat(32), verified: true, receipt_hex: 'saved-receipt' });
        testState.chain = { balance: '1.23', height: 300000 };
        testState.drafts = { ['d:' + '22'.repeat(32)]: { text: 'Private draft', reply_to: '' } };
        testState.settings.theme = width === 390 ? 'dark' : 'light';
        paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
      }, width);
      await page.locator(width < 761 ? '.mobile-tabs [data-tab="direct"]' : '[data-tab="direct"]').first().click();
      const options = page.getByRole('button', { name: 'Options for Bob', exact: true });
      await options.waitFor();
      const bounds = await options.boundingBox();
      assert.ok(bounds.width >= 44 && bounds.height >= 44 && bounds.x >= 0 && bounds.x + bounds.width <= width);
      if (width === 390) await page.screenshot({ path: path.join(output, 'delete-chat-list.png') });
      await options.click();
      await page.getByRole('button', { name: 'Delete chat', exact: true }).click();
      await page.getByRole('heading', { name: 'Delete chat and contact?', exact: true }).waitFor();
      assert.equal(await page.getByText('This deletes the message history on this phone. A new message from this person will start a new chat.', { exact: true }).isVisible(), true);
      await page.getByRole('button', { name: 'Cancel', exact: true }).click();
      assert.equal(await page.evaluate(() => testCalls.filter(call => call.op === 'delete_conversation').length), 0);
      assert.equal(await options.isVisible(), true);

      await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
      assert.equal(await page.locator('#compose').inputValue(), 'Private draft');
      await page.locator('#compose').fill('Delete this unsent draft too.');
      await page.locator('#chat-options-button').click();
      await page.getByRole('button', { name: 'Delete chat', exact: true }).click();
      await page.mouse.move(0, 0);
      await page.screenshot({ path: path.join(output, `delete-chat-${width}.png`) });
      const colors = await page.getByRole('button', { name: 'Delete chat', exact: true }).evaluate(button => ({ text: getComputedStyle(button).color, background: getComputedStyle(button).backgroundColor }));
      assert.equal(colors.text, 'rgb(255, 255, 255)');
      assert.equal(colors.background, 'rgb(164, 46, 33)');
      await page.getByRole('button', { name: 'Delete chat', exact: true }).click();
      await page.locator('#modal').waitFor({ state: 'hidden' });
      assert.equal(await options.count(), 0);
      assert.equal(await page.getByRole('button', { name: 'Options for Eve', exact: true }).isVisible(), true);
      let result = await page.evaluate(() => ({ contacts: testState.contacts.map(contact => contact.name), ids: testState.messages.map(message => message.id), drafts: testState.drafts, receipts: testState.receipts.length, chain: testState.chain, call: testCalls.filter(call => call.op === 'delete_conversation').at(-1) }));
      assert.deepEqual(result.contacts, ['Eve']); assert.deepEqual(result.ids, ['hello', 'payment', 'eve-private']);
      assert.equal(result.drafts['d:' + '22'.repeat(32)], undefined);
      assert.equal(result.receipts, 1); assert.equal(result.chain.balance, '1.23');
      assert.deepEqual(result.call, { op: 'delete_conversation', chat: 'd:' + '22'.repeat(32), confirmed: true });
      checks.push({ width, check: 'Row and header menus delete the chat, contact and draft while preserving other chats and wallet records' });

      await page.evaluate(() => {
        const bob = { id: '22'.repeat(32), name: 'Bob', address: 'o1fixture-bob' };
        testState.contacts.push(bob);
        testState.messages.push({ id: 'new-private', chat: 'd:' + bob.id, sender: bob, message: { type: 'text', text: 'A new conversation starts here.' }, created_ms: Date.now(), status: 'received' });
        paramo1dUpdate(JSON.parse(JSON.stringify(testState)));
      });
      await options.waitFor();
      await page.locator('.conversation-row').filter({ hasText: 'Bob' }).click();
      await page.locator('#messages').getByText('A new conversation starts here.', { exact: true }).waitFor();
      assert.equal(await page.locator('#compose').inputValue(), '');
      assert.equal(await page.locator('#messages .message').count(), 1);
      checks.push({ width, check: 'A new incoming message restores the contact and starts an empty conversation without restoring its deleted draft or history' });
      await page.locator('#chat-options-button').click(); await page.getByRole('button', { name: 'Delete chat', exact: true }).click();
      await page.evaluate(() => { window.testDeleteError = true; });
      await page.getByRole('button', { name: 'Delete chat', exact: true }).click();
      await page.getByText('Chat could not be deleted. Try again.', { exact: true }).waitFor();
      assert.equal(await page.getByRole('button', { name: 'Delete chat', exact: true }).isEnabled(), true);
      assert.equal(await page.evaluate(() => testState.contacts.some(contact => contact.name === 'Bob')), true);
      await page.locator('#close-modal').click();
      if (width < 761) await page.locator('#back-button').click();
      await page.locator(width < 761 ? '.mobile-tabs [data-tab="groups"]' : '[data-tab="groups"]').first().click();
      await page.locator('#chat-options-button').click();
      assert.equal(await page.getByRole('button', { name: 'Delete chat', exact: true }).count(), 0);
      checks.push({ width, check: 'A failed deletion keeps the conversation and can be retried; Community has no contact-deletion action' });
      const layout = await page.evaluate(() => ({ width: innerWidth, scroll: document.documentElement.scrollWidth }));
      assert.ok(layout.scroll <= width + 1, JSON.stringify(layout));
      await page.close();
    }
    assert.deepEqual(errors, []);
    await fs.writeFile(path.join(output, 'delete-result.json'), JSON.stringify({ ok: true, checks, errors }, null, 2));
    console.log(JSON.stringify({ ok: true, checks: checks.length, widths: [320, 390, 1280], errors }));
  } finally { await browser.close(); await new Promise(resolve => server.close(resolve)); }
})().catch(error => { console.error(error); process.exitCode = 1; });
