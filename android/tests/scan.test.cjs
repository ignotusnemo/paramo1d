const assert = require('node:assert/strict');
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');
const { bridge, server } = require('./ui.test.cjs');

(async () => {
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const browser = await chromium.launch({ executablePath: process.env.CHROME || '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox'] });
  const failures = [];
  try {
    const page = await browser.newPage({ viewport: { width: 390, height: 844 } });
    page.on('pageerror', error => failures.push(error.message));
    await bridge(page); await page.goto(`http://127.0.0.1:${server.address().port}/`);
    await page.locator('#messages .message').first().waitFor();
    await page.locator('.mobile-tabs [data-tab="wallet"]').click();
    await page.locator('#send-button').click();
    const address = page.getByLabel('Recipient NOID address');
    const amount = page.getByLabel('Amount · NOID', { exact: true });
    await amount.fill('0.010000');
    await page.evaluate(() => { testScanResult = { kind: 'address', text: 'o1fixture-scanned-recipient' }; });
    await page.getByRole('button', { name: 'Scan a NOID address', exact: true }).click();
    await page.waitForFunction(() => document.querySelector('#modal input').value === 'o1fixture-scanned-recipient');
    assert.equal(await amount.inputValue(), '0.010000');
    assert.equal(await page.evaluate(() => testCalls.some(call => ['payment_preview', 'payment_send'].includes(call.op))), false, 'Scanning must only fill the recipient');

    await page.evaluate(() => { testScanResult = { cancelled: true }; });
    await page.getByRole('button', { name: 'Scan a NOID address', exact: true }).click();
    assert.equal(await address.inputValue(), 'o1fixture-scanned-recipient', 'Cancelling must preserve the existing recipient');
    await page.evaluate(() => { testScanResult = { error: 'Scan a NOID receiving address QR code.' }; });
    await page.getByRole('button', { name: 'Scan a NOID address', exact: true }).click();
    await page.locator('#toast').getByText('Scan a NOID receiving address QR code.', { exact: true }).waitFor();
    assert.equal(await address.inputValue(), 'o1fixture-scanned-recipient');

    await page.evaluate(() => { delete testScanResult; });
    await page.getByRole('button', { name: 'Scan a NOID address', exact: true }).click();
    const oldScan = await page.evaluate(() => testCalls.filter(call => call.op === 'scan_qr').at(-1).scan_id);
    await page.locator('#close-modal').click(); await page.locator('#send-button').click();
    await page.evaluate(scan_id => paramo1dScanResult({ scan_id, kind: 'address', text: 'o1stale-result' }), oldScan);
    assert.equal(await page.getByLabel('Recipient NOID address').inputValue(), '', 'A result from a closed form must not fill a new payment');
    await page.locator('#close-modal').click();

    await page.locator('.mobile-tabs [data-tab="direct"]').click();
    await page.getByRole('button', { name: 'Add a contact', exact: true }).click();
    const uri = 'paramo1d://contact/fixture-qr-contact', peer = { id: 'ac'.repeat(32), name: 'QR contact', box_key: 'cd'.repeat(32), address: 'o1fixture-contact' };
    await page.evaluate(({ uri, peer }) => { testContactLinks = { [uri]: peer }; testScanResult = { kind: 'contact', text: uri, contact: peer }; }, { uri, peer });
    await page.getByRole('button', { name: 'Scan a contact QR code', exact: true }).click();
    await page.locator('.scanned-contact').getByText('QR contact', { exact: true }).waitFor();
    assert.equal(await page.getByLabel('Contact link').inputValue(), uri);
    assert.equal(await page.evaluate(id => testState.contacts.some(contact => contact.id === id), peer.id), false, 'A scanned contact must wait for confirmation');
    await page.getByRole('button', { name: 'Add contact', exact: true }).click();
    assert.equal(await page.evaluate(id => testState.contacts.some(contact => contact.id === id), peer.id), true);

    await page.getByRole('button', { name: 'Settings', exact: true }).click();
    const capture = page.getByRole('switch', { name: 'Allow screenshots', exact: true });
    assert.equal(await capture.getAttribute('aria-checked'), 'false');
    await capture.click();
    await page.waitForFunction(() => document.querySelector('[aria-label="Allow screenshots"]').getAttribute('aria-checked') === 'true');
    await capture.click();
    await page.waitForFunction(() => document.querySelector('[aria-label="Allow screenshots"]').getAttribute('aria-checked') === 'false');
    assert.deepEqual(failures, []);
    console.log('PASS: address and contact scans, cancellation, invalid codes, stale results, explicit confirmation and screenshot preference.');
  } finally { await browser.close(); server.close(); }
})().catch(error => { console.error(error); process.exitCode = 1; server.close(); });
