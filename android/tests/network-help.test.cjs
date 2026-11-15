const assert = require('node:assert/strict');
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');
const { bridge, server } = require('./ui.test.cjs');

(async () => {
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const browser = await chromium.launch({ executablePath: process.env.CHROME || '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox'] });
  const page = await browser.newPage({ viewport: { width: 320, height: 720 } });
  const errors = [];
  page.on('pageerror', error => errors.push(error.message));
  try {
    await bridge(page);
    await page.goto(`http://127.0.0.1:${server.address().port}`);
    await page.waitForFunction(() => window.testState && state?.profile);
    await page.evaluate(() => { window.testState.nearby = { enabled: false, peers: [] }; });
    const publish = async id => page.evaluate(id => {
      window.testState.network_help = { recommend_vpn: true, issue: 'wallet', id };
      window.paramo1dUpdate(JSON.parse(JSON.stringify(window.testState)));
    }, id);
    await page.locator('#compose').focus();
    await page.evaluate(() => { walletBusy = true; });
    await publish('wallet:1000');
    assert.equal(await page.locator('#modal').evaluate(node => node.open), false, 'A suggestion waits while typing');
    await page.evaluate(() => { document.activeElement.blur(); render(); });
    await page.getByRole('heading', { name: 'Having trouble connecting?' }).waitFor();
    assert.equal(await page.evaluate(() => state.paranoid_mode), false, 'Ordinary wallets receive connection help');
    assert.equal(await page.evaluate(() => walletBusy), true, 'A pending balance request does not hide connection help');
    await page.evaluate(() => { walletBusy = false; });
    assert.equal(await page.locator('#vpn-switch').getAttribute('aria-checked'), 'false', 'The suggestion keeps VPN off until chosen');
    await page.getByRole('button', { name: 'Not now', exact: true }).click();
    await publish('wallet:1000');
    assert.equal(await page.locator('#modal').evaluate(node => node.open), false, 'The same outage does not interrupt again');
    await page.evaluate(() => { window.testState.paranoid_mode = true; window.paramo1dUpdate(JSON.parse(JSON.stringify(window.testState))); });
    await page.getByRole('button', { name: 'Settings', exact: true }).click();
    await publish('wallet:2000');
    assert.notEqual(await page.locator('#modal').getAttribute('data-kind'), 'CONNECTION HELP', 'An open dialog is preserved');
    await page.locator('#close-modal').click();
    await page.getByRole('heading', { name: 'Having trouble connecting?' }).waitFor();
    assert.equal(await page.evaluate(() => state.paranoid_mode), true, 'Paranoid wallets retain the same connection help');
    await page.getByRole('button', { name: 'Turn on App VPN', exact: true }).click();
    await page.waitForFunction(() => document.getElementById('vpn-switch').dataset.status === 'connected');
    assert.equal(await page.locator('#modal').evaluate(node => node.open), false);
    await publish('wallet:3000');
    assert.equal(await page.locator('#modal').evaluate(node => node.open), false, 'An enabled VPN suppresses suggestions');
    assert.deepEqual(errors, []);
    console.log('PASS: App VPN suggestions in both wallet modes, typing and dialog guards, dismissal and explicit activation.');
  } finally {
    await browser.close();
    await new Promise(resolve => server.close(resolve));
  }
})().catch(error => { console.error(error); process.exitCode = 1; });
