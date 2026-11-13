'use strict';

const $ = (id) => document.getElementById(id);
const pending = new Map();
let requestNumber = 0;
let state = null;
let tab = 'groups';
let chat = 'g:parano1d';
let polling = false;
let pollTimer;
let walletBusy = false;
const readingChats = new Set();
let reportedChat;
let scanNumber = 0, scanContext = null;

function native(op, args = {}) {
  return new Promise((resolve, reject) => {
    if (!window.Paramo1d?.request) {
      reject(new Error('Open Paramo1d on Android to connect your local identity.'));
      return;
    }
    const id = String(++requestNumber);
    const timeout = setTimeout(() => {
      pending.delete(id);
      reject(new Error('This operation is taking longer than expected.'));
    }, ['sync', 'payment_preview', 'payment_send', 'receipt_verify'].includes(op) ? 300000 : 45000);
    pending.set(id, { resolve, reject, timeout });
    window.Paramo1d.request(id, JSON.stringify({ op, ...args }));
  });
}

window.paramo1dReply = (id, response) => {
  const call = pending.get(id);
  if (!call) return;
  clearTimeout(call.timeout);
  pending.delete(id);
  if (response.ok) call.resolve(response.result);
  else call.reject(new Error(response.error || 'The operation could not be completed.'));
};
window.paramo1dUpdate = (updated) => { state = updated; render(); };
window.paramo1dKeyboard = (visible) => {
  document.body.classList.toggle('keyboard-open', !!visible);
  ChatUI.layoutChanged();
};

function element(tag, attributes = {}, ...children) {
  const node = document.createElement(tag);
  for (const [key, value] of Object.entries(attributes)) {
    if (key === 'class') node.className = value;
    else if (key === 'text') node.textContent = value;
    else if (key.startsWith('on')) node.addEventListener(key.slice(2), value);
    else node.setAttribute(key, value);
  }
  for (const child of children.flat()) if (child != null) node.append(typeof child === 'string' ? document.createTextNode(child) : child);
  if (tag === 'button' && attributes.class && typeof attributes.text === 'string' && /(?:primary|outline|text)-button/.test(attributes.class)) {
    const match = attributes.text.match(/\s*([↗↓↻↑])$/);
    if (match) { node.textContent = attributes.text.slice(0, match.index); node.append(icon({ '↗': 'outgoing', '↓': 'receive', '↻': 'refresh', '↑': 'send' }[match[1]])); }
  }
  return node;
}

function icon(name) {
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.classList.add('icon'); svg.setAttribute('aria-hidden', 'true');
  const use = document.createElementNS('http://www.w3.org/2000/svg', 'use');
  use.setAttribute('href', `icons.svg#${name}`); svg.append(use); return svg;
}

function toast(message) {
  $('toast').textContent = message;
  $('toast').hidden = false;
  clearTimeout(toast.timer);
  toast.timer = setTimeout(() => { $('toast').hidden = true; }, 5500);
}

async function run(button, work, busyLabel) {
  if (button?.disabled) return;
  const original = button?.innerHTML;
  if (button) { button.disabled = true; if (busyLabel) button.textContent = busyLabel; }
  try { return await work(); } catch (error) { if (ChatStorageUI.isFullError(error.message)) ChatStorageUI.reportFull(); else toast(explainError(error.message)); }
  finally { if (button) { button.disabled = false; if (busyLabel) button.innerHTML = original; } }
}

function explainError(message = 'Please try again.') {
  if (needsNewApproval(message)) return 'This payment expired. Its sender needs to connect, update the wallet and approve a new payment.';
  if (message.startsWith('Insufficient available NOID')) return 'Not enough available NOID. Check pending payments or update your balance.';
  if (message.includes('Connect once') || message.includes('offline view')) return 'Connect to the internet and tap Update balance before making an offline payment.';
  if (message.includes('State advanced') || message.includes('crossed a block boundary') || message.includes('Wallet data is ahead')) return 'The network changed during the check. Update your balance and try again.';
  if (message.startsWith('Invalid recipient')) return 'Check the recipient’s NOID address and try again.';
  return message.replaceAll('Check balance', 'Update balance');
}

function needsNewApproval(message = '') { return message.includes('BadEpochAnchor') || message.startsWith('Payment epoch changed.'); }

function initials(name) { return String(name || '?').trim().split(/\s+/).slice(0, 2).map((v) => [...v][0]).join('').toUpperCase(); }
function short(id) { return id ? `${id.slice(0, 8)} · ${id.slice(-8)}` : ''; }
function time(ms) { return new Date(ms).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' }); }
function contact(id) { return state?.contacts?.find((c) => c.id === id); }
function chatMessages(key) { return (state?.messages || []).filter((m) => m.chat === key); }
function preview(message) {
  if (!message) return 'Start the conversation';
  return ChatUI.preview(message);
}

function applyTheme() {
  const mode = state?.settings?.theme || 'system';
  document.documentElement.dataset.theme = mode === 'system' ? (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light') : mode;
}
matchMedia('(prefers-color-scheme: dark)').addEventListener('change', applyTheme);
function render() {
  applyTheme();
  if (!state?.profile) { $('onboarding').hidden = false; $('toast').hidden = true; return; }
  $('onboarding').hidden = true;
  $('my-name').textContent = state.profile.name;
  WarriorAvatar.paint($('my-avatar'), state.profile.id, state.profile.name);
  $('my-fingerprint').textContent = short(state.profile.id);
  renderConnection();
  ChatStorageUI.renderNotice();
  document.querySelectorAll('[data-tab]').forEach((button) => button.classList.toggle('active', button.dataset.tab === tab));
  const unreadDirect = Object.entries(state.unread || {}).filter(([key]) => key.startsWith('d:')).reduce((sum, [, count]) => sum + Number(count), 0);
  document.querySelectorAll('[data-tab="direct"]').forEach(button => {
    let badge = button.querySelector('.tab-unread');
    if (!unreadDirect) { badge?.remove(); return; }
    if (!badge) { badge = element('span', { class: 'tab-unread' }); button.append(badge); }
    badge.textContent = unreadDirect > 99 ? '99+' : String(unreadDirect);
  });
  $('list-heading').textContent = tab === 'direct' ? 'Messages' : 'Community';
  $('new-button').hidden = tab !== 'direct';
  $('new-button').setAttribute('aria-label', 'Add a contact');
  $('list-footnote').textContent = tab === 'direct' ? 'Private messages are encrypted on your device.' : 'One community. Direct connections.';
  renderConversations();
  renderChat();
  renderWallet();
  renderNearbyPanel();
  renderBackgroundSetting();
  renderSecuritySetting();
  renderCaptureSetting();
  renderNodeSetting();
  $('wallet-panel').hidden = tab !== 'wallet';
  $('chat-panel').hidden = tab === 'wallet' || !chat;
  $('welcome-panel').hidden = tab === 'wallet' || !!chat;
  document.body.classList.toggle('chat-open', !!chat && tab !== 'wallet');
  document.body.classList.toggle('direct-open', !!chat?.startsWith('d:') && tab !== 'wallet');
  document.body.classList.toggle('wallet-open', tab === 'wallet');
  reportVisibleChat();
}

function renderConnection() {
  const online = !!state?.connection?.online;
  const nearby = (state?.nearby?.peers || []).length > 0;
  const status = state?.protection?.checking || !online && state?.connection?.checking ? 'connecting' : online ? 'online' : nearby ? 'nearby' : 'offline';
  const label = { online: 'Online', nearby: 'Bluetooth only', offline: 'Offline', connecting: 'Connecting…' }[status];
  const button = $('connection');
  button.dataset.status = status;
  button.classList.toggle('online', status === 'online');
  button.classList.toggle('nearby', status === 'nearby');
  button.setAttribute('aria-label', `Connection options: ${label.toLowerCase()}`);
  $('connection-status').textContent = label;
}

function renderConversations() {
  const list = $('conversation-list');
  list.replaceChildren();
  const query = $('search').value.trim().toLowerCase();
  const conversations = tab === 'direct'
    ? (state.contacts || []).map((c) => ({ key: `d:${c.id}`, title: c.name, avatar: initials(c.name), description: short(c.id), contact: c }))
    : [{ key: 'g:parano1d', title: '#parano1d', avatar: '#', description: 'Community chat' }];
  for (const item of conversations.filter((c) => `${c.title} ${c.description}`.toLowerCase().includes(query))) {
    const messages = chatMessages(item.key);
    const last = messages.at(-1);
    const row = element('button', { class: `conversation-row${chat === item.key ? ' selected' : ''}`, onclick: () => openChat(item.key) },
      item.contact ? WarriorAvatar.node(item.contact.id, item.contact.name) : element('span', { class: 'avatar' }, icon('community')),
      element('span', { class: 'row-text' }, element('strong', { text: item.title }), element('p', { text: last ? preview(last.message) : item.description })),
      last ? element('time', { text: time(last.created_ms) }) : null);
    if (item.contact) list.append(element('div', { class: 'conversation-item' }, row,
      element('button', { class: 'icon-button conversation-options', 'aria-label': `Options for ${item.title}`, onclick: () => showChatOptions(item.key) }, icon('more'))));
    else list.append(row);
    row.addEventListener('contextmenu', event => { event.preventDefault(); showChatOptions(item.key); });
    const count = Number(state.unread?.[item.key] || 0);
    if (count) row.append(element('span', { class: 'unread', 'aria-label': `${count} unread messages`, text: count > 99 ? '99+' : String(count) }));
  }
  if (!list.children.length) list.append(query ? empty('No contacts found', 'Try another name.') : empty('No private chats yet', 'Tap Add contact, or tap someone’s name in the community chat.'));
}

function empty(title, description) {
  return element('div', { class: 'empty-state' }, element('span', { class: 'empty-symbol' }, icon('chat')), element('strong', { text: title }), element('p', { text: description }));
}

async function openChat(key) {
  ChatUI.beforeSwitch();
  chat = key;
  tab = key.startsWith('d:') ? 'direct' : 'groups';
  render();
  await markCurrentRead(true);
  await poll();
  $('message-scroll').scrollTop = $('message-scroll').scrollHeight;
}

function renderChat() {
  ChatUI.render();
}

async function markCurrentRead(force = false) {
  const key = chat;
  if (!key || tab === 'wallet' || $('modal').open || !state?.profile || document.hidden || readingChats.has(key) || !force && !Number(state.unread?.[key])) return;
  readingChats.add(key);
  try { state = await native('mark_read', { chat: key, message_id: chatMessages(key).at(-1)?.id || '' }); render(); }
  catch { }
  finally { readingChats.delete(key); }
}

async function reportVisibleChat() {
  if (!state?.profile) return;
  const key = document.hidden || $('modal').open || tab === 'wallet' ? '' : chat || '';
  const paymentFlow=$('modal').open && ['NOID / SEND','AUTHORIZE'].includes($('modal').dataset.kind);
  const walletVisible=!document.hidden && tab==='wallet' && !$('modal').open;
  const marker=key+String(paymentFlow)+String(walletVisible);
  if (reportedChat === marker) return;
  reportedChat = marker;
  try { await native('view_chat', { chat: key, payment_flow:paymentFlow, wallet_visible:walletVisible }); }
  catch { if (reportedChat === marker) reportedChat = undefined; }
}

function paymentCard(item, mine) {
  const message = item.message;
  if (message.type === 'transaction') {
    return transactionCard(item, mine);
  }
  if (message.type === 'invoice') {
    const checked = (state.receipts || []).find(r => r.verified && r.invoice_id === message.invoice_id);
    const received = chatMessages(item.chat).some(m => m.message.type === 'receipt' && m.message.invoice_id === message.invoice_id);
    const card = element('div', { class: 'payment-card', 'data-invoice-id': message.invoice_id }, element('header', { text: checked ? 'PAYMENT CHECKED' : 'PAYMENT REQUEST' }));
    const content = element('div', {}, element('div', { class: 'amount' }, message.amount, ' ', element('span', { text: 'NOID' })), element('p', { text: message.memo || 'A direct payment in NOID.' }), element('code', { text: short(message.address) }));
    if (checked) content.append(element('p', { text: 'Receipt checked on this phone.' }), element('button', { class: 'primary-button', text: 'View receipt ↗', onclick: () => showReceipt(checked) }));
    else if (!mine) content.append(element('button', { class: 'primary-button', text: 'Review payment ↗', onclick: (event) => reviewPayment(message.address, message.amount, message.invoice_id, event.currentTarget) }));
    else if (received) content.append(element('p', { text: 'Receipt received. Check it below.' }));
    else content.append(element('p', { text: 'Waiting for a payment receipt.' }));
    card.append(content); return card;
  }
  const verified = (state.receipts || []).find((r) => r.message_id === item.id);
  const card = element('div', { class: 'payment-card' }, element('header', { text: verified ? 'VERIFIED PAYMENT' : 'PAYMENT RECEIPT' }));
  const content = element('div', {}, element('p', { text: verified ? `Included at block ${verified.height.toLocaleString()}.` : 'Check this receipt against your verified chain.' }));
  content.append(element('button', { class: 'primary-button', text: verified ? 'View receipt ↗' : 'Check payment ↗', onclick: () => verified ? showReceipt(verified) : verifyMessageReceipt(item) }));
  card.append(content); return card;
}

function transactionCard(item, mine) {
  const txid = item.payment?.txid;
  const reports = (state.observations || []).filter((o) => o.message.txid === txid && o.chat === item.chat);
  const latest = reports.slice().sort((a, b) => b.created_ms - a.created_ms)[0];
  const evidence = reports.find((o) => o.message.stage === 'included' && o.message.receipt_hex);
  const verified = (state.receipts || []).find((r) => r.txid === txid && r.verified);
  const ownPacket = (state.prepared_payments || []).find((p) => p.txid === txid);
  const outdated = !verified && !evidence && needsNewApproval(item.broadcast_error || ownPacket?.delivery_error || '');
  const card = element('div', { class: `payment-card transaction-card${verified ? ' verified' : ''}`, 'data-txid': txid || '' });
  const title = verified ? (verified.finalized ? 'FINALIZED PAYMENT' : 'PAYMENT CHECKED') : 'PAYMENT';
  card.append(element('header', { text: title }));
  const content = element('div');
  const statuses = { submitted: 'Sent · waiting for confirmation', in_mempool: 'Sent · waiting for confirmation', included: 'Payment found · ready to check', rejected: 'A helper reported rejection' };
  content.append(element('strong', { class: 'payment-stage', text: verified ? `Block ${Number(verified.height).toLocaleString()}` : outdated ? 'Payment expired' : statuses[latest?.message.stage] || 'Waiting to reach the network' }));
  if (txid) content.append(element('code', { text: short(txid) }));
  if (verified) content.append(element('p', { text: 'This phone checked that the payment is included in the blockchain.' }));
  else if (outdated) content.append(element('p', { class: 'danger', text: mine ? 'Connect, update your wallet and approve a new payment.' : 'Ask the sender to connect, update their wallet and send a new payment.' }));
  else if (latest) content.append(element('p', { class: 'report-meta', text: `${latest.sender.name} · ${time(latest.created_ms)} · network observation` }));
  else content.append(element('p', { text: 'This payment is already approved by its sender. Help it reach the network.' }));
  const helpers = new Set(reports.map((o) => o.sender.id)).size;
  if (helpers) content.append(element('small', { class: 'helper-count', text: `${helpers} ${helpers === 1 ? 'helper' : 'helpers'} · status updates appear here` }));
  if (evidence && !verified) {
    const check = element('button', { class: 'primary-button', text: 'Check payment ↗', onclick: () => run(check, async () => {
      const result = await native('receipt_verify', { receipt_hex: evidence.message.receipt_hex, expected_txid: txid, message_id: item.id });
      state = result.state; render(); showReceipt(result.receipt);
    }) });
    content.append(check);
  }
  if (!verified) {
    if (outdated && mine && ownPacket?.to && !ownPacket.replaced_by) content.append(element('button', { class: 'primary-button', text: 'Review fresh payment ↗', onclick: event => reviewPayment(ownPacket.to, ownPacket.amount, ownPacket.invoice_id || '', event.currentTarget, false, txid) }));
    const broadcast = element('button', { class: evidence || outdated ? 'outline-button' : 'primary-button', text: outdated ? 'Retry network submission ↗' : 'Help send this payment ↗', onclick: () => inspectBroadcast(item) });
    content.append(broadcast);
  } else content.append(element('button', { class: 'outline-button', text: 'View verified receipt ↗', onclick: () => showReceipt(verified) }));
  if (mine && !outdated && item.chat.startsWith('d:')) content.append(element('button', { class: 'text-button', text: 'Ask the community to help', onclick: () => sharePrepared(txid) }));
  card.append(content); return card;
}

async function inspectBroadcast(item) {
  await run(null, async () => {
    const review = await native('broadcast_preview', { message_id: item.id });
    const outputs = review.outputs.map((o) => element('div', { class: 'detail', text: `${formatMicronoid(o.amount_micronoid)} NOID → ${o.address}` }));
    const forward = element('button', { class: 'primary-button', text: 'Send to the network ↗', onclick: () => run(forward, async () => {
      await native('broadcast_send', { message_id: item.id, txid: review.txid }); $('modal').close(); await poll(); toast('Forwarded. This card will collect status updates.');
    }) });
    modal('Help it reach the network.', [element('p', { text: 'Send the approved payment to the network. Its sender pays the fee. This uses no NOID from your wallet.' }), ...outputs, element('div', { class: 'review-row' }, element('span', { text: 'Network fee' }), element('span', { text: `${review.fee} NOID` })), element('div', { class: 'detail', text: review.txid }), forward], 'BROADCAST');
  });
}

function formatMicronoid(value) { const amount = BigInt(value); return `${amount / 1000000n}.${String(amount % 1000000n).padStart(6, '0')}`; }
function paymentAmount(value) {
  const amount = String(value).trim().replace(',', '.');
  if (!/^\d+(?:\.\d{1,6})?$/.test(amount) || !/[1-9]/.test(amount)) throw new Error('Enter an amount greater than zero, with up to six decimal places.');
  return amount;
}
async function sharePrepared(txid) { await run(null, async () => { state = await native('share_prepared', { txid }); $('modal').close(); await openChat('g:parano1d'); toast('Help request shared. Updates will appear on its card.'); }); }

function renderWallet() {
  if (!state) return;
  $('wallet-address').textContent = state.profile?.address || '';
  $('balance').textContent = state.chain?.balance || '—';
  const renewing = !!state.chain?.automatic && !!state.node?.renewing_authorization;
  const verifying = !!state.chain?.automatic && state.node?.phase === 'verifying' && !renewing;
  const busy = !!state.chain?.running && !state.chain?.automatic || walletBusy || verifying;
  $('node-status').textContent = busy ? verifying ? 'Checking a balance change…' : 'Checking for payments…' : state.chain?.retrying ? 'Wallet will retry' : state.node?.phase === 'starting' ? 'Connecting…' : state.chain?.height ? state.connection?.online ? 'Wallet ready' : 'Saved balance' : 'Preparing your wallet…';
  $('node-status').classList.toggle('busy', busy);
  $('sync-button').disabled = busy;
  $('sync-button').textContent = busy ? verifying ? 'Updating…' : 'Checking…' : 'Update balance';
  $('balance-description').textContent = busy ? verifying ? 'Verifying a change to your balance. You can keep chatting.' : 'Checking for new payments. You can keep chatting.' : !state.chain?.height ? 'Open your wallet online before making your first payment.' : !state.connection?.online ? 'Saved balance. Reconnect to check for changes.' : renewing ? 'Keeping payments ready in the background.' : state.chain?.retrying ? 'Showing your saved balance. Wallet updates will retry.' : 'Balance updates automatically.';
  const setup = $('wallet-setup'); setup.replaceChildren();
  if (!state.backup_saved) setup.append(element('section', { class: 'wallet-reminder' }, element('strong', { text: 'Keep access if you lose this phone' }), element('p', { text: 'Save an encrypted backup of your wallet and chats.' }), element('button', { class: 'outline-button', text: 'Save a backup', onclick: showBackup })));
  if (state.security && !state.security.available) setup.append(element('section', { class: 'wallet-reminder' }, element('strong', { text: 'Protect access to this wallet' }), element('p', { text: 'Set a phone PIN or fingerprint to lock Paramo1d when you leave it.' }), element('button', { class: 'outline-button', text: 'Set up phone screen lock', onclick: () => run(null, () => native('phone_security')) })));
  const receipts = $('receipts'); receipts.replaceChildren();
  for (const r of state.receipts || []) receipts.append(element('button', { class: 'receipt-row', onclick: () => showReceipt(r) }, element('span', {}, element('strong', { text: r.amount ? `${r.amount} NOID` : 'Verified payment' }), element('small', { text: `Block ${r.height} · ${short(r.txid)}` })), element('span', { text: r.finalized ? 'FINALIZED ↗' : 'VERIFIED ↗' })));
  if (!receipts.children.length) receipts.append(empty('Keep the proof.', 'Verified payment receipts are saved here.'));
  const pendingPayments = $('pending-payments'); pendingPayments.replaceChildren();
  for (const packet of (state.prepared_payments || []).filter((p) => !p.replaced_by).slice(-20).reverse()) {
    if ((state.receipts || []).some((r) => r.txid === packet.txid && r.verified)) continue;
    const outdated = needsNewApproval(packet.delivery_error);
    const row = element('div', { class: 'pending-payment' }, element('strong', { text: `${packet.amount || '—'} NOID` }), element('p', { text: packet.submitted ? 'Sent. Waiting for confirmation.' : outdated ? 'Payment expired.' : 'Saved on this phone. Waiting to send.' }), element('code', { text: short(packet.txid) }));
    if (packet.delivery_error) row.append(element('p', { class: 'danger', text: explainError(packet.delivery_error) }), element('button', { class: 'outline-button', text: outdated ? 'Review fresh payment ↗' : 'Try sending again', onclick: (event) => outdated ? run(null, async () => { if (packet.chat?.startsWith('d:')) await openChat(packet.chat); await reviewPayment(packet.to, packet.amount, packet.invoice_id || '', event.currentTarget, false, packet.txid); }) : run(event.currentTarget, async () => { state = await native('retry_payment', { txid: packet.txid }); render(); toast('Trying to send the saved payment.'); }) }));
    if (!outdated) row.append(element('button', { class: 'outline-button', text: 'Ask the community to help ↗', onclick: () => sharePrepared(packet.txid) }));
    const evidence = (state.observations || []).find((o) => o.message.txid === packet.txid && o.message.stage === 'included' && o.message.receipt_hex);
    if (evidence) row.append(element('button', { class: 'primary-button', text: 'Check payment ↗', onclick: () => run(null, async () => { const result = await native('receipt_verify', { receipt_hex: evidence.message.receipt_hex, expected_txid: packet.txid }); state = result.state; render(); showReceipt(result.receipt); }) }));
    pendingPayments.append(row);
  }
}

function modal(title, children, eyebrow = 'PARAMO1D') {
  $('modal').dataset.kind=eyebrow;
  $('modal-title').textContent = title;
  $('modal-eyebrow').textContent = eyebrow;
  $('modal-content').replaceChildren(...children);
  if (!$('modal').open) $('modal').showModal();
  reportVisibleChat();
}

function field(label, options = {}) {
  const input = element(options.multiline ? 'textarea' : 'input', { type: options.type || 'text', placeholder: options.placeholder || '', ...(options.value != null ? { value: options.value } : {}) });
  if (options.multiline) input.value = options.value || '';
  if (options.autocomplete) input.autocomplete = options.autocomplete;
  return { label: element('label', {}, label, input), input };
}

function scannedField(kind, value, preview) {
  const button = element('button', { class: 'scan-trigger', type: 'button', 'aria-label': kind === 'contact' ? 'Scan a contact QR code' : 'Scan a NOID address', onclick: async () => {
    if (scanContext) return;
    const scan = { id: String(++scanNumber), kind, input: value.input, button, preview };
    scanContext = scan; button.disabled = true;
    try { await native('scan_qr', { kind, scan_id: scan.id }); }
    catch (error) { if (scanContext === scan) scanContext = null; button.disabled = false; toast(explainError(error.message)); }
  } }, icon('scan'), 'Scan');
  return element('div', { class: 'scan-field' }, value.label, button);
}

window.paramo1dScanResult = result => {
  const scan = scanContext;
  if (!scan || result.scan_id !== scan.id) return;
  scanContext = null; scan.button.disabled = false;
  if (result.cancelled || !scan.input.isConnected || !$('modal').open) return;
  if (result.error) { toast(explainError(result.error)); return; }
  if (result.kind !== scan.kind || typeof result.text !== 'string') { toast('Please scan the QR code again.'); return; }
  scan.input.value = result.text; scan.input.dispatchEvent(new Event('input', { bubbles: true }));
  if (scan.preview && result.contact) {
    scan.preview.replaceChildren(WarriorAvatar.node(result.contact.id, result.contact.name), element('span', {}, element('strong', { text: result.contact.name }), element('small', { text: short(result.contact.id) })));
    scan.preview.hidden = false;
  }
  toast(scan.kind === 'contact' ? 'Contact scanned. Tap Add contact to save it.' : 'Address scanned. Check the recipient before sending.');
};

function showContact(peer) {
  if (peer.id === state.profile.id) { showInvite(); return; }
  const button = element('button', { class: 'primary-button', text: 'Message ↗', onclick: () => run(button, async () => {
    state = await native('add_contact', { contact: peer }); $('modal').close(); await openChat(`d:${peer.id}`);
  }) });
  modal(peer.name, [button, element('details', { class: 'advanced-settings' }, element('summary', { text: 'Contact details' }), element('p', { text: 'Compare this code with the person you want to message.' }), element('div', { class: 'detail', text: peer.id }), element('p', { text: 'NOID address' }), element('div', { class: 'detail', text: peer.address }))], 'CONTACT');
}

function showInvite() {
  if (!state?.profile) return;
  const children = [element('p', { text: 'Share this contact to start an encrypted conversation.' })];
  if (window.qrcode && state.invite) {
    const box = element('div', { class: 'qr' });
    const code = qrcode(0, 'M'); code.addData(state.invite); code.make();
    // QR generator creates SVG from encoded modules, without user markup.
    box.innerHTML = code.createSvgTag({ cellSize: 3, margin: 3, scalable: true });
    children.push(box);
  }
  children.push(element('div', { class: 'detail', text: short(state.profile.id) }), element('button', { class: 'primary-button', text: 'Share contact ↗', onclick: () => run(null, () => native('share', { text: state.invite })) }), element('button', { class: 'text-button', text: 'Copy contact link', onclick: () => copy(state.invite) }));
  modal(state.profile.name, children, 'YOUR CONTACT');
}

function showAddContact() {
  const uri = field('Contact link', { multiline: true, placeholder: 'paramo1d://contact/…' });
  const preview = element('div', { class: 'scanned-contact contact-card-person', hidden: '' });
  uri.input.addEventListener('input', () => { preview.hidden = true; });
  const add = element('button', { class: 'primary-button', text: 'Add contact ↗', onclick: () => run(add, async () => {
    state = await native('import_contact', { uri: uri.input.value.trim() }); $('modal').close(); render();
  }) });
  modal('Add a contact', [element('p', { text: 'Scan their contact QR code or paste their Paramo1d contact link.' }), scannedField('contact', uri, preview), preview, add], 'MESSAGES');
}

function showSettings() {
  const select = element('select', { id: 'theme-select', 'aria-label': 'Appearance' }, ...[['system', 'Use phone setting'], ['light', 'Light'], ['dark', 'Dark']].map(([value, text]) => element('option', { value, text })));
  select.value = state.settings?.theme || 'system';
  select.addEventListener('change', () => run(null, async () => { state = await native('theme', { value: select.value }); render(); }));
  const appearance = element('label', {}, 'Appearance', select);
  const relays = field('Delivery relays · one HTTPS address per line', { multiline: true, value: (state.settings?.relays || []).join('\n'), placeholder: 'https://your-relay.example' });
  const rpc = field('Chain data endpoint', { value: state.settings?.rpc || '', placeholder: 'https://your-node.example/rpc' });
  const save = element('button', { class: 'primary-button', text: 'Save connection settings ↗', onclick: () => run(save, async () => {
    state = await native('settings', { relays: relays.input.value.split('\n').map((s) => s.trim()).filter(Boolean), rpc: rpc.input.value.trim() }); $('modal').close(); render(); await poll();
  }) });
  modal('Settings', [appearance, element('button', { class: 'outline-button', text: 'Connections', onclick: showConnections }),
    element('button', { class: 'outline-button', text: 'Chat storage', onclick: () => void ChatStorageUI.open() }), element('div', { id: 'node-setting' }), element('div', { id: 'background-setting' }), element('div', { id: 'security-setting' }), element('div', { id: 'capture-setting' }),
    element('button', { class: 'outline-button', text: 'Save an encrypted backup ↗', onclick: showBackup }),
    element('details', { class: 'advanced-settings' }, element('summary', { text: 'Advanced settings' }), element('p', { text: 'Choose your delivery relays and wallet data service.' }), relays.label, rpc.label, save, element('button', { class: 'outline-button', text: 'Import a payment receipt', onclick: showImportReceipt }), element('p', { text: 'Direct-message encryption: X25519 and XSalsa20-Poly1305. The community chat and NOID payments are public.' }))], 'SETTINGS');
  if (state.storage_full) $('modal-content').prepend(element('section', { class: 'wallet-reminder' }, element('strong', { text: 'Storage is full' }), element('p', { text: 'Choose the chats to clear so new messages can arrive.' }), element('button', { class: 'outline-button', text: 'Choose chats', onclick: () => void ChatStorageUI.open() })));
  renderBackgroundSetting();
  renderSecuritySetting();
  renderCaptureSetting();
  renderNodeSetting();
}

function renderNodeSetting() {
  const panel=$('node-setting'); if(!panel)return;
  panel.replaceChildren(element('section',{class:'connection-card'},element('strong',{text:'Automatic wallet updates'}),element('p',{text:'Checks for wallet changes while the app is open. Your phone verifies new balances. Stops when you leave or lock the phone. Use Update balance to check now.'})));
}

function renderSecuritySetting() {
  const panel = $('security-setting'); if (!panel) return;
  const security = state.security || {};
  const toggle = connectionToggle('App lock', !!security.enabled, async () => { state = await native('app_lock', { enabled: !security.enabled }); render(); });
  toggle.disabled = !security.available;
  const card = element('section', { class: 'connection-card' }, element('div', { class: 'connection-card-heading' }, element('strong', { text: 'App lock' }), toggle), element('p', { text: security.available ? 'Unlock on entry with your fingerprint or phone PIN. Locks after 30 seconds away.' : 'Set a phone PIN or fingerprint to protect access to your messages and wallet.' }));
  if (!security.available) card.append(element('button', { class: 'outline-button', text: 'Set up phone screen lock', onclick: () => run(null, () => native('phone_security')) }));
  if (security.enabled) card.append(element('button', { class: 'outline-button', text: 'Lock now', onclick: () => run(null, () => native('lock_now')) }));
  panel.replaceChildren(card);
}

function connectionToggle(label, on, action) {
  const button = element('button', { class: 'connection-toggle', role: 'switch', 'aria-label': label, 'aria-checked': String(on), onclick: () => run(button, action) }, element('span', { text: on ? 'On' : 'Off' }), element('span', { class: 'toggle-track', 'aria-hidden': 'true' }));
  return button;
}
function renderCaptureSetting() {
  const panel = $('capture-setting'); if (!panel) return;
  const enabled = !!state.allow_screenshots;
  const toggle = connectionToggle('Allow screenshots', enabled, async () => { state = await native('allow_screenshots', { enabled: !enabled }); render(); });
  panel.replaceChildren(element('section', { class: 'connection-card' }, element('div', { class: 'connection-card-heading' }, element('strong', { text: 'Allow screenshots' }), toggle), element('p', { text: 'Save screenshots or record the app screen on this phone. Off by default.' })));
}
function renderBackgroundSetting() {
  const panel = $('background-setting'); if (!panel) return;
  const on = !!state.background_delivery;
  const toggle = connectionToggle('Receive with screen off', on, async () => { state = await native(on ? 'background_disable' : 'background_enable'); render(); });
  toggle.disabled = !!state.protection?.enabled;
  const card = element('section', { class: 'connection-card' }, element('div', { class: 'connection-card-heading' }, element('strong', { text: 'Background messages' }), toggle), element('p', { text: state.protection?.enabled ? 'Kept on while App VPN is enabled.' : 'Keep receiving with the screen off. Shows a notification while on.' }));
  if (on && state.notifications_enabled === false) card.append(element('button', { class: 'outline-button', text: 'Allow notifications', onclick: () => run(null, () => native('notification_settings')) }));
  panel.replaceChildren(card);
}
function showConnections() {
  modal('Connections', [element('div', { id: 'nearby-panel' })], 'PARAMO1D'); renderNearbyPanel();
}
function renderNearbyPanel() {
  const panel = $('nearby-panel'); if (!panel) return;
  const scroll = $('modal').scrollTop;
  const nearby = state?.nearby || {}, peers = nearby.peers || [];
  const online = !!state.connection?.online, protection = state.protection || {};
  const trying = !!protection.checking || !!state.connection?.checking;
  const title = online ? 'You are online' : peers.length ? 'Connected by Bluetooth' : trying ? 'Connecting to the internet…' : 'You are offline';
  const summary = online ? 'Messages send now.' : peers.length ? 'Messages travel through nearby phones.' : 'Messages stay saved until you connect.';
  const overview = element('div', { class: 'connection-overview', 'data-online': String(online) }, element('strong', { text: title }), element('p', { text: summary }));
  const internet = element('section', { class: 'connection-card' }, element('div', { class: 'connection-card-heading' }, element('strong', { text: 'Internet' }), element('span', { class: 'connection-badge', 'data-active': String(online), text: online ? 'Connected' : trying ? 'Checking…' : 'Not connected' })), element('p', { text: online ? protection.connected ? 'Connected through App VPN.' : 'Using your normal phone connection.' : 'If your phone has internet but this app cannot connect, turn on App VPN below.' }));
  if (!online) {
    const retry = element('button', { class: 'outline-button', text: trying ? 'Checking connection…' : 'Try again', onclick: () => run(retry, async () => {
      if (!(state.settings?.relays || []).length) state = await native('settings', { relays: ['https://chat.parano1d.org'], rpc: state.settings?.rpc || '' });
      await poll();
    }) });
    retry.disabled = trying; internet.append(retry);
  }
  const vpnOn = !!(protection.enabled || protection.checking || protection.connected);
  const vpnToggle = connectionToggle('App VPN', vpnOn, async () => { state = await native(vpnOn ? 'protection_disable' : 'protection_enable'); render(); });
  vpnToggle.disabled = !!state.chain?.running && !state.chain?.automatic;
  const vpn = element('section', { class: 'connection-card' }, element('div', { class: 'connection-card-heading' }, element('strong', { text: 'App VPN' }), vpnToggle), element('p', { class: 'connection-detail', text: protection.checking ? 'On · connecting…' : vpnOn ? online && protection.connected ? 'On · connected' : 'On · waiting for a connection' : 'Off · using your normal connection' }), element('p', { text: 'For restricted networks. Only Paramo1d uses this VPN.' }));
  if (protection.problem) vpn.append(element('p', { class: 'danger', text: protection.problem }));
  if (state.chain?.running && !state.chain?.automatic) vpn.append(element('p', { text: 'Available after the current wallet check finishes.' }));
  const bluetooth = element('section', { class: 'connection-card' }, element('div', { class: 'connection-card-heading' }, element('strong', { text: 'Bluetooth' }), connectionToggle('Bluetooth messaging', !!nearby.enabled, async () => { state = await native(nearby.enabled ? 'nearby_stop' : 'nearby_start'); render(); })), element('p', { class: 'connection-detail', text: nearby.enabled ? peers.length ? `On · ${peers.length} phone${peers.length === 1 ? '' : 's'} connected` : 'On · no phone connected yet' : 'Off' }), element('p', { text: 'No internet needed. Enable on both phones.' }));
  if (nearby.enabled) {
    for (const peer of peers) bluetooth.append(element('button', { class: 'nearby-device connected', onclick: async () => { $('modal').close(); await openChat(`d:${peer.id}`); } }, element('span', { class: 'avatar', text: initials(peer.name) }), element('span', {}, element('strong', { text: peer.name }), element('small', { text: 'Connected · open chat' })), icon('direct')));
    const controls = peers.length ? element('details', {}, element('summary', { text: 'Connect another phone' })) : bluetooth;
    const search = element('button', { class: 'outline-button', text: nearby.scanning ? 'Looking for phones…' : 'Find a phone', onclick: () => run(search, async () => { state = await native('nearby_scan'); render(); }) });
    search.disabled = !!nearby.scanning;
    controls.append(search, element('button', { class: 'outline-button', text: 'Make this phone visible', onclick: () => run(null, () => native('nearby_visible')) }));
    for (const device of nearby.devices || []) {
      const connect = element('button', { class: 'nearby-device', onclick: () => run(connect, async () => { await native('nearby_connect', { address: device.address }); toast('Connecting to the nearby phone…'); }) }, icon('nearby'), element('span', {}, element('strong', { text: device.name }), element('small', { text: 'Tap to connect' })));
      controls.append(connect);
    }
    if (peers.length) bluetooth.append(controls);
    if (nearby.problem) bluetooth.append(element('p', { class: 'danger', text: nearby.problem }));
  }
  panel.replaceChildren(overview, internet, vpn, bluetooth);
  $('modal').scrollTop = scroll;
}

function showBackup() {
  const password = field('Backup password · at least 12 characters', { type: 'password', autocomplete: 'new-password' });
  const confirm = field('Repeat password', { type: 'password', autocomplete: 'new-password' });
  const save = element('button', { class: 'primary-button', text: 'Save encrypted backup ↗', onclick: () => run(save, async () => {
    if (password.input.value.length < 12 || password.input.value !== confirm.input.value) throw new Error('Use matching passwords with at least 12 characters.');
    await native('backup_export', { password: password.input.value }); password.input.value = ''; confirm.input.value = ''; $('modal').close();
  }) });
  modal('Save a backup', [element('p', { text: 'Restore your wallet and chats if you lose this phone. Choose a password for this backup file and keep it separately.' }), password.label, confirm.label, save], 'BACKUP');
}

function showRestore() {
  const backup = field('Encrypted backup', { multiline: true, placeholder: 'Paste your encrypted backup JSON' });
  const password = field('Backup password', { type: 'password', autocomplete: 'current-password' });
  const restore = element('button', { class: 'primary-button', text: 'Restore identity ↗', onclick: () => run(restore, async () => {
    state = await native('backup_restore', { backup: backup.input.value, password: password.input.value }); password.input.value = ''; backup.input.value = ''; $('modal').close(); render(); await poll();
  }) });
  const file = element('button', { class: 'outline-button', text: 'Choose a backup file ↗', onclick: () => run(file, async () => { await native('backup_restore_file', { password: password.input.value }); password.input.value = ''; }) });
  modal('Restore from a backup', [element('p', { text: 'Enter the password you chose for your backup, then choose the saved file.' }), password.label, file, element('details', { class: 'advanced-settings' }, element('summary', { text: 'Paste backup text instead' }), backup.label, restore)], 'RESTORE');
}

function showInvoice() {
  if (!chat?.startsWith('d:')) return;
  const amount = field('Amount · NOID', { placeholder: '0.00' }); amount.input.inputMode = 'decimal';
  const memo = field('What is it for?', { placeholder: 'Optional note' });
  const send = element('button', { class: 'primary-button', text: 'Send payment request ↗', onclick: () => run(send, async () => {
    state = await native('invoice', { contact_id: chat.slice(2), amount: paymentAmount(amount.input.value), memo: memo.input.value }); $('modal').close(); render(); await poll();
  }) });
  modal('Request a payment.', [amount.label, memo.label, send], 'NOID / REQUEST');
}

function showChatOptions(scope = chat) {
  if (!scope) return;
  const peer = scope.startsWith('d:') ? contact(scope.slice(2)) : null;
  const actions = [];
  if (peer) actions.push(element('button', { class: 'outline-button', text: 'View contact', onclick: () => showContact(peer) }));
  actions.push(element('button', { class: 'outline-button', text: 'Clear history', onclick: () => void ChatStorageUI.open(scope) }), element('button', { class: 'outline-button', text: 'Manage chat storage', onclick: () => void ChatStorageUI.open() }));
  if (peer) actions.push(element('button', { class: 'outline-button danger', text: 'Delete chat', onclick: () => showDeleteConversation(scope) }));
  modal(peer?.name || 'Community', actions, 'CHAT OPTIONS');
}

function showDeleteConversation(scope) {
  const peer = scope.startsWith('d:') ? contact(scope.slice(2)) : null;
  if (!peer) return;
  const remove = element('button', { class: 'primary-button destructive-button', text: 'Delete chat', onclick: () => run(remove, async () => {
    state = await native('delete_conversation', { chat: scope, confirmed: true });
    ChatUI.conversationDeleted(scope);
    if (chat === scope) { chat = ''; tab = 'direct'; }
    $('modal').close(); render(); toast('Chat and contact deleted. New messages can still arrive.');
  }, 'Deleting…') });
  const content = [element('p', { text: `Delete your conversation with ${peer.name} and remove this contact from your list?` }),
    element('p', { text: 'This deletes the message history on this phone. A new message from this person will start a new chat.' })];
  if (chatMessages(scope).some(message => message.status === 'queued')) content.push(element('p', { text: 'Already queued messages will still be delivered.' }));
  content.push(element('button', { class: 'outline-button', text: 'Cancel', onclick: () => $('modal').close() }), remove);
  modal('Delete chat and contact?', content, 'DELETE CHAT');
}

function showActions() {
  if (!chat?.startsWith('d:')) {
    modal('Chat actions', [element('div', { class: 'modal-actions' }, element('button', { class: 'outline-button', text: 'Help send a saved payment', onclick: showBroadcastHelp }), element('button', { class: 'outline-button', text: 'Share my contact', onclick: showInvite }), element('button', { class: 'outline-button', text: 'Add a contact', onclick: showAddContact }))], 'COMMUNITY'); return;
  }
  modal('Payments', [element('div', { class: 'modal-actions' }, element('button', { class: 'outline-button', text: 'Send NOID', onclick: showSend }), element('button', { class: 'outline-button', text: 'Request NOID', onclick: showInvoice }), element('button', { class: 'outline-button', text: 'Share a payment receipt', onclick: showAttachReceipt }))], 'MESSAGES');
}

function showBroadcastHelp() {
  const payments = (state.prepared_payments || []).filter(p => !p.replaced_by && !needsNewApproval(p.delivery_error) && !(state.receipts || []).some(r => r.verified && r.txid === p.txid));
  const items = [element('p', { text: 'Choose a saved payment. Someone with internet can help send it to the network.' })];
  for (const payment of payments.slice(-20).reverse()) items.push(element('button', { class: 'saved-payment-choice', onclick: () => sharePrepared(payment.txid) }, element('strong', { text: `${payment.amount} NOID` }), element('small', { text: `To ${short(payment.to)} · fee ${payment.fee} NOID` }), element('span', { text: 'Ask the community to help' })));
  if (!payments.length) items.push(element('p', { text: 'No payments waiting to send.' }), element('button', { class: 'primary-button', text: 'Open wallet', onclick: () => { $('modal').close(); selectTab('wallet'); } }));
  const packet = field('Payment data', { multiline: true, placeholder: 'Paste exported payment data' });
  const send = element('button', { class: 'outline-button', text: 'Share imported payment', onclick: () => run(send, async () => { state = await native('send', { chat: 'g:parano1d', message: { type: 'transaction', intent_hex: packet.input.value.trim() } }); $('modal').close(); render(); }) });
  items.push(element('details', { class: 'advanced-settings' }, element('summary', { text: 'Import payment data' }), packet.label, send));
  modal('Ask for help sending a payment', items, 'COMMUNITY');
}

function showSend() {
  const peer = chat?.startsWith('d:') ? contact(chat.slice(2)) : null;
  const address = field('Recipient NOID address', { value: peer?.address || '', placeholder: 'o1…' });
  const amount = field('Amount · NOID', { placeholder: '0.00' }); amount.input.inputMode = 'decimal';
  const button = element('button', { class: 'primary-button', text: 'Review payment ↗', onclick: () => reviewPayment(address.input.value.trim(), amount.input.value, '', button) });
  modal('Send NOID.', [scannedField('address', address), amount.label, element('p', { text: state.connection?.online ? 'Review the amount and fee before sending.' : 'Use the balance last checked on this phone. A nearby person can carry your payment to the network.' }), button], 'NOID / SEND');
}

async function reviewPayment(address, amount, invoiceId, button, useCached = !!state?.chain?.height || !state?.connection?.online, replacesTxid = '') {
  await run(button, async () => {
    amount = paymentAmount(amount);
    if (!address) throw new Error('Enter the recipient’s NOID address.');
    toast(useCached ? 'Preparing from your saved balance…' : 'Updating your wallet and preparing the payment…');
    const review = await native('payment_preview', { address, amount, invoice_id: invoiceId, chat: chat?.startsWith('d:') ? chat : '', use_cached: useCached, replaces_txid: replacesTxid });
    const rows = [['To', review.to], ['Amount', `${review.amount} NOID`], ['Network fee', `${review.fee} NOID`], ['Total', `${review.total} NOID`]]
      .map(([key, value]) => element('div', { class: 'review-row' }, element('span', { text: key }), element('span', { text: value })));
    const approve = element('button', { class: 'primary-button', text: 'Send payment ↗', onclick: () => run(approve, async () => {
      const sent = await native('payment_send', { review_id: review.review_id }); state = sent.state; render();
      const help = element('button', { class: 'primary-button', text: 'Ask the community to help ↗', onclick: () => sharePrepared(sent.txid) });
      modal(sent.submitted ? 'Payment sent' : sent.delivery_queued ? 'Sending your payment' : 'Payment saved on this phone', [element('p', { text: sent.submitted ? 'Waiting for confirmation. Follow the payment in your wallet or chat.' : sent.delivery_queued ? 'Your payment is saved and is being sent to the network. Follow its status in your wallet or chat.' : 'It will need to reach the network to confirm. Ask the community to help send it.' }), element('button', { class: 'primary-button', text: 'View in wallet', onclick: () => { $('modal').close(); selectTab('wallet'); } }), help, element('details', { class: 'advanced-settings' }, element('summary', { text: 'Payment details' }), element('div', { class: 'detail', text: sent.txid }))], 'PAYMENT');
    }, 'Sending…') });
    const validity = element('p', { text: 'Send it soon. If the payment expires before reaching the network, you will need to approve a new one.' });
    if (review.valid_through_height) validity.append(element('details', { class: 'payment-validity-details' }, element('summary', { text: 'Payment timing' }), element('small', { text: `The network can accept this payment through block ${Number(review.valid_through_height).toLocaleString()}.` })));
    modal('Check your payment.', [...rows, element('p', { text: review.using_saved_state ? 'Using the balance last checked on this phone.' : 'Check the recipient, amount and fee before sending.' }), validity, approve], 'AUTHORIZE');
  }, 'Preparing…');
}

function showAttachReceipt() {
  const invoice = chatMessages(chat).filter(m => m.message.type === 'invoice' && m.sender.id !== state.profile.id).at(-1)?.message;
  if (!invoice) { toast('Ask this contact to send a payment request first.'); return; }
  const items = [element('p', { text: 'Choose a checked payment receipt to send to this contact.' })];
  const receipts = (state.receipts || []).filter(r => r.verified);
  for (const receipt of receipts.slice(-20).reverse()) items.push(element('button', { class: 'saved-payment-choice', onclick: () => run(null, async () => { state = await native('share_receipt', { chat, txid: receipt.txid, invoice_id: invoice.invoice_id }); $('modal').close(); render(); }) }, element('strong', { text: receipt.amount ? `${receipt.amount} NOID` : 'Checked payment' }), element('small', { text: short(receipt.txid) }), element('span', { text: 'Send receipt' })));
  if (!receipts.length) items.push(element('p', { text: 'No checked receipts yet. Check a payment first, then its receipt will appear here.' }));
  const receipt = field('Receipt data', { multiline: true, placeholder: 'Paste exported receipt data' });
  const send = element('button', { class: 'outline-button', text: 'Send imported receipt', onclick: () => run(send, async () => { state = await native('send', { chat, message: { type: 'receipt', invoice_id: invoice.invoice_id, receipt_hex: receipt.input.value.trim() } }); $('modal').close(); render(); }) });
  items.push(element('details', { class: 'advanced-settings' }, element('summary', { text: 'Import receipt data' }), receipt.label, send));
  modal('Share a payment receipt', items, 'PAYMENTS');
}

async function verifyMessageReceipt(item) {
  const invoice = chatMessages(item.chat).find((m) => m.message.type === 'invoice' && m.message.invoice_id === item.message.invoice_id)?.message;
  if (!invoice) { toast('The original payment request is needed to check this receipt.'); return; }
  await run(null, async () => {
    toast('Checking the receipt against the verified chain…');
    const result = await native('receipt_verify', { receipt_hex: item.message.receipt_hex, invoice_id: invoice.invoice_id, address: invoice.address, amount: invoice.amount, message_id: item.id });
    state = result.state; render(); showReceipt(result.receipt);
  });
}

function showReceipt(receipt) {
  const amount = receipt.amount || (state.prepared_payments || []).find(p => p.txid === receipt.txid)?.amount;
  modal('Payment verified.', [element('strong', { class: 'receipt-amount', text: amount ? `${amount} NOID` : 'Payment included in the blockchain' }), element('p', { text: `Checked on this phone. ${receipt.finalized ? 'Final confirmation reached.' : `${receipt.confirmations || 1} confirmations when checked.`}` }), element('details', { class: 'advanced-settings' }, element('summary', { text: 'Payment details' }), element('p', { text: `Block ${receipt.height}` }), element('div', { class: 'detail', text: receipt.txid }), element('button', { class: 'outline-button', text: 'Copy transaction ID', onclick: () => copy(receipt.txid) }))], 'PAYMENT RECEIPT');
}

function showImportReceipt() {
  const receipt = field('Payment receipt', { multiline: true });
  const amount = field('Expected amount · NOID', { placeholder: '0.00' });
  const button = element('button', { class: 'primary-button', text: 'Verify receipt ↗', onclick: () => run(button, async () => {
    const result = await native('receipt_verify', { receipt_hex: receipt.input.value.trim(), address: state.profile.address, amount: amount.input.value, invoice_id: '', message_id: '' });
    state = result.state; render(); showReceipt(result.receipt);
  }) });
  modal('Check a payment.', [receipt.label, amount.label, button], 'IMPORT RECEIPT');
}

async function copy(text) { await run(null, async () => { await native('copy', { text }); toast('Copied.'); }); }
async function poll() {
  if (polling || !state?.profile || document.hidden) return;
  polling = true;
  try { state = await native('poll'); render(); }
  catch (error) { state.connection = { online: false }; renderConnection(); }
  finally { polling = false; }
}
window.paramo1dBack = () => {
  if ($('modal').open) { $('modal').close(); return true; }
  if (ChatUI.back()) return true;
  if (chat?.startsWith('d:')) { ChatUI.beforeSwitch(); chat = null; render(); return true; }
  if (tab !== 'groups') { selectTab('groups'); return true; }
  return false;
};
function selectTab(value) { ChatUI.beforeSwitch(); tab = value; chat = value === 'groups' ? 'g:parano1d' : null; $('search').value = ''; render(); }

$('create-identity-form').addEventListener('submit', (event) => { event.preventDefault(); run(event.submitter, async () => { state = await native('create_identity', { name: $('display-name').value.trim() }); render(); await poll(); }); });
ChatUI.setup();
$('compose').addEventListener('keydown', (event) => { if (event.key === 'Enter' && !event.shiftKey && !event.isComposing && matchMedia('(min-width:761px)').matches) { event.preventDefault(); $('compose-form').requestSubmit(); } });
document.querySelectorAll('[data-tab]').forEach((button) => button.addEventListener('click', () => selectTab(button.dataset.tab)));
$('search').addEventListener('input', renderConversations);
$('home-button').addEventListener('click', () => selectTab('groups'));
$('back-button').addEventListener('click', () => { ChatUI.beforeSwitch(); chat = null; render(); });
$('new-button').addEventListener('click', showAddContact);
$('settings-button').addEventListener('click', () => state?.profile ? showSettings() : toast('Create or restore your identity first.'));
$('connection').addEventListener('click', () => state?.profile ? showConnections() : toast('Create or restore your identity first.'));
$('identity-button').addEventListener('click', showInvite);
$('invite-button').addEventListener('click', showInvite);
$('welcome-group').addEventListener('click', () => openChat('g:parano1d'));
$('close-modal').addEventListener('click', () => $('modal').close());
$('modal').addEventListener('close', render);
$('message-scroll').addEventListener('scroll', () => { const s = $('message-scroll'); if (s.scrollHeight - s.scrollTop - s.clientHeight < 100) markCurrentRead(); }, { passive: true });
$('restore-button').addEventListener('click', showRestore);
$('payment-button').addEventListener('click', showSend);
$('attachment-button').addEventListener('click', showActions);
$('chat-options-button').addEventListener('click', () => showChatOptions());
$('chat-profile').addEventListener('click', () => { if (chat?.startsWith('d:')) showContact(contact(chat.slice(2))); });
$('wallet-address').addEventListener('click', () => copy(state.profile.address));
$('receive-button').addEventListener('click', () => {
  const children = [element('p', { text: 'Scan this code or copy the address to receive NOID.' })];
  if (window.qrcode) {
    const code = qrcode(0, 'M'); code.addData(state.profile.address); code.make();
    const box = element('div', { class: 'qr' });
    const svg = new DOMParser().parseFromString(code.createSvgTag({ scalable: true, margin: 4 }), 'image/svg+xml').documentElement;
    box.append(document.importNode(svg, true)); children.push(box);
  }
  children.push(element('div', { class: 'detail', text: state.profile.address }), element('button', { class: 'primary-button', text: 'Copy address ↗', onclick: () => copy(state.profile.address) }));
  modal('Receive NOID.', children, 'RECEIVE');
});
$('send-button').addEventListener('click', showSend);
$('import-receipt-button').addEventListener('click', showImportReceipt);
$('sync-button').addEventListener('click', () => run(null, async () => {
  if (walletBusy) return;
  walletBusy = true; renderWallet();
  try { const before = state.chain?.balance; state = await native('sync'); render(); toast(state.chain?.running && state.chain?.automatic ? 'Your wallet is updating in the background.' : state.chain?.balance === before ? 'No new payments.' : 'Balance updated.'); }
  finally { walletBusy = false; renderWallet(); }
}));
document.addEventListener('visibilitychange', () => { reportVisibleChat(); clearInterval(pollTimer); if (!document.hidden) { poll(); pollTimer = setInterval(poll, 10000); } });
window.paramo1dOpenContact = (uri) => run(null, async () => { state = await native('import_contact', { uri }); render(); toast('Contact added.'); });
window.paramo1dOpenChat = (key) => { if (/^d:[0-9a-f]{64}$/.test(key)) { $('modal').close(); return openChat(key); } };

(async () => {
  try { state = await native('boot'); render(); }
  catch (error) { $('onboarding').hidden = false; if (window.Paramo1d) toast(error.message); }
  finally { window.Paramo1d?.ready?.(); }
  await poll(); pollTimer = setInterval(poll, 10000);
})();
