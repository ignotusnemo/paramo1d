'use strict';

window.ChatStorageUI = (() => {
  let noticeShown = false, current = null;
  const PAGE = 50;
  function size(value) {
    const bytes = Math.max(0, Number(value) || 0);
    if (bytes < 1024) return `${bytes} B`;
    if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
    return `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
  }
  function isFullError(message = '') { return /(?:app|local) storage is full/i.test(message); }
  function renderNotice() {
    const banner = $('storage-alert'), full = !!state?.profile && !!state.storage_full;
    banner.hidden = !full;
    $('storage-manage').onclick = () => void open();
    if (!full) noticeShown = false;
    if (!$('modal').open || $('modal').dataset.kind !== 'STORAGE') current = null;
    if (full && !noticeShown && !$('modal').open && !walletBusy && !scanContext) {
      noticeShown = true;
      queueMicrotask(() => {
        if (state?.storage_full && !$('modal').open && !walletBusy) void open();
        else noticeShown = false;
      });
    }
  }
  function reportFull() {
    if (state) state.storage_full = true;
    noticeShown = true; renderNotice(); void open();
  }
  async function open(initialChat = '') {
    noticeShown = !!state?.storage_full;
    const view = { selected: new Set(initialChat ? [initialChat] : []), initialChat, query: '', limit: PAGE };
    current = view;
    modal('Chat storage', [element('p', { text: 'Loading chats…' })], 'STORAGE');
    try {
      view.stats = await native('chat_storage');
      if (current !== view || !$('modal').open || $('modal').dataset.kind !== 'STORAGE') return;
      for (const id of view.selected) if (!view.stats.chats.some(row => row.id === id && row.clearable > 0)) view.selected.delete(id);
      build(view);
    } catch (error) {
      if (current !== view || !$('modal').open) return;
      $('modal-content').replaceChildren(element('p', { text: 'Chat storage could not be loaded.' }), element('button', { class: 'primary-button', text: 'Try again', onclick: () => void open() }));
    }
  }
  function build(view) {
    const stats = view.stats, body = $('modal-content'); body.replaceChildren();
    if (stats.full || state.storage_full) body.append(element('section', { class: 'storage-warning', role: 'status' }, element('strong', { text: 'Storage is full' }), element('p', { text: 'Choose chats to clear so new messages can arrive.' })));
    else body.append(element('p', { text: 'Choose the chats to clear on this phone.' }));
    body.append(element('p', { class: 'storage-usage', text: `${Number(stats.messages).toLocaleString()} / ${Number(stats.message_limit).toLocaleString()} messages · ${size(stats.used_bytes)} used` }));
    const rows = stats.chats || [], eligible = rows.filter(row => row.clearable > 0);
    const controls = element('div', { class: 'storage-controls' });
    const all = element('button', { class: 'text-button', text: 'Select all', onclick: () => {
      const selected = eligible.every(row => view.selected.has(row.id));
      for (const row of eligible) selected ? view.selected.delete(row.id) : view.selected.add(row.id);
      paint();
    } }); all.disabled = !eligible.length;
    controls.append(all, element('button', { class: 'text-button', text: 'Save a backup', onclick: showBackup })); body.append(controls);
    let search;
    if (rows.length > 9) {
      search = element('input', { type: 'search', placeholder: 'Find a chat', 'aria-label': 'Find a chat' });
      search.addEventListener('input', () => { view.query = search.value.toLocaleLowerCase().trim(); view.limit = PAGE; paint(); }); body.append(search);
    }
    const list = element('div', { class: 'storage-chats' }); body.append(list);
    const summary = element('p', { class: 'storage-selection', 'aria-live': 'polite' });
    const clear = element('button', { class: 'primary-button', text: 'Clear selected history', onclick: () => run(clear, async () => {
      const chats = [...view.selected];
      state = await native('clear_history', { chats, confirmed: true });
      ChatUI.historyCleared(chats);
      if (state.storage_full) { await open(); toast('Clear more history to make room for new messages.'); }
      else { $('modal').close(); render(); toast('Selected history cleared. Your wallet and queued messages are kept.'); }
    }) });
    body.append(element('div', { class: 'storage-footer' }, summary, clear, element('p', { class: 'storage-preserved', text: 'Contacts, wallet, queued messages and saved payment records are kept.' })));
    function paint() {
      const focused = document.activeElement?.closest('.storage-chat')?.dataset.chat;
      list.replaceChildren();
      const filtered = rows.filter(row => !view.query || `${row.name} ${row.id}`.toLocaleLowerCase().includes(view.query));
      const community = filtered.find(row => row.id === 'g:parano1d');
      const privateChats = filtered.filter(row => row.id !== 'g:parano1d').sort((a, b) => Number(b.id === view.initialChat) - Number(a.id === view.initialChat) || b.clearable_bytes - a.clearable_bytes || a.name.localeCompare(b.name));
      if (community) list.append(rowNode(community));
      if (privateChats.length) list.append(element('h3', { class: 'storage-group', text: 'Private chats' }));
      for (const row of privateChats.slice(0, view.limit)) list.append(rowNode(row));
      if (privateChats.length > view.limit) list.append(element('button', { class: 'outline-button', text: 'Show more chats', onclick: () => { view.limit += PAGE; paint(); } }));
      if (!filtered.length) list.append(element('p', { class: 'storage-empty', text: 'No matching chats.' }));
      if (!eligible.length) list.append(element('p', { class: 'storage-empty', text: rows.some(row => row.queued) ? 'The remaining messages are waiting to send. Reconnect to deliver them before clearing their history.' : 'There is no chat history to clear.' }));
      const selected = rows.filter(row => view.selected.has(row.id)), bytes = selected.reduce((total, row) => total + Number(row.clearable_bytes), 0);
      summary.textContent = selected.length ? `${selected.length} ${selected.length === 1 ? 'chat' : 'chats'} selected · About ${size(bytes)} to clear` : 'Select Community or any private chats.';
      clear.disabled = selected.length === 0;
      all.textContent = eligible.length && eligible.every(row => view.selected.has(row.id)) ? 'Deselect all' : 'Select all';
      if (focused) [...list.querySelectorAll('.storage-chat')].find(row => row.dataset.chat === focused)?.querySelector('input').focus({ preventScroll: true });
    }
    function rowNode(row) {
      const checkbox = element('input', { type: 'checkbox', 'aria-label': row.name }); checkbox.checked = view.selected.has(row.id); checkbox.disabled = row.clearable === 0;
      checkbox.addEventListener('change', () => { checkbox.checked ? view.selected.add(row.id) : view.selected.delete(row.id); paint(); });
      const detail = `${Number(row.messages).toLocaleString()} ${row.messages === 1 ? 'message' : 'messages'} · ${size(row.bytes)}`;
      const description = element('span', { class: 'storage-chat-copy' }, element('strong', { text: row.name }), element('small', { text: detail }));
      if (row.queued) description.append(element('small', { text: `${row.queued} waiting to send will be kept` }));
      const label = element('label', { class: 'storage-chat' }, checkbox, description); label.dataset.chat = row.id;
      if (checkbox.checked) label.classList.add('selected');
      return label;
    }
    paint();
  }
  return { open, renderNotice, isFullError, reportFull };
})();
