'use strict';

window.ChatUI = (() => {
  const PAGE = 120;
  const drafts = new Map(), draftTimers = new Map(), rows = new Map(), cards = new Map();
  const previewQueue = [];
  let previewWorkers = 0, currentChat = '', renderKey = '', rangeStart = null, rangeEnd = null;
  let lastStart = 0, lastEnd = 0, lastTotal = 0, sending = false, replyId = '', caret = [0, 0];
  let searchMatches = [], searchIndex = 0, searchQuery = '', recentEmoji = [];
  let followLatest = true, lastScrollTop = 0, bottomFrame = 0;
  const quickEmoji = ['👍', '❤️', '😂', '🔥', '😮', '🙏'];
  const emojiGroups = {
    Smileys: ['😀','😃','😄','😁','😆','😅','😂','🤣','😊','🙂','🙃','😉','😍','🥰','😘','😎','🤓','🥳','🤔','🫡','🤨','😐','🙄','😏','😴','😭','😢','😤','😡','🤯','😱','😬','🫠','🥹','🤗','🤫'],
    Gestures: ['👍','👎','👋','🤚','✋','👌','🤌','🤏','✌️','🤞','🫰','🤟','🤘','🤙','👈','👉','👆','👇','☝️','✊','👊','🤛','🤜','👏','🙌','👐','🤝','🙏','💪','🫶'],
    Hearts: ['❤️','🧡','💛','💚','💙','💜','🖤','🤍','🤎','🩷','🩵','🩶','💔','❤️‍🔥','💕','💞','💓','💗','💖','💘','💝','💟','❣️','💯'],
    More: ['🔥','✨','⭐','🌟','💫','⚡','☀️','🌙','🌍','🚀','🛸','💎','🪙','💰','🎉','🎊','🎁','🏆','✅','❌','❓','❗','👀','🧠','🤖','👻','💀','🐈','🐕','☕','🍕','🍺','🥂','🎵','🛠️','🔒'],
  };
  let emojiCategory = 'Smileys';
  const cardObserver = typeof IntersectionObserver === 'function' ? new IntersectionObserver(entries => {
    for (const entry of entries) if (entry.isIntersecting && !document.hidden) {
      cardObserver.unobserve(entry.target); hydrateContact(entry.target, entry.target.dataset.contactUri);
    }
  }, { rootMargin: '160px' }) : null;

  function textOf(item) {
    const message = item.message;
    if (message.type === 'text') {
      const text = ChatText.parse(message.text).text;
      return ChatText.contacts(text).length ? 'Shared a contact' : text;
    }
    if (message.type === 'invoice') return `Payment request · ${message.amount} NOID`;
    if (message.type === 'receipt') return 'Payment receipt';
    if (message.type === 'transaction') return 'Approved NOID payment';
    return 'Payment update';
  }
  function reactionOf(item) {
    if (item.message.type !== 'text') return null;
    const parsed = ChatText.parse(item.message.text);
    if (!parsed.reply) return null;
    if (parsed.text === 'Reaction removed.') return { target: parsed.reply.id, emoji: '' };
    const match = parsed.text.match(/^Reaction: (.+)$/u);
    return match && quickEmoji.includes(match[1]) ? { target: parsed.reply.id, emoji: match[1] } : null;
  }
  function preview(message) {
    if (message.type === 'text') {
      const parsed = ChatText.parse(message.text);
      return ChatText.contacts(parsed.text).length ? 'Shared a contact' : parsed.text.startsWith('Reaction: ') && parsed.reply ? `${parsed.text.slice(10)} Reaction` : parsed.text;
    }
    return textOf({ message });
  }
  function history() { return chatMessages(chat).slice().sort((a, b) => a.created_ms - b.created_ms || a.id.localeCompare(b.id)); }
  function isBottom() { const s = $('message-scroll'); return s.scrollHeight - s.scrollTop - s.clientHeight < 90; }
  function snapToBottom() {
    if (!followLatest || !currentChat || currentChat !== chat || $('chat-panel').hidden) return;
    const scroller = $('message-scroll');
    scroller.scrollTop = scroller.scrollHeight; lastScrollTop = scroller.scrollTop; updateJump();
  }
  function queueBottom() {
    if (!followLatest || bottomFrame) return;
    bottomFrame = requestAnimationFrame(() => { bottomFrame = 0; snapToBottom(); });
  }
  function draft(scope = chat) { return drafts.get(scope) || state?.drafts?.[scope] || { text: '', reply_to: '' }; }
  function keepDraft() {
    if (!currentChat) return;
    drafts.set(currentChat, { text: $('compose').value, reply_to: replyId });
  }
  function persistDraft(scope = currentChat) {
    clearTimeout(draftTimers.get(scope));
    if (!scope || !drafts.has(scope) || !state?.profile) return;
    const value = { ...drafts.get(scope) };
    if (ChatText.bytes(value.text) > 4096) return;
    native('save_draft', { chat: scope, ...value }).catch(() => {});
  }
  function beforeSwitch() {
    keepDraft(); persistDraft(); closeEmoji(); closeSearch();
  }
  function composer() {
    const original = state?.messages?.find(item => item.id === replyId && item.chat === chat);
    $('reply-preview').hidden = !replyId;
    $('reply-preview-author').textContent = original ? `Replying to ${original.sender.name}` : 'Replying to a message';
    $('reply-preview-text').textContent = original ? textOf(original).slice(0, 180) : 'Original message is not saved on this phone.';
    const plain = $('compose').value;
    let encoded = plain.trim();
    if (original && encoded) encoded = ChatText.reply(encoded, original, textOf(original));
    const bytes = ChatText.bytes(encoded);
    const send = $('compose-form').querySelector('[type="submit"]');
    send.disabled = sending || !plain.trim() || bytes > 4096 || !!replyId && !original;
    send.setAttribute('aria-busy', String(sending));
    $('compose-limit').hidden = bytes < 3600;
    $('compose-limit').textContent = bytes > 4096 ? 'Message too long' : `${bytes.toLocaleString('en')} / 4,096`;
    $('compose-limit').classList.toggle('danger', bytes > 4096);
    $('compose').style.height = 'auto';
    $('compose').style.height = `${Math.min(144, Math.max(26, $('compose').scrollHeight - 16))}px`;
  }
  function inputChanged() {
    keepDraft(); composer();
    clearTimeout(draftTimers.get(currentChat));
    const scope = currentChat;
    draftTimers.set(scope, setTimeout(() => persistDraft(scope), 3000));
  }
  function reply(item) {
    replyId = item.id; closeEmoji(); $('modal').close(); composer(); keepDraft(); $('compose').focus();
  }
  function plainText(parent, text) {
    const links = /https?:\/\/[^\s<>]+/g;
    let at = 0;
    for (const match of text.matchAll(links)) {
      parent.append(document.createTextNode(text.slice(at, match.index)));
      const url = match[0].replace(/[.,!?;:)\]}]+$/g, '');
      const link = element('a', { href: url, text: url, onclick: event => { event.preventDefault(); run(null, () => native('open_link', { url })); } });
      parent.append(link, document.createTextNode(match[0].slice(url.length)));
      at = match.index + match[0].length;
    }
    parent.append(document.createTextNode(text.slice(at)));
  }
  function requestContact(uri) {
    if (cards.has(uri)) return cards.get(uri);
    if (cards.size >= 256) cards.delete(cards.keys().next().value);
    const promise = new Promise(resolve => { previewQueue.push({ uri, resolve }); pumpPreviews(); });
    cards.set(uri, promise); return promise;
  }
  function pumpPreviews() {
    while (previewWorkers < 2 && previewQueue.length) {
      const job = previewQueue.shift(); previewWorkers++;
      native('preview_contact', { uri: job.uri }).then(result => job.resolve(result.contact)).catch(() => { cards.delete(job.uri); job.resolve(null); }).finally(() => { previewWorkers--; pumpPreviews(); });
    }
  }
  function contactCard(uri) {
    const card = element('div', { class: 'contact-card', 'data-contact-uri': uri }, element('span', { class: 'contact-card-kind', text: 'PARAMO1D CONTACT' }), element('div', { class: 'contact-card-person' }, element('span', { class: 'avatar' }, icon('direct')), element('span', {}, element('strong', { text: 'Contact' }), element('small', { text: 'Checking contact link…' }))), element('button', { class: 'contact-copy', 'aria-label': 'Copy contact link', onclick: () => copy(uri) }, icon('copy'), 'Copy link'));
    if (cardObserver) cardObserver.observe(card);
    else queueMicrotask(() => hydrateContact(card, uri));
    return card;
  }
  async function hydrateContact(card, uri) {
    const peer = await requestContact(uri);
    if (!card.isConnected) return;
    const person = card.querySelector('.contact-card-person');
    if (!peer) {
      person.querySelector('small').textContent = 'Could not check this contact. Try again or ask for a new link.';
      card.classList.add('invalid');
      if (!card.querySelector('.contact-retry')) card.append(element('button', { class: 'contact-copy contact-retry', text: 'Try again', onclick: event => {
        event.currentTarget.remove(); card.classList.remove('invalid'); person.querySelector('small').textContent = 'Checking contact link…'; hydrateContact(card, uri);
      } }));
      return;
    }
    card.classList.remove('invalid'); card.querySelector('.contact-retry')?.remove();
    person.replaceChildren(WarriorAvatar.node(peer.id, peer.name), element('span', {}, element('strong', { text: peer.name }), element('small', { text: short(peer.id) })));
    const actions = element('div', { class: 'contact-card-actions' });
    const own = peer.id === state.profile.id, added = !!contact(peer.id);
    if (!own) {
      actions.append(element('button', { class: 'contact-primary', text: added ? 'Message' : 'Add contact', onclick: event => run(event.currentTarget, async () => {
        const alreadyAdded = !!contact(peer.id);
        state = await native('import_contact', { uri });
        if (alreadyAdded) await openChat(`d:${peer.id}`);
        else { await hydrateContact(card, uri); render(); toast('Contact added.'); }
      }) }));
      if (!added) actions.append(element('button', { class: 'contact-secondary', text: 'Message', onclick: event => run(event.currentTarget, async () => { state = await native('import_contact', { uri }); await openChat(`d:${peer.id}`); }) }));
    } else actions.append(element('span', { class: 'contact-self', text: 'Your contact' }));
    const details = element('details', { class: 'contact-link-details' }, element('summary', { text: 'Contact link' }), element('div', { class: 'selectable-contact-link', text: uri }));
    card.querySelector('.contact-card-actions')?.remove(); card.querySelector('details')?.remove(); card.append(actions, details);
  }
  function messageText(item, allById) {
    const parsed = ChatText.parse(item.message.text);
    const fragment = document.createDocumentFragment();
    if (parsed.reply) {
      const original = allById.get(parsed.reply.id);
      const quote = element('button', { class: 'message-quote', 'aria-label': 'Go to original message', onclick: () => jumpTo(parsed.reply.id) }, element('strong', { text: original ? original.sender.name : 'Quoted message' }), element('span', { text: original ? textOf(original) : parsed.reply.excerpt }));
      fragment.append(quote);
    }
    const contacts = ChatText.contacts(parsed.text).slice(0, 4);
    let at = 0;
    for (const link of contacts) {
      if (link.at > at) { const text = element('span', { class: 'message-text' }); plainText(text, parsed.text.slice(at, link.at)); fragment.append(text); }
      fragment.append(contactCard(link.uri)); at = link.at + link.uri.length;
    }
    if (at < parsed.text.length || !contacts.length) {
      const text = element('span', { class: 'message-text' }); plainText(text, parsed.text.slice(at)); fragment.append(text);
    }
    return fragment;
  }
  function status(item) {
    if (item.status === 'sent') return { icon: 'check', label: 'Sent to the relay' };
    if (item.nearby_delivered) return { icon: 'nearby', label: 'Shared over Bluetooth' };
    if (item.status === 'expired') return { icon: 'close', label: 'Not sent. Message expired.' };
    return { icon: 'clock', label: 'Saved. Waiting for a connection.' };
  }
  function hold(node, item) {
    let timer, point;
    const cancel = () => { clearTimeout(timer); point = null; };
    node.addEventListener('pointerdown', event => {
      if (event.button !== 0 || event.target.closest('button,a,summary,input,textarea')) return;
      point = [event.clientX, event.clientY]; timer = setTimeout(() => { point = null; messageMenu(item); }, 480);
    });
    node.addEventListener('pointermove', event => { if (point && Math.hypot(event.clientX - point[0], event.clientY - point[1]) > 9) cancel(); });
    for (const name of ['pointerup', 'pointercancel', 'pointerleave']) node.addEventListener(name, cancel);
    node.addEventListener('contextmenu', event => { if (!event.target.closest('a,input,textarea')) { event.preventDefault(); cancel(); messageMenu(item); } });
  }
  function buildRow(item, previous, allById, reactions) {
    const mine = item.sender.id === state.profile.id, direct = chat.startsWith('d:');
    const grouped = previous && previous.sender.id === item.sender.id && item.created_ms - previous.created_ms < 4 * 60000 && new Date(item.created_ms).toDateString() === new Date(previous.created_ms).toDateString();
    const article = element('article', { id: `message-${item.id}`, class: `message${mine ? ' mine' : ''}${grouped ? ' grouped' : ''}${item.message.type !== 'text' ? ' payment-message' : ''}`, 'data-message-id': item.id });
    if (item.message.type === 'text' && ChatText.contacts(ChatText.parse(item.message.text).text).length) article.classList.add('contact-message');
    if (!mine && !direct) article.append(WarriorAvatar.node(item.sender.id, item.sender.name, 'button', { class: 'avatar message-avatar', onclick: () => showContact(item.sender), 'aria-label': `Open ${item.sender.name}` }));
    const body = element('div', { class: 'message-body' });
    if (!mine && !direct && !grouped) body.append(element('button', { class: `message-author color-${parseInt(item.sender.id.slice(0, 2), 16) % 6 || 0}`, text: item.sender.name, onclick: () => showContact(item.sender) }));
    if (item.message.type === 'text') body.append(messageText(item, allById));
    else body.append(paymentCard(item, mine));
    const footer = element('span', { class: 'message-footer' }, element('time', { text: time(item.created_ms), datetime: new Date(item.created_ms).toISOString() }));
    if (mine) {
      const delivery = status(item); footer.append(element('span', { class: `delivery-state ${delivery.icon}`, 'aria-label': delivery.label, title: delivery.label }, icon(delivery.icon)));
    } else if (item.via_nearby) footer.append(element('span', { class: 'delivery-state', title: 'Received over Bluetooth', 'aria-label': 'Received over Bluetooth' }, icon('nearby')));
    body.append(footer); article.append(body, element('button', { class: 'message-more', 'aria-label': `Message options for ${item.sender.name}`, onclick: () => messageMenu(item) }, icon('more')));
    hold(body, item);
    if (reactions?.size) {
      const strip = element('div', { class: 'message-reactions' });
      const counts = new Map();
      for (const reaction of reactions.values()) if (reaction.emoji) { if (!counts.has(reaction.emoji)) counts.set(reaction.emoji, []); counts.get(reaction.emoji).push(reaction); }
      for (const [emoji, members] of counts) strip.append(element('button', { class: `reaction-chip${members.some(r => r.sender.id === state.profile.id) ? ' mine' : ''}`, text: `${emoji} ${members.length}`, title: members.map(r => r.sender.name).join(', '), 'aria-label': `${emoji}, ${members.length} reactions`, onclick: () => react(item, emoji) }));
      if (strip.children.length) { body.append(strip); article.classList.add('has-reactions'); }
    }
    return article;
  }
  function dayLabel(ms) {
    const day = new Date(ms), now = new Date(), yesterday = new Date(); yesterday.setDate(now.getDate() - 1);
    if (day.toDateString() === now.toDateString()) return 'Today';
    if (day.toDateString() === yesterday.toDateString()) return 'Yesterday';
    return day.toLocaleDateString('en', { day: 'numeric', month: 'short', ...(day.getFullYear() !== now.getFullYear() ? { year: 'numeric' } : {}) });
  }
  function renderChat() {
    if (!chat || !state?.profile) return;
    const switched = currentChat !== chat;
    if (switched) {
      for (const cached of rows.values()) for (const card of cached.node.querySelectorAll('.contact-card')) cardObserver?.unobserve(card);
      currentChat = chat; renderKey = ''; rangeStart = null; rangeEnd = null; rows.clear();
      followLatest = true; lastScrollTop = 0;
      const saved = draft(chat); $('compose').value = saved.text || ''; replyId = saved.reply_to || '';
    }
    const direct = chat.startsWith('d:'), peer = direct ? contact(chat.slice(2)) : null;
    $('chat-name').textContent = direct ? peer?.name || 'Contact' : '#parano1d';
    if (direct && peer) WarriorAvatar.paint($('chat-avatar'), peer.id, peer.name);
    else { $('chat-avatar').classList.remove('warrior-avatar'); $('chat-avatar').replaceChildren(icon('community')); }
    $('chat-description').textContent = direct ? 'Encrypted conversation' : 'Public community';
    $('chat-context').hidden = !state.storage_full;
    $('chat-context').textContent = state.storage_full ? 'Storage is full. Tap Choose chats above to clear some history.' : '';
    $('payment-button').hidden = !direct; $('back-button').hidden = !direct; $('attachment-button').hidden = false;
    composer();
    const full = history(), byId = new Map(full.map(item => [item.id, item])), reactions = new Map();
    for (const item of full) {
      const reaction = reactionOf(item);
      if (reaction && byId.has(reaction.target)) {
        if (!reactions.has(reaction.target)) reactions.set(reaction.target, new Map());
        reactions.get(reaction.target).set(item.sender.id, { emoji: reaction.emoji, sender: item.sender });
      }
    }
    const messages = full.filter(item => { const reaction = reactionOf(item); return !reaction || !byId.has(reaction.target); });
    const scroller = $('message-scroll'), bottom = switched || followLatest || isBottom();
    const start = Math.min(rangeStart ?? Math.max(0, messages.length - PAGE), messages.length);
    const end = Math.min(rangeEnd ?? messages.length, messages.length);
    const visible = messages.slice(start, end);
    const financial = JSON.stringify([
      (state.receipts || []).map(r => [r.txid, r.message_id, r.invoice_id, r.height, r.verified, r.finalized, r.amount]),
      (state.observations || []).map(o => [o.id, o.message.txid, o.message.stage, o.message.receipt_hex?.length]),
      full.filter(item => item.message.type === 'receipt').map(item => [item.id, item.message.invoice_id]),
      state.prepared_payments,
    ]);
    const signatures = visible.map((item, i) => {
      const reference = item.message.type === 'text' && ChatText.parse(item.message.text).reply;
      return JSON.stringify([item.id, item.sender.name, item.created_ms, item.status, item.via_nearby, item.nearby_delivered, item.broadcast_error, item.payment, item.message.type === 'text' ? item.message.text : item.message.type, visible[i - 1]?.id, reference ? byId.get(reference.id)?.sender.name ?? null : null, reactions.has(item.id) ? [...reactions.get(item.id).entries()] : [], item.message.type !== 'text' ? financial : '']);
    });
    const key = JSON.stringify([chat, start, end, dayLabel(Date.now()), signatures]);
    lastStart = start; lastEnd = end; lastTotal = messages.length;
    if (key !== renderKey) {
      const anchor = bottom ? null : [...$('messages').querySelectorAll('.message')].find(node => node.getBoundingClientRect().bottom > scroller.getBoundingClientRect().top);
      const anchorId = anchor?.id, anchorTop = anchor?.getBoundingClientRect().top, oldScroll = scroller.scrollTop;
      const fragment = document.createDocumentFragment();
      if (start > 0) fragment.append(element('button', { class: 'history-button', text: 'Load earlier messages', onclick: () => { rangeStart = Math.max(0, start - PAGE); rangeEnd = Math.min(end, rangeStart + PAGE * 2); renderKey = ''; render(); } }));
      let day = '';
      visible.forEach((item, i) => {
        const label = dayLabel(item.created_ms);
        if (label !== day) { fragment.append(element('div', { class: 'date-divider', text: label })); day = label; }
        const cached = rows.get(item.id);
        const node = cached?.signature === signatures[i] ? cached.node : buildRow(item, visible[i - 1], byId, reactions.get(item.id));
        rows.set(item.id, { signature: signatures[i], node }); fragment.append(node);
      });
      if (end < messages.length) fragment.append(element('button', { class: 'history-button', text: 'Load newer messages', onclick: () => { rangeEnd = Math.min(messages.length, end + PAGE); rangeStart = Math.max(0, rangeEnd - PAGE * 2); if (rangeEnd === messages.length) rangeEnd = null; renderKey = ''; render(); } }));
      if (!visible.length) fragment.append(empty(direct ? 'Say hello.' : 'Welcome to #parano1d.', direct ? 'Send a message, share a contact or request NOID.' : 'One public chat. Everyone is welcome.'));
      $('messages').replaceChildren(fragment); renderKey = key;
      const retained = new Set(visible.map(item => item.id));
      for (const [id, cached] of rows) if (!retained.has(id)) {
        for (const card of cached.node.querySelectorAll('.contact-card')) cardObserver?.unobserve(card);
        rows.delete(id);
      }
      if (bottom && end === messages.length) { followLatest = true; snapToBottom(); queueBottom(); }
      else { const restored = anchorId && document.getElementById(anchorId); scroller.scrollTop = restored ? oldScroll + restored.getBoundingClientRect().top - anchorTop : oldScroll; lastScrollTop = scroller.scrollTop; }
    }
    updateJump();
    if (bottom && end === messages.length && Number(state.unread?.[chat]) > 0) queueMicrotask(() => markCurrentRead());
  }
  function updateJump() {
    const missing = Math.max(0, lastTotal - lastEnd);
    $('latest-messages').hidden = isBottom() && !missing;
    $('latest-message-count').hidden = !missing;
    $('latest-message-count').textContent = missing > 99 ? '99+' : String(missing);
  }
  function latest() {
    followLatest = true; rangeStart = null; rangeEnd = null; renderKey = ''; render(); snapToBottom(); queueBottom(); markCurrentRead(true);
  }
  function jumpTo(id) {
    const full = history(), known = new Map(full.map(item => [item.id, item]));
    const messages = full.filter(item => { const r = reactionOf(item); return !r || !known.has(r.target); });
    const index = messages.findIndex(item => item.id === id);
    if (index < 0) { toast('The original message is not saved on this phone.'); return; }
    followLatest = false;
    if (index < lastStart || index >= lastEnd) { rangeStart = Math.max(0, index - 40); rangeEnd = Math.min(messages.length, index + 80); renderKey = ''; render(); }
    const node = document.getElementById(`message-${id}`);
    node?.scrollIntoView({ block: 'center', behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' });
    node?.classList.remove('message-highlight'); requestAnimationFrame(() => node?.classList.add('message-highlight'));
    setTimeout(() => node?.classList.remove('message-highlight'), 1800);
  }
  function messageMenu(item) {
    const buttons = element('div', { class: 'message-menu-actions' });
    const reactions = element('div', { class: 'quick-reactions' });
    for (const emoji of quickEmoji) reactions.append(element('button', { text: emoji, 'aria-label': `React ${emoji}`, onclick: () => { $('modal').close(); react(item, emoji); } }));
    buttons.append(element('button', { onclick: () => reply(item) }, icon('reply'), 'Reply'));
    if (item.message.type === 'text') {
      const text = ChatText.parse(item.message.text).text;
      buttons.append(element('button', { onclick: () => { $('modal').close(); copy(text); } }, icon('copy'), 'Copy text'));
      buttons.append(element('button', { onclick: () => {
        const selected = element('textarea', { class: 'select-message-text', readonly: '', 'aria-label': 'Select message text' }); selected.value = text;
        modal('Select text', [selected, element('button', { class: 'outline-button', text: 'Copy text', onclick: () => copy(selected.value) })], 'MESSAGE');
        selected.focus(); selected.select();
      } }, icon('chat'), 'Select text'));
      const link = ChatText.contacts(text)[0];
      if (link) buttons.append(element('button', { onclick: () => { $('modal').close(); copy(link.uri); } }, icon('direct'), 'Copy contact link'));
    } else if (item.payment?.txid) buttons.append(element('button', { onclick: () => { $('modal').close(); copy(item.payment.txid); } }, icon('copy'), 'Copy transaction ID'));
    modal(item.sender.name, [reactions, buttons, element('p', { class: 'message-menu-meta', text: `${new Date(item.created_ms).toLocaleString('en')} · ${item.sender.id === state.profile.id ? status(item).label : item.via_nearby ? 'Received over Bluetooth' : 'Received message'}` })], 'MESSAGE');
    $('modal').dataset.kind = 'MESSAGE ACTIONS';
  }
  async function react(item, emoji) {
    await run(null, async () => {
      const own = history().filter(entry => entry.sender.id === state.profile.id).map(entry => ({ entry, reaction: reactionOf(entry) })).filter(({ reaction }) => reaction?.target === item.id).at(-1)?.reaction;
      const text = ChatText.reply(own?.emoji === emoji ? 'Reaction removed.' : `Reaction: ${emoji}`, item, textOf(item));
      state = await native('send', { chat: item.chat, message: { type: 'text', text } }); render();
    });
  }
  function closeEmoji() { $('emoji-panel').hidden = true; $('emoji-button').setAttribute('aria-expanded', 'false'); }
  function renderEmoji() {
    const groups = recentEmoji.length ? { Recent: recentEmoji, ...emojiGroups } : emojiGroups;
    if (!groups[emojiCategory]) emojiCategory = 'Smileys';
    $('emoji-categories').replaceChildren(...Object.keys(groups).map(name => element('button', { role: 'tab', 'aria-selected': String(name === emojiCategory), text: name, onclick: () => { emojiCategory = name; renderEmoji(); } })));
    $('emoji-grid').replaceChildren(...groups[emojiCategory].map(emoji => element('button', { text: emoji, 'aria-label': `Insert ${emoji}`, onpointerdown: event => event.preventDefault(), onclick: () => {
      const input = $('compose'); input.setRangeText(emoji, caret[0], caret[1], 'end'); caret = [input.selectionStart, input.selectionEnd];
      recentEmoji = [emoji, ...recentEmoji.filter(value => value !== emoji)].slice(0, 24); inputChanged();
    } })));
  }
  function toggleEmoji() {
    if (!$('emoji-panel').hidden) { closeEmoji(); $('compose').focus(); return; }
    caret = [$('compose').selectionStart, $('compose').selectionEnd]; $('compose').blur();
    renderEmoji(); $('emoji-panel').hidden = false; $('emoji-button').setAttribute('aria-expanded', 'true');
  }
  async function send(event) {
    event.preventDefault();
    const input = $('compose'), text = input.value.trim(), scope = chat;
    if (!text || !scope || sending) return;
    const original = state.messages.find(item => item.id === replyId && item.chat === scope);
    const encoded = original ? ChatText.reply(text, original, textOf(original)) : text;
    if (ChatText.bytes(encoded) > 4096) { toast('Your message is too long. Shorten it before sending.'); return; }
    if (replyId && !original) { toast('Cancel this reply or choose a saved message.'); return; }
    const saved = { text: input.value, reply_to: replyId };
    sending = true; input.value = ''; replyId = ''; keepDraft(); composer();
    clearTimeout(draftTimers.get(scope));
    try {
      const result = await native('send', { chat: scope, message: { type: 'text', text: encoded } });
      state = result;
      if (chat === scope) { rangeStart = null; rangeEnd = null; }
      render(); if (chat === scope) latest();
    } catch (error) {
      const current = drafts.get(scope) || { text: '', reply_to: '' };
      const restored = current.text ? { ...current, text: `${saved.text}\n${current.text}` } : saved;
      drafts.set(scope, restored);
      if (chat === scope) { input.value = restored.text; replyId = restored.reply_to; }
      if (ChatStorageUI.isFullError(error.message)) ChatStorageUI.reportFull();
      else toast(explainError(error.message));
    }
    finally { sending = false; composer(); }
  }
  function closeSearch() { $('chat-search').hidden = true; searchQuery = ''; searchMatches = []; $('chat-search-input').value = ''; }
  function search(move = 0) {
    const query = $('chat-search-input').value.trim().toLocaleLowerCase();
    if (query !== searchQuery) {
      searchQuery = query; searchIndex = 0;
      searchMatches = query ? history().filter(item => !reactionOf(item) && `${item.sender.name}\n${textOf(item)}`.toLocaleLowerCase().includes(query)).map(item => item.id).reverse() : [];
    } else if (searchMatches.length) searchIndex = (searchIndex + move + searchMatches.length) % searchMatches.length;
    $('chat-search-count').textContent = query ? searchMatches.length ? `${searchIndex + 1} / ${searchMatches.length}` : 'No matches' : '';
    $('chat-search-previous').disabled = $('chat-search-next').disabled = !searchMatches.length;
    if (searchMatches.length) jumpTo(searchMatches[searchIndex]);
  }
  function back() {
    if (!$('emoji-panel').hidden) { closeEmoji(); return true; }
    if (!$('chat-search').hidden) { closeSearch(); return true; }
    if (replyId) { replyId = ''; composer(); inputChanged(); return true; }
    return false;
  }
  function layoutChanged() {
    const wrapper = document.querySelector('.compose-wrapper');
    if (wrapper && !$('chat-panel').hidden) {
      const height = `${Math.ceil(wrapper.getBoundingClientRect().height)}px`;
      if ($('chat-panel').style.getPropertyValue('--composer-height') !== height) $('chat-panel').style.setProperty('--composer-height', height);
    }
    queueBottom();
  }
  function setup() {
    $('compose-form').addEventListener('submit', send);
    $('compose').addEventListener('input', inputChanged);
    $('compose').addEventListener('focus', closeEmoji);
    $('compose').addEventListener('blur', () => { keepDraft(); persistDraft(); });
    $('emoji-button').addEventListener('click', toggleEmoji);
    $('cancel-reply').addEventListener('click', () => { replyId = ''; composer(); inputChanged(); });
    $('reply-preview-message').addEventListener('click', () => jumpTo(replyId));
    $('latest-messages').addEventListener('click', latest);
    $('message-scroll').addEventListener('scroll', () => {
      const scroller = $('message-scroll');
      if (isBottom()) followLatest = true;
      else if (scroller.scrollTop < lastScrollTop - 1) followLatest = false;
      lastScrollTop = scroller.scrollTop;
      if (!followLatest && !isBottom() && rangeStart === null) { rangeStart = lastStart; rangeEnd = lastEnd; }
      if (isBottom() && rangeEnd === lastTotal) rangeEnd = null;
      updateJump();
    }, { passive: true });
    if (typeof ResizeObserver === 'function') {
      const sizing = new ResizeObserver(queueBottom);
      sizing.observe($('messages'), { box: 'border-box' }); sizing.observe($('message-scroll'));
      const composerSizing = new ResizeObserver(layoutChanged);
      composerSizing.observe(document.querySelector('.compose-wrapper'));
    }
    document.fonts?.ready.then(queueBottom);
    $('chat-search-button').addEventListener('click', () => { $('chat-search').hidden = false; $('chat-search-input').focus(); });
    $('chat-search-close').addEventListener('click', closeSearch);
    $('chat-search-input').addEventListener('input', () => search());
    $('chat-search-input').addEventListener('keydown', event => { if (event.key === 'Enter') { event.preventDefault(); search(event.shiftKey ? -1 : 1); } if (event.key === 'Escape') closeSearch(); });
    $('chat-search-previous').addEventListener('click', () => search(-1)); $('chat-search-next').addEventListener('click', () => search(1));
    document.addEventListener('visibilitychange', () => { if (document.hidden) { keepDraft(); persistDraft(); } });
    document.addEventListener('keydown', event => { if (event.key === 'Escape' && !$('modal').open) back(); });
  }
  function historyCleared(scopes) {
    const known = new Set((state.messages || []).map(item => item.id));
    for (const scope of scopes) {
      const saved = drafts.get(scope);
      if (saved?.reply_to && !known.has(saved.reply_to)) saved.reply_to = '';
    }
    if (scopes.includes(currentChat)) {
      if (replyId && !known.has(replyId)) replyId = '';
      renderKey = ''; rangeStart = null; rangeEnd = null; rows.clear();
      closeSearch(); composer();
    }
  }
  function conversationDeleted(scope) {
    clearTimeout(draftTimers.get(scope)); draftTimers.delete(scope); drafts.delete(scope);
    if (currentChat !== scope) return;
    for (const cached of rows.values()) for (const card of cached.node.querySelectorAll('.contact-card')) cardObserver?.unobserve(card);
    currentChat = ''; renderKey = ''; rangeStart = null; rangeEnd = null; rows.clear();
    replyId = ''; $('compose').value = ''; closeEmoji(); closeSearch();
    $('messages').replaceChildren();
  }
  return { render: renderChat, preview, beforeSwitch, setup, back, jumpTo, composer, messageMenu, historyCleared, conversationDeleted, layoutChanged };
})();
