'use strict';

// Replies remain ordinary signed text so existing clients can read the quote.
window.ChatText = Object.freeze({
  bytes(text) { return new TextEncoder().encode(text).length; },
  parse(text = '') {
    const match = text.match(/^> \[([^\]\n]{1,64})\]\(paramo1d:\/\/message\/([0-9a-f]{64})\)\n((?:> [^\n]*\n){1,4})\n([\s\S]+)$/);
    return match ? { text: match[4], reply: { id: match[2], name: match[1], excerpt: match[3].trimEnd().split('\n').map(line => line.slice(2)).join('\n') } } : { text, reply: null };
  },
  reply(text, original, excerpt) {
    if (!/^[0-9a-f]{64}$/.test(original.id)) throw new Error('This message cannot be quoted.');
    const name = Array.from(original.sender.name.replace(/[\[\]\r\n]/g, ' ')).slice(0, 32).join('');
    const snippet = Array.from(excerpt.replace(/\r/g, '')).slice(0, 220).join('').split('\n').slice(0, 3).map(line => `> ${line}`).join('\n');
    return `> [${name}](paramo1d://message/${original.id})\n${snippet}\n\n${text}`;
  },
  contacts(text = '') { return [...text.matchAll(/paramo1d:\/\/contact\/[A-Za-z0-9_-]+/g)].map(match => ({ uri: match[0], at: match.index })); },
});
