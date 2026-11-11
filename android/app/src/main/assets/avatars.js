'use strict';

window.WarriorAvatar = (() => {
  const cache = new Map();
  const palettes = [
    ['#13332a','#38dc91','#b7ffe0','#187a56'],
    ['#172c48','#6dacf6','#d4eaff','#385e9c'],
    ['#342345','#ba8df0','#efdfff','#7752a5'],
    ['#3b2a1e','#f1b24f','#fff0bf','#ad6f29'],
    ['#3d2534','#ee82b1','#ffe0ed','#ab487b'],
    ['#18373c','#60d7d9','#d1ffff','#2b8d99'],
    ['#372d2a','#e89165','#ffe6c9','#a65736'],
    ['#262d3a','#a1b2ca','#eff6ff','#60718b'],
  ];
  function source(identity = '') {
    if (cache.has(identity)) return cache.get(identity);
    let seed = 2166136261;
    for (const character of String(identity)) seed = Math.imul(seed ^ character.charCodeAt(0), 16777619) >>> 0;
    const next = () => { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return seed >>> 0; };
    const [background, armor, light, shadow] = palettes[next() % palettes.length];
    const skin = ['#eec5a3','#d49e76','#b47751','#805137','#f3d8bf'][next() % 5];
    const dark = '#111c22', steel = '#b9cad2', shine = '#f1f9fa';
    const helmet = next() % 5, cape = next() % 2, weapon = next() % 3;
    const shapes = [];
    const rect = (x, y, w, h, color) => shapes.push(`<rect x="${x}" y="${y}" width="${w}" height="${h}" fill="${color}"/>`);
    rect(0, 0, 24, 24, background); rect(4, 22, 16, 1, '#00000033');
    if (cape) { rect(6, 10, 12, 10, shadow); rect(5, 15, 14, 5, shadow); }
    rect(8, 11, 8, 8, dark); rect(8, 12, 8, 6, armor);
    rect(8, 12, 2, 5, light); rect(14, 12, 2, 6, shadow);
    rect(10, 13, 3, 3, steel); rect(11, 13, 1, 2, shine);
    rect(8, 18, 8, 2, dark); rect(11, 18, 2, 1, '#efc35b');
    rect(8, 20, 3, 2, steel); rect(13, 20, 3, 2, steel);
    rect(7, 22, 4, 1, dark); rect(13, 22, 4, 1, dark);
    rect(5, 12, 3, 5, armor); rect(5, 12, 3, 1, light);
    rect(16, 12, 3, 5, shadow); rect(16, 12, 2, 1, light);
    rect(6, 16, 2, 2, skin); rect(17, 16, 2, 2, skin);
    rect(8, 4, 8, 7, dark); rect(9, 5, 6, 5, skin);
    rect(8, 3, 8, 3, armor); rect(9, 3, 6, 1, light);
    rect(7, 5, 2, 5, armor); rect(15, 5, 2, 5, shadow);
    rect(10, 7, 1, 1, dark); rect(13, 7, 1, 1, dark); rect(11, 9, 2, 1, '#9d5b48');
    if (helmet === 0) { rect(11, 1, 2, 4, armor); rect(11, 1, 1, 3, light); rect(9, 8, 6, 2, steel); rect(10, 8, 4, 1, dark); }
    if (helmet === 1) { rect(5, 2, 2, 4, steel); rect(6, 5, 3, 2, steel); rect(17, 2, 2, 4, steel); rect(15, 5, 3, 2, steel); }
    if (helmet === 2) { rect(7, 3, 10, 2, shadow); rect(8, 8, 8, 3, shadow); rect(9, 6, 6, 1, light); rect(10, 7, 1, 1, shine); rect(13, 7, 1, 1, shine); }
    if (helmet === 3) { rect(7, 4, 10, 2, steel); rect(11, 2, 2, 8, steel); rect(12, 3, 1, 6, shadow); rect(9, 7, 2, 1, dark); rect(13, 7, 2, 1, dark); }
    if (helmet === 4) { rect(9, 1, 1, 3, '#efc35b'); rect(12, 1, 1, 3, '#efc35b'); rect(15, 1, 1, 3, '#efc35b'); rect(9, 3, 7, 1, '#efc35b'); }
    if (weapon === 0) { rect(20, 5, 1, 11, steel); rect(20, 5, 1, 5, shine); rect(18, 15, 5, 1, '#efc35b'); rect(20, 16, 1, 4, dark); }
    if (weapon === 1) { rect(20, 5, 1, 14, '#a67a47'); rect(18, 5, 5, 4, steel); rect(18, 5, 5, 1, shine); }
    if (weapon === 2) { rect(20, 3, 1, 16, '#a67a47'); rect(19, 2, 3, 3, light); rect(20, 1, 1, 5, armor); }
    rect(2, 12, 5, 6, dark); rect(3, 13, 3, 5, armor); rect(3, 18, 3, 1, dark);
    rect(4, 13, 1, 5, light); rect(3, 15, 3, 1, light);
    const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" shape-rendering="crispEdges">${shapes.join('')}</svg>`;
    const uri = `data:image/svg+xml;charset=utf-8,${encodeURIComponent(svg)}`;
    if (cache.size >= 512) cache.delete(cache.keys().next().value);
    cache.set(identity, uri); return uri;
  }
  function paint(node, identity, name = '') {
    const uri = source(identity);
    if (!node.classList.contains('warrior-avatar') || node.firstElementChild?.getAttribute('src') !== uri) {
      const image = document.createElement('img'); image.src = uri; image.alt = ''; image.draggable = false;
      node.replaceChildren(image); node.classList.add('warrior-avatar');
    }
    node.title = name;
    return node;
  }
  function node(identity, name = '', tag = 'span', attributes = {}) {
    const target = document.createElement(tag);
    for (const [key, value] of Object.entries(attributes)) {
      if (key.startsWith('on')) target.addEventListener(key.slice(2), value);
      else target.setAttribute(key, value);
    }
    if (!target.classList.contains('avatar')) target.classList.add('avatar');
    return paint(target, identity, name);
  }
  return Object.freeze({ source, paint, node });
})();
