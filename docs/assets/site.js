// Общий код страницы Zorko: фоны, темы и сообщения.
(function () {
  'use strict';

  const THEMES = [
    { id: 'black', label: 'Чёрный', dot: 'linear-gradient(135deg,#000000 50%,#f5f5f7 50%)' },
    { id: 'night', label: 'Ночной радар', dot: 'linear-gradient(135deg,#0b0f17 50%,#ff9a3c 50%)' },
    { id: 'sakura', label: 'Сакура', dot: 'linear-gradient(135deg,#ffbfd4 50%,#c2255c 50%)' },
    { id: 'neon', label: 'Неон-Токио', dot: 'linear-gradient(135deg,#3b0a5c 50%,#19e3ff 50%)' },
    { id: 'sunset', label: 'Закат', dot: 'linear-gradient(135deg,#7b3b8c 50%,#ffa76b 50%)' },
    { id: 'stars', label: 'Звёздное небо', dot: 'linear-gradient(135deg,#0b1a4a 50%,#9cc2ff 50%)' },
    { id: 'manga', label: 'Манга', dot: 'linear-gradient(135deg,#ffffff 50%,#111111 50%)' },
    { id: 'ocean', label: 'Летнее море', dot: 'linear-gradient(135deg,#8fd0ff 50%,#0a5fb4 50%)' },
    { id: 'matcha', label: 'Матча', dot: 'linear-gradient(135deg,#dce8c6 50%,#3a6723 50%)' },
    { id: 'vapor', label: 'Ретро-волна', dot: 'linear-gradient(135deg,#5a1a7a 50%,#ff7ad1 50%)' }
  ];
  const root = document.getElementById('page');
  const listeners = [];
  let sessionBg = '';

  // Память браузера может быть недоступна (частный режим), поэтому всё через try/catch.
  function load(key) { try { return localStorage.getItem(key); } catch (e) { return null; } }
  function save(key, value) { try { localStorage.setItem(key, value); return true; } catch (e) { return false; } }

  function customBg() { return sessionBg || load('zorko-bg') || ''; }
  function isTheme(id) { return THEMES.some((t) => t.id === id) || (id === 'custom' && !!customBg()); }
  function getTheme() { const t = load('zorko-theme'); return isTheme(t) ? t : 'black'; }

  function paint(id) {
    if (!root) return;
    for (const c of Array.from(root.classList)) if (c.indexOf('t-') === 0) root.classList.remove(c);
    root.classList.add('t-' + id);
    const img = root.querySelector('.cimg');
    if (img) img.style.backgroundImage = id === 'custom' && customBg() ? 'url("' + customBg() + '")' : 'none';
    for (const chip of document.querySelectorAll('[data-theme-id]')) {
      const on = chip.dataset.themeId === id;
      chip.classList.toggle('on', on);
      chip.setAttribute('aria-pressed', String(on));
    }
    const label = document.getElementById('bg-label');
    if (label) label.classList.toggle('on', id === 'custom');
  }

  function setTheme(id, silent) {
    if (!isTheme(id)) id = 'black';
    save('zorko-theme', id);
    paint(id);
    if (!silent) for (const fn of listeners) fn(id);
  }

  function buildScenes() {
    for (const holder of document.querySelectorAll('[data-scene]')) holder.innerHTML = window.ZORKO_SCENE || '';
  }

  function buildChips() {
    const box = document.querySelector('[data-theme-chips]');
    if (!box) return;
    const before = box.firstChild;
    for (const t of THEMES) {
      const b = document.createElement('button');
      b.type = 'button'; b.className = 'chip'; b.dataset.themeId = t.id;
      const dot = document.createElement('span'); dot.className = 'dot'; dot.style.background = t.dot;
      const text = document.createElement('span'); text.textContent = t.label;
      b.append(dot, text);
      b.addEventListener('click', () => setTheme(t.id));
      box.insertBefore(b, before);
    }
    const file = document.getElementById('bg-file');
    if (file) file.addEventListener('change', () => {
      const f = file.files && file.files[0];
      if (!f) return;
      const reader = new FileReader();
      reader.onload = () => {
        sessionBg = String(reader.result);
        // Большая картинка может не поместиться в память браузера: тогда фон продержится до закрытия вкладки.
        const kept = save('zorko-bg', sessionBg);
        setTheme('custom');
        toast(kept ? 'Фон установлен' : 'Фон установлен до закрытия вкладки: файл слишком большой, чтобы его запомнить');
      };
      reader.readAsDataURL(f);
    });
  }

  let toastTimer = 0;
  function toast(text) {
    let n = document.getElementById('toast');
    if (!n) { n = document.createElement('div'); n.id = 'toast'; n.setAttribute('role', 'status'); n.setAttribute('aria-live', 'polite'); document.body.append(n); }
    n.textContent = text; n.classList.add('on');
    clearTimeout(toastTimer); toastTimer = setTimeout(() => n.classList.remove('on'), 4000);
  }

  buildScenes();
  buildChips();
  paint(getTheme());

  window.Zorko = { themes: THEMES, getTheme, setTheme, toast, onTheme(fn) { listeners.push(fn); } };
})();
