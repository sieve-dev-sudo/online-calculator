// ===== Elements =====
const displayEl = document.getElementById('display');
const historyEl = document.getElementById('history');
const previewEl = document.getElementById('preview');
const angleBadge = document.getElementById('angle-badge');
const angleBtn = document.getElementById('angle-mode');
const secondBtn = document.getElementById('second');
const themeToggleBtn = document.getElementById('theme-toggle');
const funcButtons = document.querySelectorAll('[data-action="func"]');

// ===== State =====
// tokens: the expression as a list of pieces, e.g. ['2', '*', 'sin(', '3', '0', ')']
// A token starting with '#' is a whole calculated result (used for negative or very large/small results)
let tokens = [];
let justCalculated = false;
let angleMode = 'deg';
let secondMode = false;

const BINARY_OPS = ['+', '-', '*', '/', '^'];
const VALUE_END = [')', 'π', 'ℯ', '!', '%', '^(2)', '^(-1)'];
const DISPLAY_MAP = {
  '*': '×',
  '/': '÷',
  '-': '−',
  'ℯ': 'e',
  'ℯ^(': 'e^(',
  'sqrt(': '√(',
  'asin(': 'sin⁻¹(',
  'acos(': 'cos⁻¹(',
  'atan(': 'tan⁻¹(',
  'log(': 'lg(',
  '^(2)': '²',
  '^(-1)': '⁻¹'
};

// ===== Token helpers =====
const last = () => tokens[tokens.length - 1];
const isNumTok = t => t !== undefined && /^[\d.#]/.test(t);
const isValueEnd = t => t !== undefined && (isNumTok(t) || VALUE_END.includes(t));
const isBinOp = t => BINARY_OPS.includes(t);
const isOpen = t => t !== undefined && t.endsWith('(');
// true when a new number/function must be joined with an explicit ×
const needsMultiply = t => isValueEnd(t) && !/^[\d.]$/.test(t);

function tokenToDisplay(t) {
  if (t.startsWith('#')) return t.slice(1).replace('-', '−');
  return DISPLAY_MAP[t] ?? t;
}

function toDisplay(list) {
  return list.map(tokenToDisplay).join('');
}

function countParens(str) {
  return {
    open: (str.match(/\(/g) || []).length,
    close: (str.match(/\)/g) || []).length
  };
}

function buildExpression() {
  const str = tokens.map(t => (t.startsWith('#') ? '(' + t.slice(1) + ')' : t)).join('');
  const { open, close } = countParens(str);
  return str + ')'.repeat(Math.max(0, open - close));
}

function missingParens() {
  const { open, close } = countParens(tokens.join(''));
  return Math.max(0, open - close);
}

// ===== Math engine (safe parser, no eval) =====
function factorial(n) {
  if (n < 0 || !Number.isInteger(n)) return NaN;
  if (n > 170) return Infinity;
  let r = 1;
  for (let i = 2; i <= n; i++) r *= i;
  return r;
}

function applyFunc(name, x) {
  const toRad = v => (angleMode === 'deg' ? (v * Math.PI) / 180 : v);
  const fromRad = v => (angleMode === 'deg' ? (v * 180) / Math.PI : v);

  switch (name) {
    case 'sin': return Math.sin(toRad(x));
    case 'cos': return Math.cos(toRad(x));
    case 'tan': {
      const r = toRad(x);
      if (Math.abs(Math.cos(r)) < 1e-12) return NaN; // tan(90°) is undefined
      return Math.tan(r);
    }
    case 'asin': return fromRad(Math.asin(x));
    case 'acos': return fromRad(Math.acos(x));
    case 'atan': return fromRad(Math.atan(x));
    case 'sqrt': return Math.sqrt(x);
    case 'log': return Math.log10(x);
    case 'ln': return Math.log(x);
    default: throw new Error('Unknown function');
  }
}

function tokenize(str) {
  const list = [];
  let i = 0;

  while (i < str.length) {
    const ch = str[i];

    if (/[\d.]/.test(ch)) {
      const m = str.slice(i).match(/^\d*\.?\d*(?:e[+-]?\d+)?/);
      if (m[0] === '.') throw new Error('Bad number');
      list.push({ type: 'num', value: parseFloat(m[0]) });
      i += m[0].length;
      continue;
    }

    if (/[a-z]/.test(ch)) {
      const m = str.slice(i).match(/^[a-z]+/);
      list.push({ type: 'func', value: m[0] });
      i += m[0].length;
      continue;
    }

    if (ch === 'π') { list.push({ type: 'num', value: Math.PI }); i++; continue; }
    if (ch === 'ℯ') { list.push({ type: 'num', value: Math.E }); i++; continue; }

    if ('+-*/^()!%'.includes(ch)) {
      list.push({ type: 'op', value: ch });
      i++;
      continue;
    }

    throw new Error('Unexpected character');
  }
  return list;
}

function evaluate(str) {
  const t = tokenize(str);
  let p = 0;

  const peek = () => t[p];
  const next = () => t[p++];
  const isOp = v => peek() && peek().type === 'op' && peek().value === v;
  const startsPrimary = () => {
    const k = peek();
    return k && (k.type === 'num' || k.type === 'func' || (k.type === 'op' && k.value === '('));
  };

  // expr := term (('+' | '-') term)*
  function parseExpr() {
    let v = parseTerm();
    while (isOp('+') || isOp('-')) {
      const o = next().value;
      const r = parseTerm();
      v = o === '+' ? v + r : v - r;
    }
    return v;
  }

  // term := unary (('*' | '/') unary | implicit multiply)*
  function parseTerm() {
    let v = parseUnary();
    while (true) {
      if (isOp('*') || isOp('/')) {
        const o = next().value;
        const r = parseUnary();
        v = o === '*' ? v * r : v / r;
      } else if (startsPrimary()) {
        v *= parseUnary();
      } else {
        break;
      }
    }
    return v;
  }

  // unary := ('-' | '+') unary | power
  function parseUnary() {
    if (isOp('-')) { next(); return -parseUnary(); }
    if (isOp('+')) { next(); return parseUnary(); }
    return parsePower();
  }

  // power := postfix ('^' unary)?   (right associative)
  function parsePower() {
    const base = parsePostfix();
    if (isOp('^')) {
      next();
      return Math.pow(base, parseUnary());
    }
    return base;
  }

  // postfix := primary ('!' | '%')*
  function parsePostfix() {
    let v = parsePrimary();
    while (isOp('!') || isOp('%')) {
      const o = next().value;
      v = o === '!' ? factorial(v) : v / 100;
    }
    return v;
  }

  // primary := number | '(' expr ')' | func '(' expr ')'
  function parsePrimary() {
    const k = next();
    if (!k) throw new Error('Unexpected end');

    if (k.type === 'num') return k.value;

    if (k.type === 'op' && k.value === '(') {
      const v = parseExpr();
      if (!isOp(')')) throw new Error('Missing )');
      next();
      return v;
    }

    if (k.type === 'func') {
      if (!isOp('(')) throw new Error('Missing (');
      next();
      const arg = parseExpr();
      if (!isOp(')')) throw new Error('Missing )');
      next();
      return applyFunc(k.value, arg);
    }

    throw new Error('Unexpected token');
  }

  const result = parseExpr();
  if (p < t.length) throw new Error('Unexpected token');
  return result;
}

function formatNumber(n) {
  if (Math.abs(n) < 1e-12) n = 0; // clean up tiny float errors like sin(180°)
  return String(parseFloat(n.toPrecision(12)));
}

function tryEvaluate() {
  try {
    const r = evaluate(buildExpression());
    return Number.isFinite(r) ? r : null;
  } catch (e) {
    return null;
  }
}

// ===== Rendering =====
function render() {
  const text = toDisplay(tokens);
  displayEl.textContent = text === '' ? '0' : text;
  displayEl.scrollLeft = displayEl.scrollWidth;
  updatePreview();
}

function updatePreview() {
  previewEl.textContent = '';
  if (justCalculated || tokens.length === 0) return;
  if (tokens.every(t => /^[\d.]$/.test(t))) return; // plain number, nothing to preview
  const r = tryEvaluate();
  if (r !== null) previewEl.textContent = '= ' + formatNumber(r).replace('-', '−');
}

function startFreshIfNeeded() {
  if (justCalculated) {
    tokens = [];
    justCalculated = false;
  }
}

// ===== Input handlers =====
function inputNumber(value) {
  startFreshIfNeeded();
  if (needsMultiply(last())) tokens.push('*');
  for (const ch of value) tokens.push(ch);
  render();
}

function inputDecimal() {
  startFreshIfNeeded();

  if (needsMultiply(last())) {
    tokens.push('*', '0', '.');
    return render();
  }

  // find the digits of the current number
  let segment = '';
  for (let i = tokens.length - 1; i >= 0 && /^[\d.]$/.test(tokens[i]); i--) {
    segment = tokens[i] + segment;
  }
  if (segment.includes('.')) return;

  if (segment === '') tokens.push('0', '.');
  else tokens.push('.');
  render();
}

function inputOperator(op) {
  justCalculated = false;
  const l = last();

  // start of expression or right after "(": only a minus sign is allowed
  if (l === undefined || isOpen(l)) {
    if (op === '-') tokens.push('-');
    return render();
  }

  if (isBinOp(l)) {
    // allow a negative number after ×, ÷ or ^  (e.g. 5×−2)
    if (op === '-' && ['*', '/', '^'].includes(l)) {
      tokens.push('-');
      return render();
    }
    // otherwise replace the previous operator
    tokens.pop();
    if (isBinOp(last())) tokens.pop();
    if (tokens.length === 0 || isOpen(last())) {
      if (op === '-') tokens.push('-');
    } else {
      tokens.push(op);
    }
    return render();
  }

  tokens.push(op);
  render();
}

function inputPrefix(tok) {
  startFreshIfNeeded();
  if (isValueEnd(last())) tokens.push('*');
  tokens.push(tok);
  render();
}

function inputPostfix(tok) {
  justCalculated = false;
  if (!isValueEnd(last())) return;
  tokens.push(tok);
  render();
}

function inputConst(c) {
  startFreshIfNeeded();
  if (isValueEnd(last())) tokens.push('*');
  tokens.push(c);
  render();
}

function inputOpen() {
  startFreshIfNeeded();
  if (isValueEnd(last())) tokens.push('*');
  tokens.push('(');
  render();
}

function inputClose() {
  if (missingParens() > 0 && isValueEnd(last())) {
    justCalculated = false;
    tokens.push(')');
    render();
  }
}

function inputFunc(btn) {
  const tok = secondMode ? btn.dataset.fn2 : btn.dataset.fn;
  if (tok.startsWith('^')) inputPostfix(tok); // x²
  else inputPrefix(tok);
}

function backspace() {
  justCalculated = false;
  tokens.pop();
  render();
}

function clearAll() {
  tokens = [];
  justCalculated = false;
  historyEl.textContent = '';
  render();
}

function calculate() {
  if (tokens.length === 0) return;

  const shownExpression = toDisplay(tokens) + ')'.repeat(missingParens());
  let result;
  try {
    result = evaluate(buildExpression());
  } catch (e) {
    result = NaN;
  }

  historyEl.textContent = shownExpression + ' =';
  historyEl.scrollLeft = historyEl.scrollWidth;

  if (!Number.isFinite(result)) {
    tokens = [];
    justCalculated = true;
    displayEl.textContent = 'Error';
    previewEl.textContent = '';
    return;
  }

  const text = formatNumber(result);
  // keep simple positive results as separate digits so backspace works digit by digit
  tokens = /^[\d.]+$/.test(text) ? text.split('') : ['#' + text];
  justCalculated = true;
  render();
}

// ===== 2nd and angle mode =====
funcButtons.forEach(btn => {
  btn.dataset.label = btn.innerHTML;
});

function setSecond(on) {
  secondMode = on;
  secondBtn.classList.toggle('active', on);
  funcButtons.forEach(btn => {
    btn.innerHTML = on ? btn.dataset.label2 : btn.dataset.label;
  });
}

function applyAngleMode(mode) {
  angleMode = mode;
  angleBadge.textContent = mode.toUpperCase();
  angleBtn.textContent = mode === 'deg' ? 'rad' : 'deg'; // button shows the mode it switches to
  try {
    localStorage.setItem('calculator-angle', mode);
  } catch (e) {}
  updatePreview();
}

// ===== Basic / scientific keypad (phones) =====
const calculatorEl = document.querySelector('.calculator');

function setKeypad(basic) {
  calculatorEl.classList.toggle('basic', basic);
  try {
    localStorage.setItem('calculator-keypad', basic ? 'basic' : 'sci');
  } catch (e) {}
}

// ===== Button clicks =====
function handleButton(btn) {
  const { action, value } = btn.dataset;

  switch (action) {
    case 'num': inputNumber(value); break;
    case 'op': inputOperator(value); break;
    case 'postfix': inputPostfix(value); break;
    case 'const': inputConst(value); break;
    case 'func': inputFunc(btn); break;
    case 'open': inputOpen(); break;
    case 'close': inputClose(); break;
    case 'decimal': inputDecimal(); break;
    case 'equals': calculate(); break;
    case 'clear': clearAll(); break;
    case 'backspace': backspace(); break;
    case 'second': setSecond(!secondMode); break;
    case 'angle': applyAngleMode(angleMode === 'deg' ? 'rad' : 'deg'); break;
    case 'swap': setKeypad(!calculatorEl.classList.contains('basic')); break;
  }
}

document.querySelectorAll('.keys button').forEach(btn => {
  btn.addEventListener('click', () => handleButton(btn));
});

// ===== Keyboard =====
const KHMER_DIGITS = '០១២៣៤៥៦៧៨៩';
const NUMPAD_KEYS = {
  NumpadAdd: '+',
  NumpadSubtract: '-',
  NumpadMultiply: '*',
  NumpadDivide: '/',
  NumpadDecimal: '.',
  NumpadEnter: 'Enter'
};

// physical keys without Shift
const CODE_KEYS = {
  Minus: '-',
  Equal: '=',
  Slash: '/',
  Period: '.'
};

// physical keys with Shift (same positions as an English keyboard)
const SHIFT_CODE_KEYS = {
  Equal: '+',
  Digit8: '*',
  Digit9: '(',
  Digit0: ')',
  Digit5: '%',
  Digit1: '!',
  Digit6: '^'
};

const VALID_KEYS = '0123456789+-*/^().%!=';

// Turns any keyboard layout (English, Khmer, numpad) into the same keys
function normalizeKey(e) {
  const code = e.code || '';
  const k = e.key;

  // English layout: the key already gives the right character
  if (k.length === 1 && VALID_KEYS.includes(k)) return k;

  // Khmer digits ០-៩ become 0-9
  const khmerIndex = KHMER_DIGITS.indexOf(k);
  if (khmerIndex !== -1) return String(khmerIndex);

  // numpad operators, decimal and Enter
  if (NUMPAD_KEYS[code]) return NUMPAD_KEYS[code];

  // numpad number keys (also when Num Lock is off)
  if (/^Numpad[0-9]$/.test(code)) return code.slice(6);

  // other layouts (like Khmer): read the key by its physical position
  if (e.shiftKey && SHIFT_CODE_KEYS[code]) return SHIFT_CODE_KEYS[code];
  if (!e.shiftKey && /^Digit[0-9]$/.test(code)) return code.slice(5);
  if (!e.shiftKey && CODE_KEYS[code]) return CODE_KEYS[code];

  // some keyboards send × or ÷ directly
  if (k === '×') return '*';
  if (k === '÷') return '/';

  return k;
}

document.addEventListener('keydown', (e) => {
  if (e.ctrlKey || e.metaKey || e.altKey) return;

  const k = normalizeKey(e);
  let handled = true;

  if (/^[0-9]$/.test(k)) inputNumber(k);
  else if (BINARY_OPS.includes(k)) inputOperator(k);
  else if (k === '.') inputDecimal();
  else if (k === '(') inputOpen();
  else if (k === ')') inputClose();
  else if (k === '%' || k === '!') inputPostfix(k);
  else if (k === 'Enter' || k === '=') calculate();
  else if (k === 'Backspace') backspace();
  else if (k === 'Escape' || k === 'Delete') clearAll();
  else handled = false;

  // stops Enter from also "clicking" a focused button
  if (handled) e.preventDefault();
});

// ===== Dark mode toggle =====
function applyTheme(isDark) {
  document.body.classList.toggle('dark', isDark);
  themeToggleBtn.textContent = isDark ? '☀️' : '🌙';
}

themeToggleBtn.addEventListener('click', () => {
  const isDark = !document.body.classList.contains('dark');
  applyTheme(isDark);
  try {
    localStorage.setItem('calculator-theme', isDark ? 'dark' : 'light');
  } catch (e) {}
});

// ===== Init =====
let savedTheme = null;
let savedAngle = null;
let savedKeypad = null;
try {
  savedTheme = localStorage.getItem('calculator-theme');
  savedAngle = localStorage.getItem('calculator-angle');
  savedKeypad = localStorage.getItem('calculator-keypad');
} catch (e) {}

applyTheme(savedTheme === 'dark');
applyAngleMode(savedAngle === 'rad' ? 'rad' : 'deg');
setKeypad(savedKeypad !== 'sci'); // phones start with the basic keypad
render();
