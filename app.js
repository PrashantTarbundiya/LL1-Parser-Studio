/**
 * ============================================================
 * LL(1) PARSER STUDIO — APPLICATION ENGINE (app.js)
 * Principles of Compiler Design
 * Full grammar transformation, FIRST/FOLLOW, Table, Conflicts,
 * Step-by-step Parser Simulator & Vector SVG Parse Tree
 * ============================================================
 */

// ============================================================
// GLOBAL STATE
// ============================================================
var G = null;                 // Original grammar object
var G_transformed = null;     // Preprocessed grammar object
var G_active = null;          // Currently active grammar for analysis
var preprocessResult = null;  // Steps and details of left recursion & factoring
var NULLABLE_INFO = null;     // Object: { nullable: Set, reasons: Map, steps: Array }
var FIRST_SETS = null;        // Map: NonTerminal -> Set of terminals + ε
var FOLLOW_SETS = null;       // Map: NonTerminal -> Set of terminals + $
var FIRST_SIM_STEPS = [];     // Array of FIRST step objects for simulator
var FOLLOW_SIM_STEPS = [];    // Array of FOLLOW step objects for simulator
var FIRST_DEPS = new Map();   // Map: NT -> Set(NT) for FIRST dependencies
var FOLLOW_DEPS = new Map();  // Map: NT -> Set(NT) for FOLLOW dependencies
var PARSE_TABLE = null;       // Map: NonTerminal -> Map(Terminal -> [productions])
var simTrace = [];            // Array of parsing simulation steps
var parseTreeRoot = null;     // Parse tree root node
var simCurrentStep = 0;       // Current step in simulation
var autoPlayInterval = null;  // Auto-play timer for PDA
var tableWhyMap = new Map();  // Why explanations for table cells
var firstWhyMap = new Map();  // Why explanations for FIRST entries
var followWhyMap = new Map(); // Why explanations for FOLLOW entries
var conflictInfo = [];        // Conflict info array
var treeZoomLevel = 1.0;      // Current SVG parse tree zoom scale

// FIRST and FOLLOW interactive simulators state
var firstSimIndex = 0;
var followSimIndex = 0;
var firstSimTimer = null;
var followSimTimer = null;
var firstSimSpeed = 1000;
var followSimSpeed = 1000;
var inspectorNT = null;
var graphEdgeFilter = 'all';

// ============================================================
// SECTION 1: BUILT-IN EXAMPLE GRAMMARS (TESTS 1 - 10 & ADVANCED)
// ============================================================

var EXAMPLES = [
  // 0: Test 1 — Simple
  "S -> a",

  // 1: Test 2 — Epsilon
  "S -> \u03b5",

  // 2: Test 3 — Chain
  "S -> A\nA -> B\nB -> c",

  // 3: Test 4 — Nullable Chain
  "S -> A B\nA -> \u03b5\nB -> \u03b5",

  // 4: Test 5 — Classic LL(1) Expression Grammar
  "E -> T E'\nE' -> + T E' | \u03b5\nT -> F T'\nT' -> * F T' | \u03b5\nF -> ( E ) | id",

  // 5: Test 6 — Multiple Nullable Symbols
  "S -> A B C d\nA -> \u03b5\nB -> \u03b5\nC -> \u03b5",

  // 6: Test 7 — Mutual Recursion
  "A -> B\nB -> C\nC -> A | d",

  // 7: Test 8 — Left Recursion
  "E -> E + T | T\nT -> id",

  // 8: Test 9 — Nullable Recursive Grammar
  "A -> B C\nB -> A | \u03b5\nC -> c | \u03b5",

  // 9: Test 10 — Detailed CFG with Nullable Chains (Section 1)
  "S -> a B D h\nB -> c C\nC -> b C | \u03b5\nD -> E F\nE -> g | \u03b5\nF -> f | \u03b5",

  // 10: Branching Statement (Left Factoring)
  "S -> if E then S else S | if E then S | a\nE -> b",

  // 11: Dangling-Else Ambiguity
  "S -> i E t S SP | a\nSP -> e S | \u03b5\nE -> b"
];

var EXAMPLE_INPUTS = [
  "a",
  "",
  "c",
  "",
  "id + id * id",
  "d",
  "d",
  "id + id",
  "c",
  "a c b g f h",
  "if b then a else a",
  "i b t a e a"
];

// ============================================================
// SECTION 2: UTILITY FUNCTIONS
// ============================================================

var EPS = '\u03b5'; // Canonical epsilon symbol

function isEpsilon(sym) {
  return sym === '\u03b5' || sym === 'eps' || sym === '#' || sym === 'epsilon' || sym === '@';
}

function normSym(sym) {
  return isEpsilon(sym) ? EPS : sym.trim();
}

function looksLikeNT(sym) {
  return sym.length > 0 && /^[A-Z]/.test(sym);
}

function fmtProd(lhs, rhs, ntSet) {
  var rhsHtml = rhs.map(function(s) {
    if (s === EPS) return '<span class="epsilon">\u03b5</span>';
    if (ntSet.has(s)) return '<span class="nt">' + esc(s) + '</span>';
    return '<span class="terminal">' + esc(s) + '</span>';
  }).join(' ');
  return '<span class="nt">' + esc(lhs) + '</span><span class="arrow"> \u2192 </span>' + rhsHtml;
}

function fmtProdText(lhs, rhs) {
  return lhs + ' \u2192 ' + rhs.join(' ');
}

function esc(s) {
  return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}

function cloneGrammar(g) {
  var newRules = new Map();
  g.rules.forEach(function(v, k) {
    newRules.set(k, v.map(function(alt) { return alt.slice(); }));
  });
  return {
    nonTerminals: new Set(g.nonTerminals),
    terminals: new Set(g.terminals),
    rules: newRules,
    startSymbol: g.startSymbol,
    orderedNTs: g.orderedNTs.slice()
  };
}

function collectTerminals(rules, nts) {
  var terms = new Set();
  rules.forEach(function(alts) {
    alts.forEach(function(alt) {
      alt.forEach(function(sym) {
        if (sym !== EPS && !nts.has(sym)) terms.add(sym);
      });
    });
  });
  return terms;
}

function freshNT(base, existing) {
  var name = base + "'";
  while (existing.has(name)) name += "'";
  return name;
}

function ensureGrammarConsistency(g) {
  if (!g) return;
  if (!g.nonTerminals) g.nonTerminals = new Set();
  if (!g.orderedNTs) g.orderedNTs = [];
  if (!g.rules) g.rules = new Map();

  // 1. Any NT in rules must be in nonTerminals
  g.rules.forEach(function(_, nt) {
    g.nonTerminals.add(nt);
  });

  // 2. Any NT in nonTerminals must be in orderedNTs
  g.nonTerminals.forEach(function(nt) {
    if (g.orderedNTs.indexOf(nt) === -1) {
      g.orderedNTs.push(nt);
    }
  });

  // 3. Remove any orderedNTs not in nonTerminals
  g.orderedNTs = g.orderedNTs.filter(function(nt) {
    return g.nonTerminals.has(nt);
  });

  // 3.5 Ensure every non-terminal in nonTerminals has a rules entry
  g.nonTerminals.forEach(function(nt) {
    if (!g.rules.has(nt)) {
      g.rules.set(nt, []);
    }
  });

  // 4. Start symbol fallback
  if (!g.startSymbol && g.orderedNTs.length > 0) {
    g.startSymbol = g.orderedNTs[0];
  }

  // 5. Always refresh terminals set
  g.terminals = collectTerminals(g.rules, g.nonTerminals);
}

function generateSampleInputs(grammar, maxSamples) {
  if (!grammar || !grammar.startSymbol || !grammar.rules) return [];
  maxSamples = maxSamples || 4;
  var nts = grammar.nonTerminals;
  var valid = [];
  var seen = new Set();
  var queue = [ [grammar.startSymbol] ];
  var visitedForms = new Set([ grammar.startSymbol ]);
  var steps = 0;

  while (queue.length > 0 && valid.length < maxSamples && steps < 600) {
    steps++;
    var form = queue.shift();

    // Check if form has non-terminals
    var firstNTIdx = -1;
    for (var i = 0; i < form.length; i++) {
      if (nts.has(form[i])) { firstNTIdx = i; break; }
    }

    if (firstNTIdx === -1) {
      var clean = form.filter(function(s) { return s !== EPS; });
      var str = clean.join(' ');
      if (str.length > 0 && !seen.has(str)) {
        seen.add(str);
        valid.push(str);
      }
      continue;
    }

    var nt = form[firstNTIdx];
    var alts = (grammar.rules.get(nt) || []).slice();
    // Prioritize non-recursive and shorter alternatives first
    alts.sort(function(a, b) { return a.length - b.length; });

    for (var a = 0; a < alts.length; a++) {
      var alt = alts[a];
      var replacement = (alt.length === 1 && alt[0] === EPS) ? [] : alt;
      var nextForm = form.slice(0, firstNTIdx).concat(replacement, form.slice(firstNTIdx + 1));
      var key = nextForm.join(' ');
      if (nextForm.length <= 14 && !visitedForms.has(key)) {
        visitedForms.add(key);
        queue.push(nextForm);
      }
    }
  }

  return valid;
}

// ============================================================
// SECTION 3: GRAMMAR PARSING & VALIDATION
// ============================================================

function tokenizeChunk(chunk, lhsNTs) {
  var tokens = [];
  var pos = 0;

  var sortedNTs = Array.from(lhsNTs).sort(function(a, b) { return b.length - a.length; });
  var multiTerms = ['==', '<=', '>=', '!=', '&&', '||', 'id', 'num', 'while', 'else', 'if', 'then', 'do', 'for'];
  multiTerms.sort(function(a, b) { return b.length - a.length; });

  while (pos < chunk.length) {
    var rem = chunk.slice(pos);

    // 1. Epsilon
    if (rem.charAt(0) === EPS || rem.charAt(0) === '#' || rem.charAt(0) === '@') {
      tokens.push(EPS);
      pos += 1;
      continue;
    }
    if (rem.startsWith('eps')) {
      tokens.push(EPS);
      pos += 3;
      continue;
    }
    if (rem.startsWith('epsilon')) {
      tokens.push(EPS);
      pos += 7;
      continue;
    }

    // 2. Quoted terminal
    if (rem.charAt(0) === "'" || rem.charAt(0) === '"') {
      var quote = rem.charAt(0);
      var endQ = rem.indexOf(quote, 1);
      if (endQ > 0) {
        tokens.push(rem.slice(1, endQ));
        pos += endQ + 1;
        continue;
      }
    }

    // 3. Known LHS non-terminals (longest match first)
    var matchedNT = null;
    for (var i = 0; i < sortedNTs.length; i++) {
      var nt = sortedNTs[i];
      if (rem.startsWith(nt)) {
        matchedNT = nt;
        break;
      }
    }
    if (matchedNT) {
      tokens.push(matchedNT);
      pos += matchedNT.length;
      continue;
    }

    // 4. Multi-character terminal keywords
    var matchedMulti = null;
    for (var i = 0; i < multiTerms.length; i++) {
      var mt = multiTerms[i];
      if (rem.startsWith(mt)) {
        if (pos + mt.length === chunk.length || !/[a-zA-Z0-9_]/.test(chunk.charAt(pos + mt.length))) {
          matchedMulti = mt;
          break;
        }
      }
    }
    if (matchedMulti) {
      tokens.push(matchedMulti);
      pos += matchedMulti.length;
      continue;
    }

    // 5. Capital letter non-terminal (e.g. A, A', A1)
    var ntMatch = rem.match(/^[A-Z]('|[0-9])*/);
    if (ntMatch) {
      tokens.push(ntMatch[0]);
      pos += ntMatch[0].length;
      continue;
    }

    // 6. Lowercase letter terminal
    if (/^[a-z]/.test(rem)) {
      tokens.push(rem.charAt(0));
      pos += 1;
      continue;
    }

    // 7. Operators / punctuation / other characters
    tokens.push(rem.charAt(0));
    pos += 1;
  }

  return tokens;
}

function tokenizeAlternative(altText, lhsNTs) {
  var trimmed = altText.trim();
  if (isEpsilon(trimmed)) return [EPS];
  if (lhsNTs.has(trimmed)) return [trimmed];

  var rawWords = trimmed.split(/\s+/).filter(Boolean);
  var result = [];

  for (var w = 0; w < rawWords.length; w++) {
    var word = rawWords[w];
    if (isEpsilon(word)) {
      result.push(EPS);
    } else if (lhsNTs.has(word)) {
      result.push(word);
    } else if ((word.startsWith("'") && word.endsWith("'") && word.length >= 2) ||
               (word.startsWith('"') && word.endsWith('"') && word.length >= 2)) {
      result.push(word.slice(1, -1));
    } else if (word === 'id' || word === 'num' || word === 'while' || word === 'else' || word === 'if' || word === 'then') {
      result.push(word);
    } else if (word.length === 1) {
      result.push(word);
    } else {
      var subTokens = tokenizeChunk(word, lhsNTs);
      subTokens.forEach(function(st) { result.push(st); });
    }
  }

  return result;
}

function parseGrammarText(text) {
  var errors = [];
  var rules = new Map();
  var orderedNTs = [];
  var nonTerminals = new Set();
  var startSymbol = null;

  var lines = text.split('\n').map(function(l) { return l.trim(); }).filter(function(l) {
    return l.length > 0 && !l.startsWith('//');
  });

  if (lines.length === 0) {
    return { grammar: null, errors: ['No grammar rules provided.'] };
  }

  // PASS 1: Identify all Non-Terminals from LHS of rules
  for (var i = 0; i < lines.length; i++) {
    var line = lines[i];
    var arrowIdx = line.indexOf('->');
    var arrowIdx2 = line.indexOf('\u2192');
    var splitIdx = arrowIdx >= 0 ? arrowIdx : arrowIdx2;

    if (splitIdx < 0) {
      errors.push('Line ' + (i + 1) + ': Missing "->" in production "' + line + '".');
      continue;
    }

    var lhs = line.substring(0, splitIdx).trim();

    if (!lhs) {
      errors.push('Line ' + (i + 1) + ': Empty left-hand side before "->".');
      continue;
    }

    if (lhs.indexOf('$') >= 0) {
      errors.push('Line ' + (i + 1) + ': "$" is reserved as the end-of-input marker and cannot be used in productions.');
      continue;
    }

    if (isEpsilon(lhs)) {
      errors.push('Line ' + (i + 1) + ': Epsilon cannot be on the left-hand side of a production.');
      continue;
    }

    if (!nonTerminals.has(lhs)) {
      nonTerminals.add(lhs);
      orderedNTs.push(lhs);
    }

    if (!startSymbol) {
      startSymbol = lhs;
    }
  }

  if (errors.length > 0 && nonTerminals.size === 0) {
    return { grammar: null, errors: errors };
  }

  // PASS 2: Parse and validate RHS alternatives using tokenizeAlternative
  for (var i = 0; i < lines.length; i++) {
    var line = lines[i];
    var arrowIdx = line.indexOf('->');
    var arrowIdx2 = line.indexOf('\u2192');
    var splitIdx = arrowIdx >= 0 ? arrowIdx : arrowIdx2;
    var arrowLen = arrowIdx >= 0 ? 2 : 1;

    if (splitIdx < 0) continue;

    var lhs = line.substring(0, splitIdx).trim();
    if (!lhs || lhs.indexOf('$') >= 0 || isEpsilon(lhs)) continue;

    var rhsText = line.substring(splitIdx + arrowLen).trim();
    if (!rhsText) {
      errors.push('Line ' + (i + 1) + ': Missing right-hand side for non-terminal "' + lhs + '".');
      continue;
    }

    var altTexts = rhsText.split('|');
    var alts = [];

    for (var j = 0; j < altTexts.length; j++) {
      var altText = altTexts[j].trim();
      if (!altText) {
        errors.push('Line ' + (i + 1) + ', alternative ' + (j + 1) + ': Empty alternative. Use \u03b5, eps, #, or @ for epsilon.');
        continue;
      }

      var rawSymbols = tokenizeAlternative(altText, nonTerminals);
      var symbols = [];
      var hasDollar = false;

      for (var k = 0; k < rawSymbols.length; k++) {
        var sym = rawSymbols[k];
        if (sym.indexOf('$') >= 0) {
          hasDollar = true;
          break;
        }
        symbols.push(normSym(sym));
        // Capital letter = non-terminal convention
        if (sym !== EPS && looksLikeNT(sym) && !nonTerminals.has(sym)) {
          nonTerminals.add(sym);
          orderedNTs.push(sym);
        }
      }

      if (hasDollar) {
        errors.push('Line ' + (i + 1) + ': "$" is reserved as the end-of-input marker and cannot be used in productions.');
        continue;
      }

      if (symbols.length === 0) {
        errors.push('Line ' + (i + 1) + ', alternative ' + (j + 1) + ': No valid symbols found.');
        continue;
      }

      if (symbols.length > 1 && symbols.indexOf(EPS) >= 0) {
        errors.push('Line ' + (i + 1) + ', alternative ' + (j + 1) + ': \u03b5 must be alone in the alternative, not combined with other symbols.');
        continue;
      }

      // Check for duplicate alternative for this LHS
      var isDuplicate = alts.some(function(existingAlt) {
        return existingAlt.length === symbols.length && existingAlt.every(function(s, idx) { return s === symbols[idx]; });
      });

      if (!isDuplicate) {
        alts.push(symbols);
      }
    }

    if (alts.length === 0) {
      if (errors.length === 0) errors.push('Line ' + (i + 1) + ': No valid alternatives for "' + lhs + '".');
      continue;
    }

    if (rules.has(lhs)) {
      var existing = rules.get(lhs);
      alts.forEach(function(a) {
        var alreadyThere = existing.some(function(ea) {
          return ea.length === a.length && ea.every(function(s, idx) { return s === a[idx]; });
        });
        if (!alreadyThere) existing.push(a);
      });
    } else {
      rules.set(lhs, alts);
    }
  }

  if (errors.length > 0 && rules.size === 0) {
    return { grammar: null, errors: errors };
  }

  var terminals = collectTerminals(rules, nonTerminals);
  var gObj = { nonTerminals: nonTerminals, terminals: terminals, rules: rules, startSymbol: startSymbol, orderedNTs: orderedNTs };
  ensureGrammarConsistency(gObj);

  return {
    grammar: gObj,
    errors: errors
  };
}

// ============================================================
// SECTION 4: GRAMMAR ANALYSIS (DETECTION)
// ============================================================

function detectImmediateLeftRecursion(grammar) {
  var details = [];
  grammar.orderedNTs.forEach(function(nt) {
    var alts = grammar.rules.get(nt) || [];
    alts.forEach(function(alt) {
      if (alt[0] === nt) {
        details.push(nt + ' \u2192 ' + alt.join(' ') + ' (immediate left recursion)');
      }
    });
  });
  return { hasIt: details.length > 0, details: details };
}

function detectIndirectLeftRecursion(grammar) {
  var canDerive = new Map();
  grammar.orderedNTs.forEach(function(nt) { canDerive.set(nt, new Set()); });

  grammar.rules.forEach(function(alts, nt) {
    alts.forEach(function(alt) {
      if (alt[0] !== EPS && grammar.nonTerminals.has(alt[0])) {
        canDerive.get(nt).add(alt[0]);
      }
    });
  });

  var changed = true;
  while (changed) {
    changed = false;
    canDerive.forEach(function(reachable, nt) {
      var toAdd = [];
      reachable.forEach(function(r) {
        var rReach = canDerive.get(r);
        if (rReach) rReach.forEach(function(rr) {
          if (!reachable.has(rr)) toAdd.push(rr);
        });
      });
      toAdd.forEach(function(x) { reachable.add(x); changed = true; });
    });
  }

  var details = [];
  canDerive.forEach(function(reachable, nt) {
    if (reachable.has(nt)) details.push(nt + ' can derive itself on the left (left-recursive cycle)');
  });

  return { hasIt: details.length > 0, details: details };
}

function detectCommonPrefixes(grammar) {
  var details = [];
  grammar.rules.forEach(function(alts, nt) {
    if (alts.length < 2) return;
    var seen = new Set();
    for (var i = 0; i < alts.length; i++) {
      for (var j = i + 1; j < alts.length; j++) {
        if (alts[i][0] === alts[j][0] && alts[i][0] !== EPS && !seen.has(nt)) {
          details.push(nt + ': "' + alts[i].join(' ') + '" and "' + alts[j].join(' ') + '" share prefix "' + alts[i][0] + '"');
          seen.add(nt);
        }
      }
    }
  });
  return details;
}

// ============================================================
// SECTION 5: LEFT RECURSION ELIMINATION
// ============================================================

function eliminateImmediateLeftRec(nt, alts, existingNTs) {
  var recursive = [];
  var nonRecursive = [];
  var steps = [];

  alts.forEach(function(alt) {
    if (alt[0] === nt) recursive.push(alt.slice(1));
    else nonRecursive.push(alt);
  });

  if (recursive.length === 0) {
    var m = new Map(); m.set(nt, alts);
    return { changed: false, newRules: m, newNT: null, steps: [] };
  }

  var ntPrime = freshNT(nt, existingNTs);
  existingNTs.add(ntPrime);

  var newAltsA = nonRecursive.map(function(beta) {
    if (beta.length === 1 && beta[0] === EPS) return [ntPrime];
    return beta.concat([ntPrime]);
  });

  var newAltsPrime = recursive.map(function(alpha) { return alpha.concat([ntPrime]); });
  newAltsPrime.push([EPS]);

  steps.push('Found immediate left recursion in ' + nt);
  steps.push('Recursive tails: ' + recursive.map(function(a) { return a.join(' '); }).join('; '));
  steps.push('Non-recursive alts: ' + nonRecursive.map(function(a) { return a.join(' '); }).join('; '));
  steps.push('Rewritten: ' + nt + ' \u2192 ' + newAltsA.map(function(a) { return a.join(' '); }).join(' | '));
  steps.push('New rule: ' + ntPrime + ' \u2192 ' + newAltsPrime.map(function(a) { return a.join(' '); }).join(' | '));

  var newRules = new Map();
  newRules.set(nt, newAltsA);
  newRules.set(ntPrime, newAltsPrime);
  return { changed: true, newRules: newRules, newNT: ntPrime, steps: steps };
}

function eliminateAllLeftRecursion(grammar) {
  var g = cloneGrammar(grammar);
  var allSteps = [];
  var ordNTs = g.orderedNTs.slice();

  allSteps.push('=== Left Recursion Elimination ===');
  allSteps.push('Non-terminal ordering: ' + ordNTs.join(', '));

  var anyChange = false;

  for (var i = 0; i < ordNTs.length; i++) {
    var Ai = ordNTs[i];

    for (var j = 0; j < i; j++) {
      var Aj = ordNTs[j];
      var aiAlts = g.rules.get(Ai) || [];
      var newAlts = [];
      var substituted = false;

      for (var k = 0; k < aiAlts.length; k++) {
        var alt = aiAlts[k];
        if (alt[0] === Aj) {
          var gamma = alt.slice(1);
          var ajAlts = g.rules.get(Aj) || [];
          for (var m = 0; m < ajAlts.length; m++) {
            var delta = ajAlts[m];
            if (delta.length === 1 && delta[0] === EPS) {
              newAlts.push(gamma.length > 0 ? gamma.slice() : [EPS]);
            } else {
              newAlts.push(delta.concat(gamma));
            }
          }
          substituted = true;
        } else {
          newAlts.push(alt);
        }
      }

      if (substituted) {
        anyChange = true;
        g.rules.set(Ai, newAlts);
        allSteps.push('Substituted ' + Aj + ' into ' + Ai + ': ' +
          Ai + ' \u2192 ' + newAlts.map(function(a) { return a.join(' '); }).join(' | '));
      }
    }

    var immResult = eliminateImmediateLeftRec(Ai, g.rules.get(Ai) || [], g.nonTerminals);
    if (immResult.changed) {
      anyChange = true;
      immResult.steps.forEach(function(s) { allSteps.push(s); });
      immResult.newRules.forEach(function(alts, nt) {
        g.rules.set(nt, alts);
        g.nonTerminals.add(nt);
        if (g.orderedNTs.indexOf(nt) === -1) {
          var insertIdx = g.orderedNTs.indexOf(Ai) + 1;
          if (insertIdx <= 0) insertIdx = g.orderedNTs.length;
          g.orderedNTs.splice(insertIdx, 0, nt);
        }
      });
    }
  }

  if (!anyChange) allSteps.push('No left recursion detected \u2014 grammar unchanged.');
  ensureGrammarConsistency(g);
  return { grammar: g, steps: allSteps, changed: anyChange };
}

// ============================================================
// SECTION 6: LEFT FACTORING
// ============================================================

function findLongestCommonPrefix(alts) {
  var bestPrefix = [];
  var bestGroups = null;

  for (var i = 0; i < alts.length; i++) {
    for (var j = i + 1; j < alts.length; j++) {
      var a = alts[i];
      var b = alts[j];
      var pLen = 0;
      while (pLen < a.length && pLen < b.length && a[pLen] === b[pLen] && a[pLen] !== EPS) {
        pLen++;
      }
      if (pLen > bestPrefix.length) {
        bestPrefix = a.slice(0, pLen);
      }
    }
  }

  if (bestPrefix.length === 0) return null;

  var prefixed = [];
  var other = [];

  alts.forEach(function(alt) {
    var matches = true;
    if (alt.length < bestPrefix.length) matches = false;
    else {
      for (var k = 0; k < bestPrefix.length; k++) {
        if (alt[k] !== bestPrefix[k]) { matches = false; break; }
      }
    }
    if (matches) prefixed.push(alt);
    else other.push(alt);
  });

  bestGroups = { prefixed: prefixed, other: other };
  return { prefix: bestPrefix, groups: bestGroups };
}

function leftFactorGrammar(grammar) {
  var g = cloneGrammar(grammar);
  var allSteps = [];
  var anyChange = false;

  allSteps.push('=== Left Factoring ===');

  var changed = true;
  var maxIter = 50;
  while (changed && maxIter-- > 0) {
    changed = false;
    var ntsCopy = g.orderedNTs.slice();

    for (var idx = 0; idx < ntsCopy.length; idx++) {
      var nt = ntsCopy[idx];
      var alts = g.rules.get(nt);
      if (!alts || alts.length < 2) continue;

      var cp = findLongestCommonPrefix(alts);
      if (!cp) continue;

      changed = true;
      anyChange = true;

      var prefix = cp.prefix;
      var grps = cp.groups;
      var newNT = freshNT(nt, g.nonTerminals);
      g.nonTerminals.add(newNT);
      g.orderedNTs.push(newNT);

      allSteps.push('Common prefix in ' + nt + ': "' + prefix.join(' ') + '"');

      var newAltsNT = [];
      newAltsNT.push(prefix.concat([newNT]));
      grps.other.forEach(function(a) { newAltsNT.push(a); });

      var newAltsPrime = [];
      grps.prefixed.forEach(function(a) {
        var suffix = a.slice(prefix.length);
        newAltsPrime.push(suffix.length === 0 ? [EPS] : suffix);
      });

      g.rules.set(nt, newAltsNT);
      g.rules.set(newNT, newAltsPrime);

      allSteps.push('  ' + nt + ' \u2192 ' + newAltsNT.map(function(a) { return a.join(' '); }).join(' | '));
      allSteps.push('  ' + newNT + ' \u2192 ' + newAltsPrime.map(function(a) { return a.join(' '); }).join(' | '));
      break;
    }
  }

  if (!anyChange) allSteps.push('No common prefixes found \u2014 grammar unchanged.');
  ensureGrammarConsistency(g);
  return { grammar: g, steps: allSteps, changed: anyChange };
}

// ============================================================
// SECTION 7: NULLABLE & FIRST SET COMPUTATION ENGINE
// ============================================================

function computeNullableWithReasons(grammar) {
  ensureGrammarConsistency(grammar);
  var nullable = new Set();
  var reasons = new Map();
  var steps = [];
  var changed = true;

  while (changed) {
    changed = false;
    grammar.orderedNTs.forEach(function(nt) {
      if (nullable.has(nt)) return;
      var alts = grammar.rules.get(nt) || [];
      for (var i = 0; i < alts.length; i++) {
        var alt = alts[i];
        if (alt.length === 1 && alt[0] === EPS) {
          nullable.add(nt);
          var r = nt + ' \u2192 \u03b5 directly produces \u03b5';
          reasons.set(nt, r);
          steps.push({ nt: nt, reason: r, rule: nt + ' \u2192 \u03b5' });
          changed = true;
          return;
        }
        var allNull = true;
        for (var j = 0; j < alt.length; j++) {
          if (!nullable.has(alt[j])) { allNull = false; break; }
        }
        if (allNull && alt.length > 0) {
          nullable.add(nt);
          var r = nt + ' \u2192 ' + alt.join(' ') + ' where every symbol {' + alt.join(', ') + '} derives \u03b5';
          reasons.set(nt, r);
          steps.push({ nt: nt, reason: r, rule: nt + ' \u2192 ' + alt.join(' ') });
          changed = true;
          return;
        }
      }
    });
  }

  return { nullable: nullable, reasons: reasons, steps: steps };
}

function computeFirstSets(grammar, nullableSet) {
  ensureGrammarConsistency(grammar);
  if (!nullableSet) {
    var nInfo = computeNullableWithReasons(grammar);
    nullableSet = nInfo.nullable;
  }

  var first = new Map();
  var whyMap = new Map();
  var firstDeps = new Map();
  var simSteps = [];
  var iterationSteps = [];

  grammar.orderedNTs.forEach(function(nt) {
    first.set(nt, new Set());
    firstDeps.set(nt, new Set());
  });
  grammar.nonTerminals.forEach(function(nt) {
    if (!first.has(nt)) first.set(nt, new Set());
    if (!firstDeps.has(nt)) firstDeps.set(nt, new Set());
  });

  function cloneSets() {
    var snap = new Map();
    grammar.orderedNTs.forEach(function(nt) {
      snap.set(nt, new Set(first.get(nt) || []));
    });
    return snap;
  }

  // Initial Step 0
  simSteps.push({
    stepIndex: 0,
    iteration: 0,
    type: 'init',
    nt: grammar.startSymbol || (grammar.orderedNTs[0] || ''),
    ruleStr: 'Initialization',
    added: [],
    reason: 'Initialize all FIRST sets to empty: FIRST(A) = \u2205 for all non-terminals.',
    category: 'Initialization',
    snapshot: cloneSets(),
    changed: false
  });

  var iteration = 0;
  var changed = true;

  while (changed) {
    changed = false;
    iteration++;
    var iterDetails = [];

    grammar.orderedNTs.forEach(function(nt) {
      var alts = grammar.rules.get(nt) || [];

      for (var ai = 0; ai < alts.length; ai++) {
        var alt = alts[ai];
        var ruleStr = nt + ' \u2192 ' + alt.join(' ');

        // Rule: A -> eps
        if (alt.length === 1 && alt[0] === EPS) {
          if (!first.get(nt).has(EPS)) {
            first.get(nt).add(EPS);
            changed = true;
            var reason = 'Rule: ' + ruleStr + ' directly produces \u03b5. Add \u03b5 to FIRST(' + nt + ').';
            whyMap.set(nt + ':' + EPS, reason);
            iterDetails.push({ nt: nt, added: EPS, reason: reason, rule: ruleStr });
            simSteps.push({
              stepIndex: simSteps.length,
              iteration: iteration,
              type: 'rule_eval',
              nt: nt,
              ruleStr: ruleStr,
              added: [EPS],
              reason: reason,
              category: 'Epsilon Production',
              snapshot: cloneSets(),
              changed: true
            });
          }
          continue;
        }

        var allNullable = true;
        var addedThisAlt = [];

        for (var i = 0; i < alt.length; i++) {
          var sym = alt[i];

          // Terminal
          if (grammar.terminals.has(sym)) {
            if (!first.get(nt).has(sym)) {
              first.get(nt).add(sym);
              changed = true;
              addedThisAlt.push(sym);
              var reason = (i === 0)
                ? 'Rule: In ' + ruleStr + ', the first symbol "' + sym + '" is a terminal. Add "' + sym + '" to FIRST(' + nt + ').'
                : 'Rule: In ' + ruleStr + ', preceding symbols ' + alt.slice(0, i).join(' ') + ' derive \u03b5. Symbol "' + sym + '" is a terminal. Add "' + sym + '" to FIRST(' + nt + ').';
              whyMap.set(nt + ':' + sym, reason);
              iterDetails.push({ nt: nt, added: sym, reason: reason, rule: ruleStr });
            }
            allNullable = false;
            break;
          }

          // Non-Terminal
          if (grammar.nonTerminals.has(sym)) {
            if (nt !== sym) firstDeps.get(nt).add(sym);
            var fs = first.get(sym);
            if (fs) {
              fs.forEach(function(t) {
                if (t !== EPS && !first.get(nt).has(t)) {
                  first.get(nt).add(t);
                  changed = true;
                  addedThisAlt.push(t);
                  var reason = (i === 0)
                    ? 'Rule: In ' + ruleStr + ', first symbol is non-terminal ' + sym + '. Propagate FIRST(' + sym + ') \u2216 {\u03b5} into FIRST(' + nt + '). Added "' + t + '".'
                    : 'Rule: In ' + ruleStr + ', preceding symbols ' + alt.slice(0, i).join(' ') + ' derive \u03b5. Propagate FIRST(' + sym + ') \u2216 {\u03b5} into FIRST(' + nt + '). Added "' + t + '".';
                  whyMap.set(nt + ':' + t, reason);
                  iterDetails.push({ nt: nt, added: t, reason: reason, rule: ruleStr });
                }
              });
            }

            if (!nullableSet.has(sym)) {
              allNullable = false;
              break;
            }
          } else {
            // Unknown symbol, treat as terminal
            if (!first.get(nt).has(sym)) {
              first.get(nt).add(sym);
              changed = true;
              addedThisAlt.push(sym);
              var reason = 'In ' + ruleStr + ', symbol "' + sym + '" is a terminal. Add "' + sym + '" to FIRST(' + nt + ').';
              whyMap.set(nt + ':' + sym, reason);
              iterDetails.push({ nt: nt, added: sym, reason: reason, rule: ruleStr });
            }
            allNullable = false;
            break;
          }
        }

        if (allNullable && !first.get(nt).has(EPS)) {
          first.get(nt).add(EPS);
          changed = true;
          addedThisAlt.push(EPS);
          var reason = 'Rule: In ' + ruleStr + ', all symbols in RHS {' + alt.join(', ') + '} derive \u03b5. Add \u03b5 to FIRST(' + nt + ').';
          whyMap.set(nt + ':' + EPS, reason);
          iterDetails.push({ nt: nt, added: EPS, reason: reason, rule: ruleStr });
        }

        if (addedThisAlt.length > 0) {
          simSteps.push({
            stepIndex: simSteps.length,
            iteration: iteration,
            type: 'rule_eval',
            nt: nt,
            ruleStr: ruleStr,
            added: addedThisAlt,
            reason: addedThisAlt.map(function(s) { return whyMap.get(nt + ':' + s); }).join('; '),
            category: 'Symbol Propagation',
            snapshot: cloneSets(),
            changed: true
          });
        }
      }
    });

    iterationSteps.push({ num: iteration, details: iterDetails, sets: cloneSets(), changed: changed });
  }

  // Final Convergence step
  simSteps.push({
    stepIndex: simSteps.length,
    iteration: iteration,
    type: 'converged',
    nt: grammar.startSymbol || '',
    ruleStr: 'Convergence Reached',
    added: [],
    reason: 'Fixed-point convergence reached in ' + iteration + ' iteration(s). No new symbols added across all non-terminals. FIRST sets are complete and stable.',
    category: 'Fixed Point',
    snapshot: cloneSets(),
    changed: false
  });

  var firstOfNTs = new Map();
  grammar.nonTerminals.forEach(function(nt) { firstOfNTs.set(nt, first.get(nt) || new Set()); });

  return {
    firstSets: firstOfNTs,
    steps: iterationSteps,
    whyMap: whyMap,
    deps: firstDeps,
    simSteps: simSteps,
    iterations: iteration
  };
}

function firstOfSequence(seq, firstSets, nullableSet) {
  var result = new Set();
  if (!seq || seq.length === 0) { result.add(EPS); return result; }

  var allDeriveEps = true;
  for (var i = 0; i < seq.length; i++) {
    var sym = seq[i];
    if (sym === EPS) continue;

    if (firstSets && firstSets.has(sym)) {
      var sf = firstSets.get(sym);
      sf.forEach(function(t) {
        if (t !== EPS) result.add(t);
      });

      var isSymNull = sf.has(EPS) || (nullableSet && nullableSet.has(sym));
      if (!isSymNull) {
        allDeriveEps = false;
        break;
      }
    } else {
      // Terminal
      result.add(sym);
      allDeriveEps = false;
      break;
    }
  }

  if (allDeriveEps) result.add(EPS);
  return result;
}

// ============================================================
// SECTION 8: FOLLOW SET COMPUTATION ENGINE
// ============================================================

function computeFollowSets(grammar, firstSets, nullableSet) {
  ensureGrammarConsistency(grammar);
  if (!nullableSet) {
    var nInfo = computeNullableWithReasons(grammar);
    nullableSet = nInfo.nullable;
  }

  var follow = new Map();
  var whyMap = new Map();
  var followDeps = new Map();
  var simSteps = [];
  var iterationSteps = [];

  grammar.orderedNTs.forEach(function(nt) {
    follow.set(nt, new Set());
    followDeps.set(nt, new Set());
  });
  grammar.nonTerminals.forEach(function(nt) {
    if (!follow.has(nt)) follow.set(nt, new Set());
    if (!followDeps.has(nt)) followDeps.set(nt, new Set());
  });

  function cloneSets() {
    var snap = new Map();
    grammar.orderedNTs.forEach(function(nt) {
      snap.set(nt, new Set(follow.get(nt) || []));
    });
    return snap;
  }

  // Rule 1: $ in FOLLOW(startSymbol)
  if (grammar.startSymbol) {
    if (!follow.has(grammar.startSymbol)) follow.set(grammar.startSymbol, new Set());
    follow.get(grammar.startSymbol).add('$');
    var r1 = 'Rule 1: Start symbol "' + grammar.startSymbol + '" is assigned the end-of-input marker "$". Add $ to FOLLOW(' + grammar.startSymbol + ').';
    whyMap.set(grammar.startSymbol + ':$', r1);

    simSteps.push({
      stepIndex: 0,
      iteration: 0,
      type: 'rule_eval',
      nt: grammar.startSymbol,
      ruleStr: 'FOLLOW(' + grammar.startSymbol + ') \u2190 { $ }',
      added: ['$'],
      reason: r1,
      category: 'Start Symbol Rule',
      snapshot: cloneSets(),
      changed: true
    });

    iterationSteps.push({
      num: 0,
      details: [{ nt: grammar.startSymbol, added: '$', reason: r1, rule: 'Rule 1' }],
      sets: cloneSets(),
      changed: true
    });
  }

  var iteration = 0;
  var changed = true;

  while (changed) {
    changed = false;
    iteration++;
    var iterDetails = [];

    grammar.orderedNTs.forEach(function(A) {
      var alts = grammar.rules.get(A) || [];

      for (var ai = 0; ai < alts.length; ai++) {
        var alt = alts[ai];
        var ruleStr = A + ' \u2192 ' + alt.join(' ');

        for (var i = 0; i < alt.length; i++) {
          var B = alt[i];
          if (!grammar.nonTerminals.has(B)) continue;

          var beta = alt.slice(i + 1);
          var firstBeta = firstOfSequence(beta, firstSets, nullableSet);
          var addedForB = [];

          // Rule 2: In A -> alpha B beta, add FIRST(beta) - {eps} to FOLLOW(B)
          firstBeta.forEach(function(b) {
            if (b !== EPS) {
              if (!follow.has(B)) follow.set(B, new Set());
              if (!follow.get(B).has(b)) {
                follow.get(B).add(b);
                changed = true;
                addedForB.push(b);
                var reason = 'Rule 2: In ' + ruleStr + ', symbol ' + B + ' is followed by "' + (beta.length > 0 ? beta.join(' ') : '\u03b5') + '". FIRST(' + (beta.length > 0 ? beta.join(' ') : '\u03b5') + ') contains "' + b + '". Add "' + b + '" to FOLLOW(' + B + ').';
                whyMap.set(B + ':' + b, reason);
                iterDetails.push({ nt: B, added: b, reason: reason, rule: ruleStr });
              }
            }
          });

          // Rule 3: If beta is empty or beta derives eps: FOLLOW(A) <= FOLLOW(B)
          if (beta.length === 0 || firstBeta.has(EPS)) {
            if (A !== B) followDeps.get(B).add(A);
            var followA = follow.get(A) || new Set();
            followA.forEach(function(a) {
              if (!follow.has(B)) follow.set(B, new Set());
              if (!follow.get(B).has(a)) {
                follow.get(B).add(a);
                changed = true;
                addedForB.push(a);
                var reason = (beta.length === 0)
                  ? 'Rule 3: In ' + ruleStr + ', ' + B + ' is at the end of the production. Everything that follows ' + A + ' can follow ' + B + ' (FOLLOW(' + A + ') \u2286 FOLLOW(' + B + ')). Added "' + a + '".'
                  : 'Rule 3: In ' + ruleStr + ', suffix "' + beta.join(' ') + '" can derive \u03b5. Everything that follows ' + A + ' can follow ' + B + ' (FOLLOW(' + A + ') \u2286 FOLLOW(' + B + ')). Added "' + a + '".';
                whyMap.set(B + ':' + a, reason);
                iterDetails.push({ nt: B, added: a, reason: reason, rule: ruleStr });
              }
            });
          }

          if (addedForB.length > 0) {
            simSteps.push({
              stepIndex: simSteps.length,
              iteration: iteration,
              type: 'rule_eval',
              nt: B,
              ruleStr: ruleStr + ' [Target: ' + B + ']',
              added: addedForB,
              reason: addedForB.map(function(s) { return whyMap.get(B + ':' + s); }).join('; '),
              category: (beta.length === 0 || firstBeta.has(EPS)) ? 'Rightmost / Nullable Suffix Rule' : 'Adjacent Symbol FIRST Rule',
              snapshot: cloneSets(),
              changed: true
            });
          }
        }
      }
    });

    iterationSteps.push({ num: iteration, details: iterDetails, sets: cloneSets(), changed: changed });
  }

  // Final Convergence step
  simSteps.push({
    stepIndex: simSteps.length,
    iteration: iteration,
    type: 'converged',
    nt: grammar.startSymbol || '',
    ruleStr: 'Convergence Reached',
    added: [],
    reason: 'Fixed-point convergence reached in ' + iteration + ' iteration(s). No new symbols added across all non-terminals. FOLLOW sets are complete and stable.',
    category: 'Fixed Point',
    snapshot: cloneSets(),
    changed: false
  });

  grammar.nonTerminals.forEach(function(nt) {
    if (!follow.has(nt)) follow.set(nt, new Set());
  });

  return {
    followSets: follow,
    steps: iterationSteps,
    whyMap: whyMap,
    deps: followDeps,
    simSteps: simSteps,
    iterations: iteration
  };
}

// ============================================================
// SECTION 9: LL(1) PARSING TABLE CONSTRUCTION
// ============================================================

function buildParseTable(grammar, firstSets, followSets) {
  var table = new Map();
  var whyMap = new Map();
  var terminalsList = [];

  grammar.terminals.forEach(function(t) { terminalsList.push(t); });
  terminalsList.sort();
  terminalsList.push('$');

  grammar.orderedNTs.forEach(function(nt) {
    var row = new Map();
    terminalsList.forEach(function(t) { row.set(t, []); });
    table.set(nt, row);
  });

  grammar.orderedNTs.forEach(function(nt) {
    var alts = grammar.rules.get(nt) || [];
    alts.forEach(function(alt) {
      var firstAlpha = firstOfSequence(alt, firstSets);

      firstAlpha.forEach(function(a) {
        if (a !== EPS) {
          var row = table.get(nt);
          if (row && row.has(a)) {
            row.get(a).push(alt);
            var key = nt + ':' + a;
            var reason = nt + ' \u2192 ' + alt.join(' ') + ' because ' + a + ' \u2208 FIRST(' + alt.join(' ') + ')';
            if (whyMap.has(key)) {
              whyMap.set(key, whyMap.get(key) + '; ALSO ' + reason);
            } else {
              whyMap.set(key, reason);
            }
          }
        }
      });

      if (firstAlpha.has(EPS)) {
        var followNT = followSets.get(nt) || new Set();
        followNT.forEach(function(b) {
          var row = table.get(nt);
          if (row && row.has(b)) {
            var entries = row.get(b);
            var alreadyThere = entries.some(function(e) {
              return e.length === alt.length && e.every(function(s, idx) { return s === alt[idx]; });
            });
            if (!alreadyThere) entries.push(alt);
            var key = nt + ':' + b;
            var reason = nt + ' \u2192 ' + alt.join(' ') + ' because \u03b5 \u2208 FIRST(' + alt.join(' ') + ') and ' + b + ' \u2208 FOLLOW(' + nt + ')';
            if (whyMap.has(key)) {
              whyMap.set(key, whyMap.get(key) + '; ALSO ' + reason);
            } else {
              whyMap.set(key, reason);
            }
          }
        });
      }
    });
  });

  return { table: table, terminals: terminalsList, whyMap: whyMap };
}

// ============================================================
// SECTION 10: CONFLICT DETECTION & EXPLANATION
// ============================================================

function detectConflicts(table, grammar, firstSets, followSets) {
  var conflicts = [];

  table.forEach(function(row, nt) {
    row.forEach(function(entries, terminal) {
      if (entries.length > 1) {
        var prods = entries.map(function(e) { return nt + ' \u2192 ' + e.join(' '); });
        var type = 'Unknown';
        var explanation = '';
        var suggestion = '';

        var firstConflictCount = 0;
        var followConflictCount = 0;
        entries.forEach(function(alt) {
          var f = firstOfSequence(alt, firstSets);
          if (f.has(terminal)) firstConflictCount++;
          if (f.has(EPS)) followConflictCount++;
        });

        if (firstConflictCount > 1) {
          type = 'FIRST/FIRST';
          explanation = 'Productions ' + prods.join(' and ') + " both have '" + terminal + "' in their FIRST set.";
          suggestion = 'Try left factoring the common prefix, or rewrite the grammar to remove the ambiguity.';
        } else if (followConflictCount > 0 && firstConflictCount > 0) {
          type = 'FIRST/FOLLOW';
          explanation = nt + " is nullable and FIRST(" + nt + ") overlaps with FOLLOW(" + nt + ") on token '" + terminal + "'.";
          suggestion = 'This often indicates ambiguity. Consider whether the \u03b5-production for ' + nt + ' is necessary, or restructure the grammar.';
        } else {
          type = 'FIRST/FOLLOW';
          explanation = "Multiple productions for " + nt + " are applicable when lookahead is '" + terminal + "'.";
          suggestion = 'Review the grammar for ambiguity or left recursion.';
        }

        var alts = grammar.rules.get(nt) || [];
        var hasLR = alts.some(function(alt) { return alt[0] === nt; });
        if (hasLR) {
          suggestion = nt + ' has left recursion. Eliminate left recursion first, then try again.';
        }

        conflicts.push({
          nt: nt, terminal: terminal, type: type,
          explanation: explanation, suggestion: suggestion,
          productions: prods
        });
      }
    });
  });

  return { isLL1: conflicts.length === 0, conflicts: conflicts };
}

// ============================================================
// SECTION 11: PARSING SIMULATION ENGINE
// ============================================================

function runParsingSimulation(inputTokens, table, grammar, followSets) {
  var tokens = inputTokens.concat(['$']);
  var ptr = 0;
  var stack = ['$', grammar.startSymbol];
  var trace = [];
  var errors = [];
  var stepNum = 0;
  var accepted = false;

  var nodeId = 1;
  var treeRoot = { symbol: grammar.startSymbol, children: [], id: 0 };
  var treeStack = [null, treeRoot];

  function recordStep(action, cellNT, cellT) {
    stepNum++;
    var stackDisplay = stack.slice().reverse();
    trace.push({
      step: stepNum,
      stack: stackDisplay.join(' '),
      rawStack: stack.slice(),
      input: tokens.slice(ptr).join(' '),
      rawInput: tokens.slice(),
      ptr: ptr,
      action: action,
      cellNT: cellNT || '',
      cellT: cellT || ''
    });
  }

  var MAX_STEPS = 500;

  while (stepNum < MAX_STEPS) {
    var top = stack[stack.length - 1];
    var current = tokens[ptr];

    if (top === '$' && current === '$') {
      recordStep('\u2705 Accept!');
      accepted = true;
      break;
    }

    if (top === '$') {
      recordStep('\u274c Error: Stack empty but input has \'' + current + '\'');
      errors.push('Unexpected token \'' + current + '\' \u2014 stack is empty.');
      break;
    }

    // Top is a terminal
    if (!grammar.nonTerminals.has(top)) {
      if (top === current) {
        recordStep('Match \'' + top + '\'');
        stack.pop();
        treeStack.pop();
        ptr++;
      } else {
        recordStep('\u274c Error: Expected \'' + top + '\' but found \'' + current + '\'');
        errors.push('Mismatch: expected \'' + top + '\', found \'' + current + '\' at position ' + (ptr + 1) + '.');
        stack.pop();
        treeStack.pop();
      }
      continue;
    }

    // Top is a non-terminal
    var row = table.get(top);
    if (!row) {
      recordStep('\u274c Error: No table row for ' + top);
      errors.push('Internal error: non-terminal \'' + top + '\' not in table.');
      stack.pop();
      treeStack.pop();
      continue;
    }

    var entries = row.get(current);
    if (!entries || entries.length === 0) {
      // Panic-mode recovery
      var followSet = (followSets && followSets.get(top)) ? followSets.get(top) : new Set();
      var expectedTokens = [];
      row.forEach(function(e, t) { if (e.length > 0) expectedTokens.push(t); });
      var expectedStr = expectedTokens.map(function(t) { return '\'' + t + '\''; }).join(', ');
      recordStep('\u274c Error: No entry M[' + top + ', ' + current + ']. Expected: ' + expectedStr);
      errors.push('Syntax error at \'' + current + '\' (pos ' + (ptr + 1) + '). Expected: ' + expectedStr + '. Panic-mode: skip until FOLLOW(' + top + ').');

      var recovered = false;
      while (ptr < tokens.length) {
        if (tokens[ptr] === '$') break;
        if (followSet.has(tokens[ptr])) {
          stack.pop();
          treeStack.pop();
          recordStep('\ud83d\udd27 Recovery: popped ' + top + ', synced on \'' + tokens[ptr] + '\'');
          recovered = true;
          break;
        }
        var rowCheck = table.get(top);
        var entriesCheck = rowCheck ? rowCheck.get(tokens[ptr]) : null;
        if (entriesCheck && entriesCheck.length > 0) {
          recordStep('\ud83d\udd27 Recovery: synced on \'' + tokens[ptr] + '\', retrying ' + top);
          recovered = true;
          break;
        }
        ptr++;
        recordStep('\ud83d\udd27 Recovery: skipped \'' + tokens[ptr - 1] + '\'');
      }
      if (!recovered) { stack.pop(); treeStack.pop(); }
      continue;
    }

    var production = entries[0];
    var prodStr = top + ' \u2192 ' + production.join(' ');
    recordStep('Expand: ' + prodStr, top, current);

    stack.pop();
    var treeNode = treeStack.pop();

    if (production.length === 1 && production[0] === EPS) {
      if (treeNode) treeNode.children.push({ symbol: EPS, children: [], id: nodeId++ });
    } else {
      var childNodes = [];
      for (var ci = 0; ci < production.length; ci++) {
        childNodes.push({ symbol: production[ci], children: [], id: nodeId++ });
      }
      if (treeNode) treeNode.children = childNodes;

      for (var ri = production.length - 1; ri >= 0; ri--) {
        stack.push(production[ri]);
        treeStack.push(childNodes[ri]);
      }
    }
  }

  if (stepNum >= MAX_STEPS) {
    errors.push('Parsing exceeded maximum step limit (possible infinite loop).');
  }

  return { trace: trace, accepted: accepted, errors: errors, treeRoot: treeRoot };
}

// ============================================================
// SECTION 12: PARSE TREE RENDERING (VECTOR SVG)
// ============================================================

function renderParseTreeSVG(root, ntSet) {
  if (!root) return '<p class="text-muted">No parse tree available.</p>';

  var NODE_W = 56;
  var NODE_H = 32;
  var H_GAP = 16;
  var V_GAP = 56;
  var PAD = 35;

  function computeWidth(node) {
    if (!node.children || node.children.length === 0) {
      node._width = NODE_W + H_GAP;
      return node._width;
    }
    var totalW = 0;
    node.children.forEach(function(ch) { totalW += computeWidth(ch); });
    node._width = Math.max(totalW, NODE_W + H_GAP);
    return node._width;
  }

  function assignPositions(node, x, y) {
    node._y = y;
    if (!node.children || node.children.length === 0) {
      node._x = x + node._width / 2;
      return;
    }
    var childX = x;
    node.children.forEach(function(ch) {
      assignPositions(ch, childX, y + V_GAP + NODE_H);
      childX += ch._width;
    });
    node._x = (node.children[0]._x + node.children[node.children.length - 1]._x) / 2;
  }

  computeWidth(root);
  assignPositions(root, PAD, PAD);

  var maxX = 0, maxY = 0;
  function findBounds(node) {
    maxX = Math.max(maxX, node._x + NODE_W / 2 + PAD);
    maxY = Math.max(maxY, node._y + NODE_H + PAD);
    (node.children || []).forEach(findBounds);
  }
  findBounds(root);

  var svgW = Math.max(maxX + PAD, 420);
  var svgH = Math.max(maxY + PAD, 220);

  var svg = '<svg id="parseTreeSvg" width="' + svgW + '" height="' + svgH + '" viewBox="0 0 ' + svgW + ' ' + svgH + '" xmlns="http://www.w3.org/2000/svg">';

  // Draw smooth cubic bezier edges
  function drawEdges(node) {
    (node.children || []).forEach(function(child) {
      svg += '<path class="edge" d="M' + node._x + ',' + (node._y + NODE_H / 2) +
        ' C' + node._x + ',' + ((node._y + child._y) / 2 + NODE_H / 2) +
        ' ' + child._x + ',' + ((node._y + child._y) / 2 + NODE_H / 2) +
        ' ' + child._x + ',' + (child._y - NODE_H / 2) + '"/>';
      drawEdges(child);
    });
  }
  drawEdges(root);

  // Draw node rectangles and labels
  function drawNodes(node) {
    var isNT = ntSet && ntSet.has(node.symbol);
    var isEps = node.symbol === EPS;
    var cls = isEps ? 'node-eps' : (isNT ? 'node-nt' : 'node-t');
    var labelCls = isEps ? 'label-eps' : (isNT ? 'label-nt' : 'label-t');
    var label = isEps ? '\u03b5' : node.symbol;
    var fontSize = label.length > 3 ? 10.5 : 12;

    svg += '<rect class="' + cls + '" x="' + (node._x - NODE_W / 2) + '" y="' + (node._y - NODE_H / 2) +
      '" width="' + NODE_W + '" height="' + NODE_H + '" rx="3" ry="3"/>';
    svg += '<text class="' + labelCls + '" x="' + node._x + '" y="' + node._y +
      '" font-size="' + fontSize + '">' + esc(label) + '</text>';

    (node.children || []).forEach(drawNodes);
  }
  drawNodes(root);

  svg += '</svg>';
  return svg;
}

// ============================================================
// SECTION 13: UI - TAB SWITCHING
// ============================================================

function switchTab(tabId) {
  document.querySelectorAll('.section').forEach(function(s) { s.classList.remove('active'); });
  document.querySelectorAll('.tab-btn').forEach(function(b) { b.classList.remove('active'); });

  var sec = document.getElementById('sec-' + tabId);
  if (sec) sec.classList.add('active');

  var btn = document.querySelector('.tab-btn[data-tab="' + tabId + '"]');
  if (btn) btn.classList.add('active');

  if (tabId === 'tree') {
    renderTreeTab();
  } else if (tabId === 'simulate') {
    renderSimulateTab();
  }
}

// ============================================================
// SECTION 14: UI - LOAD EXAMPLES & CLEAR
// ============================================================

function insertEps(symbol) {
  var txt = document.getElementById('txtGrammar');
  if (!txt) return;
  var start = txt.selectionStart !== undefined ? txt.selectionStart : txt.value.length;
  var end = txt.selectionEnd !== undefined ? txt.selectionEnd : txt.value.length;
  var val = txt.value;
  txt.value = val.substring(0, start) + symbol + val.substring(end);
  txt.focus();
  txt.selectionStart = txt.selectionEnd = start + symbol.length;
  updateEditorStats();
}

function formatGrammar() {
  var txt = document.getElementById('txtGrammar');
  if (!txt) return;
  var raw = txt.value;
  if (!raw.trim()) return;

  var lines = raw.split('\n');
  var formatted = [];

  lines.forEach(function(line) {
    var trimmed = line.trim();
    if (!trimmed) {
      if (formatted.length > 0 && formatted[formatted.length - 1] !== '') {
        formatted.push('');
      }
      return;
    }
    // Check if line contains arrow
    var arrowMatch = trimmed.match(/^([A-Za-z0-9_']+)\s*(?:->|-->|=>|→)\s*(.*)$/);
    if (arrowMatch) {
      var lhs = arrowMatch[1];
      var rhsPart = arrowMatch[2];
      // Normalize eps / # in RHS and format alternatives
      var alts = rhsPart.split('|').map(function(alt) {
        var tokens = alt.trim().split(/\s+/).filter(Boolean).map(function(sym) {
          if (sym === 'eps' || sym === 'epsilon' || sym === '#') return EPS;
          return sym;
        });
        return tokens.join(' ');
      });
      formatted.push(lhs + ' -> ' + alts.join(' | '));
    } else {
      formatted.push(trimmed);
    }
  });

  txt.value = formatted.join('\n');
  updateEditorStats();
  analyzeGrammar();
}

function updateEditorStats() {
  var txt = document.getElementById('txtGrammar');
  if (!txt) return;
  var val = txt.value;
  var lines = val.split('\n').filter(function(l) { return l.trim().length > 0; }).length;
  var rulesCount = 0;
  val.split('\n').forEach(function(l) {
    if (/->|→/.test(l)) {
      var parts = l.split(/->|→/);
      if (parts[1]) rulesCount += parts[1].split('|').length;
    }
  });

  var el = document.getElementById('editorStats');
  if (el) {
    el.innerHTML = lines + ' rules &bull; ' + rulesCount + ' prods';
  }
  var sbRules = document.getElementById('statusRuleCount');
  if (sbRules) {
    sbRules.textContent = rulesCount + ' Productions';
  }
}

function loadExample(idx) {
  if (idx === '' || idx === undefined) return;
  var i = parseInt(idx);
  document.getElementById('txtGrammar').value = EXAMPLES[i];
  var sel = document.getElementById('selExample');
  if (sel) sel.value = String(i);
  document.getElementById('grammarErrors').innerHTML = '';

  document.querySelectorAll('.preset-chip').forEach(function(chip) {
    chip.classList.toggle('active', chip.getAttribute('onclick') === "loadExample('" + i + "')");
  });

  updateEditorStats();
  analyzeGrammar();
}

function clearAll() {
  var txtG = document.getElementById('txtGrammar');
  if (txtG) txtG.value = '';
  var selEx = document.getElementById('selExample');
  if (selEx) selEx.value = '';
  document.getElementById('grammarErrors').innerHTML = '';
  document.getElementById('grammarInfo').innerHTML = '<p class="text-muted">Enter or select a grammar and click <strong>Analyze</strong> to begin.</p>';
  G = null; G_transformed = null; G_active = null;
  FIRST_SETS = null; FOLLOW_SETS = null; PARSE_TABLE = null;
  simTrace = []; parseTreeRoot = null;

  ['summary','first','follow','graph','preprocess','table','conflicts','simulate'].forEach(function(tab) {
    var el = document.getElementById('sec-' + tab);
    var content = el ? el.querySelector('[id$="Content"]') : null;
    if (content) content.innerHTML = '<p class="text-muted">Analyze a grammar first.</p>';
  });

  var tc = document.getElementById('treeContent');
  if (tc) tc.innerHTML = '<p class="text-muted">Enter or select a grammar and click <strong>Run Analysis</strong> to view its parse tree.</p>';
  var ts = document.getElementById('treeStatus');
  if (ts) ts.innerHTML = '';
  var tq = document.getElementById('treeQuickInputs');
  if (tq) tq.innerHTML = '';

  var headerStatus = document.getElementById('headerStatus');
  if (headerStatus) {
    headerStatus.className = 'status-pill status-ready';
    headerStatus.innerHTML = '<span class="status-dot"></span> Ready';
  }

  var sbSum = document.getElementById('statusGrammarSummary');
  if (sbSum) sbSum.textContent = 'Grammar: Ready';
  var sbDet = document.getElementById('statusDeterminism');
  if (sbDet) sbDet.textContent = 'LL(1) Ready';
  var sbRules = document.getElementById('statusRuleCount');
  if (sbRules) sbRules.textContent = '0 Rules';

  document.querySelectorAll('.preset-chip').forEach(function(chip) { chip.classList.remove('active'); });
  document.querySelectorAll('.tab-btn .badge').forEach(function(b) { b.remove(); });
  if (autoPlayInterval) { clearInterval(autoPlayInterval); autoPlayInterval = null; }
  updateEditorStats();
}

// ============================================================
// SECTION 15: UI - MAIN ANALYZE FUNCTION
// ============================================================

function analyzeGrammar() {
  var text = document.getElementById('txtGrammar').value.trim();
  if (!text) { showErrors(['Please enter a grammar.']); return; }

  var result = parseGrammarText(text);
  if (result.errors.length > 0) {
    showErrors(result.errors);
    if (!result.grammar) return;
  } else {
    document.getElementById('grammarErrors').innerHTML = '';
  }

  G = result.grammar;

  var immLR = detectImmediateLeftRecursion(G);
  var indLR = detectIndirectLeftRecursion(G);
  var commonPrefixes = detectCommonPrefixes(G);

  renderGrammarInfo(G, immLR, indLR, commonPrefixes);

  // Preprocessing
  preprocessResult = runPreprocessing(G);
  renderPreprocessing(preprocessResult);

  G_active = preprocessResult.transformed ? preprocessResult.transformed : G;
  if (preprocessResult.transformed) G_transformed = preprocessResult.transformed;

  // Nullable Computation with reasons
  NULLABLE_INFO = computeNullableWithReasons(G_active);

  // FIRST Sets & Simulation Trace
  var firstResult = computeFirstSets(G_active, NULLABLE_INFO.nullable);
  FIRST_SETS = firstResult.firstSets;
  FIRST_SIM_STEPS = firstResult.simSteps;
  FIRST_DEPS = firstResult.deps;
  firstWhyMap = firstResult.whyMap;
  firstSimIndex = FIRST_SIM_STEPS.length > 0 ? FIRST_SIM_STEPS.length - 1 : 0;
  if (firstSimTimer) { clearInterval(firstSimTimer); firstSimTimer = null; }

  // FOLLOW Sets & Simulation Trace
  var followResult = computeFollowSets(G_active, FIRST_SETS, NULLABLE_INFO.nullable);
  FOLLOW_SETS = followResult.followSets;
  FOLLOW_SIM_STEPS = followResult.simSteps;
  FOLLOW_DEPS = followResult.deps;
  followWhyMap = followResult.whyMap;
  followSimIndex = FOLLOW_SIM_STEPS.length > 0 ? FOLLOW_SIM_STEPS.length - 1 : 0;
  if (followSimTimer) { clearInterval(followSimTimer); followSimTimer = null; }

  // Render Summary Overview Table
  renderSummaryTable();

  // Render FIRST and FOLLOW Interactive Engines
  renderFirstSets();
  renderFollowSets();

  // Render Dependency Graph & Symbol Inspector
  inspectorNT = G_active.startSymbol || (G_active.orderedNTs[0] || null);
  renderDependencyGraph();

  // Parse Table
  var tableResult = buildParseTable(G_active, FIRST_SETS, FOLLOW_SETS);
  PARSE_TABLE = tableResult.table;
  tableWhyMap = tableResult.whyMap;
  renderParseTable(tableResult.terminals);

  // Conflicts
  var conflictResult = detectConflicts(PARSE_TABLE, G_active, FIRST_SETS, FOLLOW_SETS);
  conflictInfo = conflictResult.conflicts;
  renderConflicts(conflictResult);

  updateBadges(immLR, indLR, commonPrefixes, conflictResult);

  // Derive valid test sentences directly from this user-made/active grammar
  var sampleInputs = generateSampleInputs(G_active, 5);
  var defInput = sampleInputs.length > 0 ? sampleInputs[0] : (G_active.terminals.size > 0 ? Array.from(G_active.terminals)[0] : '');

  var simIn = document.getElementById('simInput');
  if (simIn) simIn.value = defInput;
  var treeIn = document.getElementById('treeInput');
  if (treeIn) treeIn.value = defInput;

  renderSimulateUI(sampleInputs);
  renderTreeQuickInputs(sampleInputs);

  // Automatically execute simulation and build tree for user grammar input
  autoRunSimulation(defInput);
}

function showErrors(errors) {
  document.getElementById('grammarErrors').innerHTML =
    '<div class="banner banner-error"><span>\u26a0</span><ul class="error-list">' +
    errors.map(function(e) { return '<li>\u2022 ' + esc(e) + '</li>'; }).join('') +
    '</ul></div>';
}

// ============================================================
// SECTION 16: UI - RENDER GRAMMAR INFO
// ============================================================

function getNullableNTs(g) {
  var nullables = new Set();
  var changed = true;
  while (changed) {
    changed = false;
    g.orderedNTs.forEach(function(nt) {
      if (nullables.has(nt)) return;
      var alts = g.rules.get(nt) || [];
      for (var i = 0; i < alts.length; i++) {
        var alt = alts[i];
        if (alt.length === 1 && alt[0] === EPS) {
          nullables.add(nt);
          changed = true;
          break;
        }
        if (alt.length > 0 && alt.every(function(s) { return nullables.has(s); })) {
          nullables.add(nt);
          changed = true;
          break;
        }
      }
    });
  }
  return nullables;
}

function renderGrammarInfo(g, immLR, indLR, prefixes) {
  var totalProds = 0;
  g.orderedNTs.forEach(function(nt) {
    totalProds += (g.rules.get(nt) || []).length;
  });
  var nullables = getNullableNTs(g);
  var isLL1Compatible = !immLR.hasIt && !indLR.hasIt && prefixes.length === 0;

  var html = '<div class="bento-grid">';

  // Card 1: Start Symbol & Grammatical Root
  html += '<div class="bento-card">' +
    '<div class="bento-header"><span class="bento-title">Start Symbol</span><span class="bento-tag">LHS #1</span></div>' +
    '<div class="bento-val"><span class="bento-chip nt" style="font-size:13px;padding:2px 8px;">' + esc(g.startSymbol) + '</span>' +
    '<span style="font-size:11.5px;color:var(--text-muted);font-weight:400;">Grammar Root</span></div>' +
    '</div>';

  // Card 2: Production Scale
  html += '<div class="bento-card">' +
    '<div class="bento-header"><span class="bento-title">Complexity</span><span class="bento-tag">' + totalProds + ' Prods</span></div>' +
    '<div class="bento-val"><span style="color:var(--accent-light);">' + g.orderedNTs.length + '</span> <span style="font-size:11.5px;color:var(--text-muted);font-weight:400;">NTs</span> &bull; <span style="color:var(--cyan);">' + g.terminals.size + '</span> <span style="font-size:11.5px;color:var(--text-muted);font-weight:400;">Terms</span></div>' +
    '</div>';

  // Card 3: Non-Terminals
  html += '<div class="bento-card bento-card-full">' +
    '<div class="bento-header"><span class="bento-title">Non-Terminals (V<sub>N</sub>) &mdash; ' + g.orderedNTs.length + '</span></div>' +
    '<div class="bento-chips">' +
    g.orderedNTs.map(function(nt) {
      return '<span class="bento-chip nt">' + esc(nt) + '</span>';
    }).join('') +
    '</div></div>';

  // Card 4: Terminals
  html += '<div class="bento-card bento-card-full">' +
    '<div class="bento-header"><span class="bento-title">Terminals (V<sub>T</sub>) &mdash; ' + g.terminals.size + '</span></div>' +
    '<div class="bento-chips">' +
    (g.terminals.size > 0 
      ? Array.from(g.terminals).map(function(t) { return '<span class="bento-chip term">' + esc(t) + '</span>'; }).join('')
      : '<span style="font-size:12px;color:var(--text-muted);">(none)</span>') +
    '</div></div>';

  // Card 5: Nullable Non-Terminals
  html += '<div class="bento-card bento-card-full">' +
    '<div class="bento-header"><span class="bento-title">Nullable Symbols (&rArr; &epsilon;) &mdash; ' + nullables.size + '</span></div>' +
    '<div class="bento-chips">' +
    (nullables.size > 0 
      ? Array.from(nullables).map(function(n) { return '<span class="bento-chip null">' + esc(n) + ' &rArr; \u03b5</span>'; }).join('')
      : '<span style="font-size:12px;color:var(--text-muted);">(none &mdash; all symbols derive non-empty strings)</span>') +
    '</div></div>';

  html += '</div>'; // End bento-grid

  // Structural Diagnostics Banners
  html += '<div class="diagnostics-summary mb-12">';
  if (immLR.hasIt || indLR.hasIt || prefixes.length > 0) {
    if (immLR.hasIt) {
      html += '<div class="banner banner-warn mb-8"><span>\u26a0</span><div><strong>Immediate Left Recursion Detected:</strong><br>' +
        immLR.details.map(function(d) { return '&bull; ' + esc(d); }).join('<br>') + '</div></div>';
    }
    if (indLR.hasIt) {
      html += '<div class="banner banner-warn mb-8"><span>\u26a0</span><div><strong>Indirect Left Recursion Detected:</strong><br>' +
        indLR.details.map(function(d) { return '&bull; ' + esc(d); }).join('<br>') + '</div></div>';
    }
    if (prefixes.length > 0) {
      html += '<div class="banner banner-info mb-8"><span>\u2139</span><div><strong>Common Prefixes (Left Factoring required):</strong><br>' +
        prefixes.map(function(d) { return '&bull; ' + esc(d); }).join('<br>') + '</div></div>';
    }
  } else {
    html += '<div class="banner banner-success"><span>\u2705</span> <strong>Grammar Well-Formed:</strong> No left recursion or common prefixes found. Ready for LL(1) construction.</div>';
  }
  html += '</div>';

  // Formatted clean rules list
  html += '<div class="grammar-display-title" style="font-size:11px;font-weight:600;text-transform:uppercase;color:var(--text-subtle);margin-bottom:6px;">Normalized CFG Rules:</div>';
  html += '<div class="grammar-display mb-12">';
  g.orderedNTs.forEach(function(nt) {
    var alts = g.rules.get(nt) || [];
    if (alts.length === 0) {
      html += '<div class="grammar-rule"><span class="nt">' + esc(nt) + '</span><span class="arrow"> \u2192 </span><span style="color:var(--text-muted);font-style:italic;">(no productions defined)</span></div>';
      return;
    }
    var altsHtml = alts.map(function(alt) {
      return alt.map(function(s) {
        if (s === EPS) return '<span class="epsilon">\u03b5</span>';
        if (g.nonTerminals.has(s)) return '<span class="nt">' + esc(s) + '</span>';
        return '<span class="terminal">' + esc(s) + '</span>';
      }).join(' ');
    }).join(' <span style="color:var(--text-subtle);font-weight:bold;margin:0 4px;">|</span> ');
    html += '<div class="grammar-rule"><span class="nt">' + esc(nt) + '</span><span class="arrow"> \u2192 </span>' + altsHtml + '</div>';
  });
  html += '</div>';

  document.getElementById('grammarInfo').innerHTML = html;

  // Update Bottom Status Bar
  var sbSum = document.getElementById('statusGrammarSummary');
  if (sbSum) sbSum.textContent = 'Grammar: ' + g.startSymbol + ' (' + g.orderedNTs.length + ' NTs, ' + g.terminals.size + ' Ts)';
  var sbDet = document.getElementById('statusDeterminism');
  if (sbDet) {
    if (isLL1Compatible) {
      sbDet.innerHTML = '<span style="color:var(--accent-light);">LL(1) Compatible &#10003;</span>';
    } else {
      sbDet.innerHTML = '<span style="color:var(--amber-light);">&#9888; Requires Preprocessing</span>';
    }
  }
}

// ============================================================
// SECTION 17: UI - RENDER PREPROCESSING
// ============================================================

function runPreprocessing(grammar) {
  ensureGrammarConsistency(grammar);
  var lrResult = eliminateAllLeftRecursion(grammar);
  ensureGrammarConsistency(lrResult.grammar);
  var lfResult = leftFactorGrammar(lrResult.grammar);
  ensureGrammarConsistency(lfResult.grammar);
  var anyTransform = lrResult.changed || lfResult.changed;
  return {
    original: grammar,
    transformed: anyTransform ? lfResult.grammar : null,
    lrResult: lrResult, lfResult: lfResult, anyTransform: anyTransform
  };
}

function renderPreprocessing(result) {
  var html = '';

  if (result.anyTransform) {
    html += '<div class="toggle-grammar-source mb-16">';
    html += '<label><input type="radio" name="gramSrc" value="transformed" checked onchange="switchGrammarSource(\'transformed\')"> Use transformed grammar</label>';
    html += '<label><input type="radio" name="gramSrc" value="original" onchange="switchGrammarSource(\'original\')"> Use original grammar</label>';
    html += '</div>';
  }

  // Left recursion
  html += '<h3 style="margin:16px 0 8px;color:var(--accent-light)">Step 1: Left Recursion Elimination</h3>';
  html += result.lrResult.changed
    ? '<div class="banner banner-info mb-8"><span>\ud83d\udd27</span> Left recursion was found and eliminated.</div>'
    : '<div class="banner banner-success mb-8"><span>\u2705</span> No left recursion found.</div>';
  html += '<div class="step-log mb-16">';
  result.lrResult.steps.forEach(function(s, i) {
    html += '<div class="step-entry"><span class="step-num">' + (i + 1) + '</span><span class="step-reason">' + esc(s) + '</span></div>';
  });
  html += '</div>';

  // Left factoring
  html += '<h3 style="margin:16px 0 8px;color:var(--cyan)">Step 2: Left Factoring</h3>';
  html += result.lfResult.changed
    ? '<div class="banner banner-info mb-8"><span>\ud83d\udd27</span> Common prefixes were factored.</div>'
    : '<div class="banner banner-success mb-8"><span>\u2705</span> No common prefixes found.</div>';
  html += '<div class="step-log mb-16">';
  result.lfResult.steps.forEach(function(s, i) {
    html += '<div class="step-entry"><span class="step-num">' + (i + 1) + '</span><span class="step-reason">' + esc(s) + '</span></div>';
  });
  html += '</div>';

  if (result.anyTransform) {
    html += '<h3 style="margin:16px 0 8px;color:var(--emerald)">Final Transformed Grammar</h3>';
    html += '<div class="grammar-display mb-16">';
    var tg = result.transformed;
    tg.orderedNTs.forEach(function(nt) {
      var alts = tg.rules.get(nt);
      if (!alts) return;
      html += '<div class="grammar-rule">' + fmtProd(nt, [alts.map(function(a) {
        return a.map(function(s) { return s === EPS ? '\u03b5' : s; }).join(' ');
      }).join(' | ')], tg.nonTerminals) + '</div>';
    });
    html += '</div>';
  }

  document.getElementById('preprocessContent').innerHTML = html;
}

function switchGrammarSource(src) {
  G_active = src === 'original' ? G : (G_transformed || G);

  NULLABLE_INFO = computeNullableWithReasons(G_active);

  var fr = computeFirstSets(G_active, NULLABLE_INFO.nullable);
  FIRST_SETS = fr.firstSets;
  FIRST_SIM_STEPS = fr.simSteps;
  FIRST_DEPS = fr.deps;
  firstWhyMap = fr.whyMap;
  firstSimIndex = FIRST_SIM_STEPS.length > 0 ? FIRST_SIM_STEPS.length - 1 : 0;
  if (firstSimTimer) { clearInterval(firstSimTimer); firstSimTimer = null; }

  var flr = computeFollowSets(G_active, FIRST_SETS, NULLABLE_INFO.nullable);
  FOLLOW_SETS = flr.followSets;
  FOLLOW_SIM_STEPS = flr.simSteps;
  FOLLOW_DEPS = flr.deps;
  followWhyMap = flr.whyMap;
  followSimIndex = FOLLOW_SIM_STEPS.length > 0 ? FOLLOW_SIM_STEPS.length - 1 : 0;
  if (followSimTimer) { clearInterval(followSimTimer); followSimTimer = null; }

  renderSummaryTable();
  renderFirstSets();
  renderFollowSets();

  inspectorNT = G_active.startSymbol || (G_active.orderedNTs[0] || null);
  renderDependencyGraph();

  var tr = buildParseTable(G_active, FIRST_SETS, FOLLOW_SETS);
  PARSE_TABLE = tr.table; tableWhyMap = tr.whyMap;
  renderParseTable(tr.terminals);

  var cr = detectConflicts(PARSE_TABLE, G_active, FIRST_SETS, FOLLOW_SETS);
  conflictInfo = cr.conflicts;
  renderConflicts(cr);

  renderSimulateUI();
  autoRunSimulation();
}

// ============================================================
// SECTION 17B: UI - SUMMARY TABLE & OVERVIEW
// ============================================================

function renderSummaryTable() {
  var container = document.getElementById('summaryContent');
  if (!container || !G_active) return;
  var nullables = NULLABLE_INFO ? NULLABLE_INFO.nullable : new Set();
  var isLL1 = conflictInfo ? conflictInfo.length === 0 : true;

  var html = '<div class="bento-grid mb-16">';
  html += '<div class="bento-card"><div class="bento-header"><span class="bento-title">Start Symbol</span><span class="bento-tag">Root</span></div><div class="bento-val"><span class="bento-chip nt">' + esc(G_active.startSymbol) + '</span></div></div>';
  html += '<div class="bento-card"><div class="bento-header"><span class="bento-title">Non-Terminals</span><span class="bento-tag">V<sub>N</sub></span></div><div class="bento-val" style="color:var(--accent-light)">' + G_active.orderedNTs.length + ' NTs</div></div>';
  html += '<div class="bento-card"><div class="bento-header"><span class="bento-title">Terminals</span><span class="bento-tag">V<sub>T</sub></span></div><div class="bento-val" style="color:var(--cyan)">' + G_active.terminals.size + ' Ts</div></div>';
  html += '<div class="bento-card"><div class="bento-header"><span class="bento-title">Nullable Symbols</span><span class="bento-tag">&rArr; &epsilon;</span></div><div class="bento-val" style="color:var(--emerald)">' + nullables.size + ' Nullable</div></div>';
  html += '<div class="bento-card"><div class="bento-header"><span class="bento-title">LL(1) Status</span><span class="bento-tag">Grammar</span></div><div class="bento-val">' + (isLL1 ? '<span style="color:var(--accent-light)">LL(1) Ready &#10003;</span>' : '<span style="color:var(--rose)">' + conflictInfo.length + ' Conflicts &#9888;</span>') + '</div></div>';
  html += '</div>';

  html += '<div class="table-wrap mb-16"><table class="data-table"><thead><tr><th style="width:14%">Non-Terminal</th><th style="width:16%">Nullable (&rArr; &epsilon;)</th><th style="width:32%">FIRST Set</th><th style="width:26%">FOLLOW Set</th><th style="width:12%">Actions</th></tr></thead><tbody>';

  G_active.orderedNTs.forEach(function(nt) {
    var isNull = nullables.has(nt);
    var nullReason = NULLABLE_INFO && NULLABLE_INFO.reasons ? (NULLABLE_INFO.reasons.get(nt) || '') : '';
    var nullBadge = isNull
      ? '<span class="tooltip-cell"><span class="bento-chip null" style="font-size:11px;padding:2px 6px;">YES (&rArr; \u03b5)</span>' + (nullReason ? '<span class="tooltip-text">' + esc(nullReason) + '</span>' : '') + '</span>'
      : '<span style="font-size:11.5px;color:var(--text-subtle);font-weight:500;">NO</span>';

    var fs = FIRST_SETS ? FIRST_SETS.get(nt) : new Set();
    var fsArr = Array.from(fs || []);
    fsArr.sort(function(a, b) { if (a === EPS) return 1; if (b === EPS) return -1; return a.localeCompare(b); });
    var fsItems = fsArr.map(function(t) {
      var why = firstWhyMap ? (firstWhyMap.get(nt + ':' + t) || '') : '';
      return '<span class="tooltip-cell"><span class="' + (t === EPS ? 'epsilon' : 'terminal') + '">' +
        (t === EPS ? '\u03b5' : esc(t)) + '</span>' +
        (why ? '<span class="tooltip-text">' + esc(why) + '</span>' : '') + '</span>';
    });

    var fls = FOLLOW_SETS ? FOLLOW_SETS.get(nt) : new Set();
    var flsArr = Array.from(fls || []);
    flsArr.sort(function(a, b) { if (a === '$') return 1; if (b === '$') return -1; return a.localeCompare(b); });
    var flsItems = flsArr.map(function(t) {
      var why = followWhyMap ? (followWhyMap.get(nt + ':' + t) || '') : '';
      return '<span class="tooltip-cell"><span class="terminal">' + esc(t) + '</span>' +
        (why ? '<span class="tooltip-text">' + esc(why) + '</span>' : '') + '</span>';
    });

    html += '<tr>' +
      '<td class="fw-700 text-accent font-mono"><span class="bento-chip nt">' + esc(nt) + '</span></td>' +
      '<td>' + nullBadge + '</td>' +
      '<td class="font-mono">{ ' + (fsItems.length > 0 ? fsItems.join(', ') : '<span style="color:var(--text-subtle)">&empty;</span>') + ' }</td>' +
      '<td class="font-mono">{ ' + (flsItems.length > 0 ? flsItems.join(', ') : '<span style="color:var(--text-subtle)">&empty;</span>') + ' }</td>' +
      '<td><button class="btn btn-secondary btn-sm" onclick="selectInspectorNT(\'' + esc(nt) + '\');switchTab(\'graph\')" title="Inspect this symbol in Dependency Graph">&#128269; Inspect</button></td>' +
      '</tr>';
  });

  html += '</tbody></table></div>';

  // Educational Sequence FIRST Calculator
  html += '<div class="seq-eval-card">';
  html += '<div class="card-headline mb-8"><span class="headline-icon">&#128295;</span> <span>Arbitrary Sequence FIRST Evaluator &mdash; FIRST(&alpha;)</span></div>';
  html += '<p style="font-size:12.5px;color:var(--text-muted);margin-bottom:8px;">Enter any sequence of grammar symbols (e.g. <code>T E\'</code> or <code>B D h</code> or <code>+ T</code>) to inspect its step-by-step derivation:</p>';
  html += '<div class="seq-eval-input-bar">';
  html += '<input type="text" id="seqFirstInput" class="seq-eval-input" placeholder="e.g. B D h" onkeydown="if(event.key===\'Enter\')evalSequenceFirst()">';
  html += '<button class="btn btn-primary btn-sm" onclick="evalSequenceFirst()">&#9654; Evaluate FIRST(&alpha;)</button>';
  html += '</div>';
  html += '<div id="seqFirstResult" class="seq-steps-box" style="display:none;"></div>';
  html += '</div>';

  container.innerHTML = html;
}

// ============================================================
// SECTION 18: UI - FIRST SETS ENGINE & STEP-BY-STEP SIMULATOR
// ============================================================

function renderFirstSets() {
  var container = document.getElementById('firstContent');
  if (!container || !G_active) return;

  var totalSteps = FIRST_SIM_STEPS.length;
  if (firstSimIndex >= totalSteps) firstSimIndex = Math.max(0, totalSteps - 1);

  var html = '';

  // Simulator Player Control Bar
  html += '<div class="sim-controls-bar">';
  html += '<div class="sim-btn-group">';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFirstFirst()" title="Jump to First Step">|&#9664;&#9664;</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFirstPrev()" title="Previous Step">&#9664; Prev</button>';
  html += '<button id="btnFirstPlay" class="btn btn-primary btn-sm" onclick="simFirstTogglePlay()" title="Auto Play Simulation">&#9654; Play</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFirstNext()" title="Next Step">Next &#9654;</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFirstLast()" title="Jump to Final Step">&#9654;&#9654;|</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFirstReset()" title="Reset to Step 0">&#8635; Reset</button>';
  html += '</div>';

  html += '<div class="sim-scrubber-group">';
  html += '<input type="range" id="firstSimSlider" class="sim-slider" min="0" max="' + Math.max(0, totalSteps - 1) + '" value="' + firstSimIndex + '" oninput="simFirstGoTo(parseInt(this.value))">';
  html += '<span id="firstSimBadge" class="sim-step-badge">Step ' + (firstSimIndex + 1) + ' of ' + totalSteps + '</span>';
  html += '</div>';
  html += '</div>';

  // Active Step Card
  html += '<div id="firstStepCard" class="sim-step-card">';
  html += '<div class="sim-step-meta">';
  html += '<div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap;">';
  html += '<span id="firstStepIter" class="sim-tag sim-tag-iter">Iteration 0</span>';
  html += '<span id="firstStepRule" class="sim-tag sim-tag-rule">Initialization</span>';
  html += '<span id="firstStepAdded" class="sim-tag sim-tag-added">&empty;</span>';
  html += '</div>';
  html += '<span id="firstStepCat" class="bento-tag">Fixed Point</span>';
  html += '</div>';

  html += '<div class="sim-explanation-box">';
  html += '<div class="sim-reason-title">Step Reasoning &amp; Mathematical Rule Justification:</div>';
  html += '<div id="firstStepReason" style="color:var(--text-main);font-size:13px;line-height:1.6;">-</div>';
  html += '</div>';
  html += '</div>';

  // Live Snapshot State Table
  html += '<h4 style="font-size:12px;text-transform:uppercase;letter-spacing:0.05em;color:var(--text-subtle);margin-bottom:8px;">Live Non-Terminal FIRST Sets State (At Active Step):</h4>';
  html += '<div class="table-wrap mb-16">';
  html += '<table class="data-table sim-snapshot-table" id="firstSnapshotTable">';
  html += '<thead><tr><th style="width:18%">Non-Terminal</th><th style="width:16%">Nullable</th><th style="width:50%">Current FIRST Set Snapshot</th><th style="width:16%">Step Activity</th></tr></thead>';
  html += '<tbody id="firstSnapshotBody"></tbody>';
  html += '</table>';
  html += '</div>';

  // Comprehensive Iteration History Log
  html += '<details class="step-log-details mb-16" open>';
  html += '<summary style="cursor:pointer;font-weight:600;font-size:13px;color:var(--accent-light);padding:8px 0;user-select:none;">&#128220; Complete FIRST Iteration History Log (' + totalSteps + ' Steps)</summary>';
  html += '<div class="step-log" style="margin-top:10px;">';
  FIRST_SIM_STEPS.forEach(function(s, idx) {
    var isConv = s.type === 'converged';
    var isInit = s.type === 'init';
    var icon = isConv ? '&#10003;' : (isInit ? '0' : '+');
    var badgeCls = isConv ? 'badge-ok' : (isInit ? 'badge' : 'badge-warn');

    html += '<div class="step-entry" style="cursor:pointer;" onclick="simFirstGoTo(' + idx + ')">';
    html += '<span class="step-num ' + badgeCls + '">' + icon + '</span>';
    html += '<div style="flex:1;">';
    html += '<div><strong>Step ' + (idx + 1) + '</strong> (Iter ' + s.iteration + '): <span class="font-mono text-accent">' + esc(s.ruleStr) + '</span></div>';
    html += '<div class="step-reason" style="margin-top:2px;">' + esc(s.reason) + '</div>';
    html += '</div>';
    html += '</div>';
  });
  html += '</div>';
  html += '</details>';

  container.innerHTML = html;
  updateFirstSimUI();
}

function updateFirstSimUI() {
  if (!FIRST_SIM_STEPS || FIRST_SIM_STEPS.length === 0) return;
  var step = FIRST_SIM_STEPS[firstSimIndex];
  if (!step) return;

  var slider = document.getElementById('firstSimSlider');
  if (slider) slider.value = String(firstSimIndex);

  var badge = document.getElementById('firstSimBadge');
  if (badge) badge.textContent = 'Step ' + (firstSimIndex + 1) + ' of ' + FIRST_SIM_STEPS.length + ' (Iter ' + step.iteration + ')';

  var iterEl = document.getElementById('firstStepIter');
  if (iterEl) iterEl.textContent = 'Iteration ' + step.iteration;

  var ruleEl = document.getElementById('firstStepRule');
  if (ruleEl) ruleEl.textContent = step.ruleStr;

  var addedEl = document.getElementById('firstStepAdded');
  if (addedEl) {
    if (step.added && step.added.length > 0) {
      addedEl.innerHTML = '+ { ' + step.added.map(function(s) { return s === EPS ? '\u03b5' : esc(s); }).join(', ') + ' }';
      addedEl.style.display = 'inline-flex';
    } else {
      addedEl.style.display = 'none';
    }
  }

  var catEl = document.getElementById('firstStepCat');
  if (catEl) catEl.textContent = step.category;

  var reasonEl = document.getElementById('firstStepReason');
  if (reasonEl) reasonEl.innerHTML = esc(step.reason);

  var card = document.getElementById('firstStepCard');
  if (card) {
    if (step.type === 'converged') card.classList.add('converged-card');
    else card.classList.remove('converged-card');
  }

  // Update Live Snapshot Table
  var tbody = document.getElementById('firstSnapshotBody');
  if (tbody && G_active) {
    var nullables = NULLABLE_INFO ? NULLABLE_INFO.nullable : new Set();
    var bHtml = '';

    G_active.orderedNTs.forEach(function(nt) {
      var isTarget = (step.nt === nt && step.type === 'rule_eval');
      var trCls = isTarget ? 'highlighted' : '';
      var currentSet = step.snapshot ? step.snapshot.get(nt) : (FIRST_SETS ? FIRST_SETS.get(nt) : new Set());
      var setArr = Array.from(currentSet || []);
      setArr.sort(function(a, b) { if (a === EPS) return 1; if (b === EPS) return -1; return a.localeCompare(b); });

      var items = setArr.map(function(sym) {
        var isNew = isTarget && step.added && step.added.indexOf(sym) >= 0;
        var label = sym === EPS ? '\u03b5' : esc(sym);
        return isNew ? '<span class="symbol-new">' + label + '</span>' : '<span class="' + (sym === EPS ? 'epsilon' : 'terminal') + '">' + label + '</span>';
      });

      var isNull = nullables.has(nt);
      var actBadge = isTarget
        ? '<span class="bento-chip term" style="font-size:11px;padding:2px 6px;">Updated + ' + (step.added ? step.added.length : 0) + '</span>'
        : '<span style="color:var(--text-subtle);font-size:12px;">Unchanged</span>';

      bHtml += '<tr class="' + trCls + '">' +
        '<td class="fw-700 text-accent font-mono">' + esc(nt) + '</td>' +
        '<td>' + (isNull ? '<span class="bento-chip null" style="font-size:10.5px;padding:1px 5px;">YES (&rArr; \u03b5)</span>' : '<span style="color:var(--text-subtle);font-size:11px;">NO</span>') + '</td>' +
        '<td class="font-mono">{ ' + (items.length > 0 ? items.join(', ') : '<span style="color:var(--text-subtle)">&empty;</span>') + ' }</td>' +
        '<td>' + actBadge + '</td>' +
        '</tr>';
    });

    tbody.innerHTML = bHtml;
  }
}

function simFirstGoTo(stepIdx) {
  firstSimIndex = Math.max(0, Math.min(FIRST_SIM_STEPS.length - 1, stepIdx));
  updateFirstSimUI();
}

function simFirstNext() {
  if (firstSimIndex < FIRST_SIM_STEPS.length - 1) {
    firstSimIndex++;
    updateFirstSimUI();
  } else {
    simFirstPause();
  }
}

function simFirstPrev() {
  if (firstSimIndex > 0) {
    firstSimIndex--;
    updateFirstSimUI();
  }
}

function simFirstFirst() {
  firstSimIndex = 0;
  updateFirstSimUI();
}

function simFirstLast() {
  firstSimIndex = Math.max(0, FIRST_SIM_STEPS.length - 1);
  updateFirstSimUI();
}

function simFirstReset() {
  simFirstPause();
  firstSimIndex = 0;
  updateFirstSimUI();
}

function simFirstTogglePlay() {
  if (firstSimTimer) {
    simFirstPause();
  } else {
    simFirstPlay();
  }
}

function simFirstPlay() {
  if (firstSimTimer) return;
  if (firstSimIndex >= FIRST_SIM_STEPS.length - 1) {
    firstSimIndex = 0;
    updateFirstSimUI();
  }
  var btn = document.getElementById('btnFirstPlay');
  if (btn) btn.innerHTML = '&#9208; Pause';
  firstSimTimer = setInterval(function() {
    if (firstSimIndex < FIRST_SIM_STEPS.length - 1) {
      firstSimIndex++;
      updateFirstSimUI();
    } else {
      simFirstPause();
    }
  }, firstSimSpeed);
}

function simFirstPause() {
  if (firstSimTimer) {
    clearInterval(firstSimTimer);
    firstSimTimer = null;
  }
  var btn = document.getElementById('btnFirstPlay');
  if (btn) btn.innerHTML = '&#9654; Play';
}

function simFirstSetSpeed(speed) {
  firstSimSpeed = parseInt(speed) || 1000;
  if (firstSimTimer) {
    simFirstPause();
    simFirstPlay();
  }
}

function evalSequenceFirst() {
  var inputEl = document.getElementById('seqFirstInput');
  var resBox = document.getElementById('seqFirstResult');
  if (!inputEl || !resBox || !G_active || !FIRST_SETS) return;

  var text = inputEl.value.trim();
  if (!text) {
    resBox.style.display = 'none';
    return;
  }

  var tokens = text.split(/\s+/).filter(Boolean);
  var nullables = NULLABLE_INFO ? NULLABLE_INFO.nullable : new Set();
  var resultSet = new Set();
  var stepsLog = [];

  var allDeriveEps = true;
  for (var i = 0; i < tokens.length; i++) {
    var sym = tokens[i];
    if (sym === EPS || sym === 'eps' || sym === '#') continue;

    if (FIRST_SETS.has(sym)) {
      var fs = FIRST_SETS.get(sym);
      var fsNoEps = [];
      fs.forEach(function(t) {
        if (t !== EPS) { resultSet.add(t); fsNoEps.push(t); }
      });
      stepsLog.push('Symbol #' + (i + 1) + ' is non-terminal <strong class="text-accent">' + esc(sym) + '</strong>: FIRST(' + esc(sym) + ') = { ' + Array.from(fs).join(', ') + ' }. Added { ' + fsNoEps.join(', ') + ' } to result.');

      var isSymNull = fs.has(EPS) || nullables.has(sym);
      if (!isSymNull) {
        stepsLog.push('<strong class="text-accent">' + esc(sym) + '</strong> does NOT derive \u03b5. Sequence scanning stops here.');
        allDeriveEps = false;
        break;
      } else {
        stepsLog.push('<strong class="text-accent">' + esc(sym) + '</strong> is nullable (&rArr; \u03b5). Continuing to next symbol in sequence.');
      }
    } else {
      // Terminal
      resultSet.add(sym);
      stepsLog.push('Symbol #' + (i + 1) + ' is terminal <strong class="text-cyan">"' + esc(sym) + '"</strong>. Added "' + esc(sym) + '" to result. Scanning stops.');
      allDeriveEps = false;
      break;
    }
  }

  if (allDeriveEps) {
    resultSet.add(EPS);
    stepsLog.push('All symbols in sequence can derive \u03b5 (or sequence was empty). Added \u03b5 to FIRST(&alpha;).');
  }

  var resArr = Array.from(resultSet);
  resArr.sort(function(a, b) { if (a === EPS) return 1; if (b === EPS) return -1; return a.localeCompare(b); });

  var outHtml = '<div style="margin-bottom:8px;font-weight:700;color:var(--accent-light);font-size:14px;">FIRST( ' + esc(tokens.join(' ')) + ' ) = { ' + resArr.map(function(s) { return s === EPS ? '\u03b5' : esc(s); }).join(', ') + ' }</div>';
  outHtml += '<div style="font-size:12px;color:var(--text-muted);margin-bottom:6px;">Derivation Trace:</div>';
  outHtml += '<ul style="margin:0 0 0 18px;font-size:12.5px;line-height:1.6;">';
  stepsLog.forEach(function(s) { outHtml += '<li>' + s + '</li>'; });
  outHtml += '</ul>';

  resBox.innerHTML = outHtml;
  resBox.style.display = 'block';
}

// ============================================================
// SECTION 19: UI - FOLLOW SETS ENGINE & STEP-BY-STEP SIMULATOR
// ============================================================

function renderFollowSets() {
  var container = document.getElementById('followContent');
  if (!container || !G_active) return;

  var totalSteps = FOLLOW_SIM_STEPS.length;
  if (followSimIndex >= totalSteps) followSimIndex = Math.max(0, totalSteps - 1);

  var html = '';

  // Simulator Player Control Bar
  html += '<div class="sim-controls-bar">';
  html += '<div class="sim-btn-group">';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFollowFirst()" title="Jump to First Step">|&#9664;&#9664;</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFollowPrev()" title="Previous Step">&#9664; Prev</button>';
  html += '<button id="btnFollowPlay" class="btn btn-primary btn-sm" onclick="simFollowTogglePlay()" title="Auto Play Simulation">&#9654; Play</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFollowNext()" title="Next Step">Next &#9654;</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFollowLast()" title="Jump to Final Step">&#9654;&#9654;|</button>';
  html += '<button class="btn btn-secondary btn-sm" onclick="simFollowReset()" title="Reset to Step 0">&#8635; Reset</button>';
  html += '</div>';

  html += '<div class="sim-scrubber-group">';
  html += '<input type="range" id="followSimSlider" class="sim-slider" min="0" max="' + Math.max(0, totalSteps - 1) + '" value="' + followSimIndex + '" oninput="simFollowGoTo(parseInt(this.value))">';
  html += '<span id="followSimBadge" class="sim-step-badge">Step ' + (followSimIndex + 1) + ' of ' + totalSteps + '</span>';
  html += '</div>';
  html += '</div>';

  // Active Step Card (Warm Amber Border)
  html += '<div id="followStepCard" class="sim-step-card follow-card">';
  html += '<div class="sim-step-meta">';
  html += '<div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap;">';
  html += '<span id="followStepIter" class="sim-tag sim-tag-iter" style="color:var(--amber);border-color:rgba(245,158,11,0.3)">Iteration 0</span>';
  html += '<span id="followStepRule" class="sim-tag sim-tag-rule">Initialization</span>';
  html += '<span id="followStepAdded" class="sim-tag sim-tag-added-amber">&empty;</span>';
  html += '</div>';
  html += '<span id="followStepCat" class="bento-tag">Start Symbol Rule</span>';
  html += '</div>';

  html += '<div class="sim-explanation-box">';
  html += '<div class="sim-reason-title">Step Reasoning &amp; Mathematical Rule Justification:</div>';
  html += '<div id="followStepReason" style="color:var(--text-main);font-size:13px;line-height:1.6;">-</div>';
  html += '</div>';
  html += '</div>';

  // Live Snapshot State Table
  html += '<h4 style="font-size:12px;text-transform:uppercase;letter-spacing:0.05em;color:var(--text-subtle);margin-bottom:8px;">Live Non-Terminal FOLLOW Sets State (At Active Step):</h4>';
  html += '<div class="table-wrap mb-16">';
  html += '<table class="data-table sim-snapshot-table" id="followSnapshotTable">';
  html += '<thead><tr><th style="width:18%">Non-Terminal</th><th style="width:16%">Nullable</th><th style="width:50%">Current FOLLOW Set Snapshot</th><th style="width:16%">Step Activity</th></tr></thead>';
  html += '<tbody id="followSnapshotBody"></tbody>';
  html += '</table>';
  html += '</div>';

  // Comprehensive Iteration History Log
  html += '<details class="step-log-details mb-16" open>';
  html += '<summary style="cursor:pointer;font-weight:600;font-size:13px;color:var(--amber);padding:8px 0;user-select:none;">&#128220; Complete FOLLOW Iteration History Log (' + totalSteps + ' Steps)</summary>';
  html += '<div class="step-log" style="margin-top:10px;">';
  FOLLOW_SIM_STEPS.forEach(function(s, idx) {
    var isConv = s.type === 'converged';
    var isInit = s.iteration === 0;
    var icon = isConv ? '&#10003;' : (isInit ? '$' : '+');
    var badgeCls = isConv ? 'badge-ok' : (isInit ? 'badge' : 'badge-warn');

    html += '<div class="step-entry" style="cursor:pointer;" onclick="simFollowGoTo(' + idx + ')">';
    html += '<span class="step-num ' + badgeCls + '">' + icon + '</span>';
    html += '<div style="flex:1;">';
    html += '<div><strong>Step ' + (idx + 1) + '</strong> (Iter ' + s.iteration + '): <span class="font-mono text-accent">' + esc(s.ruleStr) + '</span></div>';
    html += '<div class="step-reason" style="margin-top:2px;">' + esc(s.reason) + '</div>';
    html += '</div>';
    html += '</div>';
  });
  html += '</div>';
  html += '</details>';

  container.innerHTML = html;
  updateFollowSimUI();
}

function updateFollowSimUI() {
  if (!FOLLOW_SIM_STEPS || FOLLOW_SIM_STEPS.length === 0) return;
  var step = FOLLOW_SIM_STEPS[followSimIndex];
  if (!step) return;

  var slider = document.getElementById('followSimSlider');
  if (slider) slider.value = String(followSimIndex);

  var badge = document.getElementById('followSimBadge');
  if (badge) badge.textContent = 'Step ' + (followSimIndex + 1) + ' of ' + FOLLOW_SIM_STEPS.length + ' (Iter ' + step.iteration + ')';

  var iterEl = document.getElementById('followStepIter');
  if (iterEl) iterEl.textContent = 'Iteration ' + step.iteration;

  var ruleEl = document.getElementById('followStepRule');
  if (ruleEl) ruleEl.textContent = step.ruleStr;

  var addedEl = document.getElementById('followStepAdded');
  if (addedEl) {
    if (step.added && step.added.length > 0) {
      addedEl.innerHTML = '+ { ' + step.added.map(function(s) { return esc(s); }).join(', ') + ' }';
      addedEl.style.display = 'inline-flex';
    } else {
      addedEl.style.display = 'none';
    }
  }

  var catEl = document.getElementById('followStepCat');
  if (catEl) catEl.textContent = step.category;

  var reasonEl = document.getElementById('followStepReason');
  if (reasonEl) reasonEl.innerHTML = esc(step.reason);

  var card = document.getElementById('followStepCard');
  if (card) {
    if (step.type === 'converged') card.classList.add('converged-card');
    else card.classList.remove('converged-card');
  }

  // Update Live Snapshot Table
  var tbody = document.getElementById('followSnapshotBody');
  if (tbody && G_active) {
    var nullables = NULLABLE_INFO ? NULLABLE_INFO.nullable : new Set();
    var bHtml = '';

    G_active.orderedNTs.forEach(function(nt) {
      var isTarget = (step.nt === nt && step.type === 'rule_eval');
      var trCls = isTarget ? 'highlighted-amber' : '';
      var currentSet = step.snapshot ? step.snapshot.get(nt) : (FOLLOW_SETS ? FOLLOW_SETS.get(nt) : new Set());
      var setArr = Array.from(currentSet || []);
      setArr.sort(function(a, b) { if (a === '$') return 1; if (b === '$') return -1; return a.localeCompare(b); });

      var items = setArr.map(function(sym) {
        var isNew = isTarget && step.added && step.added.indexOf(sym) >= 0;
        var label = esc(sym);
        return isNew ? '<span class="symbol-new-amber">' + label + '</span>' : '<span class="terminal">' + label + '</span>';
      });

      var isNull = nullables.has(nt);
      var actBadge = isTarget
        ? '<span class="bento-chip null" style="font-size:11px;padding:2px 6px;">Updated + ' + (step.added ? step.added.length : 0) + '</span>'
        : '<span style="color:var(--text-subtle);font-size:12px;">Unchanged</span>';

      bHtml += '<tr class="' + trCls + '">' +
        '<td class="fw-700 text-accent font-mono">' + esc(nt) + '</td>' +
        '<td>' + (isNull ? '<span class="bento-chip null" style="font-size:10.5px;padding:1px 5px;">YES (&rArr; \u03b5)</span>' : '<span style="color:var(--text-subtle);font-size:11px;">NO</span>') + '</td>' +
        '<td class="font-mono">{ ' + (items.length > 0 ? items.join(', ') : '<span style="color:var(--text-subtle)">&empty;</span>') + ' }</td>' +
        '<td>' + actBadge + '</td>' +
        '</tr>';
    });

    tbody.innerHTML = bHtml;
  }
}

function simFollowGoTo(stepIdx) {
  followSimIndex = Math.max(0, Math.min(FOLLOW_SIM_STEPS.length - 1, stepIdx));
  updateFollowSimUI();
}

function simFollowNext() {
  if (followSimIndex < FOLLOW_SIM_STEPS.length - 1) {
    followSimIndex++;
    updateFollowSimUI();
  } else {
    simFollowPause();
  }
}

function simFollowPrev() {
  if (followSimIndex > 0) {
    followSimIndex--;
    updateFollowSimUI();
  }
}

function simFollowFirst() {
  followSimIndex = 0;
  updateFollowSimUI();
}

function simFollowLast() {
  followSimIndex = Math.max(0, FOLLOW_SIM_STEPS.length - 1);
  updateFollowSimUI();
}

function simFollowReset() {
  simFollowPause();
  followSimIndex = 0;
  updateFollowSimUI();
}

function simFollowTogglePlay() {
  if (followSimTimer) {
    simFollowPause();
  } else {
    simFollowPlay();
  }
}

function simFollowPlay() {
  if (followSimTimer) return;
  if (followSimIndex >= FOLLOW_SIM_STEPS.length - 1) {
    followSimIndex = 0;
    updateFollowSimUI();
  }
  var btn = document.getElementById('btnFollowPlay');
  if (btn) btn.innerHTML = '&#9208; Pause';
  followSimTimer = setInterval(function() {
    if (followSimIndex < FOLLOW_SIM_STEPS.length - 1) {
      followSimIndex++;
      updateFollowSimUI();
    } else {
      simFollowPause();
    }
  }, followSimSpeed);
}

function simFollowPause() {
  if (followSimTimer) {
    clearInterval(followSimTimer);
    followSimTimer = null;
  }
  var btn = document.getElementById('btnFollowPlay');
  if (btn) btn.innerHTML = '&#9654; Play';
}

function simFollowSetSpeed(speed) {
  followSimSpeed = parseInt(speed) || 1000;
  if (followSimTimer) {
    simFollowPause();
    simFollowPlay();
  }
}

// ============================================================
// SECTION 19B: UI - DEPENDENCY GRAPH & INTERACTIVE INSPECTOR
// ============================================================

function renderDependencyGraph() {
  var container = document.getElementById('graphContent');
  if (!container || !G_active) return;

  var html = '';

  // Toolbar with Edge Filters
  html += '<div class="graph-toolbar">';
  html += '<div class="graph-legend-group">';
  html += '<div class="graph-legend-item"><span class="legend-line legend-line-first"></span> Solid Green: FIRST Dependency (A &rarr; B)</div>';
  html += '<div class="graph-legend-item"><span class="legend-line legend-line-follow"></span> Dashed Amber: FOLLOW Dependency (B &rarr; A)</div>';
  html += '</div>';

  html += '<div style="display:flex;gap:6px;">';
  html += '<button class="btn btn-secondary btn-sm' + (graphEdgeFilter === 'all' ? ' active' : '') + '" onclick="setGraphEdgeFilter(\'all\')">Show All</button>';
  html += '<button class="btn btn-secondary btn-sm' + (graphEdgeFilter === 'first' ? ' active' : '') + '" onclick="setGraphEdgeFilter(\'first\')">FIRST Only</button>';
  html += '<button class="btn btn-secondary btn-sm' + (graphEdgeFilter === 'follow' ? ' active' : '') + '" onclick="setGraphEdgeFilter(\'follow\')">FOLLOW Only</button>';
  html += '</div>';
  html += '</div>';

  // SVG Canvas Box
  html += '<div class="graph-canvas-box" id="depGraphContainer">';
  html += generateDependencyGraphSVG(G_active.orderedNTs, FIRST_DEPS || new Map(), FOLLOW_DEPS || new Map(), graphEdgeFilter, inspectorNT);
  html += '</div>';

  // Non-Terminal Inspector Box
  html += '<div id="inspectorContainer">';
  html += renderInspectorHTML(inspectorNT || G_active.startSymbol);
  html += '</div>';

  container.innerHTML = html;
}

function setGraphEdgeFilter(filter) {
  graphEdgeFilter = filter;
  renderDependencyGraph();
}

function selectInspectorNT(nt) {
  inspectorNT = nt;
  var container = document.getElementById('depGraphContainer');
  if (container && G_active) {
    container.innerHTML = generateDependencyGraphSVG(G_active.orderedNTs, FIRST_DEPS || new Map(), FOLLOW_DEPS || new Map(), graphEdgeFilter, inspectorNT);
  }
  var insp = document.getElementById('inspectorContainer');
  if (insp) {
    insp.innerHTML = renderInspectorHTML(inspectorNT);
  }
}

function renderInspectorHTML(nt) {
  if (!nt || !G_active) return '<p class="text-muted">Select a non-terminal above to inspect.</p>';

  var nullables = NULLABLE_INFO ? NULLABLE_INFO.nullable : new Set();
  var isNull = nullables.has(nt);
  var nullReason = NULLABLE_INFO && NULLABLE_INFO.reasons ? (NULLABLE_INFO.reasons.get(nt) || '') : '';
  var isStart = (nt === G_active.startSymbol);

  var alts = G_active.rules.get(nt) || [];
  var prodsHtml = alts.map(function(alt) {
    return '<li>' + fmtProd(nt, alt, G_active.nonTerminals) + '</li>';
  }).join('');

  var fs = FIRST_SETS ? FIRST_SETS.get(nt) : new Set();
  var fsArr = Array.from(fs || []);
  fsArr.sort(function(a, b) { if (a === EPS) return 1; if (b === EPS) return -1; return a.localeCompare(b); });
  var fsHtml = fsArr.map(function(t) {
    var why = firstWhyMap ? (firstWhyMap.get(nt + ':' + t) || 'Direct derivation') : '';
    return '<li><strong class="' + (t === EPS ? 'epsilon' : 'terminal') + '">' + (t === EPS ? '\u03b5' : esc(t)) + '</strong> &mdash; <span style="color:var(--text-muted)">' + esc(why) + '</span></li>';
  }).join('');

  var fls = FOLLOW_SETS ? FOLLOW_SETS.get(nt) : new Set();
  var flsArr = Array.from(fls || []);
  flsArr.sort(function(a, b) { if (a === '$') return 1; if (b === '$') return -1; return a.localeCompare(b); });
  var flsHtml = flsArr.map(function(t) {
    var why = followWhyMap ? (followWhyMap.get(nt + ':' + t) || 'Grammar constraint') : '';
    return '<li><strong class="terminal">' + esc(t) + '</strong> &mdash; <span style="color:var(--text-muted)">' + esc(why) + '</span></li>';
  }).join('');

  var fDeps = FIRST_DEPS ? Array.from(FIRST_DEPS.get(nt) || []) : [];
  var flDeps = FOLLOW_DEPS ? Array.from(FOLLOW_DEPS.get(nt) || []) : [];

  var html = '<div class="inspector-card">';
  html += '<div class="inspector-header">';
  html += '<div class="inspector-title">';
  html += '<span>&#128269; Symbol Inspector:</span> <span class="bento-chip nt" style="font-size:14px;padding:3px 10px;">' + esc(nt) + '</span>';
  if (isStart) html += '<span class="bento-tag" style="background:#18181b;color:var(--accent-light);border-color:var(--accent-dark);">Grammar Start Symbol</span>';
  html += '</div>';

  html += '<div>';
  html += isNull
    ? '<span class="bento-chip null">Nullable (&rArr; \u03b5)' + (nullReason ? ': ' + esc(nullReason) : '') + '</span>'
    : '<span style="color:var(--text-subtle);font-size:12px;">Non-Nullable (Always produces non-empty string)</span>';
  html += '</div>';
  html += '</div>';

  html += '<div class="inspector-grid">';

  // Productions
  html += '<div class="inspector-box">';
  html += '<div class="inspector-box-title">&#128221; Grammar Productions (' + alts.length + ')</div>';
  html += '<ul class="reason-list">' + (prodsHtml || '<li>None</li>') + '</ul>';
  html += '</div>';

  // FIRST Set
  html += '<div class="inspector-box">';
  html += '<div class="inspector-box-title" style="color:var(--accent-light);">&#9312; FIRST(' + esc(nt) + ') &mdash; ' + fsArr.length + ' symbols</div>';
  html += '<ul class="reason-list">' + (fsHtml || '<li>&empty;</li>') + '</ul>';
  html += '</div>';

  // FOLLOW Set
  html += '<div class="inspector-box">';
  html += '<div class="inspector-box-title" style="color:var(--amber);">&#9313; FOLLOW(' + esc(nt) + ') &mdash; ' + flsArr.length + ' symbols</div>';
  html += '<ul class="reason-list">' + (flsHtml || '<li>&empty;</li>') + '</ul>';
  html += '</div>';

  // Dependencies
  html += '<div class="inspector-box">';
  html += '<div class="inspector-box-title">&#128392; Propagation Dependencies</div>';
  html += '<div style="font-size:12px;color:var(--text-muted);line-height:1.6;">';
  html += '<div style="margin-bottom:6px;"><strong style="color:var(--accent-light);">FIRST Dependencies:</strong> ' + (fDeps.length > 0 ? fDeps.map(function(d){ return '<span class="bento-chip nt" style="font-size:10.5px;padding:1px 5px;">' + esc(d) + '</span>'; }).join(' ') : '<span style="color:var(--text-subtle)">(none)</span>') + '</div>';
  html += '<div><strong style="color:var(--amber);">FOLLOW From:</strong> ' + (flDeps.length > 0 ? flDeps.map(function(d){ return '<span class="bento-chip nt" style="font-size:10.5px;padding:1px 5px;">' + esc(d) + '</span>'; }).join(' ') : '<span style="color:var(--text-subtle)">(none)</span>') + '</div>';
  html += '</div>';
  html += '</div>';

  html += '</div>'; // End inspector-grid
  html += '</div>'; // End inspector-card

  return html;
}

// SVG Graph Generator
function generateDependencyGraphSVG(orderedNTs, firstDeps, followDeps, activeFilter, selectedNT) {
  var w = 720;
  var h = 380;
  var cx = w / 2;
  var cy = h / 2;
  var rx = 240;
  var ry = 130;
  var n = orderedNTs.length;

  var nodeCoords = new Map();
  for (var i = 0; i < n; i++) {
    var nt = orderedNTs[i];
    var angle = (2 * Math.PI * i) / Math.max(n, 1) - Math.PI / 2;
    var x = Math.round(cx + rx * Math.cos(angle));
    var y = Math.round(cy + ry * Math.sin(angle));
    nodeCoords.set(nt, { x: x, y: y });
  }

  var svg = '<svg id="depGraphSvg" class="dep-graph-svg" width="' + w + '" height="' + h + '" viewBox="0 0 ' + w + ' ' + h + '" xmlns="http://www.w3.org/2000/svg">';
  svg += '<defs>';
  svg += '<marker id="arrow-first" viewBox="0 0 10 10" refX="28" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#10b981"/></marker>';
  svg += '<marker id="arrow-follow" viewBox="0 0 10 10" refX="28" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#f59e0b"/></marker>';
  svg += '</defs>';

  // Edges
  if (activeFilter === 'all' || activeFilter === 'first') {
    orderedNTs.forEach(function(u) {
      var targets = firstDeps.get(u) || new Set();
      targets.forEach(function(v) {
        if (!nodeCoords.has(u) || !nodeCoords.has(v)) return;
        var p1 = nodeCoords.get(u);
        var p2 = nodeCoords.get(v);
        var isHl = selectedNT && (selectedNT === u || selectedNT === v);
        var isDim = selectedNT && !isHl;
        var cls = 'dep-edge-first' + (isHl ? ' dep-edge-highlight' : '') + (isDim ? ' dep-edge-dimmed' : '');
        var dx = p2.x - p1.x;
        var dy = p2.y - p1.y;
        var mx = (p1.x + p2.x) / 2 - dy * 0.15;
        var my = (p1.y + p2.y) / 2 + dx * 0.15;
        svg += '<path class="' + cls + '" d="M ' + p1.x + ' ' + p1.y + ' Q ' + mx + ' ' + my + ' ' + p2.x + ' ' + p2.y + '" marker-end="url(#arrow-first)"/>';
      });
    });
  }

  if (activeFilter === 'all' || activeFilter === 'follow') {
    orderedNTs.forEach(function(u) {
      var targets = followDeps.get(u) || new Set();
      targets.forEach(function(v) {
        if (!nodeCoords.has(u) || !nodeCoords.has(v)) return;
        var p1 = nodeCoords.get(u);
        var p2 = nodeCoords.get(v);
        var isHl = selectedNT && (selectedNT === u || selectedNT === v);
        var isDim = selectedNT && !isHl;
        var cls = 'dep-edge-follow' + (isHl ? ' dep-edge-highlight' : '') + (isDim ? ' dep-edge-dimmed' : '');
        var dx = p2.x - p1.x;
        var dy = p2.y - p1.y;
        var mx = (p1.x + p2.x) / 2 + dy * 0.15;
        var my = (p1.y + p2.y) / 2 - dx * 0.15;
        svg += '<path class="' + cls + '" d="M ' + p1.x + ' ' + p1.y + ' Q ' + mx + ' ' + my + ' ' + p2.x + ' ' + p2.y + '" marker-end="url(#arrow-follow)"/>';
      });
    });
  }

  // Nodes
  orderedNTs.forEach(function(nt) {
    var pt = nodeCoords.get(nt);
    var nw = Math.max(68, nt.length * 10 + 28);
    var nh = 32;
    var isSel = selectedNT === nt;
    var cls = 'dep-node' + (isSel ? ' active' : '');
    svg += '<g class="' + cls + '" onclick="selectInspectorNT(\'' + esc(nt) + '\')">';
    svg += '<rect x="' + (pt.x - nw / 2) + '" y="' + (pt.y - nh / 2) + '" width="' + nw + '" height="' + nh + '" rx="4" ry="4"/>';
    svg += '<text x="' + pt.x + '" y="' + pt.y + '">' + esc(nt) + '</text>';
    svg += '</g>';
  });

  svg += '</svg>';
  return svg;
}

// ============================================================
// SECTION 20: UI - RENDER PARSE TABLE
// ============================================================

function renderParseTable(terminalsList) {
  var gramLabel = G_active === G ? 'Original' : 'Transformed';
  var html = '<div class="banner banner-info mb-16"><span>\ud83d\udcca</span> LL(1) Parsing Table for: <strong class="font-mono">' + gramLabel + ' Grammar</strong></div>';

  html += '<div class="table-wrap"><table class="data-table" id="parseTableGrid"><tr><th>Non-Terminal</th>';
  terminalsList.forEach(function(t) { html += '<th>' + esc(t) + '</th>'; });
  html += '</tr>';

  G_active.orderedNTs.forEach(function(nt) {
    var row = PARSE_TABLE.get(nt);
    if (!row) return;
    html += '<tr><td class="fw-700 text-accent">' + esc(nt) + '</td>';
    terminalsList.forEach(function(t) {
      var entries = row.get(t) || [];
      var cellId = 'cell-' + nt.replace(/[^a-zA-Z0-9]/g, '_') + '-' + t.replace(/[^a-zA-Z0-9]/g, '_');
      if (entries.length === 0) {
        html += '<td id="' + cellId + '" style="color:var(--text-subtle);text-align:center;">&bull;</td>';
      } else if (entries.length === 1) {
        var prodStr = nt + ' \u2192 ' + entries[0].join(' ');
        var why = tableWhyMap.get(nt + ':' + t) || '';
        html += '<td id="' + cellId + '" class="tooltip-cell font-mono" style="color:var(--cyan)">' +
          esc(prodStr) + '<span class="tooltip-text">' + esc(why) + '</span></td>';
      } else {
        var prodStrs = entries.map(function(e) { return nt + ' \u2192 ' + e.join(' '); }).join('<br>');
        var why = tableWhyMap.get(nt + ':' + t) || 'CONFLICT';
        html += '<td id="' + cellId + '" class="conflict-cell tooltip-cell font-mono">' +
          prodStrs + '<span class="tooltip-text">' + esc(why) + '</span></td>';
      }
    });
    html += '</tr>';
  });

  html += '</table></div>';
  document.getElementById('tableContent').innerHTML = html;
}

// ============================================================
// SECTION 21: UI - RENDER CONFLICTS
// ============================================================

function renderConflicts(result) {
  var html = '';
  if (result.isLL1) {
    html += '<div class="banner banner-success mb-16"><span>\u2705</span> <strong>This grammar IS LL(1)!</strong> No conflicts detected. The parsing table has at most one entry per cell.</div>';
  } else {
    html += '<div class="banner banner-error mb-16"><span>\u274c</span> <strong>This grammar is NOT LL(1).</strong> ' + result.conflicts.length + ' conflict(s) found.</div>';
    result.conflicts.forEach(function(c, i) {
      html += '<div class="conflict-card">' +
        '<div class="card-title" style="color:var(--rose)"><span class="icon red">\u26a0</span> Conflict ' + (i + 1) + ': ' + esc(c.type) + ' at M[' + esc(c.nt) + ', ' + esc(c.terminal) + ']</div>' +
        '<div class="mb-8"><strong>Conflicting productions:</strong></div>' +
        '<ul style="margin:4px 0 8px 20px;font-family:var(--font-mono);color:var(--rose)">' +
        c.productions.map(function(p) { return '<li>' + esc(p) + '</li>'; }).join('') + '</ul>' +
        '<div class="explanation-box"><strong>Why:</strong> ' + esc(c.explanation) + '<br><br>' +
        '<strong>\ud83d\udca1 Suggestion:</strong> ' + esc(c.suggestion) + '</div></div>';
    });
  }
  document.getElementById('conflictsContent').innerHTML = html;
}

function updateBadges(immLR, indLR, commonPrefixes, conflictResult) {
  document.querySelectorAll('.tab-btn .badge').forEach(function(b) { b.remove(); });

  var prepBtn = document.querySelector('.tab-btn[data-tab="preprocess"]');
  if (prepBtn && (immLR.hasIt || indLR.hasIt || commonPrefixes.length > 0) && typeof prepBtn.insertAdjacentHTML === 'function') {
    prepBtn.insertAdjacentHTML('beforeend', '<span class="badge badge-warn">!</span>');
  }

  var confBtn = document.querySelector('.tab-btn[data-tab="conflicts"]');
  if (confBtn && typeof confBtn.insertAdjacentHTML === 'function') {
    if (conflictResult.isLL1) {
      confBtn.insertAdjacentHTML('beforeend', '<span class="badge badge-ok">\u2713</span>');
    } else {
      confBtn.insertAdjacentHTML('beforeend', '<span class="badge badge-error">' + conflictResult.conflicts.length + '</span>');
    }
  }

  var headerStatus = document.getElementById('headerStatus');
  if (headerStatus) {
    if (conflictResult.isLL1) {
      headerStatus.className = 'status-pill status-ok';
      headerStatus.innerHTML = '<span class="status-dot"></span> LL(1) Valid';
    } else {
      headerStatus.className = 'status-pill status-error';
      headerStatus.innerHTML = '<span class="status-dot"></span> ' + conflictResult.conflicts.length + ' Conflicts';
    }
  }
}

// ============================================================
// SECTION 22: UI - PUSHDOWN AUTOMATON (PDA) SIMULATION
// ============================================================

function renderSimulateTab() {
  var container = document.getElementById('simulateContent');
  if (!container) return;

  if (!G_active || !PARSE_TABLE) {
    container.innerHTML = '<p class="text-muted">Enter or select a grammar and click <strong>Run Analysis</strong> first.</p>';
    return;
  }

  var simIn = document.getElementById('simInput');
  var currentInput = simIn ? simIn.value.trim() : '';
  if (!currentInput) {
    var samples = generateSampleInputs(G_active, 1);
    currentInput = samples.length > 0 ? samples[0] : (G_active.terminals.size > 0 ? Array.from(G_active.terminals)[0] : '');
  }

  // Ensure the full container DOM is present
  var board = document.getElementById('pdaBoard');
  if (!board) {
    renderSimulateUI();
  }

  // Ensure an input string is present
  var simInEl = document.getElementById('simInput');
  if (simInEl && !simInEl.value) {
    simInEl.value = currentInput;
  }

  // Ensure simulation trace exists
  if (!simTrace || simTrace.length === 0) {
    var tokens = currentInput.split(/\s+/).filter(Boolean);
    var res = runParsingSimulation(tokens, PARSE_TABLE, G_active, FOLLOW_SETS);
    simTrace = res.trace;
    parseTreeRoot = res.treeRoot;
    simCurrentStep = 0;
  }

  renderPDABoard();
  renderSimTrace();
}

function renderSimulateUI(sampleInputs) {
  var container = document.getElementById('simulateContent');
  if (!container) return;

  var gramLabel = G_active === G ? 'Original' : 'Transformed';
  var conflictWarn = conflictInfo.length > 0 ? '<span class="text-orange" style="margin-left:12px">\u26a0 Grammar has conflicts \u2014 parser uses first applicable rule</span>' : '';
  var html = '<div class="banner banner-info mb-12"><span>\u25b6</span> Simulating Pushdown Automaton on: <strong class="font-mono">' + gramLabel + ' Grammar</strong>' + conflictWarn + '</div>';

  var samples = sampleInputs || (G_active ? generateSampleInputs(G_active, 5) : []);
  var currentVal = '';
  var simInputEl = document.getElementById('simInput');
  if (simInputEl && simInputEl.value) {
    currentVal = simInputEl.value;
  } else if (samples.length > 0) {
    currentVal = samples[0];
  }

  html += '<div class="tree-input-bar mb-8" style="display:flex;gap:8px;align-items:center;flex-wrap:wrap;">' +
    '<input type="text" id="simInput" placeholder="Enter token sequence e.g.: ' + (samples[0] || 'id + id * id') + '" value="' + esc(currentVal) + '" style="flex:1;min-width:220px;" />' +
    '<button class="btn btn-primary btn-sm" onclick="startSimulation()">\ud83d\ude80 Parse &amp; Simulate</button>' +
    '</div>';

  if (samples.length > 0) {
    html += '<div class="quick-inputs-wrap mb-12">' +
      '<span class="quick-inputs-title">Valid Inputs for this Grammar:</span>' +
      '<div class="quick-chips">' +
      samples.map(function(s) {
        return '<button type="button" class="quick-chip-btn" onclick="applyQuickInput(\'' + esc(s).replace(/'/g, "\\'") + '\')">' + esc(s) + '</button>';
      }).join('') +
      '</div></div>';
  }

  html += '<div class="sim-controls mb-12">' +
    '<button class="btn btn-secondary btn-sm" onclick="simJumpTo(0)" title="Jump to start">\u23ee Start</button>' +
    '<button class="btn btn-secondary btn-sm" onclick="simPrev()" title="Step backward">\u25c0 Prev</button>' +
    '<button id="btnAutoPlay" class="btn btn-success btn-sm" onclick="simAutoPlay()" title="Play automatic step-by-step animation">\u25b6 Play</button>' +
    '<button class="btn btn-secondary btn-sm" onclick="simStop()" title="Pause animation">\u23f8 Pause</button>' +
    '<button class="btn btn-secondary btn-sm" onclick="simNext()" title="Step forward">Next \u25b6</button>' +
    '<button class="btn btn-secondary btn-sm" onclick="simRunAll()" title="Jump to last step">End \u23ed</button>' +
    '<button class="btn btn-secondary btn-sm" onclick="simReset()" title="Reset simulation">\ud83d\udd04 Reset</button>' +
    '<div class="speed-control"><span class="speed-label">Speed:</span>' +
    '<input type="range" id="simSpeed" min="100" max="2000" value="700" step="100">' +
    '<span class="speed-label" id="speedVal">700ms</span></div></div>';

  html += '<div id="pdaBoard" class="pda-board mb-16"></div>';
  html += '<div id="simErrors" class="mb-8"></div>';
  html += '<div id="simTraceArea"></div>';

  container.innerHTML = html;

  var speedSlider = document.getElementById('simSpeed');
  if (speedSlider && typeof speedSlider.addEventListener === 'function') {
    speedSlider.addEventListener('input', function() {
      var sv = document.getElementById('speedVal');
      if (sv) sv.textContent = speedSlider.value + 'ms';
    });
  }

  var simInp = document.getElementById('simInput');
  if (simInp && typeof simInp.addEventListener === 'function') {
    simInp.addEventListener('keydown', function(e) {
      if (e.key === 'Enter') startSimulation();
    });
  }
}

function renderPDABoard() {
  var board = document.getElementById('pdaBoard');
  if (!board) return;

  if (!simTrace || simTrace.length === 0 || simCurrentStep >= simTrace.length) {
    board.innerHTML = '<p class="text-muted">No simulation steps available.</p>';
    return;
  }

  var step = simTrace[simCurrentStep];
  var rawStack = step.rawStack || (step.stack ? step.stack.split(' ').reverse() : ['$']);
  var rawInput = step.rawInput || (step.input ? step.input.split(' ') : ['$']);
  var ptr = step.ptr !== undefined ? step.ptr : 0;

  // 1. Stack Panel (Bottom-to-Top vertically, TOS at the very top)
  var stackHtml = '<div class="pda-card">';
  stackHtml += '<div class="pda-card-title"><span>\ud83d\udcda LIFO Stack</span><span class="bento-tag">' + rawStack.length + ' symbols</span></div>';
  stackHtml += '<div class="pda-stack-container">';
  
  for (var i = rawStack.length - 1; i >= 0; i--) {
    var sym = rawStack[i];
    var isTOS = (i === rawStack.length - 1);
    var isNT = G_active && G_active.nonTerminals && G_active.nonTerminals.has(sym);
    var isBot = (sym === '$');
    var cellCls = isBot ? 'bottom' : (isNT ? 'nt' : 'term');
    
    stackHtml += '<div class="pda-stack-cell ' + cellCls + (isTOS ? ' tos' : '') + '">';
    stackHtml += '<span>' + esc(sym) + '</span>';
    if (isTOS) {
      stackHtml += '<span class="pda-tos-tag">TOS \u25bc</span>';
    } else if (isBot) {
      stackHtml += '<span style="font-size:10px;color:var(--text-subtle);">Base ($)</span>';
    }
    stackHtml += '</div>';
  }
  stackHtml += '</div></div>';

  // 2. Control Unit Panel (State, Transition, Action)
  var isAccept = step.action.indexOf('Accept') >= 0;
  var isError = step.action.indexOf('Error') >= 0;
  var stateName = isAccept ? 'q_acc' : (step.step === 1 ? 'q_0' : 'q_1');

  var controlHtml = '<div class="pda-card">';
  controlHtml += '<div class="pda-card-title"><span>\u2699\ufe0f PDA Control Unit</span><span class="pda-state-badge">State: <strong>' + stateName + '</strong></span></div>';
  controlHtml += '<div class="pda-control-state">';
  
  controlHtml += '<div class="pda-action-box">';
  controlHtml += '<div class="pda-action-main' + (isAccept ? ' text-green' : (isError ? ' text-red' : '')) + '">' + esc(step.action) + '</div>';
  if (step.cellNT && step.cellT) {
    controlHtml += '<div class="pda-action-sub">Lookup Table M[' + esc(step.cellNT) + ', ' + esc(step.cellT) + ']</div>';
  } else if (isAccept) {
    controlHtml += '<div class="pda-action-sub text-green">\u2713 Input string is valid and accepted by the automaton!</div>';
  } else {
    controlHtml += '<div class="pda-action-sub">Step ' + step.step + ' of ' + simTrace.length + '</div>';
  }
  controlHtml += '</div>';

  var pct = Math.round(((simCurrentStep + 1) / simTrace.length) * 100);
  controlHtml += '<div style="margin-top:auto;padding-top:10px;">' +
    '<div style="display:flex;justify-content:space-between;font-size:11px;color:var(--text-subtle);margin-bottom:4px;">' +
    '<span>Step ' + (simCurrentStep + 1) + ' of ' + simTrace.length + '</span><span>' + pct + '%</span></div>' +
    '<div style="height:4px;background:#27272a;border-radius:2px;overflow:hidden;">' +
    '<div style="height:100%;background:var(--accent);width:' + pct + '%;transition:width 0.2s;"></div></div>' +
    '</div>';

  controlHtml += '</div></div>';

  // 3. Input Tape Panel (Remaining and matched tokens)
  var tapeHtml = '<div class="pda-card">';
  tapeHtml += '<div class="pda-card-title"><span>\ud83d\udcbf Input Tape</span><span class="bento-tag">Head: #' + ptr + '</span></div>';
  tapeHtml += '<div class="pda-tape-container">';
  tapeHtml += '<div class="pda-tape-cells">';
  
  for (var ti = 0; ti < rawInput.length; ti++) {
    var tok = rawInput[ti];
    var isHead = (ti === ptr);
    var isMatched = (ti < ptr);
    var tapeCls = isHead ? 'active-token' : (isMatched ? 'matched-token' : '');
    
    tapeHtml += '<div class="pda-tape-cell ' + tapeCls + '" title="Token #' + ti + ': ' + esc(tok) + '">';
    tapeHtml += '<span>' + esc(tok) + '</span>';
    tapeHtml += '</div>';
  }
  
  tapeHtml += '</div>';
  tapeHtml += '<div style="font-size:11px;color:var(--text-subtle);margin-top:14px;">' +
    (isAccept 
      ? '<span class="text-green">\u2705 End of Input marker ($) reached.</span>' 
      : 'Lookahead: <strong class="text-cyan font-mono">' + esc(rawInput[ptr] || '$') + '</strong>') +
    '</div>';
  tapeHtml += '</div></div>';

  board.innerHTML = stackHtml + controlHtml + tapeHtml;
}

function startSimulation() {
  if (!PARSE_TABLE || !G_active) { alert('Please analyze a grammar first.'); return; }

  var inputStr = document.getElementById('simInput').value.trim();
  var treeIn = document.getElementById('treeInput');
  if (treeIn) treeIn.value = inputStr;

  var tokens = inputStr.split(/\s+/).filter(Boolean);
  var result = runParsingSimulation(tokens, PARSE_TABLE, G_active, FOLLOW_SETS);

  simTrace = result.trace;
  parseTreeRoot = result.treeRoot;
  simCurrentStep = 0;

  renderSimTrace();

  var errEl = document.getElementById('simErrors');
  if (errEl) {
    if (result.errors.length > 0) {
      errEl.innerHTML = '<div class="banner banner-error"><span>\u274c</span><div>' +
        result.errors.map(function(e) { return '<div>' + esc(e) + '</div>'; }).join('') + '</div></div>';
    } else {
      errEl.innerHTML = result.accepted
        ? '<div class="banner banner-success"><span>\u2705</span> Input accepted successfully!</div>' : '';
    }
  }

  renderTreeTab();
}

function renderSimTrace() {
  if (simTrace.length === 0) return;

  renderPDABoard();

  var html = '<div class="table-wrap"><table class="data-table" id="simTable">' +
    '<tr><th>Step</th><th>Stack (TOS at Right)</th><th>Input Buffer</th><th>Action Taken</th></tr>';

  simTrace.forEach(function(t, i) {
    var cls = i === simCurrentStep ? ' class="active-step"' : '';
    html += '<tr id="sim-row-' + i + '" style="cursor:pointer;" onclick="simJumpTo(' + i + ')">' +
      '<td' + cls + '>' + t.step + '</td>' +
      '<td' + cls + ' style="font-family:var(--font-mono);font-size:12px">' + esc(t.stack) + '</td>' +
      '<td' + cls + ' style="font-family:var(--font-mono);font-size:12px">' + esc(t.input) + '</td>' +
      '<td' + cls + '>' + esc(t.action) + '</td></tr>';
  });

  html += '</table></div>';
  html += '<div class="text-muted mt-8" style="font-size:12px">Step ' + (simCurrentStep + 1) + ' of ' + simTrace.length + ' &bull; Click any table row to jump to that step</div>';

  var traceArea = document.getElementById('simTraceArea');
  if (traceArea) traceArea.innerHTML = html;
  highlightTableCell();

  var row = document.getElementById('sim-row-' + simCurrentStep);
  if (row && typeof row.scrollIntoView === 'function') row.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
}

function highlightTableCell() {
  document.querySelectorAll('#parseTableGrid td.highlight').forEach(function(td) { td.classList.remove('highlight'); });
  if (simCurrentStep < simTrace.length) {
    var step = simTrace[simCurrentStep];
    if (step.cellNT && step.cellT) {
      var cellId = 'cell-' + step.cellNT.replace(/[^a-zA-Z0-9]/g, '_') + '-' + step.cellT.replace(/[^a-zA-Z0-9]/g, '_');
      var cell = document.getElementById(cellId);
      if (cell) cell.classList.add('highlight');
    }
  }
}

function simJumpTo(stepIndex) {
  if (stepIndex >= 0 && stepIndex < simTrace.length) {
    simStop();
    simCurrentStep = stepIndex;
    renderSimTrace();
  }
}

function simNext() {
  if (simTrace.length === 0) startSimulation();
  if (simCurrentStep < simTrace.length - 1) { simCurrentStep++; renderSimTrace(); }
}

function simPrev() {
  if (simTrace.length === 0) startSimulation();
  if (simCurrentStep > 0) { simCurrentStep--; renderSimTrace(); }
}

function simAutoPlay() {
  if (simTrace.length === 0) startSimulation();
  simStop();
  if (simCurrentStep >= simTrace.length - 1) {
    simCurrentStep = 0;
  }
  var speed = parseInt((document.getElementById('simSpeed') || {}).value || '700');
  autoPlayInterval = setInterval(function() {
    if (simCurrentStep < simTrace.length - 1) {
      simCurrentStep++;
      renderSimTrace();
    } else {
      simStop();
    }
  }, speed);
}

function simStop() { if (autoPlayInterval) { clearInterval(autoPlayInterval); autoPlayInterval = null; } }

function simRunAll() {
  if (simTrace.length === 0) startSimulation();
  simStop();
  simCurrentStep = simTrace.length - 1;
  renderSimTrace();
}

function simReset() {
  simStop();
  simCurrentStep = 0;
  if (simTrace.length > 0) renderSimTrace();
}

// ============================================================
// SECTION 23: UI - PARSE TREE TAB & CONTROLS
// ============================================================

function autoRunSimulation(overrideInput) {
  if (!PARSE_TABLE || !G_active) return;
  var inputStr = overrideInput !== undefined ? overrideInput : '';
  if (!inputStr) {
    var simInputEl = document.getElementById('simInput');
    inputStr = simInputEl ? simInputEl.value.trim() : '';
  }
  if (!inputStr) {
    var samples = generateSampleInputs(G_active, 1);
    inputStr = samples.length > 0 ? samples[0] : (G_active.terminals.size > 0 ? Array.from(G_active.terminals)[0] : '');
  }

  var simInputEl = document.getElementById('simInput');
  if (simInputEl) simInputEl.value = inputStr;
  var treeInputEl = document.getElementById('treeInput');
  if (treeInputEl) treeInputEl.value = inputStr;

  var tokens = inputStr.split(/\s+/).filter(Boolean);
  var result = runParsingSimulation(tokens, PARSE_TABLE, G_active, FOLLOW_SETS);
  simTrace = result.trace;
  parseTreeRoot = result.treeRoot;
  simCurrentStep = simTrace.length > 0 ? simTrace.length - 1 : 0;

  renderSimTrace();
  renderTreeTab();
}

function renderTreeTab() {
  var container = document.getElementById('treeContent');
  if (!container) return;

  if (!G_active || !PARSE_TABLE) {
    container.innerHTML = '<p class="text-muted">Enter or select a grammar and click <strong>Analyze Grammar</strong> first.</p>';
    return;
  }

  // Ensure simulation has run with the active grammar's input
  if (!parseTreeRoot) {
    var treeIn = document.getElementById('treeInput');
    var inputStr = treeIn ? treeIn.value.trim() : '';
    if (!inputStr) {
      var samples = generateSampleInputs(G_active, 1);
      inputStr = samples.length > 0 ? samples[0] : (G_active.terminals.size > 0 ? Array.from(G_active.terminals)[0] : '');
      if (treeIn) treeIn.value = inputStr;
    }
    var tokens = inputStr.split(/\s+/).filter(Boolean);
    var res = runParsingSimulation(tokens, PARSE_TABLE, G_active, FOLLOW_SETS);
    parseTreeRoot = res.treeRoot;
    simTrace = res.trace;
  }

  var statusEl = document.getElementById('treeStatus');
  if (statusEl && simTrace && simTrace.length > 0) {
    var lastAction = simTrace[simTrace.length - 1].action;
    var accepted = lastAction.indexOf('Accept') >= 0;
    statusEl.innerHTML = accepted
      ? '<div class="banner banner-success"><span>\u2705</span> <strong>Parse Tree generated successfully!</strong> Input string matches grammar rules.</div>'
      : '<div class="banner banner-warn"><span>\u26a0</span> <strong>Partial Parse Tree:</strong> Input contains syntax errors (panic-mode recovery applied).</div>';
  }

  treeZoomLevel = 1.0;
  var svgHtml = renderParseTreeSVG(parseTreeRoot, G_active.nonTerminals);
  container.innerHTML = '<div class="tree-container"><div id="treeSvgWrapper" style="display:inline-block;transform-origin:top center;transition:transform 0.15s ease-out;">' + svgHtml + '</div></div>';
  setupTreePanAndZoom();
}

var isPanning = false;
var panStartX = 0, panStartY = 0;
var panScrollLeft = 0, panScrollTop = 0;

function setupTreePanAndZoom() {
  var container = document.querySelector('.tree-container');
  if (!container || container._panZoomInit || typeof container.addEventListener !== 'function') return;
  container._panZoomInit = true;

  container.addEventListener('mousedown', function(e) {
    if (e.button !== 0 || e.target.tagName === 'BUTTON' || e.target.tagName === 'INPUT') return;
    isPanning = true;
    container.classList.add('is-panning');
    panStartX = e.pageX - container.offsetLeft;
    panStartY = e.pageY - container.offsetTop;
    panScrollLeft = container.scrollLeft;
    panScrollTop = container.scrollTop;
  });

  window.addEventListener('mouseup', function() {
    if (isPanning) {
      isPanning = false;
      var c = document.querySelector('.tree-container');
      if (c) c.classList.remove('is-panning');
    }
  });

  window.addEventListener('mousemove', function(e) {
    if (!isPanning) return;
    e.preventDefault();
    var c = document.querySelector('.tree-container');
    if (!c) return;
    var x = e.pageX - c.offsetLeft;
    var y = e.pageY - c.offsetTop;
    var walkX = (x - panStartX);
    var walkY = (y - panStartY);
    c.scrollLeft = panScrollLeft - walkX;
    c.scrollTop = panScrollTop - walkY;
  });

  container.addEventListener('wheel', function(e) {
    if (e.ctrlKey || e.metaKey) {
      e.preventDefault();
      if (e.deltaY < 0) {
        zoomTree(1.15);
      } else {
        zoomTree(0.85);
      }
    }
  }, { passive: false });
}

function fitTreeToView() {
  var container = document.querySelector('.tree-container');
  var svg = document.getElementById('parseTreeSvg');
  var wrapper = document.getElementById('treeSvgWrapper');
  if (!container || !svg || !wrapper) return;

  var containerW = container.clientWidth - 48;
  var containerH = container.clientHeight - 48;
  var svgW = parseFloat(svg.getAttribute('width')) || svg.clientWidth || 500;
  var svgH = parseFloat(svg.getAttribute('height')) || svg.clientHeight || 300;

  var scale = Math.min(containerW / svgW, containerH / svgH);
  treeZoomLevel = Math.max(0.25, Math.min(2.0, Math.round(scale * 100) / 100));
  wrapper.style.transform = 'scale(' + treeZoomLevel + ')';
  container.scrollLeft = 0;
  container.scrollTop = 0;
}

function renderTreeQuickInputs(sampleInputs) {
  var el = document.getElementById('treeQuickInputs');
  if (!el) return;
  var samples = sampleInputs || (G_active ? generateSampleInputs(G_active, 5) : []);
  if (!samples || samples.length === 0) {
    el.innerHTML = '<span class="text-muted" style="font-size:12px;">Type any token sequence above and click <strong>Generate Tree</strong></span>';
    return;
  }
  var html = '<div class="quick-inputs-wrap">' +
    '<span class="quick-inputs-title">Valid Inputs for this Grammar:</span>' +
    '<div class="quick-chips">' +
    samples.map(function(s) {
      return '<button type="button" class="quick-chip-btn" onclick="applyQuickInput(\'' + esc(s).replace(/'/g, "\\'") + '\')">' + esc(s) + '</button>';
    }).join('') +
    '</div></div>';
  el.innerHTML = html;
}

function applyQuickInput(val) {
  var simIn = document.getElementById('simInput');
  if (simIn) simIn.value = val;
  var treeIn = document.getElementById('treeInput');
  if (treeIn) treeIn.value = val;
  startSimulation();
  renderTreeTab();
}

function generateTreeFromInput() {
  if (!PARSE_TABLE || !G_active) {
    alert('Please enter and analyze a grammar first in the Grammar tab.');
    return;
  }
  var treeInputEl = document.getElementById('treeInput');
  var inputStr = treeInputEl ? treeInputEl.value.trim() : '';

  var simIn = document.getElementById('simInput');
  if (simIn) simIn.value = inputStr;

  var tokens = inputStr.split(/\s+/).filter(Boolean);
  var result = runParsingSimulation(tokens, PARSE_TABLE, G_active, FOLLOW_SETS);

  simTrace = result.trace;
  parseTreeRoot = result.treeRoot;
  simCurrentStep = simTrace.length > 0 ? simTrace.length - 1 : 0;

  renderTreeTab();
  renderSimTrace();
}

function zoomTree(factor) {
  treeZoomLevel = Math.max(0.25, Math.min(3.0, Math.round((treeZoomLevel * factor) * 100) / 100));
  var wrapper = document.getElementById('treeSvgWrapper');
  if (wrapper) wrapper.style.transform = 'scale(' + treeZoomLevel + ')';
}

function resetTreeZoom() {
  treeZoomLevel = 1.0;
  var wrapper = document.getElementById('treeSvgWrapper');
  if (wrapper) wrapper.style.transform = 'scale(1)';
}

function downloadTreeSVG() {
  var svgEl = document.getElementById('parseTreeSvg') || document.querySelector('.tree-container svg');
  if (!svgEl) { alert('No parse tree to download.'); return; }
  var serializer = new XMLSerializer();
  var svgStr = serializer.serializeToString(svgEl);
  var blob = new Blob([svgStr], { type: 'image/svg+xml;charset=utf-8' });
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = 'parse_tree.svg';
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

// ============================================================
// SECTION 24: EXPORT REPORT GENERATOR
// ============================================================

function exportReport() {
  if (!G_active) { alert('Please analyze a grammar first before exporting.'); return; }

  // Clean, professional pure WHITE document theme for printing and assignment submission
  var r = '<!DOCTYPE html>' + '<html><head><meta charset="UTF-8"><title>LL(1) Parser Studio — Formal Assignment Report</title>' +
    '<style>' +
    'html, body { background: #ffffff !important; color: #1e293b !important; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; }' +
    'body { max-width: 960px; margin: 0 auto; padding: 36px 30px; line-height: 1.6; }' +
    'h1 { color: #047857; font-size: 24px; border-bottom: 2px solid #10b981; padding-bottom: 8px; margin-bottom: 6px; }' +
    'h2 { color: #0f172a; font-size: 17px; border-bottom: 1px solid #e2e8f0; padding-bottom: 6px; margin-top: 28px; }' +
    '.meta { color: #64748b; font-size: 13px; margin-bottom: 20px; }' +
    'table { border-collapse: collapse; width: 100%; margin: 14px 0; background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; overflow: hidden; font-size: 13px; }' +
    'th, td { border: 1px solid #e2e8f0; padding: 10px 14px; text-align: left; }' +
    'th { background: #f8fafc; color: #1e293b; font-weight: 700; text-transform: uppercase; font-size: 11.5px; letter-spacing: 0.03em; border: 1px solid #cbd5e1; }' +
    'tr:nth-child(even) td { background: #f8fafc; }' +
    '.conflict { background: #fee2e2 !important; color: #991b1b !important; font-weight: 700; border: 1px solid #f87171 !important; }' +
    '.mono { font-family: "Fira Code", Consolas, "Courier New", monospace; color: #0f172a; }' +
    '.success { color: #059669; font-weight: 600; }' +
    '.error { color: #dc2626; font-weight: 600; }' +
    '.step { background: #f8fafc; border: 1px solid #e2e8f0; border-left: 4px solid #10b981; padding: 10px 14px; margin: 8px 0; font-size: 13px; border-radius: 4px; color: #334155; }' +
    '.grammar-box { background: #f8fafc; border: 1px solid #e2e8f0; border-radius: 6px; padding: 14px; margin: 10px 0; font-family: "Fira Code", Consolas, monospace; font-size: 13.5px; color: #0f172a; }' +
    '.tree-box { background: #f8fafc; border: 1px solid #e2e8f0; border-radius: 8px; padding: 24px; text-align: center; margin: 14px 0; overflow-x: auto; }' +
    '.tree-box svg { max-width: 100%; height: auto; display: block; margin: 0 auto; background: #ffffff; }' +
    '.tree-box svg text { font-family: "Fira Code", Consolas, monospace; font-size: 12px; text-anchor: middle; dominant-baseline: central; user-select: none; }' +
    '.tree-box svg .node-nt { fill: #ecfdf5; stroke: #059669; stroke-width: 2px; }' +
    '.tree-box svg .node-t { fill: #fef3c7; stroke: #d97706; stroke-width: 2px; }' +
    '.tree-box svg .node-eps { fill: #faf5ff; stroke: #9333ea; stroke-width: 2px; stroke-dasharray: 4 2; }' +
    '.tree-box svg .label-nt { fill: #065f46; font-weight: 700; }' +
    '.tree-box svg .label-t { fill: #92400e; font-weight: 700; }' +
    '.tree-box svg .label-eps { fill: #6b21a8; font-weight: 700; font-style: italic; }' +
    '.tree-box svg .edge { stroke: #94a3b8; stroke-width: 2px; fill: none; }' +
    '.tree-legend { display: flex; justify-content: center; gap: 20px; font-size: 12px; margin-top: 14px; font-weight: 500; }' +
    '.legend-item { display: inline-flex; align-items: center; gap: 6px; }' +
    '.legend-swatch { width: 14px; height: 14px; border-radius: 4px; display: inline-block; }' +
    '.print-btn { background: #059669; color: #ffffff; border: none; padding: 9px 18px; border-radius: 6px; font-weight: 600; cursor: pointer; font-size: 13px; }' +
    '.print-btn:hover { background: #047857; }' +
    '@media print {' +
    '  body { padding: 0 !important; max-width: 100% !important; }' +
    '  .no-print { display: none !important; }' +
    '  .tree-box { border: 1px solid #cbd5e1 !important; page-break-inside: avoid; }' +
    '  table { page-break-inside: auto; }' +
    '  tr { page-break-inside: avoid; page-break-after: auto; }' +
    '  h1, h2 { page-break-after: avoid; }' +
    '}' +
    '</style></head><body>';

  r += '<div class="no-print" style="margin-bottom:18px;display:flex;justify-content:flex-end;">' +
    '<button class="print-btn" onclick="window.print()">\ud83d\udda8\ufe0f Print / Save as PDF</button></div>';

  r += '<h1>LL(1) Parser Studio \u2014 Formal Analysis Report</h1>';
  r += '<p class="meta">Principles of Compiler Design &bull; Generated: ' + new Date().toLocaleString() + '</p>';

  // Grammar
  var gramLabel = G_active === G ? 'Original' : 'Transformed';
  r += '<h2>Grammar (' + gramLabel + ')</h2><div class="grammar-box">';
  G_active.orderedNTs.forEach(function(nt) {
    var alts = G_active.rules.get(nt);
    if (!alts) return;
    r += '<div>' + nt + ' \u2192 ' + alts.map(function(a) { return a.join(' '); }).join(' | ') + '</div>';
  });
  r += '</div>';
  r += '<p style="font-size:13px;"><strong>Start Symbol:</strong> <span class="mono">' + G_active.startSymbol + '</span></p>';

  // FIRST
  if (FIRST_SETS) {
    r += '<h2>FIRST Sets</h2><table><tr><th>Non-Terminal</th><th>FIRST Set</th></tr>';
    G_active.orderedNTs.forEach(function(nt) {
      var fs = FIRST_SETS.get(nt);
      if (!fs) return;
      var arr = Array.from(fs); arr.sort();
      r += '<tr><td class="mono" style="color:#047857;font-weight:700;">' + nt + '</td><td class="mono">{ ' + arr.join(', ') + ' }</td></tr>';
    });
    r += '</table>';
  }

  // FOLLOW
  if (FOLLOW_SETS) {
    r += '<h2>FOLLOW Sets</h2><table><tr><th>Non-Terminal</th><th>FOLLOW Set</th></tr>';
    G_active.orderedNTs.forEach(function(nt) {
      var fs = FOLLOW_SETS.get(nt);
      if (!fs) return;
      var arr = Array.from(fs); arr.sort();
      r += '<tr><td class="mono" style="color:#047857;font-weight:700;">' + nt + '</td><td class="mono">{ ' + arr.join(', ') + ' }</td></tr>';
    });
    r += '</table>';
  }

  // Table
  if (PARSE_TABLE) {
    var terms = []; G_active.terminals.forEach(function(t) { terms.push(t); }); terms.sort(); terms.push('$');
    r += '<h2>LL(1) Parsing Table</h2><table><tr><th>NT</th>';
    terms.forEach(function(t) { r += '<th>' + t + '</th>'; });
    r += '</tr>';
    G_active.orderedNTs.forEach(function(nt) {
      var row = PARSE_TABLE.get(nt);
      if (!row) return;
      r += '<tr><td class="mono" style="color:#047857;font-weight:700;">' + nt + '</td>';
      terms.forEach(function(t) {
        var entries = row.get(t) || [];
        var cls = entries.length > 1 ? ' class="conflict"' : '';
        r += '<td' + cls + ' class="mono">' + entries.map(function(e) { return nt + '\u2192' + e.join(' '); }).join(', ') + '</td>';
      });
      r += '</tr>';
    });
    r += '</table>';
  }

  // Conflicts
  if (conflictInfo !== undefined) {
    r += '<h2>Conflict Analysis</h2>';
    if (conflictInfo.length === 0) {
      r += '<p class="success">\u2705 Grammar IS LL(1) \u2014 zero conflicts.</p>';
    } else {
      r += '<p class="error">\u274c Grammar is NOT LL(1) \u2014 ' + conflictInfo.length + ' conflict(s) detected.</p>';
      conflictInfo.forEach(function(c) {
        r += '<div class="step"><strong>' + c.type + ' at M[' + c.nt + ', ' + c.terminal + ']</strong><br>' +
          'Productions: <span class="mono">' + c.productions.join(', ') + '</span><br>' + c.explanation + '<br><strong>Suggestion:</strong> ' + c.suggestion + '</div>';
      });
    }
  }

  // Trace
  if (simTrace && simTrace.length > 0) {
    r += '<h2>Parsing Simulation Trace</h2><table><tr><th>Step</th><th>Stack</th><th>Input</th><th>Action</th></tr>';
    simTrace.forEach(function(t) {
      r += '<tr><td>' + t.step + '</td><td class="mono">' + esc(t.stack) + '</td><td class="mono">' + esc(t.input) + '</td><td>' + esc(t.action) + '</td></tr>';
    });
    r += '</table>';
  }

  // Ensure parse tree exists
  if (!parseTreeRoot && G_active) {
    var treeInEl = document.getElementById('treeInput');
    var fallbackInput = treeInEl ? treeInEl.value.trim() : '';
    if (!fallbackInput) {
      var sampleInputs = generateSampleInputs(G_active, 1);
      fallbackInput = sampleInputs.length > 0 ? sampleInputs[0] : '';
    }
    if (fallbackInput) {
      var res = simulateParsing(G_active, PARSE_TABLE, fallbackInput);
      parseTreeRoot = res.treeRoot;
    }
  }

  // Parse Tree SVG
  if (parseTreeRoot && G_active) {
    var treeInText = document.getElementById('treeInput');
    var activeInputStr = treeInText ? treeInText.value.trim() : '';
    r += '<h2>Parse Tree Visualization</h2><div class="tree-box">';
    if (activeInputStr) {
      r += '<p style="font-size:13px;color:#475569;margin-bottom:14px;"><strong>Target Input:</strong> <span class="mono" style="background:#ffffff;padding:2px 8px;border:1px solid #cbd5e1;border-radius:4px;">' + esc(activeInputStr) + '</span></p>';
    }
    r += renderParseTreeSVG(parseTreeRoot, G_active.nonTerminals);
    r += '<div class="tree-legend">' +
      '<span class="legend-item"><span class="legend-swatch" style="background:#ecfdf5;border:2px solid #059669;"></span> Non-Terminal</span>' +
      '<span class="legend-item"><span class="legend-swatch" style="background:#fef3c7;border:2px solid #d97706;"></span> Terminal</span>' +
      '<span class="legend-item"><span class="legend-swatch" style="background:#faf5ff;border:2px dashed #9333ea;"></span> Epsilon (&epsilon;)</span>' +
      '</div>';
    r += '</div>';
  }

  r += '</body></html>';

  var blob = new Blob([r], { type: 'text/html' });
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = 'LL1_Parser_Report.html';
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

// ============================================================
// SECTION 25: INITIALIZATION
// ============================================================

document.addEventListener('DOMContentLoaded', function() {
  var txt = document.getElementById('txtGrammar');
  if (txt) {
    txt.addEventListener('input', updateEditorStats);
    txt.addEventListener('keydown', function(e) {
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        analyzeGrammar();
      }
    });
  }

  switchTab('summary');

  var treeIn = document.getElementById('treeInput');
  if (treeIn) {
    treeIn.addEventListener('keydown', function(e) {
      if (e.key === 'Enter') generateTreeFromInput();
    });
  }
});
