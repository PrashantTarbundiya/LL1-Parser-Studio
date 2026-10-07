# ⚡ LL(1) Parser Studio — Compiler Design Workbench

> A comprehensive, interactive **FIRST & FOLLOW Set Calculator, Table Generator & CFG Simulator** built for Compiler Design (PCD) students, educators, and engineers.

![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)
![Status: 100% Tests Passed](https://img.shields.io/badge/Tests-77%2F77%20Passed-success.svg)
![Stack: HTML5 / Vanilla CSS / Modern JS](https://img.shields.io/badge/Stack-Vanilla%20Web-orange.svg)

---

## 📖 Overview

**LL(1) Parser Studio** is a full-featured web-based compiler workbench that accepts arbitrary Context-Free Grammars (CFGs), computes exact **FIRST and FOLLOW sets** using the standard fixed-point iteration algorithm, verifies **LL(1) grammar compatibility**, diagnoses parsing conflicts, constructs the **LL(1) parsing table**, and visualizes step-by-step stack execution with a live interactive simulator.

---

## ✨ Key Features

- **Accurate FIRST & FOLLOW Set Engine**:
  - Implements the formal fixed-point iterative algorithm across all CFG scenarios.
  - Full mathematical justification and step-by-step trace for every added symbol.
- **Dual Grammar Syntax Support**:
  - Supports standard space-delimited productions:
    ```text
    S -> a B D h
    B -> c C
    C -> b C | ε
    D -> E F
    E -> g | ε
    F -> f | ε
    ```
  - Also automatically tokenizes unspaced CFG shorthand:
    ```text
    S -> aBDh
    B -> cC
    C -> bC | ε
    D -> EF
    ```
- **Standard Compiler Design Symbol Conventions**:
  - **Capital Letters** (`A-Z`, e.g., `S`, `B`, `C`, `D`, `E`, `F`, `E'`, `T'`, `Expr`) = **Non-Terminals**.
  - **Small Letters & Symbols** (`a-z`, `+`, `*`, `(`, `)`, `id`, `num`, `while`, `else`) = **Terminals**.
  - **Epsilon Representations**: Supports `ε`, `eps`, `epsilon`, `#`, and `@`.
  - **End-of-Input Marker**: Reserved `$` symbol.
- **Advanced Grammar Diagnostics**:
  - Immediate & indirect left recursion detection.
  - Common prefix detection (left factoring requirement).
  - Nullability tracking with full dependency chains.
- **LL(1) Parsing Table & Conflict Analyzer**:
  - Constructs the predictive parsing table $M[A, a]$.
  - Pinpoints **FIRST/FIRST** and **FIRST/FOLLOW** conflicts with exact symbol references.
- **Step-by-Step Interactive Simulator**:
  - Step forward, backward, auto-play with adjustable speed (0.5x, 1x, 2x).
  - Live stack snapshots, remaining input stream, and production derivation tracking.
- **Export Formal Reports**:
  - Export self-contained HTML reports with complete mathematical derivations and parsing tables.

---

## 🚀 Getting Started

No build tools, npm packages, or dependencies required! Simply run directly in any web browser.

### Option 1: Direct Browser Launch
Open either [`index.html`](index.html) or [`LL1-Parser-Studio.html`](LL1-Parser-Studio.html) directly in Chrome, Firefox, Edge, or Safari.

### Option 2: Local HTTP Server
Using Python:
```bash
python -m http.server 8085
```
Using Node.js:
```bash
npx serve .
```
Then navigate to `http://localhost:8085` in your browser.

---

## 🧪 Regression Test Suite

All 12 standard CFG scenarios are verified and pass 100% (77/77 checks):

| # | Test Scenario | Grammar | Key Verification |
|:---:|---|---|---|
| **1** | **Very Simple** | `S -> a` | Basic terminal derivation |
| **2** | **Epsilon** | `S -> A`, `A -> a \| ε` | $\varepsilon$-propagation to start symbol |
| **3** | **Nullable Chain** | `S -> A B C`, `A -> a \| ε`, `B -> b \| ε`, `C -> c` | Multi-symbol lookahead through nullable symbols |
| **4** | **Complex CFG** | `S -> a B D h`, `B -> c C`, `C -> b C \| ε`, `D -> E F`, `E -> g \| ε`, `F -> f \| ε` | Suffix nullable propagation & multi-symbol FOLLOW |
| **5** | **Classic Expression** | `E -> T E'`, `E' -> + T E' \| ε`, `T -> F T'`, `T' -> * F T' \| ε`, `F -> ( E ) \| id` | Standard compiler design arithmetic expressions |
| **6** | **Multiple Nullable** | `S -> A B C`, `A -> ε`, `B -> ε`, `C -> ε` | Pure nullable grammar propagation |
| **7** | **Terminal After Nullable** | `S -> A B c`, `A -> a \| ε`, `B -> b \| ε` | Trailing terminal FOLLOW propagation |
| **8** | **Indirect Dependency** | `S -> A`, `A -> B`, `B -> C`, `C -> d` | Multi-step fixed-point convergence |
| **9** | **Recursive Grammar** | `S -> A`, `A -> B \| a`, `B -> A \| b` | Mutual recursion loop termination |
| **10** | **Left Recursion** | `E -> E + T \| T`, `T -> T * F \| F`, `F -> id` | Left recursion warning + set derivation |
| **11** | **FIRST/FIRST Conflict** | `S -> a A \| a B`, `A -> c`, `B -> d` | Conflict detection on terminal `a` |
| **12** | **FIRST/FOLLOW Conflict** | `S -> A b`, `A -> b \| ε` | Conflict detection on terminal `b` |

---

## 📂 Project Structure

```text
├── index.html               # Main entry point (identical to LL1-Parser-Studio.html)
├── LL1-Parser-Studio.html   # Primary studio workbench interface
├── app.js                   # CFG parser, FIRST/FOLLOW engine, table builder & simulator
├── style.css                # Modern dark-mode UI stylesheet
├── README.md                # Documentation and usage guide
└── .gitignore               # Ignored test artifacts
```

---

## 📜 License

This project is licensed under the MIT License.
