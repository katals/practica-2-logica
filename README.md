# PCNF Converter

- **Author:** `Juan Carlos Muñoz Trejos`

## Versions Used

- **Operating System**: `Windows 11`
- **Programming Language**: `Python 3.10.12`

## Execution Instructions

To run the solution, follow these steps:

1. **Clone or download the repository**, and make sure the file solucion.py is in your working directory.
2. **Open a terminal** or command line in that directory.
3. **Run the script using** the Python interpreter. The script includes predefined examples and will execute directly:

```bash
python solucion.py
```

4. **View the results:** The output will appear directly in the terminal, showing each original expression and its conversion to CNF using the implemented methods.

## General Explanation of the Code

This program takes first-order logic formulas and transforms them into Prenex Conjunctive Normal Form (PCNF), following the standard grammar and classical steps of mathematical logic.

The code is organized into functions that perform:
- **Parsing:** Converts the input expression into an abstract syntax tree (AST) according to the grammar.
- **Logical transformations:** Applies rules to eliminate biconditionals, implications, and push negations inward.
- **Variable standardization:** Renames bound variables to avoid collisions.
- **Quantifier extraction:** Moves all quantifiers to the prefix of the formula.
- **Conversion to CNF:** Applies the distributive law and transforms the matrix (quantifier-free part) into conjunctive normal form.

The result is an equivalent formula in PCNF, ready for further analysis or processing.

This solution converts first-order logic formulas to Prenex Conjunctive Normal Form (PCNF), following Ben-Ari (2012, Def. 9.9).

### 1. Grammar and Syntax

The input must follow the grammar:

```
F ::= a | x | (- F) | (F & F) | (F v F) | (F -> F) | (F <-> F) | (Ax F) | (Ex F)
```
- `a, b, c, ...` are constants (single lowercase letters)
- `x, y, z, ...` are variables (single lowercase letters)
- `A` and `E` are universal (∀) and existential (∃) quantifiers

**Note:** Names like `foo`, `bar`, `xy`, etc. are not allowed. Only single letters.

### 2. Algorithm Steps

The code performs the following steps on the formula:

#### a) Parsing (Syntax Analysis)
Converts the input string into an Abstract Syntax Tree (AST) according to the grammar.

#### b) Logical Transformations
- **Eliminate biconditionals (`<->`)**:  
  `(P <-> Q) ≡ (P -> Q) & (Q -> P)`
- **Eliminate implications (`->`)**:  
  `(P -> Q) ≡ (- P) v Q`
- **Push negations inward (De Morgan and quantifier duality)**:  
  `-(P & Q) ≡ (- P) v (- Q)`  
  `-(P v Q) ≡ (- P) & (- Q)`  
  `-∀x P ≡ ∃x -P`  
  `-∃x P ≡ ∀x -P`

#### c) Variable Standardization
Renames bound variables so that each quantifier uses a unique name, avoiding collisions.

#### d) Quantifier Extraction (Prenex)
Moves all quantifiers to the prefix of the formula, maintaining order and scope.

#### e) Matrix Conversion to CNF
- Applies the distributive law:  
  `P v (Q & R) ≡ (P v Q) & (P v R)`
- Iterates until the quantifier-free part (matrix) is in Conjunctive Normal Form (conjunction of disjunctions of literals).

### 3. Final Result

The output is a formula in the form:
```
Q1x1 Q2x2 ... Qnxn M
```
Where `Q` is a quantifier (`A` or `E`), `x` is a variable, and `M` is the matrix in CNF.

## References
- Ben-Ari, M. (2012). Mathematical Logic for Computer Science (3rd ed.). Springer. Definition 9.9 (p. 172), Section 9.2.
- Assignment specification: CM0845 Logic Assignment 2, Sergio Ramírez Rico, 2025.

## AIs used
- Qwen
- Copilot
