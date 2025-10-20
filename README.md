# PCNF Converter

- **Author:** `Juan Carlos Muñoz Trejos`

## Versions Used

- **Operating System**: `Windows 11`
- **Programming Language**: `Python 3.10.12`

## Instrucciones de Ejecución

To run the solution, follow these steps:

1. **Clone or download the repository**, and make sure the file solucion.py is in your working directory.

2. **Open a terminal** or command line in that directory.

3. **Run the script using** the Python interpreter. The script includes predefined examples and will execute directly:

```bash
python solucion.py
```

4. **View the results:** The output will appear directly in the terminal, showing each original expression and its conversion to CNF using the two implemented methods.

## Explanation of the Solution

This implementation translates first-order logic formulas into Prenex Conjunctive Normal Form (PCNF) as defined in Ben-Ari (2012, Definition 9.9). The algorithm follows the standard logical transformation steps:

1. **Parsing:** The input string is parsed into an Abstract Syntax Tree (AST) according to the grammar:

F ::= a | x | (- F) | (F & F) | (F v F) | (F -> F) | (F <-> F) | (Ax F) | (Ex F)

a, b, c, ... represent constant symbols.

x, y, z, ... represent variable symbols.

A and E represent universal (∀) and existential (∃) quantifiers, respectively.

Logical Transformations:
Eliminate biconditionals (<->) using:
P↔Q≡(P→Q)∧(Q→P)
Eliminate implications (->) using:
P→Q≡¬P∨Q
Push negations inward using De Morgan’s laws and quantifier duality:
¬(P∧Q)≡¬P∨¬Q
¬(P∨Q)≡¬P∧¬Q
¬∀xP≡∃x¬P
¬∃xP≡∀x¬P
Standardize Variables: Rename bound variables to ensure all quantifiers use unique variable names, avoiding name clashes during prenex extraction.
Extract Quantifiers: Move all quantifiers to the front of the formula, maintaining their relative order and scope. This is valid after standardization and because the matrix is quantifier-free.
Convert Matrix to CNF:
Apply distributive law: P∨(Q∧R)≡(P∨Q)∧(P∨R)
Iterate until the quantifier-free part is in Conjunctive Normal Form (a conjunction of disjunctions of literals).
The final result is a formula in the form Q1x1Q2x2…Qnxn M , where M is in CNF.

## Reference Sources
Ben-Ari, M. (2012). Mathematical Logic for Computer Science (3rd ed.). Springer. Definition 9.9 (p. 172), Section 9.2.
Assignment specification: CM0845 Logic Assignment 2, Sergio Ramírez Rico, 2025.


## AIs

Qwen, Copilot