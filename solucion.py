import copy
import re

class Node:
    """Represents a node in the Abstract Syntax Tree (AST) for first-order logic."""
    def __init__(self, value, left=None, right=None, variable=None):
        self.value = value
        self.left = left
        self.right = right
        self.variable = variable  # Only used for quantifiers ('A' or 'E')

    def __repr__(self):
        if self.value in ('A', 'E'):
            return f"Node(value='{self.value}', variable='{self.variable}')"
        return f"Node(value='{self.value}')"

def build_ast_from_expression(expression: str) -> Node:
    """
    Builds an AST from a first-order logic formula string.
    Grammar: F ::= a | x | (- F) | (F & F) | (F v F) | (F -> F) | (F <-> F) | (Ax F) | (Ex F)
    Only single lowercase letters are allowed for constants and variables.
    """
    expression = expression.strip()

    # Remove outer parentheses
    if expression.startswith('(') and expression.endswith(')'):
        level = 0
        is_wrapper = True
        for i, char in enumerate(expression[1:-1], 1):
            if char == '(': level += 1
            elif char == ')':
                level -= 1
                if level < 0:
                    is_wrapper = False
                    break
        if is_wrapper and level == 0:
            return build_ast_from_expression(expression[1:-1])

    # Detect quantifiers: (A var ...) or (E var ...)
    match_quant = re.match(r'^([AE])([a-z])\s+(.+)$', expression)
    if match_quant:
        quantifier = match_quant.group(1)
        var = match_quant.group(2)
        body = match_quant.group(3)
        return Node(value=quantifier, right=build_ast_from_expression(body), variable=var)

    # Binary operators by precedence
    operators_by_precedence = [['<->'], ['->'], ['v'], ['&']]
    for ops in operators_by_precedence:
        level = 0
        # Right-to-left for correct associativity
        for i in range(len(expression) - 1, -1, -1):
            char = expression[i]
            if char == ')': level += 1
            elif char == '(': level -= 1
            if level == 0:
                for op in ops:
                    if expression.startswith(op, i):
                        return Node(
                            value=op,
                            left=build_ast_from_expression(expression[:i]),
                            right=build_ast_from_expression(expression[i + len(op):])
                        )

    # Unary negation: (- F)
    if expression.startswith('- '):
        return Node(value='-', right=build_ast_from_expression(expression[2:]))

    # Base case: atom (single lowercase letter)
    if re.fullmatch(r'[a-z]', expression):
        return Node(expression)

    raise ValueError(f"Invalid expression: {expression}")

def ast_to_string(node) -> str:
    """Converts an AST to its string representation."""
    if node is None:
        return ""
    if getattr(node, 'left', None) is None and getattr(node, 'right', None) is None:
        return node.value
    if node.value in ('A', 'E'):
        body = ast_to_string(getattr(node, 'right', None))
        return f"({node.value}{node.variable} {body})"
    if node.value == '-':
        right = ast_to_string(getattr(node, 'right', None))
        return f"(- {right})"
    left = ast_to_string(getattr(node, 'left', None))
    right = ast_to_string(getattr(node, 'right', None))
    return f"({left} {node.value} {right})"

# --- Transformaciones proposicionales (matriz) ---

def remove_biconditionals(node):
    if node is None: return None
    if node.value in ('A', 'E'):
        if node.right is not None:
            node.right = remove_biconditionals(node.right)
        return node
    if node.left is not None:
        node.left = remove_biconditionals(node.left)
    if node.right is not None:
        node.right = remove_biconditionals(node.right)
    if node.value == '<->':
        p, q = node.left, node.right
        imp1 = Node('->', p, q)
        imp2 = Node('->', q, p)
        return Node('&', imp1, imp2)
    return node

def remove_implications(node):
    if node is None: return None
    if node.value in ('A', 'E'):
        if node.right is not None:
            node.right = remove_implications(node.right)
        return node
    if node.left is not None:
        node.left = remove_implications(node.left)
    if node.right is not None:
        node.right = remove_implications(node.right)
    if node.value == '->':
        p, q = node.left, node.right
        neg_p = Node('-', right=p)
        return Node('v', neg_p, q)
    return node

def push_negations_demorgan(node):
    if node is None: return None
    if node.value in ('A', 'E'):
        if node.right is not None:
            node.right = push_negations_demorgan(node.right)
        return node
    if node.value == '-':
        child = node.right
        if child is not None and getattr(child, 'value', None) == '-':
            return push_negations_demorgan(child.right)
        if child is not None and getattr(child, 'value', None) == '&':
            new_left = push_negations_demorgan(Node('-', right=getattr(child, 'left', None)))
            new_right = push_negations_demorgan(Node('-', right=getattr(child, 'right', None)))
            return Node('v', new_left, new_right)
        if child is not None and getattr(child, 'value', None) == 'v':
            new_left = push_negations_demorgan(Node('-', right=getattr(child, 'left', None)))
            new_right = push_negations_demorgan(Node('-', right=getattr(child, 'right', None)))
            return Node('&', new_left, new_right)
        if child is not None and getattr(child, 'value', None) == 'A':  # -∀x P ≡ ∃x -P
            new_right = push_negations_demorgan(Node('-', right=getattr(child, 'right', None)))
            return Node('E', right=new_right, variable=getattr(child, 'variable', None))
        if child is not None and getattr(child, 'value', None) == 'E':  # -∃x P ≡ ∀x -P
            new_right = push_negations_demorgan(Node('-', right=getattr(child, 'right', None)))
            return Node('A', right=new_right, variable=getattr(child, 'variable', None))
    if node.left is not None:
        node.left = push_negations_demorgan(node.left)
    if node.right is not None:
        node.right = push_negations_demorgan(node.right)
    return node

def distribute_or_over_and(node):
    if node is None: return None
    if node.value in ('A', 'E'):
        if node.right is not None:
            node.right = distribute_or_over_and(node.right)
        return node
    if node.left is not None:
        node.left = distribute_or_over_and(node.left)
    if node.right is not None:
        node.right = distribute_or_over_and(node.right)
    if node.value == 'v':
        left, right = node.left, node.right
        if right is not None and getattr(right, 'value', None) == '&':
            b, c = right.left, right.right
            new_left = distribute_or_over_and(Node('v', left, b))
            new_right = distribute_or_over_and(Node('v', left, c))
            return Node('&', new_left, new_right)
        if left is not None and getattr(left, 'value', None) == '&':
            a, b = left.left, left.right
            new_left = distribute_or_over_and(Node('v', a, right))
            new_right = distribute_or_over_and(Node('v', b, right))
            return Node('&', new_left, new_right)
    return node

def convert_matrix_to_cnf(node):
    """Converts the quantifier-free part to CNF, iterating until convergence."""
    def nodes_equal(a, b):
        if a is None and b is None:
            return True
        if a is None or b is None:
            return False
        if getattr(a, 'value', None) != getattr(b, 'value', None):
            return False
        if getattr(a, 'value', None) in ('A', 'E') and getattr(a, 'variable', None) != getattr(b, 'variable', None):
            return False
        return nodes_equal(getattr(a, 'left', None), getattr(b, 'left', None)) and nodes_equal(getattr(a, 'right', None), getattr(b, 'right', None))
    max_iterations = 100
    for _ in range(max_iterations):
        previous = node
        node = distribute_or_over_and(node)
        if nodes_equal(previous, node):
            break
    return node

# --- Manejo de cuantificadores ---

def collect_free_variables(node, bound: set) -> set:
    if node is None:
        return set()
    if getattr(node, 'value', None) in ('A', 'E'):
        new_bound = bound | {getattr(node, 'variable', None)}
        return collect_free_variables(getattr(node, 'right', None), new_bound)
    if getattr(node, 'left', None) is None and getattr(node, 'right', None) is None:
        if getattr(node, 'value', None) in bound:
            return set()
        else:
            v = getattr(node, 'value', None)
            return {v} if v and len(v) == 1 and v.islower() else set()
    free = set()
    free |= collect_free_variables(getattr(node, 'left', None), bound)
    free |= collect_free_variables(getattr(node, 'right', None), bound)
    return free

def standardize_variables(node, used=None):
    if used is None:
        used = set()
    if node is None:
        return None
    if getattr(node, 'value', None) in ('A', 'E'):
        var = getattr(node, 'variable', None)
        new_var = var if var is not None else 'v'
        count = 0
        while new_var in used:
            if var is not None:
                new_var = var + str(count)
            else:
                new_var = 'v' + str(count)
            count += 1
        new_used = used | {new_var}
        new_right = standardize_variables(getattr(node, 'right', None), new_used)
        if new_var != var and var is not None:
            new_right = rename_variable(new_right, var, new_var, {var})
        return Node(getattr(node, 'value', None), right=new_right, variable=new_var)
    new_left = standardize_variables(getattr(node, 'left', None), used)
    new_right = standardize_variables(getattr(node, 'right', None), used)
    return Node(getattr(node, 'value', None), new_left, new_right)

def rename_variable(node, old, new, bound):
    if node is None:
        return None
    if getattr(node, 'value', None) in ('A', 'E'):
        var = getattr(node, 'variable', None)
        is_bound = var == old if var is not None and old is not None else False
        new_bound = bound | {var} if var is not None else bound
        new_right = rename_variable(getattr(node, 'right', None), old, new, new_bound)
        if is_bound:
            return Node(getattr(node, 'value', None), right=new_right, variable=new)
        else:
            return Node(getattr(node, 'value', None), right=new_right, variable=var)
    if getattr(node, 'left', None) is None and getattr(node, 'right', None) is None:
        v = getattr(node, 'value', None)
        if v == old and old is not None and len(str(old)) == 1:
            return Node(new)
    new_left = rename_variable(getattr(node, 'left', None), old, new, bound)
    new_right = rename_variable(getattr(node, 'right', None), old, new, bound)
    return Node(getattr(node, 'value', None), new_left, new_right)

def extract_quantifiers(node):
    if node is None:
        return [], None
    if getattr(node, 'value', None) in ('A', 'E'):
        quants, matrix = extract_quantifiers(getattr(node, 'right', None))
        return [(getattr(node, 'value', None), getattr(node, 'variable', None))] + quants, matrix
    if getattr(node, 'value', None) in ('&', 'v'):
        c1, m1 = extract_quantifiers(getattr(node, 'left', None))
        c2, m2 = extract_quantifiers(getattr(node, 'right', None))
        return c1 + c2, Node(getattr(node, 'value', None), m1, m2)
    if getattr(node, 'value', None) == '-':
        c, m = extract_quantifiers(getattr(node, 'right', None))
        return c, Node('-', right=m)
    return [], node

def build_pcnf(quantifiers, matrix):
    node = matrix
    for q_type, var in reversed(quantifiers):
        node = Node(value=q_type, right=node, variable=var)
    return node

def convert_to_pcnf(root: Node) -> Node:
    ast = remove_biconditionals(root)
    ast = remove_implications(ast)
    ast = push_negations_demorgan(ast)
    ast = standardize_variables(ast)
    quants, matrix = extract_quantifiers(ast)
    if matrix is None:
        matrix = Node('a')
    matrix_cnf = convert_matrix_to_cnf(matrix)
    return build_pcnf(quants, matrix_cnf)

# --- Ejecución de ejemplo ---

if __name__ == "__main__":
    # Test cases according to correct grammar:
    expressions = [
        "(Ay (a v b))",           # Variable y, constants a, b
        "(Ex (p v q))",           # Variable x, constants p, q
        "(Ax (Ey (r & (- s))))",  # Variables x, y; constants r, s
        "((Az p) v (Ew q))",      # Variables z, w; constants p, q
        # Transformations
        "(Ax (p -> q))",          # Implication
        "(Ay ((p v q) <-> r))",   # Biconditional
        # De Morgan cases
        "(Ex (- (a & b)))",       # Should convert to (Ex ((- a) v (- b)))
        "(Ay (- (c v d)))",       # Should convert to (Ay ((- c) & (- d)))
    ]
    for expr in expressions:
        try:
            print(f"===========================================================")
            print(f"Original Expression: {expr}\n")
            ast_original = build_ast_from_expression(expr)
            ast_for_pcnf = copy.deepcopy(ast_original)
            pcnf_ast = convert_to_pcnf(ast_for_pcnf)
            pcnf_str = ast_to_string(pcnf_ast)
            print(f"PCNF: {pcnf_str}\n")
        except Exception as e:
            print(f"Error processing '{expr}': {e}\n")