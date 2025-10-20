import copy
import re

class Nodo:
    """Representa un nodo en el Árbol de Sintaxis Abstracta (AST)."""
    def __init__(self, valor, izquierdo=None, derecho=None, variable=None):
        self.valor = valor
        self.izquierdo = izquierdo
        self.derecho = derecho
        self.variable = variable  # Solo usado para cuantificadores ('A' o 'E')

    def __repr__(self):
        if self.valor in ('A', 'E'):
            return f"Nodo(valor='{self.valor}', variable='{self.variable}')"
        return f"Nodo(valor='{self.valor}')"

def construir_ast_desde_expresion(expresion: str) -> Nodo:
    """
    Construye un AST a partir de una fórmula de primer orden según la gramática dada.
    
    Gramática: F ::= a | x | (- F) | (F & F) | (F v F) | (F -> F) | (F <-> F) | (Ax F) | (Ex F)
    
    Restricciones importantes:
    - Los átomos son LETRAS INDIVIDUALES minúsculas (a, b, c, ..., x, y, z)
    - NO existen proposiciones, solo constantes y variables
    - Las variables en cuantificadores son LETRAS INDIVIDUALES (Ax, Ay, NO Axy)
    """
    expresion = expresion.strip()

    # Elimina paréntesis externos que envuelven toda la expresión
    if expresion.startswith('(') and expresion.endswith(')'):
        nivel = 0
        es_envoltorio = True
        for i, char in enumerate(expresion[1:-1], 1):
            if char == '(':
                nivel += 1
            elif char == ')':
                nivel -= 1
                if nivel < 0:
                    es_envoltorio = False
                    break
        if es_envoltorio and nivel == 0:
            return construir_ast_desde_expresion(expresion[1:-1])

    # Detectar cuantificadores: (A var ...) o (E var ...)
    # Variable debe ser una sola letra minúscula
    match_quant = re.match(r'^([AE])([a-z])\s+(.+)$', expresion)
    if match_quant:
        cuantificador = match_quant.group(1)
        var = match_quant.group(2)
        cuerpo = match_quant.group(3)
        return Nodo(valor=cuantificador, derecho=construir_ast_desde_expresion(cuerpo), variable=var)

    # Búsqueda de operadores binarios por precedencia (de menor a mayor)
    operadores_por_precedencia = [['<->'], ['->'], ['v'], ['&']]
    for grupo_ops in operadores_por_precedencia:
        nivel = 0
        # Recorremos de derecha a izquierda para asociatividad correcta
        for i in range(len(expresion) - 1, -1, -1):
            char = expresion[i]
            if char == ')':
                nivel += 1
            elif char == '(':
                nivel -= 1
            if nivel == 0:
                for op in grupo_ops:
                    if expresion.startswith(op, i):
                        return Nodo(
                            valor=op,
                            izquierdo=construir_ast_desde_expresion(expresion[:i]),
                            derecho=construir_ast_desde_expresion(expresion[i + len(op):])
                        )

    # Negación unaria: (- F)
    if expresion.startswith('- '):
        return Nodo(valor='-', derecho=construir_ast_desde_expresion(expresion[2:]))

    # Caso base: átomo - solo letras individuales minúsculas (constantes o variables)
    # No existen "proposiciones", solo constantes y variables
    if re.fullmatch(r'[a-z]', expresion):
        return Nodo(expresion)

    raise ValueError(f"Expresión no válida: {expresion}")

def ast_a_cadena(nodo: Nodo) -> str:
    """Convierte un AST a su representación en cadena."""
    if nodo is None:
        return ""
    if nodo.izquierdo is None and nodo.derecho is None:
        return nodo.valor
    if nodo.valor in ('A', 'E'):
        cuerpo = ast_a_cadena(nodo.derecho)
        return f"({nodo.valor}{nodo.variable} {cuerpo})"
    if nodo.valor == '-':
        der = ast_a_cadena(nodo.derecho)
        return f"(- {der})"
    izq = ast_a_cadena(nodo.izquierdo)
    der = ast_a_cadena(nodo.derecho)
    return f"({izq} {nodo.valor} {der})"

# --- Transformaciones proposicionales (matriz) ---

def eliminar_bicondicionales(nodo: Nodo) -> Nodo:
    if nodo is None: return None
    if nodo.valor in ('A', 'E'):
        nodo.derecho = eliminar_bicondicionales(nodo.derecho)
        return nodo
    nodo.izquierdo = eliminar_bicondicionales(nodo.izquierdo)
    nodo.derecho = eliminar_bicondicionales(nodo.derecho)
    if nodo.valor == '<->':
        p, q = nodo.izquierdo, nodo.derecho
        imp1 = Nodo('->', p, q)
        imp2 = Nodo('->', q, p)
        return Nodo('&', imp1, imp2)
    return nodo

def eliminar_implicaciones(nodo: Nodo) -> Nodo:
    if nodo is None: return None
    if nodo.valor in ('A', 'E'):
        nodo.derecho = eliminar_implicaciones(nodo.derecho)
        return nodo
    nodo.izquierdo = eliminar_implicaciones(nodo.izquierdo)
    nodo.derecho = eliminar_implicaciones(nodo.derecho)
    if nodo.valor == '->':
        p, q = nodo.izquierdo, nodo.derecho
        neg_p = Nodo('-', derecho=p)
        return Nodo('v', neg_p, q)
    return nodo

def adentrar_negaciones_demorgan(nodo: Nodo) -> Nodo:
    if nodo is None: return None
    if nodo.valor in ('A', 'E'):
        nodo.derecho = adentrar_negaciones_demorgan(nodo.derecho)
        return nodo
    if nodo.valor == '-':
        hijo = nodo.derecho
        if hijo.valor == '-':
            return adentrar_negaciones_demorgan(hijo.derecho)
        if hijo.valor == '&':
            nuevo_izq = adentrar_negaciones_demorgan(Nodo('-', derecho=hijo.izquierdo))
            nuevo_der = adentrar_negaciones_demorgan(Nodo('-', derecho=hijo.derecho))
            return Nodo('v', nuevo_izq, nuevo_der)
        if hijo.valor == 'v':
            nuevo_izq = adentrar_negaciones_demorgan(Nodo('-', derecho=hijo.izquierdo))
            nuevo_der = adentrar_negaciones_demorgan(Nodo('-', derecho=hijo.derecho))
            return Nodo('&', nuevo_izq, nuevo_der)
        if hijo.valor == 'A':  # -∀x P ≡ ∃x -P
            nuevo_der = adentrar_negaciones_demorgan(Nodo('-', derecho=hijo.derecho))
            return Nodo('E', derecho=nuevo_der, variable=hijo.variable)
        if hijo.valor == 'E':  # -∃x P ≡ ∀x -P
            nuevo_der = adentrar_negaciones_demorgan(Nodo('-', derecho=hijo.derecho))
            return Nodo('A', derecho=nuevo_der, variable=hijo.variable)
    nodo.izquierdo = adentrar_negaciones_demorgan(nodo.izquierdo)
    nodo.derecho = adentrar_negaciones_demorgan(nodo.derecho)
    return nodo

def distribuir_disyuncion_sobre_conjuncion(nodo: Nodo) -> Nodo:
    if nodo is None: return None
    if nodo.valor in ('A', 'E'):
        nodo.derecho = distribuir_disyuncion_sobre_conjuncion(nodo.derecho)
        return nodo
    nodo.izquierdo = distribuir_disyuncion_sobre_conjuncion(nodo.izquierdo)
    nodo.derecho = distribuir_disyuncion_sobre_conjuncion(nodo.derecho)
    if nodo.valor == 'v':
        izq, der = nodo.izquierdo, nodo.derecho
        if der.valor == '&':
            b, c = der.izquierdo, der.derecho
            nuevo_izq = distribuir_disyuncion_sobre_conjuncion(Nodo('v', izq, b))
            nuevo_der = distribuir_disyuncion_sobre_conjuncion(Nodo('v', izq, c))
            return Nodo('&', nuevo_izq, nuevo_der)
        if izq.valor == '&':
            a, b = izq.izquierdo, izq.derecho
            nuevo_izq = distribuir_disyuncion_sobre_conjuncion(Nodo('v', a, der))
            nuevo_der = distribuir_disyuncion_sobre_conjuncion(Nodo('v', b, der))
            return Nodo('&', nuevo_izq, nuevo_der)
    return nodo

def convertir_matriz_a_cnf(nodo: Nodo) -> Nodo:
    """Convierte la parte cuantificador-libre a CNF, iterando hasta convergencia."""
    def nodos_iguales(a: Nodo, b: Nodo) -> bool:
        if a is None and b is None:
            return True
        if a is None or b is None:
            return False
        if a.valor != b.valor:
            return False
        if a.valor in ('A', 'E') and a.variable != b.variable:
            return False
        return nodos_iguales(a.izquierdo, b.izquierdo) and nodos_iguales(a.derecho, b.derecho)
    
    max_iteraciones = 100
    for _ in range(max_iteraciones):
        anterior = nodo
        nodo = distribuir_disyuncion_sobre_conjuncion(nodo)
        if nodos_iguales(anterior, nodo):
            break
    return nodo

# --- Manejo de cuantificadores ---

def recolectar_variables_libres(nodo: Nodo, ligadas: set) -> set:
    if nodo is None:
        return set()
    if nodo.valor in ('A', 'E'):
        nuevas_ligadas = ligadas | {nodo.variable}
        return recolectar_variables_libres(nodo.derecho, nuevas_ligadas)
    if nodo.izquierdo is None and nodo.derecho is None:
        # Átomo: si es una variable y no está ligada, es libre
        if nodo.valor in ligadas:
            return set()
        else:
            # Solo consideramos variables (letras individuales como x, y, z)
            # En esta gramática, los átomos pueden ser constantes o variables
            # Pero en PCNF (cerrada), no debería haber libres. Así que lo dejamos simple.
            return {nodo.valor} if len(nodo.valor) == 1 and nodo.valor.islower() else set()
    libres = set()
    libres |= recolectar_variables_libres(nodo.izquierdo, ligadas)
    libres |= recolectar_variables_libres(nodo.derecho, ligadas)
    return libres

def renombrar_variable(nodo: Nodo, vieja: str, nueva: str, ligadas: set) -> Nodo:
    if nodo is None:
        return None
    if nodo.valor in ('A', 'E'):
        nueva_ligada = nodo.variable == vieja
        nuevas_ligadas = ligadas | {nodo.variable}
        nuevo_derecho = renombrar_variable(nodo.derecho, vieja, nueva, nuevas_ligadas)
        if nueva_ligada:
            return Nodo(nodo.valor, derecho=nuevo_derecho, variable=nueva)
        else:
            return Nodo(nodo.valor, derecho=nuevo_derecho, variable=nodo.variable)
    # Renombrar en átomos si es una variable (letra única)
    if nodo.izquierdo is None and nodo.derecho is None:
        if nodo.valor == vieja and len(vieja) == 1:
            return Nodo(nueva)
    nuevo_izq = renombrar_variable(nodo.izquierdo, vieja, nueva, ligadas)
    nuevo_der = renombrar_variable(nodo.derecho, vieja, nueva, ligadas)
    return Nodo(nodo.valor, nuevo_izq, nuevo_der)

def estandarizar_variables(nodo: Nodo, usadas: set = None) -> Nodo:
    if usadas is None:
        usadas = set()
    if nodo is None:
        return None
    if nodo.valor in ('A', 'E'):
        var = nodo.variable
        nueva_var = var
        contador = 0
        while nueva_var in usadas:
            nueva_var = var + str(contador)
            contador += 1
        nuevas_usadas = usadas | {nueva_var}
        nuevo_derecho = estandarizar_variables(nodo.derecho, nuevas_usadas)
        if nueva_var != var:
            nuevo_derecho = renombrar_variable(nuevo_derecho, var, nueva_var, {var})
        return Nodo(nodo.valor, derecho=nuevo_derecho, variable=nueva_var)
    nuevo_izq = estandarizar_variables(nodo.izquierdo, usadas)
    nuevo_der = estandarizar_variables(nodo.derecho, usadas)
    return Nodo(nodo.valor, nuevo_izq, nuevo_der)

def extraer_cuantificadores(nodo: Nodo):
    if nodo is None:
        return [], None
    if nodo.valor in ('A', 'E'):
        cuants, matriz = extraer_cuantificadores(nodo.derecho)
        return [(nodo.valor, nodo.variable)] + cuants, matriz
    if nodo.valor in ('&', 'v'):
        c1, m1 = extraer_cuantificadores(nodo.izquierdo)
        c2, m2 = extraer_cuantificadores(nodo.derecho)
        return c1 + c2, Nodo(nodo.valor, m1, m2)
    if nodo.valor == '-':
        c, m = extraer_cuantificadores(nodo.derecho)
        return c, Nodo('-', derecho=m)
    return [], nodo

def construir_pcnf(cuantificadores, matriz):
    nodo = matriz
    for q_type, var in reversed(cuantificadores):
        nodo = Nodo(valor=q_type, derecho=nodo, variable=var)
    return nodo

def convertir_a_pcnf(nodo_raiz: Nodo) -> Nodo:
    ast = eliminar_bicondicionales(nodo_raiz)
    ast = eliminar_implicaciones(ast)
    ast = adentrar_negaciones_demorgan(ast)
    ast = estandarizar_variables(ast)
    cuants, matriz = extraer_cuantificadores(ast)
    if matriz is None:
        matriz = Nodo('a')
    matriz_cnf = convertir_matriz_a_cnf(matriz)
    return construir_pcnf(cuants, matriz_cnf)

# --- Ejecución de ejemplo ---

if __name__ == "__main__":
    # Casos de prueba según la gramática correcta:
    # - Solo letras individuales como átomos (constantes/variables)
    # - Variables en cuantificadores son letras individuales
    expresiones = [
        "(Ay (a v b))",           # Variable y, constantes a, b
        "(Ex (p v q))",           # Variable x, constantes p, q
        "(Ax (Ey (r & (- s))))",  # Variables x, y; constantes r, s
        "((Az p) v (Ew q))",      # Variables z, w; constantes p, q
        # Casos con transformaciones
        "(Ax (p -> q))",          # Implicación
        "(Ay ((p v q) <-> r))",   # Bicondicional
        # Casos con De Morgan
        "(Ex (- (a & b)))",       # Debe convertir a (Ex ((- a) v (- b)))
        "(Ay (- (c v d)))",       # Debe convertir a (Ay ((- c) & (- d)))
    ]
    
    for expr in expresiones:
        try:
            print(f"===========================================================")
            print(f"Expresión Original: {expr}\n")
            ast_original = construir_ast_desde_expresion(expr)
            ast_para_pcnf = copy.deepcopy(ast_original)
            pcnf_ast = convertir_a_pcnf(ast_para_pcnf)
            pcnf_str = ast_a_cadena(pcnf_ast)
            print(f"PCNF: {pcnf_str}\n")
        except Exception as e:
            print(f"Error procesando '{expr}': {e}\n")