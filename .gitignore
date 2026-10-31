import itertools
import re

import pandas as pd
import streamlit as st

# ============================================================
# MOTOR LÓGICO (parser propio, sin eval)
# Precedencia: ¬ > ∧ > ∨ > ⊕ > → > ↔
# ============================================================
import itertools
import re

TOKENS = [
    ("IFF", r"<->|<=>|↔"),
    ("IMP", r"->|=>|→"),
    ("XOR", r"⊕|\bXOR\b"),
    ("AND", r"∧|&&|&|\bAND\b"),
    ("OR", r"∨|\|\||\||\bOR\b"),
    ("NOT", r"¬|~|!|\bNOT\b"),
    ("LP", r"\("),
    ("RP", r"\)"),
    ("CONST", r"\b[01]\b"),
    ("VAR", r"[A-Za-z_][A-Za-z0-9_]*"),
    ("WS", r"\s+"),
]
REGEX = re.compile("|".join(f"(?P<{n}>{p})" for n, p in TOKENS), re.IGNORECASE)

SIMBOLO = {"and": "∧", "or": "∨", "xor": "⊕", "imp": "→", "iff": "↔"}
TIPO = {"AND": "and", "OR": "or", "XOR": "xor", "IMP": "imp", "IFF": "iff"}


class ErrorSintaxis(Exception):
    pass


def tokenizar(texto):
    pos, out = 0, []
    while pos < len(texto):
        m = REGEX.match(texto, pos)
        if not m:
            raise ErrorSintaxis(f"Carácter no reconocido: '{texto[pos]}' (posición {pos + 1})")
        pos = m.end()
        if m.lastgroup != "WS":
            out.append((m.lastgroup, m.group()))
    return out


class Parser:
    """Precedencia (mayor a menor): ¬  >  ∧  >  ∨  >  ⊕  >  →  >  ↔"""

    def __init__(self, tokens):
        self.t, self.i = tokens, 0

    def _ver(self):
        return self.t[self.i][0] if self.i < len(self.t) else None

    def _tomar(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def parsear(self):
        if not self.t:
            raise ErrorSintaxis("La expresión está vacía.")
        nodo = self._iff()
        if self.i < len(self.t):
            raise ErrorSintaxis(f"Símbolo inesperado: '{self.t[self.i][1]}'")
        return nodo

    def _iff(self):
        izq = self._imp()
        while self._ver() == "IFF":
            self._tomar()
            izq = ("iff", izq, self._imp())
        return izq

    def _imp(self):  # asociativa a la derecha
        izq = self._xor()
        if self._ver() == "IMP":
            self._tomar()
            return ("imp", izq, self._imp())
        return izq

    def _xor(self):
        izq = self._or()
        while self._ver() == "XOR":
            self._tomar()
            izq = ("xor", izq, self._or())
        return izq

    def _or(self):
        izq = self._and()
        while self._ver() == "OR":
            self._tomar()
            izq = ("or", izq, self._and())
        return izq

    def _and(self):
        izq = self._not()
        while self._ver() == "AND":
            self._tomar()
            izq = ("and", izq, self._not())
        return izq

    def _not(self):
        if self._ver() == "NOT":
            self._tomar()
            return ("not", self._not())
        return self._atomo()

    def _atomo(self):
        v = self._ver()
        if v == "VAR":
            return ("var", self._tomar()[1])
        if v == "CONST":
            return ("const", self._tomar()[1] == "1")
        if v == "LP":
            self._tomar()
            nodo = self._iff()
            if self._ver() != "RP":
                raise ErrorSintaxis("Falta cerrar un paréntesis ')'.")
            self._tomar()
            return nodo
        if v is None:
            raise ErrorSintaxis("La expresión termina de forma inesperada.")
        raise ErrorSintaxis(f"Símbolo inesperado: '{self.t[self.i][1]}'")


def parsear(texto):
    return Parser(tokenizar(texto)).parsear()


def variables(nodo, acc=None):
    """Variables en orden de aparición."""
    acc = [] if acc is None else acc
    if nodo[0] == "var":
        if nodo[1] not in acc:
            acc.append(nodo[1])
    elif nodo[0] != "const":
        for hijo in nodo[1:]:
            variables(hijo, acc)
    return acc


def evaluar(nodo, env):
    k = nodo[0]
    if k == "var":
        return env[nodo[1]]
    if k == "const":
        return nodo[1]
    if k == "not":
        return not evaluar(nodo[1], env)
    a, b = evaluar(nodo[1], env), evaluar(nodo[2], env)
    return {
        "and": a and b,
        "or": a or b,
        "xor": a != b,
        "imp": (not a) or b,
        "iff": a == b,
    }[k]


def a_texto(nodo, raiz=True):
    k = nodo[0]
    if k == "var":
        return nodo[1]
    if k == "const":
        return "1" if nodo[1] else "0"
    if k == "not":
        return "¬" + a_texto(nodo[1], False)
    s = f"{a_texto(nodo[1], False)} {SIMBOLO[k]} {a_texto(nodo[2], False)}"
    return s if raiz else f"({s})"


def subexpresiones(nodo, acc=None):
    """Subexpresiones no triviales, de adentro hacia afuera, sin repetir."""
    acc = [] if acc is None else acc
    if nodo[0] in ("var", "const"):
        return acc
    for hijo in nodo[1:]:
        subexpresiones(hijo, acc)
    if nodo not in acc:
        acc.append(nodo)
    return acc


def tabla_de_verdad(texto, max_vars=6, paso_a_paso=True):
    """Devuelve (filas, columnas, clasificación). Cada fila es lista de bools."""
    arbol = parsear(texto)
    vs = variables(arbol)
    if len(vs) > max_vars:
        raise ErrorSintaxis(f"Máximo {max_vars} variables (tienes {len(vs)}).")
    subs = subexpresiones(arbol) if paso_a_paso else [arbol]
    if arbol not in subs:  # expresión que es solo una variable o constante
        subs.append(arbol)
    columnas = vs + [a_texto(s) for s in subs]
    filas = []
    for valores in itertools.product([True, False], repeat=len(vs)):
        env = dict(zip(vs, valores))
        filas.append(list(valores) + [evaluar(s, env) for s in subs])
    resultado = [f[-1] for f in filas]
    if all(resultado):
        clase = "tautología"
    elif not any(resultado):
        clase = "contradicción"
    else:
        clase = "contingencia"
    return filas, columnas, clase


# ============================================================
# CONFIGURACIÓN
# ============================================================
st.set_page_config(page_title="Calculadora Tabla de la Verdad", page_icon="🧮", layout="centered")

st.title("🧮 Calculadora de Tabla de la Verdad")
st.markdown("Construye tu expresión haciendo clic. El resultado se muestra en **0 y 1**.")

# ============================================================
# ESTADO DE LA SESIÓN
# ============================================================
if "expr" not in st.session_state:
    st.session_state.expr = ""


def agregar(texto):
    st.session_state.expr += texto


def limpiar():
    st.session_state.expr = ""


def borrar_ultimo():
    st.session_state.expr = st.session_state.expr.rstrip()[:-1]


def cargar(texto):
    st.session_state.expr = texto


# ============================================================
# CONSTRUCTOR DE EXPRESIÓN
# ============================================================
st.subheader("🛠️ Constructor de Expresión")

st.markdown("**Variables:**")
cols = st.columns(6)
for i, v in enumerate(["p", "q", "r", "s", "t", "u"]):
    cols[i].button(v, key=f"btn_{v}", use_container_width=True, on_click=agregar, args=(f" {v} ",))

st.markdown("**Operadores:**")
cols = st.columns(6)
for i, (simbolo, nombre) in enumerate(
    [("∧", "AND"), ("∨", "OR"), ("¬", "NOT"), ("⊕", "XOR"), ("→", "IMPLIES"), ("↔", "IFF")]
):
    cols[i].button(simbolo, key=f"btn_{nombre}", use_container_width=True, help=nombre,
                   on_click=agregar, args=(f" {simbolo} ",))

c1, c2, c3, c4 = st.columns(4)
c1.button("(", use_container_width=True, on_click=agregar, args=("(",))
c2.button(")", use_container_width=True, on_click=agregar, args=(")",))
c3.button("🗑️ Limpiar Todo", use_container_width=True, on_click=limpiar)
c4.button("⌫ Borrar Último", use_container_width=True, on_click=borrar_ultimo)

st.markdown("---")
st.markdown("**Expresión actual:**")
st.code(st.session_state.expr.strip() or "(vacío)", language="text")

# ============================================================
# EJEMPLOS
# ============================================================
st.markdown("**Ejemplos rápidos:**")
ejemplos = {
    "p ∧ q": "Conjunción simple",
    "p ∨ q": "Disyunción simple",
    "p ⊕ q": "XOR",
    "p → q": "Condicional",
    "p ↔ q": "Bicondicional",
    "¬p": "Negación",
    "(p → q) ↔ (¬q → ¬p)": "Ley contrarrecíproca",
    "p ∨ ¬p": "Tautología",
    "p ∧ ¬p": "Contradicción",
}
cols = st.columns(3)
for i, (expr, desc) in enumerate(ejemplos.items()):
    cols[i % 3].button(expr, key=f"ejemplo_{i}", help=desc, use_container_width=True,
                       on_click=cargar, args=(expr,))

mostrar_pasos = st.checkbox("Mostrar subexpresiones paso a paso", value=False)
st.markdown("---")

# ============================================================
# GENERAR TABLA
# ============================================================
if st.button("🚀 Generar Tabla", type="primary", use_container_width=True):
    if not st.session_state.expr.strip():
        st.warning("⚠️ Ingresa o construye una expresión primero.")
    else:
        try:
            filas, columnas, clase = tabla_de_verdad(st.session_state.expr, paso_a_paso=mostrar_pasos)
        except ErrorSintaxis as e:
            st.error(f"❌ {e}")
            st.info("Revisa operadores faltantes, paréntesis balanceados y que cada operador tenga sus dos operandos.")
        else:
            df = pd.DataFrame([[int(x) for x in fila] for fila in filas], columns=columnas)
            resultados = df.iloc[:, -1].tolist()

            n_vars = len(variables(parsear(st.session_state.expr)))
            st.success(f"✅ Tabla generada para {n_vars} variable(s) - {len(filas)} filas")

            if clase == "tautología":
                st.info("📊 **Tipo: TAUTOLOGÍA** (siempre verdadera)")
            elif clase == "contradicción":
                st.error("📊 **Tipo: CONTRADICCIÓN** (siempre falsa)")
            else:
                st.info("📊 **Tipo: CONTINGENCIA** (depende de los valores)")

            st.dataframe(df, use_container_width=True, hide_index=True)

            m1, m2, m3 = st.columns(3)
            m1.metric("Total de filas", len(filas))
            m2.metric("Verdaderos (1)", sum(resultados))
            m3.metric("Falsos (0)", len(filas) - sum(resultados))

            st.download_button("📥 Descargar CSV", df.to_csv(index=False).encode("utf-8"),
                               "tabla_verdad.csv", "text/csv", use_container_width=True)

# ============================================================
# GUÍA
# ============================================================
with st.expander("📚 Guía de Operadores"):
    st.markdown("""
| Símbolo | Nombre | Significado |
|:-------:|:-------|:------------|
| **∧** | Conjunción | AND - Verdadero si AMBOS son verdaderos |
| **∨** | Disyunción | OR - Verdadero si al menos UNO es verdadero |
| **¬** | Negación | NOT - Invierte el valor |
| **⊕** | XOR | Verdadero si son DIFERENTES |
| **→** | Condicional | Falso solo si p=1 y q=0 |
| **↔** | Bicondicional | Verdadero si ambos son IGUALES |

**Precedencia (mayor a menor):** ¬, ∧, ∨, ⊕, →, ↔. Usa paréntesis para cambiar el orden.

**También puedes escribir:** `~` `&` `|` `->` `<->` `XOR` directamente en las expresiones.
""")

st.markdown("---")
st.markdown("""
<div style='text-align: center; color: gray; font-size: 0.9em;'>
<p>🎓 <strong>Estructuras Discretas</strong> - Ingeniería en Software</p>
<p>💻 Desarrollado con Python y Streamlit</p>
</div>
""", unsafe_allow_html=True)
