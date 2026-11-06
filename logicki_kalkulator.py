"""Logički kalkulator za konačne domene (Tkinter, samo standardna biblioteka)."""

from __future__ import annotations

import itertools
import queue
import re
import threading
import time
import tkinter as tk
from dataclasses import dataclass
from tkinter import messagebox, ttk
from typing import Any


# Boje i granice računanja
INDIGO = "#061492"
PALE = "#f4f4f9"
INK = "#20243a"
MUTED = "#62677d"
GREEN = "#11733c"
RED = "#b42336"
MAX_TOKENS = 4_000
MAX_EXPANDED_NODES = 30_000
MAX_CNF_CLAUSES = 120_000
MAX_SOLVER_NODES = 80_000
SOLVER_SECONDS = 5.0
COUNT_SECONDS = 20.0
MAX_COUNT_SOLVER_NODES = 250_000
MAX_TABLE_ROWS = 120


class FormulaError(ValueError):
    """Pogreška u zapisu formule koju možemo objasniti korisniku."""


@dataclass(frozen=True, slots=True)
class Predicate:
    name: str
    args: tuple[Any, ...]


@dataclass(frozen=True, slots=True)
class Negation:
    child: Any


@dataclass(frozen=True, slots=True)
class Binary:
    operator: str
    left: Any
    right: Any


@dataclass(frozen=True, slots=True)
class Quantifier:
    operator: str
    variable: str
    body: Any


TOKEN_RE = re.compile(
    r"(?P<operator>[¬∨∧→↔∀∃])|(?P<left>\()|(?P<right>\))|"
    r"(?P<comma>,)|(?P<identifier>[^\W\d]\w*)",
    re.UNICODE,
)


def tokenize(source: str) -> list[str]:
    tokens: list[str] = []
    position = 0
    while position < len(source):
        if source[position].isspace():
            position += 1
            continue
        match = TOKEN_RE.match(source, position)
        if not match:
            bad = source[position]
            raise FormulaError(f"Nedopušten znak {bad!r} na mjestu {position + 1}.")
        tokens.append(match.group(0))
        position = match.end()
        if len(tokens) > MAX_TOKENS:
            raise FormulaError("Formula sadrži previše oznaka (najviše 4.000).")
    if not tokens:
        raise FormulaError("Formula je prazna.")
    return tokens


class FormulaParser:
    """Parser za ¬, ∧, ∨, →, ↔, ∀ i ∃ te predikate oblika A(x,y)."""

    def __init__(self, source: str):
        self.tokens = tokenize(source)
        self.position = 0

    def peek(self) -> str | None:
        if self.position >= len(self.tokens):
            return None
        return self.tokens[self.position]

    def take(self) -> str:
        token = self.peek()
        if token is None:
            raise FormulaError("Formula nije dovršena.")
        self.position += 1
        return token

    def accept(self, token: str) -> bool:
        if self.peek() == token:
            self.position += 1
            return True
        return False

    def identifier(self, purpose: str) -> str:
        token = self.peek()
        if token is None or not token.isidentifier():
            raise FormulaError(f"Očekujem naziv {purpose}.")
        return self.take()

    def parse(self) -> Any:
        expression = self.parse_iff()
        if self.peek() is not None:
            raise FormulaError(f"Neočekivani znak {self.peek()!r}.")
        return expression

    def parse_iff(self) -> Any:
        node = self.parse_implication()
        while self.accept("↔"):
            node = Binary("↔", node, self.parse_implication())
        return node

    def parse_implication(self) -> Any:
        node = self.parse_or()
        if self.accept("→"):
            return Binary("→", node, self.parse_implication())
        return node

    def parse_or(self) -> Any:
        node = self.parse_and()
        while self.accept("∨"):
            node = Binary("∨", node, self.parse_and())
        return node

    def parse_and(self) -> Any:
        node = self.parse_unary()
        while self.accept("∧"):
            node = Binary("∧", node, self.parse_unary())
        return node

    def parse_unary(self) -> Any:
        token = self.peek()
        if token == "¬":
            self.take()
            return Negation(self.parse_unary())
        if token in ("∀", "∃"):
            operator = self.take()
            variable = self.identifier("varijable iza kvantifikatora")
            return Quantifier(operator, variable, self.parse_unary())
        if self.accept("("):
            node = self.parse_iff()
            if not self.accept(")"):
                raise FormulaError("Nedostaje zatvorena zagrada ')'.")
            return node

        name = self.identifier("predikata")
        if not self.accept("("):
            raise FormulaError(f"Predikat {name} treba imati argumente, npr. {name}(x).")
        arguments = [self.identifier("argumenta predikata")]
        while self.accept(","):
            arguments.append(self.identifier("argumenta predikata"))
        if not self.accept(")"):
            raise FormulaError(f"Nedostaje ')' nakon argumenata predikata {name}.")
        return Predicate(name, tuple(arguments))


def parse_problem(premise_lines: list[str], conclusion_text: str) -> tuple[list[Any], Any, dict[str, int]]:
    premises: list[Any] = []
    for number, line in enumerate(premise_lines, start=1):
        if not line.strip():
            continue
        try:
            premises.append(FormulaParser(line).parse())
        except FormulaError as error:
            raise FormulaError(f"Premisa {number}: {error}") from error
    if not premises:
        raise FormulaError("Upiši barem jednu premisu.")
    try:
        conclusion = FormulaParser(conclusion_text).parse()
    except FormulaError as error:
        raise FormulaError(f"Zaključak: {error}") from error

    arities: dict[str, int] = {}

    def inspect(node: Any) -> None:
        if isinstance(node, Predicate):
            arity = len(node.args)
            if node.name in arities and arities[node.name] != arity:
                raise FormulaError(
                    f"Predikat {node.name} upotrijebljen je s različitim brojem argumenata."
                )
            arities[node.name] = arity
        elif isinstance(node, Negation):
            inspect(node.child)
        elif isinstance(node, Binary):
            inspect(node.left)
            inspect(node.right)
        elif isinstance(node, Quantifier):
            inspect(node.body)

    def free_variables(node: Any, bound: frozenset[str] = frozenset()) -> set[str]:
        if isinstance(node, Predicate):
            return {name for name in node.args if name not in bound}
        if isinstance(node, Negation):
            return free_variables(node.child, bound)
        if isinstance(node, Binary):
            return free_variables(node.left, bound) | free_variables(node.right, bound)
        if isinstance(node, Quantifier):
            return free_variables(node.body, bound | {node.variable})
        return set()

    for formula in [*premises, conclusion]:
        inspect(formula)
        free = sorted(free_variables(formula))
        if free:
            raise FormulaError(
                "Sve varijable moraju biti obuhvaćene kvantifikatorom (∀ ili ∃). "
                f"Slobodne varijable: {', '.join(free)}."
            )
    return premises, conclusion, arities


def ground_formula(node: Any, environment: dict[str, int], domain_size: int, counter: list[int]) -> Any:
    counter[0] += 1
    if counter[0] > MAX_EXPANDED_NODES:
        raise FormulaError(
            "Formula se za ovu domenu razvija u prevelik izraz. "
            "Pokušaj s manjom domenom ili kraćim formulama."
        )
    if isinstance(node, Predicate):
        try:
            return Predicate(node.name, tuple(environment[arg] for arg in node.args))
        except KeyError as error:
            raise FormulaError(f"Varijabla {error.args[0]} nije vezana kvantifikatorom.") from error
    if isinstance(node, Negation):
        return Negation(ground_formula(node.child, environment, domain_size, counter))
    if isinstance(node, Binary):
        return Binary(
            node.operator,
            ground_formula(node.left, environment, domain_size, counter),
            ground_formula(node.right, environment, domain_size, counter),
        )
    if isinstance(node, Quantifier):
        grounded = []
        for value in range(domain_size):
            updated = environment.copy()
            updated[node.variable] = value
            grounded.append(ground_formula(node.body, updated, domain_size, counter))
        connective = "∧" if node.operator == "∀" else "∨"
        expression = grounded[0]
        for child in grounded[1:]:
            counter[0] += 1
            if counter[0] > MAX_EXPANDED_NODES:
                raise FormulaError("Formula je prevelika za ovaj opseg domene.")
            expression = Binary(connective, expression, child)
        return expression
    raise FormulaError("Nepoznata vrsta izraza.")


def collect_ground_atoms(node: Any, result: set[tuple[str, tuple[int, ...]]]) -> None:
    if isinstance(node, Predicate):
        result.add((node.name, tuple(node.args)))
    elif isinstance(node, Negation):
        collect_ground_atoms(node.child, result)
    elif isinstance(node, Binary):
        collect_ground_atoms(node.left, result)
        collect_ground_atoms(node.right, result)


def compile_program(node: Any, atom_indexes: dict[tuple[str, tuple[int, ...]], int], output: list[tuple[str, int | None]]) -> None:
    if isinstance(node, Predicate):
        output.append(("A", atom_indexes[(node.name, tuple(node.args))]))
    elif isinstance(node, Negation):
        compile_program(node.child, atom_indexes, output)
        output.append(("¬", None))
    elif isinstance(node, Binary):
        compile_program(node.left, atom_indexes, output)
        compile_program(node.right, atom_indexes, output)
        output.append((node.operator, None))


def run_program(program: list[tuple[str, int | None]], values: list[bool]) -> bool:
    stack: list[bool] = []
    for operator, argument in program:
        if operator == "A":
            stack.append(values[argument])
        elif operator == "¬":
            stack[-1] = not stack[-1]
        else:
            right = stack.pop()
            left = stack.pop()
            if operator == "∧":
                stack.append(left and right)
            elif operator == "∨":
                stack.append(left or right)
            elif operator == "→":
                stack.append((not left) or right)
            elif operator == "↔":
                stack.append(left == right)
    return stack[-1]


class TseitinEncoder:
    """Pretvara prizemljenu formulu u CNF bez promjene njezine istinitosti."""

    def __init__(self, atom_indexes: dict[tuple[str, tuple[int, ...]], int]):
        self.atom_indexes = atom_indexes
        self.atom_variables: dict[tuple[str, tuple[int, ...]], int] = {}
        self.next_variable = 1
        self.clauses: list[list[int]] = []

    def new_variable(self) -> int:
        variable = self.next_variable
        self.next_variable += 1
        return variable

    def atom_variable(self, key: tuple[str, tuple[int, ...]]) -> int:
        if key not in self.atom_variables:
            self.atom_variables[key] = self.new_variable()
        return self.atom_variables[key]

    def encode(self, node: Any) -> int:
        if isinstance(node, Predicate):
            return self.atom_variable((node.name, tuple(node.args)))
        if isinstance(node, Negation):
            child = self.encode(node.child)
            result = self.new_variable()
            self.clauses.extend([[-result, -child], [result, child]])
            return result

        left = self.encode(node.left)
        right = self.encode(node.right)
        result = self.new_variable()
        if node.operator == "∧":
            self.clauses.extend([[-result, left], [-result, right], [result, -left, -right]])
        elif node.operator == "∨":
            self.clauses.extend([[result, -left], [result, -right], [-result, left, right]])
        elif node.operator == "→":
            self.clauses.extend([[result, left], [result, -right], [-result, -left, right]])
        elif node.operator == "↔":
            self.clauses.extend(
                [
                    [-result, -left, right],
                    [-result, left, -right],
                    [result, left, right],
                    [result, -left, -right],
                ]
            )
        else:
            raise FormulaError(f"Nepoznat operator {node.operator}.")
        if len(self.clauses) > MAX_CNF_CLAUSES:
            raise FormulaError("Formula je prevelika za sigurnu provjeru na ovom računalu.")
        return result


class DpllSolver:
    """Mali SAT rješavač s jediničnim širenjem i ograničenjima resursa."""

    def __init__(
        self,
        clauses: list[list[int]],
        variable_count: int,
        *,
        time_limit: float = SOLVER_SECONDS,
        node_limit: int = MAX_SOLVER_NODES,
    ):
        self.clauses = clauses
        self.variable_count = variable_count
        self.nodes = 0
        self.deadline = time.monotonic() + time_limit
        self.node_limit = node_limit
        self.aborted = False
        self.scans = 0

    def solve(self) -> list[int] | None | bool:
        assignment = [0] * (self.variable_count + 1)
        result = self.search(assignment)
        if result is False:
            return False
        if result is None:
            return None
        return result

    def search(self, assignment: list[int]) -> list[int] | None | bool:
        self.nodes += 1
        if self.nodes > self.node_limit or time.monotonic() > self.deadline:
            self.aborted = True
            return None
        propagated = self.propagate(assignment)
        if propagated is None:
            return None
        if not propagated:
            return False
        variable = self.choose_variable(assignment)
        if variable is None:
            return assignment
        for value in (1, -1):
            branch = assignment.copy()
            branch[variable] = value
            result = self.search(branch)
            if result is not False:
                return result
            if self.aborted:
                return None
        return False

    def propagate(
        self,
        assignment: list[int],
        protected_variables: set[int] | None = None,
    ) -> bool | None:
        while True:
            changed = False
            pure_signs = [0] * (self.variable_count + 1)
            for clause in self.clauses:
                self.scans += 1
                if self.scans % 256 == 0 and time.monotonic() > self.deadline:
                    self.aborted = True
                    return None
                satisfied = False
                unassigned = 0
                last_literal = 0
                for literal in clause:
                    value = assignment[abs(literal)]
                    if value and (value > 0) == (literal > 0):
                        satisfied = True
                        break
                    if value == 0:
                        unassigned += 1
                        last_literal = literal
                if satisfied:
                    continue
                if unassigned == 0:
                    return False
                if unassigned == 1:
                    variable = abs(last_literal)
                    required = 1 if last_literal > 0 else -1
                    if assignment[variable] not in (0, required):
                        return False
                    if assignment[variable] == 0:
                        assignment[variable] = required
                        changed = True
                for literal in clause:
                    variable = abs(literal)
                    if assignment[variable] == 0:
                        sign = 1 if literal > 0 else -1
                        pure_signs[variable] |= 1 if sign > 0 else 2
            if changed:
                continue
            for variable in range(1, self.variable_count + 1):
                if (
                    assignment[variable] == 0
                    and (protected_variables is None or variable not in protected_variables)
                    and pure_signs[variable] in (1, 2)
                ):
                    assignment[variable] = 1 if pure_signs[variable] == 1 else -1
                    changed = True
            if changed:
                continue
            return True

    def choose_variable(self, assignment: list[int]) -> int | None:
        best_candidates: list[int] | None = None
        scores = [0] * (self.variable_count + 1)
        for clause in self.clauses:
            satisfied = False
            candidates = []
            for literal in clause:
                value = assignment[abs(literal)]
                if value and (value > 0) == (literal > 0):
                    satisfied = True
                    break
                if value == 0:
                    candidates.append(abs(literal))
            if satisfied:
                continue
            if not candidates:
                return None
            for variable in candidates:
                scores[variable] += 1
            if best_candidates is None or len(candidates) < len(best_candidates):
                best_candidates = candidates
        if best_candidates is None:
            return None
        return max(best_candidates, key=lambda variable: scores[variable])

    def count_projected_models(self, projected_variables: list[int]) -> tuple[int, bool]:
        """Count satisfying assignments to selected variables, ignoring Tseitin auxiliaries."""
        projected = set(projected_variables)
        count = self.count_search([0] * (self.variable_count + 1), projected)
        return count, not self.aborted

    def count_search(self, assignment: list[int], projected: set[int]) -> int:
        self.nodes += 1
        if self.nodes > self.node_limit or time.monotonic() > self.deadline:
            self.aborted = True
            return 0

        propagated = self.propagate(assignment, protected_variables=projected)
        if propagated is None:
            return 0
        if not propagated:
            return 0

        unassigned_projected = [variable for variable in projected if assignment[variable] == 0]
        relevant_scores: dict[int, int] = {}
        unresolved_clauses = 0
        for clause in self.clauses:
            satisfied = False
            candidates: list[int] = []
            for literal in clause:
                value = assignment[abs(literal)]
                if value and (value > 0) == (literal > 0):
                    satisfied = True
                    break
                if value == 0:
                    candidates.append(abs(literal))
            if satisfied:
                continue
            unresolved_clauses += 1
            for variable in candidates:
                if variable in projected:
                    relevant_scores[variable] = relevant_scores.get(variable, 0) + 1

        if unresolved_clauses == 0:
            return 1 << len(unassigned_projected)

        # If all open clauses only depend on auxiliary variables, one SAT query
        # determines whether every remaining projected assignment works.
        if not relevant_scores:
            satisfiable = self.search(assignment.copy())
            if satisfiable is False:
                return 0
            if satisfiable is None:
                return 0
            return 1 << len(unassigned_projected)

        variable = max(relevant_scores, key=relevant_scores.get)
        total = 0
        for value in (1, -1):
            branch = assignment.copy()
            branch[variable] = value
            total += self.count_search(branch, projected)
            if self.aborted:
                break
        return total


def safe_power_count(exponent: int) -> str:
    if exponent <= 20:
        return f"{1 << exponent:,}".replace(",", ".")
    if exponent.bit_length() < 13_000:
        return f"2^{exponent:,}".replace(",", ".")
    return "2^(zbroj veličina svih predikata)"


def build_counterexample_problem(
    premise_lines: list[str],
    conclusion_text: str,
    domain: list[str],
) -> tuple[dict[str, int], list[tuple[str, tuple[int, ...]]], int, TseitinEncoder, int]:
    premises, conclusion, arities = parse_problem(premise_lines, conclusion_text)
    size = len(domain)
    if not 2 <= size <= 6:
        raise FormulaError("Domena mora imati od 2 do 6 elemenata.")

    counter = [0]
    grounded_premises = [ground_formula(item, {}, size, counter) for item in premises]
    grounded_conclusion = ground_formula(conclusion, {}, size, counter)

    interpretation_bits = sum(size ** arity for arity in arities.values())
    used_atoms: set[tuple[str, tuple[int, ...]]] = set()
    for item in grounded_premises:
        collect_ground_atoms(item, used_atoms)
    collect_ground_atoms(grounded_conclusion, used_atoms)
    atom_keys = sorted(used_atoms)
    atom_indexes = {key: index for index, key in enumerate(atom_keys)}

    counter_formula: Any = grounded_premises[0]
    for item in grounded_premises[1:]:
        counter_formula = Binary("∧", counter_formula, item)
    counter_formula = Binary("∧", counter_formula, Negation(grounded_conclusion))
    encoder = TseitinEncoder(atom_indexes)
    root_variable = encoder.encode(counter_formula)
    encoder.clauses.append([root_variable])
    return arities, atom_keys, interpretation_bits, encoder, root_variable


def analyze(premise_lines: list[str], conclusion_text: str, domain: list[str]) -> dict[str, Any]:
    arities, atom_keys, interpretation_bits, encoder, _root_variable = build_counterexample_problem(
        premise_lines, conclusion_text, domain
    )
    solver = DpllSolver(encoder.clauses, encoder.next_variable - 1)
    solved = solver.solve()
    if solved is False:
        status = "valid"
        model_values = None
    elif solved is None:
        status = "unknown"
        model_values = None
    else:
        status = "invalid"
        model_values = [False] * len(atom_keys)
        atom_indexes = {key: index for index, key in enumerate(atom_keys)}
        for key, variable in encoder.atom_variables.items():
            value = solved[variable]
            model_values[atom_indexes[key]] = value > 0

    return {
        "status": status,
        "domain": domain,
        "arities": arities,
        "atom_keys": atom_keys,
        "model_values": model_values,
        "interpretation_bits": interpretation_bits,
        "interpretation_count": safe_power_count(interpretation_bits),
        "solver_nodes": solver.nodes,
        "premises": premise_lines,
        "conclusion": conclusion_text,
    }


def count_counterexamples(
    premise_lines: list[str],
    conclusion_text: str,
    domain: list[str],
) -> dict[str, Any]:
    """Optionally count projected SAT models, multiplying in unused relation cells."""
    _arities, atom_keys, interpretation_bits, encoder, _root_variable = build_counterexample_problem(
        premise_lines, conclusion_text, domain
    )
    projected_variables = [encoder.atom_variables[key] for key in atom_keys]
    solver = DpllSolver(
        encoder.clauses,
        encoder.next_variable - 1,
        time_limit=COUNT_SECONDS,
        node_limit=MAX_COUNT_SOLVER_NODES,
    )
    used_counterexamples, complete = solver.count_projected_models(projected_variables)
    return {
        "used_counterexamples": used_counterexamples,
        "free_atom_bits": interpretation_bits - len(atom_keys),
        "interpretation_bits": interpretation_bits,
        "complete": complete,
        "solver_nodes": solver.nodes,
    }


def format_big_count(value: int) -> str:
    if value.bit_length() > 12_000:
        return f"točan broj od {value.bit_length():,} bitova".replace(",", ".")
    return f"{value:,}".replace(",", ".")


def format_scaled_count(value: int, power_of_two: int) -> str:
    if value == 0:
        return "0"
    if value & (value - 1) == 0:
        return f"2^{value.bit_length() - 1 + power_of_two:,}".replace(",", ".")
    if value.bit_length() + power_of_two <= 12_000:
        return format_big_count(value << power_of_two)
    if power_of_two:
        return f"{format_big_count(value)} × 2^{power_of_two:,}".replace(",", ".")
    return format_big_count(value)


class LogicalCalculator:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Logički kalkulator")
        self.root.geometry("960x850")
        self.root.minsize(800, 700)
        self.root.configure(bg=PALE)
        self.active_text: tk.Text | None = None
        self.premise_text = ""
        self.conclusion_text = ""
        self.name_vars: list[tk.StringVar] = []
        self.result_queue: queue.Queue[tuple[str, Any]] = queue.Queue()
        self.analysis_running = False
        self.count_button: ttk.Button | None = None

        self.setup_style()
        header = tk.Frame(root, bg=INDIGO, height=74)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Label(
            header,
            text="Logički kalkulator",
            font=("Segoe UI", 22, "bold"),
            fg="white",
            bg=INDIGO,
        ).pack(side="left", padx=24, pady=17)
        tk.Label(
            header,
            text="Konačne domene · predikatska logika",
            font=("Segoe UI", 10),
            fg="#dce1ff",
            bg=INDIGO,
        ).pack(side="right", padx=24)

        self.page_host = tk.Frame(root, bg=PALE)
        self.page_host.pack(fill="both", expand=True, padx=18, pady=14)
        self.formula_page = tk.Frame(self.page_host, bg=PALE)
        self.domain_page = tk.Frame(self.page_host, bg=PALE)
        self.build_formula_page()
        self.build_domain_page()
        self.show_page(self.formula_page)

    def setup_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TButton", font=("Segoe UI", 10), padding=(12, 8))
        style.configure("Primary.TButton", font=("Segoe UI", 11, "bold"), padding=(16, 9))
        style.map("Primary.TButton", background=[("!disabled", INDIGO), ("active", "#101fae")], foreground=[("!disabled", "white")])
        style.configure("TLabel", font=("Segoe UI", 10), background=PALE, foreground=INK)
        style.configure("Card.TLabelframe", background="white", bordercolor="#d9dced", relief="solid")
        style.configure("Card.TLabelframe.Label", background="white", foreground=INDIGO, font=("Segoe UI", 11, "bold"))
        style.configure("TEntry", padding=6)
        style.configure("TSpinbox", padding=5)

    def card(self, parent: tk.Widget, title: str) -> ttk.LabelFrame:
        return ttk.LabelFrame(parent, text=title, style="Card.TLabelframe", padding=12)

    def build_formula_page(self) -> None:
        page = self.formula_page
        tk.Label(
            page,
            text="Upiši svaku premisu u zaseban redak i zatim konkluziju.",
            font=("Segoe UI", 11),
            fg=MUTED,
            bg=PALE,
            anchor="w",
        ).pack(fill="x", pady=(0, 10))

        premise_card = self.card(page, "Premise")
        premise_card.pack(fill="x", pady=(0, 9))
        self.premises_box = tk.Text(
            premise_card, height=4, wrap="word", font=("Segoe UI Symbol", 14),
            undo=True, relief="solid", bd=1, padx=9, pady=7,
            highlightthickness=1, highlightbackground="#c9cde0", highlightcolor=INDIGO,
        )
        self.premises_box.pack(fill="x")
        self.premises_box.bind("<FocusIn>", lambda _event: self.set_active(self.premises_box))

        conclusion_card = self.card(page, "Konkluzija")
        conclusion_card.pack(fill="x", pady=(0, 9))
        self.conclusion_box = tk.Text(
            conclusion_card, height=2, wrap="word", font=("Segoe UI Symbol", 14),
            undo=True, relief="solid", bd=1, padx=9, pady=7,
            highlightthickness=1, highlightbackground="#c9cde0", highlightcolor=INDIGO,
        )
        self.conclusion_box.pack(fill="x")
        self.conclusion_box.bind("<FocusIn>", lambda _event: self.set_active(self.conclusion_box))

        symbols_card = self.card(page, "Oznake koje možeš umetnuti")
        symbols_card.pack(fill="x", pady=(0, 9))
        toolbar = tk.Frame(symbols_card, bg="white")
        toolbar.pack(fill="x")
        symbol_items = [("¬", "¬"), ("∨", "∨"), ("∧", "∧"), ("→", "→"), ("↔", "↔"), ("∀", "∀"), ("∃", "∃"), ("A( )", "A()"), ("( )", "()")]
        for index, (label, value) in enumerate(symbol_items):
            button = ttk.Button(toolbar, text=label, command=lambda item=value: self.insert_symbol(item))
            button.grid(row=index // 5, column=index % 5, padx=4, pady=4, sticky="ew")
            toolbar.grid_columnconfigure(index % 5, weight=1)

        help_text = (
            "Primjeri:  ∀x A(x)     ∃x (A(x) ∧ B(x))     R(x,y)\n"
            "Prioritet je ¬, ∧, ∨, →, ↔. Zagradama odredi opseg kvantifikatora, npr. ∀x (A(x) → B(x)).\n"
            "Svaka varijabla u predikatu mora biti vezana s ∀ ili ∃. Predikat s više argumenata piše se R(x,y)."
        )
        tk.Label(
            symbols_card, text=help_text, justify="left", anchor="w", wraplength=880,
            font=("Segoe UI", 9), fg=MUTED, bg="white",
        ).pack(fill="x", padx=3, pady=(7, 2))

        examples = tk.Frame(page, bg=PALE)
        examples.pack(fill="x", pady=(0, 8))
        ttk.Button(examples, text="Učitaj valjan primjer", command=self.load_valid_example).pack(side="left", padx=(0, 7))
        ttk.Button(examples, text="Učitaj primjer s protuprimjerom", command=self.load_counterexample).pack(side="left")

        ttk.Button(page, text="OK — dalje na domenu", style="Primary.TButton", command=self.go_to_domain).pack(anchor="e", pady=(2, 0))

    def build_domain_page(self) -> None:
        page = self.domain_page
        tk.Label(
            page,
            text="Odredi konačnu domenu. Kvantifikatori ∀ i ∃ prolaze kroz sve njezine elemente.",
            font=("Segoe UI", 11),
            fg=MUTED,
            bg=PALE,
            anchor="w",
            wraplength=900,
        ).pack(fill="x", pady=(0, 10))

        summary_card = self.card(page, "Unesena konkluzija")
        summary_card.pack(fill="x", pady=(0, 10))
        self.problem_summary = tk.Label(
            summary_card, text="", justify="left", anchor="w", wraplength=880,
            font=("Segoe UI Symbol", 11), fg=INK, bg="white",
        )
        self.problem_summary.pack(fill="x")

        domain_card = self.card(page, "Domena")
        domain_card.pack(fill="x", pady=(0, 10))
        count_row = tk.Frame(domain_card, bg="white")
        count_row.pack(fill="x", pady=(0, 8))
        tk.Label(count_row, text="Broj elemenata (2–6):", bg="white", fg=INK, font=("Segoe UI", 10)).pack(side="left")
        self.domain_count = tk.IntVar(value=2)
        self.count_spin = ttk.Spinbox(count_row, from_=2, to=6, width=6, textvariable=self.domain_count, command=self.rebuild_domain_entries)
        self.count_spin.pack(side="left", padx=10)
        self.count_spin.bind("<KeyRelease>", lambda _event: self.rebuild_domain_entries())
        self.count_spin.bind("<FocusOut>", lambda _event: self.rebuild_domain_entries())
        tk.Label(count_row, text="Imena su oznake elemenata domene, npr. a, b, c.", bg="white", fg=MUTED, font=("Segoe UI", 9)).pack(side="left", padx=6)

        self.domain_entries_frame = tk.Frame(domain_card, bg="white")
        self.domain_entries_frame.pack(fill="x")
        self.rebuild_domain_entries()

        actions = tk.Frame(page, bg=PALE)
        actions.pack(fill="x", pady=(0, 9))
        ttk.Button(actions, text="Natrag", command=lambda: self.show_page(self.formula_page)).pack(side="left")
        self.check_button = ttk.Button(actions, text="Provjeri valjanost", style="Primary.TButton", command=self.start_analysis)
        self.check_button.pack(side="right")

        result_card = self.card(page, "Rezultat")
        result_card.pack(fill="both", expand=True)
        result_area = tk.Frame(result_card, bg="white")
        result_area.pack(fill="both", expand=True)
        result_area.grid_rowconfigure(0, weight=1)
        result_area.grid_columnconfigure(0, weight=1)
        self.result_canvas = tk.Canvas(result_area, bg="white", highlightthickness=0, height=235)
        self.result_canvas.grid(row=0, column=0, sticky="nsew")
        vertical = ttk.Scrollbar(result_area, orient="vertical", command=self.result_canvas.yview)
        vertical.grid(row=0, column=1, sticky="ns")
        horizontal = ttk.Scrollbar(result_area, orient="horizontal", command=self.result_canvas.xview)
        horizontal.grid(row=1, column=0, sticky="ew")
        self.result_canvas.configure(yscrollcommand=vertical.set, xscrollcommand=horizontal.set)
        self.result_inner = tk.Frame(self.result_canvas, bg="white")
        self.result_canvas_window = self.result_canvas.create_window((0, 0), window=self.result_inner, anchor="nw")
        self.result_inner.bind("<Configure>", self.update_result_scrollregion)

    def update_result_scrollregion(self, _event: Any = None) -> None:
        self.result_canvas.configure(scrollregion=self.result_canvas.bbox("all"))

    def show_page(self, page: tk.Frame) -> None:
        for child in self.page_host.winfo_children():
            child.pack_forget()
        page.pack(fill="both", expand=True)

    def set_active(self, widget: tk.Text) -> None:
        self.active_text = widget

    def insert_symbol(self, symbol: str) -> None:
        widget = self.root.focus_get()
        if not isinstance(widget, tk.Text):
            widget = self.active_text
        if not isinstance(widget, tk.Text):
            self.premises_box.focus_set()
            widget = self.premises_box
        if widget.tag_ranges("sel"):
            start, end = widget.index("sel.first"), widget.index("sel.last")
            widget.delete(start, end)
            widget.mark_set("insert", start)
        snippets = {
            "∀": ("∀x()", "insert-1c"),
            "∃": ("∃x()", "insert-1c"),
            "A()": ("A()", "insert-1c"),
            "()": ("()", "insert-1c"),
            "∨": (" ∨ ", "insert"),
            "∧": (" ∧ ", "insert"),
            "→": (" → ", "insert"),
            "↔": (" ↔ ", "insert"),
            "¬": ("¬", "insert"),
        }
        value, cursor = snippets[symbol]
        widget.insert("insert", value)
        widget.mark_set("insert", cursor)
        widget.focus_set()
        widget.see("insert")
        self.active_text = widget

    def load_valid_example(self) -> None:
        self.premises_box.delete("1.0", "end")
        self.premises_box.insert("1.0", "∀x A(x)")
        self.conclusion_box.delete("1.0", "end")
        self.conclusion_box.insert("1.0", "∀x A(x)")
        self.active_text = self.premises_box

    def load_counterexample(self) -> None:
        self.premises_box.delete("1.0", "end")
        self.premises_box.insert("1.0", "∀x (A(x) ∨ B(x))")
        self.conclusion_box.delete("1.0", "end")
        self.conclusion_box.insert("1.0", "∀x B(x)")
        self.active_text = self.premises_box

    def read_formula_inputs(self) -> tuple[list[str], str]:
        premises = self.premises_box.get("1.0", "end-1c").splitlines()
        conclusion = self.conclusion_box.get("1.0", "end-1c").strip()
        parse_problem(premises, conclusion)
        return premises, conclusion

    def go_to_domain(self) -> None:
        try:
            self.premise_text, self.conclusion_text = self.read_formula_inputs()
        except FormulaError as error:
            messagebox.showerror("Provjeri formule", str(error), parent=self.root)
            return
        compact_premises = "\n".join(line.strip() for line in self.premise_text if line.strip())
        self.problem_summary.configure(text=f"{compact_premises}\n∴  {self.conclusion_text}")
        self.show_page(self.domain_page)

    def rebuild_domain_entries(self) -> None:
        try:
            count = int(self.domain_count.get())
        except (ValueError, tk.TclError):
            return
        if not 2 <= count <= 6:
            return
        existing = [variable.get() for variable in self.name_vars]
        for child in self.domain_entries_frame.winfo_children():
            child.destroy()
        defaults = ["a", "b", "c", "d", "e", "f"]
        self.name_vars = []
        for index in range(count):
            row, column = divmod(index, 2)
            value = existing[index] if index < len(existing) else defaults[index]
            variable = tk.StringVar(value=value)
            self.name_vars.append(variable)
            cell = tk.Frame(self.domain_entries_frame, bg="white")
            cell.grid(row=row, column=column, sticky="ew", padx=(0, 18), pady=4)
            tk.Label(cell, text=f"Element {index + 1}:", width=11, anchor="w", bg="white", fg=INK).pack(side="left")
            ttk.Entry(cell, textvariable=variable, width=22).pack(side="left", fill="x", expand=True)
            self.domain_entries_frame.grid_columnconfigure(column, weight=1)

    def read_domain(self) -> list[str]:
        try:
            count = int(self.domain_count.get())
        except (ValueError, tk.TclError) as error:
            raise FormulaError("Odaberi broj elemenata domene između 2 i 6.") from error
        if not 2 <= count <= 6 or count != len(self.name_vars):
            raise FormulaError("Broj elemenata domene mora biti između 2 i 6.")
        names = [variable.get().strip() for variable in self.name_vars]
        if any(not name for name in names):
            raise FormulaError("Upiši ime za svaki element domene.")
        normalized = [name.casefold() for name in names]
        if len(set(normalized)) != len(names):
            raise FormulaError("Imena elemenata domene moraju biti različita.")
        return names

    def start_analysis(self) -> None:
        if self.analysis_running:
            return
        try:
            domain = self.read_domain()
        except FormulaError as error:
            messagebox.showerror("Provjeri domenu", str(error), parent=self.root)
            return
        self.analysis_running = True
        self.check_button.configure(state="disabled", text="Provjeravam…")
        self.write_result("SAT rješavač traži protuprimjer…\n")

        def worker() -> None:
            try:
                result = analyze(self.premise_text, self.conclusion_text, domain)
                self.result_queue.put(("result", result))
            except (FormulaError, RecursionError, MemoryError) as error:
                self.result_queue.put(("error", str(error) or "Formula je prezahtjevna za ovu provjeru."))
            except Exception as error:  # Prikaži i neočekivanu pogrešku umjesto da se prozor zamrzne.
                self.result_queue.put(("error", f"Došlo je do pogreške pri računanju: {error}"))

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(100, self.poll_result)

    def poll_result(self) -> None:
        try:
            kind, payload = self.result_queue.get_nowait()
        except queue.Empty:
            self.root.after(100, self.poll_result)
            return
        self.analysis_running = False
        self.check_button.configure(state="normal", text="Provjeri valjanost")
        if kind == "error":
            self.write_result("Ne mogu provjeriti unos.\n\n" + payload, "unknown")
        elif kind == "count_error":
            self.add_result_line("Brojanje nije dovršeno.", color=INDIGO, bold=True)
            self.add_result_line(payload, color=MUTED)
            if self.count_button is not None:
                self.count_button.configure(state="normal", text="Pokušaj prebrojiti ponovno")
        elif kind == "count_result":
            self.display_count_result(payload)
        else:
            self.display_result(payload)

    def clear_result(self) -> None:
        for child in self.result_inner.winfo_children():
            child.destroy()
        self.result_canvas.yview_moveto(0)
        self.result_canvas.xview_moveto(0)

    def add_result_line(self, text: str, *, color: str = INK, bold: bool = False) -> None:
        font = ("Segoe UI", 10, "bold") if bold else ("Segoe UI", 10)
        tk.Label(
            self.result_inner, text=text, font=font, fg=color, bg="white",
            anchor="w", justify="left", wraplength=840,
        ).pack(fill="x", anchor="w", padx=6, pady=2)

    def write_result(self, text: str, heading_tag: str = "normal") -> None:
        self.clear_result()
        colors = {"valid": GREEN, "invalid": RED, "unknown": INDIGO, "normal": INK}
        first_line, separator, rest = text.partition("\n")
        self.add_result_line(first_line, color=colors.get(heading_tag, INK), bold=True)
        if separator:
            for line in rest.splitlines():
                if line:
                    self.add_result_line(line)

    def start_counting(self, result: dict[str, Any]) -> None:
        if self.analysis_running:
            return
        self.analysis_running = True
        self.check_button.configure(state="disabled", text="Brojim…")
        if self.count_button is not None:
            self.count_button.configure(state="disabled", text="Brojim protuprimjere…")
        self.add_result_line("Prebrojavam protuprimjere; aplikacija ostaje dostupna…", color=INDIGO)

        def worker() -> None:
            try:
                counts = count_counterexamples(
                    result["premises"], result["conclusion"], result["domain"]
                )
                self.result_queue.put(("count_result", counts))
            except (FormulaError, RecursionError, MemoryError) as error:
                self.result_queue.put(("count_error", str(error) or "Brojanje je prezahtjevno."))
            except Exception as error:
                self.result_queue.put(("count_error", f"Došlo je do pogreške pri brojanju: {error}"))

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(100, self.poll_result)

    def display_count_result(self, counts: dict[str, Any]) -> None:
        numerator = format_scaled_count(
            counts["used_counterexamples"], counts["free_atom_bits"]
        )
        total = safe_power_count(counts["interpretation_bits"])
        if counts["complete"]:
            self.add_result_line(
                f"Ukupno protuprimjera: {numerator} od {total} mogućih rasporeda.",
                bold=True,
            )
            self.add_result_line("Brojanje je završeno.", color=GREEN)
            if self.count_button is not None:
                self.count_button.configure(state="disabled", text="Brojanje dovršeno")
        else:
            self.add_result_line(
                f"Brojanje je prekinuto. Prebrojano je najmanje {numerator} protuprimjera "
                f"od {total} mogućih rasporeda.",
                color=INDIGO,
                bold=True,
            )
            self.add_result_line(
                "Dosegnuto je vremensko ili računsko ograničenje; prikazani broj može biti manji od ukupnog.",
                color=MUTED,
            )
            if self.count_button is not None:
                self.count_button.configure(state="normal", text="Pokušaj prebrojiti ponovno")

    def add_truth_tables(self, result: dict[str, Any]) -> None:
        values = result["model_values"] or []
        truth_by_atom = {
            key: values[index]
            for index, key in enumerate(result["atom_keys"])
            if index < len(values)
        }
        by_arity: dict[int, list[str]] = {}
        for name, arity in result["arities"].items():
            by_arity.setdefault(arity, []).append(name)

        self.add_result_line("Tablica istinitosti protuprimjera (1 = istinito, 0 = neistinito):", bold=True)
        domain = result["domain"]
        size = len(domain)
        for arity, names in sorted(by_arity.items()):
            names.sort()
            title = "Predikati s jednim argumentom" if arity == 1 else f"Predikati s {arity} argumenata"
            tk.Label(
                self.result_inner, text=title, font=("Segoe UI", 10, "bold", "underline"),
                fg=INDIGO, bg="white", anchor="w",
            ).pack(fill="x", anchor="w", padx=6, pady=(8, 3))
            table = tk.Frame(self.result_inner, bg="white")
            table.pack(anchor="w", padx=6, pady=(0, 5))

            row_heading = "Element domene" if arity == 1 else "" + "Vrijednosti varijabli"
            tk.Label(
                table, text=row_heading, font=("Segoe UI", 9, "bold"),
                borderwidth=1, relief="solid", padx=7, pady=5,
                bg="#e0e7ff", fg=INDIGO, anchor="center",
            ).grid(row=0, column=0, sticky="nsew")
            for column, name in enumerate(names, start=1):
                tk.Label(
                    table, text=name, font=("Segoe UI", 10, "bold"),
                    borderwidth=1, relief="solid", padx=10, pady=5,
                    bg="#e0e7ff", fg=INDIGO,
                ).grid(row=0, column=column, sticky="nsew")

            total_rows = size ** arity
            tuples = list(itertools.islice(itertools.product(range(size), repeat=arity), MAX_TABLE_ROWS))
            for row_number, tuple_indexes in enumerate(tuples, start=1):
                if arity == 1:
                    row_label = domain[tuple_indexes[0]]
                else:
                    row_label = "(" + ", ".join(domain[index] for index in tuple_indexes) + ")"
                tk.Label(
                    table, text=row_label, font=("Segoe UI", 9, "bold"),
                    borderwidth=1, relief="solid", padx=7, pady=4,
                    bg="#e0e7ff", fg=INDIGO,
                ).grid(row=row_number, column=0, sticky="nsew")
                for column, name in enumerate(names, start=1):
                    value = truth_by_atom.get((name, tuple(tuple_indexes)), False)
                    tk.Label(
                        table, text="1" if value else "0", font=("Segoe UI", 10, "bold"),
                        borderwidth=1, relief="solid", padx=12, pady=4,
                        bg="#ffffff" if value else "#ffd6d6", fg=INDIGO,
                    ).grid(row=row_number, column=column, sticky="nsew")
            if total_rows > len(tuples):
                omitted = f"{total_rows - len(tuples):,}".replace(",", ".")
                self.add_result_line(f"Prikazano je {len(tuples)} redaka; izostavljeno redaka: {omitted}.", color=MUTED)

    def display_result(self, result: dict[str, Any]) -> None:
        self.count_button = None
        self.clear_result()
        status = result["status"]
        if status == "valid":
            self.add_result_line("Zaključak je valjan za ovu domenu.", color=GREEN, bold=True)
        elif status == "invalid":
            self.add_result_line("Zaključak nije valjan za ovu domenu.", color=RED, bold=True)
        else:
            self.add_result_line("Valjanost nije potvrđena; pretraga je dosegla svoj limit.", color=INDIGO, bold=True)
            self.add_result_line("Pokušaj s manjom domenom ili jednostavnijim formulama.")

        if status != "unknown":
            self.add_result_line(
                f"Mogući rasporedi istinitosti predikata: {result['interpretation_count']}."
            )
        if status == "unknown":
            self.add_result_line(f"Broj obrađenih grana pretrage: {result['solver_nodes']:,}.".replace(",", "."))
        if status == "invalid":
            self.add_truth_tables(result)
            self.count_button = ttk.Button(
                self.result_inner,
                text="Prebroji sve protuprimjere",
                command=lambda: self.start_counting(result),
            )
            self.count_button.pack(anchor="w", padx=6, pady=(7, 5))
            if messagebox.askyesno(
                "Prebroj protuprimjere?",
                "SAT rješavač je pronašao protuprimjer. Želiš li prebrojiti sve "
                "protuprimjere od svih mogućih rasporeda istinitosti?\n\n"
                "Brojanje može potrajati do 20 sekundi.",
                parent=self.root,
            ):
                self.start_counting(result)


def main() -> None:
    root = tk.Tk()
    LogicalCalculator(root)
    root.mainloop()


if __name__ == "__main__":
    main()
