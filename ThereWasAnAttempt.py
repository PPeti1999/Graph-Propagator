from z3.z3 import *

class GraphUserPropagator(UserPropagateBase):
    def __init__(self, solver, num_nodes, ctx=None):
        super().__init__(solver, ctx)
        self.num_nodes = num_nodes
        self.solver = solver

        # Csúcsok és élek definiálása
        self.Node = DeclareSort("Node")  # Csúcsok típusa
        self.edge = Function("edge", self.Node, self.Node, BoolSort())  # Élek relációja

        # Callback-ek regisztrálása
        self.add_fixed(self.on_fixed)
        self.add_final(self.on_final)

        # Belső állapot tárolása a propagátorban
        self.active_edges = []  # Aktív élek listája
        self.state_stack = []  # Állapotok mentésére stack

    def push(self):
        """Mentjük az aktuális állapotot."""
        self.state_stack.append(list(self.active_edges))
        print(f"State pushed: {self.active_edges}")

    def pop(self, num_scopes):
        """Visszaállítjuk az előző állapotot."""
        for _ in range(num_scopes):
            if self.state_stack:
                self.active_edges = self.state_stack.pop()
                print(f"State popped: {self.active_edges}")

    def on_fixed(self, fixed):
        """Callback triggered when a variable is fixed."""
        print(f"on_fixed called for: {fixed}")

        if fixed.decl() == self.edge:
            u, v = fixed.children()
            is_true = self.solver.model().evaluate(fixed, model_completion=True)
            if is_true:
                print(f"Edge added to active edges: ({u}, {v})")
                self.active_edges.append((u, v))

    def on_final(self):
        """Callback triggered when the solver reaches a final decision."""
        print("on_final called")
        model = self.solver.model()

        self.active_edges = []
        for i in range(self.num_nodes):
            for j in range(self.num_nodes):
                if i != j:
                    u = Const(f"n{i}", self.Node)
                    v = Const(f"n{j}", self.Node)
                    if model.evaluate(self.edge(u, v), model_completion=True):
                        self.active_edges.append((i, j))

        print(f"Final active edges: {self.active_edges}")

        if not self.is_dag(self.active_edges):
            print("Graph is not a DAG")
            self.conflict()
        else:
            print("Graph is a DAG")

    def is_dag(self, edges):
        """Körmentesség ellenőrzése Kahn algoritmussal."""
        adj = {i: [] for i in range(self.num_nodes)}
        in_degree = {i: 0 for i in range(self.num_nodes)}

        for u, v in edges:
            adj[u].append(v)
            in_degree[v] += 1

        queue = [node for node in range(self.num_nodes) if in_degree[node] == 0]
        visited_count = 0

        while queue:
            current = queue.pop(0)
            visited_count += 1

            for neighbor in adj[current]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        return visited_count == self.num_nodes

    def add_at_least_one_edge_constraint(self):
        """Legalább egy él létezésének kényszere."""
        at_least_one_edge = []
        for i in range(self.num_nodes):
            for j in range(self.num_nodes):
                if i != j:
                    u = Const(f"n{i}", self.Node)
                    v = Const(f"n{j}", self.Node)
                    at_least_one_edge.append(self.edge(u, v))

        self.solver.add(Or(*at_least_one_edge))
        print("Constraint added: At least one edge must exist.")

    def add_minimum_connectivity_constraints(self):
        """Minden csúcsnak legyen legalább egy ki- vagy bemenő éle."""
        for i in range(self.num_nodes):
            outgoing_or_incoming = []
            for j in range(self.num_nodes):
                if i != j:
                    u = Const(f"n{i}", self.Node)
                    v = Const(f"n{j}", self.Node)
                    outgoing_or_incoming.append(self.edge(u, v))  # Kimenő él
                    outgoing_or_incoming.append(self.edge(v, u))  # Bemenő él
            self.solver.add(Or(*outgoing_or_incoming))
            print(f"Constraint added: Node {i} must have at least one edge.")

def main():
    num_nodes = 4
    solver = Solver()
    propagator = GraphUserPropagator(solver, num_nodes)

    nodes = [Const(f"n{i}", propagator.Node) for i in range(num_nodes)]

    # Páronként különböző csúcsok
    for i in range(num_nodes):
        for j in range(i + 1, num_nodes):
            solver.add(nodes[i] != nodes[j])

    # Legalább egy él létezzen
    propagator.add_at_least_one_edge_constraint()

    # Minden csúcsnak legyen legalább egy ki- vagy bemenő éle
    propagator.add_minimum_connectivity_constraints()

    if solver.check() == sat:
        print("SAT: Körmentes gráf található.")
    else:
        print("UNSAT: Nem található körmentes gráf.")

if __name__ == "__main__":
    main()
