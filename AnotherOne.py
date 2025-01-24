from z3.z3 import *


class KahnUserPropagator(UserPropagateBase):
    def __init__(self, solver, num_nodes, ctx=None):
        UserPropagateBase.__init__(self, solver, ctx)
        self.num_nodes = num_nodes

        # Declare a sort for the nodes of the graph
        self.Node = DeclareSort("Node")
        self.edge = Function("edge", self.Node, self.Node, BoolSort())

        # Register callbacks
        self.add_fixed(self.on_fixed)
        self.add_final(self.on_final)

    def on_fixed(self, fixed):
        """Callback triggered when a variable is fixed."""
        pass  # No action needed for individual fixed variables in this implementation

    def on_final(self):
        """Callback triggered when the solver reaches a final decision."""
        solver = self.ctx_ref().solver()  # Access the solver's model
        model = solver.model()

        # Collect active edges from the model
        active_edges = []
        for i in range(self.num_nodes):
            for j in range(self.num_nodes):
                u = Const(f"n{i}", self.Node)
                v = Const(f"n{j}", self.Node)
                if model.evaluate(self.edge(u, v), model_completion=True):
                    active_edges.append((i, j))

        # Check if the graph described by active_edges is a DAG
        if not self.is_dag(active_edges):
            # Report a conflict if the graph is not a DAG
            self.conflict()

    def is_dag(self, edges):
        """Checks if a graph with the given edges is a DAG using Kahn's algorithm."""
        # Step 1: Build adjacency list and in-degree map
        adj = {i: [] for i in range(self.num_nodes)}
        in_degree = {i: 0 for i in range(self.num_nodes)}

        for u, v in edges:
            adj[u].append(v)
            in_degree[v] += 1

        # Step 2: Initialize a queue with nodes that have in-degree 0
        queue = [node for node in range(self.num_nodes) if in_degree[node] == 0]

        # Step 3: Process nodes in topological order
        visited_count = 0
        while queue:
            current = queue.pop(0)
            visited_count += 1

            for neighbor in adj[current]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        # If visited_count equals the number of nodes, it's a DAG
        return visited_count == self.num_nodes


# Example usage
def main():
    num_nodes = 4
    solver = Solver()  # Use the context for the solver
    propagator = KahnUserPropagator(solver, num_nodes)

    # Add node constraints dynamically
    nodes = [Const(f"n{i}", propagator.Node) for i in range(num_nodes)]
    for i in range(num_nodes):
        for j in range(num_nodes):
            if i != j:
                solver.add(Or(propagator.edge(nodes[i], nodes[j]), Not(propagator.edge(nodes[i], nodes[j]))))

    # The propagator is already linked to the solver since they share the same context
    if solver.check() == sat:
        print("The graph is a DAG.")
    else:
        print("The graph is not a DAG.")


if __name__ == "__main__":
    main()
