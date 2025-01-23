from z3.z3 import *


def is_complete_or_acyclic(num_vertices, edges_input):
    # Create Z3 solver
    solver = Solver()

    # Boolean variables for edges
    edges = {}
    for i in range(num_vertices):
        for j in range(i + 1, num_vertices):  # Only upper triangle for undirected graph
            edges[(i, j)] = Bool(f"edge_{i}_{j}")

    # Add input edges to the solver
    for (i, j) in edges_input:
        solver.add(edges[(min(i, j), max(i, j))] == True)

    # Completeness constraint: All possible edges must exist
    def is_complete():
        complete_solver = Solver()
        for i in range(num_vertices):
            for j in range(i + 1, num_vertices):
                # Add constraints that every edge between two vertices must exist
                complete_solver.add(edges[(i, j)] == True)

        # Check if the graph satisfies completeness
        if complete_solver.check() == sat:
            return True
        return False

    # Acyclicity constraint: No cycles
    def is_acyclic():
        acyclic_solver = Solver()

        # Use symbolic reachability to enforce no cycles
        reachable = [[Bool(f"reachable_{i}_{j}") for j in range(num_vertices)] for i in range(num_vertices)]

        # Define reachability: A node is reachable from itself
        for i in range(num_vertices):
            acyclic_solver.add(reachable[i][i] == True)

        # Define reachability: If there's an edge between i and j, they are reachable
        for i in range(num_vertices):
            for j in range(i + 1, num_vertices):
                acyclic_solver.add(Implies(edges[(i, j)], And(reachable[i][j], reachable[j][i])))

        # Define transitivity of reachability: If i->j and j->k, then i->k
        for i in range(num_vertices):
            for j in range(num_vertices):
                for k in range(num_vertices):
                    acyclic_solver.add(Implies(And(reachable[i][j], reachable[j][k]), reachable[i][k]))

        # Prevent cycles: If two nodes are reachable from each other, they must not form a cycle
        for i in range(num_vertices):
            for j in range(i + 1, num_vertices):
                acyclic_solver.add(Implies(And(reachable[i][j], reachable[j][i]), Not(edges[(i, j)])))

        # Check if all constraints for acyclicity are satisfied
        if acyclic_solver.check() == sat:
            return True
        return False

    # Check for completeness
    if is_complete():
        print("The graph is complete.")
        return True

    # Check for acyclicity
    if is_acyclic():
        print("The graph is acyclic.")
        return True

    # If neither, print the result
    print("The graph is neither complete nor acyclic.")
    return False


if __name__ == "__main__":
    # Example Usage
    num_vertices = 5
    edges_input = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]  # Modify this as a random graph
    is_complete_or_acyclic(num_vertices, edges_input)
