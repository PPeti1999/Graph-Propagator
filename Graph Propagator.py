import pytest
from z3.z3 import *


class GraphConstraintPropagator:
    def __init__(self, solver, directed=False):
        self.solver = solver    #solver
        self.edges = []     #élek
        self.nodes = set()  #csomópont
        self.parent = {}    #szülő
        self.directed = directed        #Az self.directed általában a gráf inicializálásakor kerül beállításra, például az osztály hogy irányított e vagy nem
        self.graph = {} # gráf

    ###NINCS HASZNÁLVA
    ##A get_constraints függvény célja, hogy lekérdezze és visszaadja az összes olyan korlátozást (assertion), amelyet korábban hozzáadtak az SMT solverhez (pl. a z3.Solver-hez). 
    # Ezek a korlátozások a gráf működéséhez, tulajdonságaihoz vagy egyéb logikai szabályokhoz kapcsolódnak.
    def get_constraints(self):
        """Return all constraints added to the solver."""
        return list(self.solver.assertions())
    

    ####NINCS HASZNÁLVA
    #A set_directedness függvény a gráf irányítottságát állítja be:
    def set_directedness(self, directedness):
        if self.directed != directedness:
            self.directed = directedness


    ##add_node függvény egy csúcsot ad a gráfhoz, miközben ellenőrzi, hogy a csúcs érvényes-e és hogy még nem létezik a gráfban.
    def add_node(self, node):
        try:
            self.validate_node(node) #Ellenőrzi, hogy a csúcs megfelel-e az érvényességi szabályoknak a validate_node függvény segítségével.
        except ValueError as e:
            print(f"Exception while adding node: {e}")
        else:
            """Add a node to the graph."""
            self.nodes.add(node)    #Hozzáadja a csúcsot a gráf csúcsok halmazához (nodes).
            self.parent[node] = node    #A csúcsot saját magához rendeli szülőként, ezzel inicializálva a Union-Find struktúrát.

    ##Az add_edge függvény felelős egy él hozzáadásáért a gráfhoz. A következő fő funkciókat látja el:
    #Élek listájának frissítése: hozzáadja a (u,v) a gráf éleihez
    #Szomszédsági lista frissítése: Frissíti a gráf szomszédsági listáját u és v között kapcsolat legyen
    #Irányítatlan gráf kezelése: Ha a gráf nem irányított akk FALSE, ha az akkor az irányát is hozzáadja.
    def add_edge(self, u, v):
        self.edges.append((u, v))  # Az élt hozzáadja az osztály által tárolt élek listájához.
        if u not in self.graph:     #Ellenőrzi, hogy u benne van-e a gráf szomszédsági listájában: Ha nem, létrehoz egy üres listát neki.
            self.graph[u] = []
        self.graph[u].append(v) # u hoz hozzá adja v t jelezve h u->v

        if not self.directed:   #Ha a gráf irányítatlan FALSE 
            if v not in self.graph:
                self.graph[v] = []
            self.graph[v].append(u) #  hozzáadja a fordított irányú élt is v->u


    #############NINCS HASZNÁLVA
    #Gyökér keresése:A függvény megkeresi az adott csúcs (node) reprezentatívját (gyökerét) a Union-Find struktúrában.
    #Ha egy csúcs nem közvetlenül a gyökérhez kapcsolódik, a függvény rekurzívan meghívja önmagát, hogy megtalálja a gyökeret.
    #Az útvonal-tömörítés optimalizálja a struktúrát, mert minden csúcs közvetlenül a gyökérhez lesz kapcsolva, csökkentve a későbbi find hívások időigényét.
    def find(self, node):
        """Union-Find: Find the root of a node."""
        if self.parent[node] != node:
            self.parent[node] = self.find(self.parent[node])
        return self.parent[node]
    
    #############NINCS HASZNÁLVA
    #Két halmaz egyesítése:Megkeresi u és v gyökerét a find függvény segítségével.Ha a két gyökér különbözik, az egyik gyökér szülőjének beállítja a másik gyökeret,
    #  egyesítve ezzel a két halmazt.Egyesítés (Union):A két halmaz egyesítése biztosítja, hogy a gráf csúcsai ugyanabba az összefüggő komponensbe kerüljenek.
    def union(self, u, v):
        """Union-Find: Merge two sets."""
        root_u = self.find(u)
        root_v = self.find(v)
        if root_u != root_v:
            self.parent[root_u] = root_v

    #A propagate_rtc függvény az RTC (Reflexive-Transitive Closure) elvét valósítja meg egy gráfban:
    #Létrehozza a reflexív-tranzitív zárás logikai szabályait a gráf minden csúcsára és élére.
    #Ha azaz ha u->W és w->v akkor u->v is igaz
    def propagate_rtc(self):
        rtc_table = {(u, v): Bool(f'rtc_{u}_{v}') for u in self.nodes for v in self.nodes} #Létrehoz egy logikai táblázatot rtc_{u}_{v} amely azt jelöli, hogy van-e elérhetőség u bol v be.
        for u in self.nodes:    ##Minden csúcsra hozzáadja a reflexív elérhetőséget: Ez biztosítja, hogy minden csúcs elérje saját magát, ami a reflexivitás alapelve.
            for v in self.nodes:
                if u == v:
                    self.solver.add(rtc_table[u, v])  # Reflexivity
        for u, v in self.edges:  # Az élekhez tartozó közvetlen elérhetőséget hozzáadja a solverhez
            self.solver.add(rtc_table[u, v])

        for w in self.nodes:    #Hozzáadja a tranzitivitási szabályokat ha u->W és w->v akkor u->v is igaz
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(rtc_table[u, w], rtc_table[w, v]), rtc_table[u, v]))
        print(f"RTC propagation constraints added: {len(self.edges)} edges processed.")


    ##A _check_transitivity egy segédfüggvény, amely egy tranzitivitási feltételt állít elő három csúc (u,v,w) között.
    def _check_transitivity(self, u, v, w):
        """Add transitivity constraints to the solver."""
        rtc_u_w = Bool(f'rtc_{u}_{w}')
        rtc_w_v = Bool(f'rtc_{w}_{v}')
        rtc_u_v = Bool(f'rtc_{u}_{v}')
        return Implies(And(rtc_u_w, rtc_w_v), rtc_u_v)
    


    #2. Mit csinál a függvény?
    #A detect_transitivity_conflicts célja: A gráf tranzitivitási konfliktusainak detektálása.
    #Tranzitivitási szabályokat ad a solverhez:
    #A gráfban a csúcsok közötti tranzitív relációk (elérhetőségek vagy kapcsolatok) érvényesítésére.
    #Például: Ha azaz ha u->W és w->v akkor u->v is igaz
    #Konfliktusok detektálása:
    #Ellenőrzi, hogy ezek a tranzitivitási szabályok nem okoznak ellentmondást a meglévő gráfstruktúrában.
    #Ha a solver nem tudja kielégíteni a feltételt, egy hibát dob (ValueError), jelezve a konfliktust.
    ###
    #Tranzitivitási konfliktusokat szeretnél azonosítani.
    #A gráfban lévő szabályok közvetlen ellenőrzésére van szükséged.
    #A cél egy gráf konzisztenciájának ellenőrzése.
    def detect_transitivity_conflicts(self):
        """Add transitivity constraints for all nodes to the solver."""
        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:#Három beágyazott ciklussal minden lehetséges csúcs-párra (u,v) és egy köztes csúcsra (w) iterál.
                    constraint = self._check_transitivity(u, v, w)  #Meghívja a belső _check_transitivity metódust, amely a tranzitivitási szabályt állítja elő.
                    self.solver.add(constraint) #Hozzáadja a tranzitivitási szabályt a solver korlátozásaihoz.
                    if self.solver.check() == z3.unsat: #Ellenőrzi, hogy a solver kielégíthető-e az új feltétel mellett.Ha a solver nem kielégíthető (unsat), az azt jelenti, hogy ellentmondás van a gráfban
                        raise ValueError("Implicit transitivity conflict")
        print("Transitivity constraints added.")

    ########NINCS HASZNÁLVA
    #Mit csinál?
    #Dinamikusan létrehozott logikai vagy matematikai kifejezéseket regisztrál a solverben.
    #Cél: Lehetővé teszi, hogy futásidőben új feltételeket adjunk hozzá a problémához.
    def register_dynamic_term(self, term):
        """Register a dynamically created term."""
        print(f"Registering term dynamically: {term}")
        self.solver.add(term)

    ########NINCS HASZNÁLVA
    #Mit csinál?Egy adott csúcs (node) számára egy fixált értéket rendel hozzá (value).
    # Cél: Biztosítja, hogy a csúcs viselkedése megfeleljen a fix értéknek.
    def propagate_fixed_values(self, node, value):
        """Handle fixed value propagation dynamically."""
        print(f"Propagating fixed value for {node}: {value}")
        self.solver.add(Bool(f'fixed_{node}') == value)

    ########NINCS HASZNÁLVA
    #Mit csinál?
    #Olyan szabályt vezet be, hogy ha egy csúcs fixált, akkor legalább egy másik csúcsnak is fixáltnak kell lennie.
    #Cél: Megakadályozza, hogy csak egy csúcs legyen fixált a gráfban.
    def handle_fixed_assignments(self):
        """Handle assignments to fixed values dynamically."""
        for node in self.nodes:
            fixed = Bool(f'fixed_{node}')
            self.solver.add(Implies(fixed, Or([Bool(f'fixed_{other}') for other in self.nodes if other != node])))
        print("Fixed assignments constraints added.")
    
    ########NINCS HASZNÁLVA
    #Mit csinál?
    #k-lépéses dominanciát modellez:
    #Egy csúcs domináns, ha a gráfban legfeljebb k-lépésnyire található tőle más csúcsok.
    #Cél: Az irányított vagy irányítatlan gráfban domináns csúcsokat azonosít.
    #Fontosabb lépések:
    #Távolság-mátrix: Számolja a csúcsok közötti távolságot.
    #Dominancia: Minden csúcsnak van egy domináns csúcsa legfeljebb  k-lépésnyire.
    def propagate_k_hop_dominance(self, k):
        """Propagate k-hop dominance."""
        dominant = {node: Bool(f'dominant_{node}') for node in self.nodes}
        distance = {(u, v): Int(f'distance_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u in self.nodes:
            for v in self.nodes:
                if u == v:
                    self.solver.add(distance[u, v] == 0)
                else:
                    self.solver.add(distance[u, v] >= 0)

        for u, v in self.edges:
            self.solver.add(distance[u, v] == 1)

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(distance[u, v] <= distance[u, w] + distance[w, v])

        for node in self.nodes:
            self.solver.add(Or([And(dominant[n], distance[node, n] <= k) for n in self.nodes]))
    
    
    
    ########NINCS HASZNÁLVA       
    #Mit csinál?
    #Kiszámítja a gráf fa-mélységét (treedepth), amely a gráf hierarchikus szerkezetének maximális mélységét méri.
    #Cél: A gráf struktúrájának elemzése, például algoritmusok optimalizálása érdekében.
    #Fontosabb lépések:
    #Szülő-csúcsok: Minden csúcsnak van egy szülője parent).Mélység-számítás: A csúcsok mélységét (depth) rekurzívan határozza meg.
    #Maximális mélység: Meghatározza a gráf fa-mélységének maximális értékét.
    def compute_treedepth(self):
        """Compute the treedepth of the graph."""
        # Z3-kompatibilis változók definiálása
        parent = {node: Int(f'parent_{node}') for node in self.nodes}
        depth = {node: Int(f'depth_{node}') for node in self.nodes}

        # Parent és depth korlátozások definiálása
        for node in self.nodes:
            self.solver.add(depth[node] >= 0)  # Depth nem lehet negatív
            self.solver.add(Or([parent[node] == IntVal(-1)] + [parent[node] == parent[other] for other in self.nodes if other != node]))

        # Gyökércsúcsok mélységének beállítása
        for node in self.nodes:
            self.solver.add(Implies(parent[node] == IntVal(-1), depth[node] == 0))

        # Él alapú tranzitivitási korlátozások
        for u, v in self.edges:
            self.solver.add(Implies(parent[v] == parent[u], depth[v] == depth[u] + 1))

        # Maximális mélység kiszámítása Z3-kompatibilis módon
        max_depth = Int('max_depth')
        depth_list = [depth[node] for node in self.nodes]
        self.solver.add(max_depth >= 0)  # Mélység nem lehet negatív
        for d in depth_list:
            self.solver.add(max_depth >= d)  # max_depth legyen legalább akkora, mint bármelyik depth

        # Kiírás a konzolra
        if self.solver.check() == sat:
            model = self.solver.model()
            max_depth_value = model[max_depth].as_long()
            print(f"Maximum treedepth of the graph: {max_depth_value}")
        else:
            print("The solver could not find a solution.")

    ########NINCS HASZNÁLVA
    ##A propagate_union_distributive függvény egy gráf összetételét modellezi, különösen az elérhetőség (reachability) szempontjából, unió-disztributív tulajdonságokkal:
    #Meghatározza, hogy a gráf egy adott élén keresztül mely csúcsok érhetők el.
    #Tranzitív zárást alkalmaz az elérhetőségi relációra, azaz ha u->W és w->v akkor u->v is igaz
    #Ez a függvény különösen fontos, ha a gráfot olyan műveletek modelljére használjuk, ahol az egyesített elérhetőség disztributív tulajdonságokat mutat.
    ###
    ###Tipikus alkalmazási terület:
    #Gráfok kompozícióinak vizsgálata.
    #Hálózatok általános elérhetőségének modellezése.
    #Unió-disztributív tulajdonságok modellezése.
    def propagate_union_distributive(self):
        """Model graph composition with union-distributive properties."""
        reach = {(u, v): Bool(f'reach_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(reach[u, v])

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(reach[u, w], reach[w, v]), reach[u, v]))


    #### NINCS HASZNÁLVA
    ##A propagate_ifds függvény célja:Interprocedural Data Flow Analysis (IFDS) végrehajtása gráf alapú korlátozásokkal.
    # Adatáramlási szabályokat állít be a gráf csúcsai között,
    # hogy meghatározza, mely csúcsok között van adatáramlás.Az áramlásokat tranzitív módon terjeszti ki
    # ha u->W és w->v akkor u->v is igaz
    ###
    ##Tipikus alkalmazási terület:
    #Program analízis.
    #Adatáramlás követése.
    #üggőségek modellezése egy algoritmuson belül.
    def propagate_ifds(self):
        """Interprocedural data flow analysis using graph constraints."""
        flow = {(u, v): Bool(f'flow_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(flow[u, v])

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(flow[u, w], flow[w, v]), flow[u, v]))


    ######## NINCS HASZNÁLVA
    #A propagate_data_dependency_graph függvény egy súlyozott gráfot kezel, amely a adatfüggőségek elemzésére szolgál. 
    # A súlyozott gráfban az élek súlyokat kapnak, amelyek egy adott adatátvitel mértékét, kapacitását vagy más releváns tulajdonságát jelölik.
    # A függvény:Súlyokat rendel minden élhez.Biztosítja, hogy az élek súlyai nem negatívak.Korlátozást vezet be a csúcsokra, hogy az adategyensúly teljesüljön:
    # Az egy csúcsba belépő adatmennyiség (incomingincoming) megegyezzen az onnan kilépő adatmennyiséggel (outgoingoutgoing).
    def propagate_data_dependency_graph(self):
        """Handle data dependency analysis using weighted graphs."""
        weights = {(u, v): Int(f'weight_{u}_{v}') for u, v in self.edges}

        for (u, v), weight in weights.items():
            self.solver.add(weight >= 0)

        for node in self.nodes:
            incoming = Sum([weights[e] for e in self.edges if e[1] == node])
            outgoing = Sum([weights[e] for e in self.edges if e[0] == node])
            self.solver.add(incoming == outgoing)
    
    
    ############ NINCS HASZNÁLVA
    ###Az enforce_cycle_constraints függvény célja:Korlátozásokat vezet be a ciklusokra vonatkozóan egy gráfban.Biztosítja,
    #  hogy:Ha egy csúcs (𝑢u) látogatott, akkor az él célcsúcsa (𝑣v) is látogatott legyen.Megakadályozza, hogy a gráfban teljes ciklus alakuljon ki, amely minden csúcsot érint.
    def enforce_cycle_constraints(self):
        """Enforce constraints to prevent or allow specific cycles."""
        visited = {node: Bool(f'visited_{node}') for node in self.nodes}
        for u, v in self.edges:
            self.solver.add(Implies(visited[u], visited[v]))
        self.solver.add(Not(And([visited[node] for node in self.nodes])))  # Prevent full graph cycles


    ##########NINCS HASZNÁLVA
    #Az optimize_treewidth függvény egy gráf fa szélességének (treewidth) optimalizálását végzi. A treewidth a gráf egy tulajdonsága, amely a gráf fa-dekompozíciójának "szélességét" méri.
    #  A függvény a csúcsokhoz súlyokat rendel, majd korlátozásokat alkalmaz ezekre a súlyokra, hogy minimalizálja a treewidth-et.
    def optimize_treewidth(self):
        """Optimize treewidth with weighted nodes or edges."""
        weight = {node: Int(f'weight_{node}') for node in self.nodes}
        for node in self.nodes:
            self.solver.add(weight[node] >= 1)
        total_weight = Sum([weight[node] for node in self.nodes])
        self.solver.add(total_weight <= len(self.nodes))

    ####NINCS HASZNÁLVA
    ####A propagate_stateful_por függvény a Stateful Partial Order Reduction (POR) nevű technikát alkalmazza, amely a gráf optimalizálására és redundáns útvonalak csökkentésére szolgál. 
    # A függvény a gráf csúcsai és élei alapján logikai korlátozásokat vezet be, hogy minimalizálja az állapotok átfedését és biztosítsa a helyességet.
    def propagate_stateful_por(self):
        """Apply stateful partial order reduction (POR) constraints."""
        safe_set = {node: Bool(f'safe_{node}') for node in self.nodes}
        source_set = {node: Bool(f'source_{node}') for node in self.nodes}

        for u, v in self.edges:
            self.solver.add(Implies(safe_set[u], source_set[v]))

        # New logic for stateful POR based on dependency ordering
        for u, v in self.edges:
            if u != v:
                self.solver.add(Implies(source_set[u], Not(safe_set[v])))  # Avoid overlapping sources and safe sets

        # Ensure at least one safe node exists
        self.solver.add(Or([safe_set[node] for node in self.nodes]))  # At least one safe node
        print("Stateful partial order reduction constraints applied.")

    ##############NINCS HASZNÁLVA
    ##A propagate_dependency_graph egy függőségi gráf kezelésére szolgál:
    #Függőségi mátrixot hoz létre, amely azt mutatja, hogy egy adott csúcs (𝑢u) függ-e egy másik csúcstól (𝑣v).
    # Korlátozásokat ad hozzá a solverhez, amelyek biztosítják, hogy a függőségek szimmetrikusak (azaz ha 𝑢u függ 𝑣v-től, akkor 𝑣v is függ 𝑢u-tól).
    #Ez a függvény biztosítja, hogy a gráf megfeleljen az adott függőségi szabályoknak, és a solver segítségével ellenőrzi azok érvényességét.
    def propagate_dependency_graph(self):
        """Construct and validate dependencies using graph matrices."""
        dependency_matrix = {(u, v): Bool(f'dependency_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(dependency_matrix[u, v])

        for u in self.nodes:
            for v in self.nodes:
                self.solver.add(Implies(dependency_matrix[u, v], dependency_matrix[v, u]))  # Symmetric dependency

    ############ NINCS HASZNÁLVA
    #####Az optimize_sparsity függvény a gráf sűrűségének és ritkaságának (sparsity) optimalizálására szolgál. Ez azt jelenti, hogy:
    #Elemzi, hogy a gráf mennyire ritka (kevés él a csúcsok számához képest).
    #Korlátozásokat ad a solverhez, hogy minimalizálja az élek számát, miközben bizonyos tulajdonságok megmaradnak.
    #A ritkaságot a következő képlettel számítja ki irányítatlan gráfokra:  sparsity=|élek száma| -|csúcsok száma|+1
    def optimize_sparsity(self):
        """Leverage graph sparsity for optimization."""
        sparsity = Int('sparsity')
        edge_count = len(self.edges)
        node_count = len(self.nodes)

        # Existing sparsity formula
        self.solver.add(sparsity == edge_count - node_count + 1)  # Sparsity formula for undirected graphs
        self.solver.add(sparsity >= 0)# Ritkaság alsó korlátjának megadása

        # Advanced sparsity constraints (from the book) 
        #Sűrűség (density) kiszámítása
        density = Real('density')
        self.solver.add(density == edge_count / (node_count * (node_count - 1)))  # Density formula
        self.solver.add(density <= 1) #Biztosítja, hogy a sűrűség nem lehet nagyobb 1-nél (ami azt jelentené, hogy több él van, mint lehetséges).

        # Optimize sparsity with constraints on edge reduction
        #Mit csinál?
        #A ritkasági súlyt az élek számának összegzésével határozza meg.
        #Ez egyszerűen az élek száma.
        sparsity_weight = Int('sparsity_weight')
        self.solver.add(sparsity_weight == Sum([1 for (u, v) in self.edges]))
        ##Mit csinál?
        #Korlátozza a ritkasági súlyt úgy, hogy az ne haladja meg a csúcsok számát.
        #Miért fontos?
        #Ez minimalizálja az élek számát, miközben biztosítja, hogy a gráf ne legyen túlságosan ritka.
        # Add constraints for sparsity minimization
        self.solver.add(sparsity_weight <= node_count)  # Example constraint
        print("Advanced sparsity optimization constraints added.")


    #######NINCS HASZNÁLVA 
    ##A final_check a gráf élein keresztül végleges ellenőrzést végez, hogy az összes él elérhető e.
    def final_check(self):
        """Perform final validation of all constraints."""
        print("Performing final checks.")
        for u, v in self.edges:
            if not self._check_reachability(u, v):
                print(f"Conflict detected between nodes {u} and {v}.")
   
   
    ###NINCS HASZNÁLVA
    ##A _check_reachability függvény azt vizsgálja, hogy egy adott csúcs (v) elérhető-e egy másik csúcsból (u) a gráf élein keresztül.
    def _check_reachability(self, u, v):
        """Check if node v is reachable from node u."""
        visited = set()

        def dfs(node):
            if node == v:
                return True
            visited.add(node)
            for x, y in self.edges:
                if x == node and y not in visited:
                    if dfs(y):
                        return True
            return False

        return dfs(u)
    
    ## ELMENTI AZ AKTUÁLIS SOLVER STATET
    def push_state(self):
        """Push the current solver state."""
        self.solver.push()
        print("Solver state pushed.")
    
    ## ELDOBJA A MENTET SOLVER STATE-t
    def pop_state(self):
        """Pop the solver state."""
        self.solver.pop()
        print("Solver state popped.")
    
    
    
    ##### NINCS HASZNÁLVA DEBUGGOLÁSHOZ KELLET
    ##Az log_event egy egyszerű segédfüggvény, amely egy adott eseményt naplóz (logol) a hibaelhárítás (debugging) céljából. Az eseményt (egy szöveges üzenet vagy információ) a konzolra írja ki.
    def log_event(self, event):
        """Log an event for debugging purposes."""
        print(f"Event logged: {event}")
    
    
    #####NINCS HASZNÁLVA
    ##Ez a függvény egy új Z3 SMT solver példányt hoz létre és visszaadja azt. Az új solver teljesen független az aktuális solver állapotától, és egy különálló környezetként használható.
    def create_nested_solver(self):
        """Simulate nested solver creation."""
        nested_solver = Solver()
        print("Nested solver created.")
        return nested_solver
    
    
    ###############NINCS HASZNÁLVA
    ##egy egyszerű hibadiagnosztikai funkció, amely egy adott konfliktus okát magyarázza meg a felhasználónak, hogy Ha két csúcs nem elégiti ki a feltételt.
    def explain_conflict(self, u, v):
        """Explain the cause of a conflict."""
        print(f"Conflict: Path between {u} and {v} violates constraints.")


    
    #########################   FONTOS
    #Az explore_model célja, hogy a Z3 SMT solver által talált modellt megvizsgálja, és annak tartalmát megjelenítse. 
    # A modell a solver által kiszámított kielégítő értékek halmaza, amely megfelel az összes hozzáadott állításnak (assertion).
    def explore_model(self):
        """Explore the model of the solver."""
        if self.solver.check() == sat:
            model = self.solver.model()
            print("Model found:")
            for d in model.decls():
                print(f"{d.name()} = {model[d]}")
        else:
            print("No model found.")

    #############NINCS HASZNÁLVA
    #Ez a függvény a Z3 SMT solverhez ad hozzá egy vagy több logikai állítást (assertions), 
    # majd minden egyes állítás után ellenőrzi, hogy a meglévő korlátozásokkal együtt a gráf még mindig kielégíthető-e.
    #  Az add_assertions célja tehát az új állítások fokozatos hozzáadása a solverhez úgy, hogy közben meggyőződik azok érvényességéről.
    def add_assertions(self, *constraints):
        """Add multiple assertions to the solver."""
        for constraint in constraints:
            self.solver.add(constraint)
            if self.solver.check() == z3.unsat:
                raise ValueError("Constraint not satisfied.")
        print("Assertions added to the solver.")

    
    #függvény a gráf automatikus tesztelésére szolgál. Több lépést hajt végre:
    #1. Előkészíti a gráf transzitív tulajdonságait és konfliktusokat keres.
    #2. Elvégzi a Z3 SMT solver segítségével a gráf tulajdonságainak ellenőrzését.
    #További tesztek
    #4.Visszaállítja az állapotot, hogy a solver további változtatások nélkül folytatható legyen.
    def run_tests(self):
        """Run automated tests on the graph, including additional analysis."""
        print("\n \n Run automated tests on the graph...")
        if not hasattr(self, 'test_run_count'):
            self.test_run_count = 0
        self.test_run_count += 1
        print(f"run_tests has been called {self.test_run_count} times.")
        # 1. Solver állapot mentése
        self.push_state()  # Elmenti az aktuális solver állapotot.

        # 2. Alapvető RTC propagálás és tranzitivitási konfliktusok vizsgálata
        self.propagate_rtc()
        self.detect_transitivity_conflicts()
        # 4. Irányítottság ellenőrzése
        print(f"Graph is directed: {self.is_directed()}")

        # 5. Optimalizációs vizsgálatok
        self.optimize_sparsity()
        self.optimize_treewidth()


        # 6. Speciális propagálások és elemzések
        self.propagate_dependency_graph()
        self.propagate_stateful_por()
        self.propagate_data_dependency_graph()
        self.propagate_ifds()
        self.propagate_union_distributive()
        self.compute_treedepth()
        self.propagate_k_hop_dominance(k=2)

        # 7. Egyéb ellenőrzések
        self.final_check()

         # 7. Union-Find tesztelése
        if 'A' in self.nodes and 'B' in self.nodes:
            self.union('A', 'B')  # Összekapcsoljuk A és B csúcsokat
            print(f"Union-Find: Root of 'A' is {self.find('A')}")

        # 8. Debugging funkciók
        self.log_event("All tests executed.")
        nested_solver = self.create_nested_solver()
        print(f"Nested solver state: {nested_solver.check()}")

        # 9. Korlátozások hozzáadása és vizsgálata
        for constraint in self.get_constraints():
            self.solver.add(constraint)
        print(f"Solver state: {'satisfiable' if self.solver.check() == sat else 'unsatisfiable'}")

        # 10. Fixált értékek kezelése
        self.handle_fixed_assignments()
        # Dinamikus kifejezés helyes használata
        dynamic_term_example = Implies(Bool('rtc_A_B'), Bool('rtc_B_C'))

        # A dinamikus kifejezés regisztrálása
        self.register_dynamic_term(dynamic_term_example)
        self.propagate_fixed_values('A', True)

        # 11. Konfliktusok magyarázata (ha van)
        if self.solver.check() == unsat:
            self.explain_conflict('A', 'C')

        # 12. Solver állapot ellenőrzése
        result = self.solver.check()  # Az SMT solver ellenőrzi a korlátozásokat.
        print(f"Test result: {result}")

        # 13. Solver állapot visszaállítása
        self.pop_state()  # Visszaállítja az állapotot az utolsó mentésre.
        print("Automated tests on the graph its over...... \n \n \n")

    ##########NINCS HASZNÁLVA
    #Ez a függvény egyszerűen azt ellenőrzi, hogy a gráf irányított-e vagy sem
    def is_directed(self):
        """Check if the graph is directed."""
        return self.directed
    

    #Ez a függvény azt ellenőrzi, hogy egy gráf összefüggő-e, azaz minden csúcs elérhető-e a többi csúcsból. Az összefüggőség ellenőrzése a mélységi keresés (DFS) algoritmust használja.
    # Minden csúcs elérhető-e a gráf bármely más csúcsából.
    def is_connected(self):
        """Check if the graph is connected."""
        if not self.nodes:                                      #Ha a gráfban nincsenek csúcsok,akkor a gráf triviálisan összefüggő.
            return True  # An empty graph is trivially connected

        # Pick an arbitrary starting node
        start_node = next(iter(self.nodes)) #Kiválaszt egy tetszőleges kezdőcsúcsot a gráf csúcsai közül 
        visited = set()                     #A mélységi keresésnek szüksége van egy kezdőpontra, ahonnan elindulhat az elérhető csúcsok bejárása.

        def dfs(node):
            """Depth-first search to visit all reachable nodes."""
            if node in visited: #visited halmazba hozzáadja a jelenlegi csúcsot, jelezve, hogy azt már bejárta.
                return
            visited.add(node)
            for u, v in self.edges: #Végignézi a gráf minden élét
                if u == node and v not in visited: #Ha az aktuális csúcs u forrás a célcsúcs v rekurzívan bejárja.
                    dfs(v)
                elif v == node and u not in visited:#Ha az aktuális csúcs v forrás a célcsúcs u rekurzívan bejárja.
                    dfs(u)

        # Start DFS from the arbitrary node
        dfs(start_node)

        # The graph is connected if all nodes are visited
        return len(visited) == len(self.nodes)  # visited halmaz (bejárt csúcsok) mérete megegyezik-e a gráf csúcsainak számával.Ha minden csúcsot bejártunk, akkor a gráf összefüggő.
    

    #Ez a függvény azt ellenőrzi, hogy a gráf aciklikus-e, azaz tartalmaz nem tart köröket.
    #A ciklusok detektálására a mélységi keresést (DFS) használja, miközben egy rekurziós stack segítségével nyomon követi az aktuálisan bejárt útvonalat.
    def is_acyclic(self):
        """Check if the graph is acyclic using DFS."""
        visited = set()#Tartalmazza az összes olyan csúcsot, amelyet már teljesen bejártunk.
        stack = set()#Nyomon követi az aktuálisan bejárt útvonal csúcsait. Ez segít detektálni, ha a DFS egy olyan csúcsra tér vissza, amely már az aktuális útvonalon van (kört talál).

        def dfs(node):
            if node in stack:  # Ha a csúcs már az aktuális DFS hívási láncban szerepel (azaz a stack-ben van), akkor egy ciklust találtunk.
                return False
            if node in visited: #Ha a csúcs már szerepel a visited halmazban, az azt jelenti, hogy azt a csúcsot egy korábbi DFS futás már feldolgozta, így nincs szükség újra megvizsgálni.
                return True
            visited.add(node) #A csúcsot hozzáadja mind a visited, mind a stack halmazhoz, jelezve, hogy most kezdjük feldolgozni.
            stack.add(node)     #A csúcsot hozzáadja mind a visited, mind a stack halmazhoz, jelezve, hogy most kezdjük feldolgozni.

            for u, v in self.edges:     #Végignézi az összes él(u,v) Ha az él kiinduló csúcsa (U) megegyezik a jelenlegi csúccsal(node), akkor rekurzívan meghívja a DFS-t a célcsúcsra(v)
                if u == node and not dfs(v):
                    return False    #Ha bármelyik rekurzív hívás ciklust talál, azonnal false értékkel vissza tér.
            stack.remove(node)  #Miután az adott csúcsot teljesen feldolgozta, eltávolítja azt a stack ből  mivel már nem része az aktuális útvonalnak.
            return True

        for node in self.nodes:# A gráf minden csúcsára elindít egy DFS-t, amennyiben az adott csúcsot még nem látogattuk meg.
                                #Ha bármelyik DFS hívás ciklust talál, a függvény False értékkel tér vissza.
            if node not in visited:
                if not dfs(node):
                    return False
        return True #Ha az összes DFS hívás befejeződött ciklus találása nélkül, a gráf aciklikus, és a függvény True értéket ad vissza.
    #egyszerű gráf csekkolás
    def is_simple_graph(self):
        """Check if the graph is a simple graph (no loops, no multiple edges)."""
        edge_set = set()  # Tracks unique edges
        for u, v in self.edges:
            if u == v:  # Loops are not allowed #Nem tartalmaz hurokéleket (azaz egy csúcs nem kapcsolódhat saját magához u!=v)
                return False
            if self.directed:
                # For directed graphs, (u, v) is distinct from (v, u) #Nem tartalmaz többszörös éleket (azaz két csúcs között legfeljebb egy él lehet, irányított vagy irányítatlan esetben).
                if (u, v) in edge_set:
                    return False
                edge_set.add((u, v))
            else:
                # For undirected graphs, (u, v) is the same as (v, u) #Nem tartalmaz többszörös éleket (azaz két csúcs között legfeljebb egy él lehet, irányított vagy irányítatlan esetben).
                if (u, v) in edge_set or (v, u) in edge_set:
                    return False
                edge_set.add((u, v))
        return True

    #teljes gráf e ellenőrzés azazMinden csúcs közvetlenül össze van-e kötve minden más csúccsal egy éllel.
    #A teljes gráf élhálózatának számítása az n-től függ:Irányítatlan gráf esetén (n x (n-1))/2 és irányítottra  n x (n-1)
    def is_complete(self):
        n = len(self.nodes)  # Total number of nodes Meghatározza a gráfban található csúcsok számát
        # Calculate expected number of edges
        expected_edges = n * (n - 1)  # For directed graph Egy csúcsból az összes többi csúcsba mutathat él 
        if not self.directed:
            expected_edges //= 2  # For undirected graph    Mivel az élek mindkét irányban egyenértékűek, a várt élhálózatot megfelezi

        # Check if the number of edges matches Ellenőrzi, hogy a gráfban jelenleg tárolt élek száma megegyezik-e a várható élek számával.
        if len(self.edges) // (1 if self.directed else 2) != expected_edges:        
            return False #Azonnal visszatér False értékkel, mert nem lehet teljes gráf.

        # Verify all possible pairs of nodes are connectedMinden csúcs-párra (u,v) ellenőrzi hogy van e él közöttük.
        for u in self.nodes:
            for v in self.nodes:
                if u != v:
                    if self.directed:
                        # Check that both (u, v) exists
                        if (u, v) not in self.edges:
                            return False
                    else:
                        # Check that at least (u, v) exists (undirected case)
                        if (u, v) not in self.edges and (v, u) not in self.edges:
                            return False
        return True
    
    #Ez a függvény ellenőrzi, hogy egy csúcs (node) érvényes-e, mielőtt hozzáadnánk a gráfhoz. 
    # --Érvényes e a csúcs továbbá nincs e már benne ? --
    #Ellenőrzi, hogy a csúcs egész szám (int) vagy szöveg (str) típusú.
    #Érvényes: "A", "Node1", 123.
    #Érvénytelen: "!@#", None, []. alfanumerikusok
    def validate_node(self, node):
        if not isinstance(node, (int, str)) or not node.isalnum():
            raise ValueError("Node must be an integer or string.")
        if node in self.nodes:
            raise ValueError(f"Node {node} already exists.")

    ##########NINCS HASZNÁLVA
    #Ez a függvény ellenőrzi, hogy egy él (edge) érvényes-e, mielőtt hozzáadnánk a gráfhoz.
    #Ellenőrzi, hogy az él két végpontja (start és end) integer vagy string típusú.
    #Ellenőrzi, hogy az él kezdő- és végpontja létezik-e a gráfban.
    def validate_edge(self, start, end):
        if not isinstance(start, (int, str)) or not isinstance(end, (int, str)):
            raise ValueError("Edge must be made up of integer or string nodes.")
        if start not in self.nodes or end not in self.nodes:
            raise ValueError("Edge must start and end with existing nodes.")
    
    #Ellenőrzi, hogy a gráf teljes gráf-e, azaz minden csúcs össze van kötve minden másikkal.
    def test_complete(self, propagator):
        print("Checking complete graph...")
        if propagator.is_complete():
            print("The graph is complete.")
        else:
            print("The graph is not complete.")
     #Ellenőrzi, hogy a gráf egyszerű gráf-e, azaz nincs benne önhurok vagy többszörös él.
    def test_simple_graph(self, propagator):
        print("Checking simple graph...")
        if propagator.is_simple_graph():
            print("The graph is simple.")
        else:
            print("The graph is not simple.")
   
    #Ellenőrzi, hogy a gráf ciklikus-e, vagyis  tartalmaz-e köröket.
    def test_acyclicity(self, propagator):
        print("Checking acyclicity...")
        if propagator.is_acyclic():
            print("The graph is acyclic.")
        else:
            print("The graph has a cycle.")
    
    #Ellenőrzi, hogy egy gráf összefüggő-e, vagyis minden csúcs elérhető-e az összes többitől.
    def test_connectivity(self, propagator):
        print("Checking connectivity...")
        if propagator.is_connected():
            print("The graph is connected.")
        else:
            print("The graph is not connected.")


# Example usage
if __name__ == "__main__":
    # BAsic
    #solver = Solver()
    #prop = GraphConstraintPropagator(solver, True)

    #prop.add_node('A')
    #prop.add_node('B')
    #prop.add_node('C')
    #prop.add_edge('A', 'B')
    #prop.add_edge('B', 'C')
    #prop.add_edge('A', 'C')

    #prop.propagate_rtc()
    #prop.detect_transitivity_conflicts()
    #prop.propagate_fixed_values('A', True)
    #prop.register_dynamic_term(Bool('dynamic_term'))

    #prop.propagate_k_hop_dominance(2)
    #prop.handle_fixed_assignments()

    #prop.push_state()
    #prop.final_check()
    #prop.pop_state()

    # Demonstrate nested solver usage
    #nested_solver = prop.create_nested_solver()

    #result = solver.check()
    #print(f"Solver result: {result}")

    # Explore the model
    #prop.explore_model()

    # Run automated tests
    #prop.run_tests()

    # Add example assertions
    #prop.add_assertions(Bool('example_assertion_1'), Bool('example_assertion_2'))
    #result = solver.check()
    #print(f"Solver result after adding assertions: {result}")

    #s = Solver()
    #b = GraphConstraintPropagator(s)

    # Add nodes and edges
    #b.add_node('A')
    #b.add_node('B')
    #b.add_edge('A', 'B')

    # Add RTC constraints and SMT formulas
    #b.propagate_rtc()
    #s.add(Bool('example_assertion_1'))

    # Check satisfiability
    #print(s.check())

    solver = Solver()                            #Egy SMT solver példány, amely korlátozások ellenőrzésére szolgál (pl. z3 használatával).
    und_prop = GraphConstraintPropagator(solver) #Egy GraphConstraintPropagator példány, amely a gráf tulajdonságainak kezelésére és korlátozások kezelésére szolgál.

    # Define a graph
    und_prop.add_node('A')                      #Három csúcsot adunk hozzá a gráfhoz: add_node függvény biztosítja, hogy a csúcsok érvényesek és ne legyenek duplikáltak.
    und_prop.add_node('B')
    und_prop.add_node('C')
    und_prop.add_edge('A', 'B')                 #Élek definiálása.
    und_prop.add_edge('B', 'C')
    
    #und_prop.run_tests() #Automatized tests, prop_rtc és detect_trans.. ÖSSZES NEM HASZNÁLT FV IDE beágyazva majd állapot visszaállítása a rtc előtti állapotra.
    und_prop.add_edge('C', 'A')
    # Propagate RTC and check transitivity
    und_prop.propagate_rtc()                    #A Reflexive-Transitive Closure (RTC) szabályait alkalmazzuk a gráfra.
    und_prop.detect_transitivity_conflicts()    #Ellenőrzi, hogy a tranzitivitási szabályok ellentmondásba kerülnek-e a gráf meglévő szerkezetével.

    # Test connectivity and acyclicity
    und_prop.test_connectivity(und_prop)        #Minden csúcs elérhető-e bármely másik csúcsból.
    und_prop.test_acyclicity(und_prop)          #Ellenőrzi, hogy a gráf tartalmaz-e kört.
    und_prop.test_simple_graph(und_prop)        #Ellenőrzi, hogy a gráf egyszerű-e:Nincsenek hurok- vagy többszörös élek.
    und_prop.test_complete(und_prop)            #Ellenőrzi, hogy a gráf teljes-e:Egy teljes gráfban minden csúcs össze van kapcsolva minden más csúccsal. Az eredmény itt negatív lesz, mert nem minden csúcs között van él.

    # Explore the model
    print("Exploring the model:")
    und_prop.explore_model()                    # A solver által generált modellt vizsgálja.Ha a solver kielégítő (sat), megjeleníti az összes olyan változót (pl. rtc_), amelyek igaz értéket vesznek fel.
    #for constraint in und_prop.get_constraints(): #Lekérdezi az összes korlátozást, amelyet korábban definiáltunk, és hozzáadja őket a solverhez. Ez biztosítja, hogy minden korábban definiált szabály figyelembe legyen véve.
    #    solver.add(constraint)
    #solver.model
    # Summary
    print("\nSummary:")
    print(f"RTC constraints added: {len(und_prop.edges)} edges processed.") #Hány él került feldolgozásra az RTC szabályok alkalmazása során.
    print("Solver state: satisfiable" if solver.check() == sat else "Solver state: unsatisfiable")  #A solver állapotát (sat vagy unsat)
