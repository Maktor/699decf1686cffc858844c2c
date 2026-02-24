import z3
import time

def solve_slitherlink():
    print("Setting up the Slitherlink grid and constraints...")
    
    grid_data = [
        "3  2 22  2  2  23 2 ",
        "3 3   1    11 23  0 ",
        " 123 31 1 2 2 2 2   ",
        "3 2    2 33    3  2",
        "  1 3 2 02   23  2  ",
        "223    2     2  1   ",
        " 1 222 1  32   3 3 3",
        "22 2   3 3   32    3",
        " 22  1    120 1 3 3 ",
        "2  2 3 3 2   3      ",
        "  21  1   211  3 3 3",
        "3   222  1    231 1 ",
        "   1    3232 11 11 2",
        "3  11    1213   22  ",
        "212 13 2   3   22 3 ",
        " 3      3121321     ",
        "2  2  2    23 2  3 3",
        "  2      22  3  2  ",
        " 122222 321  2  23 3",
        "233   3 23 3   2 22 "
    ]
    
    grid = [row.ljust(20, ' ') for row in grid_data]
    H = len(grid)
    W = len(grid[0])

    s = z3.Solver()

    H_e = [[z3.Bool(f"H_{r}_{c}") for c in range(W)] for r in range(H + 1)]
    V_e = [[z3.Bool(f"V_{r}_{c}") for c in range(W + 1)] for r in range(H)]

    for r in range(H):
        for c in range(W):
            ch = grid[r][c]
            if ch in '0123':
                num = int(ch)
                edges = [H_e[r][c], H_e[r+1][c], V_e[r][c], V_e[r][c+1]]
                s.add(z3.Sum([z3.If(e, 1, 0) for e in edges]) == num)

    Active = [[z3.Bool(f"A_{r}_{c}") for c in range(W + 1)] for r in range(H + 1)]
    for r in range(H + 1):
        for c in range(W + 1):
            incident = []
            if c < W: incident.append(H_e[r][c])
            if c > 0: incident.append(H_e[r][c-1])
            if r < H: incident.append(V_e[r][c])      
            if r > 0: incident.append(V_e[r-1][c])     
            
            degree = z3.Sum([z3.If(e, 1, 0) for e in incident])
            s.add(degree == z3.If(Active[r][c], 2, 0))

    flow_H_R = [[z3.Int(f"fHR_{r}_{c}") for c in range(W)] for r in range(H + 1)]
    flow_H_L = [[z3.Int(f"fHL_{r}_{c}") for c in range(W)] for r in range(H + 1)]
    flow_V_D = [[z3.Int(f"fVD_{r}_{c}") for c in range(W + 1)] for r in range(H)]
    flow_V_U = [[z3.Int(f"fVU_{r}_{c}") for c in range(W + 1)] for r in range(H)]

    MaxFlow = (H + 1) * (W + 1)
    
    for r in range(H + 1):
        for c in range(W):
            s.add(flow_H_R[r][c] >= 0, flow_H_L[r][c] >= 0)
            s.add(z3.Implies(z3.Not(H_e[r][c]), flow_H_R[r][c] == 0))
            s.add(z3.Implies(z3.Not(H_e[r][c]), flow_H_L[r][c] == 0))
            s.add(flow_H_R[r][c] + flow_H_L[r][c] <= MaxFlow)

    for r in range(H):
        for c in range(W + 1):
            s.add(flow_V_D[r][c] >= 0, flow_V_U[r][c] >= 0)
            s.add(z3.Implies(z3.Not(V_e[r][c]), flow_V_D[r][c] == 0))
            s.add(z3.Implies(z3.Not(V_e[r][c]), flow_V_U[r][c] == 0))
            s.add(flow_V_D[r][c] + flow_V_U[r][c] <= MaxFlow)

    Source = [[z3.Bool(f"S_{r}_{c}") for c in range(W + 1)] for r in range(H + 1)]
    s.add(z3.Sum([z3.If(Source[r][c], 1, 0) for r in range(H + 1) for c in range(W + 1)]) == 1)

    TotalActive = z3.Sum([z3.If(Active[r][c], 1, 0) for r in range(H + 1) for c in range(W + 1)])

    for r in range(H + 1):
        for c in range(W + 1):
            s.add(z3.Implies(Source[r][c], Active[r][c]))
            
            flow_out = 0
            flow_in = 0
            
            if c < W: 
                flow_out += flow_H_R[r][c]; flow_in += flow_H_L[r][c]
            if c > 0:
                flow_out += flow_H_L[r][c-1]; flow_in += flow_H_R[r][c-1]
            if r < H:
                flow_out += flow_V_D[r][c]; flow_in += flow_V_U[r][c]
            if r > 0:
                flow_out += flow_V_U[r-1][c]; flow_in += flow_V_D[r-1][c]
                
            net_flow = flow_out - flow_in
            s.add(net_flow == z3.If(Source[r][c], TotalActive - 1, z3.If(Active[r][c], -1, 0)))

    print("Solving... (This may take roughly 10-60 seconds due to grid size)")
    start_time = time.time()
    
    if s.check() == z3.sat:
        m = s.model()
        print(f"Solution found in {time.time() - start_time:.2f} seconds!\n")
      
        bottom_row_idx = H - 1
        inside_numbers = []
        
        for c in range(W):
            ch = grid[bottom_row_idx][c]
            if ch in '0123':
                crossings = sum(1 for k in range(c + 1) if z3.is_true(m[V_e[bottom_row_idx][k]]))
                if crossings % 2 == 1:
                    inside_numbers.append(ch)
                    
        print("-" * 50)
        print("Final Answer (Numbers in the bottom row that are INSIDE the loop):")
        print(", ".join(inside_numbers))
        print("-" * 50)
    else:
        print("No solution found. Check grid logic.")

if __name__ == "__main__":
    solve_slitherlink()
