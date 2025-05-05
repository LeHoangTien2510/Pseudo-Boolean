from math import inf
import time
from pysat.solvers import Glucose3
import sys

# Dữ liệu đầu vào cho Mertens
n = 7
m = 6
c = 18
time_list = [1, 5, 4, 3, 5, 6, 5]
W = [41, 21, 49, 23, 41, 17, 13]
adj = [(0, 1), (0, 3), (1, 2), (1, 4), (3, 6), (4, 5)]

# Khởi tạo các biến toàn cục
neighbors = [[0 for i in range(n)] for j in range(n)]
reversed_neighbors = [[0 for i in range(n)] for j in range(n)]
visited = [False for i in range(n)]
toposort = []
clauses = []

# Tạo đồ thị phụ thuộc
for a, b in adj:
    neighbors[a][b] = 1
    reversed_neighbors[b][a] = 1

def generate_variables(n, m, c):
    return [[j * m + i + 1 for i in range(m)] for j in range(n)], [[m * n + j * c + i + 1 for i in range(c)] for j in range(n)], [[m * n + c * n + j * c + i + 1 for i in range(c)] for j in range(n)]

def dfs(v):
    visited[v] = True
    for i in range(n):
        if neighbors[v][i] == 1 and not visited[i]:
            dfs(i)
    toposort.append(v)

def preprocess(n, m, c, time_list, adj):
    earliest_start = [[-9999999 for _ in range(m)] for _ in range(n)]
    latest_start = [[99999999 for _ in range(m)] for _ in range(n)]
    ip1 = [[0 for _ in range(m)] for _ in range(n)]
    ip2 = [[[0 for _ in range(c)] for _ in range(m)] for _ in range(n)]

    for i in range(n):
        if not visited[i]:
            dfs(i)
    toposort.reverse()

    for j in toposort:
        k = 0
        earliest_start[j][k] = 0
        for i in range(n):
            if neighbors[i][j] == 1:
                earliest_start[j][k] = max(earliest_start[j][k], earliest_start[i][k] + time_list[i])
                while earliest_start[j][k] > c - time_list[j]:
                    ip1[j][k] = 1
                    k += 1
                    if k < m:
                        earliest_start[j][k] = max(0, earliest_start[i][k] + time_list[i])
                    else:
                        break
                if k < m and earliest_start[j][k] <= c - time_list[j]:
                    for t in range(earliest_start[j][k]):
                        if ip2[j][k][t] == 0:
                            ip2[j][k][t] = 1

    toposort.reverse()
    for j in toposort:
        k = m - 1
        latest_start[j][k] = c - time_list[j]
        for i in range(n):
            if neighbors[j][i] == 1:
                latest_start[j][k] = min(latest_start[j][k], latest_start[i][k] - time_list[j])
                while latest_start[j][k] < 0:
                    ip1[j][k] = 1
                    k -= 1
                    if k >= 0:
                        latest_start[j][k] = min(c - time_list[j], latest_start[i][k] - time_list[j])
                    else:
                        break
                if k >= 0 and latest_start[j][k] >= 0:
                    for t in range(latest_start[j][k] + 1, c):
                        if ip2[j][k][t] == 0:
                            ip2[j][k][t] = 1

    return ip1, ip2

def generate_clauses(n, m, c, time_list, adj, ip1, ip2):
    clauses.clear()  # Xóa clauses để đảm bảo không bị trùng lặp
    # Ràng buộc 1: Mỗi task phải được gán cho một máy
    for j in range(n):
        constraint = [X[j][k] for k in range(m) if ip1[j][k] == 0]
        clauses.append(constraint)

    # Ràng buộc 2: Mỗi task chỉ được gán cho một máy
    for j in range(n):
        for k1 in range(m - 1):
            for k2 in range(k1 + 1, m):
                if ip1[j][k1] == 1 or ip1[j][k2] == 1:
                    continue
                clauses.append([-X[j][k1], -X[j][k2]])

    # Ràng buộc 3: Tuân thủ thứ tự ưu tiên
    for a, b in adj:
        for k in range(m - 1):
            for h in range(k + 1, m):
                if ip1[b][k] == 1 or ip1[a][h] == 1:
                    continue
                clauses.append([-X[b][k], -X[a][h]])

    # Ràng buộc 4: Mỗi task phải bắt đầu tại một thời điểm
    for j in range(n):
        clauses.append([S[j][t] for t in range(c - time_list[j] + 1)])

    # Ràng buộc 5: Mỗi task chỉ được bắt đầu tại một thời điểm
    for j in range(n):
        for t1 in range(c - time_list[j]):
            for t2 in range(t1 + 1, c - time_list[j] + 1):
                clauses.append([-S[j][t1], -S[j][t2]])

    # Ràng buộc 6: Task không thể bắt đầu khi không đủ thời gian
    for j in range(n):
        for t in range(c - time_list[j] + 1, c):
            clauses.append([-S[j][t]])

    # Ràng buộc 7: Hai task không thể chạy cùng lúc trên một máy
    for i in range(n - 1):
        for j in range(i + 1, n):
            for k in range(m):
                if ip1[i][k] == 1 or ip1[j][k] == 1:
                    continue
                for t in range(c):
                    clauses.append([-X[i][k], -X[j][k], -A[i][t], -A[j][t]])

    # Ràng buộc 8: Liên kết thời điểm bắt đầu và thời gian hoạt động
    for j in range(n):
        for t in range(c - time_list[j] + 1):
            for l in range(time_list[j]):
                if time_list[j] >= c / 2 and c - time_list[j] <= t + l < time_list[j]:
                    continue
                clauses.append([-S[j][t], A[j][t + l]])

    # Ràng buộc 9: Tuân thủ thứ tự trên cùng máy
    for i, j in adj:
        for k in range(m):
            if ip1[i][k] == 1 or ip1[j][k] == 1:
                continue
            for t1 in range(c - time_list[i] + 1):
                for t2 in range(c - time_list[j] + 1):
                    if ip2[i][k][t1] == 1 or ip2[j][k][t2] == 1:
                        continue
                    if t1 > t2:
                        clauses.append([-X[i][k], -X[j][k], -S[i][t1], -S[j][t2]])

    # Ràng buộc 10 & 11: Loại bỏ các gán không khả thi
    for j in range(n):
        for k in range(m):
            if ip1[j][k] == 1:
                clauses.append([-X[j][k]])
                continue
            for t in range(c - time_list[j] + 1):
                if ip2[j][k][t] == 1:
                    clauses.append([-X[j][k], -S[j][t]])

    # Ràng buộc 12: Task dài phải hoạt động ở giữa chu kỳ
    for j in range(n):
        if time_list[j] >= c / 2:
            for t in range(c - time_list[j], time_list[j]):
                clauses.append([A[j][t]])

    return clauses

def solve(solver):
    if solver.solve():
        return solver.get_model()
    return None

def get_value(solution):
    if solution is None:
        return 100, []
    x = [[solution[j * m + i] for i in range(m)] for j in range(n)]
    s = [[solution[m * n + j * c + i] for i in range(c)] for j in range(n)]
    a = [[solution[m * n + c * n + j * c + i] for i in range(c)] for j in range(n)]
    value = 0
    for t in range(c):
        tmp = 0
        for j in range(n):
            if a[j][t] > 0:
                for l in range(max(0, t - time_list[j]), t + 1):
                    if s[j][l] > 0:
                        tmp += W[j]
                        break
        value = max(value, tmp)
    return value, []

def optimal_with_pbo(X, S, A, n, m, c, sol, solbb, start_time):
    ip1, ip2 = preprocess(n, m, c, time_list, adj)
    clauses = generate_clauses(n, m, c, time_list, adj, ip1, ip2)

    # Bước 1: Giải ban đầu với SAT solver
    solver = Glucose3()
    for clause in clauses:
        solver.add_clause(clause)
    model = solve(solver)
    if model is None:
        print("No initial solution found")
        return None, 0, 0, 0, 0

    best_solution = model
    initial_value, _ = get_value(model)
    best_value = initial_value
    sol = 1
    solbb = 1

    print(f"Initial peak value: {best_value}")

    # Bước 2: Chuyển sang PBO và lặp
    W_max = m * n + 2 * c * n + 1
    while True:
        sol += 1
        current_time = time.time()
        if current_time - start_time >= 3600:
            print("Time out")
            break

        # Tạo mô hình PBO
        pbo_clauses = clauses.copy()
        for t in range(c):
            active_tasks = [A[j][t] for j in range(n)]
            pbo_clauses.append(active_tasks + [-W_max])

        solver = Glucose3()
        for clause in pbo_clauses:
            solver.add_clause(clause)

        # Giải PBO với giả định W_max nhỏ hơn best_value
        found_better = False
        for i in range(best_value - 1, 0, -1):  # Thử các giá trị nhỏ hơn best_value
            solver = Glucose3()
            for clause in pbo_clauses:
                solver.add_clause(clause)
            # Tạo giả định để W_max <= i
            assumptions = []
            for t in range(c):
                active_tasks = [A[j][t] for j in range(n)]
                power = sum(W[j] for j in range(n) if model[A[j][t] - 1] > 0)
                if power > i:
                    assumptions.extend([-lit for lit in active_tasks])
            if solver.solve(assumptions=assumptions):
                model = solver.get_model()
                value, _ = get_value(model)
                if value < best_value:
                    best_value = value
                    best_solution = model
                    solbb = sol
                    print(f"New peak value: {best_value}")
                    found_better = True
                    break
        if not found_better:
            print("Unsat or no better solution")
            break

    return best_solution, sol, solbb, best_value

# Chạy chương trình
X, S, A = generate_variables(n, m, c)
val = max(max(row) for row in A)
start_time = time.time()
sol = 0
solbb = 0
solution, sol, solbb, solval = optimal_with_pbo(X, S, A, n, m, c, sol, solbb, start_time)
end_time = time.time()

# Lưu giá trị gốc của sys.stdout
original_stdout = sys.stdout

# Ghi kết quả vào file
if solution is not None:
    with open("output.txt", "a") as output_file:
        sys.stdout = output_file
        print("Dataset: Mertens", file=output_file)
        print("#Var:", val, file=output_file)
        print("#Cons:", len(clauses), file=output_file)
        print("Peak:", solval, file=output_file)
        print("#Sol:", sol, file=output_file)
        print("#SolBB:", solbb, file=output_file)
        print(f"Time taken: {end_time - start_time} seconds", file=output_file)
        print(" ", file=output_file)

    # Khôi phục sys.stdout về console
    sys.stdout = original_stdout

    # In kết quả ra console
    print("Dataset: Mertens")
    print("#Var:", val)
    print("#Cons:", len(clauses))
    print("Peak:", solval)
    print("#Sol:", sol)
    print("#SolBB:", solbb)
    print(f"Time taken: {end_time - start_time} seconds")
else:
    print("No solution found")