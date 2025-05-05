from math import inf
import re
import time
import sys
from pysat.formula import WCNF
from pysat.card import CardEnc, EncType
from pysat.pb import PBEnc
from pysat.examples.rc2 import RC2
import fileinput
from tabulate import tabulate
import webbrowser

# Các biến đầu vào mặc định
n = 28  # Số task
m = 3  # Số máy
c = 342  # Số đơn vị thời gian (cycle)
val = 0
cons = 0
sol = 0
solbb = 0
type = 2

# Danh sách các file đầu vào
file = ["MITCHELL.IN2", "MERTENS.IN2", "BOWMAN.IN2", "ROSZIEG.IN2", "BUXEY.IN2",
        "HESKIA.IN2", "SAWYER.IN2", "JAESCHKE.IN2", "MANSOOR.IN2", "JACKSON.IN2", "GUNTHER.IN2"]
filename = file[5]  # Chọn file HESKIA.IN2

fileName = filename.split(".")

# Đọc thông tin về trọng số công việc từ file
with open('task_power/' + fileName[0] + '.txt', 'r') as file:
    W = [int(line.strip()) for line in file]

# Khởi tạo các ma trận và danh sách
neighbors = [[0 for i in range(n)] for j in range(n)]
reversed_neighbors = [[0 for i in range(n)] for j in range(n)]
visited = [False for i in range(n)]
toposort = []
adj = []
time_list = []


def input():
    """Đọc dữ liệu đầu vào từ file."""
    cnt = 0
    for line in fileinput.input(filename):
        line = line.strip()
        if line:
            if cnt == 0:
                n = int(line)
            elif cnt <= n:
                time_list.append(int(line))
            else:
                line = line.split(",")
                if (line[0] != "-1" and line[1] != "-1"):
                    adj.append([int(line[0]) - 1, int(line[1]) - 1])
                    neighbors[int(line[0]) - 1][int(line[1]) - 1] = 1
                    reversed_neighbors[int(line[1]) - 1][int(line[0]) - 1] = 1
                else:
                    break
            cnt = cnt + 1


def generate_variables(n, m, c):
    """Tạo các biến quyết định cho bài toán."""
    return [[j * m + i + 1 for i in range(m)] for j in range(n)], \
        [[m * n + j * c + i + 1 for i in range(c)] for j in range(n)], \
        [[m * n + c * n + j * c + i + 1 for i in range(c)] for j in range(n)]


def dfs(v):
    """Thuật toán DFS để tìm thứ tự tô-pô."""
    visited[v] = True
    for i in range(n):
        if (neighbors[v][i] == 1 and visited[i] == False):
            dfs(i)
    toposort.append(v)


def preprocess(n, m, c, time_list, adj):
    """Tiền xử lý để giảm không gian tìm kiếm."""
    earliest_start = [[-9999999 for _ in range(m)] for _ in range(n)]
    latest_start = [[99999999 for _ in range(m)] for _ in range(n)]
    ip1 = [[0 for _ in range(m)] for _ in range(n)]
    ip2 = [[[0 for _ in range(c)] for _ in range(m)] for _ in range(n)]

    # Tính thời điểm bắt đầu sớm nhất có thể
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
                while (earliest_start[j][k] > c - time_list[j]):
                    ip1[j][k] = 1  # Đánh dấu (task j, máy k) không khả thi
                    k = k + 1
                    earliest_start[j][k] = max(0, earliest_start[i][k] + time_list[i])

                if earliest_start[j][k] <= c - time_list[j]:
                    for t in range(earliest_start[j][k]):
                        if (ip2[j][k][t] == 0):
                            ip2[j][k][t] = 1  # Đánh dấu (task j, máy k, thời điểm t) không khả thi

    # Tính thời điểm bắt đầu muộn nhất có thể
    toposort.reverse()
    for j in toposort:
        k = m - 1
        latest_start[j][k] = c - time_list[j]
        for i in range(n):
            if (neighbors[j][i] == 1):
                latest_start[j][k] = min(latest_start[j][k], latest_start[i][k] - time_list[j])
                while (latest_start[j][k] < 0):
                    ip1[j][k] = 1  # Đánh dấu (task j, máy k) không khả thi
                    k = k - 1
                    latest_start[j][k] = min(c - time_list[j], latest_start[i][k] - time_list[j])

                if (latest_start[j][k] >= 0):
                    for t in range(latest_start[j][k] + 1, c):
                        if (ip2[j][k][t] == 0):
                            ip2[j][k][t] = 1  # Đánh dấu (task j, máy k, thời điểm t) không khả thi

    return ip1, ip2


def generate_pbo_model(X, S, A, n, m, c, time_list, adj, ip1, ip2):
    """Tạo mô hình PBO (Pseudo-Boolean Optimization) với Sequential Counter."""
    wcnf = WCNF()
    clauses = []
    top_weight = 1000000  # Trọng số cho các ràng buộc cứng

    # --- Phần 1: Các ràng buộc cứng ---

    # Ràng buộc 1: Mỗi task phải được gán cho một máy (sử dụng Sequential Counter)
    for j in range(n):
        valid_machines = [X[j][k] for k in range(m) if ip1[j][k] == 0]
        if valid_machines:  # Nếu danh sách không rỗng
            card = CardEnc.equals(lits=valid_machines, bound=1,
                                  encoding=0)
            for clause in card.clauses:
                wcnf.append(clause, weight=top_weight)

    # Ràng buộc 2: Mỗi task chỉ được gán cho một máy (mặc dù Sequential Counter đã đảm bảo điều này)
    # Giữ lại để đảm bảo đủ các ràng buộc
    for j in range(n):
        for k1 in range(m - 1):
            for k2 in range(k1 + 1, m):
                if ip1[j][k1] == 1 or ip1[j][k2] == 1:
                    continue
                wcnf.append([-X[j][k1], -X[j][k2]], weight=top_weight)

    # Ràng buộc 3: Tuân thủ thứ tự ưu tiên trong task (nếu a -> b thì b không thể gán cho máy có số hiệu nhỏ hơn a)
    for a, b in adj:
        for k in range(m - 1):
            for h in range(k + 1, m):
                if ip1[b][k] == 1 or ip1[a][h] == 1:
                    continue
                wcnf.append([-X[b][k], -X[a][h]], weight=top_weight)

    # Ràng buộc 4: Mỗi task phải được bắt đầu tại một thời điểm (sử dụng Sequential Counter)
    for j in range(n):
        valid_start_times = [S[j][t] for t in range(c - time_list[j] + 1)]
        if valid_start_times:
            card = CardEnc.equals(lits=valid_start_times, bound=1,
                                  encoding=0)
            for clause in card.clauses:
                wcnf.append(clause, weight=top_weight)

    # Ràng buộc 5: Mỗi task chỉ được bắt đầu tại một thời điểm
    for j in range(n):
        for t1 in range(c - time_list[j]):
            for t2 in range(t1 + 1, c - time_list[j] + 1):
                wcnf.append([-S[j][t1], -S[j][t2]], weight=top_weight)

    # Ràng buộc 6: Task không thể bắt đầu khi không còn đủ thời gian để hoàn thành
    for j in range(n):
        for t in range(c - time_list[j] + 1, c):
            wcnf.append([-S[j][t]], weight=top_weight)

    # Ràng buộc 7: Hai task khác nhau không thể cùng chạy trên một máy tại cùng thời điểm
    for i in range(n - 1):
        for j in range(i + 1, n):
            for k in range(m):
                if ip1[i][k] == 1 or ip1[j][k] == 1:
                    continue
                for t in range(c):
                    wcnf.append([-X[i][k], -X[j][k], -A[i][t], -A[j][t]], weight=top_weight)

    # Ràng buộc 8: Liên kết giữa thời điểm bắt đầu và thời gian hoạt động của task
    for j in range(n):
        for t in range(c - time_list[j] + 1):
            for l in range(time_list[j]):
                if time_list[j] >= c / 2 and t + l >= c - time_list[j] and t + l < time_list[j]:
                    continue
                wcnf.append([-S[j][t], A[j][t + l]], weight=top_weight)

    # Ràng buộc 9: Tuân thủ ràng buộc thứ tự giữa các task
    for i, j in adj:
        for k in range(m):
            if ip1[i][k] == 1 or ip1[j][k] == 1:
                continue
            for t1 in range(c - time_list[i] + 1):
                for t2 in range(c - time_list[j] + 1):
                    if ip2[i][k][t1] == 1 or ip2[j][k][t2] == 1:
                        continue
                    if t1 > t2:
                        wcnf.append([-X[i][k], -X[j][k], -S[i][t1], -S[j][t2]], weight=top_weight)

    # Ràng buộc 10 & 11: Loại bỏ các gán không khả thi từ tiền xử lý
    for j in range(n):
        for k in range(m):
            if ip1[j][k] == 1:
                wcnf.append([-X[j][k]], weight=top_weight)
                continue
            for t in range(c - time_list[j] + 1):
                if ip2[j][k][t] == 1:
                    wcnf.append([-X[j][k], -S[j][t]], weight=top_weight)

    # Ràng buộc 12: Ràng buộc đặc biệt cho task dài
    for j in range(n):
        if time_list[j] >= c / 2:
            for t in range(c - time_list[j], time_list[j]):
                wcnf.append([A[j][t]], weight=top_weight)

    # --- Phần 2: Hàm mục tiêu - Tối thiểu hóa tải lớn nhất ---

    # Tạo biến mới để biểu diễn giá trị tối đa của tải trên tất cả thời điểm
    max_load_var = wcnf.nv + 1
    wcnf.nv = max(wcnf.nv, max_load_var)

    # Tạo biến cho tải tại mỗi thời điểm
    time_load_vars = []
    for t in range(c):
        load_var_t = wcnf.nv + 1
        wcnf.nv = max(wcnf.nv, max_load_var)
        time_load_vars.append(load_var_t)

        # Tạo ràng buộc Pseudo-Boolean: tải tại thời điểm t = Σ W[j] * A[j][t]
        coeffs = [W[j] for j in range(n)]
        lits = [A[j][t] for j in range(n)]

        # Mã hóa ràng buộc: tải tại thời điểm t <= load_var_t
        for bound in range(1, sum(W) + 1):
            # Nếu tải vượt quá bound, thì load_var_t >= bound
            pb_constraint = PBEnc.leq(lits=lits, weights=coeffs, bound=bound - 1)
            for clause in pb_constraint.clauses:
                # Nếu tổng tải > bound-1, thì load_var_t phải ít nhất là bound
                wcnf.append(clause + [load_var_t], weight=top_weight)

    # Ràng buộc: max_load_var >= tất cả các time_load_vars
    for load_var in time_load_vars:
        wcnf.append([-load_var, max_load_var], weight=top_weight)

    # Hàm mục tiêu: Tối thiểu hóa max_load_var
    wcnf.append([-max_load_var], weight=1)  # Trọng số thấp để đây là mục tiêu tối ưu

    return wcnf


def solve_pbo(wcnf):
    """Giải bài toán PBO."""
    solver = RC2(wcnf)
    solution = solver.compute()
    cost = solver.cost
    return solution, cost


def print_solution(solution, n, m, c, time_list):
    """In ra giải pháp."""
    if solution is None:
        return None
    else:
        # Chuyển các biến quyết định về dạng ma trận
        x = [[solution[j * m + i] > 0 for i in range(m)] for j in range(n)]
        s = [[solution[m * n + j * c + i] > 0 for i in range(c)] for j in range(n)]
        a = [[solution[m * n + c * n + j * c + i] > 0 for i in range(c)] for j in range(n)]

        # Tạo bảng lịch trình các task
        table = [[0 for t in range(c)] for k in range(m)]
        for k in range(m):
            for t in range(c):
                for j in range(n):
                    if x[j][k] and a[j][t]:
                        for l in range(max(0, t - time_list[j]), t + 1):
                            if s[j][l]:
                                table[k][t] = j + 1

        # Tạo nội dung HTML
        html_content = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Task Assignment to Machines</title>
            <style>
                table {
                    width: 100%;
                    border-collapse: collapse;
                }
                table, th, td {
                    border: 1px solid black;
                }
                th, td {
                    padding: 8px;
                    text-align: center;
                }
                th {
                    background-color: #f2f2f2;
                }
            </style>
        </head>
        <body>
            <h2>Task Assignment to Machines (PBO Solution)</h2>
            <table>
                <tr>
                    <th>Machine</th>
                    """ + "".join([f"<th>Time {t + 1}</th>" for t in range(c)]) + """
                </tr>
        """

        for k in range(m):
            row = f"<tr><td>Machine {k + 1}</td>" + "".join(
                [f"<td>{table[k][t]}</td>" if table[k][t] > 0 else "<td></td>" for t in range(c)]) + "</tr>"
            html_content += row

        html_content += """
            </table>
        </body>
        </html>
        """

        # Ghi nội dung HTML vào file
        file_path = "task_assignment_pbo.html"
        with open(file_path, "w") as file:
            file.write(html_content)

        return True


def get_solution_value(solution, n, m, c, time_list, W):
    """Tính giá trị tải lớn nhất của giải pháp."""
    if solution is None:
        return 100  # Giá trị vô cùng lớn nếu không tìm được giải pháp

    x = [[solution[j * m + i] > 0 for i in range(m)] for j in range(n)]
    s = [[solution[m * n + j * c + i] > 0 for i in range(c)] for j in range(n)]
    a = [[solution[m * n + c * n + j * c + i] > 0 for i in range(c)] for j in range(n)]

    max_load = 0
    for t in range(c):
        current_load = 0
        for j in range(n):
            if a[j][t]:
                for l in range(max(0, t - time_list[j]), t + 1):
                    if s[j][l]:
                        current_load += W[j]
                        break
        max_load = max(max_load, current_load)

    return max_load


def main():
    # Đọc dữ liệu đầu vào
    input()

    # Tạo các biến quyết định
    X, S, A = generate_variables(n, m, c)
    val = max(max(A))

    start_time = time.time()

    # Tiền xử lý
    ip1, ip2 = preprocess(n, m, c, time_list, adj)

    # Tạo mô hình PBO
    wcnf = generate_pbo_model(X, S, A, n, m, c, time_list, adj, ip1, ip2)

    # Giải bài toán
    solution, cost = solve_pbo(wcnf)

    end_time = time.time()

    if solution:
        # In ra kết quả
        print_solution(solution, n, m, c, time_list)

        # Tính giá trị của giải pháp
        solution_value = get_solution_value(solution, n, m, c, time_list, W)

        # Ghi kết quả vào file
        with open("output_pbo.txt", "a") as output_file:
            print(f"Filename: {filename}", file=output_file)
            print(f"Number of variables: {val}", file=output_file)
            print(f"Number of constraints: {len(wcnf.clauses)}", file=output_file)
            print(f"Solution value (max load): {solution_value}", file=output_file)
            print(f"PBO cost: {cost}", file=output_file)
            print(f"Time taken: {end_time - start_time} seconds", file=output_file)
            print(" ", file=output_file)

        print(f"Solution found! Max load: {solution_value}")
        print(f"Time taken: {end_time - start_time} seconds")
    else:
        print("No solution found.")

print("a")
if __name__ == "__main__":
    main()
