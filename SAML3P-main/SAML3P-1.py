from math import inf
import re
import time
from tracemalloc import start
from pysat.solvers import Glucose3
import fileinput
from tabulate import tabulate
import webbrowser
import sys
import test

# input variables in database ?? mertens 1
n = 28
m = 3
c = 342
val = 0
cons = 0
sol = 0
solbb = 0
type = 2
#           0              1                2           3           4           5           6           7               8                   9
file = ["MITCHELL.IN2","MERTENS.IN2","BOWMAN.IN2","ROSZIEG.IN2","BUXEY.IN2","HESKIA.IN2","SAWYER.IN2","JAESCHKE.IN2","MANSOOR.IN2",
        "JACKSON.IN2","GUNTHER.IN2"]
#            9          10              11          12          13          14          15          16          17   
filename = file[5]

fileName = filename.split(".")

with open('task_power/'+fileName[0]+'.txt', 'r') as file:
    W = [int(line.strip()) for line in file]

neighbors = [[ 0 for i in range(n)] for j in range(n)]
reversed_neighbors = [[ 0 for i in range(n)] for j in range(n)]

visited = [False for i in range(n)]
toposort = []
clauses = []
time_list = []
adj = []
# W = [41, 13, 21, 24, 11, 11, 41, 32, 31, 25, 29, 25, 31, 3, 14, 37, 34, 6, 18, 35, 18, 19, 25, 40, 20, 20, 36, 23, 29, 48, 41, 20, 31, 25, 1]




def input():
    cnt = 0
    for line in fileinput.input(filename):
        line = line.strip()
        if line:
            if cnt == 0:
                n = int(line)
            elif cnt <= n: # type: ignore
                time_list.append(int(line))
            else:
                line = line.split(",")
                if(line[0] != "-1" and line[1] != "-1"):
                    adj.append([int(line[0])-1, int(line[1])-1])
                    neighbors[int(line[0])-1][int(line[1])-1] = 1
                    reversed_neighbors[int(line[1])-1][int(line[0])-1] = 1
                else:
                    break
            cnt = cnt + 1

def generate_variables(n,m,c):
    return [[j*m+i+1 for i in range (m)] for j in range(n)], [[m*n + j*c + i + 1 for i in range (c)] for j in range(n)], [[m*n + c*n + j*c + i + 1 for i in range (c)] for j in range(n)]

def dfs(v):
    visited[v] = True
    for i in range(n):
        if(neighbors[v][i] == 1 and visited[i] == False):
            dfs(i)
    toposort.append(v)
def preprocess(n,m,c,time_list,adj):
    earliest_start = [[-9999999 for _ in range(m)] for _ in range(n)]
    latest_start = [[99999999 for _ in range(m)] for _ in range(n)]
    ip1 = [[0 for _ in range(m)] for _ in range(n)]
    test_ip1 = [[0 for _ in range(m)] for _ in range(n)]
    ip2 = [[[0 for _ in range(c)] for _ in range(m)] for _ in range(n)]
    # Compute earliest possible starting date and assigned workstation
    for i in range(n):
        if not visited[i]:
            dfs(i)
    toposort.reverse()
    # print(toposort)
    for j in toposort:
        k = 0
        earliest_start[j][k] = 0
        for i in range(n):
            if neighbors[i][j] == 1:

                earliest_start[j][k] = max(earliest_start[j][k], earliest_start[i][k] + time_list[i])

                while(earliest_start[j][k] > c - time_list[j]):
                    ip1[j][k] = 1
                    # print('X '+str(j+1)+' '+str(k+1))
                    k = k + 1
                    earliest_start[j][k] = max(0, earliest_start[i][k] + time_list[i])

                if earliest_start[j][k] <= c - time_list[j] :
                    for t in range(earliest_start[j][k]):
                        
                        if(ip2[j][k][t] == 0):
                            # with open("output.txt", "a") as output_file: 
                            #     sys.stdout = output_file  
                            #     print(j+1, k+1, t, file=output_file) 
                            ip2[j][k][t] = 1
    toposort.reverse()
    for j in toposort:
        k = m-1
        latest_start[j][k] = c - time_list[j]
        for i in range(n):
            #?????
            if(neighbors[j][i] == 1): 
                
                latest_start[j][k] = min(latest_start[j][k], latest_start[i][k] - time_list[j])
                while(latest_start[j][k] < 0):
                    ip1[j][k] = 1
                    # print('X '+str(j+1)+' '+str(k+1))
                    k = k - 1
                    latest_start[j][k] = min(c - time_list[j], latest_start[i][k] - time_list[j])
                
                if(latest_start[j][k] >= 0):
                        for t in range(latest_start[j][k] + 1, c):
                            
                            if(ip2[j][k][t] == 0):
                                # with open("output.txt", "a") as output_file: 
                                #     sys.stdout = output_file
                                #     print(j+1, k+1, t, file=output_file) 
                                ip2[j][k][t] = 1
    
    # sys.stdout = sys.__stdout__


    # for j in range(n):
    #     for k in range(m):
    #         for t in range(c):
                # if(ip1[j][k] == 1):
                #     continue
                # if(j == 11 or j == 14):
                #     print(f"task {j+1} in machine {k+1} time {t+1}: {ip2[j][k][t]}")
                # if(j == 0 and k == 2):
                #     print(f"task {j+1} in machine {k+1} time {t+1}: {ip2[j][k][t]}")
    # print(ip2)
    return ip1,ip2


def generate_clauses(n,m,c,time_list,adj,ip1,ip2):
    # #test
    # clauses.append([X[11 - 1][2 - 1]])
    # 1
    for j in range (0, n):
        constraint = []
        for k in range (0, m):
            if ip1[j][k] == 1:
                continue
            constraint.append(X[j][k])
        clauses.append(constraint)
    # 2 
    for j in range(0,n):
        for k1 in range (0,m-1):
            for k2 in range(k1+1,m):
                if ip1[j][k1] == 1 or ip1[j][k2] == 1:
                    continue
                clauses.append([-X[j][k1], -X[j][k2]])

    #3
    for a,b in adj:
        for k in range (0, m-1):
            for h in range(k+1, m):
                if ip1[b][k] == 1 or ip1[a][h] == 1:
                    continue
                clauses.append([-X[b][k], -X[a][h]])
    print("first 3 constraints:", len(clauses))

    #4

    for j in range(n):
        clauses.append([S[j][t] for t in range (c-time_list[j]+1)])

    #5
    for j in range(n):
        for k in range(c-time_list[j]):
            for h in range(k+1, c-time_list[j]+1):
                clauses.append([-S[j][k], -S[j][h]])

    #6
    for j in range(n):
        for t in range(c-time_list[j]+1,c):
            if t > c- time_list[j]:
                clauses.append([-S[j][t]])
    print("4 5 6 constraints:", len(clauses))

    #7
    for i in range(n-1):
        for j in range(i+1,n):
            for k in range (m):
                if ip1[i][k] == 1 or ip1[j][k] == 1 :
                    continue
                for t in range(c):
                    # if ip2[i][k][t] == 1 or ip2[j][k][t] == 1:
                    #     continue
                    clauses.append([-X[i][k], -X[j][k], -A[i][t], -A[j][t]])
    print("7 constraints:", len(clauses))
    #8
    for j in range(n):
        for t in range (c-time_list[j]+1):
            for l in range (time_list[j]):
                if(time_list[j] >= c/2 and t+l >= c-time_list[j] and t+l < time_list[j]):
                    continue
                clauses.append([-S[j][t],A[j][t+l]])
    
    print("8 constraints:", len(clauses))

    # addtional constraints
    # a task cant run before its active time

    # for j in range(n):
    #     for t in range (c-time_list[j]+1):
    #         for l in range (t):
    #             if(time_list[j] >= c/2 and l >= c-time_list[j] and l < time_list[j]):
    #                 continue
    #             clauses.append([-S[j][t],-A[j][l]])


    # addtional constraints option 2


    # for j in range(n):
    #     for t in range (c-1): 
    #         if(time_list[j] >= c/2 and t+1 >= c-time_list[j] and t+1 < time_list[j]):
    #             continue
    #         clauses.append([ -A[j][t], A[j][t+1] , S[j][max(0,t-time_list[j]+1)]])
    
    #9
    for i, j in adj:
        for k in range(m):
            if ip1[i][k] == 1 or ip1[j][k] == 1:
                continue
            for t1 in range(c - time_list[i] +1):
                #t1>t2
                for t2 in range(c-time_list[j]+1):
                    if ip2[i][k][t1] == 1 or ip2[j][k][t2] == 1:
                        continue
                    if t1 > t2:
                        clauses.append([-X[i][k], -X[j][k], -S[i][t1], -S[j][t2]])
    cons = len(clauses)
    print("Constraints:",cons)

    # #10
    for j in range(n):
        for k in range(m):
            if ip1[j][k] == 1:
                clauses.append([-X[j][k]])
                continue
                # print("constraint ", j+1, k+1)
            #11
            for t in range(c - time_list[j] +1):
                if ip2[j][k][t] == 1:
                    clauses.append([-X[j][k], -S[j][t]])
                    # print("constraint ", j+1, k+1, t)
    
    #12 
    for j in range(n):
        if(time_list[j] >= c/2):
            for t in range(c-time_list[j],time_list[j]):
                clauses.append([A[j][t]])
    print("12 constraints:", len(clauses))
    return clauses

def solve(solver):
    if solver.solve():
        model = solver.get_model()
        return model
    else:
        # print("no solution")
        return None

def print_solution(solution):
    if solution is None:
        # print("No solution found.")
        return None
    else:
        x = [[solution[j*m+i] for i in range(m)] for j in range(n)]
        s = [[solution[m*n + j*c + i] for i in range(c)] for j in range(n)]
        a = [[solution[m*n + c*n + j*c + i] for i in range(c)] for j in range(n)]
        table = [[0 for t in range(c)] for k in range(m)]
        for k in range(m):
            for t in range(c):
                for j in range(n):
                    if x[j][k] > 0 and a[j][t] > 0 and table[k][t] == 0:
                        for l in range(max(0,t-time_list[j]),t+1):
                            if s[j][l] > 0:
                                table[k][t] = j+1

        # Generate HTML content
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
            <h2>Task Assignment to Machines</h2>
            <table>
                <tr>
                    <th>Machine</th>
                    """ + "".join([f"<th>Time {t+1}</th>" for t in range(c)]) + """
                </tr>
        """

        for k in range(m):
            row = f"<tr><td>Machine {k+1}</td>" + "".join([f"<td>{table[k][t]}</td>" if table[k][t] > 0 else "<td></td>" for t in range(c)]) + "</tr>"
            html_content += row

        html_content += """
            </table>
        </body>
        </html>
        """

        # Write HTML content to a file
        file_path = "task_assignment.html"
        with open(file_path, "w") as file:
            file.write(html_content)

        # Open the HTML file in the default web browser
        # webbrowser.open(file_path)

def get_value(solution,best_value):
    if solution is None:
        return 100, []
    else:
        x = [[  solution[j*m+i] for i in range (m)] for j in range(n)]
        s = [[  solution[m*n + j*c + i ] for i in range (c)] for j in range(n)]
        a = [[  solution[m*n + c*n + j*c + i ] for i in range (c)] for j in range(n)]
        t = 0
        value = 0

        for t in range(c):
            tmp = 0
            for j in range(n):
                if a[j][t] > 0 :
                    # tmp = tmp + W[j]
                    for l in range(max(0,t-time_list[j]),t+1):
                        if s[j][l] > 0:
                            tmp = tmp + W[j]
                            # print(tmp)
                            break
                
            if tmp > value:
                value = tmp
                # print(value)

        constraints = []
        for t in range(c):
            tmp = 0
            station = []
            for j in range(n):
                if a[j][t] > 0:
                    # tmp = tmp + W[j]
                    # station.append(j+1)
                    for l in range(max(0,t-time_list[j]),t+1):
                        if s[j][l] > 0:
                            tmp = tmp + W[j]
                            station.append(j+1)
                            break
            if tmp >= min(best_value, value):
                constraints.append(station)
                # print("value:",value)
        unique_constraints = list(map(list, set(map(tuple, constraints))))

        return value, unique_constraints

def optimal(X,S,A,n,m,c,sol,solbb,start_time):
    ip1,ip2 = preprocess(n,m,c,time_list,adj)

    # print(ip2[])


    clauses = generate_clauses(n,m,c,time_list,adj,ip1,ip2)

    solver = Glucose3()
    for clause in clauses:
        solver.add_clause(clause)

    model = solve(solver)
    if model is None:
        return None
    bestSolution = model 
    infinity = 1000000
    result = get_value(model, infinity)

    bestValue, station = result
    print("initial value:",bestValue)
    print("initial station:",station)
    for t in range(c):
        for stations in station:
            
            solver.add_clause([-A[j-1][t] for j in stations])
    sol = 1
    solbb = 1
    while True:
        # start_time = time.time()
        sol = sol + 1
        model = solve(solver)
        current_time = time.time()
        if current_time - start_time >= 3600:
            print("time out")
            return bestSolution, sol, solbb, bestValue
        # print(f"Time taken: {end_time - start_time} seconds")
        if model is None:
            # print(bestSolution)
            return bestSolution, sol, solbb, bestValue
        value, station = get_value(model, bestValue)
        # print("value:",value)
        # print("station:",station)
        if value < bestValue:
            solbb = sol
            bestSolution = model
            bestValue = value
            # print("new value:",bestValue)
            # print("new station:",station)

        for t in range(c):
            for stations in station:
                solver.add_clause([-A[j-1][t] for j in stations])
                # print(stations)


X, S, A = generate_variables(n,m,c)
input()
val = max(A)
# print(val)
start_time = time.time()
sol = 0
solbb = 0
solution, sol, solbb, solval = optimal(X,S,A,n,m,c,sol,solbb,start_time) #type: ignore
end_time = time.time()
if(solution is not None):
    print_solution(solution)
    x = [[solution[j*m+i] for i in range(m)] for j in range(n)]
    s = [[solution[m*n + j*c + i] for i in range(c)] for j in range(n)]
    a = [[solution[m*n + c*n + j*c + i] for i in range(c)] for j in range(n)]

    with open("output.txt", "a") as output_file: 
        sys.stdout = output_file
        # print(, file=output_file) 
        print(filename,type,file=output_file)
        
        print("#Var:",val[c-1],file=output_file)
        print("#Cons:",len(clauses),file=output_file)
        print("value:",solval,file=output_file)
        print("#sol:",sol,file=output_file)
        print("#solbb:",solbb,file=output_file)
        print(f"Time taken: {end_time - start_time} seconds",file=output_file)
        print(" ",file=output_file)




# print(clauses)
# tmp = 0
# for i in time_list: 
#     tmp = tmp + i
# print(tmp)

