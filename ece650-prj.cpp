#include <iostream>
#include <sstream>
#include <vector>
#include <queue>
#include <algorithm>
#include <memory>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
#include <pthread.h>
#include <time.h>
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <sys/types.h>
#include <chrono>

#define handle_error(msg) \
               do { perror(msg); exit(EXIT_FAILURE); } while (0)

       #define handle_error_en(en, msg) \
               do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

bool timeddout = false;
std::vector<std::vector<int>> g;
int n_v ;
pthread_t io_thread,cnf_thread,approxvc1_thread,approxvc2_thread;
long long int cnf_time,approxvc1_time,approxvc2_time;

std::vector<int> cnf_sat_vc;
std::vector<int> approx_vc1_vc;
std::vector<int> approx_vc2_vc; 


void addEdge(std::vector<std::vector<int>>& g, int u, int v) 
{
    g[u].push_back(v);
    g[v].push_back(u);
}

void printGraph(const std::vector<std::vector<int>>& g) 
{
    std::cout << "Graph: " << std::endl;
    for (int i = 1; i < g.size(); ++i) {
        std::cout << i;
        for (int j : g[i]) {
            std::cout << "->" << j;
        }
        std::cout << std::endl;
    }
}

bool isempty(const std::vector<std::vector<int>>& gr) 
{
    for (int i = 1; i < gr.size(); ++i) {
        if (gr[i].size() != 0)
            return false;
    }
    return true;
}


enum class CommandsValue 
{
    V,
    E,
    s,
    err
};

CommandsValue commandtooption(const std::string& str) 
{
    if (str == "V")
        return CommandsValue::V;
    else if (str == "E")
        return CommandsValue::E;
    else if (str == "s")
        return CommandsValue::s;
    else
        return CommandsValue::err;
}

std::vector<int> approxvc2(const std::vector<std::vector<int>>& g) {
    bool visited[g.size()];
    std::vector<int> vc;
    std::vector<std::vector<int>> g_copy = g;
    for (int i = 0; i < g.size(); ++i) {
        visited[i] = false;
    }
    for (int u = 1; u < g.size(); ++u) {
        if (visited[u] == false) {
            for (int i = 0; i < g_copy[u].size(); ++i) {
                int v = g_copy[u][i];
                if (visited[v] == false) {
                    visited[u] = true;
                    visited[v] = true;
                    vc.push_back(u);
                    vc.push_back(v);
                    break;
                }
            }
        }
    }
    std::sort(vc.begin(), vc.end());
    return vc;
}


void *approxvc2_thread_func(void *arg)
{
    auto start = std::chrono::high_resolution_clock::now();
    approx_vc2_vc = approxvc2(g);
    auto end = std::chrono::high_resolution_clock::now();
    approxvc2_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
}


std::vector<int> approxvc1(const std::vector<std::vector<int>>& g) {
    std::vector<int> vc;
    std::vector<std::vector<int>> g_copy = g;
    while (!isempty(g_copy)) {
        int max = 0;
        int max_index = 0;
        for (int i = 1; i < g_copy.size(); ++i) {
            if (g_copy[i].size() > max) {
                max = g_copy[i].size();
                max_index = i;
            }
        }
        vc.push_back(max_index);
        for (int i = 0; i < g_copy[max_index].size(); ++i) {
            int temp = g_copy[max_index][i];
            for (int j = 0; j < g_copy[temp].size(); ++j) {
                if (g_copy[temp][j] == max_index) {
                    g_copy[temp].erase(g_copy[temp].begin() + j);
                    break;
                }
            }
        }
        g_copy[max_index].clear();
    }
    std::sort(vc.begin(), vc.end());
    return vc;
}

void *approxvc1_thread_func(void *arg)
{
    auto start = std::chrono::high_resolution_clock::now();
    approx_vc1_vc = approxvc1(g);
    auto end = std::chrono::high_resolution_clock::now();
    approxvc1_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
}
 

std::vector<int> cnfsatvc(int k, int n, const std::vector<std::vector<int>>& g) {
    std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
    std::vector<std::vector<Minisat::Lit>> lits(n);

    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < k; ++j) {
            Minisat::Lit lit(Minisat::mkLit(solver->newVar()));
            lits[i].push_back(lit);
        }
    }

    for (int i = 0; i < k; ++i) {
        Minisat::vec<Minisat::Lit> clause;
        for (int j = 0; j < n; ++j) {
            clause.push(lits[j][i]);
        }
        solver->addClause(clause);
        clause.clear();
    }

    for (int i = 0; i < n; ++i) {
        for (int p = 0; p < k - 1; ++p) {
            for (int q = p + 1; q < k; ++q) {
                solver->addClause(~lits[i][p], ~lits[i][q]);
            }
        }
    }

    for (int i = 0; i < k; ++i) {
        for (int p = 0; p < n - 1; ++p) {
            for (int q = p + 1; q < n; ++q) {
                solver->addClause(~lits[p][i], ~lits[q][i]);
            }
        }
    }

    for (int i = 1; i <= n; ++i) {
        for (int j : g[i]) {
            Minisat::vec<Minisat::Lit> literals;
            for (int p = 0; p < k; ++p) {
                literals.push(lits[i - 1][p]);
                literals.push(lits[j - 1][p]);
            }
            solver->addClause(literals);
            literals.clear();
        }
    }
    //

    bool res = solver->solve();

    if (res) {
        std::vector<int> vc;
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < k; ++j) {
                if (Minisat::toInt(solver->modelValue(lits[i][j])) == 0) {
                    vc.push_back(i + 1);
                }
            }
        }
        lits.clear();
        std::sort(vc.begin(), vc.end());
        return vc;
    } else {
        return std::vector<int>();
    }
    return std::vector<int>();
}

void *cnf_thread_func(void *arg)
{
    auto start = std::chrono::high_resolution_clock::now();
    int low = 1;
    int high = n_v;

    while (low <= high) 
    {
        int mid = floor((low + high) / 2);
        std::vector<int> vc = cnfsatvc(mid, n_v, g);
        if (vc.size() == 0) 
        {
            low = mid + 1;
        } 
        else 
        {
            cnf_sat_vc = vc;
            high = mid - 1;
        }
    }
    auto end = std::chrono::high_resolution_clock::now();
    cnf_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
}

void print_output()
{
    if(!timeddout)
    {
        std::cout << "CNF-SAT-VC: ";
        for (int i = 0; i < cnf_sat_vc.size(); ++i) 
        {
            if(i<cnf_sat_vc.size()-1)
                std::cout << cnf_sat_vc[i] << ",";
            else
                std::cout << cnf_sat_vc[i];
        }
        std::cout << std::endl;
        std::cout << "APPROX-VC-1: ";
        for (int i = 0; i < approx_vc1_vc.size(); ++i) 
        {
            if(i<approx_vc1_vc.size()-1)
                std::cout << approx_vc1_vc[i] << ",";
            else
                std::cout << approx_vc1_vc[i];
        }
        std::cout << std::endl;
        std::cout << "APPROX-VC-2: ";
        for (int i = 0; i < approx_vc2_vc.size(); ++i) 
        {
            if(i<approx_vc2_vc.size()-1)
                std::cout << approx_vc2_vc[i] << ",";
            else
                std::cout << approx_vc2_vc[i];
        }
        std::cout << std::endl;
    }
    else
    {
        std::cout<<"CNF-SAT-VC: timeout"<<std::endl;
        std::cout << "APPROX-VC-1: ";
        for (int i = 0; i < approx_vc1_vc.size(); ++i) 
        {
            if(i<approx_vc1_vc.size()-1)
                std::cout << approx_vc1_vc[i] << ",";
            else
                std::cout << approx_vc1_vc[i];
        }
        std::cout << std::endl;
        std::cout << "APPROX-VC-2: ";
        for (int i = 0; i < approx_vc2_vc.size(); ++i) 
        {
            if(i<approx_vc2_vc.size()-1)
                std::cout << approx_vc2_vc[i] << ",";
            else
                std::cout << approx_vc2_vc[i];
        }
        std::cout << std::endl;
    }

    cnf_sat_vc.clear();
    approx_vc1_vc.clear();
    approx_vc2_vc.clear();
    //std::cout << "CNF-SAT-VC-RUN-TIME: " << cnf_time << " microseconds" << std::endl;
    //std::cout << "APPROX-VC-1-RUN-TIME: " << approxvc1_time << " microseconds" << std::endl;
    //std::cout << "APPROX-VC-2-RUN-TIME: " << approxvc2_time << " microseconds" << std::endl;
    //std::cout << "Approximation ratio for CNF-SAT-VC: " << float(cnf_sat_vc.size()) / float(cnf_sat_vc.size()) << std::endl;
    //std::cout << "Approximation ratio for APPROX-VC-1: " << float(approx_vc1_vc.size()) / float(cnf_sat_vc.size()) << std::endl;
    //std::cout << "Approximation ratio for APPROX-VC-2: " << float(approx_vc2_vc.size()) / float(cnf_sat_vc.size()) << std::endl;
    //int l = 0;
    //if(!timeddout)
    //{
    //    l = cnf_sat_vc.size();
    //}
    //else
    //{
    //    l = 0;
    //}
    //int m = approx_vc1_vc.size();
    //int n = approx_vc2_vc.size();
    //if(l!=0)
    //    std::cout << n_v << " " << cnf_time << " " << approxvc1_time << " " << approxvc2_time << " " << l << " " << m << " " << n << " " <<float(cnf_sat_vc.size()) / float(cnf_sat_vc.size()) << " " << float(approx_vc1_vc.size()) / float(cnf_sat_vc.size()) << " " << float(approx_vc2_vc.size()) / float(cnf_sat_vc.size()) << std::endl;
    //else
    //    std::cout << n_v << " " << "120000000" << " " << approxvc1_time << " " << approxvc2_time << " " << "0" << " " << m << " " << n << " " <<"0"<< " " << "0"<< " " << "0" << std::endl;
}

void *io_thread_func(void *arg)
{
    n_v = 0;
    std::string num;
    std::string inp;
    bool flag = false;
    bool g_exist = false;

    

    while (std::getline(std::cin, inp)) {
        if(inp.size() == 0)
        {
         //   std::cout<<"Error: No command given"<<std::endl;
            continue;
        }
        std::stringstream ss(inp);
        std::string command;
        ss >> command;
        CommandsValue cmd = commandtooption(command);

        switch (cmd) {
            
            case CommandsValue::V: {
                ss >> num;
                if (num.size() == 0) {
                    std::cout << "Error: Number of vertices not given" << std::endl;
                    break;
                }
                n_v = std::stoi(num);
                if (n_v <= 0) {
                    std::cout << "Error: Number of vertices cannot be less than or equal to zero" << std::endl;
                    break;
                }
                g_exist = false;
                flag = false;
                g.clear();
                g.resize(n_v + 1);
                break;
            }
            case CommandsValue::E: {
                if (flag)
                    break;
                ss >> inp;
                if (inp.size() == 0) {
                    std::cout << "Error: No edges given" << std::endl;
                    break;
                }
                int u;
                int v;
                for (int i = 0; i < inp.length(); ++i) {
                    if (isdigit(inp[i])) {
                        int start = i;
                        while (isdigit(inp[i]))
                            i++;
                        int end = i;
                        u = std::stoi(inp.substr(start, end - start));
                        i++;
                        start = i;
                        while (isdigit(inp[i]))
                            i++;
                        end = i;
                        v = std::stoi(inp.substr(start, end - start));
                        if (u > n_v || v > n_v || u <= 0 || v <= 0) {
                            std::cout << "Error: Vertex cannot be greater than the number of vertices or less than zero" << std::endl;
                            g_exist = false;
                            break;
                        }
                        if (u == v) {
                            std::cout << "Error: Self-loop not allowed" << std::endl;
                            g_exist = false;
                            break;
                        }
                        addEdge(g, u, v);
                        g_exist = true;
                    }
                }
                if (!g_exist) {
                    std::cout << std::endl;
                    break;
                }

                int t2;
                t2 = pthread_create(&cnf_thread,NULL,cnf_thread_func,NULL);
                if(t2)
                {
                    std::cout<<"Error in creating cnf thread"<<std::endl;
                    exit(-1);
                }
                t2 = pthread_create(&approxvc1_thread,NULL,approxvc1_thread_func,NULL);
                if(t2)
                {
                    std::cout<<"Error in creating approxvc1 thread"<<std::endl;
                    exit(-1);
                }
                t2 = pthread_create(&approxvc2_thread,NULL,approxvc2_thread_func,NULL);
                if(t2)
                {
                    std::cout<<"Error in creating approxvc2 thread"<<std::endl;
                    exit(-1);
                }
                
                //pthread_join(cnf_thread,NULL);
                struct timespec timeout;
                clock_gettime(CLOCK_REALTIME, &timeout);
                timeout.tv_sec += 300;

    // Wait for the cnf_thread to finish or timeout
                int join_result = pthread_timedjoin_np(cnf_thread, NULL, &timeout);

                if(join_result == ETIMEDOUT)
                {
                    timeddout = true;
                }
                else if(join_result == 0)
                {
                    timeddout = false;
                }
                pthread_join(approxvc1_thread,NULL);
                pthread_join(approxvc2_thread,NULL);

                print_output();

                flag = true;
                break;
            }
            case CommandsValue::s:
             {
                std::cout << "Error: Invalid Command" << std::endl;
                break;
            }
            case CommandsValue::err: {
                
                break;
            }
        }
        
        if (std::cin.eof()) {
            break;
        }
    }
}

int main() {
    int t;
    
    t = pthread_create(&io_thread,NULL,io_thread_func,NULL);
    if(t){
        std::cout<<"Error in creating io thread"<<std::endl;
        exit(-1);
    }

    pthread_join(io_thread,NULL);


    return 0;
}
