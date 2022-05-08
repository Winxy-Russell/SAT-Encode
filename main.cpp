/*
 * Sat encoding. Walk the maze
 *
 * */
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <string>
#include <cmath>
#include <string.h>
#include <sstream>
#include <map>
#include <unordered_map>
#include <vector>
#include <algorithm>
#include "microsat.c"
using namespace std;

bool **maze, finish;
int *x; // t为1 2n^2 i 增加1 2n j增加1 n
int n, squareN;
const int UP = 0, DOWN = 1, LEFT = 2, RIGHT = 3, ZERO = INT_MAX;
unordered_map<int, int> toAjacent;
unordered_map<int, int> toNotAjacent;
vector<vector<int> > clauses;
vector<int> clause;
int fill_pointer = 0;
void init(string);
void del_memory();
void show_clauses();
void construct_clauses();
void output(string);
void convert();
int encode(int t, int i, int j, int v);
int action_encode(const int type, int t);
string decode(int x);

int main() {
    string path = "D:\\Clion projects\\Training camp\\work1\\test2";
    string out_path = "D:\\Clion projects\\Training camp\\work1\\res2";
    char* file = new char[100];
    strcpy(file, out_path.c_str());
    init(path);
    construct_clauses();
    convert();
    output(out_path);
    vector<int> ans;
    struct solver S;	                                               // Create the solver datastructure
    if (parse (&S, file) == UNSAT) printf("1. s UNSATISFIABLE\n");  // Parse the DIMACS file in argv[1]
    else if (solve (&S)          == UNSAT) printf("2.s UNSATISFIABLE\n");  // Solve without limit (number of conflicts)
    else {
        printf("s SATISFIABLE\n")  ;  // And print whether the formula has a solution
        for(int i = 1;i <= S.nVars;i++){
            if(S.model[i]){
                ans.emplace_back(toNotAjacent[i]);
            }
        }
        sort(ans.begin(), ans.end());

        for(auto& it:ans){
            cout<<decode(it);
            if(decode(it) == "")break;
        }
    }
//    show_clauses();
    del_memory();
    return 0;
}

void init(string path){
    fstream fin(path, ios::in);
    int i, j, t, tmp;
    if(!fin){
        std::cerr<<"Can't open the file."<<endl;
    }
    char buf[1024] = {0};
    fin>>buf;
    sscanf(buf, "%d", &n);
    squareN = n * n;
    maze = new bool*[n];
    for(i = 0;i < n;i++){
        maze[i] = new bool[n];
    }
    int line = 0;
    while(fin >> buf){
        for(i = 0;i < n;i++){
            maze[line][i] = buf[i] - '0';
        }
        line++;
    }
    finish = 0;
}

void construct_clauses(){
    int i, j, t, len;
    vector<int> tmp;
    // initial point must be traversed
    clause.clear();
    clause.emplace_back(0);
    clauses.emplace_back(clause);

    // at time t, only one state variable could be true
    for(t = 0;t < squareN;t++){
        clause.clear();
        //at least one
        for(i = 0;i < n;i++){
            for(j = 0;j < n;j++){
                if(maze[i][j] == 0)
                {
                    clause.emplace_back(encode(t, i, j, maze[i][j]));
                }
            }
        }
        clauses.emplace_back(clause);

        //at most one
        tmp = clauses.back();
        len = tmp.size();
        for(i = 0;i < len;i++){
            for(j = i + 1;j < len;j++){
                clause.resize(2);
                if(tmp[i] != 0){
                    clause[0] = -tmp[i];
                    clause[1] = -tmp[j];
                }
                else{
                    clause.resize(1);
                    clause[0] = -tmp[j];
                }
                clauses.emplace_back(clause);
            }
        }
    }


    clause.clear();
    //end point should be true at least one time
    for(t = 0;t < squareN;t++){
        clause.emplace_back(encode(t, n - 1, n - 1, 0));

    }
    clauses.emplace_back(clause);


    // at any time, one state variable could be true at most once
    clause.resize(1);
    for(t = 1;t < squareN;t++){
        clause[0] = -encode(t, 0, 0, 0);
        clauses.emplace_back(clause);
    }

    for(i = 0;i < n;i++){
        for(j = 0;j < n;j++){
            if(i == 0 && j == 0)continue;
            if(i == n - 1 && j == n - 1)continue;
            if(maze[i][j] == 0){
                for(t = 1;t < squareN;t++){
                    for(int t2 = t + 1;t2 < squareN;t2++){
                        clause.clear();
                        clause.emplace_back(-encode(t, i, j, 0));
                        clause.emplace_back(-encode(t2, i, j, 0));
                        clauses.emplace_back(clause);
                    }

                }
            }
        }
    }

    // one position must come from an ajacent position

    int u, v;
    bool canReach = false;
    for(t = 1; t < squareN;t++){
        for(i = 0;i < n;i++){
            for(j = 0;j < n;j++){
                if(i == 0 && j == 0)continue;
                clause.clear();
                canReach = 0;
                if(maze[i][j] == 0){
                    clause.emplace_back(-encode(t, i, j, 0));
                    u = i - 1; v = j;
                    if(u >= 0 && maze[u][v] == 0){
                        clause.emplace_back(encode(t - 1, u, v, 0));
                        canReach = 1;
                    }
                    u = i + 1; v = j;
                    if(u < n && maze[u][v] == 0){
                        clause.emplace_back(encode(t - 1, u, v, 0));
                        canReach = 1;
                    }
                    u = i; v = j - 1;
                    if(v >= 0 && maze[u][v] == 0){
                        clause.emplace_back(encode(t - 1, u, v, 0));
                        canReach = 1;
                    }
                    u = i; v = j + 1;
                    if(v < n && maze[u][v] == 0){
                        clause.emplace_back(encode(t - 1, u, v, 0));
                        canReach = 1;
                    }
                    if(i == n - 1 && j == n - 1){
                        clause.emplace_back(encode(t - 1, n - 1, n - 1, 0));
                        canReach = 1;
                    }
                    if(canReach){
                        clauses.emplace_back(clause);
                    }
                }

            }
        }
    }

//    show_clauses();
    // state variable cannot be changed unless one action takes place
    // seems useless
}

inline int encode(int t, int i, int j, int v){
    return 2 * t * n * n + i * 2 * n + j * 2 + v;
}

inline int action_encode(const int type, int t){
    return 2 * squareN * squareN + type * squareN + t;
}

string decode(int x){
    stringstream ss;
    if(x < 0){
        x = -x;
        ss<<"-";
    }

    int t = x / (2 * n * n);
    x = x - (2 * n * n) * t;
    int i = x / (2 * n);
    x %= (2 * n);
    int j = x / 2;

    if(finish == 0)
        ss<<"("<<(i + 1)<<" ,"<<(j + 1)<<" ,"<<t<<")"<<" ";
    if(i == n - 1 && j == n - 1){
        finish = 1;
    }
    return ss.str();
}

void del_memory(){
    for(int i = 0;i < n;i++){
        delete []maze[i];
    }
    delete [] maze;
    delete [] x;
}

void convert(){
    for(auto& it:clauses){
        for(auto &x: it){
            if(fabs(x) == ZERO){
                if(!toAjacent.count(0)) {
                    toAjacent[0] = (++fill_pointer);
                    toNotAjacent[fill_pointer] = 0;
                }
            }
            else if(!toAjacent.count(fabs(x))){
                toAjacent[fabs(x)] = (++fill_pointer);
                toNotAjacent[fill_pointer] = fabs(x);
            }
        }
    }
}

void show_clauses(){
    for(auto& c: clauses){
        for(auto& x:c){
            cout<<decode(x);
        }
        cout<<endl;
    }
}

void output(string path){
    fstream os(path, ios::out);
    os<<"p cnf "<< fill_pointer<<" "<<clauses.size()<<endl;
//    os<<"p cnf "<< 60<<" "<<clauses.size()<<endl;
    for(auto& it: clauses){
        for(auto &x: it){
            if(x < 0)os<<"-";
            if(fabs(x) == ZERO){
                os<<toAjacent[0]<<" ";
            }
            else os<<toAjacent[fabs(x)]<<" ";
        }
        os<<0<<endl;
    }
}

string decode_path(struct solver &S){
    stringstream ss;
}

