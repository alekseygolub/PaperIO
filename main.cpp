#include<bits/stdc++.h>

#include "./nlohmann/json.hpp"

using namespace std;
using namespace nlohmann;

mt19937 rnd((int)time(NULL));

#define all(x) x.begin(), x.end()
#define rall(x) x.rbegin(), x.rend()
#define F first
#define S second
#define pb push_back
#define pii pair<int, int>
#define len(x) (long long)x.size()
const long long INF = (int)numeric_limits<int>::max() >> 1;

typedef long double ld;

template<typename A, typename B>
bool cmax(A &a, const B &b) {
    if (a < b) {
        a = b;
        return true;
    }
    return false;
}

template<typename A, typename B>
bool cmin(A &a, const B &b) {
    if (a > b) {
        a = b;
        return true;
    }
    return false;
}

double STAT_SUM = 0;
int STAT_TICK = 0;

int MAXLAYER_ = 10;
int MAXTICK = 2500;

int maxPathLen = 15;
int maxCandidateCount = 5;

const ld mulct_standard = 1.0;
const ld mulct_special = 0.5;

ld mulct = mulct_standard;
const int limit_change_mulct = 5;
int timer_mulct = 0;

int n, m, speed, width, n_big, m_big;
int curDir = -1;

const vector<string> commands = {"left", "right", "up", "down"};
map<string, int> Directions;
const vector<pii> commandsDir = {{-1, 0}, {1, 0}, {0, 1}, {0, -1}};
const vector<int> signs = {-1, 1};

int TICK = 0;

struct player {
    int x_big = 0, y_big = 0, x_little = 0, y_little = 0;
    int D = -1;
    bool fast = 0, slow = 0;
    player(int x = 0, int y = 0) {
        x_little = x;
        y_little = y;
        x_big = x / width;
        y_big = y / width;
    };
    void recalc() {
        y_little -= 15;
        x_little -= 15;
        x_big = x_little / width;
        y_big = y_little / width;

        if (D == 1) {
            x_big = x_little / width + bool(x_little % width); 
        }
        if (D == 2) {
            y_big = y_little / width + bool(y_little % width);
        }
    }
};

struct myset {
    long long bit = 0;
    int sz = 0;
    int size() {
        return sz;
    }
    bool count(int x) {
        x += 3;
        return (bool)(bit & (1ll << x));
    }
    void insert(int x) {
        x += 3;
        if ((bit & (1ll << x)) == 0) sz++;
        bit |= (1ll << x);
    }
};

vector<player> P; vector<int> disthome;
vector<vector<int>> g_big, lines_big;
vector<vector<char>> used;
vector<vector<int>> arr_path;
vector<vector<int>> new_g;
vector<vector<int>> bonuses;
vector<vector<pii>> parents;
vector<int> to_best_border;
vector<vector<char>> safe_area;

vector<vector<ld>> rate_area;
vector<vector<ld>> block_area;
int ID = 0;

int dist(pii a, pii b) {
    return abs(a.F - b.F) + abs(a.S - b.S);
}

bool check_coord(int x, int y) {
    if (x < 0 || x >= n_big || y < 0 || y >= m_big) return 0;
    return 1;
}

template<class T>
void cleararr(vector<vector<T>> &arr, T x) {
    for (auto &X: arr) {
        for (auto &Y: X) {
            Y = x;
        }
    }
}

void coloring(int x, int y, int c, vector<vector<int>> &G, myset &res) {
    G[x][y] = c;
    for (auto dx: commandsDir) {
        int X = x + dx.F;
        int Y = y + dx.S;
        if (check_coord(X, Y) && G[X][Y] == 0) coloring(X, Y, c, G, res);
        if (!check_coord(X, Y)) {
            res.insert(-3);
            continue;
        }
        if (G[X][Y] != c) res.insert(G[X][Y]);
    }
}   

template<class T>
void SHOW(vector<vector<T>> &arr) {
    for (auto &X: arr) {
        for (auto &Y: X) cerr << Y << " ";
        cerr << "\n";
    }
    cerr << "\n";
}

void init_game(json state) {
    if (state["type"] != "start_game") return;
    n = state["params"]["x_cells_count"];
    m = state["params"]["y_cells_count"];
    speed = state["params"]["speed"];
    width = state["params"]["width"];
    n_big = n; m_big = m;
    n *= width;
    m *= width;
    g_big.resize(n_big, vector<int>(m_big));
    lines_big.resize(n_big, vector<int>(m_big));
    used.resize(n_big, vector<char>(m_big));
    arr_path.resize(n_big, vector<int>(m_big));
    new_g.resize(n_big, vector<int>(m_big));
    bonuses.resize(n_big, vector<int>(m_big));
    parents.resize(n_big, vector<pii>(m_big));
    safe_area.resize(n_big, vector<char>(m_big));
    rate_area.resize(n_big, vector<ld>(m_big));
    block_area.resize(4, vector<ld>(4));
    for (int i = 0; i < len(commands); i++) Directions[commands[i]] = i;
}

int dist_to_territory(int playerID, int territoryID, pii pos = {-1, -1}) {
    cleararr(used, (char)0);
    queue<pii> q;
    if (pos == pii{-1, -1}) {
        q.push({P[playerID].x_big, P[playerID].y_big});
        used[P[playerID].x_big][P[playerID].y_big] = 1;
    } else {
        q.push(pos);
        used[pos.F][pos.S] = 1;
    }
    while (!q.empty()) {
        int curx = q.front().F, cury = q.front().S;
        q.pop();
        if (g_big[curx][cury] == territoryID + 1) {
            int to_home = used[curx][cury] - 1;
            if (P[playerID].fast && P[ID].fast); 
            else if (P[playerID].fast && P[ID].slow) to_home /= 2;
            else if (P[playerID].slow && P[ID].fast) to_home *= 2;
            else if (P[playerID].slow && P[ID].slow);
            else if (P[playerID].fast) to_home = (to_home * 5) / 6;
            else if (P[playerID].slow) to_home = (to_home * 10) / 6;
            else if (P[ID].fast) to_home = (to_home * 6) / 5;
            else if (P[ID].slow) to_home = (to_home * 6) / 10;
            return to_home;
        }
        for (auto dx: commandsDir) {
            int X = curx + dx.F;
            int Y = cury + dx.S;
            if (check_coord(X, Y)) {
                if (lines_big[X][Y] == playerID + 1 || used[X][Y]) continue;
                used[X][Y] = used[curx][cury] + 1;
                q.push({X, Y});
            }
        }
    }
    return INF;
} 

void paint_the_territory(vector<pii> &L, int playerID, int COLOR) {
    cleararr(new_g, 0);
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            if (lines_big[i][j] == playerID + 1) L.pb({i, j});
            if (g_big[i][j] == playerID + 1) new_g[i][j] = -1;
        }
    }
    L.pb({P[playerID].x_big, P[playerID].y_big});

    for (auto x: L) {
        if (new_g[x.F][x.S] != -1) new_g[x.F][x.S] = -2;
    } 
    int color = 1;
    myset my;
    my.insert(-2);  
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            myset res;
            if (new_g[i][j] == 0) {
                coloring(i, j, color++, new_g, res);
                if ((len(res) == 2 && res.count(-2) && res.count(-1)) || (len(res) == 1 && res.count(-2))) my.insert(color - 1);
            }
        }
    }
    int rate = 0;
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            if (my.count(new_g[i][j])) {
                if (g_big[i][j] != playerID + 1) {
                    cmin(safe_area[i][j], (char)COLOR);
                }
            }
        }
    }
}

int dist_to_ememy(int x, int y) {
    int res = INF;
    for (int i = 0; i < len(P); i++) {
        if (i != ID) {
            if (P[i].D == -1) {
                if (pii{P[i].x_big, P[i].y_big} == pii{x, y}) cmin(res, 0);
            } else {
                int DIST = abs(P[i].x_big - x) + abs(P[i].y_big - y);
                //
                if (P[i].fast && P[ID].fast); 
                else if (P[i].fast && P[ID].slow) DIST /= 2;
                else if (P[i].slow && P[ID].fast) DIST *= 2;
                else if (P[i].slow && P[ID].slow);   
                else if (P[i].fast) DIST = (DIST * 5) / 6;
                else if (P[i].slow) DIST = (DIST * 10) / 6;
                else if (P[ID].fast) DIST = (DIST * 6) / 5;
                else if (P[ID].slow) DIST = (DIST * 6) / 10;
                //
                cmin(res, DIST);
            }
        } 
    }
    return res;
}

vector<pii> get_path_to_area(int playerID) {
    cleararr(used, (char)0);
    int x = P[playerID].x_big, y = P[playerID].y_big;
    queue<pair<pii, int>> q;
    used[x][y] = P[playerID].D + 1;
    q.push({{x, y}, 0});
    while (!q.empty()) {
        int curx = q.front().F.F; int cury = q.front().F.S;
        int L = q.front().S;
        q.pop();
        if (g_big[curx][cury] == playerID + 1 && safe_area[curx][cury] > L + 2) {
            vector<pii> path;
            while (pii{curx, cury} != pii{x, y}) {
                path.pb({curx, cury});
                int D = used[curx][cury] - 1;
                curx += commandsDir[D ^ 1].F;
                cury += commandsDir[D ^ 1].S;
            }
            return path;
        }
        for (int i = 0; i < 4; i++) {
            if ((i ^ 1) == used[curx][cury] - 1) continue;
            auto dx = commandsDir[i];
            int X = curx + dx.F, Y = cury + dx.S;
            if (check_coord(X, Y) && !used[X][Y] && lines_big[X][Y] != playerID + 1 && (playerID != ID || L + 1 != safe_area[X][Y])) {
                if (L < 3 && dist_to_ememy(X, Y) <= 1) continue; 
                used[X][Y] = i + 1;
                q.push({{X, Y}, L + 1});
            }
        }
    }
    return vector<pii>();
}

vector<pii> get_candidate(int playerID, int countCandidate) {
    vector<pii> candidate;
    cleararr(used, (char)0);
    int x = P[playerID].x_big, y = P[playerID].y_big;
    queue<pair<pii, int>> q;
    used[x][y] = P[playerID].D + 1;
    q.push({{x, y}, 0});
    while (!q.empty()) {
        int curx = q.front().F.F; int cury = q.front().F.S;
        int L = q.front().S;
        q.pop();
        if (g_big[curx][cury] == playerID + 1) {
            candidate.pb({curx, cury});
            if (len(candidate) == countCandidate) return candidate;
            continue;
        }
        for (int i = 0; i < 4; i++) {
            if ((i ^ 1) == used[curx][cury] - 1) continue;
            auto dx = commandsDir[i];
            int X = curx + dx.F, Y = cury + dx.S;
            if (check_coord(X, Y) && !used[X][Y] && lines_big[X][Y] != playerID + 1) {
                used[X][Y] = i + 1;
                q.push({{X, Y}, L + 1});
            }
        }
    }
    return candidate;
}

vector<pii> get_path_to_position(int playerID, pii pos) {
    cleararr(used, (char)0);
    int x = P[playerID].x_big, y = P[playerID].y_big;
    queue<pair<pii, int>> q;
    used[x][y] = P[playerID].D + 1;
    q.push({{x, y}, 0});
    while (!q.empty()) {
        int curx = q.front().F.F; int cury = q.front().F.S;
        int L = q.front().S;
        q.pop();
        if (pii{curx, cury} == pos) {
            vector<pii> path;
            while (pii{curx, cury} != pii{x, y}) {
                path.pb({curx, cury});
                int D = used[curx][cury] - 1;
                curx += commandsDir[D ^ 1].F;
                cury += commandsDir[D ^ 1].S;
            }
            return path;
        }
        for (int i = 0; i < 4; i++) {
            if ((i ^ 1) == used[curx][cury] - 1) continue;
            auto dx = commandsDir[i];
            int X = curx + dx.F, Y = cury + dx.S;
            if (check_coord(X, Y) && !used[X][Y] && lines_big[X][Y] != playerID + 1) {
                used[X][Y] = i + 1;
                q.push({{X, Y}, L + 1});
            }
        }
    }
    return vector<pii>();
}

void calc_safe_area() {
    cleararr(safe_area, (char)100);
    for (int i = 0; i < len(P); i++) {
        if (i == ID) continue;
        auto candidate = get_candidate(i, 20);
        for (auto pos: candidate) {
            auto path = get_path_to_position(i, pos);
            if (len(path) == 0) continue;
            int to_home = len(path);

            if (P[i].fast && P[ID].fast); 
            else if (P[i].fast && P[ID].slow) to_home /= 2;
            else if (P[i].slow && P[ID].fast) to_home *= 2;
            else if (P[i].slow && P[ID].slow);
            else if (P[i].fast) to_home = (to_home * 5) / 6;
            else if (P[i].slow) to_home = (to_home * 10) / 6;
            else if (P[ID].fast) to_home = (to_home * 6) / 5;
            else if (P[ID].slow) to_home = (to_home * 6) / 10;

            paint_the_territory(path, i, to_home);
        }
    }
    for (int i = 0; i < len(P); i++) {
        if (i == ID) continue;
        for (int j = 0; j < 4; j++) {
            auto dx = commandsDir[j];
            if ((j ^ 1) == P[i].D) continue;
            int X = P[i].x_big + dx.F, Y = P[i].y_big + dx.S;
            if (check_coord(X, Y) && bonuses[X][Y] == 51) {
                while (check_coord(X, Y)) {
                    cmin(safe_area[X][Y], 1);
                    X += dx.F; Y += dx.S;
                }
                dx = commandsDir[j ^ 1];
                while (check_coord(X, Y)) {
                    cmin(safe_area[X][Y], 1);
                    X += dx.F; Y += dx.S;
                }
            }
        }
    }
}

int rate_cell(int x, int y) {
    int res = 0;
    if (g_big[x][y] == 0) res += 1;
    if (g_big[x][y] != 0 && g_big[x][y] != ID + 1) res += 5;
    if (lines_big[x][y] && lines_big[x][y] != ID + 1 && (g_big[x][y] == 0 || g_big[x][y] == ID + 1)) res += 3;
    return res;
}

int rate_position(int x, int y) {
    ld rate = 0;
    int max_dist = 4;
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            int D = dist({i, j}, {x, y});
            if (D <= 4) rate += rate_cell(i, j) * 1.0;
            else if (D <= 7) rate += rate_cell(i, j) * 0.5;
            else if (D <= 10) rate += rate_cell(i, j) * 0.2;
            else rate += rate_cell(i, j) * 0.05;
        }
    }
    for (int i = 0; i < len(P); i++) {
        if (i == ID) continue;
        int D = dist({P[i].x_big, P[i].y_big}, {x, y});
        if (D <= 4) rate -= 49;
        else if (D <= 7) rate -= 13;
        else if (D <= 10) rate -= 7; 
    }
    rate /= M_PI;
    return rate;
}

void calc_rate_area() {
    cleararr(rate_area, (ld)0.0);
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            rate_area[i][j] = rate_position(i, j);
        }
    }
}

void init_tick(json state) {
    if (state["type"] != "tick") return;
    P.clear();
    disthome.clear();
    for (auto &x: g_big) fill(all(x), 0);
    for (auto &x: lines_big) fill(all(x), 0);
    int i = 0;
    for (auto it = state["params"]["players"].begin(); it != state["params"]["players"].end(); ++it) {
        if (it.key() == "i") ID = i;
        i++;
    }
    for (auto p: state["params"]["players"]) {
        string S = p.dump();
        P.pb(player(p["position"][0], p["position"][1]));
        for (auto x: p["params"]["bonuses"]) {
            if (x["type"] == 'n') P.back().fast = 1;
            if (x["type"] == 's') P.back().slow = 1;
        }
        if (P.back().fast && P.back().slow) P.back().fast = P.back().slow = 0;

        if (!p["direction"].is_null()) P.back().D = Directions[(p["direction"])];  
        for (auto &coord: p["territory"]) {
            int x = coord[0], y = coord[1];
            g_big[x / width][y / width] = len(P);
        }
        for (auto coord: p["lines"]) {
            lines_big[(int)coord[0] / width][(int)coord[1] / width] = len(P);
        }
        P.back().recalc();
    }
    disthome.resize(len(P), INF);
    for (i = 0; i < len(P); i++) {
        disthome[i] = dist_to_territory(i, i);
    }
    cleararr(bonuses, 0);
    for (auto p: state["params"]["bonuses"]) {
        if (p["type"] != "s") bonuses[(int)p["position"][0] / width][(int)p["position"][1] / width] = 50 + bool(p["type"] == "saw");
        else bonuses[(int)p["position"][0] / width][(int)p["position"][1] / width] = -1000;
    }
    TICK = state["params"]["tick_num"];
    if (TICK > MAXTICK) MAXTICK += 500;
    if (TICK > 50) {
        int cnt = 0;
        for (int i = 0; i < len(P); i++) if (i != ID && P[i].D != -1) cnt++;
        // MAXLAYER_ = 10 - (5 - cnt);
        MAXLAYER_ = 10;
        if (dist_to_ememy(P[ID].x_big, P[ID].y_big) > MAXLAYER_ - 1) cmin(MAXLAYER_, 8);
        if (cnt == 0) MAXLAYER_ = 6;
    }
    calc_safe_area();
    calc_rate_area();
}

int calc_saw(int x, int y, int DIR) {
    bool flag = 0;
    while (check_coord(x + commandsDir[DIR].F, y + commandsDir[DIR].S)) {
        x += commandsDir[DIR].F; y += commandsDir[DIR].S;
        if (g_big[x][y] != 0 && g_big[x][y] != ID + 1) flag = 1;
    }
    if (flag) return 50;
    return 0;
}

int calcRate(vector<pii> &L, int last_x, int last_y, int DIR) {
    int LEN = 0;
    cleararr(new_g, 0);
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            if (g_big[i][j] == ID + 1) new_g[i][j] = -1;
        }
    }
    for (auto x: L) {
        if (g_big[x.F][x.S] != ID + 1) LEN++;
        if (new_g[x.F][x.S] != -1) new_g[x.F][x.S] = -2;
    } 
    int color = 1;
    myset my;
    my.insert(-2);
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            myset res;
            if (new_g[i][j] == 0) {
                coloring(i, j, color++, new_g, res);
                if ((len(res) == 2 && res.count(-2) && res.count(-1)) || (len(res) == 1 && res.count(-2))) my.insert(color - 1);
            }
        }
    }
    int rate = 0;
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            if (my.count(new_g[i][j])) {
                if (g_big[i][j] == 0) rate += 1;
                if (g_big[i][j] != 0 && g_big[i][j] != ID + 1) rate += 5;
                if (bonuses[i][j] == 51) {
                    rate += calc_saw(last_x, last_y, DIR);
                } else {
                    rate += bonuses[i][j];
                }
            }
        }
    }
    int RES = rate - int(mulct * (ld)LEN) + rate_position(last_x, last_y);
    return RES;
}

int getDIR(pii prev, pii next) {
    for (int i = 0; i < 4; i++) {
        if (pii{prev.F + commandsDir[i].F, prev.S + commandsDir[i].S} == next) return i;
    }
    return rnd() % 4;
}

pii get_path(int x, int y, vector<vector<char>> localused, int layer, int C, int DIR) {
    int RATE = -INF;
    int bestlen = INF;
    vector<pii> curpath;
    localused[x][y] = C;
    bool flag = 1;
    for (int i = 0; i < n_big; i++) 
        for (int j = 0; j < m_big; j++) {
            if (lines_big[i][j] == ID + 1) localused[i][j] = C;
            if (localused[i][j] == C) {
                curpath.pb({i, j});
                if (g_big[i][j] != ID + 1) flag = 0;
            } 
            if (dist_to_ememy(i, j) <= layer) {
                if (localused[i][j] == C) {
                    return {-INF, INF};
                }
                localused[i][j] = C + 1;
            }
        }

    if (flag) return {0, 0}; 
    if (g_big[x][y] == ID + 1) return {calcRate(curpath, x, y, DIR), 0};

    for (int l = 1; l < maxPathLen; l++) {
        int curlen = layer + l;
        if (P[ID].fast && TICK + curlen * 5 >= MAXTICK) continue;
        else if (P[ID].slow && TICK + curlen * 10 >= MAXTICK) continue;
        else if (TICK + curlen * 6 >= MAXTICK) continue;
        flag = false;

        for (int p = 0; p < len(P); p++) {
            if (p == ID || P[p].D == -1) continue;
            int X = P[p].x_big, Y = P[p].y_big;
            //
            int was_curlen = curlen;

            if (P[p].fast && P[ID].fast); 
            else if (P[p].fast && P[ID].slow) curlen *= 2;
            else if (P[p].slow && P[ID].fast) curlen = curlen / 2 + curlen % 2;
            else if (P[p].slow && P[ID].slow);   
            else if (P[p].fast) curlen = curlen * 6 / 5 + bool((curlen * 6) % 5);
            else if (P[p].slow) curlen = curlen * 6 / 10 + bool((curlen * 6) % 10);
            else if (P[ID].fast) curlen = curlen * 5 / 6 + bool((curlen * 5) % 6);
            else if (P[ID].slow) curlen = curlen * 10 / 6 + bool((curlen * 10) % 6);
            //
            for (int a = -curlen; a <= curlen; a++) {
                for (auto S: signs) {
                    int b = (curlen - abs(a)) * S;
                    if (abs(a) + abs(b) != curlen) continue;
                    if (check_coord(X + a, Y + b)) {
                        if (localused[X + a][Y + b] == C) flag = 1;
                        localused[X + a][Y + b] = C + 1;
                    }
                }
            }
            //
            curlen = was_curlen;
            //
        }
        if (flag) break;
        cleararr(parents, pii{-1, -1});
        queue<pair<pii, pii>> q[2];
        vector<pii> candidate;

        q[1].push({{x, y}, {DIR, layer}});
        for (int i = 0; i < l; i++) {
            swap(q[0], q[1]);
            while (!q[0].empty()) {
                int curx = q[0].front().F.F, cury = q[0].front().F.S;
                int D = q[0].front().S.F;
                int L = q[0].front().S.S;
                q[0].pop();
                if (L == safe_area[curx][cury]) continue;
                if (g_big[curx][cury] == ID + 1 && safe_area[curx][cury] > curlen + 2) {
                    continue;
                }
                for (int j = 0; j < 4; j++) {
                    if ((D ^ 1) == j) continue;
                    auto dx = commandsDir[j];
                    int X = curx + dx.F, Y = cury + dx.S;
                    if (check_coord(X, Y) && localused[X][Y] != C && localused[X][Y] != C + 1 && localused[X][Y] != C + 2) {
                        parents[X][Y] = {curx, cury};
                        localused[X][Y] = C + 2;
                        q[1].push({{X, Y}, {j, L + 1}});
                    }
                }
            }
        }
        for (int i = 0; i < n_big; i++) 
                for (int j = 0; j < m_big; j++) 
                    if (localused[i][j] == C + 2) localused[i][j] = 0;
        

        while (!q[1].empty()) {
            if (g_big[q[1].front().F.F][q[1].front().F.S] == ID + 1 && safe_area[q[1].front().F.F][q[1].front().F.S] > curlen + 2) candidate.pb(q[1].front().F);
            q[1].pop();
        }
        int curx = -1, cury = -1;
        if (candidate.empty()) continue;
        shuffle(all(candidate), rnd);

        for (int i = 0; i < min((long long)maxCandidateCount, len(candidate)); i++) {
            curx = candidate[i].F; cury = candidate[i].S;
            int cnt = 0;
            while (pii{curx, cury} != pii{x, y}) {
                cnt++;
                curpath.pb({curx, cury});
                pii par = parents[curx][cury];
                curx = par.F; cury = par.S;
            }
            if (cmax(RATE, calcRate(curpath, candidate[i].F, candidate[i].S, getDIR({parents[candidate[i].F][candidate[i].S]}, candidate[i])))) {
                bestlen = cnt;
            }
            for (int j = 0; j < cnt; j++) curpath.pop_back();
        }
        candidate.clear();
    }
    return {RATE, bestlen};
}

int goDIR(int curD, int needD, int x, int y) {
    if ((curD ^ 1) != needD) return needD;
    for (int i = 0; i < 4; i++) if (i != curD && i != needD && check_coord(x + commandsDir[i].F, y + commandsDir[i].S)) return i;
    return needD;
}

string deb = "";

pair<pii, int> dfs(int x, int y, vector<vector<char>> &localused, int layer, int DIR, int MAXLAYER, char C = 1) {
    if (layer >= MAXLAYER) return {{-INF, -1}, -1};

    if (layer > 0 && bonuses[x][y] == -1000) return {{-1000, -1}, -1};
    if (layer > 0 && safe_area[x][y] == layer) return {{-INF, -1}, -1};
    if (layer == 1 && dist_to_ememy(x, y) <= 2) return {{-INF, -1}, -1};

    int WAS = localused[x][y];
    localused[x][y] = C;

    auto path = get_path(x, y, localused, layer, C, DIR);
    if (bonuses[x][y] < 0) path.F += bonuses[x][y];
    if (bonuses[x][y] == 51) path.F += calc_saw(x, y, DIR);
    if (g_big[x][y] != ID + 1 && path.F < -INF / 2) {
        localused[x][y] = WAS;
        return  {{-INF, -1}, -1};
    }

    bool safe = 0;
    if (g_big[x][y] == ID + 1) {
        safe = 1;
        C++;
    }
    if (layer != 0) {
        int rate = path.F;
        //ADD Bonuses;
        if (lines_big[x][y] != 0 && lines_big[x][y] != ID + 1 && disthome[lines_big[x][y] - 1] > layer) rate += 100;
        if (bonuses[x][y] != 51) if (g_big[x][y] == ID + 1) rate += bonuses[x][y];
        //---
        vector<pii> can = {pii{rate, -1 * (path.S + layer)}};
        for (int i = 0; i < 4; i++) {
            int X = x + commandsDir[i].F;
            int Y = y + commandsDir[i].S;
            if ((i ^ 1) != DIR && check_coord(X, Y) && localused[X][Y] != C && (safe || lines_big[X][Y] != ID + 1)) {
                can.pb(dfs(X, Y, localused, layer + 1, i, MAXLAYER, C).F);
            }
        }
        localused[x][y] = WAS;
        return {*max_element(all(can)) , -1};
    } else {
        vector<pair<pii, int>> can;
         for (int i = 0; i < 4; i++) {
            int X = x + commandsDir[i].F;
            int Y = y + commandsDir[i].S;
            if ((i ^ 1) != DIR && check_coord(X, Y) && localused[X][Y] != C && (safe || lines_big[X][Y] != ID + 1)) {
                can.pb({dfs(X, Y, localused, layer + 1, i, MAXLAYER, C).F, i});
            }
        }
        localused[x][y] = WAS;
        return *max_element(all(can));
    }
}

int nearest_border(int x, int y, int DIR) {
    cleararr(parents, pii{-1, -1});
    queue<pii> q;
    q.push({x, y});
    while (!q.empty()) {
        int curx = q.front().F; int cury = q.front().S;
        q.pop();
        if (g_big[curx][cury] != ID + 1) {
            int cnt = 1;
            while (parents[curx][cury] != pii{x, y}) {
                auto C = parents[curx][cury];
                cnt++;
                curx = C.F;
                cury = C.S;
                if (curx == -1 || cury == -1) return -1;
            }
            if (cnt + 2 < MAXLAYER_) {
                return -1;
            }
            for (int i = 0; i < 4; i++) {
                auto dx = commandsDir[i];
                if (x + dx.F == curx && y + dx.S == cury) return goDIR(DIR, i, x, y);
            }
        }
        for (auto dx: commandsDir) {
            int X = curx + dx.F, Y = cury + dx.S;
            if (check_coord(X, Y) && parents[X][Y] == pii{-1, -1} && bonuses[X][Y] != -1000) {
                parents[X][Y] = {curx, cury};
                q.push({X, Y});
            }
        }
    }
    for (int i = 0; i < 4; i++) {
        if (check_coord(x + commandsDir[i].F, y + commandsDir[i].S)) return goDIR(DIR, i, x, y);;
    }
    return -1;
}

int best_border(int x, int y, int DIR) {
    if (dist_to_ememy(x, y) <= 3) return -1;
    cleararr(used, (char)0);
    ld bestRate = -1000;
    pii bestPos = {-1, -1};
    for (int i = 0; i < n_big; i++) {
        for (int j = 0; j < m_big; j++) {
            int LEN = dist(pii{x, y}, pii{i, j});
            ld R = rate_area[i][j] - LEN;
            if (g_big[i][j] != ID + 1 && cmax(bestRate, R)) bestPos = {i, j};
        }
    }
    used[x][y] = DIR + 1;
    queue<pair<pii, int>> q;
    q.push({{x, y}, 0});
    while (!q.empty()) {
        int curx = q.front().F.F, cury = q.front().F.S;
        int L = q.front().S;
        q.pop();
        if (pii{curx, cury} == bestPos) {
            int cnt = 0;
            while (pii{curx + commandsDir[(used[curx][cury] - 1)^1].F, cury + commandsDir[(used[curx][cury] - 1)^1].S} != pii{x, y}) {
                int D = used[curx][cury] - 1;
                curx += commandsDir[D ^ 1].F;
                cury += commandsDir[D ^ 1].S;
                cnt++;
            }
            if (cnt + 2 < MAXLAYER_) return -1;
            return used[curx][cury] - 1;
        }
        for (int i = 0; i < 4; i++) {
            if ((i ^ 1) == used[curx][cury] - 1) continue;
            auto dx = commandsDir[i];
            int X = curx + dx.F, Y = cury + dx.S;
            if (check_coord(X, Y) && !used[X][Y] && lines_big[X][Y] != ID + 1 && L + 1 != safe_area[X][Y]) {
                used[X][Y] = i + 1;
                q.push({{X, Y}, L + 1});
            }
        }
    }
    return rnd() % 4;
}

pair<pii, int> time_calculating(int my_x, int my_y, int T) {
    int k = 1;
    if (T < 15) k = 2;

    int was_MAXLAYER_ = MAXLAYER_;
    int was_maxPathLen = maxPathLen;
    int was_maxCandidateCount = maxCandidateCount;
    if (len(P) > 2) {
        MAXLAYER_ = MAXLAYER_ + 1 + k;
        maxPathLen = 15 + 5 * k;
        maxCandidateCount = 20 + 10 * k;
    }

    vector<vector<char>> kekused(n_big, vector<char>(m_big));
    auto res = dfs(my_x, my_y, kekused, 0, curDir, MAXLAYER_);

    MAXLAYER_ = was_MAXLAYER_;
    maxPathLen = was_maxPathLen;
    maxCandidateCount = was_maxCandidateCount;
    return res;
}

long long to_ms(long long dx) {
    return ((ld)dx / CLOCKS_PER_SEC) * 1000;
}

signed main() {
    iostream::sync_with_stdio(false);
    cin.tie(0);
    cout.tie(0);
    srand(time(NULL));
    string input_string, input_type;

    while (true) {
        input_string.clear();
        getline(cin, input_string); 

        long long START = clock();
        json state = json::parse(input_string);

        if (state["type"] == "end_game") return 0;
        if (state["type"] == "start_game") {
            init_game(state);
            continue;
        }
        init_tick(state);
        if (TICK == 1) {
            curDir = rnd() % 4;
            json res;
            res["command"] = commands[curDir];
            cout << res.dump() << endl;
            continue;
        }
        int my_x = P[ID].x_big, my_y = P[ID].y_big;
        string deg = "";

        vector<vector<char>> kekused(n_big, vector<char>(m_big));
        auto step = dfs(my_x, my_y, kekused, 0, curDir, MAXLAYER_);
        if (step.F.F < 60) {
            timer_mulct = 0;
            mulct = mulct_special;
        }

        long long T = to_ms((long long)clock() - START);
        if (T <= 100) step = time_calculating(my_x, my_y, T);

        deg += to_string(step.F.F) + ":" + to_string(step.S) + " >> ";
        int next = 0;
        if (step.F.F == 0) {
            deg += "1: ";
            timer_mulct = 0;
            mulct = mulct_special;
            next = best_border(my_x, my_y, curDir);
            if (next != -1) step.S = next;
        } else {
            timer_mulct++;
            to_best_border.clear();
        }
        if (step.F.F < -INF / 2) {
            deg += "2: ";
            auto path = get_path_to_area(ID);
            if (len(path) == 0) {
                for (int i = 0; i < 4; i++) {
                    int X = my_x + commandsDir[i].F, Y = my_y + commandsDir[i].S;
                    if (check_coord(X, Y)) step.S = i;
                }
            } else {
                for (int i = 0; i < 4; i++) {
                    int X = my_x + commandsDir[i].F, Y = my_y + commandsDir[i].S;
                    if (check_coord(X, Y) && pii{X, Y} == path.back()) step.S = i;
                }
            }
        }
        deg += to_string(step.S) + ";";
        if (timer_mulct >= limit_change_mulct) mulct = mulct_standard;
        json res;
        curDir = step.S;
        res["command"] = commands[curDir];
        deb = "";
        auto END = clock();
        long long elapsed = to_ms((long long)clock() - START);
        res["debug"] = to_string(elapsed) + "ms" + " " + deg + " " + to_string(T) + " -- " + to_string(elapsed);
        #ifdef LOCAL
            cerr << res["debug"] << "\n";
        #endif
        cout << res.dump() << endl;
    }
    return 0;
}   