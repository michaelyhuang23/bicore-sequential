
#include <iostream>
#include <fstream>
#include <utility>
#include <algorithm>
#include <vector>
#include <queue>
#include <chrono>
#include <unordered_set>
#include <fstream>
using namespace std;
using uintE  = unsigned long;
using intE = long;
using uintT = unsigned long long;
using intT = long long;

struct Graph{
  intE n, nVal;
  intT m;
  intE* degs;
  intT* offsets;
  intE* edges;
  Graph(intE n_, intE nVal_, intT m_, intE* degs_, intT* offsets_, intE* edges_)
    : n(n_), nVal(nVal_), m(m_), degs(degs_), offsets(offsets_), edges(edges_) {}
  Graph(string file_path){
    ifstream fin(file_path);
    string s; fin>>s;
    fin >> n; fin >> m;
    offsets = new intT[n];
    degs = new intE[n];
    edges = new intE[m];
    for(intE i=0; i<n; i++) cin >> offsets[i];
    for(intE i=0; i<n-1; i++) degs[i]=offsets[i+1]-offsets[i];
    degs[n-1] = m-offsets[n-1];
    for(intT i=0; i<m; i++) cin >> edges[i];
  }
  Graph(const Graph& G)
      : n(G.n),
        nVal(G.nVal),
        m(G.m)
  {
    degs = new intE[n]; offsets = new intT[n]; edges = new intE[m];
    copy(G.degs, G.degs+n, degs); copy(G.offsets, G.offsets+n, offsets);
    copy(G.edges, G.edges+n, edges); 
  }

  Graph& operator=(const Graph& G){
    clear();
    n = G.n; nVal = G.nVal; m = G.m;
    degs = new intE[n]; offsets = new intT[n]; edges = new intE[m];
    copy(G.degs, G.degs+n, degs); copy(G.offsets, G.offsets+n, offsets);
    copy(G.edges, G.edges+n, edges); 
    return *this;
  }

  Graph(Graph&& G)
      : n(G.n),
        nVal(G.nVal),
        m(G.m),
        degs(G.degs),
        offsets(G.offsets),
        edges(G.edges)
  {
    G.n = 0; G.m = 0; G.nVal = 0;
    G.degs = nullptr; G.offsets = nullptr; G.edges = nullptr;
  }

  Graph& operator=(Graph&& G){
    clear();
    n = G.n; nVal = G.nVal; m = G.m;
    degs = G.degs; offsets = G.offsets; edges = G.edges;
    G.n = 0; G.m = 0;
    G.degs = nullptr; G.offsets = nullptr; G.edges = nullptr;
    return *this;
  }

  inline void clear() {
    delete[] degs; delete[] offsets; delete[] edges;
  }

  ~Graph(){ clear(); }

  inline Graph shrink_graph(timer& st, const vector<intE>& D, intE n_a, intE n_b, intE cutoffA, intE cutoffB){
    size_t nValid = n;
    st.start();
    intE* degs_ = new intE[n]; copy(D.begin(), D.end(), degs_);
    for(intE i = 0; i<n_a; i++){
      bool cond = D[i]<cutoffA;
      degs_[i] *= (!cond);
      nValid -= cond;
    } 
    for(intE i = n_a; i<n; i++){
      bool cond = D[i]<cutoffB;
      degs_[i] *= (!cond);
      nValid -= cond;
    }
    intT* offsets_ = new intT[n+1]; offsets_[0]=0;
    for(intE i = 1; i<=n; i++) offsets_[i] = offsets_[i-1] + degs_[i-1];
    const size_t m = offsets_[n];
    intE* edges_ = new intE[m];
    uintT idx = 0;
    for(intE i = 0; i<n; i++){
      intE oldDeg = degs[i], offset = offsets_[i];
      if(degs_[i] == 0){
        idx += oldDeg;
        continue;
      }
      for(intE oj = 0; oj<oldDeg; oj++, idx++){
        intE oid = edges[idx];
        edges_[offset] = oid; 
        offset+=(degs_[oid]>0);
      }
    }
    st.stop();
    return Graph(n, nValid, m, degs_, offsets_, edges_);
  }
};

template <class E>
struct dyn_arr {
	E* A;
	size_t size;
	size_t capacity;
	bool alloc;

	void del() {
		// free allocated memory and set allocated to false
		if (alloc) {
			delete[] A;
			alloc = false;
		}
    }
	void clear() {
		size = 0;
	}
	inline void resize(size_t new_size) {
		if (new_size + size > capacity) {
			size_t new_capacity = max(2 * (new_size + size), 2000); // k dyn array min bucket size = 2000
			E* nA = new E[new_capacity];
      copy(A, A+size, nA);
			if (alloc) {
				delete[] A; // clear for new
			}
			A = nA; // new array
			capacity = new_capacity;
			alloc = true;
		}
	}
	inline void insert(E val, size_t pos) { 
		A[size + pos] = val; 
	}
	inline void push_back(E val) {
      	A[size] = val;
      	size++;
    }
};

struct Buckets{
	vector<intE>* bkts;
	vector<intE>& degs;
	intE ahead, curPos;
	intE n,curDeg;
	Buckets(vector<intE>& degs_, intE startPos, intE endPos)
	 : degs(degs_), curPos(0)
	{
		intE maxDeg = 0;
		intE minDeg = numeric_limits<intE>::max();
		for(size_t i=startPos; i<endPos; i++) {
			maxDeg = max(degs[i], maxDeg);
			if(degs[i]>0) minDeg = min(degs[i], minDeg);
		}
		bkts = new vector<intE>[maxDeg+1];
		ahead = 0;
		for(size_t i=startPos; i<endPos; i++)
			if(degs[i]>0){bkts[degs[i]].push_back(i); ahead++;}
		curDeg = minDeg;
		n = maxDeg;
	}

	inline void update(intE idx, intE newDeg){ bkts[newDeg].push_back(idx); }

	inline intE next_vtx(){
		if(curPos >= bkts[curDeg].size()){
			curDeg++;
			curPos = 0;
			while(curDeg <= n && bkts[curDeg].size() == 0) curDeg++;
		}
		vector<intE>& bkt = bkts[curDeg];
		while(curPos < bkt.size() && degs[bkt[curPos]] != curDeg) curPos++;
		if(curPos < bkt.size()) {ahead--; return bkt[curPos++];}
		else return next_vtx();
	}

	inline vector<intE> next_bucket(){
		vector<intE> filterBkt; filterBkt.reserve(bkts[curDeg].size());
		while(filterBkt.size()==0){
			while(curDeg <= n && bkts[curDeg].size() == 0) curDeg++;
			vector<intE>& bkt = bkts[curDeg];
			for(intE i = bkt.size()-1; true; i--){
				if(degs[bkt[i]] == curDeg) filterBkt.push_back(bkt[i]);
				bkt.pop_back();
				if(i==0) break;
			}
		}
		ahead -= filterBkt.size();	
		return filterBkt;
	}

	inline bool empty(){
		return ahead == 0;
	}
};

template <class Graph>
inline void BiCore_serial(Graph &G, size_t num_buckets = 16, size_t bipartition = 2, size_t peel_core_alpha = 0, size_t peel_core_beta = 0)
{
	cout << "starting" << endl;
	const size_t n = G.n;					// # of vertices
	const size_t n_a = bipartition + 1;		// number of vertices in first partition
	const size_t n_b = n - bipartition - 1; // number of vertices in second partition

	auto ret = KCore(G, num_buckets);
	
	int max_ret = 0;
	for (int i = 0; i < ret.size(); i++) {
		max_ret = ret[i] > max_ret ? ret[i] : max_ret;
	}

	const intE delta = static_cast<intE>(max_ret);
	double pqt = 0;
	double pt = 0;
	vector<intE> DA(n);
	for(size_t i=0; i<n; i++) DA[i] = G.get_vertex(i).out_degree();
	vector<intE> DB = DA;
	Graph GA = G.copy();
	Graph GB = G.copy();
	cout<<"finished preprocessing"<<endl;
	for(intE core = 1; core<=delta; core++){
		cout<<"running PeelFixA core "<<core<<endl;
		auto ret = PeelFixA(GA, DA, core, n_a, n_b);
		pqt += ret.first;
		pt += ret.second;
	}
	for(intE core = 1; core<=delta; core++){
		cout<<"running PeelFixB core "<<core<<endl;
		auto ret = PeelFixB(GB, DB, core, n_a, n_b);
		pqt += ret.first;
		pt += ret.second;
	}
	cout<<"pq time "<<pqt<<endl;
	cout<<"pt time "<<pt<<endl;
	//mkt.reportTotal("make_graph time");
}

inline void check(Graph& G, vector<intE>& D, size_t n_a, size_t n_b, intE cutoffA, intE cutoffB){
	const size_t n = n_a + n_b;
	for(intE i = 0; i<n; i++){
		if(i<n_a && D[i]<cutoffA) continue;
		if(i>=n_a && D[i]<cutoffB) continue;
		auto neighbors = G.get_vertex(i).out_neighbors();
		intE idx = 0;
		for(intE j = 0; j<neighbors.degree; j++){
			intE neigh = neighbors.get_neighbor(j);
			if(neigh<n_a && D[neigh]<cutoffA) continue;
			if(neigh>=n_a && D[neigh]<cutoffB) continue;
			if(idx>=D[i])
				cout<<i<<" "<<idx<<" "<<D[i]<<endl;
			assert(idx<D[i]);idx++;
		}
	}
}

inline pair<double, double> PeelFixA(Graph& G, vector<intE>& Deg, intE alpha, size_t n_a, size_t n_b)
{
	const size_t n = n_a + n_b;
	timer pqt, pt, st;
	intE rho_alpha = 0;
	intE max_beta = 0;
	intE vtxCount = n;
	bool firstMove = true;
	pt.start();

	vector<intE> uDel;
	for (size_t i = 0; i < n_a; i++)
		if (Deg[i] == alpha-1) uDel.push_back(i);
	// (alpha,0)
	// peels all vertices in U which are < alpha, and repeatedly peels vertices in V which has deg == 0
	while (uDel.size()>0)
	{
		vector<intE> newUDel;
		for(intE const& ui : uDel){
			auto neighborsUi = G.get_vertex(ui).out_neighbors();
			for(intE i = 0; i<neighborsUi.degree; i++){
				intE vi = neighborsUi.get_neighbor(i);
				if(Deg[vi]-- ==1){
					auto neighborsVi = G.get_vertex(vi).out_neighbors();
					for(intE j = 0; j<neighborsVi.degree; j++){
						intE uii = neighborsVi.get_neighbor(j); 
						if(Deg[uii]-- == alpha) newUDel.push_back(uii);
					}
				}
			}
		}
		uDel = move(newUDel);
	}
	vector<intE> D = Deg;
	for(intE i=0; i<n_a; i++) if(D[i]<alpha) vtxCount--;
	for(intE i=n_a; i<n; i++) if(D[i]<1) vtxCount--;
	Graph new_G;
	if(vtxCount*1.1 < G.nValid){
		firstMove=false;
		new_G = shrink_graph(st,G, D, n_a, n_b, alpha, 1);
		G = new_G;
		cout<<"compact at start "<<vtxCount<<endl;
	} else 
		new_G = move(G);

	pt.stop();

	pqt.start();

	Buckets bbuckets(D, n_a, n);
	pqt.stop();
	size_t iter = 0;
	vector<size_t> tracker(n, 0);
	dyn_arr<intE> changeVtx(16);
	while (!bbuckets.empty())
	{
		iter++;
		vector<intE> bkt = bbuckets.next_bucket();
		if(bbuckets.curDeg > max_beta){
			if(vtxCount*3.5 < new_G.nValid && new_G.nValid*10 > n){
				if(firstMove){
					firstMove = false;
					G = move(new_G);
					new_G = shrink_graph(st,G, D, n_a, n_b, alpha, max_beta+1);
				}else
					new_G = shrink_graph(st,new_G, D, n_a, n_b, alpha, max_beta+1);
				cout<<"compact "<<vtxCount<<" "<<new_G.nValid<<endl;
			}
			max_beta = bbuckets.curDeg;
		}
		for(auto const& vi : bkt){
			vtxCount--;
			auto neighborsVi = new_G.get_vertex(vi).out_neighbors();
			for(intE i = 0; i<neighborsVi.degree; i++){
				auto ui = neighborsVi.get_neighbor(i);
				if(D[ui]-- == alpha){
					vtxCount--;
					auto neighborsUi = new_G.get_vertex(ui).out_neighbors();
					for(intE j = 0; j<neighborsUi.degree; j++){
						auto vii = neighborsUi.get_neighbor(j); 
						changeVtx.resize_serial(1);
						changeVtx.A[changeVtx.size] = vii;
						size_t curIter = tracker[vii];
						bool cond = (D[vii]-- > max_beta) & (curIter!=iter);
						changeVtx.size += cond;
						tracker[vii] += (iter - curIter)*cond;
					}
				}
			}
		}
		for(intE i = 0; i<changeVtx.size; i++){
			intE vii = changeVtx.A[i];
			D[vii] = max(D[vii], max_beta);
			bbuckets.update(vii, D[vii]);
		}
		changeVtx.clear();
		rho_alpha++;
	}
	cout<<rho_alpha << " "<<max_beta<<endl;
	if(firstMove) G = move(new_G);
	return make_pair(pqt.get_total(), st.get_total());
}

inline pair<double, double> PeelFixB(Graph& G, vector<intE>& Deg, intE beta, size_t n_a, size_t n_b)
{
	const size_t n = n_a + n_b;
	timer pqt,pt,st;
	intE rho_beta = 0;
	intE max_alpha = 0;
	intE vtxCount = n;
	bool firstMove = true;
	pt.start();

	vector<intE> vDel;
	for (intE i = n_a; i < n; i++)
		if (Deg[i] == beta-1) vDel.push_back(i);

	while (vDel.size()>0)
	{
		vector<intE> newVDel;
		for(intE const& vi : vDel){
			auto neighborsVi = G.get_vertex(vi).out_neighbors();
			for(intE i = 0; i<neighborsVi.degree; i++){
				intE ui = neighborsVi.get_neighbor(i);
				if(Deg[ui]-- ==1){
					auto neighborsUi = G.get_vertex(ui).out_neighbors();
					for(intE j = 0; j<neighborsUi.degree; j++){
						intE vii = neighborsUi.get_neighbor(j); 
						if(Deg[vii]-- ==beta) newVDel.push_back(vii);
					}
				}
			}
		}
		vDel = move(newVDel);
	}
	vector<intE> D = Deg;
	for(intE i=0; i<n_a; i++) if(D[i]<1) vtxCount--;
	for(intE i=n_a; i<n; i++) if(D[i]<beta) vtxCount--;
	Graph new_G;
	cout<<"initial count "<<vtxCount<<" "<<G.nValid<<endl;
	if(vtxCount*1.1 < G.nValid){
		firstMove=false;
		new_G = shrink_graph(st, G, D, n_a, n_b, 1, beta);
		G = new_G;
		cout<<"compact at start "<<vtxCount<<endl;
	}else 
		new_G = move(G);

	pt.stop();

	pqt.start();

	Buckets abuckets(D, 0, n_a);
	pqt.stop();
	size_t iter = 0;
	vector<size_t> tracker(n, 0);
	dyn_arr<intE> changeVtx(16);
	while (!abuckets.empty())
	{
		iter++;
		vector<intE> bkt = abuckets.next_bucket();
		if(abuckets.curDeg > max_alpha){
			if(vtxCount*3.5 < new_G.nValid && new_G.nValid*10 > n){
				if(firstMove){
					firstMove = false;
					G = move(new_G);
					new_G = shrink_graph(st,G, D, n_a, n_b, max_alpha+1, beta);
				}else
					new_G = shrink_graph(st,new_G, D, n_a, n_b, max_alpha+1, beta);
				cout<<"compact "<<vtxCount<<endl;
			}
			max_alpha = abuckets.curDeg;
		}
		for(auto const& ui : bkt){
			vtxCount--;
			auto neighborsUi = new_G.get_vertex(ui).out_neighbors();
			for(intE i = 0; i<neighborsUi.degree; i++){
				auto vi = neighborsUi.get_neighbor(i);
				if(D[vi]-- ==beta){
					vtxCount--;
					auto neighborsVi = new_G.get_vertex(vi).out_neighbors();
					for(intE j = 0; j<neighborsVi.degree; j++){
						auto uii = neighborsVi.get_neighbor(j); 
						changeVtx.resize_serial(1);
						changeVtx.A[changeVtx.size] = uii;
						size_t curIter = tracker[uii];
						bool cond = (D[uii]-- > max_alpha) & (curIter!=iter);
						changeVtx.size += cond;
						tracker[uii] += (iter - curIter)*cond;
					}
				}
			}
		}
		for(intE i = 0; i<changeVtx.size; i++){
			intE uii = changeVtx.A[i];
			D[uii] = max(D[uii], max_alpha);
			abuckets.update(uii,D[uii]);
		}
		changeVtx.clear();
		rho_beta++;
	}
	cout<<rho_beta << " "<<max_alpha<<endl;
	if(firstMove) G = move(new_G);
	return make_pair(pqt.get_total(), st.get_total());
}


