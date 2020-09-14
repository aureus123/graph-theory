/*
 * SOLVER - Computes the weighted upper irredundant/domination number
 * Made in 2018-2020 by Daniel Severin
 *
 * Requires IBM ILOG CPLEX 12.7
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <ilcplex/ilocplex.h>
#include <ilcplex/cplex.h>

/* for linux users: do not define VISUALC */
#ifndef VISUALC
#include <unistd.h>
#include <sys/times.h>
#else
#include <windows.h>
#endif

ILOSTLBEGIN

using namespace std;

/* CONSTANTS */

#define EPSILON 0.00001
#define INFDIST 9999999
#define MAXTIME 7200.0
#define VERBOSE
//#define SHOWINSTANCE
#define SHOWCPLEX
//#define SAVELP "form.lp"

/* FLAGS OF THE OPTIMIZATION */

//#define TUNEDPARAMS

/* GLOBAL VARIABLES */

bool r_heur, r_cliquer, r_domination, is_weighted; /* options selection */
int vertices, edges; /* number of vertices and edges */
int* weight; /* weight of each vertex */
int *edge_u, *edge_v; /* array of endpoints of edges */
int *degrees; /* degree of each vertex + 1, i.e. |N[v]| */
int **neigh_vertices; /* neighbors of each vertex including itself, i.e. N[v] */
int **adjacency; /* adjacency matrix: 0 means no adjacency; >0 gives the index to the edge + 1
				    also adjacency[u][u] = 1 */
int **dist; /* distance matrix */
int card, *Dset, *Dpriv; /* best solution found so far (Dset = vertices of the set; Dpriv[i] is the private of Dset[i] for all i) */
int LB, UB; /* bounds of the parameter */

/* FUNCTIONS */

/*
 * ECOclock - get a timestamp (in seconds)
 */
double ECOclock() {
#ifndef VISUALC
	/* measure user-time: use it on single-threaded system in Linux (more accurate) */
	struct tms buf;
	times(&buf);
	return ((double)buf.tms_utime) / (double)sysconf(_SC_CLK_TCK);
#else
	/* measure standard wall-clock: use it on Windows */
	return ((double)clock()) / (double)CLOCKS_PER_SEC;
#endif
}

/*
 * set_color - change color of text
 *   0 - Black, 1 - Blue, 2 - Green, 3 - Cyan, 4 - Red, 5 - Purple, 6 - Yellow, 7 - Gray
 *   8 - 15 - Brighter colors
 */
void set_color(int color)
{
#ifdef VERBOSE
#ifdef VISUALC
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), color);
#else
	const char* codes[] = {
	  "30", "34", "32", "36", "31", "35", "33", "37",
	  "90", "94", "92", "96", "91", "95", "93", "97"
	};
	printf("\e[%sm", codes[color]);
#endif
#endif
}

/*
 * bye - finish executing and show a message
 */
void bye(char *string)
{
#ifdef VERBOSE
	set_color(12);
	cout << string << endl;
	set_color(7);
#else
	std::cout.clear();
	cout << "0" << endl;
#endif
	exit(1);
}

/*
 * read_graph - read a graph in the following format:
 *   in the first line, the number of vertices and edges separated by a colon ":"
 *   then, for each line, the endpoints of an edge (u,v) where u < v
 *   note that vertices starts from 0, i.e. 0 < v < |V|-1
 *   example for a diamond graph:
 *     4:5
 *     0,1
 *     0,2
 *     0,3
 *     1,2
 *     1,3
 */
void read_graph(char *filename)
{
	/* open file */
	FILE *stream = fopen(filename, "rt");
	if (!stream) bye("Graph file cannot be opened");
	fscanf(stream, "%d:%d\n", &vertices, &edges);
	/* do not accept graph of less than 4 vertices or stable sets */
	if (vertices < 3) bye("Number of vertices of out range!");
	if (edges < 1 || edges > vertices*(vertices - 1) / 2) bye("Number of edges out of range!");

	/* ask for memory */
	weight = new int[vertices];
	degrees = new int[vertices];
	adjacency = new int*[vertices];
	for (int u = 0; u < vertices; u++) {
		weight[u] = 1;
		degrees[u] = 1;
		adjacency[u] = new int[vertices];
		for (int v = 0; v < vertices; v++) adjacency[u][v] = 0;
		adjacency[u][u] = 1;
	}
	is_weighted = false;
	edge_u = new int[edges];
	edge_v = new int[edges];

	/* read edges */
	for (int e = 0; e < edges; e++) {
		int u, v;
		fscanf(stream, "%d,%d\n", &u, &v);
		if (u < 0 || u >= v || v >= vertices) {
			cout << "Error reading edge " << e + 1 << "!" << endl;
			bye("Bye!");
		}
		if (adjacency[u][v] != 0) {
			cout << "A repeated edge was found: (" << u << ", " << v << ")" << endl;
			bye("Bye!");
		}
		else {
			degrees[u]++;
			degrees[v]++;
			edge_u[e] = u;
			edge_v[e] = v;
			adjacency[u][v] = e + 1;
			adjacency[v][u] = e + 1;
		}
	}
	fclose(stream);

	/* also closed neighborhoods are computed */
	neigh_vertices = new int*[vertices];
	for (int v = 0; v < vertices; v++) {
		int degree = degrees[v];

		/* ask for more memory and fill it */
		neigh_vertices[v] = new int[degree];
		neigh_vertices[v][0] = v;
		int d = 1;
		for (int e = 0; e < edges; e++) {
			if (edge_u[e] == v) {
				int w = edge_v[e];
				neigh_vertices[v][d] = w;
				d++;
			}
			if (edge_v[e] == v) {
				int w = edge_u[e];
				neigh_vertices[v][d] = w;
				d++;
			}
		}

		/* check if everything is on order */
		if (degree != d) bye("Internal error!");
	}
#ifdef SHOWINSTANCE
	cout << endl << "Closed neighborhoods:" << endl;
	for (int v = 0; v < vertices; v++) {
		cout << "N[" << v << "] = {";
		int degree = degrees[v];
		for (int d = 0; d < degree; d++) cout << " " << neigh_vertices[v][d];
		cout << " }, degree = " << degree << endl;
	}
#endif
}

/*
 * read_weight - read the weights of an instance in the following format:
 *   in the first line, the number of vertices
 *   the next line has a number per vertex, in ascending order (w_0, w_1, w_2, ...)
 * example for a graph of 5 vertices:
 *   5
 *   1 2 2 1 2
 *
 */
void read_weight(char* filename)
{
	int vv;

	/* open file */
	FILE* stream = fopen(filename, "rt");
	if (!stream) bye("Weight file cannot be opened");
	fscanf(stream, "%d\n", &vv);
	/* check if the number of vertices is right */
	if (vv != vertices) bye("Number of vertices differ from the graph!");

	/* read weights */
	for (int v = 0; v < vertices; v++) {
		int w;
		fscanf(stream, "%d", &w);
		if (w <= 0 || w >= 10000) bye("Weights should be between 1 and 10000!");
		weight[v] = w;
	}
	fclose(stream);
	is_weighted = true;

#ifdef SHOWINSTANCE
	cout << endl << "Weights:";
	for (int v = 0; v < vertices; v++) cout << " " << weight[v];
	cout << "." << endl;
#endif
}

/*
 * connected() - check if G is a connected graph
 * in addition, we compute a matrix of distances between vertices
 */
bool connected()
{
	/* we ask for memory and fill the distance matrix with 0 in the diagonal, 1 for neighbors and +inf for the remaining entries */
	dist = new int*[vertices];
	for (int u = 0; u < vertices; u++) {
		dist[u] = new int[vertices];
		for (int v = 0; v < vertices; v++) {
			int d = INFDIST;
			if (u == v)	d = 0;
			else { if (adjacency[u][v] > 0) d = 1; }
			dist[u][v] = d;
		}
	}

	/* we use a simple implementation of Floyd algorithm (note: it is not the best way of knowing if G is connected!) */
	for (int v = 0; v < vertices; v++) {
		for (int u = 0; u < vertices; u++) {
			for (int w = 0; w < vertices; w++) {
				int sum = dist[u][v] + dist[v][w];
				if (sum < dist[u][w]) dist[u][w] = sum;
			}
		}
	}

	/* compute diameter */
	int diameter = 0;
	for (int u = 0; u < vertices - 1; u++) {
		for (int v = u + 1; v < vertices; v++) {
			int d = dist[u][v];
			if (d >= INFDIST) {
				cout << "There is no path between " << u << " and " << v << "." << endl;
				return false;
			}
			if (diameter < d) diameter = d;
		}
	}
	cout << "Diameter of G: " << diameter << endl;

	return true;
}

/*
 * get_bounds - compute initial lower and upper bounds
 */
bool get_bounds()
{
	int *D = new int[vertices];
	bool *W = new bool[vertices];
	bool *R = new bool[vertices];
	bool *tmp = new bool[vertices];

	int *sD_size = new int[vertices];
	int **sD = new int*[vertices];
	for (int z = 0; z < vertices; z++) sD[z] = new int[degrees[z]];

	int delta_min = INFDIST;

	/* Start with Dmax <- { vertex of max. weight } */
	int zmax, wmax = 0;
	for (int z = 0; z < vertices; z++) {
		if (weight[z] > wmax) {
			zmax = z;
			wmax = weight[z];
		}
	}
	card = 0;
	Dset[card] = zmax;
	Dpriv[card++] = zmax;
	LB = wmax;

	for (int v1 = 0; v1 < vertices - 1; v1++) {
		for (int v2 = v1 + 1; v2 < vertices; v2++) {
			if (v1 != v2) {
				/* compute D=emptyset, R=V, sD(v1)=N[v1]-N[v2], sD(v2)=N[v2]-N[v1], W=N[v1]cupN[v2]
					 D (and D_size and D_weight), sD (and sD_size)     <- represented as an array
					 R (and R_size), W (and W_weight)                  <- represented as a characteristic vector */
				int D_size = 0;
				int D_weight = 0;
				int R_size = vertices;
				int W_weight = 0;
				sD_size[v1] = 0;
				sD_size[v2] = 0;
				for (int z = 0; z < vertices; z++) {
					R[z] = true;
					W[z] = false;
				}
				int u1 = -1, u2 = -1;
				for (int z = 0; z < vertices; z++) {
					bool is_in_Nv1 = adjacency[v1][z] > 0;
					bool is_in_Nv2 = adjacency[v2][z] > 0;
					if (is_in_Nv1 || is_in_Nv2) {
						W[z] = true;
						W_weight += weight[z];
					}
					if (is_in_Nv1 && !is_in_Nv2) {
						sD[v1][sD_size[v1]++] = z;
						u1 = z;
					}
					if (is_in_Nv2 && !is_in_Nv1) {
						sD[v2][sD_size[v2]++] = z;
						u2 = z;
					}
				}

				/* if u1 and u2 exists, proceed */
				if (u1 != -1 && u2 != -1) {
					int delta = W_weight - weight[u1] - weight[u2];
					if (delta < delta_min) delta_min = delta;

					/* now, perform the greedy heuristic; start by assigning D = { v1, v2 }, R = V - D */
					D[D_size++] = v1; D[D_size++] = v2;
					D_weight += weight[v1] + weight[v2];
					R[v1] = false; R_size--; R[v2] = false; R_size--;

					while (R_size > 0) {
						int v = -1;
						float best_metric = -1.0;
						for (int z = 0; z < vertices; z++) {
							if (R[z]) {
								/* check if z is an eligible vertex */
								int NvminusW_card = 0;
								for (int n = 0; n < degrees[z]; n++) {
									int nei = neigh_vertices[z][n];
									if (!W[nei]) NvminusW_card++;
								}
								if (NvminusW_card == 0) {
									/* do not choose z in future iterations */
									R[z] = false; R_size--;
								}
								else {
									bool eligible = true;
									for (int d = 0; d < D_size; d++) {
										int u = D[d];
										bool sDuminusNv_nonempty = false;
										for (int q = 0; q < sD_size[u]; q++) {
											int priv = sD[u][q];
											if (adjacency[z][priv] == 0) {
												sDuminusNv_nonempty = true;
												break;
											}
										}
										if (sDuminusNv_nonempty == false) {
											/* do not choose z in future iterations */
											R[z] = false; R_size--;
											eligible = false;
											break;
										}
									}
									if (eligible) {
										/* compute the metric */
										float rnd = (float)rand() / (float)RAND_MAX;
										float metric = (1.0 - (float)NvminusW_card / (float)vertices) * (float)weight[z] + rnd / 10.0;
										if (metric > best_metric) {
											v = z;
											best_metric = metric;
										}
									}
								}
							}
						}
						if (v == -1) break;
						/* if some vertex was chosen, make updates:
							 sD(v) = N[v] - W
							 sD(u) = sD(u) - N[v] for all u in D
							 add v to D
							 remove v from R
							 W <- W cup N[v] */
						sD_size[v] = 0;
						for (int n = 0; n < degrees[v]; n++) {
							int nei = neigh_vertices[v][n];
							if (!W[nei]) sD[v][sD_size[v]++] = nei;
						}

						for (int d = 0; d < D_size; d++) {
							int u = D[d];
							/* compute tmp <- sD(u) - N[v] */
							for (int z = 0; z < vertices; z++) tmp[z] = false;
							for (int q = 0; q < sD_size[u]; q++) {
								int priv = sD[u][q];
								if (adjacency[v][priv] == 0) tmp[priv] = true;
							}
							/* then, copy tmp to sD(u) */
							sD_size[u] = 0;
							for (int z = 0; z < vertices; z++) {
								if (tmp[z]) sD[u][sD_size[u]++] = z;
							}
						}

						D[D_size++] = v; D_weight += weight[v];
						R[v] = false; R_size--;

						for (int n = 0; n < degrees[v]; n++) {
							int nei = neigh_vertices[v][n];
							if (!W[nei]) {
								W[nei] = true;
								W_weight += weight[v];
							}
						}
					}

					if (D_weight > LB) {
						/* update Dmax */
						for (int d = 0; d < D_size; d++) {
							int v = D[d];
							Dset[d] = v;
							Dpriv[d] = sD[v][0];
						}
						card = D_size;
						LB = D_weight;
					}
				}
			}
		}
	}

	/* compute upper bound: w(V) - delta_min */
	UB -= delta_min;

	/* free mem */
	for (int z = 0; z < vertices; z++) delete[] sD[z];
	delete[] sD;
	delete[] sD_size;
	delete[] tmp;
	delete[] R;
	delete[] W;
	delete[] D;

	if (LB == UB) {
		set_color(10);
		cout << "Optimal solution found! :)" << endl;
		set_color(7);
		return true;
	}
	return false;
}

/*
 * return index of variable x(u,v)
 */
int XUV(int u, int v)
{
	return v + vertices*u;
}

/*
 * optimize - Generate the model and solve it with CPLEX
 *   returns true if an optimal solution is reached
 */
bool optimize()
{
	IloEnv cplexenv;
	IloModel model(cplexenv);
	IloCplex cplex(model);
	IloNumVarArray vars(cplexenv);

	/* generate variables x(u,v): if v notin N[u] then the variable is set to zero */
	int count_variables = 0;
	char str[128];
	for (int u = 0; u < vertices; u++) {
		for (int v = 0; v < vertices; v++) {
			count_variables++;
			IloNum ub = 1.0;
			sprintf(str, "x(%d,%d)", u, v);
			if (adjacency[u][v] == 0) ub = 0.0;
			vars.add(IloNumVar(cplexenv, 0.0, ub, ILOBOOL, str));
		}
	}

	/* generate objective function: maximize sum_{uv} w_u x_uv */
	IloExpr fobj(cplexenv, 0);
	for (int u = 0; u < vertices; u++) {
		for (int d = 0; d < degrees[u]; d++) {
			int v = neigh_vertices[u][d];
			fobj += weight[u] * vars[XUV(u, v)];
		}
	}
	model.add(IloMaximize(cplexenv, fobj));

	int count_constraints = 0;

	/* if the heuristic was executed, then restrict the maximum objective <= UB
	 *    (we commented it since it doesn't seem to help) */
	/* if (r_heur) {
		cout << "Adding upper bound constraint..." << endl;
		IloExpr restr(cplexenv);
		for (int u = 0; u < vertices; u++) {
			for (int d = 0; d < degrees[u]; d++) {
				int v = neigh_vertices[u][d];
				restr += weight[u] * vars[XUV(u, v)];
			}
		}
		model.add(restr <= UB);
		count_constraints++;
	} */

	for (int u = 0; u < vertices; u++) {
		for (int z = 0; z < vertices; z++) {
			if (u != z) {
				IloExpr restr(cplexenv);
				bool is_not_empty = false;
				for (int v = 0; v < vertices; v++) {
					if (adjacency[u][v] > 0 && adjacency[z][v] > 0) {
						is_not_empty = true;
						restr += vars[XUV(u, v)];
					}
				}
				if (is_not_empty) {
					for (int d = 0; d < degrees[z]; d++) {
						int r = neigh_vertices[z][d];
						restr += vars[XUV(z, r)];
					}
					model.add(restr <= 1);
					count_constraints++;
				}
			}
		}
	}

	if (r_domination) {
		cout << "Adding domination constraints..." << endl;
		for (int u = 0; u < vertices; u++) {
			IloExpr restr(cplexenv);
			for (int v = 0; v < vertices; v++) {
				if (adjacency[u][v] > 0) {
					for (int z = 0; z < vertices; z++) {
						if (adjacency[v][z] > 0) restr += vars[XUV(v, z)];
					}
				}
			}
			model.add(restr >= 1);
			count_constraints++;
		}
	}

	cplex.setDefaults();
	cplex.setParam(IloCplex::Param::MIP::Tolerances::LowerCutoff, LB+1); /* <-- the solution should be at least better than the heuristic one */
#ifndef SHOWCPLEX
	cplex.setOut(cplexenv.getNullStream());
	cplex.setWarning(cplexenv.getNullStream());
#endif
	cplex.setParam(IloCplex::MIPDisplay, 3);
	cplex.setParam(IloCplex::WorkMem, 2048);
	cplex.setParam(IloCplex::TreLim, 2048);
	cplex.setParam(IloCplex::NodeFileInd, 0);
	cplex.setParam(IloCplex::TiLim, MAXTIME);
	cplex.setParam(IloCplex::EpGap, 0.0);
	cplex.setParam(IloCplex::EpAGap, 0.0);
	cplex.setParam(IloCplex::EpInt, EPSILON);
	cplex.setParam(IloCplex::Threads, 1);
	cplex.setParam(IloCplex::RandomSeed, 1);

#ifdef TUNECPLEX
	/* set Traditional B&C with pseudo costs branching strategy */
	//cplex.setParam(IloCplex::MIPSearch, 1);
	//cplex.setParam(IloCplex::VarSel, CPX_VARSEL_PSEUDO);

	/* turn off other features, including presolve */
	//cplex.setParam(IloCplex::PreInd, CPX_OFF);
	cplex.setParam(IloCplex::LBHeur, 0);
	cplex.setParam(IloCplex::Probe, -1);
	cplex.setParam(IloCplex::HeurFreq, -1);
	//cplex.setParam(IloCplex::RINSHeur, -1);
	//cplex.setParam(IloCplex::RepeatPresolve, 0);

	/* turn off cuts */
	//cplex.setParam(IloCplex::Cliques, -1);
	cplex.setParam(IloCplex::Covers, -1);
	cplex.setParam(IloCplex::DisjCuts, -1);
	cplex.setParam(IloCplex::FlowCovers, -1);
	cplex.setParam(IloCplex::FlowPaths, -1);
	cplex.setParam(IloCplex::FracCuts, -1);
	cplex.setParam(IloCplex::GUBCovers, -1);
	cplex.setParam(IloCplex::ImplBd, -1);
	cplex.setParam(IloCplex::MIRCuts, -1);
	//cplex.setParam(IloCplex::ZeroHalfCuts, -1);
	cplex.setParam(IloCplex::MCFCuts, -1);
	cplex.setParam(IloCplex::LiftProjCuts, -1);
	cplex.setParam(IloCplex::Param::MIP::Cuts::LocalImplied, -1); // <-- in CPLEX 12.6.1
#endif

	set_color(15);
	cout << "Model has " << count_variables << " variables and " << count_constraints << " constraints." << endl;
	set_color(7);

	cplex.extract(model);
#ifdef SAVELP
	cplex.exportModel(SAVELP);
	cout << "Integer formulation saved." << endl;
#endif

	/* solve it! */
	bool ret = false;
	cplex.solve();
	IloInt nodes = cplex.getNnodes();
	cout << "Number of nodes evaluated: " << nodes << endl;
	IloCplex::CplexStatus status = cplex.getCplexStatus();
	if (status == IloCplex::Optimal) {
		set_color(10);
		cout << "Optimal solution found! :)" << endl;
		set_color(7);
		ret = true;
	}
	else {
		switch (status) {
		case IloCplex::AbortTimeLim: cout << "Time limit reached!" << endl; break;
		case IloCplex::InfOrUnbd:
		case IloCplex::Infeasible:
			if (r_heur) {
				set_color(10);
				cout << "Infeasible. Therefore, then solution given by the heuristic is optimal!" << endl;
				set_color(7);
				UB = LB;
				cplexenv.end();
				return true;
			}
			else bye("Infeasible! :(");
		default: bye("Unexpected error :(");
		}
		UB = (int)(cplex.getBestObjValue() + EPSILON);
		cout << "Best upper bound is " << UB << endl;
		/* relgap = 100.0 * (upper - lower) / lower;       Rel Gap = |bestbound - bestinteger|/|bestinteger| */
	}

	/* retrieve the solution */
	LB = 0;
	card = 0;
	for (int u = 0; u < vertices; u++) {
		for (int v = 0; v < vertices; v++) {
			if (adjacency[u][v] > 0 && cplex.getValue(vars[XUV(u, v)]) > 0.1) {
				Dset[card] = u;
				Dpriv[card++] = v;
				LB += weight[u];
				break;
			}
		}
	}

	cplexenv.end();
	return ret;
}

/*
 * dimacs_gen - Generate the complement of G' and solve it with CLIQUER
 *   returns true if an optimal solution is reached
 */
void dimacs_gen() {
	if (is_weighted) bye("Not implemented yet for weighted graphs!");

	/* compute number of vertices and edges of G' */
	int vertices2 = 0;
	for (int u = 0; u < vertices; u++) vertices2 += degrees[u];

	int edges2 = 0;
	for (int u = 0; u < vertices; u++) {
		for (int du = 0; du < degrees[u]; du++) {
			int v = neigh_vertices[u][du];
			for (int z = 0; z < vertices; z++) {
				for (int dz = 0; dz < degrees[z]; dz++) {
					int r = neigh_vertices[z][dz];
					if ((u != z || v != r) && (adjacency[u][r] > 0 || adjacency[v][z] > 0)) edges2++;
				}
			}
		}
	}
	edges2 /= 2;

	FILE *stream = fopen("output.dimacs", "wt");
	if (!stream) bye("Output file cannot be written");

	fprintf(stream, "p edge %d %d\n", vertices2, edges2);

	int uv = 0;
	for (int u = 0; u < vertices; u++) {
		for (int du = 0; du < degrees[u]; du++) {
			int v = neigh_vertices[u][du];
			uv++;
			int zr = 0;
			for (int z = 0; z < vertices; z++) {
				for (int dz = 0; dz < degrees[z]; dz++) {
					int r = neigh_vertices[z][dz];
					zr++;
					if (uv < zr && (adjacency[u][r] > 0 || adjacency[v][z] > 0)) {
						fprintf(stream, "e %d %d\n", uv, zr);
					}
				}
			}
		}
	}
	fclose(stream);
}

void show_sol() {
	set_color(4);
	cout << "Solution (card = " << card << ", weight = " << LB << "):" << endl;
	for (int i = 0; i < card; i++) cout << "  private of " << Dset[i] << " is " << Dpriv[i] << endl;
	set_color(7);
}

/*
 * main - Main program
 */
int main(int argc, char **argv)
{
	double start_t, elapsed_t;

#ifndef VERBOSE
	std::cout.setstate(std::ios::failbit);
#endif
	set_color(15);
	cout << "SOLVER - Computes the weighted upper irredundant/domination number." << endl;
	cout << "Made in 2018-2020 by Daniel Severin." << endl;
	set_color(7);

	if (argc < 3) {
		cout << "Usage: solver option file.graph [file.weight]" << endl;
		cout << "The graph must have at least 3 vertices and must be connected." << endl;
		cout << "If the weight file is not given, every weight is 1." << endl;
		cout << "Options:" << endl;
		cout << "  1 - integer programming for solving IR_w(G)" << endl;
		cout << "  2 - heuristic + integer programming for solving IR_w(G)" << endl;
		cout << "  3 - generate complement of G' (DIMACS format) for solving IR_w(G) with CLIQUER" << endl;
		cout << "  4 - integer programming for solving Gamma_w(G)" << endl;
		bye("Bye!");
	}

	/* read model */
	r_heur = false;
	r_domination = false;
	r_cliquer = false;
	int opt = atoi(argv[1]);
	switch (opt) {
	case 1: break;
	case 2: r_heur = true; break;
	case 3: r_cliquer = true; break;
	case 4: r_domination = true; break;
	default: bye("Options must be between 1 and 4.");
	}

	/* read graph and weights */
	read_graph(argv[2]);
	if (argc > 3) read_weight(argv[3]);

	set_color(6);
	cout << "Statistics:" << endl;
	int clique_size = vertices * (vertices - 1) / 2;
	float density = 100.0 * (float)edges / (float)clique_size;
	cout << "  |V| = " << vertices << ", |E| = " << edges << " (density = " << density << "%)." << endl;

	Dset = new int[vertices];
	Dpriv = new int[vertices];
	card = 0;
	LB = 0; UB = 0;
	for (int v = 0; v < vertices; v++) UB += weight[v];
	cout << "  Initial bounds:  LB = " << LB << ", UB = " << UB << "." << endl;

	/* check if G is connected */
	if (connected() == false) bye("G is not connected, please decompose it first!");
	set_color(7);

	/* run heuristic */
	if (r_heur) {
		start_t = ECOclock();
		bool status = get_bounds();
		elapsed_t = ECOclock() - start_t;

		cout << "New bounds:  LB = " << LB << ", UB = " << UB << "." << endl;
		show_sol();
		set_color(11);
		cout << "Time elapsed during optimization = " << elapsed_t << " sec." << endl;
		set_color(7);

		if (status) goto free_mem;
	}

	/* perform optimization */
	if (r_cliquer) dimacs_gen();
	else {
		start_t = ECOclock();
		bool status;
		status = optimize();
		elapsed_t = ECOclock() - start_t;

		show_sol();
		set_color(11);
		cout << "Time elapsed during optimization = " << elapsed_t << " sec." << endl;
		if (status == false) bye("Optimality not reached :(");
	}

	/* free memory */
free_mem:;
	for (int v = 0; v < vertices; v++) delete[] dist[v];
	delete[] dist;
	delete[] Dpriv;
	delete[] Dset;
	for (int v = 0; v < vertices; v++) delete[] neigh_vertices[v];
	delete[] neigh_vertices;
	delete[] edge_v;
	delete[] edge_u;
	for (int v = 0; v < vertices; v++) delete[] adjacency[v];
	delete[] adjacency;
	delete[] degrees;
	delete[] weight;
	return 0;
}
