/*
 * SOLVER - Computes the weighted upper irredundant/domination number
 * Made in 2019-2020 by Daniel Severin
 */

//#define NOCPLEX
//#define CHECK_DIST

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>

/* for linux users: do not define VISUALC */
#ifndef VISUALC
#include <unistd.h>
#include <sys/times.h>
#else
#include <windows.h>
#include <time.h>
#endif

/* EXTERNALS */
#ifndef NOCPLEX
bool optimize(int vert, int *weight, int *degrees, int **neigh_vertices, int **adjacency,
	bool r_domination, bool r_heur, int *LB, int *UB, int *card, int *Dset, int *Dpriv);
#endif

using namespace std;

/* CONSTANTS */

#define INFDIST 9999999
#define VERBOSE
//#define SHOWINSTANCE
#define CLASSIC_UB

/* GLOBAL VARIABLES */

static bool r_opt, r_heur, r_cliquer, r_domination, r_coq, is_weighted; /* options selection */
static int vertices, edges; /* number of vertices and edges */
static int vertices2, edges2; /* (only for DIMACS gen) vertices and edges of the complement of G' */
static float density, density2; /* densities of G and compl. of G' */
static int* weight; /* weight of each vertex */
static int *edge_u, *edge_v; /* array of endpoints of edges */
static int *degrees; /* degree of each vertex + 1, i.e. |N[v]| */
static int **neigh_vertices; /* neighbors of each vertex including itself, i.e. N[v] */
static int **adjacency; /* adjacency matrix: 0 means no adjacency; >0 gives the index to the edge + 1
				    also adjacency[u][u] = 1 */
static int card, *Dset, *Dpriv; /* best solution found so far (Dset = vertices of the set; Dpriv[i] is the private of Dset[i] for all i) */
static int LB, UB, UB_classic; /* bounds of the parameter */
#ifdef CHECK_DIST
static int **dist; /* distance matrix */
#endif

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

#ifdef CHECK_DIST
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
#endif

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

#ifdef CLASSIC_UB
	/* compute the upper bound: w(V) - min { w(N[v] - {u}) : v in V, u in N[v] } */
	int delta_min_classic = INFDIST;
	for (int v = 0; v < vertices; v++) {
		/* find the heaviest u in N[v] */
		int max_weight = 0;
		int max_u = -1;
		for (int d = 0; d < degrees[v]; d++) {
			int u = neigh_vertices[v][d];
			int w = weight[u];
			if (w > max_weight) {
				max_weight = w;
				max_u = u;
			}
		}
		/* compute w(N[v] - {u}) */
		int wNvminusu = 0;
		for (int d = 0; d < degrees[v]; d++) {
			int u = neigh_vertices[v][d];
			if (u != max_u) wNvminusu += weight[u];
		}
		if (wNvminusu < delta_min_classic) delta_min_classic = wNvminusu;
	}
	set_color(15);
	UB_classic = UB - delta_min_classic;
	cout << "Classic UB = w(V) - min { w(N[v] - {u}) : v in V, u in N[v] } = " << UB_classic << endl;
	set_color(7);
#else
	UB_classic = 0;
#endif

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
 * dimacs_gen - Generate the complement of G' and solve it with CLIQUER
 *   returns true if an optimal solution is reached
 */
void dimacs_gen() {
	if (is_weighted) bye("Not implemented yet for weighted graphs!");

	/* compute number of vertices and edges of G' */
	vertices2 = 0;
	for (int u = 0; u < vertices; u++) vertices2 += degrees[u];

	edges2 = 0;
	for (int u = 0; u < vertices; u++) {
		for (int du = 0; du < degrees[u]; du++) {
			int v = neigh_vertices[u][du];
			for (int z = 0; z < vertices; z++) {
				for (int dz = 0; dz < degrees[z]; dz++) {
					int r = neigh_vertices[z][dz];
					if ((u != z || v != r) && !(adjacency[u][r] > 0 || adjacency[v][z] > 0)) edges2++;
				}
			}
		}
	}
	edges2 /= 2;

	set_color(5);
	cout << endl << "Complement of the transformed graph:" << endl;
	int clique_size = vertices2 * (vertices2 - 1) / 2;
	density2 = 100.0 * (float)edges2 / (float)clique_size;
	cout << "  |V| = " << vertices2 << ", |E| = " << edges2 << " (density = " << density2 << "%)." << endl;
	set_color(7);

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
					if (uv < zr && !(adjacency[u][r] > 0 || adjacency[v][z] > 0)) {
						fprintf(stream, "e %d %d\n", uv, zr);
					}
				}
			}
		}
	}
	fclose(stream);
}

/*
 * show_sol - just show the solution on screen
 */
void show_sol() {
	set_color(4);
	cout << "Solution (card = " << card << ", weight = " << LB << "):" << endl;
	for (int i = 0; i < card; i++) cout << "  private of " << Dset[i] << " is " << Dpriv[i] << endl;
	set_color(7);
}

/*
 * save_certificate - save the current solution as a Coq certificate
 */
struct cmpstruct {
	int v;
	int priv;
};

int cmpfunc(const void *a, const void *b)
{
	int first = ((struct cmpstruct*)a)->v;
	int second = ((struct cmpstruct*)b)->v;
	if (second < first) return 1;
	if (second > first) return -1;
	return 0;
}

/* Old version (tactic-based, very slow) */
void save_certificate_old()
{
	char *filename;

	if (is_weighted) filename = "weighted1.v.template";
	else filename = "unweighted1.v.template";

	FILE *stream_in = fopen(filename, "rt");
	if (!stream_in) bye("Template file cannot be read");

	FILE *stream_out = fopen("certificate.v", "wt");
	if (!stream_out) bye("Certificate file cannot be written");

	/* before starting, the irredundant set must be ordered in ascending order */
	struct cmpstruct *set = new cmpstruct[card];
	for (int i = 0; i < card; i++) {
		set[i].v = Dset[i];
		set[i].priv = Dpriv[i];
	}
	qsort((void*)set, card, sizeof(cmpstruct), cmpfunc);

	int state = 0;

	while (state != -1) {
		if (feof(stream_in)) bye("Error reading template!");
		char c = 0;
		for (;;) {
			c = fgetc(stream_in);
			if (c != '#') fputc(c, stream_out);
			else break;
		}

		switch (state) {
		case 0: /* write number of vertices after Definition of n */
			fprintf(stream_out, "%d", vertices);
			state = 1;
			break;
		case 1: /* write the edges */
			for (int e = 0; e < edges; e++) {
				fprintf(stream_out, "    | %d, %d => true\n", edge_u[e], edge_v[e]);
			}
			if (is_weighted) state = 2;
			else state = 3;
			break;
		case 2: /* write the weights */
			for (int v = 0; v < vertices - 1; v++) {
				fprintf(stream_out, "      | Ordinal %d _ => %d\n", v, weight[v]);
			}
			fprintf(stream_out, "      | Ordinal _ _ => %d\n", weight[vertices - 1]);
			state = 3;
			break;
		case 3: /* write the irredundant set */
			for (int i = 0; i < card; i++) {
				fprintf(stream_out, "'v%d", set[i].v);
				if (i < card - 1) fprintf(stream_out, "; ");
			}
			state = 4;
			break;
		case 4: /* write n again */
			fprintf(stream_out, "%d", vertices);
			state = 5;
			break;
		case 5: /* write proof of privacity of each vertex */
			for (int i = 0; i < card; i++) {
				fprintf(stream_out, "\
    - rewrite(bool_irrelevance vltn isT) => _.\n\
      apply/set0Pn; exists 'v%d ; apply/privateP ; split=> //.\n\
      move => [u ultn]; do %d try destruct u.\n\
      all : try by rewrite(bool_irrelevance ultn isT).\n\
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;\n\
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).\n\
      suff : False by contradiction.\n\
      by move: ultn; apply/negP.\n", set[i].priv, vertices);
			}
			state = 6;
			break;
		case 6: /* write the lower bound */
			fprintf(stream_out, "%d", LB);
			state = 7;
			break;
		case 7: /* write the lower bound again */
			fprintf(stream_out, "%d", LB);
			state = 8;
			break;
		default: state = -1;
		}
	}

	fclose(stream_out);
	fclose(stream_in);
	cout << "Coq certificate written in certificate.v" << endl;
}

/* New version (computation-based) */
void save_certificate()
{
	char* filename;

	if (is_weighted) filename = "weighted2.v.template";
	else filename = "unweighted2.v.template";

	FILE* stream_in = fopen(filename, "rt");
	if (!stream_in) bye("Template file cannot be read");

	FILE* stream_out = fopen("certificate.v", "wt");
	if (!stream_out) bye("Certificate file cannot be written");

	/* before starting, the irredundant set must be ordered in ascending order */
	struct cmpstruct* set = new cmpstruct[card];
	for (int i = 0; i < card; i++) {
		set[i].v = Dset[i];
		set[i].priv = Dpriv[i];
	}
	qsort((void*)set, card, sizeof(cmpstruct), cmpfunc);

	int state = 0;

	while (state != -1) {
		if (feof(stream_in)) bye("Error reading template!");
		char c = 0;
		for (;;) {
			c = fgetc(stream_in);
			if (c != '#') fputc(c, stream_out);
			else break;
		}

		switch (state) {
		case 0: /* write number of vertices after Definition of n */
			fprintf(stream_out, "%d", vertices);
			state = 1;
			break;
		case 1: /* write the edges */
			for (int e = 0; e < edges; e++) {
				fprintf(stream_out, "    | %d, %d => true\n", edge_u[e], edge_v[e]);
			}
			if (is_weighted) state = 2;
			else state = 3;
			break;
		case 2: /* write the weights */
			for (int v = 0; v < vertices - 1; v++) {
				fprintf(stream_out, "      | Ordinal %d _ => %d\n", v, weight[v]);
			}
			fprintf(stream_out, "      | Ordinal _ _ => %d\n", weight[vertices - 1]);
			state = 3;
			break;
		case 3: /* write the irredundant set */
			for (int i = 0; i < card; i++) {
				fprintf(stream_out, "'v%d", set[i].v);
				if (i < card - 1) fprintf(stream_out, "; ");
			}
			state = 4;
			break;
		case 4: /* write the set again */
			for (int i = 0; i < card; i++) {
				fprintf(stream_out, "'v%d", set[i].v);
				if (i < card - 1) fprintf(stream_out, "; ");
			}
			if (is_weighted) state = 6;
			else state = 5;
			break;
		case 5: fputc('#', stream_out); state = 6; break;
		case 6: /* write the lower bound */
			fprintf(stream_out, "%d", LB);
			state = 7;
			break;
		case 7: /* write the lower bound again */
			fprintf(stream_out, "%d", LB);
			state = 8;
			break;
		default: state = -1;
		}
	}

	fclose(stream_out);
	fclose(stream_in);
	cout << "Coq certificate written in certificate.v" << endl;
}

/*
 * main - Main program
 */
int main(int argc, char **argv)
{
	double start_t, heur_t, opt_t;

#ifndef VERBOSE
	std::cout.setstate(std::ios::failbit);
#endif
	set_color(15);
	cout << "SOLVER - Computes the weighted upper irredundant/domination number." << endl;
	set_color(7);

	if (argc < 3) {
		cout << "Usage: solver option file.graph [file.weight]" << endl;
		cout << "The graph must have at least 3 vertices and must be connected." << endl;
		cout << "If the weight file is not given, every weight is 1." << endl;
		cout << "Options:" << endl;
		cout << "  1 - heuristic for obtaining bounds of IR_w(G)" << endl;
		cout << "  2 - integer programming for solving IR_w(G)" << endl;
		cout << "  3 - heuristic + integer programming for solving IR_w(G)" << endl;
		cout << "  4 - generate complement of G' (DIMACS format) for solving IR_w(G) with CLIQUER" << endl;
		cout << "  5 - integer programming for solving Gamma_w(G)" << endl;
		cout << "  0 - for testing: heur + int. programming + CLIQUER (also saves output file)" << endl;
		cout << "Options 0-3 also generate a Coq certificate." << endl;
		bye("Bye!");
	}

	/* read model */
	r_opt = false;
	r_heur = false;
	r_domination = false;
	r_cliquer = false;
	r_coq = false;
	int opt = atoi(argv[1]);
	switch (opt) {
	case 0: r_heur = true; r_coq = true; r_opt = true; r_cliquer = true; break;
	case 1: r_heur = true; r_coq = true; break;
	case 2: r_opt = true; r_coq = true; break;
	case 3: r_heur = true; r_opt = true; r_coq = true; break;
	case 4: r_cliquer = true; break;
	case 5: r_domination = true; r_opt = true; break;
	default: bye("Options must be between 1 and 4.");
	}

	/* read graph and weights */
	read_graph(argv[2]);
	if (argc > 3) read_weight(argv[3]);

	set_color(6);
	cout << "Statistics:" << endl;
	int clique_size = vertices * (vertices - 1) / 2;
	density = 100.0 * (float)edges / (float)clique_size;
	cout << "  |V| = " << vertices << ", |E| = " << edges << " (density = " << density << "%)." << endl;

	heur_t = 0.0;
	opt_t = 0.0;

	Dset = new int[vertices];
	Dpriv = new int[vertices];
	card = 0;
	LB = 0; UB = 0;
	for (int v = 0; v < vertices; v++) UB += weight[v];
	cout << "  Initial bounds:  LB = " << LB << ", UB = " << UB << "." << endl;

	/* check if G is connected */
	set_color(7);
#ifdef CHECK_DIST
	if (connected() == false) cout << "G is not connected, please decompose it first!" << endl;
#endif

	/* run heuristic */
	int UB_heur = 0, LB_heur = 0;
	bool is_solved = false;

	if (r_heur) {
		start_t = ECOclock();
		is_solved = get_bounds();
		heur_t = ECOclock() - start_t;

		cout << "New bounds:  LB = " << LB << ", UB = " << UB << "." << endl;
		LB_heur = LB;
		UB_heur = UB;
		show_sol();
		set_color(11);
		cout << "Time elapsed for heuristic = " << heur_t << " sec." << endl;
		set_color(7);

		if (is_solved) goto free_mem;
	}

	/* perform optimization */
	if (r_cliquer) dimacs_gen();

	if (r_opt) {
#ifndef NOCPLEX
		start_t = ECOclock();
		is_solved = optimize(vertices, weight, degrees, neigh_vertices, adjacency,
			                 r_domination, r_heur, &LB, &UB, &card, Dset, Dpriv);
		opt_t = ECOclock() - start_t;

		show_sol();
		set_color(11);
		cout << "Time elapsed during optimization = " << opt_t << " sec." << endl;
		set_color(7);
#else
		bye("Cannot proceed. Enable CPLEX.");
#endif
	}

	/* free memory */
free_mem:;
	if (r_coq) save_certificate();
	if (r_heur && r_opt && r_cliquer) {
		/* save results on output file */
		FILE *stream = fopen("output", "at");
		if (!stream) bye("Output file cannot be opened");
		fprintf(stream, "%s,%c,%d,%d,%.2f,%d,%d,%d,%.2f,%d,%d,%.2f,%c,%d,%d,%.2f", argv[2], is_weighted ? 'W' : 'U',
			        vertices, edges, density, UB_classic, UB_heur, LB_heur, heur_t, UB, LB, opt_t,
					is_solved ? 'Y' : 'N', vertices2, edges2, density2);
		fclose(stream);
	}

#ifdef CHECK_DIST
	for (int v = 0; v < vertices; v++) delete[] dist[v];
	delete[] dist;
#endif
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
