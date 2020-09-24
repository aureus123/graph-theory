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

/* EXTERNALS */

void set_color(int color);
void bye(char *string);


ILOSTLBEGIN

using namespace std;

/* CONSTANTS */

#define EPSILON 0.00001
#define MAXTIME 30.0
#define SHOWCPLEX
//#define SAVELP "form.lp"
//#define TUNEDPARAMS

/* GLOBAL VARIABLES */

static int vertices;

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
bool optimize(int vert, int *weight, int *degrees, int **neigh_vertices, int **adjacency,
	bool r_domination, bool r_heur, int *LB, int *UB, int *card, int *Dset, int *Dpriv)
{
	IloEnv cplexenv;
	IloModel model(cplexenv);
	IloCplex cplex(model);
	IloNumVarArray vars(cplexenv);

	vertices = vert;

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
		model.add(restr <= *UB);
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
	cplex.setParam(IloCplex::Param::MIP::Tolerances::LowerCutoff, *LB+1); /* <-- the solution should be at least better than the heuristic one */
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

#ifdef TUNEDPARAMS
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
	bool is_sol_available = cplex.solve();
	IloInt nodes = cplex.getNnodes();
	cout << "Number of nodes evaluated: " << nodes << endl;
	IloCplex::CplexStatus status = cplex.getCplexStatus();
	if (status == IloCplex::Optimal) {
		set_color(10);
		cout << "Optimal solution found! :)" << endl;
		set_color(7);
		*UB = (int)(cplex.getBestObjValue() + EPSILON);
		ret = true;
	}
	else {
		switch (status) {
		case IloCplex::AbortTimeLim: cout << "Time limit reached!" << endl; break;
		case IloCplex::InfOrUnbd:
		case IloCplex::Infeasible:
			if (r_heur) {
				set_color(10);
				cout << "Infeasible. Therefore, the solution given by the heuristic is optimal!" << endl;
				set_color(7);
				*UB = *LB;
				cplexenv.end();
				return true;
			}
			else bye("Infeasible! :(");
		default: bye("Unexpected error :(");
		}
		*UB = (int)(cplex.getBestObjValue() + EPSILON);
		cout << "Optimality not reached :(" << endl << "Best upper bound is " << *UB << endl;
		/* relgap = 100.0 * (upper - lower) / lower;       Rel Gap = |bestbound - bestinteger|/|bestinteger| */
	}

	/* retrieve the solution */
	if (is_sol_available) {
		int wei = 0;
		int count = 0;
		for (int u = 0; u < vertices; u++) {
			for (int v = 0; v < vertices; v++) {
				if (adjacency[u][v] > 0 && cplex.getValue(vars[XUV(u, v)]) > 0.1) {
					Dset[count] = u;
					Dpriv[count++] = v;
					wei += weight[u];
					break;
				}
			}
		}
		*card = count;
		*LB = wei;
	}

	cplexenv.end();
	return ret;
}
