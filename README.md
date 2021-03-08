# Formalization of aspects of the Maximum Weighted Irredundant Set (MWIS) problem

This code contains some results related to the MWIS formalized in Coq/Ssreflect and
a heuristic implemented in C++ that computes a solution and a dual bound for this problem.

Our goal is to explore two ideas related to formalizing results of graph theory: our first
proposal is that some long proofs, involving a large number of cases that can be checked
mechanically, can be channeled through a proof assistant; the other is to analyze the
possibility of generating a Coq file that **certificates** a numerical value for a given
graph parameter.

An additional feature of the algorithm that finds a solution of the MWIS is that it generates
a Coq file with the instance and the proposed solution.

## Files and folders 🔧

- mwis: The formalized theory. Use "make" inside this folder to compile it.
  - mwis/check_ir.v: Some tools to check irredundancy, cardinality and weights of given graph and set.
  - mwis/prelim.v: Some preliminary results.
  - mwis/mwis.v: Main components of the theory.
  - mwis/mwis_prop.v: The _huge_ proofs involving claw-free and copaw-free graphs.

- solver: A heuristic for solving the MWIS problem. This code is able to
      generate a Coq certificate of a lower bound of IR_w(G).
      Use "make" inside this folder to compile it.

- instances: A testbed of 26 (unweighted) instances up to 100 vertices from the
      DIMACS challenge, and an instance of 48 vertices with weights corresponding
      to a service allocation problem of the city of Buenos Aires.

- certs: Coq certificates of the instances. Use "make easy" or "make hard" to check
      the easy or hard instances resp., or "make weighted" to check the weighted instance.	  

## Requirements 📋

MWIS formalization requires packages [_graph-theory 0.8_](https://github.com/coq-community/graph-theory) and its
dependencies (Coq 8.11+, MathComp 1.10+, finmap, hierarchy builder 0.10).
Certificate verification requires previously compiling the MWIS formalization.

## Authors and contact information ✒️

- Ricardo Katz ([**@rdkatz**](https://github.com/rdkatz)), mail: katz@cifasis-conicet.gov.ar
- Daniel Severín ([**@aureus123**](https://github.com/aureus123)), mail: daniel@fceia.unr.edu.ar
