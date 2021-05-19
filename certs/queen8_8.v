
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 64.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 9 => true
    | 0, 18 => true
    | 0, 27 => true
    | 0, 36 => true
    | 0, 45 => true
    | 0, 54 => true
    | 0, 63 => true
    | 0, 1 => true
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 5 => true
    | 0, 6 => true
    | 0, 7 => true
    | 0, 8 => true
    | 0, 16 => true
    | 0, 24 => true
    | 0, 32 => true
    | 0, 40 => true
    | 0, 48 => true
    | 0, 56 => true
    | 1, 10 => true
    | 1, 19 => true
    | 1, 28 => true
    | 1, 37 => true
    | 1, 46 => true
    | 1, 55 => true
    | 1, 8 => true
    | 1, 2 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 5 => true
    | 1, 6 => true
    | 1, 7 => true
    | 1, 9 => true
    | 1, 17 => true
    | 1, 25 => true
    | 1, 33 => true
    | 1, 41 => true
    | 1, 49 => true
    | 1, 57 => true
    | 2, 11 => true
    | 2, 20 => true
    | 2, 29 => true
    | 2, 38 => true
    | 2, 47 => true
    | 2, 9 => true
    | 2, 16 => true
    | 2, 3 => true
    | 2, 4 => true
    | 2, 5 => true
    | 2, 6 => true
    | 2, 7 => true
    | 2, 10 => true
    | 2, 18 => true
    | 2, 26 => true
    | 2, 34 => true
    | 2, 42 => true
    | 2, 50 => true
    | 2, 58 => true
    | 3, 12 => true
    | 3, 21 => true
    | 3, 30 => true
    | 3, 39 => true
    | 3, 10 => true
    | 3, 17 => true
    | 3, 24 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 6 => true
    | 3, 7 => true
    | 3, 11 => true
    | 3, 19 => true
    | 3, 27 => true
    | 3, 35 => true
    | 3, 43 => true
    | 3, 51 => true
    | 3, 59 => true
    | 4, 13 => true
    | 4, 22 => true
    | 4, 31 => true
    | 4, 11 => true
    | 4, 18 => true
    | 4, 25 => true
    | 4, 32 => true
    | 4, 5 => true
    | 4, 6 => true
    | 4, 7 => true
    | 4, 12 => true
    | 4, 20 => true
    | 4, 28 => true
    | 4, 36 => true
    | 4, 44 => true
    | 4, 52 => true
    | 4, 60 => true
    | 5, 14 => true
    | 5, 23 => true
    | 5, 12 => true
    | 5, 19 => true
    | 5, 26 => true
    | 5, 33 => true
    | 5, 40 => true
    | 5, 6 => true
    | 5, 7 => true
    | 5, 13 => true
    | 5, 21 => true
    | 5, 29 => true
    | 5, 37 => true
    | 5, 45 => true
    | 5, 53 => true
    | 5, 61 => true
    | 6, 15 => true
    | 6, 13 => true
    | 6, 20 => true
    | 6, 27 => true
    | 6, 34 => true
    | 6, 41 => true
    | 6, 48 => true
    | 6, 7 => true
    | 6, 14 => true
    | 6, 22 => true
    | 6, 30 => true
    | 6, 38 => true
    | 6, 46 => true
    | 6, 54 => true
    | 6, 62 => true
    | 7, 14 => true
    | 7, 21 => true
    | 7, 28 => true
    | 7, 35 => true
    | 7, 42 => true
    | 7, 49 => true
    | 7, 56 => true
    | 7, 15 => true
    | 7, 23 => true
    | 7, 31 => true
    | 7, 39 => true
    | 7, 47 => true
    | 7, 55 => true
    | 7, 63 => true
    | 8, 17 => true
    | 8, 26 => true
    | 8, 35 => true
    | 8, 44 => true
    | 8, 53 => true
    | 8, 62 => true
    | 8, 9 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 12 => true
    | 8, 13 => true
    | 8, 14 => true
    | 8, 15 => true
    | 8, 16 => true
    | 8, 24 => true
    | 8, 32 => true
    | 8, 40 => true
    | 8, 48 => true
    | 8, 56 => true
    | 9, 18 => true
    | 9, 27 => true
    | 9, 36 => true
    | 9, 45 => true
    | 9, 54 => true
    | 9, 63 => true
    | 9, 16 => true
    | 9, 10 => true
    | 9, 11 => true
    | 9, 12 => true
    | 9, 13 => true
    | 9, 14 => true
    | 9, 15 => true
    | 9, 17 => true
    | 9, 25 => true
    | 9, 33 => true
    | 9, 41 => true
    | 9, 49 => true
    | 9, 57 => true
    | 10, 19 => true
    | 10, 28 => true
    | 10, 37 => true
    | 10, 46 => true
    | 10, 55 => true
    | 10, 17 => true
    | 10, 24 => true
    | 10, 11 => true
    | 10, 12 => true
    | 10, 13 => true
    | 10, 14 => true
    | 10, 15 => true
    | 10, 18 => true
    | 10, 26 => true
    | 10, 34 => true
    | 10, 42 => true
    | 10, 50 => true
    | 10, 58 => true
    | 11, 20 => true
    | 11, 29 => true
    | 11, 38 => true
    | 11, 47 => true
    | 11, 18 => true
    | 11, 25 => true
    | 11, 32 => true
    | 11, 12 => true
    | 11, 13 => true
    | 11, 14 => true
    | 11, 15 => true
    | 11, 19 => true
    | 11, 27 => true
    | 11, 35 => true
    | 11, 43 => true
    | 11, 51 => true
    | 11, 59 => true
    | 12, 21 => true
    | 12, 30 => true
    | 12, 39 => true
    | 12, 19 => true
    | 12, 26 => true
    | 12, 33 => true
    | 12, 40 => true
    | 12, 13 => true
    | 12, 14 => true
    | 12, 15 => true
    | 12, 20 => true
    | 12, 28 => true
    | 12, 36 => true
    | 12, 44 => true
    | 12, 52 => true
    | 12, 60 => true
    | 13, 22 => true
    | 13, 31 => true
    | 13, 20 => true
    | 13, 27 => true
    | 13, 34 => true
    | 13, 41 => true
    | 13, 48 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 21 => true
    | 13, 29 => true
    | 13, 37 => true
    | 13, 45 => true
    | 13, 53 => true
    | 13, 61 => true
    | 14, 23 => true
    | 14, 21 => true
    | 14, 28 => true
    | 14, 35 => true
    | 14, 42 => true
    | 14, 49 => true
    | 14, 56 => true
    | 14, 15 => true
    | 14, 22 => true
    | 14, 30 => true
    | 14, 38 => true
    | 14, 46 => true
    | 14, 54 => true
    | 14, 62 => true
    | 15, 22 => true
    | 15, 29 => true
    | 15, 36 => true
    | 15, 43 => true
    | 15, 50 => true
    | 15, 57 => true
    | 15, 23 => true
    | 15, 31 => true
    | 15, 39 => true
    | 15, 47 => true
    | 15, 55 => true
    | 15, 63 => true
    | 16, 25 => true
    | 16, 34 => true
    | 16, 43 => true
    | 16, 52 => true
    | 16, 61 => true
    | 16, 17 => true
    | 16, 18 => true
    | 16, 19 => true
    | 16, 20 => true
    | 16, 21 => true
    | 16, 22 => true
    | 16, 23 => true
    | 16, 24 => true
    | 16, 32 => true
    | 16, 40 => true
    | 16, 48 => true
    | 16, 56 => true
    | 17, 26 => true
    | 17, 35 => true
    | 17, 44 => true
    | 17, 53 => true
    | 17, 62 => true
    | 17, 24 => true
    | 17, 18 => true
    | 17, 19 => true
    | 17, 20 => true
    | 17, 21 => true
    | 17, 22 => true
    | 17, 23 => true
    | 17, 25 => true
    | 17, 33 => true
    | 17, 41 => true
    | 17, 49 => true
    | 17, 57 => true
    | 18, 27 => true
    | 18, 36 => true
    | 18, 45 => true
    | 18, 54 => true
    | 18, 63 => true
    | 18, 25 => true
    | 18, 32 => true
    | 18, 19 => true
    | 18, 20 => true
    | 18, 21 => true
    | 18, 22 => true
    | 18, 23 => true
    | 18, 26 => true
    | 18, 34 => true
    | 18, 42 => true
    | 18, 50 => true
    | 18, 58 => true
    | 19, 28 => true
    | 19, 37 => true
    | 19, 46 => true
    | 19, 55 => true
    | 19, 26 => true
    | 19, 33 => true
    | 19, 40 => true
    | 19, 20 => true
    | 19, 21 => true
    | 19, 22 => true
    | 19, 23 => true
    | 19, 27 => true
    | 19, 35 => true
    | 19, 43 => true
    | 19, 51 => true
    | 19, 59 => true
    | 20, 29 => true
    | 20, 38 => true
    | 20, 47 => true
    | 20, 27 => true
    | 20, 34 => true
    | 20, 41 => true
    | 20, 48 => true
    | 20, 21 => true
    | 20, 22 => true
    | 20, 23 => true
    | 20, 28 => true
    | 20, 36 => true
    | 20, 44 => true
    | 20, 52 => true
    | 20, 60 => true
    | 21, 30 => true
    | 21, 39 => true
    | 21, 28 => true
    | 21, 35 => true
    | 21, 42 => true
    | 21, 49 => true
    | 21, 56 => true
    | 21, 22 => true
    | 21, 23 => true
    | 21, 29 => true
    | 21, 37 => true
    | 21, 45 => true
    | 21, 53 => true
    | 21, 61 => true
    | 22, 31 => true
    | 22, 29 => true
    | 22, 36 => true
    | 22, 43 => true
    | 22, 50 => true
    | 22, 57 => true
    | 22, 23 => true
    | 22, 30 => true
    | 22, 38 => true
    | 22, 46 => true
    | 22, 54 => true
    | 22, 62 => true
    | 23, 30 => true
    | 23, 37 => true
    | 23, 44 => true
    | 23, 51 => true
    | 23, 58 => true
    | 23, 31 => true
    | 23, 39 => true
    | 23, 47 => true
    | 23, 55 => true
    | 23, 63 => true
    | 24, 33 => true
    | 24, 42 => true
    | 24, 51 => true
    | 24, 60 => true
    | 24, 25 => true
    | 24, 26 => true
    | 24, 27 => true
    | 24, 28 => true
    | 24, 29 => true
    | 24, 30 => true
    | 24, 31 => true
    | 24, 32 => true
    | 24, 40 => true
    | 24, 48 => true
    | 24, 56 => true
    | 25, 34 => true
    | 25, 43 => true
    | 25, 52 => true
    | 25, 61 => true
    | 25, 32 => true
    | 25, 26 => true
    | 25, 27 => true
    | 25, 28 => true
    | 25, 29 => true
    | 25, 30 => true
    | 25, 31 => true
    | 25, 33 => true
    | 25, 41 => true
    | 25, 49 => true
    | 25, 57 => true
    | 26, 35 => true
    | 26, 44 => true
    | 26, 53 => true
    | 26, 62 => true
    | 26, 33 => true
    | 26, 40 => true
    | 26, 27 => true
    | 26, 28 => true
    | 26, 29 => true
    | 26, 30 => true
    | 26, 31 => true
    | 26, 34 => true
    | 26, 42 => true
    | 26, 50 => true
    | 26, 58 => true
    | 27, 36 => true
    | 27, 45 => true
    | 27, 54 => true
    | 27, 63 => true
    | 27, 34 => true
    | 27, 41 => true
    | 27, 48 => true
    | 27, 28 => true
    | 27, 29 => true
    | 27, 30 => true
    | 27, 31 => true
    | 27, 35 => true
    | 27, 43 => true
    | 27, 51 => true
    | 27, 59 => true
    | 28, 37 => true
    | 28, 46 => true
    | 28, 55 => true
    | 28, 35 => true
    | 28, 42 => true
    | 28, 49 => true
    | 28, 56 => true
    | 28, 29 => true
    | 28, 30 => true
    | 28, 31 => true
    | 28, 36 => true
    | 28, 44 => true
    | 28, 52 => true
    | 28, 60 => true
    | 29, 38 => true
    | 29, 47 => true
    | 29, 36 => true
    | 29, 43 => true
    | 29, 50 => true
    | 29, 57 => true
    | 29, 30 => true
    | 29, 31 => true
    | 29, 37 => true
    | 29, 45 => true
    | 29, 53 => true
    | 29, 61 => true
    | 30, 39 => true
    | 30, 37 => true
    | 30, 44 => true
    | 30, 51 => true
    | 30, 58 => true
    | 30, 31 => true
    | 30, 38 => true
    | 30, 46 => true
    | 30, 54 => true
    | 30, 62 => true
    | 31, 38 => true
    | 31, 45 => true
    | 31, 52 => true
    | 31, 59 => true
    | 31, 39 => true
    | 31, 47 => true
    | 31, 55 => true
    | 31, 63 => true
    | 32, 41 => true
    | 32, 50 => true
    | 32, 59 => true
    | 32, 33 => true
    | 32, 34 => true
    | 32, 35 => true
    | 32, 36 => true
    | 32, 37 => true
    | 32, 38 => true
    | 32, 39 => true
    | 32, 40 => true
    | 32, 48 => true
    | 32, 56 => true
    | 33, 42 => true
    | 33, 51 => true
    | 33, 60 => true
    | 33, 40 => true
    | 33, 34 => true
    | 33, 35 => true
    | 33, 36 => true
    | 33, 37 => true
    | 33, 38 => true
    | 33, 39 => true
    | 33, 41 => true
    | 33, 49 => true
    | 33, 57 => true
    | 34, 43 => true
    | 34, 52 => true
    | 34, 61 => true
    | 34, 41 => true
    | 34, 48 => true
    | 34, 35 => true
    | 34, 36 => true
    | 34, 37 => true
    | 34, 38 => true
    | 34, 39 => true
    | 34, 42 => true
    | 34, 50 => true
    | 34, 58 => true
    | 35, 44 => true
    | 35, 53 => true
    | 35, 62 => true
    | 35, 42 => true
    | 35, 49 => true
    | 35, 56 => true
    | 35, 36 => true
    | 35, 37 => true
    | 35, 38 => true
    | 35, 39 => true
    | 35, 43 => true
    | 35, 51 => true
    | 35, 59 => true
    | 36, 45 => true
    | 36, 54 => true
    | 36, 63 => true
    | 36, 43 => true
    | 36, 50 => true
    | 36, 57 => true
    | 36, 37 => true
    | 36, 38 => true
    | 36, 39 => true
    | 36, 44 => true
    | 36, 52 => true
    | 36, 60 => true
    | 37, 46 => true
    | 37, 55 => true
    | 37, 44 => true
    | 37, 51 => true
    | 37, 58 => true
    | 37, 38 => true
    | 37, 39 => true
    | 37, 45 => true
    | 37, 53 => true
    | 37, 61 => true
    | 38, 47 => true
    | 38, 45 => true
    | 38, 52 => true
    | 38, 59 => true
    | 38, 39 => true
    | 38, 46 => true
    | 38, 54 => true
    | 38, 62 => true
    | 39, 46 => true
    | 39, 53 => true
    | 39, 60 => true
    | 39, 47 => true
    | 39, 55 => true
    | 39, 63 => true
    | 40, 49 => true
    | 40, 58 => true
    | 40, 41 => true
    | 40, 42 => true
    | 40, 43 => true
    | 40, 44 => true
    | 40, 45 => true
    | 40, 46 => true
    | 40, 47 => true
    | 40, 48 => true
    | 40, 56 => true
    | 41, 50 => true
    | 41, 59 => true
    | 41, 48 => true
    | 41, 42 => true
    | 41, 43 => true
    | 41, 44 => true
    | 41, 45 => true
    | 41, 46 => true
    | 41, 47 => true
    | 41, 49 => true
    | 41, 57 => true
    | 42, 51 => true
    | 42, 60 => true
    | 42, 49 => true
    | 42, 56 => true
    | 42, 43 => true
    | 42, 44 => true
    | 42, 45 => true
    | 42, 46 => true
    | 42, 47 => true
    | 42, 50 => true
    | 42, 58 => true
    | 43, 52 => true
    | 43, 61 => true
    | 43, 50 => true
    | 43, 57 => true
    | 43, 44 => true
    | 43, 45 => true
    | 43, 46 => true
    | 43, 47 => true
    | 43, 51 => true
    | 43, 59 => true
    | 44, 53 => true
    | 44, 62 => true
    | 44, 51 => true
    | 44, 58 => true
    | 44, 45 => true
    | 44, 46 => true
    | 44, 47 => true
    | 44, 52 => true
    | 44, 60 => true
    | 45, 54 => true
    | 45, 63 => true
    | 45, 52 => true
    | 45, 59 => true
    | 45, 46 => true
    | 45, 47 => true
    | 45, 53 => true
    | 45, 61 => true
    | 46, 55 => true
    | 46, 53 => true
    | 46, 60 => true
    | 46, 47 => true
    | 46, 54 => true
    | 46, 62 => true
    | 47, 54 => true
    | 47, 61 => true
    | 47, 55 => true
    | 47, 63 => true
    | 48, 57 => true
    | 48, 49 => true
    | 48, 50 => true
    | 48, 51 => true
    | 48, 52 => true
    | 48, 53 => true
    | 48, 54 => true
    | 48, 55 => true
    | 48, 56 => true
    | 49, 58 => true
    | 49, 56 => true
    | 49, 50 => true
    | 49, 51 => true
    | 49, 52 => true
    | 49, 53 => true
    | 49, 54 => true
    | 49, 55 => true
    | 49, 57 => true
    | 50, 59 => true
    | 50, 57 => true
    | 50, 51 => true
    | 50, 52 => true
    | 50, 53 => true
    | 50, 54 => true
    | 50, 55 => true
    | 50, 58 => true
    | 51, 60 => true
    | 51, 58 => true
    | 51, 52 => true
    | 51, 53 => true
    | 51, 54 => true
    | 51, 55 => true
    | 51, 59 => true
    | 52, 61 => true
    | 52, 59 => true
    | 52, 53 => true
    | 52, 54 => true
    | 52, 55 => true
    | 52, 60 => true
    | 53, 62 => true
    | 53, 60 => true
    | 53, 54 => true
    | 53, 55 => true
    | 53, 61 => true
    | 54, 63 => true
    | 54, 61 => true
    | 54, 55 => true
    | 54, 62 => true
    | 55, 62 => true
    | 55, 63 => true
    | 56, 57 => true
    | 56, 58 => true
    | 56, 59 => true
    | 56, 60 => true
    | 56, 61 => true
    | 56, 62 => true
    | 56, 63 => true
    | 57, 58 => true
    | 57, 59 => true
    | 57, 60 => true
    | 57, 61 => true
    | 57, 62 => true
    | 57, 63 => true
    | 58, 59 => true
    | 58, 60 => true
    | 58, 61 => true
    | 58, 62 => true
    | 58, 63 => true
    | 59, 60 => true
    | 59, 61 => true
    | 59, 62 => true
    | 59, 63 => true
    | 60, 61 => true
    | 60, 62 => true
    | 60, 63 => true
    | 61, 62 => true
    | 61, 63 => true
    | 62, 63 => true
    | _, _ => false
    end.

  Let inst_rel := [ rel u v : inst_vert | give_sg inst_adj u v ].
  Let inst_sym : symmetric inst_rel. Proof. exact: give_sg_sym. Qed.
  Let inst_irrefl : irreflexive inst_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition inst := SGraph inst_sym inst_irrefl.
End Instance.

Notation "''v' m" := (@Ordinal n m isT) (at level 0, m at level 8, format "''v' m").

(**********************************************************************************)
Section Certificate.
  Let inst_set := [set 'v0; 'v1; 'v2; 'v17; 'v24; 'v25; 'v26; 'v32; 'v48; 'v49; 'v50].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v1; 'v2; 'v17; 'v24; 'v25; 'v26; 'v32; 'v48; 'v49; 'v50].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 11.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 11.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.