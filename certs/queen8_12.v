
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 96.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 13 => true
    | 0, 26 => true
    | 0, 39 => true
    | 0, 52 => true
    | 0, 65 => true
    | 0, 78 => true
    | 0, 91 => true
    | 0, 1 => true
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 5 => true
    | 0, 6 => true
    | 0, 7 => true
    | 0, 8 => true
    | 0, 9 => true
    | 0, 10 => true
    | 0, 11 => true
    | 0, 12 => true
    | 0, 24 => true
    | 0, 36 => true
    | 0, 48 => true
    | 0, 60 => true
    | 0, 72 => true
    | 0, 84 => true
    | 1, 14 => true
    | 1, 27 => true
    | 1, 40 => true
    | 1, 53 => true
    | 1, 66 => true
    | 1, 79 => true
    | 1, 92 => true
    | 1, 12 => true
    | 1, 2 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 5 => true
    | 1, 6 => true
    | 1, 7 => true
    | 1, 8 => true
    | 1, 9 => true
    | 1, 10 => true
    | 1, 11 => true
    | 1, 13 => true
    | 1, 25 => true
    | 1, 37 => true
    | 1, 49 => true
    | 1, 61 => true
    | 1, 73 => true
    | 1, 85 => true
    | 2, 15 => true
    | 2, 28 => true
    | 2, 41 => true
    | 2, 54 => true
    | 2, 67 => true
    | 2, 80 => true
    | 2, 93 => true
    | 2, 13 => true
    | 2, 24 => true
    | 2, 3 => true
    | 2, 4 => true
    | 2, 5 => true
    | 2, 6 => true
    | 2, 7 => true
    | 2, 8 => true
    | 2, 9 => true
    | 2, 10 => true
    | 2, 11 => true
    | 2, 14 => true
    | 2, 26 => true
    | 2, 38 => true
    | 2, 50 => true
    | 2, 62 => true
    | 2, 74 => true
    | 2, 86 => true
    | 3, 16 => true
    | 3, 29 => true
    | 3, 42 => true
    | 3, 55 => true
    | 3, 68 => true
    | 3, 81 => true
    | 3, 94 => true
    | 3, 14 => true
    | 3, 25 => true
    | 3, 36 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 6 => true
    | 3, 7 => true
    | 3, 8 => true
    | 3, 9 => true
    | 3, 10 => true
    | 3, 11 => true
    | 3, 15 => true
    | 3, 27 => true
    | 3, 39 => true
    | 3, 51 => true
    | 3, 63 => true
    | 3, 75 => true
    | 3, 87 => true
    | 4, 17 => true
    | 4, 30 => true
    | 4, 43 => true
    | 4, 56 => true
    | 4, 69 => true
    | 4, 82 => true
    | 4, 95 => true
    | 4, 15 => true
    | 4, 26 => true
    | 4, 37 => true
    | 4, 48 => true
    | 4, 5 => true
    | 4, 6 => true
    | 4, 7 => true
    | 4, 8 => true
    | 4, 9 => true
    | 4, 10 => true
    | 4, 11 => true
    | 4, 16 => true
    | 4, 28 => true
    | 4, 40 => true
    | 4, 52 => true
    | 4, 64 => true
    | 4, 76 => true
    | 4, 88 => true
    | 5, 18 => true
    | 5, 31 => true
    | 5, 44 => true
    | 5, 57 => true
    | 5, 70 => true
    | 5, 83 => true
    | 5, 16 => true
    | 5, 27 => true
    | 5, 38 => true
    | 5, 49 => true
    | 5, 60 => true
    | 5, 6 => true
    | 5, 7 => true
    | 5, 8 => true
    | 5, 9 => true
    | 5, 10 => true
    | 5, 11 => true
    | 5, 17 => true
    | 5, 29 => true
    | 5, 41 => true
    | 5, 53 => true
    | 5, 65 => true
    | 5, 77 => true
    | 5, 89 => true
    | 6, 19 => true
    | 6, 32 => true
    | 6, 45 => true
    | 6, 58 => true
    | 6, 71 => true
    | 6, 17 => true
    | 6, 28 => true
    | 6, 39 => true
    | 6, 50 => true
    | 6, 61 => true
    | 6, 72 => true
    | 6, 7 => true
    | 6, 8 => true
    | 6, 9 => true
    | 6, 10 => true
    | 6, 11 => true
    | 6, 18 => true
    | 6, 30 => true
    | 6, 42 => true
    | 6, 54 => true
    | 6, 66 => true
    | 6, 78 => true
    | 6, 90 => true
    | 7, 20 => true
    | 7, 33 => true
    | 7, 46 => true
    | 7, 59 => true
    | 7, 18 => true
    | 7, 29 => true
    | 7, 40 => true
    | 7, 51 => true
    | 7, 62 => true
    | 7, 73 => true
    | 7, 84 => true
    | 7, 8 => true
    | 7, 9 => true
    | 7, 10 => true
    | 7, 11 => true
    | 7, 19 => true
    | 7, 31 => true
    | 7, 43 => true
    | 7, 55 => true
    | 7, 67 => true
    | 7, 79 => true
    | 7, 91 => true
    | 8, 21 => true
    | 8, 34 => true
    | 8, 47 => true
    | 8, 19 => true
    | 8, 30 => true
    | 8, 41 => true
    | 8, 52 => true
    | 8, 63 => true
    | 8, 74 => true
    | 8, 85 => true
    | 8, 9 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 20 => true
    | 8, 32 => true
    | 8, 44 => true
    | 8, 56 => true
    | 8, 68 => true
    | 8, 80 => true
    | 8, 92 => true
    | 9, 22 => true
    | 9, 35 => true
    | 9, 20 => true
    | 9, 31 => true
    | 9, 42 => true
    | 9, 53 => true
    | 9, 64 => true
    | 9, 75 => true
    | 9, 86 => true
    | 9, 10 => true
    | 9, 11 => true
    | 9, 21 => true
    | 9, 33 => true
    | 9, 45 => true
    | 9, 57 => true
    | 9, 69 => true
    | 9, 81 => true
    | 9, 93 => true
    | 10, 23 => true
    | 10, 21 => true
    | 10, 32 => true
    | 10, 43 => true
    | 10, 54 => true
    | 10, 65 => true
    | 10, 76 => true
    | 10, 87 => true
    | 10, 11 => true
    | 10, 22 => true
    | 10, 34 => true
    | 10, 46 => true
    | 10, 58 => true
    | 10, 70 => true
    | 10, 82 => true
    | 10, 94 => true
    | 11, 22 => true
    | 11, 33 => true
    | 11, 44 => true
    | 11, 55 => true
    | 11, 66 => true
    | 11, 77 => true
    | 11, 88 => true
    | 11, 23 => true
    | 11, 35 => true
    | 11, 47 => true
    | 11, 59 => true
    | 11, 71 => true
    | 11, 83 => true
    | 11, 95 => true
    | 12, 25 => true
    | 12, 38 => true
    | 12, 51 => true
    | 12, 64 => true
    | 12, 77 => true
    | 12, 90 => true
    | 12, 13 => true
    | 12, 14 => true
    | 12, 15 => true
    | 12, 16 => true
    | 12, 17 => true
    | 12, 18 => true
    | 12, 19 => true
    | 12, 20 => true
    | 12, 21 => true
    | 12, 22 => true
    | 12, 23 => true
    | 12, 24 => true
    | 12, 36 => true
    | 12, 48 => true
    | 12, 60 => true
    | 12, 72 => true
    | 12, 84 => true
    | 13, 26 => true
    | 13, 39 => true
    | 13, 52 => true
    | 13, 65 => true
    | 13, 78 => true
    | 13, 91 => true
    | 13, 24 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 16 => true
    | 13, 17 => true
    | 13, 18 => true
    | 13, 19 => true
    | 13, 20 => true
    | 13, 21 => true
    | 13, 22 => true
    | 13, 23 => true
    | 13, 25 => true
    | 13, 37 => true
    | 13, 49 => true
    | 13, 61 => true
    | 13, 73 => true
    | 13, 85 => true
    | 14, 27 => true
    | 14, 40 => true
    | 14, 53 => true
    | 14, 66 => true
    | 14, 79 => true
    | 14, 92 => true
    | 14, 25 => true
    | 14, 36 => true
    | 14, 15 => true
    | 14, 16 => true
    | 14, 17 => true
    | 14, 18 => true
    | 14, 19 => true
    | 14, 20 => true
    | 14, 21 => true
    | 14, 22 => true
    | 14, 23 => true
    | 14, 26 => true
    | 14, 38 => true
    | 14, 50 => true
    | 14, 62 => true
    | 14, 74 => true
    | 14, 86 => true
    | 15, 28 => true
    | 15, 41 => true
    | 15, 54 => true
    | 15, 67 => true
    | 15, 80 => true
    | 15, 93 => true
    | 15, 26 => true
    | 15, 37 => true
    | 15, 48 => true
    | 15, 16 => true
    | 15, 17 => true
    | 15, 18 => true
    | 15, 19 => true
    | 15, 20 => true
    | 15, 21 => true
    | 15, 22 => true
    | 15, 23 => true
    | 15, 27 => true
    | 15, 39 => true
    | 15, 51 => true
    | 15, 63 => true
    | 15, 75 => true
    | 15, 87 => true
    | 16, 29 => true
    | 16, 42 => true
    | 16, 55 => true
    | 16, 68 => true
    | 16, 81 => true
    | 16, 94 => true
    | 16, 27 => true
    | 16, 38 => true
    | 16, 49 => true
    | 16, 60 => true
    | 16, 17 => true
    | 16, 18 => true
    | 16, 19 => true
    | 16, 20 => true
    | 16, 21 => true
    | 16, 22 => true
    | 16, 23 => true
    | 16, 28 => true
    | 16, 40 => true
    | 16, 52 => true
    | 16, 64 => true
    | 16, 76 => true
    | 16, 88 => true
    | 17, 30 => true
    | 17, 43 => true
    | 17, 56 => true
    | 17, 69 => true
    | 17, 82 => true
    | 17, 95 => true
    | 17, 28 => true
    | 17, 39 => true
    | 17, 50 => true
    | 17, 61 => true
    | 17, 72 => true
    | 17, 18 => true
    | 17, 19 => true
    | 17, 20 => true
    | 17, 21 => true
    | 17, 22 => true
    | 17, 23 => true
    | 17, 29 => true
    | 17, 41 => true
    | 17, 53 => true
    | 17, 65 => true
    | 17, 77 => true
    | 17, 89 => true
    | 18, 31 => true
    | 18, 44 => true
    | 18, 57 => true
    | 18, 70 => true
    | 18, 83 => true
    | 18, 29 => true
    | 18, 40 => true
    | 18, 51 => true
    | 18, 62 => true
    | 18, 73 => true
    | 18, 84 => true
    | 18, 19 => true
    | 18, 20 => true
    | 18, 21 => true
    | 18, 22 => true
    | 18, 23 => true
    | 18, 30 => true
    | 18, 42 => true
    | 18, 54 => true
    | 18, 66 => true
    | 18, 78 => true
    | 18, 90 => true
    | 19, 32 => true
    | 19, 45 => true
    | 19, 58 => true
    | 19, 71 => true
    | 19, 30 => true
    | 19, 41 => true
    | 19, 52 => true
    | 19, 63 => true
    | 19, 74 => true
    | 19, 85 => true
    | 19, 20 => true
    | 19, 21 => true
    | 19, 22 => true
    | 19, 23 => true
    | 19, 31 => true
    | 19, 43 => true
    | 19, 55 => true
    | 19, 67 => true
    | 19, 79 => true
    | 19, 91 => true
    | 20, 33 => true
    | 20, 46 => true
    | 20, 59 => true
    | 20, 31 => true
    | 20, 42 => true
    | 20, 53 => true
    | 20, 64 => true
    | 20, 75 => true
    | 20, 86 => true
    | 20, 21 => true
    | 20, 22 => true
    | 20, 23 => true
    | 20, 32 => true
    | 20, 44 => true
    | 20, 56 => true
    | 20, 68 => true
    | 20, 80 => true
    | 20, 92 => true
    | 21, 34 => true
    | 21, 47 => true
    | 21, 32 => true
    | 21, 43 => true
    | 21, 54 => true
    | 21, 65 => true
    | 21, 76 => true
    | 21, 87 => true
    | 21, 22 => true
    | 21, 23 => true
    | 21, 33 => true
    | 21, 45 => true
    | 21, 57 => true
    | 21, 69 => true
    | 21, 81 => true
    | 21, 93 => true
    | 22, 35 => true
    | 22, 33 => true
    | 22, 44 => true
    | 22, 55 => true
    | 22, 66 => true
    | 22, 77 => true
    | 22, 88 => true
    | 22, 23 => true
    | 22, 34 => true
    | 22, 46 => true
    | 22, 58 => true
    | 22, 70 => true
    | 22, 82 => true
    | 22, 94 => true
    | 23, 34 => true
    | 23, 45 => true
    | 23, 56 => true
    | 23, 67 => true
    | 23, 78 => true
    | 23, 89 => true
    | 23, 35 => true
    | 23, 47 => true
    | 23, 59 => true
    | 23, 71 => true
    | 23, 83 => true
    | 23, 95 => true
    | 24, 37 => true
    | 24, 50 => true
    | 24, 63 => true
    | 24, 76 => true
    | 24, 89 => true
    | 24, 25 => true
    | 24, 26 => true
    | 24, 27 => true
    | 24, 28 => true
    | 24, 29 => true
    | 24, 30 => true
    | 24, 31 => true
    | 24, 32 => true
    | 24, 33 => true
    | 24, 34 => true
    | 24, 35 => true
    | 24, 36 => true
    | 24, 48 => true
    | 24, 60 => true
    | 24, 72 => true
    | 24, 84 => true
    | 25, 38 => true
    | 25, 51 => true
    | 25, 64 => true
    | 25, 77 => true
    | 25, 90 => true
    | 25, 36 => true
    | 25, 26 => true
    | 25, 27 => true
    | 25, 28 => true
    | 25, 29 => true
    | 25, 30 => true
    | 25, 31 => true
    | 25, 32 => true
    | 25, 33 => true
    | 25, 34 => true
    | 25, 35 => true
    | 25, 37 => true
    | 25, 49 => true
    | 25, 61 => true
    | 25, 73 => true
    | 25, 85 => true
    | 26, 39 => true
    | 26, 52 => true
    | 26, 65 => true
    | 26, 78 => true
    | 26, 91 => true
    | 26, 37 => true
    | 26, 48 => true
    | 26, 27 => true
    | 26, 28 => true
    | 26, 29 => true
    | 26, 30 => true
    | 26, 31 => true
    | 26, 32 => true
    | 26, 33 => true
    | 26, 34 => true
    | 26, 35 => true
    | 26, 38 => true
    | 26, 50 => true
    | 26, 62 => true
    | 26, 74 => true
    | 26, 86 => true
    | 27, 40 => true
    | 27, 53 => true
    | 27, 66 => true
    | 27, 79 => true
    | 27, 92 => true
    | 27, 38 => true
    | 27, 49 => true
    | 27, 60 => true
    | 27, 28 => true
    | 27, 29 => true
    | 27, 30 => true
    | 27, 31 => true
    | 27, 32 => true
    | 27, 33 => true
    | 27, 34 => true
    | 27, 35 => true
    | 27, 39 => true
    | 27, 51 => true
    | 27, 63 => true
    | 27, 75 => true
    | 27, 87 => true
    | 28, 41 => true
    | 28, 54 => true
    | 28, 67 => true
    | 28, 80 => true
    | 28, 93 => true
    | 28, 39 => true
    | 28, 50 => true
    | 28, 61 => true
    | 28, 72 => true
    | 28, 29 => true
    | 28, 30 => true
    | 28, 31 => true
    | 28, 32 => true
    | 28, 33 => true
    | 28, 34 => true
    | 28, 35 => true
    | 28, 40 => true
    | 28, 52 => true
    | 28, 64 => true
    | 28, 76 => true
    | 28, 88 => true
    | 29, 42 => true
    | 29, 55 => true
    | 29, 68 => true
    | 29, 81 => true
    | 29, 94 => true
    | 29, 40 => true
    | 29, 51 => true
    | 29, 62 => true
    | 29, 73 => true
    | 29, 84 => true
    | 29, 30 => true
    | 29, 31 => true
    | 29, 32 => true
    | 29, 33 => true
    | 29, 34 => true
    | 29, 35 => true
    | 29, 41 => true
    | 29, 53 => true
    | 29, 65 => true
    | 29, 77 => true
    | 29, 89 => true
    | 30, 43 => true
    | 30, 56 => true
    | 30, 69 => true
    | 30, 82 => true
    | 30, 95 => true
    | 30, 41 => true
    | 30, 52 => true
    | 30, 63 => true
    | 30, 74 => true
    | 30, 85 => true
    | 30, 31 => true
    | 30, 32 => true
    | 30, 33 => true
    | 30, 34 => true
    | 30, 35 => true
    | 30, 42 => true
    | 30, 54 => true
    | 30, 66 => true
    | 30, 78 => true
    | 30, 90 => true
    | 31, 44 => true
    | 31, 57 => true
    | 31, 70 => true
    | 31, 83 => true
    | 31, 42 => true
    | 31, 53 => true
    | 31, 64 => true
    | 31, 75 => true
    | 31, 86 => true
    | 31, 32 => true
    | 31, 33 => true
    | 31, 34 => true
    | 31, 35 => true
    | 31, 43 => true
    | 31, 55 => true
    | 31, 67 => true
    | 31, 79 => true
    | 31, 91 => true
    | 32, 45 => true
    | 32, 58 => true
    | 32, 71 => true
    | 32, 43 => true
    | 32, 54 => true
    | 32, 65 => true
    | 32, 76 => true
    | 32, 87 => true
    | 32, 33 => true
    | 32, 34 => true
    | 32, 35 => true
    | 32, 44 => true
    | 32, 56 => true
    | 32, 68 => true
    | 32, 80 => true
    | 32, 92 => true
    | 33, 46 => true
    | 33, 59 => true
    | 33, 44 => true
    | 33, 55 => true
    | 33, 66 => true
    | 33, 77 => true
    | 33, 88 => true
    | 33, 34 => true
    | 33, 35 => true
    | 33, 45 => true
    | 33, 57 => true
    | 33, 69 => true
    | 33, 81 => true
    | 33, 93 => true
    | 34, 47 => true
    | 34, 45 => true
    | 34, 56 => true
    | 34, 67 => true
    | 34, 78 => true
    | 34, 89 => true
    | 34, 35 => true
    | 34, 46 => true
    | 34, 58 => true
    | 34, 70 => true
    | 34, 82 => true
    | 34, 94 => true
    | 35, 46 => true
    | 35, 57 => true
    | 35, 68 => true
    | 35, 79 => true
    | 35, 90 => true
    | 35, 47 => true
    | 35, 59 => true
    | 35, 71 => true
    | 35, 83 => true
    | 35, 95 => true
    | 36, 49 => true
    | 36, 62 => true
    | 36, 75 => true
    | 36, 88 => true
    | 36, 37 => true
    | 36, 38 => true
    | 36, 39 => true
    | 36, 40 => true
    | 36, 41 => true
    | 36, 42 => true
    | 36, 43 => true
    | 36, 44 => true
    | 36, 45 => true
    | 36, 46 => true
    | 36, 47 => true
    | 36, 48 => true
    | 36, 60 => true
    | 36, 72 => true
    | 36, 84 => true
    | 37, 50 => true
    | 37, 63 => true
    | 37, 76 => true
    | 37, 89 => true
    | 37, 48 => true
    | 37, 38 => true
    | 37, 39 => true
    | 37, 40 => true
    | 37, 41 => true
    | 37, 42 => true
    | 37, 43 => true
    | 37, 44 => true
    | 37, 45 => true
    | 37, 46 => true
    | 37, 47 => true
    | 37, 49 => true
    | 37, 61 => true
    | 37, 73 => true
    | 37, 85 => true
    | 38, 51 => true
    | 38, 64 => true
    | 38, 77 => true
    | 38, 90 => true
    | 38, 49 => true
    | 38, 60 => true
    | 38, 39 => true
    | 38, 40 => true
    | 38, 41 => true
    | 38, 42 => true
    | 38, 43 => true
    | 38, 44 => true
    | 38, 45 => true
    | 38, 46 => true
    | 38, 47 => true
    | 38, 50 => true
    | 38, 62 => true
    | 38, 74 => true
    | 38, 86 => true
    | 39, 52 => true
    | 39, 65 => true
    | 39, 78 => true
    | 39, 91 => true
    | 39, 50 => true
    | 39, 61 => true
    | 39, 72 => true
    | 39, 40 => true
    | 39, 41 => true
    | 39, 42 => true
    | 39, 43 => true
    | 39, 44 => true
    | 39, 45 => true
    | 39, 46 => true
    | 39, 47 => true
    | 39, 51 => true
    | 39, 63 => true
    | 39, 75 => true
    | 39, 87 => true
    | 40, 53 => true
    | 40, 66 => true
    | 40, 79 => true
    | 40, 92 => true
    | 40, 51 => true
    | 40, 62 => true
    | 40, 73 => true
    | 40, 84 => true
    | 40, 41 => true
    | 40, 42 => true
    | 40, 43 => true
    | 40, 44 => true
    | 40, 45 => true
    | 40, 46 => true
    | 40, 47 => true
    | 40, 52 => true
    | 40, 64 => true
    | 40, 76 => true
    | 40, 88 => true
    | 41, 54 => true
    | 41, 67 => true
    | 41, 80 => true
    | 41, 93 => true
    | 41, 52 => true
    | 41, 63 => true
    | 41, 74 => true
    | 41, 85 => true
    | 41, 42 => true
    | 41, 43 => true
    | 41, 44 => true
    | 41, 45 => true
    | 41, 46 => true
    | 41, 47 => true
    | 41, 53 => true
    | 41, 65 => true
    | 41, 77 => true
    | 41, 89 => true
    | 42, 55 => true
    | 42, 68 => true
    | 42, 81 => true
    | 42, 94 => true
    | 42, 53 => true
    | 42, 64 => true
    | 42, 75 => true
    | 42, 86 => true
    | 42, 43 => true
    | 42, 44 => true
    | 42, 45 => true
    | 42, 46 => true
    | 42, 47 => true
    | 42, 54 => true
    | 42, 66 => true
    | 42, 78 => true
    | 42, 90 => true
    | 43, 56 => true
    | 43, 69 => true
    | 43, 82 => true
    | 43, 95 => true
    | 43, 54 => true
    | 43, 65 => true
    | 43, 76 => true
    | 43, 87 => true
    | 43, 44 => true
    | 43, 45 => true
    | 43, 46 => true
    | 43, 47 => true
    | 43, 55 => true
    | 43, 67 => true
    | 43, 79 => true
    | 43, 91 => true
    | 44, 57 => true
    | 44, 70 => true
    | 44, 83 => true
    | 44, 55 => true
    | 44, 66 => true
    | 44, 77 => true
    | 44, 88 => true
    | 44, 45 => true
    | 44, 46 => true
    | 44, 47 => true
    | 44, 56 => true
    | 44, 68 => true
    | 44, 80 => true
    | 44, 92 => true
    | 45, 58 => true
    | 45, 71 => true
    | 45, 56 => true
    | 45, 67 => true
    | 45, 78 => true
    | 45, 89 => true
    | 45, 46 => true
    | 45, 47 => true
    | 45, 57 => true
    | 45, 69 => true
    | 45, 81 => true
    | 45, 93 => true
    | 46, 59 => true
    | 46, 57 => true
    | 46, 68 => true
    | 46, 79 => true
    | 46, 90 => true
    | 46, 47 => true
    | 46, 58 => true
    | 46, 70 => true
    | 46, 82 => true
    | 46, 94 => true
    | 47, 58 => true
    | 47, 69 => true
    | 47, 80 => true
    | 47, 91 => true
    | 47, 59 => true
    | 47, 71 => true
    | 47, 83 => true
    | 47, 95 => true
    | 48, 61 => true
    | 48, 74 => true
    | 48, 87 => true
    | 48, 49 => true
    | 48, 50 => true
    | 48, 51 => true
    | 48, 52 => true
    | 48, 53 => true
    | 48, 54 => true
    | 48, 55 => true
    | 48, 56 => true
    | 48, 57 => true
    | 48, 58 => true
    | 48, 59 => true
    | 48, 60 => true
    | 48, 72 => true
    | 48, 84 => true
    | 49, 62 => true
    | 49, 75 => true
    | 49, 88 => true
    | 49, 60 => true
    | 49, 50 => true
    | 49, 51 => true
    | 49, 52 => true
    | 49, 53 => true
    | 49, 54 => true
    | 49, 55 => true
    | 49, 56 => true
    | 49, 57 => true
    | 49, 58 => true
    | 49, 59 => true
    | 49, 61 => true
    | 49, 73 => true
    | 49, 85 => true
    | 50, 63 => true
    | 50, 76 => true
    | 50, 89 => true
    | 50, 61 => true
    | 50, 72 => true
    | 50, 51 => true
    | 50, 52 => true
    | 50, 53 => true
    | 50, 54 => true
    | 50, 55 => true
    | 50, 56 => true
    | 50, 57 => true
    | 50, 58 => true
    | 50, 59 => true
    | 50, 62 => true
    | 50, 74 => true
    | 50, 86 => true
    | 51, 64 => true
    | 51, 77 => true
    | 51, 90 => true
    | 51, 62 => true
    | 51, 73 => true
    | 51, 84 => true
    | 51, 52 => true
    | 51, 53 => true
    | 51, 54 => true
    | 51, 55 => true
    | 51, 56 => true
    | 51, 57 => true
    | 51, 58 => true
    | 51, 59 => true
    | 51, 63 => true
    | 51, 75 => true
    | 51, 87 => true
    | 52, 65 => true
    | 52, 78 => true
    | 52, 91 => true
    | 52, 63 => true
    | 52, 74 => true
    | 52, 85 => true
    | 52, 53 => true
    | 52, 54 => true
    | 52, 55 => true
    | 52, 56 => true
    | 52, 57 => true
    | 52, 58 => true
    | 52, 59 => true
    | 52, 64 => true
    | 52, 76 => true
    | 52, 88 => true
    | 53, 66 => true
    | 53, 79 => true
    | 53, 92 => true
    | 53, 64 => true
    | 53, 75 => true
    | 53, 86 => true
    | 53, 54 => true
    | 53, 55 => true
    | 53, 56 => true
    | 53, 57 => true
    | 53, 58 => true
    | 53, 59 => true
    | 53, 65 => true
    | 53, 77 => true
    | 53, 89 => true
    | 54, 67 => true
    | 54, 80 => true
    | 54, 93 => true
    | 54, 65 => true
    | 54, 76 => true
    | 54, 87 => true
    | 54, 55 => true
    | 54, 56 => true
    | 54, 57 => true
    | 54, 58 => true
    | 54, 59 => true
    | 54, 66 => true
    | 54, 78 => true
    | 54, 90 => true
    | 55, 68 => true
    | 55, 81 => true
    | 55, 94 => true
    | 55, 66 => true
    | 55, 77 => true
    | 55, 88 => true
    | 55, 56 => true
    | 55, 57 => true
    | 55, 58 => true
    | 55, 59 => true
    | 55, 67 => true
    | 55, 79 => true
    | 55, 91 => true
    | 56, 69 => true
    | 56, 82 => true
    | 56, 95 => true
    | 56, 67 => true
    | 56, 78 => true
    | 56, 89 => true
    | 56, 57 => true
    | 56, 58 => true
    | 56, 59 => true
    | 56, 68 => true
    | 56, 80 => true
    | 56, 92 => true
    | 57, 70 => true
    | 57, 83 => true
    | 57, 68 => true
    | 57, 79 => true
    | 57, 90 => true
    | 57, 58 => true
    | 57, 59 => true
    | 57, 69 => true
    | 57, 81 => true
    | 57, 93 => true
    | 58, 71 => true
    | 58, 69 => true
    | 58, 80 => true
    | 58, 91 => true
    | 58, 59 => true
    | 58, 70 => true
    | 58, 82 => true
    | 58, 94 => true
    | 59, 70 => true
    | 59, 81 => true
    | 59, 92 => true
    | 59, 71 => true
    | 59, 83 => true
    | 59, 95 => true
    | 60, 73 => true
    | 60, 86 => true
    | 60, 61 => true
    | 60, 62 => true
    | 60, 63 => true
    | 60, 64 => true
    | 60, 65 => true
    | 60, 66 => true
    | 60, 67 => true
    | 60, 68 => true
    | 60, 69 => true
    | 60, 70 => true
    | 60, 71 => true
    | 60, 72 => true
    | 60, 84 => true
    | 61, 74 => true
    | 61, 87 => true
    | 61, 72 => true
    | 61, 62 => true
    | 61, 63 => true
    | 61, 64 => true
    | 61, 65 => true
    | 61, 66 => true
    | 61, 67 => true
    | 61, 68 => true
    | 61, 69 => true
    | 61, 70 => true
    | 61, 71 => true
    | 61, 73 => true
    | 61, 85 => true
    | 62, 75 => true
    | 62, 88 => true
    | 62, 73 => true
    | 62, 84 => true
    | 62, 63 => true
    | 62, 64 => true
    | 62, 65 => true
    | 62, 66 => true
    | 62, 67 => true
    | 62, 68 => true
    | 62, 69 => true
    | 62, 70 => true
    | 62, 71 => true
    | 62, 74 => true
    | 62, 86 => true
    | 63, 76 => true
    | 63, 89 => true
    | 63, 74 => true
    | 63, 85 => true
    | 63, 64 => true
    | 63, 65 => true
    | 63, 66 => true
    | 63, 67 => true
    | 63, 68 => true
    | 63, 69 => true
    | 63, 70 => true
    | 63, 71 => true
    | 63, 75 => true
    | 63, 87 => true
    | 64, 77 => true
    | 64, 90 => true
    | 64, 75 => true
    | 64, 86 => true
    | 64, 65 => true
    | 64, 66 => true
    | 64, 67 => true
    | 64, 68 => true
    | 64, 69 => true
    | 64, 70 => true
    | 64, 71 => true
    | 64, 76 => true
    | 64, 88 => true
    | 65, 78 => true
    | 65, 91 => true
    | 65, 76 => true
    | 65, 87 => true
    | 65, 66 => true
    | 65, 67 => true
    | 65, 68 => true
    | 65, 69 => true
    | 65, 70 => true
    | 65, 71 => true
    | 65, 77 => true
    | 65, 89 => true
    | 66, 79 => true
    | 66, 92 => true
    | 66, 77 => true
    | 66, 88 => true
    | 66, 67 => true
    | 66, 68 => true
    | 66, 69 => true
    | 66, 70 => true
    | 66, 71 => true
    | 66, 78 => true
    | 66, 90 => true
    | 67, 80 => true
    | 67, 93 => true
    | 67, 78 => true
    | 67, 89 => true
    | 67, 68 => true
    | 67, 69 => true
    | 67, 70 => true
    | 67, 71 => true
    | 67, 79 => true
    | 67, 91 => true
    | 68, 81 => true
    | 68, 94 => true
    | 68, 79 => true
    | 68, 90 => true
    | 68, 69 => true
    | 68, 70 => true
    | 68, 71 => true
    | 68, 80 => true
    | 68, 92 => true
    | 69, 82 => true
    | 69, 95 => true
    | 69, 80 => true
    | 69, 91 => true
    | 69, 70 => true
    | 69, 71 => true
    | 69, 81 => true
    | 69, 93 => true
    | 70, 83 => true
    | 70, 81 => true
    | 70, 92 => true
    | 70, 71 => true
    | 70, 82 => true
    | 70, 94 => true
    | 71, 82 => true
    | 71, 93 => true
    | 71, 83 => true
    | 71, 95 => true
    | 72, 85 => true
    | 72, 73 => true
    | 72, 74 => true
    | 72, 75 => true
    | 72, 76 => true
    | 72, 77 => true
    | 72, 78 => true
    | 72, 79 => true
    | 72, 80 => true
    | 72, 81 => true
    | 72, 82 => true
    | 72, 83 => true
    | 72, 84 => true
    | 73, 86 => true
    | 73, 84 => true
    | 73, 74 => true
    | 73, 75 => true
    | 73, 76 => true
    | 73, 77 => true
    | 73, 78 => true
    | 73, 79 => true
    | 73, 80 => true
    | 73, 81 => true
    | 73, 82 => true
    | 73, 83 => true
    | 73, 85 => true
    | 74, 87 => true
    | 74, 85 => true
    | 74, 75 => true
    | 74, 76 => true
    | 74, 77 => true
    | 74, 78 => true
    | 74, 79 => true
    | 74, 80 => true
    | 74, 81 => true
    | 74, 82 => true
    | 74, 83 => true
    | 74, 86 => true
    | 75, 88 => true
    | 75, 86 => true
    | 75, 76 => true
    | 75, 77 => true
    | 75, 78 => true
    | 75, 79 => true
    | 75, 80 => true
    | 75, 81 => true
    | 75, 82 => true
    | 75, 83 => true
    | 75, 87 => true
    | 76, 89 => true
    | 76, 87 => true
    | 76, 77 => true
    | 76, 78 => true
    | 76, 79 => true
    | 76, 80 => true
    | 76, 81 => true
    | 76, 82 => true
    | 76, 83 => true
    | 76, 88 => true
    | 77, 90 => true
    | 77, 88 => true
    | 77, 78 => true
    | 77, 79 => true
    | 77, 80 => true
    | 77, 81 => true
    | 77, 82 => true
    | 77, 83 => true
    | 77, 89 => true
    | 78, 91 => true
    | 78, 89 => true
    | 78, 79 => true
    | 78, 80 => true
    | 78, 81 => true
    | 78, 82 => true
    | 78, 83 => true
    | 78, 90 => true
    | 79, 92 => true
    | 79, 90 => true
    | 79, 80 => true
    | 79, 81 => true
    | 79, 82 => true
    | 79, 83 => true
    | 79, 91 => true
    | 80, 93 => true
    | 80, 91 => true
    | 80, 81 => true
    | 80, 82 => true
    | 80, 83 => true
    | 80, 92 => true
    | 81, 94 => true
    | 81, 92 => true
    | 81, 82 => true
    | 81, 83 => true
    | 81, 93 => true
    | 82, 95 => true
    | 82, 93 => true
    | 82, 83 => true
    | 82, 94 => true
    | 83, 94 => true
    | 83, 95 => true
    | 84, 85 => true
    | 84, 86 => true
    | 84, 87 => true
    | 84, 88 => true
    | 84, 89 => true
    | 84, 90 => true
    | 84, 91 => true
    | 84, 92 => true
    | 84, 93 => true
    | 84, 94 => true
    | 84, 95 => true
    | 85, 86 => true
    | 85, 87 => true
    | 85, 88 => true
    | 85, 89 => true
    | 85, 90 => true
    | 85, 91 => true
    | 85, 92 => true
    | 85, 93 => true
    | 85, 94 => true
    | 85, 95 => true
    | 86, 87 => true
    | 86, 88 => true
    | 86, 89 => true
    | 86, 90 => true
    | 86, 91 => true
    | 86, 92 => true
    | 86, 93 => true
    | 86, 94 => true
    | 86, 95 => true
    | 87, 88 => true
    | 87, 89 => true
    | 87, 90 => true
    | 87, 91 => true
    | 87, 92 => true
    | 87, 93 => true
    | 87, 94 => true
    | 87, 95 => true
    | 88, 89 => true
    | 88, 90 => true
    | 88, 91 => true
    | 88, 92 => true
    | 88, 93 => true
    | 88, 94 => true
    | 88, 95 => true
    | 89, 90 => true
    | 89, 91 => true
    | 89, 92 => true
    | 89, 93 => true
    | 89, 94 => true
    | 89, 95 => true
    | 90, 91 => true
    | 90, 92 => true
    | 90, 93 => true
    | 90, 94 => true
    | 90, 95 => true
    | 91, 92 => true
    | 91, 93 => true
    | 91, 94 => true
    | 91, 95 => true
    | 92, 93 => true
    | 92, 94 => true
    | 92, 95 => true
    | 93, 94 => true
    | 93, 95 => true
    | 94, 95 => true
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
  Let inst_set := [set 'v12; 'v13; 'v17; 'v22; 'v23; 'v36; 'v37; 'v46; 'v47; 'v48; 'v49; 'v58; 'v59; 'v73; 'v82; 'v83].

  Section List_of_Set.
    Definition inst_list := [:: 'v12; 'v13; 'v17; 'v22; 'v23; 'v36; 'v37; 'v46; 'v47; 'v48; 'v49; 'v58; 'v59; 'v73; 'v82; 'v83].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 16.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 16.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
