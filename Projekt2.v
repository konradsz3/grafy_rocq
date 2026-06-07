Require Import List.
Require Import Lia.

Record Graf := {
  wierzcholki : list nat;
  krawedzie : nat -> nat -> bool;
  nieskierowany : forall u v : nat, krawedzie u v = krawedzie v u;
  bezPetli : forall v : nat, krawedzie v v = false;
  dobrzeZdef : forall u v : nat, krawedzie u v = true -> In u wierzcholki /\ In v wierzcholki
}.

Definition wierzcholkiK33 := 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil.

Definition krawedzieK33 (v : nat) (u : nat) : bool :=
  match v, u with
  | 1, 4 => true
  | 1, 5 => true
  | 1, 6 => true
  | 2, 4 => true
  | 2, 5 => true
  | 2, 6 => true
  | 3, 4 => true
  | 3, 5 => true
  | 3, 6 => true
  | 4, 1 => true
  | 4, 2 => true
  | 4, 3 => true
  | 5, 1 => true
  | 5, 2 => true
  | 5, 3 => true
  | 6, 1 => true
  | 6, 2 => true
  | 6, 3 => true
  | _, _ => false
  end.
