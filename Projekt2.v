Require Import List.
Require Import Lia.

Record Graf := {
  wierzcholki : list nat;
  krawedzie : nat -> nat -> bool;
  nieskierowany : forall u v : nat, krawedzie u v = krawedzie v u;
  bezPetli : forall v : nat, krawedzie v v = false;
  dobrzeZdef : forall u v : nat, krawedzie u v = true -> In u wierzcholki /\ In v wierzcholki
}.
