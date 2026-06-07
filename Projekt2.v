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

Lemma nieskierowanyK33 : forall u v : nat, krawedzieK33 u v = krawedzieK33 v u.
Proof.
  intros.
  destruct u.
  do 7 (destruct v; trivial).
  destruct u.
  do 7 (destruct v; trivial).
  destruct u.
  do 7 (destruct v; trivial).
  destruct u.
  do 7 (destruct v; trivial).
  destruct u.
  do 7 (destruct v; trivial).
  destruct u.
  do 7 (destruct v; trivial).
  destruct u.
  do 7 (destruct v; trivial).
  do 7 (destruct v; trivial).
Qed.

Lemma bezPetliK33 : forall v : nat, krawedzieK33 v v = false.
Proof. 
  intros.
  repeat (destruct v; trivial).
Qed.
    
Lemma dobrzeZdefK33 : forall u v : nat, krawedzieK33 u v = true -> In u wierzcholkiK33 /\ In v wierzcholkiK33.
Proof.
  intros.
  split.
  do 8 (destruct u; unfold wierzcholkiK33; simpl; intuition).
  do 7 (destruct v; unfold wierzcholkiK33; simpl; rewrite nieskierowanyK33 in H; intuition).
Qed.

Definition K33 : Graf := {|
  wierzcholki := wierzcholkiK33;
  krawedzie := krawedzieK33;
  nieskierowany := nieskierowanyK33;
  bezPetli := bezPetliK33;
  dobrzeZdef := dobrzeZdefK33
|}.

Definition wierzcholkiK16 := 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil.

Definition krawedzieK16 (v : nat) (u : nat) : bool :=
  match v, u with
  | 1, 2 => true
  | 1, 3 => true
  | 1, 4 => true
  | 1, 5 => true
  | 1, 6 => true
  | 1, 7 => true
  | 2, 1 => true
  | 3, 1 => true
  | 4, 1 => true
  | 5, 1 => true
  | 6, 1 => true
  | 7, 1 => true
  | _, _ => false
  end.    

Lemma nieskierowanyK16 : forall u v : nat, krawedzieK16 u v = krawedzieK16 v u.
Proof.
  intros.
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  destruct u.
  do 8 (destruct v; simpl; trivial).
  do 8 (destruct v; simpl; trivial).
Qed.
    
