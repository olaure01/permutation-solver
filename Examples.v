Require Import PermutationSolver.

Parameter A : Set.
Axiom eq_dec : forall x y : A, {x = y} + {x <> y}.

Goal
  forall (a b c d e : list A) x y,
    Permutation (a ++ e) (x :: c) ->
    Permutation b (y :: d) ->
    Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof.
  intros; permutation_solver eq_dec.
Qed.


Import ListNotations.

Goal
  forall (a b : list A) x y,
    Permutation a b ->
    Permutation [x] [y] ->
    Permutation (a ++ [x]) (y :: b).
Proof.
  intros; permutation_solver eq_dec.
Qed.

Goal
  forall (a b : list A) x y,
    Permutation (a ++ [x]) (y :: b) ->
    Permutation [x] [y] ->
    Permutation a b.
Proof.
  intros; permutation_solver eq_dec.
Qed.

Goal
  forall (b u t e r f l y : A) xs ys,
    Permutation xs ys ->
    Permutation ([b;u;t;t;e;r]++[f;l;y]++xs) ([f;l;u;t;t;e;r]++ys++[b;y]).
Proof.
  intros; permutation_solver eq_dec.
Qed.

(** Proving preorder, inorder and postorder of a BST are permutation of each
    other. *)
Inductive tree : Set :=
| Leaf : tree
| Node : tree -> A -> tree -> tree.

Fixpoint inorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node l v r => inorder l ++ v :: inorder r
  end.

Fixpoint preorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node l v r => v :: preorder l ++ preorder r
  end.

Fixpoint postorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node l v r => postorder l ++ postorder r ++ [v]
  end.

Theorem tree_orders :
  forall (t : tree),
    Permutation (inorder t) (preorder t) /\
    Permutation (inorder t) (postorder t).
Proof.
  induction t; simpl; intuition (permutation_solver eq_dec).
Qed.


(** Uses of [map] and [rev] *)
Goal forall (l0 l1 l2 l3 l4 l5 l6 l7 l8 : list A) n,
  Permutation (l1 ++ l8) (l4 ++ l0) ->
  Permutation l2 (l5 ++ n :: l3) ->
  Permutation (l8 ++ l6) (l4 ++ l5) ->
  Permutation l7 (rev l3 ++ rev l0) ->
  Permutation (l1 ++ l2) (n :: l6 ++ rev l7).
Proof. intros; permutation_solver eq_dec. Qed.

Goal forall B (f : B -> A) l0 l1 l2 l3 l4 l5 l6 l7 l8 (n : A),
  Permutation (l1 ++ l8) (l4 ++ map f l0) ->
  Permutation l2 (l5 ++ n :: map f l3) ->
  Permutation (l8 ++ l6) (l4 ++ l5) ->
  Permutation (map f l7) (map f l0 ++ map f l3) ->
  Permutation (l1 ++ l2) (n :: l6 ++ map f l7).
Proof. intros; permutation_solver eq_dec. Qed.

Goal forall B (f : B -> A) l0 l1 l2 l3 l4 l5 l6 l7 l8 (n : A),
  Permutation (l1 ++ l8) (l4 ++ map f l0) ->
  Permutation l2 (l5 ++ n :: map f l3) ->
  Permutation (l8 ++ l6) (l4 ++ l5) ->
  Permutation l7 (l0 ++ l3) ->
  Permutation (l1 ++ l2) (n :: l6 ++ map f l7).
Proof. intros; permutation_solver eq_dec. Qed.


(** Cancelation *)

Lemma Permutation_cancel (l1 l2 l l' : list A) :
   Permutation (l1 ++ l) (l' ++ l2) -> Permutation l l' -> Permutation l1 l2.
Proof. intros. permutation_solver eq_dec. Qed.

Lemma Permutation_cancel_sgt (l1 l2 : list A) a : Permutation (l1 ++ [a]) (a :: l2) -> Permutation l1 l2.
Proof. intros. permutation_solver eq_dec. Qed.


(** Contradiction *)

Goal forall (a : A) l, ~ Permutation (a :: l) (a :: l ++ a :: l).
Proof. intros a l HP. permutation_solver eq_dec. Qed.

Goal forall (a : A) l, ~ Permutation [a] (l ++ l).
Proof. intros a l HP. permutation_solver eq_dec. Qed.

Goal forall a (l l1 l2 : list A), Permutation [a] (l ++ l) -> Permutation l1 l2.
Proof. intros. permutation_solver eq_dec. Qed.
