Require Import PermutationSolver.

Import ListNotations.

Parameter A : Set.
Axiom eq_dec : forall x y : A, {x = y} + {x <> y}.

Goal forall a b c d e f : list A,
  Permutation (a ++ b) c ->
  Permutation (d ++ e) f ->
  Permutation (a ++ d ++ e ++ b) (f ++ c).
Proof. intros. permutation_solver eq_dec. Qed.

Goal forall a b c d e (x y : A),
  Permutation (a ++ e) (x :: c) ->
  Permutation b (y :: d) ->
  Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof. intros. permutation_solver eq_dec. Qed.

Goal forall a b (x y : A),
  Permutation a b ->
  Permutation [x] [y] ->
  Permutation (a ++ [x]) (y :: b).
Proof. intros. permutation_solver eq_dec. Qed.

Goal forall a b (x y : A),
  Permutation (a ++ [x]) (y :: b) ->
  Permutation [x] [y] ->
  Permutation a b.
Proof. intros. permutation_solver eq_dec. Qed.

Goal forall (b u t e r f l y : A) xs ys,
  Permutation xs ys ->
  Permutation ([b;u;t;t;e;r]++[f;l;y]++xs) ([f;l;u;t;t;e;r]++ys++[b;y]).
Proof. intros. permutation_solver eq_dec. Qed.


(** Proving preorder, inorder and postorder of a BST are permutation of each
    other. *)
Inductive tree : Set :=
| Leaf : tree
| Node : tree -> A -> tree -> tree.

Fixpoint inorder t : list A :=
  match t with
  | Leaf => nil
  | Node l v r => inorder l ++ v :: inorder r
  end.

Fixpoint preorder t : list A :=
  match t with
  | Leaf => nil
  | Node l v r => v :: preorder l ++ preorder r
  end.

Fixpoint postorder t : list A :=
  match t with
  | Leaf => nil
  | Node l v r => postorder l ++ postorder r ++ [v]
  end.

Theorem tree_orders t :
  Permutation (inorder t) (preorder t) /\
  Permutation (inorder t) (postorder t).
Proof. induction t; cbn; intuition (permutation_solver eq_dec). Qed.


(** Uses of [map] and [rev] *)
Goal forall l0 l1 l2 l3 l4 l5 l6 l7 l8 (a : A),
  Permutation (l1 ++ l8) (l4 ++ l0) ->
  Permutation l2 (l5 ++ a :: l3) ->
  Permutation (l8 ++ l6) (l4 ++ l5) ->
  Permutation l7 (rev l3 ++ rev l0) ->
  Permutation (l1 ++ l2) (a :: l6 ++ rev l7).
Proof. intros. permutation_solver eq_dec. Qed.

Goal forall B (f : B -> A) l0 l1 l2 l3 l4 l5 l6 l7 l8 a,
  Permutation (l1 ++ l8) (l4 ++ map f l0) ->
  Permutation l2 (l5 ++ a :: map f l3) ->
  Permutation (l8 ++ l6) (l4 ++ l5) ->
  Permutation (map f l7) (map f l0 ++ map f l3) ->
  Permutation (l1 ++ l2) (a :: l6 ++ map f l7).
Proof. intros. permutation_solver eq_dec. Qed.

Goal forall B (f : B -> A) l0 l1 l2 l3 l4 l5 l6 l7 l8 a,
  Permutation (l1 ++ l8) (l4 ++ map f l0) ->
  Permutation l2 (l5 ++ a :: map f l3) ->
  Permutation (l8 ++ l6) (l4 ++ l5) ->
  Permutation l7 (l0 ++ l3) ->
  Permutation (l1 ++ l2) (a :: l6 ++ map f l7).
Proof. intros. permutation_solver eq_dec. Qed.


(** Cancelation *)

Lemma Permutation_cancel (l1 l2 l l' : list A) :
  Permutation (l1 ++ l) (l' ++ l2) -> Permutation l l' -> Permutation l1 l2.
Proof. intros. permutation_solver eq_dec. Qed.

Lemma Permutation_cancel_sgt l1 l2 (a : A) :
  Permutation (l1 ++ [a]) (a :: l2) -> Permutation l1 l2.
Proof. intros. permutation_solver eq_dec. Qed.


(** Contradiction *)

Goal forall l (a : A),
  ~ Permutation (a :: l) (a :: l ++ a :: l).
Proof. intros a l HP. permutation_solver eq_dec. Qed.

Goal forall l (a : A),
  ~ Permutation [a] (l ++ l).
Proof. intros a l HP. permutation_solver eq_dec. Qed.

Goal forall (l l1 l2 : list A) a,
  Permutation [a] (l ++ l) -> Permutation l1 l2.
Proof. intros. permutation_solver eq_dec. Qed.
