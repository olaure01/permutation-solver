From Coq Require Export List Permutation.
From Coq Require Import Lia.

#[local] Ltac isolate_singleton Hdec h :=
  let l := fresh "l" in
  let Heql := fresh "Heql" in
  let Heq := fresh "Heq" in
  let Hc := fresh in
  remember (h :: nil) as l eqn:Heql;
  assert (forall l', h :: l' = l ++ l') as Hc by (intros; rewrite Heql; cbn; reflexivity);
  repeat match goal with
  | |- context[h :: ?t] => rewrite_all (Hc t)
  | H : Permutation _ _ |- _ => match type of H with
                                | context[h :: ?t] => rewrite_all (Hc t)
                                end
  end; clear Hc;
  destruct (proj1 (@count_occ_sgt _ Hdec _ _) Heql) as [Heq _]; clear Heql.

Ltac permutation_solver Hdec :=
  subst;
  repeat match goal with
  | |- context[?h :: ?t]  => isolate_singleton Hdec h
  | H : Permutation _ _ |- _ => match type of H with
                                | context[?h :: ?t]  => isolate_singleton Hdec h
                                end
  end;
  let z := fresh "z" in
  try (rewrite (Permutation_count_occ Hdec); intros z);
  repeat match goal with
  | H : Permutation _ _ |- _ => rewrite (Permutation_count_occ Hdec) in H; specialize (H z)
  end;
  rewrite ? count_occ_app, ? count_occ_nil in *; lia.
