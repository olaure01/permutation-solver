From Coq Require Export List Permutation.
From Coq Require Import Lia.

(* TODO remove once in stdlib *)
Lemma count_occ_rev [A] decA (l : list A) x : count_occ decA (rev l) x = count_occ decA l x.
Proof.
Admitted.

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

(* enrich Permutation hypotheses by applying [map f] *)
#[local] Ltac mapify f :=
  repeat match goal with
  | H : Permutation ?l1 ?l2 |- _ =>
     lazymatch type of H with
     | context[map f _] => fail
     | _ => idtac
     end;
     match goal with
     | Hf : Permutation (map f l1) (map f l2) |- _ => fail 1
     | _ => let Hf := fresh H in assert (Hf := Permutation_map f H)
     end
  end.

(* enrich Permutation hypotheses with all possible [map] *)
#[local] Ltac mapify_all :=
  repeat match goal with
  | |- context[map ?f _] => progress (mapify f)
  | H : context[map ?f _] |- _ => progress (mapify f)
  end;
  rewrite ? map_app in *.

Ltac permutation_solver Hdec :=
  subst;
  repeat match goal with
  | |- context[?h :: ?t]  => isolate_singleton Hdec h
  | H : Permutation _ _ |- _ => match type of H with
                                | context[?h :: ?t]  => isolate_singleton Hdec h
                                end
  end;
  rewrite <- ? map_rev in *; mapify_all; rewrite -> ? map_rev in *;
  let z := fresh "z" in
  try (rewrite (Permutation_count_occ Hdec); intros z);
  repeat match goal with
  | H : Permutation _ _ |- _ => rewrite (Permutation_count_occ Hdec) in H; specialize (H z)
  end;
  rewrite ? count_occ_app, ? count_occ_rev, ? count_occ_nil in *; lia.
