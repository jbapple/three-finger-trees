Set Implicit Arguments.
Require Import Arith.
Require Import List.

Section Measurable.

Parameter A:Type.
Parameter measure:A->nat.

Parameter maxMeasure:nat.
Parameter maxLemma:forall v, measure v <= maxMeasure.

Print comparison.

Fixpoint divideHelp (a:nat) (n:nat) (r:list A) (c:list A) :=
  match c with
    | nil => (rev r,c)
    | x :: xs =>
      let mx := measure x in
        match nat_compare (2*(a+mx)) (n+maxMeasure) with
          | Gt => (rev r,c)
          | _ => divideHelp (a+mx) n (x::r) xs
        end
  end.

Ltac help :=
  intros; simpl in *; auto; subst;
    match goal with
      | [|- context[match ?pq with
                      | pair _ _ => _
                    end]]
        =>
        let H := fresh 
          in remember pq as H; destruct H; help
      | [|- context[match ?T with
                      | Eq => _
                      | Lt => _
                      | Gt => _
                    end]]
        =>
        let H := fresh 
          in remember T as H; destruct H; help
      | [_: context[match ?pq with
                      | pair _ _ => _
                    end] |-_]
        =>
        let H := fresh 
          in remember pq as H; destruct H; help
      | [_: context[match ?T with
                      | Eq => _
                      | Lt => _
                      | Gt => _
                    end] |-_]
        =>
        let H := fresh 
          in remember T as H; destruct H; help
      | [H:(?p,?q) = (?r,?s) |-_]
        =>
        inversion_clear H; help
      | _ => idtac

    end.

Lemma divideHelpDivides :
  forall c a n r p q,
    (p,q) = divideHelp a n r c ->
    (p++q) = (rev r)++c.
Proof.
(*
  assert (forall t x (y:t) z, (x ++ y::nil) ++ z = x ++ y::z) as appSnoc.
  clear.
  induction x; intros; simpl in *; auto.
  rewrite IHx; auto.
*)

  induction c; help.
  erewrite IHc with (r := a::r); help.
  rewrite app_ass; help.
  eauto.
  erewrite IHc with (r := a::r); help.
  rewrite app_ass; help.
  eauto.
Qed.

Fixpoint total (c:list A) :=
  match c with
    | nil => 0
    | x::xs => (measure x)+(total xs)
  end.

Require Import Omega.

Lemma totalApp : forall x y, total (x++y) = total x + total y.
Proof.
  induction x; simpl; intros; auto.
  rewrite IHx; auto with arith.
Qed.

Lemma totalRev : forall x, total (rev x) = total x.
Proof.
  induction x; simpl; intros; auto.
  rewrite totalApp; simpl.
  rewrite IHx. omega.
Qed.

Lemma divideHelpLess :
  forall c n r p q,
    total r + total c = n ->
    2*(total r) <= n+maxMeasure ->
    (p,q) = divideHelp (total r) n r c ->
    2*(total p) <= n+maxMeasure
    /\
    n <= 2*(total p) + maxMeasure.
Proof.


  Ltac compareProp := help;
    match goal with
      | [H:Eq = _ |- _]
        =>
        symmetry in H; apply nat_compare_eq in H; compareProp
      | [H:Lt = _ |- _]
        =>
        symmetry in H; apply nat_compare_lt in H; compareProp
      | [H:Gt = _ |- _]
        =>
        symmetry in H; apply nat_compare_gt in H; compareProp
      | _ => idtac
    end.

  induction c; compareProp.
  rewrite totalRev; split; try omega.

  eapply IHc with (r := a::r); compareProp; try omega.
  rewrite plus_comm. eauto.

  eapply IHc with (r := a::r); compareProp; try omega.
  rewrite plus_comm. eauto.

  rewrite totalRev.
  assert (measure a <= maxMeasure). apply maxLemma.
  omega.
Qed.

Definition divide c := divideHelp 0 (total c) nil c.

Lemma divideEven :
  forall c p q,
    (p,q) = divide c ->
      (2*(total p)) <= (total c) + maxMeasure
      /\
      total c <= (2*(total p)) + maxMeasure
      /\
      (2*(total q)) <= total c + maxMeasure
      /\
      total c <= (2*(total q)) + maxMeasure.
Proof.
  compareProp.
  unfold divide in *.
  
  assert (p ++ q = c).
  erewrite divideHelpDivides; eauto; compareProp.

  assert (total p + total q = total c).
  erewrite <- totalApp. f_equal; auto.

  pose (@divideHelpLess c (total c) nil p q) as D.
  assert (2 * total p <= total c + maxMeasure
          /\
          total c <= 2 * total p + maxMeasure) as D2.
  apply D; compareProp; try omega.
  destruct D2. clear D.
  repeat split; try omega.
Qed.
