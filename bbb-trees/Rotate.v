Require Import Omega.

Definition twice x := x+x.
Definition fice x := twice(twice x).
Definition ice x := twice(fice x).

Definition vbig x y :=
  x > ice(y+1).

Definition big x y :=
  x > fice(y+1).

Definition vclose x y :=
  ~ big x y /\
  ~ big y x.

Definition close x y :=
  ~ vbig x y /\
  ~ vbig y x.

(*
  ice (x+1) >= y /\ 
  ice (y+1) >= x.
*)
Ltac basic :=
  unfold not in *;
  intros;
  unfold close in *;
  unfold vclose in *;
  unfold big in *;
  unfold vbig in *;
  unfold ice in *;
  unfold fice in *;
  unfold twice in *;
  try omega.
  

Locate "{ _ } + { _ }".
Print sumbool.
Print or.
Check (fun a b => a = b \/ a < b).

Theorem t1 a b: a = b \/ a < b -> {a = b} + {a < b}.
Proof.
  intros.
  Print or.
  elim H.
  destruct H.

Lemma singleLeft :
  exists A, exists B, exists C,
    close A B /\
    close (A+B+1) C /\
    vbig (twice A) B /\
    close (twice A - 1) B /\
    ~vclose (twice A) (B+C+1).
Proof.
  basic.
  Locate {
  intros.
Qed.

Lemma singleLeft :
  ~forall A B C,
    close A B ->
    close (A+B+1) C ->
    vbig (twice A) B ->
    close (twice A - 1) B ->
    vclose (twice A) (B+C+1).
Proof.
  basic.
  intros.
Qed.

Print singleLeft.