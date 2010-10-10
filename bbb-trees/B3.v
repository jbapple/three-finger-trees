Set Implicit Arguments.
Require Import List.
Require Import Arith.

Section Over.

Variable A:Type.
Variable NAT:Type.
Variable down:NAT -> nat.
Variable up:nat -> NAT.
Variable isoDown: forall n, up (down n) = n.
Variable isoUp: forall n, down (up n) = n.
Variable POW: NAT -> NAT.
Variable BASE: NAT.

Fixpoint pow n :=
  match n with
    | 0 => 1
    | S m => pow m * down BASE
  end.

Variable powIs : forall n, down (POW n) = pow (down n).
Variable DIGITS:NAT -> NAT.
Variable digit0 : forall n, down n = 0 -> down (DIGITS n) = 0.
Variable digitS :
  forall n, 
    down n > 0 ->
    exists m,
    down (DIGITS n) = S m
    /\
    pow m <= down n
    /\
    down n < pow (S m).


(*
Inductive FullTree := 
  Leaf : A -> FullTree
| Branch : NAT -> list (FullTree * A) -> FullTree.
*)

Inductive FullTreeMut := 
  Leaf : A -> FullTreeMut
| Branch : NAT -> ChildList (*list (FullTree * A)*) -> A -> FullTreeMut
with ChildList :=
  Nil : ChildList
| Cons : FullTreeMut -> ChildList -> ChildList.

Print FullTreeMut_ind.

Scheme fullTreeMutInduct := Induction for FullTreeMut Sort Prop
with childListInduct := Induction for ChildList Sort Prop.

Print fullTreeMutInduct.


forall 
  (P : FullTree -> Prop) 
  (Q : ChildList -> Prop),
  (forall a : A, P (Leaf a)) ->
       (forall (n : NAT) (c : ChildList), Q c -> P (Branch n c)) ->
       Q Nil ->
       (forall f2 : FullTreeMut,
        P f2 -> forall (a : A) (c : ChildList), Q c -> Q (Cons f2 a c)) ->
       forall f3 : FullTreeMut, P f3




(*
Section TreeInduct.
  
  Variables
    (P: FullTree -> Prop)
    (Q: list (FullTree * A) -> Prop)
    (R: FullTree -> A -> list (FullTree * A) -> Prop)
    (S: list (FullTree * A) -> NAT -> Prop)
    (PLeaf: forall x, P (Leaf x))
    (PBranch: forall n c, Q c -> S c n -> P (Branch n c))
    (QNil: Q nil)
    (QCons: forall t b c, P t -> R t b c -> Q c -> Q ((t,b)::c)).

  Fixpoint treeInduct (x:FullTree) : P x :=
    match x as t return P t with
      | Leaf v => PLeaf v
      | Branch n c =>
        PBranch
        ((fix help (d:list (FullTree * A)) : Q d :=
          match d as e return Q e with
            | nil => QNil
            | ((v,b)::xs) => QCons (treeInduct v) _ (help xs)
          end) c) _
    end.

End TreeInduct.
*)

(*
Section TreeInduct.
  
  Variables
    (P: FullTree -> option A -> Prop)
    (Q: list (FullTree * A) -> option A -> Prop)
    (PLeafNone: forall x, P (Leaf x) None)
    (PLeafSome: forall x, P (Leaf x) (Some x))
    (PBranchNone: forall n c, Q c None -> P (Branch n c) None)
    (PBranchSome: forall n c b, Q c (Some b) -> P (Branch n c) (Some b))
    (QNil: Q nil None)
    (QOne: forall t b, Q ((t,b)::nil) (Some b))
    (QCons: forall t b0 b1 c cs, P t (Some b0) -> Q (c::cs) b1 -> Q ((t,b0)::c::cs) b1).

  Definition LastSome S T U (f:T -> option S) :=
    fix help (ans:option S) (tyl:list (T*U)) {struct tyl} :=
    match tyl with
      | nil => ans
      | (y,_)::ys => 
        match f y with
          | None => help ans ys
          | Some newAns => help (Some newAns) ys
        end
    end.

  Fixpoint rightMost (x:FullTree) : option A :=
    match x with
      | Leaf v => Some v
      | Branch _ nil => None
      | Branch _ ((t,_)::xs) => LastSome rightMost (rightMost t) xs
    end.

(*
  Fixpoint rightMost (x:FullTree) : option A :=
    match x with
      | Leaf v => Some v
      | Branch _ nil => None
      | Branch _ ((t,_)::xs) =>
        ((fix help ans tyl {struct tyl} :=
          match tyl with
            | nil => ans
            | (y,_)::ys => 
              match rightMost y with
                | None => help ans ys
                | Some newAns => help (Some newAns) ys
              end
          end) (rightMost t) xs)
    end.
    *)
  

  Fixpoint treeInduct (x:FullTree) : P x (rightMost x) :=
    match x as t return P t with
      | Leaf v => PLeafSome v
      | Branch n zs => 
        ((fix help ss :=
          match ss with
            | nil => PBranchNone QNil
            | ((y,b)::nil) =>
              match rightMost y with
                | None => PBranchNone (treeInduct 
              match LastSome rightMost (rightMost y) xs with
                | None => PBranchNone QNil
                | Some lst => PBranchSome (
        match rightMost
        PBranch _
        ((fix help (d:list (FullTree * A)) : Q d :=
          match d as e return Q e with
            | nil => QNil
            | ((v,b)::xs) => QCons _ (treeInduct v) (help xs)
          end) c)
    end.

End TreeInduct.
*)

Section TreeInduct.
  
  Variables
    (P: FullTree -> Prop)
    (Q: list (FullTree * A) -> Prop)
    (PLeaf: forall x, P (Leaf x))
    (PBranch: forall n c, Q c -> P (Branch n c))
    (QNil: Q nil)
    (QCons: forall t b c, P t -> Q c -> Q ((t,b)::c)).

  Fixpoint treeInduct (x:FullTree) : P x :=
    match x as t return P t with
      | Leaf v => PLeaf v
      | Branch n c =>
        PBranch _
        ((fix help (d:list (FullTree * A)) : Q d :=
          match d as e return Q e with
            | nil => QNil
            | ((v,b)::xs) => QCons _ (treeInduct v) (help xs)
          end) c)
    end.

End TreeInduct.

(*
Section TreeInduct.
  
  Variables
    (P: A -> FullTree -> A -> Prop)
    (Q: A -> list (FullTree * A) -> A -> Prop)
    (PLeaf: forall x, P x (Leaf x) x)
    (PBranch: forall n a c b, Q a c b -> P a (Branch n c) b)
    (QNil: forall a b, Q a nil b)
    (QOne: forall a b t, P a t b -> Q a ((t,b)::nil) b)
    (QCons: forall t a1 a2 a3 c cs, 
      P a1 t a2 -> 
      Q a2 (c::cs) a3 -> 
      Q a1 ((t,a2)::c::cs) a3).

  Fixpoint leftMost (x:FullTree) : A :=
    match x with
      | Leaf v => v
      | Branch _ 

  Fixpoint treeInduct (a:A) (x:FullTree) (b:A) : P a x b :=
    match x as t return P t with
      | Leaf v => PLeaf v
      | Branch n c =>
        PBranch _
        ((fix help (d:list (FullTree * A)) : Q d :=
          match d as e return Q e with
            | nil => QNil
            | ((v,b)::xs) => QCons _ (treeInduct v) (help xs)
          end) c)
    end.

End TreeInduct.
*)

    

(*
Definition childReduce (S T:Type)
  (reduce:FullTree -> A ->T) 
  (zero:S)
  (one:FullTree -> A -> S)
  (more:T -> S -> S)
   :=
  fix help (xs:list (FullTree*A)) : S :=
  match xs with
    | nil => zero
    | (y,b)::nil => one y b
    | (y,b)::ys => more (reduce y b) (help ys)
  end.
*)

Definition childReduce (S T U:Type)
  (reduce:S -> U ->T) 
  (zero:T)
  (more:T -> T -> T)
   :=
  fix help (xs:list (S*U)) : T :=
  match xs with
    | nil => zero
    | (y,b)::nil => reduce y b
    | (y,b)::ys => more (reduce y b) (help ys)
  end.

Lemma childInduct :
  forall S T U (P:list (S*U) -> T -> Prop) reduce zero more, 
    P nil zero ->
    (forall y b, P ((y,b)::nil) (reduce y b)) ->
    (forall y b z zs res, P (z::zs) res -> P ((y,b)::z::zs) (more (reduce y b) res)) ->
    forall xs, P xs (childReduce reduce zero more xs).
Proof.
  intros S T U P reduce zero more pzero preduce pmore.
  induction xs.
  simpl; assumption.
  destruct xs.
  simpl. destruct a. apply preduce.
  simpl. destruct a.
  apply pmore.
  (* note how weak the IH is here *)
  simpl in IHxs.
  apply IHxs.
Qed.

(*
Lemma childInductRefine :
  forall S T U (P:list (S*U) -> T -> Prop) reduce zero more, 
    P nil zero ->
    (forall y b, P ((y,b)::nil) (reduce y b)) ->
    (forall y b z zs res, P (z::zs) res -> P ((y,b)::z::zs) (more (reduce y b) res)) ->
    forall xs, P xs (childReduce reduce zero more xs).
Proof.
  refine
    (fun S T U (P:list (S*U) -> T -> Prop) reduce zero more 
      pzero preduce pmore =>
      fix help xs :=
      match xs as xs' return P xs' (childReduce reduce zero more xs') with
        | nil => pzero
        | (y,b)::nil => preduce y b
        | (y,b)::z::zs => pmore _ _ _ _ _ _
      end).
  (* 'help' looks much too strong here *)
  unfold childReduce in help.
  simpl.
  pose (help (z :: zs)) as ans.
  destruct z as [y1 b0].
  apply ans.
  Show Proof.
  Print childInduct.
  (*Guarded.*)
Abort.
*)

Lemma childReduceDownSome :
  forall S U T reduce zero (more:option T-> option T-> option T) 
    (xs :list (S*U)),
    (forall p q,
      None <> more p q ->
      None <> p /\ None <> q) ->
    None <> childReduce reduce zero more xs ->
    (forall x y,
      In (x,y) xs ->
      None <> reduce x y).
Proof.
  induction xs; simpl in *; intros; auto.
  inversion_clear H1; simpl in *; subst; auto.
  destruct xs. auto.
  eapply H with (p := reduce x y) (q:= childReduce _ _ _ _). eauto.
  eapply IHxs; eauto.
  destruct a; destruct xs.
  simpl in *; auto.
  eapply H. eauto.
Qed.

Definition treeReduce (T:Type)
  (leaf:A -> option A -> T)
  (branch:NAT -> T -> option A -> T)
  (zero:T)
  (more:T -> T -> T) :=
  fix help (x:FullTree) (b:option A) : T :=
  match x with
    | Leaf v => leaf v b
    | Branch n c =>
      let helper x y := help x (Some y)
        in branch n (childReduce helper zero more c) b
  end.

Require Import Program.

Definition nominalSize x :=
  match x with
    | Leaf _ => up 1
    | Branch m _ => m
  end.

Check childReduce.

(*
Lemma treeRedInduct : forall
  (T:Type)
  (leaf:A -> option A -> T)
  (branch:NAT -> T -> option A -> T)
  (zero:T)
  (more:T -> T -> T)
  (P:FullTree -> option A -> T -> Prop)
  (Q:NAT -> list (FullTree*A) -> option A -> Prop)
  (pleaf:forall v b, P (Leaf v) b (leaf v b))
  (pbranch:forall n c b r, 
    Q n c b -> 
    P (Branch n c) b (branch n (childReduce r zero more c) b))
  (qnil:forall n b, Q n nil b)
  (qone:forall x b t, P x (Some b) t -> Q (nominalSize x) ((x,b)::nil) (Some b))
  (qcons:forall x b c d y ys m r, P x (Some b) r -> Q m ((y,c)::ys) d -> 
    Q (up ((down (nominalSize x)) + (down m))) ((x,b)::(y,c)::ys) d)
  (x:FullTree) (b:option A), P x b (treeReduce leaf branch zero more x b).
Proof.
  intros.
  pattern x.
  eapply treeInduct
  simpl. auto.
  simpl.
  intros.
  apply pbranch.
  apply H.
  generalize dependent b.
  generalize dependent x.
  induction x; auto.
  simpl. apply pleaf.
  simpl.
  intros.
  eapply pbranch.
  induction l.
  apply qnil.
  destruct l.
  
  apply qone.
  match x with
    | Leaf v => pleaf v b
    | Branch n c => _
  end.
Next Obligation.
  simpl in *.
*)


Program Definition treeInductP 
  (T:Type)
  (leaf:A -> option A -> T)
  (branch:NAT -> T -> option A -> T)
  (zero:T)
  (more:T -> T -> T)
  (P:FullTree -> option A -> T -> Prop)
  (Q:NAT -> list (FullTree*A) -> option A -> Prop)
  (pleaf:forall v b, P (Leaf v) b (leaf v b))
  (pbranch:forall n c b r, 
    Q n c b -> 
    P (Branch n c) b (branch n (childReduce r zero more c) b))
  (qnil:forall n b, Q n nil b)
  (qone:forall x b t, P x (Some b) t -> Q (nominalSize x) ((x,b)::nil) (Some b))
  (qcons:forall x b c d y ys m r, P x (Some b) r -> Q m ((y,c)::ys) d -> 
    Q (up ((down (nominalSize x)) + (down m))) ((x,b)::(y,c)::ys) d) :=
  fix help (x:FullTree) (b:option A) : P x b (treeReduce leaf branch zero more x b) :=
  match x with
    | Leaf v => pleaf v b
    | Branch n c => 
      match c with
        | nil => pbranch _ _ _ _ (qnil _ _)
        | (y,b)::ys => 
          ((fix inner res zs :=
            match zs with
              | nil => res
              | (u,d)::us =>
                qcons (help _ _ _ u (Some d)) (inner _ _ us)
            end) (help y (Some b)) ys)
      end
  end.
Next Obligation.
  admit.
Next Obligation.
  admit.
Defined.
Admitted.
  simpl in *.
  apply pbranch.
  
  
      

Lemma treeInduct :
  forall T 
    leaf branch (zero:T) more
    (P:FullTree -> option A -> T -> Prop) Q,
    (forall v b, P (Leaf v) b (leaf v b)) ->
    (forall n c b r, Q n (childReduce r zero more c) b -> 
      P (Branch n c) b (branch n (childReduce r zero more c) b)) ->
    forall x b, P x b (treeReduce leaf branch zero more x b).
Proof.
  intros T leaf branch zero more P Q pleaf pbranch.
  induction x.
  simpl. apply pleaf.
  simpl.
    ->
      (branch n 
        (childReduce _ zero more c) b)
    Q nil ->
    (forall y b, Q ((y,b)::nil)) ->
    (forall y b z zs res, Q c n b (z::zs) res -> P ((y,b)::z::zs) (more (reduce y b) res)) ->
    (forall v b, P (Leaf v) b (leaf v b)) ->
    (forall n c b, 
      Q res
      P (Branch n c) b 
      (let helper x y := treeReduce leaf branch zero more x (Some y)
        in branch n (childReduce helper zero more c) b)) ->
    forall x b, P x b (treeReduce leaf branch zero more x b).
Proof.
  refine 
    (fun T (P:FullTree -> option A -> T -> Prop) leaf branch (zero:T) more
      pleaf pbranch =>
      fix help (x:FullTree) (b:option A) : T :=
      match x as x' return P x' b (treeReduce leaf branch zero more x' b) 
        with
        | Leaf v => pleaf v b
        | Branch n c => 
          let helper x y := help x (Some y)
            in pbranch n (childReduce helper zero more c) b
      end 
      (T:Type)
      
      (leaf:A -> option A -> T)
      (branch:NAT -> T -> option A -> T)
      (zero:T)
      (more:T -> T -> T) :=
  fix help (x:FullTree) (b:option A) : T :=
  match x with
    | Leaf v => leaf v b
    | Branch n c =>
      let helper x y := help x (Some y)
        in branch n (childReduce helper zero more c) b
  end.

    (forall y b, P ((y,b)::nil) (reduce y b)) ->
    (forall y b z zs, P ((y,b)::z::zs) (more (reduce y b) (childReduce reduce zero more (z::zs)))) ->
    forall xs, P xs (childReduce reduce zero more xs).
Proof.
*)

Definition toList :=
  treeReduce 
  (fun x _ => cons x nil)
  (fun _ x _ => x)
  nil
  (@app _).

(*Eval compute in (toList (Leaf x)).*)

Definition someReduce (T:Type) leaf branch zero more 
  : FullTree -> option A -> option T :=
  treeReduce leaf 
  (fun n r b =>
    match r with
      | None => None
      | Some v => branch n v b
    end)
  zero
  (fun p q =>
    match p,q with
      | Some x, Some y => more x y
      | _, _ => None
    end).

Definition children x :=
  match x with
    | Leaf _ => nil
    | Branch _ xs => xs
  end.


Lemma someReduceDownSome :
  forall T leaf branch zero (more:T -> T -> option T) xs b,
    None <> someReduce leaf branch zero more xs b ->
    (forall x c,
      In (x,c) (children xs) ->
      None <> someReduce leaf branch zero more x (Some c)).
Proof.
  eapply treeInduct.


Lemma someReduceDownSome :
  forall T leaf branch zero (more:T -> T -> option T) xs b,
    None <> someReduce leaf branch zero more xs b ->
    (forall x c,
      In (x,c) (children xs) ->
      None <> someReduce leaf branch zero more x (Some c)).
Proof.
  induction xs; simpl in *; intros; auto.
  remember (childReduce
          (fun (x : FullTree) (y : A) =>
           someReduce leaf branch zero more x (Some y)) zero
          (fun p q : option T =>
           match p with
           | Some x => match q with
                       | Some y => more x y
                       | None => None
                       end
           | None => None
           end) l) as a.
  destruct a.
  pose childReduceDownSome as d.
  pose (d _ _ _ (fun x y => someReduce leaf branch zero more x (Some y))
  zero
          (fun p q : option T =>
           match p with
           | Some x => match q with
                       | Some y => more x y
                       | None => None
                       end
           | None => None
           end) l) as e.
  simpl in *.
  eapply e.
  intros; auto.
  split; destruct p; destruct q; auto; try discriminate.
  rewrite <- Heqa. discriminate. auto.

  assert False as F.
  apply H. auto. inversion F.
Qed.
    

Definition accurateNominalHelp :=
  someReduce
  (fun _ _ => Some 1)
  (fun n k _ =>
    if beq_nat (down n) k
      then Some k
      else None)
  (Some 0)
  (fun n m => Some (n+m)).

Definition digitsHelp :=
  someReduce
  (fun _ _ => Some 0)
  (fun n m _ =>
    match down n with
      | 0 => None
      | S p =>
        if beq_nat (down (DIGITS (up p))) (S m)
          then Some (S m)
          else None
    end)
  None
  (fun n m => 
    if beq_nat n m
      then Some n
      else None).

Definition orderedHelp (comp:A->A->comparison) :=
  someReduce
  (fun p _ => Some (p,p))
  (fun _ pq b => Some pq)
  None
  (fun pq rs =>
    let (p,q) := pq in
    let (r,s) := rs in
    match comp q r with
      | Gt => None
      | _ => Some (p,s)
    end).

Definition maxBoundsHelp (aeq:A->A->bool) :=
  someReduce
  (fun p q =>
    match q with
      | None => Some p
      | Some r =>
        if aeq p r
          then Some p
            else None
    end)
  (fun _ p b =>
    match b with
      | None => Some p
      | Some c =>
        if aeq p c 
          then Some p
          else None
    end)
  None
  (fun p q => Some q).


Definition ordered f x :=
  match orderedHelp f x None with
    | None => False
    | Some _ => True
  end.

Fixpoint listOrderedHelp T (f:T -> T -> comparison) x xs :=
  match xs with
    | nil => True
    | y::ys => 
      match f x y with
        | Gt => False
        | _ => listOrderedHelp f y ys
      end
  end.

Definition listOrdered T (f:T -> T -> comparison) xs :=
  match xs with
    | nil => True
    | y::ys => listOrderedHelp f y ys
  end.

Print FullTree_rect.

(*

IDEA: induction principle specific to catamorphisms above

*)

Print childReduce.


Definition childInduct
  (reduce:FullTree -> A -> Prop) 
  (zero:Prop)
   :=
  fix help (xs:list (FullTree*A)) : Prop :=
  match xs with
    | nil => zero
    | (y,b)::nil => reduce y b
    | (y,b)::ys => reduce y b /\ help ys
  end.


Lemma childReduceDownSome :
  forall T reduce zero (more:option T-> option T-> option T) xs,
    (forall p q,
      None <> more p q ->
      None <> p /\ None <> q) ->
    None <> childReduce reduce zero more xs ->
    (forall x y,
      In (x,y) xs ->
      None <> reduce x y).
Proof.
  induction xs; simpl in *; intros; auto.
  inversion_clear H1; simpl in *; subst; auto.
  destruct xs. auto.
  eapply H with (p := reduce x y) (q:= childReduce _ _ _ _). eauto.
  eapply IHxs; eauto.
  destruct a; destruct xs.
  simpl in *; auto.
  eapply H. eauto.
Qed.

Definition treeReduce (T:Type)
  (leaf:A -> option A -> T)
  (branch:NAT -> T -> option A -> T)
  (zero:T)
  (more:T -> T -> T) :=
  fix help (x:FullTree) (b:option A) : T :=
  match x with
    | Leaf v => leaf v b
    | Branch n c =>
      let helper x y := help x (Some y)
        in branch n (childReduce helper zero more c) b
  end.


Lemma orderedList :
  forall f x,
    ordered f x ->
    listOrdered f (toList x None).
Proof.
  eapply treeReduce. Focus 4. Focus 3.
  induction x. Focus 2.
  induction x; simpl in *; intros; auto.
  induction l; simpl in *; intros; auto.
  destruct a as [y b]; subst; simpl in *; auto.
  destruct l; simpl in *.




Definition boundsHelp (comp:A->A->comparison) :=
  someReduce
  (fun p q =>
    match q with
      | None => Some (p,p)
      | Some r =>
        match comp p r with
          | Eq => Some (p,r)
          | _ => None
        end
    end)
  (fun _ pq b =>
    match b with
      | None => Some pq
      | Some c =>
        let (p,q) := pq in
        match comp q c with
          | Eq => Some (p,c)
          | _ => None
        end
    end)
  None
  (fun pq rs =>
    let (p,q) := pq in
    let (r,s) := rs in
    match comp q r with
      | Gt => None
      | _ => Some (p,s)
    end).


Definition accurateAccum (f:FullTree -> option nat) :=
  fix help (x:list (FullTree * A)) :=
  match x with
    | nil => Some 0
    | (y,_) :: ys => 
      match f y with
        | None => None
        | Some k =>
          match help ys with
            | None => None
            | Some j => Some (k+j)
          end
      end
  end.

Lemma accurateAccumDownSome :
  forall f xs,
    None <> accurateAccum f xs ->
    (forall x,
      In x xs ->
      None <> f (fst x)).
Proof.
  induction xs; simpl in *; intros; auto.
  destruct a; simpl in *.
  remember (f f0) as b; destruct b; simpl in *; auto.
  remember (accurateAccum f xs) as c; destruct c; simpl in *; auto.
  inversion_clear H0; subst; simpl in *; auto.
  rewrite <- Heqb; discriminate.
  eapply IHxs; auto; discriminate.
Qed.

Lemma accurateAccumSomeUp :
  forall f xs,
    (forall x,
      In x xs ->
      ~(None = f (fst x))) ->
    ~(None = accurateAccum f xs).
Proof.
  intros f xs; induction xs; simpl in *; intros; auto.
  discriminate.
  (*remember a as d; destruct d;*)
  destruct a;
    simpl in *; auto.
  remember (f f0) as b; destruct b.
  remember (accurateAccum f xs) as c; destruct c; try discriminate.
  apply IHxs; intros; simpl in *; auto.
  pose (H (f0, a)) as e; simpl in *; auto.
  destruct e; auto.
Qed.

Fixpoint accurateNominalHelp x :=
  match x with
    | Leaf _ => Some 1
    | Branch n ys =>
      match accurateAccum accurateNominalHelp ys with
        | None => None
        | Some m =>
          if beq_nat m (down n)
            then Some m
            else None
      end
  end.


Lemma accurateNominalSomeDown :
  forall x, 
    None <> accurateNominalHelp x ->
    forall y,
      In y (children x) ->
      None <> accurateNominalHelp y.
Proof.
  induction x; intros; simpl in *; auto.
  generalize dependent n.
  induction l; simpl in *; auto; intros.
  inversion_clear H0; subst; simpl in *; auto.
  destruct a as [y ya]; simpl in *; auto.  
  remember (accurateNominalHelp y) as g; destruct g; simpl in *; auto.
  discriminate.

  destruct a; simpl in *; auto.
  remember (accurateNominalHelp f) as b; destruct b; simpl in *; auto.
  remember (accurateAccum accurateNominalHelp l) as c; destruct c;
    simpl in *; auto; try discriminate.
  apply IHl with (up n1); auto.
  
  remember (accurateAccum accurateNominalHelp l) as b; destruct b;
    simpl in *; auto; try discriminate.
  
  rewrite isoUp.
  rewrite <- beq_nat_refl.
  discriminate.
Qed.

Definition accurateNominal x :=
  match accurateNominalHelp x with
    | None => False
    | Some _ => True
  end.


Definition digitsRel (f:FullTree -> option nat) :=
  fix help (b:option nat) (xs:list (FullTree * A)) :=
  match xs with
    | nil => b
    | (y,_)::ys =>
      match b, help (f y) ys with
        | Some n, Some m =>
          if beq_nat n m
            then Some n
            else None
        | _, _ => None
      end
  end.

Fixpoint digitsHelp x :=
  match x with
    | Leaf _ => Some 0
    | Branch n nil => None
    | Branch n ((y,_)::ys) => 
      match digitsRel digitsHelp (digitsHelp y) ys with
        | None => None
        | Some m =>
          match down n with
            | 0 => None
            | S p =>
              if beq_nat (down (DIGITS (up p))) (S m)
                then Some (S m)
                else None
          end
      end
  end.

Definition balanced x :=
  match digitsHelp x with
    | None => False
    | Some _ => True
  end.

Definition boundsList
  (f:FullTree -> option (A * A)) 
  (comp:A -> A -> comparison) :=
  fix help (pq:option (A * A)) (b:A) (xs : list (FullTree * A)) 
  : option (A * A) :=
  match pq with
    | None => None
    | Some (p,q) =>
      match comp b q with
        | Gt => None
        | Lt => None
        | Eq => 
          match xs with
            | nil => Some (p,q)
            | (t',b')::ys => 
              match help (f t') b' ys with
                | None => None
                | Some (r,s) =>
                  match comp q r with
                    | Gt => None
                    | _ => Some (p,s)
                  end
              end
          end
      end
  end.

Definition boundsHelp comp :=
  fix help x :=
  match x with
    | Leaf y => Some (y,y)
    | Branch _ nil => None
    | Branch _ ((t,b)::xs) => boundsList help comp (help t) b xs
  end.


(*
Definition boundsList 
  (f:FullTree -> option (A * A)) 
  (comp:A -> A -> comparison) :=
  fix help (xs : list (FullTree * A)) 
  : option (A * A) :=
  let assist t b g :=
    match f t with
      | None => None
      | Some (p,q) =>
        match comp b q with
          | Gt => None
          | Lt => None
          | Eq => g p q
        end
    end
    in
    match xs with
      | nil => None
      | (t,b)::nil =>
        assist t b (fun p q => Some (p,q))
      | (t,b)::ys =>
        assist t b (fun p q =>               
          match help ys with
            | None => None
            | Some (r,s) =>
              match comp q r with
                | Gt => None
                | _ => Some (p,s)
              end
          end)
  end.
*)

(*
Definition boundsList 
  (f:FullTree -> option (A * A)) 
  (comp:A -> A -> comparison) :=
  fix help (xs : list (FullTree * A)) 
  : option (A * A) :=
    match xs with
      | nil => None
      | (t,b)::ys =>
        match f t with
          | None => None
          | Some (p,q) =>
            match comp b q with
              | Gt => None
              | Lt => None
              | Eq => 
                match ys with
                  | nil => Some (p,q)
                  | _ =>
                    match help ys with
                      | None => None
                      | Some (r,s) =>
                        match comp q r with
                          | Gt => None
                          | _ => Some (p,s)
                        end
                    end
                end
            end
        end
    end.

Definition boundsHelp comp :=
  fix help x :=
  match x with
    | Leaf y => Some (y,y)
    | Branch _ ys => boundsList help comp ys
  end.
*)

(*
Definition boundsList2 
  (f:FullTree -> option (A * A)) 
  (comp:A -> A -> comparison) :=
  fix help (t:FullTree) (b:A) (xs : list (FullTree * A)) 
  : option (A * A) :=
  match f t with
    | None => None
    | Some (p,q) =>
      match comp b q with
        | Gt => None
        | Lt => None
        | Eq =>
          match xs with
            | nil => Some (p,q)
            | (y,c)::ys => 
              match help y c ys with
                | None => None
                | Some (r,s) =>
                  match comp q r with
                    | Gt => None
                    | _ => Some (p,s)
                  end
              end
          end
      end
  end.

Definition boundsHelp2 comp :=
  fix help x :=
  match x with
    | Leaf y => Some (y,y)
    | Branch _ nil => None
    | Branch _ ((z,b)::zs) => boundsList2 help comp z b zs
  end.

with boundsList f x :=
  match x with
    | Zero => None
    | One t y Zero => 
      match boundsHelp f t with
        | None => None
        | Some (p,q) =>
          match f y q with
            | Eq => Some (p,q)
            | _ => None
          end
      end
    | One t y ys =>
      match boundsHelp f t with
        | None => None
        | Some (p,q) =>
          match f y q with
            | Eq => 
              match boundsList f ys with
                | None => None
                | Some (r,s) =>
                  match f q r with
                    | Gt => None
                    | _ => Some (p,s)
                  end
              end
            | _ => None
          end
      end
  end.
*)

Definition ordered f x :=
  match boundsHelp f x with
    | None => False
    | Some _ => True
  end.

Definition childList f (tyl: list A) :=
  fix help (xs : list (FullTree * A)) :=
  match xs with
    | nil => tyl
    | y::ys => f (fst y) (help ys)
  end.

Fixpoint treeList x tyl :=
  match x with
    | Leaf x => x::tyl
    | Branch _ xs => childList treeList tyl xs
  end.

(*
Fixpoint treeList x :=
  match x with 
    | Leaf x => x :: nil
    | Branch _ xs => childList xs
  end
with childList xs :=
  match xs with
    | Zero => nil
    | One t _ ts =>
      treeList t ++ childList ts
  end.
*)

(*
Scheme trees := Induction for FullTree Sort Prop
with childs := Induction for Children Sort Prop.
*)

Print In.

Lemma childListLength:
  forall xs,
    (forall x, 
      In x xs ->
      accurateNominal x -> forall tyl,
        nominalSize x + length tyl = length (treeList x tyl)) ->
    forall tyl
Proof.
  

  Check trees.
  pose trees as t1.
  pose (t1 (fun z => accurateNominal z -> nominalSize z = length (treeList z))) as t2.
  simpl in *.
  pose (t2 (fun
  intros x.
  pattern x.
  eapply trees.
  einduction x using trees.
  simpl in *; intros; auto.
  simpl in *; intros; auto.
  




Some (p,q)
            | _ => None
          end
      
    | One 
    | One y _ ys =>
      match orderHelp f b y with
        | None => None
        | Some c => orderList f c ys
      end
  end.

Fixpoint orderHelp f b x :=
  match x with
    | Leaf y => 
      match f b y with
        | Gt => None
        | _ => Some y
      end
    | Branch m ys => orderList f b ys
  end
with orderList f b x :=
  match x with
    | Zero => Some b
    | One y _ ys =>
      match orderHelp f b y with
        | None => None
        | Some c => orderList f c ys
      end
  end.

Fixpoint markerHelp (f:A -> A -> bool) b x :=
  match x with
    | Leaf y => 
      if f b y
        then True
        else False
    | Branch m ys => markerList f b ys
  end
with markerList f b x :=
  match x with
    | Zero => False
    | One y c Zero => 
      if f b c
        then markerHelp f b y
        else False
    | One y c ys => markerHelp f c y /\ markerList f b ys
  end.

          match 
      digitsHelp n y /\ digitsRel n ys
  end.

Fixpoint digitsHelp n x :=
  match x with
    | Leaf _ => 
      match n with
        | 1 => True
        | _ => False
      end
    | Branch m ys => 
      match down m with
        | 0 => False
        | S p => 
          let q := down (DIGITS (up p))
            in 
            S q = n 
            /\
            digitsRel q ys
      end
  end
with digitsRel n x :=
  match x with
    | Zero => True
    | One y _ ys => 
      digitsHelp n y /\ digitsRel n ys
  end.

Definition balanced x :=
  match x with
    | Leaf _ => True
    | Branch m ys =>
      match down m with
        | 0 => False
        | S p =>
          digitsHelp (S (down (DIGITS (up p)))) x
      end
  end.


(*
Definition MULT n m := up (down n * down m).

Lemma plusDigit :
  forall n,
    down n > 0 ->
    down (DIGITS (MULT n BASE)) > down (DIGITS n).
Proof.
  intros.
*)  




DIGITS (n-1) = up (down (DIGITS



    | Branch _ _ (y::ys) => 1 + (trueSize y) + (sum trueSize ys)
  end.



Fixpoint div p q :=
  match nat_compare p q with
    | Lt => 0
    | _ => 1 + div (p-q) q
  end

Fixpoint natDigits n :=
  match n with
    | 0 => 0
    | _ => 

(*
Definition nominalSize x :=
  match x with
    | Leaf _ => 1
    | Branch n _ _ => down n
  end.

Fixpoint sum x :=
  match x with
    | Zero => 0
    | One y ys => trueSize y + sum ys
  end
with trueSize x :=
  match x with
    | Leaf _ => 1
    | Branch _ _ ys => 1 + sum ys
  end.

Print option.
*)


Fixpoint mapSum (f:FullTree -> nat) (x:list FullTree) : nat :=
  match x with
    | nil => 0
    | z::zs => f z + mapSum f zs
  end.

Print fold_right.

Definition fold_right2 := 
fun (A B : Type) (f : B -> A -> A) (a0 : A) =>
fix fold_rightz (l : list B) : A :=
  match l with
  | nil => a0
  | b :: t => f b (fold_rightz t)
  end.



Fixpoint treeSize x :=
  match x with
    | Leaf _ => 1
    | Branch _ ys => fold_right2 (fun z zs => zs + treeSize z) 0 ys
  end.

Print mapSum.

Definition mapSum2 (f:FullTree -> nat) :=
  fix mapSumz (x:list FullTree) : nat :=
  match x with
    | nil => 0
    | z::zs => f z + mapSumz zs
  end.

Fixpoint treeSize1 x :=
  match x with
    | Leaf _ => 1
    | Branch _ ys => fold_right (fun z zs => zs + treeSize z) 0 ys
  end.

Fixpoint treeSize2 x :=
  match x with
    | Leaf _ => 1
    | Branch _ ys => mapSum2 (fun z => treeSize z) ys
  end.

End Over.

Extraction Language Haskell.

Extraction mapSum2.
Extraction mapSum.

Print mapSum.
Print mapSum2.






Fixpoint total

Check fold_right.

Fixpoint treeSize x :=
  match x with
    | Leaf _ => 1
    | Branch _ ys => listSize ys
  end
with listSize ys :=
  match ys with
    | nil => 0
    | z :: zs => treeSize z + listSize zs
  end.
      match ys with
        | nil => 

with Children :=
  Zero : Children
| One : FullTree -> A -> Children -> Children.

Fixpoint accurateNominalHelp x :=
  match x with
    | Leaf _ => Some 1
    | Branch n ys =>
      match accurateAccum ys with
        | None => None
        | Some m =>
          if beq_nat m (down n)
            then Some m
            else None
      end
  end
with accurateAccum x :=
  match x with
    | Zero => Some 0
    | One y _ ys => 
      match accurateNominalHelp y with
        | None => None
        | Some k =>
          match accurateAccum ys with
            | None => None
            | Some j => Some (k+j)
          end
      end
  end.
*)


Definition accurateNominalHelp :=
  treeReduce
  (fun _ _ => Some 1)
  (fun n r _ =>
    match r with
      | None => None
      | Some k =>
        if beq_nat (down n) k
          then Some k
          else None
    end)
  (Some 0)
  (fun p q => 
    match p,q with
      | Some n, Some m => Some (n+m)
      | _,_ => None
    end).

Definition digitsHelp :=
  treeReduce
  (fun _ _ => Some 0)
  (fun n r _ =>
    match r with
      | None => None
      | Some m =>
        match down n with
          | 0 => None
          | S p =>
            if beq_nat (down (DIGITS (up p))) (S m)
              then Some (S m)
              else None
        end
    end)
  None
  (fun p q => 
    match p,q with
      | Some n, Some m => 
        if beq_nat n m
          then Some n
          else None
      | _,_ => None
    end).

Definition boundsHelp (comp:A->A->comparison) :=
  treeReduce
  (fun p q =>
    match comp p q with
      | Eq => Some (p,q)
      | _ => None
    end)
  (fun _ r b =>
    match r with
      | None => None
      | Some (p,q) =>
        match comp q b with
          | Eq => Some (p,b)
          | _ => None
        end
    end)
  None
  (fun a b =>
    match a,b with
      | Some (p,q), Some (r,s) =>
        match comp q r with
          | Gt => None
          | _ => Some (p,s)
        end
      | _,_ => None
    end).


(*
Definition treeReduce (S T U:Type)
  (leaf:A -> A -> T)
  (branch:NAT -> U -> A -> T)
  (zero:U)
  (one:FullTree -> A -> U)
  (more:T -> U -> U) :=
  fix help (x:FullTree) (b:A) : T :=
  match x with
    | Leaf v => leaf v b
    | Branch n c =>
      branch n (childReduce help zero one more c) b
  end.
*)
