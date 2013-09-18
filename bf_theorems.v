(* -*- eval: (set-input-method "TeX"); -*- *)

Require Import bf.
Require Import Lists.Streams.
Require Import Arith.Minus.

Definition option_bind {A B : Set} (f : A -> option B) (x : option A) : option B :=
  match x with
    | None => None
    | Some a => f a
  end.

Lemma step_None : forall c m,
                    step (c, m) = None <->
                    c = END.
Proof.
  intros c m.
  split.
  intro H; destruct c; simpl in H; try discriminate H.
  reflexivity.

  intros; subst; reflexivity.
Qed.

Lemma step_Some : forall c m,
                  (exists config, step (c, m) = Some config) <->
                  c <> END.
Proof.
  intros c m.
  split.
  intro H.
  destruct H.
  destruct c; try (intro H'; discriminate H').
  intro H'.
  apply (proj2 (step_None END m)) in H'.
  rewrite H' in H.
  discriminate H.

  intro H.
  destruct c; simpl.

  exists (c, increment m); reflexivity.
  exists (c, decrement m); reflexivity.
  exists (c, stepRight m); reflexivity.
  exists (c, stepLeft m); reflexivity.
  exists (c, input m); reflexivity.
  exists (c, output m); reflexivity.
  exists (if isZero m
          then (c2, m)
          else ((sequence c1 ([c1]c2)), m)); reflexivity.
  destruct H; reflexivity.
Qed.

(* [EqState] is an equivalence relation between machine states. The
key difference from [_ = _] is that the [Stream] components of the two
[state]s are compared with [EqSt] (i.e. extensional equality). *)
Inductive EqState : state -> state -> Prop :=
| eqstate :
    forall ls curr rs stdin stdout ls' curr' rs' stdin' stdout',
      EqSt ls ls' ->
      curr = curr' ->
      EqSt rs rs' ->
      EqSt stdin stdin' ->
      stdout = stdout' ->
      EqState state[ls, curr, rs, stdin, stdout]
              state[ls', curr', rs', stdin', stdout'].

(* [state_reflexivity] can automatically solve the most trivial goals
of the form [EqState _ _], and will give suitable subgoals
otherwise. *)
Ltac state_reflexivity :=
  simpl;
  match goal with
    | [ |- EqState state[?ls, ?curr, ?rs, ?stdin, ?stdout]
                   state[?ls', ?curr', ?rs', ?stdin', ?stdout'] ] =>
      apply eqstate; [
          try apply EqSt_reflex |
          try reflexivity |
          try apply EqSt_reflex |
          try apply EqSt_reflex |
          try reflexivity ]
  end.

Notation "s ≡ₛ s'" := (EqState s s') (at level 70, no associativity) : stateeq_scope.
Open Scope stateeq_scope.

Lemma EqState_refl : forall s, s ≡ₛ s.
Proof.
  intro s; destruct s; state_reflexivity.
Qed.

Lemma EqState_trans : forall s s' s'',
                        s ≡ₛ s' ->
                        s' ≡ₛ s'' ->
                        s ≡ₛ s''.
Proof.
  intros s s' s'' H H'.
  destruct s as [ls curr rs stdin stdout];
    destruct s' as [ls' curr' rs' stdin' stdout'];
    destruct s'' as [ls'' curr'' rs'' stdin'' stdout''].
  inversion H; inversion H'; subst.
  state_reflexivity.
  apply (@trans_EqSt _ ls ls' ls''); assumption.
  apply (@trans_EqSt _ rs rs' rs''); assumption.
  apply (@trans_EqSt _ stdin stdin' stdin''); assumption.
Qed.       

Lemma EqState_sym : forall s s',
                      s ≡ₛ s' ->
                      s' ≡ₛ s.
Proof.
  intros.
  inversion H; subst.
  state_reflexivity; apply sym_EqSt; assumption.
Qed.

(* [EqBf] is an equivalence relation between configurations. It
requires the programs to be equal and the states to be equivalent
w.r.t. [EqState]. *)
Inductive EqBf :
  Instr.instruction * state -> Instr.instruction * state -> Prop :=
| eqbf :
    forall c s c' s',
      c = c' ->
      EqState s s' ->
      EqBf (c, s) (c', s').

Ltac bf_reflexivity :=
  simpl;
  match goal with
    | [ |- EqBf (?c, ?s) (?c', ?s') ] =>
      apply eqbf; [
          try reflexivity |
          try state_reflexivity ]
  end.

Notation "c ≡ c'" := (EqBf c c') (at level 70, no associativity) : bfeq_scope.
Open Scope bfeq_scope.

Lemma EqBf_refl : forall config, config ≡ config.
Proof.
  intro config; destruct config; bf_reflexivity; apply EqState_refl.
Qed.

Lemma EqBf_trans : forall config config' config'',
                     config ≡ config' ->
                     config' ≡ config'' ->
                     config ≡ config''.
Proof.
  intros conf conf' conf'' H H'.
  destruct conf as [c s];
    destruct conf' as [c' s'];
    destruct conf'' as [c'' s''].
  inversion H; subst; inversion H'; subst.
  bf_reflexivity.
  Check EqState_trans.
  apply (EqState_trans s s' s''); assumption.
Qed.  

Lemma EqBf_sym : forall config config',
                   config ≡ config' ->
                   config' ≡ config.
Proof.
  intros conf conf' H.
  inversion H; subst.
  bf_reflexivity.
  apply EqState_sym; assumption.
Qed.
  
Fixpoint n_unfolded_zeroes (n : nat) : Stream nat :=
  match n with
    | 0 => zeroes
    | S n => Cons 0 (n_unfolded_zeroes n)
  end.

Lemma about_zeroes : forall n,
                       init (n_unfolded_zeroes n) ≡ₛ init zeroes.
Proof.
  induction n.
  unfold init.
  state_reflexivity.
  
  unfold init.
  state_reflexivity.
  apply eqst.
  reflexivity.
  simpl.
  inversion IHn; subst; assumption.
Qed.

Lemma about_zeroes' : forall n c,
                        (c, init (n_unfolded_zeroes n)) ≡ (c, init zeroes).
Proof.
  intros.
  bf_reflexivity.
  apply about_zeroes.
Qed.

Lemma very_simple_equivalence : forall c,
                                  (c, init zeroes) ≡ (c, init zeroes).
Proof.
  intros.
  unfold init.
  bf_reflexivity.
Qed.

Inductive iter : (Instr.instruction * state) -> (Instr.instruction * state) -> Prop :=
| iter_idem : forall conf, iter conf conf
| iter_step : forall conf conf' conf'',
                 match step conf with
                   | Some conf''' => conf''' ≡ conf'
                   | None => False
                 end ->
                 iter conf' conf'' ->
                 iter conf conf''.

Open Scope state_scope.

Example left_right : forall m c,  iter (< > c, m) (c, m).
Proof.
  intros.
  destruct m as [[l ls] curr rs stdin stdout].
  apply (iter_step _ (> c, (state[ ls, l, Cons curr rs, stdin, stdout ])) _).
  bf_reflexivity.
  
  apply (iter_step _ (c, (state[ Cons l ls, curr, rs, stdin, stdout ])) _).
  bf_reflexivity.
  
  apply iter_idem.
Qed.

(* [bf_step] is basically an evaluation function / tactic. It *should*
always be able to prove a step on concrete configurations. It also
also works fairly well on abstract values. *)
Ltac bf_step :=
  simpl;
  match goal with
    | [ |- iter ?C ?C] =>
      apply iter_idem
    | [ |- iter (< ?C, state[?ls, ?curr, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[tl ls, hd ls, Cons curr rs, stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter (> ?C, state[?ls, ?curr, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[Cons curr ls, hd rs, tl rs, stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter (+ ?C, state[?ls, ?curr, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[ls, S curr, rs, stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter (- ?C, state[?ls, 0, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[ls, 0, rs, stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter (- ?C, state[?ls, S ?curr, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[ls, curr, rs, stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter (← ?C, state[?ls, _, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[ls, hd stdin, rs, tl stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter (→ ?C, state[?ls, ?curr, ?rs, ?stdin, ?stdout]) _] =>
      apply (iter_step _ (C, state[ls, curr, rs, stdin, curr :: stdout]));
        [bf_reflexivity|]
    | [ |- iter ([ ?b ] ?C, state[?ls, S ?n, ?rs, ?stdin, ?stdout]) _ ] =>
      apply (iter_step _ (sequence b ([ b ]C), state[ls, S n, rs, stdin, stdout]));
        [bf_reflexivity|]
    | [ |- iter ([ ?b ] ?C, state[?ls, 0, ?rs, ?stdin, ?stdout]) _ ] =>
      apply (iter_step _ (C, state[ls, 0, rs, stdin, stdout]));
        [bf_reflexivity|]
  end.

Ltac bf_destruct :=
  simpl;
  match goal with
    | [ |- iter (< ?C, ?M) _] =>
      destruct M as [[?l ?ls] ?curr ?rs ?stdin ?stdout]
    | [ |- iter (> ?C, ?M) _] =>
      destruct M as [?ls ?curr [?r ?rs] ?stdin ?stdout]
    | [ |- iter (+ ?C, ?M) _] =>
      destruct M as [?ls ?curr ?rs ?stdin ?stdout]
  end.

(* The following is a series of proofs whose purpose is mainly to test
the various tactics. *)
Module BF_Automation_Tests.
Example left_right' : forall m c,  iter (< > c, m) (c, m).
Proof.
  intros.
  bf_destruct.
  repeat bf_step.
Qed.

Example plus_minus : forall m c, iter (+ - c, m) (c, m).
Proof.
  intros.
  bf_destruct.
  repeat bf_step.
Qed.

Example minus_minus : forall ls n rs stdin stdout c,
                        iter (- c, state[ls, n, rs, stdin, stdout])
                             (c, state[ls, minus n 1, rs, stdin, stdout]).
Proof.
  intros.
  destruct n; repeat bf_step.
  rewrite <- minus_n_O.
  bf_step.
Qed.

Example input : forall ls n rs input stdin stdout c,
                  iter (← c, state[ls, n, rs, Cons input stdin, stdout])
                       (c, state[ls, input, rs, stdin, stdout]).
Proof.
  intros.
  repeat bf_step.
Qed.

Example input' : forall ls n rs stdin stdout c,
                   iter (← c, state[ls, n, rs, stdin, stdout])
                        (c, state[ls, hd stdin, rs, tl stdin, stdout]).
Proof.
  intros.
  destruct stdin as [input stdin].
  repeat bf_step.
Qed.

Example output : forall ls n rs stdin stdout c,
                   iter (→ c, state[ls, n, rs, stdin, stdout])
                        (c, state[ls, n, rs, stdin, n :: stdout]).
Proof.
  intros.
  repeat bf_step.
Qed.

Example loop : forall ls rs stdin stdout c,
                 iter ([-END] c, state[ls, 5, rs, stdin, stdout])
                      (c, state[ls, 0, rs, stdin, stdout]).
Proof.
  intros.
  repeat bf_step.
Qed.

Example nonloop : forall ls rs stdin stdout b c,
                    iter ([b]c, state[ls, 0, rs, stdin, stdout])
                         (c, state[ls, 0, rs, stdin, stdout]).
Proof.
  intros.
  repeat bf_step.
Qed.

Example non_termination : forall ls rs stdin stdout c,
                           iter ([END]c, state[ls, 1, rs, stdin, stdout])
                                (c, state[ls, 1, rs, stdin, stdout]).
Proof.
  intros.
  (* For some reason this does terminate (although it doesn't really
  change the goal *)

  repeat bf_step.
  (* Apparently [repeat] checks whether there's any progress *)
Abort.

Definition hello_world := 
  + + + + + + + + + + [ > + + + + + + + > + + + + + + + + + + > + + +
  > + < < < < - END ] > + + → > + → + + + + + + + → → + + + → > + + →
  < < + + + + + + + + + + + + + + + → > → + + + → - - - - - - → - - -
  - - - - - → > + → > → END.

Open Scope list_scope. (* wut *)
Definition hello_world_string := 10 :: 33::100::108::114::111::87::32::111::108::108::101::72::nil.

Example hello_world_works :
  exists ls n rs,
  iter (hello_world, state[zeroes, 0, zeroes, zeroes, nil])
       (END, state[
                 ls,
                 n,
                 rs,
                 zeroes,
                 hello_world_string]).
Proof.
  (* Unfortunately, we have to guess the state of the resulting cells *)
  exists (Cons 33 (Cons 100 (Cons 87 (Cons 0 zeroes)))).
  exists 10.
  exists zeroes.
  unfold  hello_world.
  unfold init.
  unfold n_unfolded_zeroes.
  unfold hello_world_string.
  repeat bf_step.
Qed.

Theorem reset_current_cell : forall ls curr rs stdin stdout c,
                               iter ([-END]c, state[ls, curr, rs, stdin, stdout])
                                    (c, state[ls, 0, rs, stdin, stdout]).
Proof.
  intros.
  induction curr.
  repeat bf_step.

  repeat bf_step.
  exact IHcurr.
Qed.

End BF_Automation_Tests.
