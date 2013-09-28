(* -*- eval: (set-input-method "TeX"); -*- *)

Require Import bf.
Require Import Lists.Streams.

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
  apply step_step_rel in H.
  inversion H; intro Heq; discriminate Heq.
  
  intro H.
  destruct c; simpl; eauto.
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
      apply eqstate; auto using EqSt_reflex, eqst
  end.

Notation "s ≡ₛ s'" := (EqState s s') (at level 70, no associativity) : stateeq_scope.
Delimit Scope stateeq_scope with stateeq.
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

Lemma EqState_sym {s s' : state} :
                      s ≡ₛ s' ->
                      s' ≡ₛ s.
Proof.
  intro H.
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
Delimit Scope bfeq_scope with bfeq.
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
  apply (EqState_trans s s' s''); assumption.
Qed.  

Lemma EqBf_sym {conf conf'} :
                   conf ≡ conf' ->
                   conf' ≡ conf.
Proof.
  intros H.
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
  apply EqState_refl.

  unfold init.
  state_reflexivity.
  apply eqst.
  reflexivity.
  inversion IHn; assumption.
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

Lemma EqBf_program :
  forall c s c' s',
    (c, s) ≡ (c', s') ->
    c = c'.
Proof.
  intros.
  inversion H; assumption.
Qed.
