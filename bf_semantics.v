(* -*- eval: (set-input-method "TeX"); -*- *)

Require Import bf bf_equivalence.
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

Inductive iter : (Instr.instruction * state) -> (Instr.instruction * state) -> Prop :=
| iter_idem : forall conf conf', conf ≡ conf' -> iter conf conf'
| iter_step : forall conf conf' conf'',
                step_rel conf conf' ->
                 iter conf' conf'' ->
                 iter conf conf''.


Example left_right : forall m c,  iter (< > c, m) (c, m).
Proof.
  intros.
  destruct m as [[l ls] curr rs stdin stdout].
  apply (iter_step _ (> c, (state[ ls, l, Cons curr rs, stdin, stdout ])) _).
  constructor.
  
  apply (iter_step _ (c, (state[ Cons l ls, curr, rs, stdin, stdout ])) _).
  constructor.
  
  apply iter_idem.
  bf_reflexivity.
Qed.

(* [bf_step] is basically an evaluation function / tactic. It *should*
always be able to prove a step on concrete configurations. It also
also works fairly well on abstract values. *)
Ltac bf_step :=
  simpl;
  match goal with
    | [ |- iter ?C ?C] =>
      apply iter_idem; bf_reflexivity
    | [ |- iter (< ?C, ?S) _] =>
      apply (iter_step _ (C, stepLeft S));
        [constructor|]
    | [ |- iter (> ?C, ?S) _] =>
      apply (iter_step _ (C, stepRight S));
        [constructor|]
    | [ |- iter (+ ?C, ?S) _] =>
      apply (iter_step _ (C, increment S));
        [constructor|]
    | [ |- iter (- ?C, ?S) _] =>
      apply (iter_step _ (C, decrement S));
        [constructor|]
    | [ |- iter (← ?C, ?S) _] =>
      apply (iter_step _ (C, input S));
        [constructor|]
    | [ |- iter (→ ?C, ?S) _] =>
      apply (iter_step _ (C, output S));
        [constructor|]
    | [ |- iter ([ ?b ] ?C, state[?ls, S ?n, ?rs, ?stdin, ?stdout]) _ ] =>
      apply (iter_step _ (sequence b ([ b ]C), state[ls, S n, rs, stdin, stdout]));
        [constructor|]
    | [ |- iter ([ ?b ] ?C, state[?ls, 0, ?rs, ?stdin, ?stdout]) _ ] =>
      apply (iter_step _ (C, state[ls, 0, rs, stdin, stdout]));
        [constructor|]
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

Lemma EqBf_increment :
  forall s s',
    s ≡ₛ s' -> increment s ≡ₛ increment s'.
Proof.
  intros.
  destruct s, s'.
  state_reflexivity; inversion H; auto.
Qed.

Lemma EqBf_decrement :
  forall s s',
    s ≡ₛ s' -> decrement s ≡ₛ decrement s'.
Proof.
  intros.
  destruct s as [? []]; destruct s' as [? []];
  state_reflexivity; inversion H; subst; auto; discriminate H11.
Qed.

Lemma EqBf_stepRight :
  forall s s',
    s ≡ₛ s' -> stepRight s ≡ₛ stepRight s'.
Proof.
  intros.
  destruct s as [? ? []], s' as [? ? []].
  state_reflexivity; inversion H; subst; auto using eqst; inversion H12; assumption.
Qed.

Lemma EqBf_stepLeft :
  forall s s',
    s ≡ₛ s' -> stepLeft s ≡ₛ stepLeft s'.
Proof.
  intros.
  destruct s as [[]], s' as [[]].
  state_reflexivity; inversion H; auto using eqst; subst;
  inversion H6; assumption.
Qed.

Lemma EqBf_input :
  forall s s',
    s ≡ₛ s' -> input s ≡ₛ input s'.
Proof.
  intros.
  destruct s as [? ? ? []], s' as [? ? ? []].
  state_reflexivity; inversion H; auto; inversion H13; auto.
Qed.

Lemma EqBf_output :
  forall s s',
    s ≡ₛ s' -> output s ≡ₛ output s'.
Proof.
  intros.
  destruct s, s'.
  destruct H.
  state_reflexivity; subst; auto.
Qed.

Lemma step_EqBf_compat :
  forall conf conf' conf'' conf''',
    step conf = Some conf' ->
    step conf'' = Some conf''' ->
    conf ≡ conf'' ->
    conf' ≡ conf'''.
Proof.
  (* HERE BE DRAGONS! *)
  intros ? ? ? ? H H' ?.
  destruct conf as [[]]; try discriminate H;
  injection H; intros;
  destruct conf'' as [[]];
  try discriminate H';
  injection H'; intros;
  subst;
  inversion H0; (injection H4 || discriminate H4); intros; subst;
  try bf_reflexivity;
  auto using EqBf_increment, EqBf_decrement, EqBf_stepRight,
  EqBf_stepLeft, EqBf_input, EqBf_output.
  inversion H6; subst; destruct curr'; simpl;
  bf_reflexivity; assumption.
Qed.

Lemma step_rel_EqBf_compat :
  forall c c' c'' c''',
    step_rel c c' ->
    step_rel c'' c''' ->
    c ≡ c'' ->
    c' ≡ c'''.
Proof.
  intros c c' c'' c''' H H'.
  apply step_step_rel in H.
  apply step_step_rel in H'.
  apply step_EqBf_compat; assumption.
Qed.

Lemma step_square_lemma :
  forall c c' c'',
    step_rel c c' ->
    c ≡ c'' ->
    exists c''',
      step_rel c'' c'''.
Proof.
  (* MORE DRAGONS AHEAD! *)
  intros c c' c'' H.
  apply step_step_rel in H.
  destruct c as [[]];
    try (destruct (step_Some END s);
         destruct H0;
         [ exists c'; assumption
                | reflexivity ]);
    try (intro H';
    inversion H'; subst;
    destruct s as [? []], s' as [? []];
    match goal with
        [ H : (_, _) ≡ ?c |- ?P ] =>
        remember (step c) as my_c;
        move Heqmy_c after H;
        simpl in Heqmy_c;
        match goal with
            [ Heqmy_c : my_c = Some ?c |- ?P ] =>
            exists c
        end
    end;
    constructor).
Qed.

Lemma iter_injective :
  forall c c' c'',
    iter c c' ->
    c' ≡ c'' ->
    iter c c''.
Proof.
  intros c1 c2 c3 H H'.
  induction H.
  eauto using iter_idem, EqBf_trans.

  apply IHiter in H'.
  apply (iter_step _ conf'); assumption.
Qed.

Lemma extend_iter_right :
  forall c c' c'',
    iter c c' ->
    step_rel c' c'' ->
    iter c c''.
Proof.
  intros c c' c'' H.
  induction H.
  intro H'.

  destruct (step_square_lemma conf' c'' conf H' (EqBf_sym H)).
  apply EqBf_sym in H.
  apply (step_rel_EqBf_compat conf' c'' conf x) in H; try assumption.
  apply (iter_step _ _ _ H0).
  apply iter_idem.
  apply EqBf_sym.
  assumption.

  intro H'.
  apply (iter_step _ _ _ H).
  apply IHiter.
  assumption.
Qed.

Lemma iter_trans :
  forall conf conf' conf'',
    iter conf conf' ->
    iter conf' conf'' ->
    iter conf conf''.
Proof.
  intros c c' c'' H H'.
  induction H'.

  exact (iter_injective _ conf _ H H0).

  exact (IHH' (extend_iter_right c conf conf' H H0)).
Qed.
