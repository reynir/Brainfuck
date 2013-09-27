Require Import bf_stack bf bf_semantics.
Require Import Lists.Streams.

Inductive ae : Set :=
| Int : nat -> ae
| Plus : ae -> ae -> ae
| Minus : ae -> ae -> ae
| Mult : ae -> ae -> ae.

Coercion Int : nat >-> ae.
Notation "a + b" := (Plus a b) : ae_scope.
Notation "a - b" := (Minus a b) : ae_scope.
Notation "a * b" := (Mult a b) : ae_scope.

Open Scope ae_scope.

Fixpoint interpret (ae : ae) : nat :=
  match ae with
    | Int n => n
    | Plus e1 e2 => (interpret e1 + interpret e2)%nat
    | Minus e1 e2 => (interpret e1 - interpret e2)%nat
    | Mult e1 e2 => (interpret e1 * interpret e2)%nat
  end.

Fixpoint compile (ae : ae) : Instr.instruction :=
  match ae with
    | Int n => push n
    | Plus e1 e2 => compile e1; compile e2; add
    | Minus e1 e2 => compile e1; compile e2; sub
    | Mult e1 e2 => compile e1; compile e2; mult
  end.

Example interpret_compile_example1 :
  iter (compile (4+5-2*3), init zeroes)
       (END, state[zeroes, interpret (4+5-2*3), zeroes, zeroes, nil]).
Proof.
  unfold init, compile, interpret.
  repeat bf_step.
  unfold sub.
  repeat bf_step.
Qed.

Theorem compiler_correctness :
  forall ae ls x,
    iter (compile ae, state[ls, x, zeroes, zeroes, nil])
         (END, state[Cons x ls, interpret ae, zeroes, zeroes, nil]).
Proof.
  intro ae.
  induction ae.
  simpl.
  intros.
  apply (iter_trans _
                    (END, state[Cons x ls, n, zeroes, zeroes, nil])).
  apply (about_push n ls x zeroes nil).
  bf_step.  

  intros.
  simpl.
  apply (about_sequence (compile ae1) (compile ae2; add)
                        _ state[Cons x ls, interpret ae1, zeroes, zeroes, nil]).
  apply IHae1.  
  apply (about_sequence (compile ae2) (add)
                        _ state[Cons (interpret ae1) (Cons x ls),
                                interpret ae2, zeroes, zeroes, nil]).
  apply IHae2.
  rewrite Arith.Plus.plus_comm.
  apply about_add.

  intros.
  simpl.
  apply (about_sequence (compile ae1) (compile ae2; sub)
                        _ state[Cons x ls, interpret ae1, zeroes, zeroes, nil]).
  apply IHae1.
  apply (about_sequence (compile ae2) sub
                        _ state[Cons (interpret ae1) (Cons x ls),
                                interpret ae2, zeroes, zeroes, nil]).
  apply IHae2.
  apply about_sub.

  intros.
  simpl.
  apply (about_sequence (compile ae1) (compile ae2; mult)
                        _ state[Cons x ls, interpret ae1, zeroes, zeroes, nil]).
  apply IHae1.
  apply (about_sequence (compile ae2) mult
                        _ state[Cons (interpret ae1) (Cons x ls),
                                interpret ae2, zeroes, zeroes, nil]).
  apply IHae2.
  apply about_mult.
Qed.
