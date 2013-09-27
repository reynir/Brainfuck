Require Import bf_stack bf bf_semantics.

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

(* TODO: Correctness proof *)
