Require Import bf_stack bf.

Inductive ae : Set :=
| Int : nat -> ae
| Plus : ae -> ae -> ae
| Minus : ae -> ae -> ae
| Mult : ae -> ae -> ae.

Fixpoint interpret ae : nat :=
  match ae with
    | Int n => n
    | Plus e1 e2 => interpret e1 + interpret e2
    | Minus e1 e2 => interpret e1 - interpret e2
    | Mult e1 e2 => interpret e1 * interpret e2
  end.

Fixpoint compile (ae : ae) : Instr.instruction :=
  match ae with
    | Int n => push n
    | Plus e1 e2 => compile e1; compile e2; add
    | Minus e1 e2 => compile e1; compile e2; sub
    | Mult e1 e2 => compile e1; compile e2; mult
  end.

(* TODO: Correctness proof *)
