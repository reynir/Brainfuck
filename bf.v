Require Import Lists.Streams.

(**** A brainfuck variant ****
 
This variant has an infinite number of cells. The cells are unbounded
in both direction. The cells hold unbounded natural numbers (i.e. 0,
1, 2, ...).

The instructions are the usual. Note: "+" will not overflow and "-",
when the current cell hold 0, will put a 0.

*)



Inductive state : Set :=
| configuration : Stream nat -> nat -> Stream nat -> Stream nat -> list nat -> state.

Notation "'state[' left , current , right , stdin , stdout ]" := (configuration left current right stdin stdout) : state_scope.

Open Scope state_scope.

CoFixpoint zeroes : Stream nat :=
  Cons 0 zeroes.

Definition init (stdin : Stream nat) : state :=
  state[ zeroes, 0, zeroes, stdin, nil ].

Definition increment m :=
  match m with
    | state[ ls, curr, rs, stdin, stdout ] =>
      state[ ls, S curr, rs, stdin, stdout ]
  end.

Definition decrement m :=
  match m with
    | state[ ls, S curr, rs, stdin, stdout ] =>
      state[ ls, curr, rs, stdin, stdout ]
    | state[ ls, 0, rs, stdin, stdout ] =>
      state[ ls, 0, rs, stdin, stdout ]
  end.

Definition stepLeft m :=
  match m with
      | state[ Cons l ls, curr, rs, stdin, stdout ] =>
        state[ ls, l, Cons curr rs, stdin, stdout ]
  end.

Definition stepRight m :=
  match m with
    | state[ ls, curr, Cons r rs, stdin, stdout ] =>
      state[ Cons curr ls, r, rs, stdin, stdout ]
  end.

Definition output m :=
  match m with
    | state[ ls, curr, rs, stdin, stdout ] =>
      state[ ls, curr, rs, stdin, curr :: stdout ]
  end.

Definition input m :=
  match m with
    | state[ ls, curr, rs, Cons input stdin, stdout ] =>
      state[ ls, input, rs, stdin, stdout ]
  end.

Definition isZero m :=
  match m with
    | state[ _, 0, _, _, _ ] => true
    | _ => false
  end.

Module Instr.

Inductive instruction : Set :=
| add : instruction -> instruction
| subtract : instruction -> instruction
| stepRight : instruction -> instruction
| stepLeft : instruction -> instruction
| input : instruction -> instruction
| output : instruction -> instruction
| loop : instruction -> instruction -> instruction
| EOF : instruction.

End Instr.

(* A notation that is close to the original syntax. Note that spaces
may be needed and that the body of a loop must end with END. *)

Notation "+ x" := (Instr.add x) (at level 35, right associativity) : bf_scope.
Notation "- x" := (Instr.subtract x) (at level 35, right associativity) : bf_scope.
Notation "> x" := (Instr.stepRight x) (at level 35, right associativity) : bf_scope.
Notation "< x" := (Instr.stepLeft x) (at level 35, right associativity) : bf_scope.
Notation "'i' x" := (Instr.input x) (at level 35, right associativity) : bf_scope.
Notation "'o' x" := (Instr.output x) (at level 35, right associativity) : bf_scope.
Notation "[ b ] x" := (Instr.loop b x) (at level 35, right associativity) : bf_scope.
Notation "'END'" := Instr.EOF : bf_scope.

Open Scope bf_scope.

Unset Printing Notations.
Compute i [ > + + < - END] o END.
Compute [[+END]END]END.
Set Printing Notations.

Fixpoint sequence (c c' : Instr.instruction) : Instr.instruction :=
  match c with
    | + c => + (sequence c c')
    | - c => - (sequence c c')
    | > c => > (sequence c c')
    | < c => < (sequence c c')
    | i c => i (sequence c c')
    | o c => o (sequence c c')
    | [ b ] c => [ b ] (sequence c c')
    | END => c'
  end.

Fixpoint step (config : Instr.instruction * state) : option (Instr.instruction * state) :=
  match config with
    | (+ c, m) => Some (c, increment m)
    | (- c, m) => Some (c, decrement m)
    | (> c, m) => Some (c, stepRight m)
    | (< c, m) => Some (c, stepLeft m)
    | (i c, m) => Some (c, input m)
    | (o c, m) => Some (c, output m)
    | ([ b ] c, m) =>
      Some (if isZero m
           then (c, m)
           else (sequence b ([ b ] c), m))
    | (END, m) => None
  end.

Compute step (i [ > + < - END] o END, init zeroes).
Compute step ([+END]END, init zeroes).
Compute step ([+END]END, increment (init zeroes)).
Compute option_map step (step ([+END]END, increment (init zeroes))).

CoInductive Trace : Set :=
| Step : state -> Trace -> Trace
| Stop : state -> Trace.

CoFixpoint run (configuration : Instr.instruction * state) : Trace :=
  match step configuration with
    | None => Stop (snd configuration)
    | Some configuration' =>
      Step (snd configuration) (run configuration')
  end.

Definition interpret (c : Instr.instruction) (stdin : Stream nat) :=
  run (c, init stdin).
