(* -*- eval: (set-input-method "TeX"); -*- *)

Require Import bf bf_equivalence bf_semantics.
Require Import Lists.Streams.
Require Import Arith.Minus Arith.Plus.

Definition option_bind {A B : Set} (f : A -> option B) (x : option A) : option B :=
  match x with
    | None => None
    | Some a => f a
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

Example loop' : forall b,
  (forall ls curr rs stdin stdout c,
     iter (b;c, state[ls, curr, rs, stdin, stdout])
          (c, state[ls, 0, rs, stdin, stdout])) ->
  (forall ls curr rs stdin stdout c,
     iter ([b] c, state[ls, curr, rs, stdin, stdout])
          (c, state[ls, 0, rs, stdin, stdout])).
Proof.
  intros b.
  intros.
  destruct curr.
  bf_step.
  bf_step.

  bf_step.
  apply (iter_trans _ ([b]c, state[ls, 0, rs, stdin, stdout])).
  apply H.
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

Definition hello_world_string := (10 :: 33::100::108::114::111::87::32::111::108::108::101::72::nil)%list.

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
  unfold hello_world_string.
  repeat bf_step.
Qed.

Lemma double_cell' : forall ls x y rs stdin stdout c,
                        iter ([- > + + <END]c, state[ls, x, Cons y rs, stdin, stdout])
                             (c, state[ls, 0, Cons (2*x + y) rs, stdin, stdout]).
Proof.
  intros ls x.
  induction x.
  intros.
  repeat bf_step.

  intros.
  repeat bf_step.
  simpl.
  assert (S (x + S (x + 0) + y) = (2 * x) + S (S y)) as Hdouble.
  rewrite <- plus_n_O.
  rewrite <- plus_n_Sm.
  rewrite plus_comm.
  rewrite <- plus_Sn_m.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  rewrite plus_comm.
  assert (x+x = 2 * x).
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
  rewrite H.
  reflexivity.
  rewrite Hdouble.
  apply IHx.
Qed.

Theorem double_cell ls x :
  forall rs stdin stdout c,
    iter ([- > + + <END]c, state[ls, x, Cons 0 rs, stdin, stdout])
         (c, state[ls, 0, Cons (2*x) rs, stdin, stdout]).
Proof.
  pose (double_cell' ls x 0) as H.
  rewrite <- plus_n_O in H.
  exact H.
Qed.

End BF_Automation_Tests.
