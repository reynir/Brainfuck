Require Import bf bf_equivalence bf_semantics.
Require Import Lists.Streams.
Require Import Setoid.
Require Import Arith.Minus.

Fixpoint add_n (n : nat) :=
  match n with
    | 0 => END
    | S n => + (add_n n)
  end.

Lemma about_add_n (n : nat) :
  forall ls x rs stdin stdout,
    iter (add_n n, state[ls, x, rs, stdin, stdout])
         (END, state[ls, n+x, rs, stdin, stdout]).
Proof.
  induction n.
  intros.
  bf_step.

  intros.
  bf_step.
  simpl.
  rewrite plus_n_Sm.
  apply IHn.
Qed.

Definition push (n: nat) := > add_n n.

Theorem about_push (n: nat) :
  forall ls x stdin stdout,
    iter (push n, state[ls, x, zeroes, stdin, stdout])
         (END, state[Cons x ls, n, zeroes, stdin, stdout]).
Proof.
  unfold push.
  intros.
  bf_step.
  simpl stepRight.
  rewrite (plus_n_O n) at 2.
  apply about_add_n.
Qed.

Definition add := [- < + >END]<END.

Theorem about_add :
  forall ls y x stdin stdout,
    iter (add, state[Cons x ls, y, zeroes, stdin, stdout])
         (END, state[ls, y+x, zeroes, stdin, stdout]).
Proof.
  unfold add.
  intros ls y.
  induction y.
  intros.
  repeat bf_step.
  apply iter_idem.
  bf_reflexivity.
  auto using eqst, EqSt_reflex.

  intros.
  do 5 bf_step.
  rewrite (plus_n_Sm).
  apply IHy.
Qed.

Definition sub := [- < - >END]<END.

Theorem about_sub :
  forall ls x y stdin stdout,
    iter (sub, state[Cons y ls, x, zeroes, stdin, stdout])
         (END, state[ls, y - x, zeroes, stdin, stdout]).
Proof.
  unfold sub.
  intros ls x.
  induction x.
  intros.
  repeat bf_step.
  apply iter_idem.
  bf_reflexivity.
  apply minus_n_O.
  auto using EqSt_reflex, eqst.

  intros.
  do 4 bf_step.
  replace (decrement state[ls, y, Cons x zeroes, stdin, stdout])
  with state[ls, y - 1, Cons x zeroes, stdin, stdout]
    by (destruct y;
        [ reflexivity
        | simpl; rewrite <- minus_n_O; reflexivity ]).
  bf_step.
  replace (y - S x)
  with ((y - 1) - x)
    by (destruct y; [ reflexivity
                   | simpl; rewrite <- minus_n_O; reflexivity ]).
  apply IHx.
Qed.

Definition dup := [> + > + < < -END] (* Add top of stack to the two next cells *)
                  > > (* Move to the result *)
                  [< < + > > -END]<END (* Copy result to top of stack *)
.

Lemma about_dup_lemma1 :
  forall ls x y stdin stdout c,
    iter ([> + > + < < -END]c, state[ls, x, Cons y (Cons y zeroes), stdin, stdout])
         (c, state[ls, 0, Cons (x+y) (Cons (x+y) zeroes), stdin, stdout]).
Proof.
  intros ls x.
  induction x.
  intros.
  bf_step.
  apply iter_idem.
  bf_reflexivity.
  auto using eqst, EqSt_reflex.

  intros.
  do 8 bf_step.
  simpl.
  rewrite plus_n_Sm.
  apply IHx.
Qed.

Lemma about_dup_lemma2 :
  forall ls x y z stdin stdout c,
    iter
      ([< < + > > - END]c,
       state[Cons y (Cons z ls), x, zeroes, stdin, stdout])
      (c, state[Cons y (Cons (x+z) ls), 0, zeroes, stdin, stdout]).
Proof.
  intros ls x.
  induction x.
  intros.
  bf_step.
  apply iter_idem.
  bf_reflexivity.
  
  intros.
  do 7 bf_step.
  simpl.
  rewrite plus_n_Sm.
  apply IHx.
Qed.

Theorem about_dup :
  forall ls x stdin stdout,
    iter (dup, state[ls, x, zeroes, stdin, stdout])
         (END, state[Cons x ls, x, zeroes, stdin, stdout]).
Proof.
  unfold dup.
  intros.
  apply (iter_trans _ (> > [< < + > > -END]<END,
                       state[ls, 0, Cons x (Cons x zeroes), stdin, stdout])).
  rewrite plus_n_O at 2.
  rewrite plus_n_O at 3.
  apply (iter_trans _ ([> + > + < < - END] > > [< < + > > -END]<END,
                       state[ls, x, Cons 0 (Cons 0 zeroes), stdin, stdout])).
  apply iter_idem.
  bf_reflexivity.
  auto using eqst, EqSt_reflex.

  apply about_dup_lemma1.
  
  do 2 bf_step.
  rewrite (plus_n_O x) at 4.
  simpl.
  apply (iter_trans _ (< END,
                       state[Cons x (Cons (x+0) ls), 0, zeroes, stdin, stdout])).
  apply about_dup_lemma2.
  
  repeat bf_step.
  simpl.
  rewrite <- plus_n_O.
  apply iter_idem.
  bf_reflexivity.
  auto using eqst, EqSt_reflex.
Qed.

Definition reset := [-END]END.

Theorem about_reset : forall ls curr rs stdin stdout,
                               iter (reset, state[ls, curr, rs, stdin, stdout])
                                    (END, state[ls, 0, rs, stdin, stdout]).
Proof.
  unfold reset.
  intros.
  induction curr.
  repeat bf_step.

  repeat bf_step.
  exact IHcurr.
Qed.

Definition mult :=
  (* [...;x1][x2][] Move x1 *)
  <[> > + < < -END]> >
  (* [...;0;x2][x1][] *)
  [<
   (* [...;i*x2][x2][x1-i] Add and copy x2 *)
   [< + > > > + < < -END]
   (* [...;(i+1)*x2][0][x1-i;x2] Move to x2 *)
   > >
   (* [...;(i+1)*x2;0;x1-i][x2][] Move back x2 *)
   [< < + > > -END]<
   (* [...;(i+1)*x2;x2][x1-i][] Decrement loop counter *)
   -END
  (* [...;(i+1)*x2;x2][x1-(i+1)][] *)
  ]<
  (* [...;x1*x2][x2][] Cleanup *)
  reset;
  <
  (* [...][x1*x2][] *)
  END.

Example mult_example1 :
  forall stdin stdout,
    iter (mult, state[Cons 2 zeroes, 3, zeroes, stdin, stdout])
         (END, state[zeroes, 6, zeroes, stdin, stdout]).
Proof.
  unfold mult.
  intros.
  repeat bf_step; simpl.
  apply iter_idem.
  bf_reflexivity; auto using eqst, EqSt_reflex.
Qed.

Example mult_example2 :
  forall stdin stdout,
    iter (mult, state[Cons 0 zeroes, 3, zeroes, stdin, stdout])
         (END, state[zeroes, 0, zeroes, stdin, stdout]).
Proof.
  unfold mult.
  intros.
  repeat bf_step; simpl.
  apply iter_idem.
  bf_reflexivity; auto using eqst, EqSt_reflex.
Qed.

Example mult_example3 :
  forall stdin stdout,
    iter (mult, state[Cons 2 zeroes, 0, zeroes, stdin, stdout])
         (END, state[zeroes, 0, zeroes, stdin, stdout]).
Proof.
  unfold mult.
  intros.
  repeat bf_step; simpl.
  apply iter_idem.
  bf_reflexivity; auto using eqst, EqSt_reflex.
Qed.
