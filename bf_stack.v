Require Import bf bf_equivalence bf_semantics.
Require Import Lists.Streams.
Require Import Setoid.
Require Import Arith.

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
  rewrite <- minus_n_O.
  bf_step.

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
  repeat bf_step.

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
  repeat bf_step.
  
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
  bf_step.

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
  bf_step.
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
  repeat bf_step.
Qed.

Example mult_example2 :
  forall stdin stdout,
    iter (mult, state[Cons 0 zeroes, 3, zeroes, stdin, stdout])
         (END, state[zeroes, 0, zeroes, stdin, stdout]).
Proof.
  unfold mult.
  intros.
  repeat bf_step.
Qed.

Example mult_example3 :
  forall stdin stdout,
    iter (mult, state[Cons 2 zeroes, 0, zeroes, stdin, stdout])
         (END, state[zeroes, 0, zeroes, stdin, stdout]).
Proof.
  unfold mult.
  intros.
  repeat bf_step.
Qed.

Theorem about_mult :
  forall ls x1 x2 stdin stdout,
    iter (mult, state[Cons x1 ls, x2, zeroes, stdin, stdout])
         (END, state[ls, x1 * x2, zeroes, stdin, stdout]).
Proof.
  unfold mult, reset.
  intros.
  repeat bf_step; simpl.
  generalize dependent x1; generalize dependent x2.
  assert
    (forall x1 x2 k c,
       iter ([> > + < < -END]c, state[ls, x1, Cons x2 (Cons k zeroes), stdin, stdout])
            (c, state[ls, 0, Cons x2 (Cons (x1+k) zeroes), stdin, stdout]))
    as Hmv2.
  induction x1; intros.
  repeat bf_step.
  repeat bf_step; simpl.
  rewrite plus_n_Sm.
  apply IHx1.

  intros.
  apply (iter_trans _ (> > [<
                            [< + > > > + < < -END]> >
                            [< < + > > -END]
                            < -END]
                             < [-END]
                             <END,
                       state[ls, 0, Cons x2 (Cons (x1+0) zeroes), stdin, stdout])).
  apply (iter_trans _ ([> > + < < -END]
                       > > [<
                            [< + > > > + < < -END]> >
                            [< < + > > -END]
                            < -END]
                       < [-END]
                       <END,
                       state[ls, x1, Cons x2 (Cons 0 zeroes), stdin, stdout])).
  bf_step.
  apply Hmv2.
  clear Hmv2.
  rewrite <- plus_n_O.
  
  do 2 bf_step; simpl.
  generalize dependent x1; generalize dependent x2.
  assert
    (forall x1 x2 k c,
       iter ([<
              [< + > > > + < < -END]
                > >
                [< < + > > -END]
                  < -END]c,
             state[Cons x2 (Cons k ls), x1, zeroes, stdin, stdout])
            (c, state[Cons x2 (Cons (x1 * x2 + k) ls), 0, zeroes, stdin, stdout]))
    as H.
  induction x1.
  intros.
  repeat bf_step.

  intros; bf_step.
  assert
    (forall x1 x2 k i c,
       iter (< [< + > > > + < < -END]> >[< < + > > -END]< -c,
             state[Cons x2 (Cons (i*x2+k) ls), S x1, zeroes, stdin, stdout])
            (c,
             state[Cons x2 (Cons (S i*x2+k) ls), x1, zeroes, stdin, stdout]))
    as Hstep.

  intros.
  bf_step; simpl.
  assert
    (forall x1 x2 k k' c,
       iter ([< + > > > + < < -END]c,
             state[Cons (k) ls, x2, Cons x1 (Cons k' zeroes), stdin, stdout])
            (c, state[Cons (x2+k) ls, 0, Cons x1 (Cons (x2+k') zeroes), stdin, stdout]))
    as Hsomething.
  intros x x'.
  induction x'.
  intros.
  repeat bf_step.
  
  intros.
  repeat bf_step; simpl.
  replace (S (x' + k')) with (x' + S k') by auto with arith.
  replace (S (x' + k1)) with (x' + S k1) by auto with arith.
  apply IHx'.

  apply (iter_trans _
                    (> >[< < + > > -END]< - c0,
                     state[Cons (x3+(i*x3+k0)) ls, 0,
                           Cons (S x0) (Cons (x3+0) zeroes), stdin, stdout])).
  apply (iter_trans _
                    ([< + > > > + < < - END]> > [< < + > > - END]< - c0,
                     state[Cons (i * x3 + k0) ls, x3,
                           Cons (S x0) (Cons 0 zeroes), stdin, stdout])).
  bf_step.
  apply (Hsomething (S x0) x3 (i*x3+k0) 0).
  clear Hsomething.
  do 2 bf_step; simpl.
  apply (iter_trans
           _ (< - c0,
              state[Cons (S x0) (Cons x3 (Cons (x3+(i*x3+k0)) ls)),
                    0, zeroes, stdin, stdout])).
  rewrite plus_0_r.
  assert
    (forall k k',
       iter
         ([< < + > > - END]< - c0,
          state[Cons (S x0) (Cons k (Cons (k' + (i * k' + k0)) ls)), 
                x3, zeroes, stdin, stdout])
         (< - c0,
          state[Cons (S x0) (Cons (x3+k) (Cons (k' + (i * k' + k0)) ls)),
                0, zeroes, stdin, stdout]))
  as Hind.
  induction x3.
  intros.
  repeat bf_step.

  intros.
  repeat bf_step; simpl.
  replace (S (x3 + k1)) with (x3 + S k1) by auto with arith.
  apply (IHx3 (S k1)).
  rewrite <- (plus_0_r x3) at 4.
  apply Hind.

  repeat bf_step; simpl.
  replace (x3 + (i * x3 + k0)) with (x3 + i * x3 + k0) by auto with arith.
  repeat bf_step.

  apply (iter_trans
           _
           ([< [< + > > > + < < - END]> > [< < + > > - END]< - END]c,
            state[Cons x2 (Cons (x2+k) ls), x1, zeroes, stdin, stdout])).
  rewrite <- (plus_0_l k) at 1.
  rewrite <- (mult_0_l x2) at 1.
  rewrite <- (mult_1_l x2) at 4.
  apply (Hstep x1 x2 k 0).
  replace (x2 + x1*x2 + k) with (x1*x2+(x2+k)).
  apply (IHx1 x2 (x2+k)).
  rewrite (plus_comm x2 (x1*x2)).
  rewrite plus_assoc.
  reflexivity.

  intros.
  apply (iter_trans
           _
           (<[-END]<END, state[Cons x2 (Cons (x1*x2) ls), 0, zeroes, stdin, stdout])).
  rewrite <- (plus_0_r (x1*x2)).
  apply (H x1 x2 0).

  repeat bf_step; simpl.

  assert
    (forall ls x rs stdin stdout c,
        iter
          ([-END]c, state[ls, x, rs, stdin, stdout])
          (c, state[ls, 0, rs, stdin, stdout]))
    as Hreset.
  intros; induction x; repeat bf_step; apply IHx.
  apply (iter_trans _ ([-END]< END, state[Cons (x1*x2) ls, x2, zeroes, stdin, stdout])).
  bf_step.
  apply (iter_trans _ (< END, state[Cons (x1*x2) ls, 0, zeroes, stdin, stdout])).
  apply (Hreset (Cons (x1*x2) ls) x2 zeroes stdin stdout (< END)).
  repeat bf_step.
Qed.
