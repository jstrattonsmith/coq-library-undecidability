(* A self-contained Cantor pairing bijection nat * nat <-> nat. No general
   pairing utility exists elsewhere in this library to reuse; this is the
   same standard construction coq-synthetic-computability's
   Shared/embed_nat.v independently provides for its own purposes.

   Deliberately its own file, importing nothing beyond PeanoNat (in
   particular, no ssreflect): the proof below relies on vanilla Rocq
   `rewrite`/`simpl` semantics, which ssreflect's own `rewrite` tactic
   overrides in ways that break this exact proof script. *)

Require Import PeanoNat.

Definition embed '(x, y) : nat :=
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

Definition unembed (n : nat) : nat * nat :=
  nat_rec _ (0, 0) (fun _ '(x, y) => match x with S x => (x, S y) | _ => (S y, 0) end) n.

Lemma embedP {xy: nat * nat} : unembed (embed xy) = xy.
Proof.
  assert (forall n, embed xy = n -> unembed n = xy).
    intro n. revert xy. induction n as [|n IH].
      intros [[|?] [|?]]; intro H; inversion H; reflexivity.
    intros [x [|y]]; simpl.
      case x as [|x]; simpl; intro H.
        inversion H.
      rewrite (IH (0, x)); [reflexivity|].
      inversion H; simpl. rewrite Nat.add_0_r. reflexivity.
    intro H. rewrite (IH (S x, y)); [reflexivity|].
    inversion H. simpl. rewrite Nat.add_succ_r. reflexivity.
  apply H. reflexivity.
Qed.
Arguments embed : simpl never.
