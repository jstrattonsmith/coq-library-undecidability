(* A total, step-indexed Gallina simulator for MM2 (two-counter machine)
   programs, built on top of MM2_stepper.v's computable mm2_step_fun,
   plus a hand-rolled Godel coding of programs as naturals
   (progOf/codeOf). MM2_facts.v/MM2_stepper.v give the step relation
   and its computable characterization; this file adds the missing
   "run the program N steps and see where it is" evaluator, which any
   simulation, decision procedure, or extraction-based construction
   needs but neither of those two files provides on its own.

   The nat<->list mm2_instr encoding is deliberately hand-rolled via
   embed/unembed (Cantor pairing) rather than a generic Countable
   instance, so it stays usable in extraction-based settings that need
   every function to bottom out in primitive recursion over nat/list,
   not a typeclass-driven encoding. *)

Require Import Stdlib.Unicode.Utf8.
From Stdlib Require Import PeanoNat Lia Relation_Operators.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat.
Import MM2Notations.

(* --- 0. nat <-> list mm2_instr, via a hand-rolled embed-based encoding -- *)

Definition instr_to_nat (i : mm2_instr) : nat :=
  match i with
  | mm2_inc_a => embed (0, 0)
  | mm2_inc_b => embed (1, 0)
  | mm2_dec_a j => embed (2, j)
  | mm2_dec_b j => embed (3, j)
  end.

Definition nat_to_instr (n : nat) : mm2_instr :=
  match unembed n with
  | (0, _) => mm2_inc_a
  | (1, _) => mm2_inc_b
  | (2, j) => mm2_dec_a j
  | (3, j) => mm2_dec_b j
  | (_, _) => mm2_inc_a
  end.

Lemma nat_to_instr_to_nat i : nat_to_instr (instr_to_nat i) = i.
Proof. destruct i; unfold nat_to_instr, instr_to_nat; now rewrite embedP. Qed.

Fixpoint list_to_nat (l : list mm2_instr) : nat :=
  match l with
  | nil => 0
  | cons i l' => S (embed (instr_to_nat i, list_to_nat l'))
  end.

Fixpoint nat_to_list (fuel n : nat) : list mm2_instr :=
  match fuel, n with
  | S fuel', S n' => let '(a, b) := unembed n' in cons (nat_to_instr a) (nat_to_list fuel' b)
  | _, _ => nil
  end.

Lemma embed_ge_snd x y : embed (x, y) >= y.
Proof. unfold embed. lia. Qed.

Lemma nat_to_list_list_to_nat_fuel (P : list mm2_instr) (fuel : nat) :
  list_to_nat P <= fuel -> nat_to_list fuel (list_to_nat P) = P.
Proof.
induction P as [| i P IH] in fuel |- *; intros Hfuel.
- destruct fuel; reflexivity.
- cbn [list_to_nat] in Hfuel |- *. destruct fuel as [| fuel']; [lia |].
  cbn [nat_to_list]. rewrite embedP.
  rewrite nat_to_instr_to_nat. f_equal.
  apply IH. pose proof (embed_ge_snd (instr_to_nat i) (list_to_nat P)). lia.
Qed.

Definition progOf (c : nat) : list mm2_instr := nat_to_list c c.

Definition codeOf (P : list mm2_instr) : nat := list_to_nat P.

Lemma progOf_codeOf P : progOf (codeOf P) = P.
Proof. unfold progOf, codeOf. apply nat_to_list_list_to_nat_fuel. lia. Qed.

(* --- 1. step-indexed MM2 evaluator, total by construction --------------- *)

Definition mm2_step_total (P : list mm2_instr) (s : mm2_state) : mm2_state :=
  match mm2_step_fun P s with Some s' => s' | None => s end.

Definition mm2_iter (P : list mm2_instr) (n : nat) (s0 : mm2_state) : mm2_state :=
  Nat.iter n (mm2_step_total P) s0.

Definition mm2_haltedAt (P : list mm2_instr) (n : nat) (s0 : mm2_state) : bool :=
  match mm2_step_fun P (mm2_iter P n s0) with Some _ => false | None => true end.

Lemma mm2_iter_S P n s0 : mm2_iter P (S n) s0 = mm2_step_total P (mm2_iter P n s0).
Proof. reflexivity. Qed.

Lemma mm2_iter_frozen P n s0 :
  mm2_step_fun P (mm2_iter P n s0) = None ->
  forall k, mm2_iter P (n + k) s0 = mm2_iter P n s0.
Proof.
  intros Hstop k. induction k as [|k IH].
  - now rewrite PeanoNat.Nat.add_0_r.
  - rewrite PeanoNat.Nat.add_succ_r, mm2_iter_S, IH.
    unfold mm2_step_total. now rewrite Hstop.
Qed.

Definition mm2_state_eqb (s1 s2 : mm2_state) : bool :=
  match s1, s2 with
  | (i1,(a1,b1)), (i2,(a2,b2)) => (Nat.eqb i1 i2 && Nat.eqb a1 a2 && Nat.eqb b1 b2)%bool
  end.

Lemma mm2_state_eqb_true s1 s2 : mm2_state_eqb s1 s2 = true <-> s1 = s2.
Proof.
destruct s1 as [i1 [a1 b1]], s2 as [i2 [a2 b2]]. unfold mm2_state_eqb.
rewrite !Bool.andb_true_iff, !PeanoNat.Nat.eqb_eq.
split.
- intros [[-> ->] ->]. reflexivity.
- intros [= -> -> ->]. auto.
Qed.

(* --- 2. connecting mm2_iter back to the library's own relational mm2_step,
   mm2_stop -- plain facts, useful to anything that wants both the
   computable iterator here and the relational reachability theory in
   MM2_facts.v (e.g. mm2_terminates_Acc, mm2_steps_confluent). *)

Lemma mm2_iter_rtc P n s0 : clos_refl_trans _ (mm2_step P) s0 (mm2_iter P n s0).
Proof.
induction n as [|n IH].
- apply rt_refl.
- rewrite mm2_iter_S. unfold mm2_step_total.
  destruct (mm2_step_fun P (mm2_iter P n s0)) as [s'|] eqn:E.
  + eapply rt_trans; [exact IH |]. apply rt_step. apply mm2_step_fun_spec. exact E.
  + exact IH.
Qed.

Lemma mm2_stop_of_step_fun_none P s :
  mm2_step_fun P s = None -> mm2_stop P s.
Proof.
intros H s' Hstep. apply mm2_step_fun_spec in Hstep. congruence.
Qed.
