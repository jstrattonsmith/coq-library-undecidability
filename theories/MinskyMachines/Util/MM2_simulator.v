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

(* --- mm2_outcome_at: a total, option-valued observation of the simulator
   at a given step count (Some 1 if halted-at-(0,(0,0)), Some 0 if halted
   elsewhere, None if not yet halted) -- pure MM2 content, no synthetic-
   computability dependency of its own (it's only ever *used* to build a
   Church's-Thesis witness downstream, in the consuming project's own
   MM2/Simulator.v, but the function itself doesn't need that machinery). *)

Definition mm2_outcome_at (c y n : nat) : option nat :=
  if mm2_haltedAt (progOf c) n (1,(y,0))
  then Some (if mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0)) then 1 else 0)
  else None.

(* --- L-extractability: every function above is built entirely from plain
   structurally-recursive Gallina functions -- no opaque parts -- so each
   extracts to an actual L-term via Undecidability.L's own `extract`
   tactic. This needs nothing beyond this library's own L/ framework;
   deliberately kept in one file with the functions
   themselves rather than split by a downstream consumer, since `extract`
   turned out not to reliably bridge a computable instance for a function
   used inside another function's body across a file boundary (confirmed
   empirically: instances registered via `computableExt` in one file
   weren't picked up by `extract` processing a caller in another file that
   Requires it, even though the same proof scripts work fine when
   colocated).

   Gotcha, confirmed by direct probing: `Require Import Undecidability.L.L.`
   (the convenience mega-import) breaks `extract` for several of the
   lemmas below with an opaque "could not simplify some occuring term,
   shelved instead" failure -- apparently via some notation/instance
   collision, not anything about these specific functions. Fix: import the
   same *targeted* set of L.Datatypes files needed, never the mega
   import. *)

From Undecidability.L Require Import Datatypes.List.List_in.
From Undecidability.L Require Import Datatypes.List.List_basics.
From Undecidability.L Require Import Datatypes.List.List_extra.
From Undecidability.L Require Import Datatypes.LProd.
From Undecidability.L Require Import Datatypes.LTerm.
From Undecidability.L Require Import Functions.Eval.
From Undecidability.L Require Import Tactics.GenEncode.

MetaRocq Run (tmGenEncode "mm2_instr_enc" mm2_instr).
Hint Resolve mm2_instr_enc_correct : Lrewrite.

Instance term_mm2_inc_a : computable mm2_inc_a.
Proof. extract constructor. Qed.
Instance term_mm2_inc_b : computable mm2_inc_b.
Proof. extract constructor. Qed.
Instance term_mm2_dec_a : computable mm2_dec_a.
Proof. extract constructor. Qed.
Instance term_mm2_dec_b : computable mm2_dec_b.
Proof. extract constructor. Qed.

(* Registering constructors above pulls in enough for the rest -- only now
   is it safe to bring in the remaining Datatypes/List instances needed
   below (nth_error, option, bool), per the ordering gotcha noted above. *)
From Undecidability.L Require Import Datatypes.List.List_nat.
From Undecidability.L Require Import Datatypes.LOptions.
From Undecidability.L Require Import Datatypes.LBool.

Instance mm2_atom_fun_computable : computable mm2_atom_fun.
Proof. extract. Qed.

Instance mm2_step_fun_computable : computable mm2_step_fun.
Proof. extract. Qed.

(* embed/unembed's computable instances: reproduced from
   SyntheticComputability.Models.CT's own proofs (this library has no
   SyntheticComputability dependency, and importing that file wholesale
   would introduce one just for this) -- these two don't actually depend
   on any of that file's *other* content. *)

Fixpoint nat_sum n : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + nat_sum n'
  end.

Definition embed' '(x, y) : nat := y + nat_sum (y + x).

Instance nat_sum_computable : computable nat_sum.
Proof. extract. Qed.

Instance embed_computable : computable embed.
Proof. change (computable embed'). extract. Qed.

Definition unembed'' := (fix F (k : nat) :=
  match k with
  | 0 => (0,0)
  | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end
  end).

Instance unembed_computable : computable unembed.
Proof.
eapply computableExt with (x := unembed''). 2:extract.
intros n. cbn. induction n; cbn.
- reflexivity.
- fold (unembed n). rewrite IHn. now destruct (unembed n).
Qed.

Instance instr_to_nat_computable : computable instr_to_nat.
Proof. extract. Qed.

Instance nat_to_instr_computable : computable nat_to_instr.
Proof. extract. Qed.

Instance list_to_nat_computable : computable list_to_nat.
Proof. extract. Qed.

Instance nat_to_list_computable : computable nat_to_list.
Proof. extract. Qed.

Instance progOf_computable : computable progOf.
Proof. extract. Qed.

Instance codeOf_computable : computable codeOf.
Proof. extract. Qed.

Instance mm2_step_total_computable : computable mm2_step_total.
Proof. extract. Qed.

(* mm2_iter recurses on its *middle* argument (Nat.iter n (mm2_step_total P)
   s0) -- extract's automatic recursive-argument detection wants the
   decreasing argument first, and Nat.iter itself has no registered
   computable instance to fall back on. Fix: give a directly-Fixpoint,
   n-first shadow definition (which extracts cleanly), then transfer
   computability to mm2_iter itself via computableExt plus an extensional
   equality proof (same idiom as unembed/unembed'' above). *)
Fixpoint mm2_iter_fix (n : nat) (P : list mm2_instr) (s0 : mm2_state) : mm2_state :=
  match n with
  | 0 => s0
  | S n' => mm2_step_total P (mm2_iter_fix n' P s0)
  end.

Instance mm2_iter_fix_computable : computable mm2_iter_fix.
Proof. extract. Qed.

Lemma mm2_iter_fix_spec P n s0 : mm2_iter_fix n P s0 = mm2_iter P n s0.
Proof.
induction n as [| n IH] in s0 |- *.
- reflexivity.
- rewrite mm2_iter_S. cbn [mm2_iter_fix]. now rewrite IH.
Qed.

Instance mm2_iter_computable : computable mm2_iter.
Proof.
eapply computableExt with (x := fun P n s0 => mm2_iter_fix n P s0).
2: extract.
intros P n s0. apply mm2_iter_fix_spec.
Qed.

Instance mm2_haltedAt_computable : computable mm2_haltedAt.
Proof. extract. Qed.

Instance mm2_state_eqb_computable : computable mm2_state_eqb.
Proof. extract. Qed.

Instance mm2_outcome_at_computable : computable mm2_outcome_at.
Proof. extract. Qed.
