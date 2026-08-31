(* A decidable, functional characterization of MM2 (two-counter machine)
   stepping: a single-instruction step function (mm2_atom_fun) and its
   program-indexed extension (mm2_step_fun), each proved equivalent to
   the relational mm2_atom/mm2_step from MM2.v. MM2_facts.v (this
   directory) already gives a rich relational theory of stepping, but
   has no computable step function -- that's the gap this file fills,
   useful for anything wanting to actually run an MM2 program in
   Gallina (a simulator, a decision procedure, an L-extractable
   evaluator, ...).

   Determinism (mm2_step_det) and the halted-iff-out-of-bounds fact are
   already proved relationally in MM2_facts.v (mm2_step_det,
   mm2_stop_index_iff) -- reuse those directly rather than re-deriving
   them functionally; see MM2_facts.v for the relational statements. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From Stdlib Require Import List Lia.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts.
Import MM2Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* mm2_atom_fun doesn't depend on a program at all -- it's the semantics
   of a single instruction, not a program-indexed step. *)

Definition mm2_atom_fun (ρ : mm2_instr) (s : mm2_state) :=
  let '(i,(a,b)) := s in
  match ρ with
  | mm2_inc_a => (1+i,(S a,b))
  | mm2_inc_b => (1+i,(a,S b))
  | mm2_dec_a j =>
    match a with
    | 0 => (1+i,(0,b))
    | S a => (j,(a,b))
    end
  | mm2_dec_b j =>
    match b with
    | 0 => (1+i,(a,0))
    | S b => (j,(a,b))
    end
  end.

Lemma mm2_atom_fun_spec ρ s1 s2 :
  mm2_atom ρ s1 s2 ↔ mm2_atom_fun ρ s1 = s2.
Proof.
split.
- by case.
- case: ρ => [||j|j].
  1,2: case: s1 => [i [a b]] /= <-; constructor.
  + case: s1 => [i [[|a] b]] /= <-; constructor.
  + case: s1 => [i [a [|b]]] /= <-; constructor.
Qed.

Arguments mm2_atom_fun_spec {_ _ _}.

Section MM2Stepper.

Variable P : list mm2_instr.
Let n := length P.

Definition mm2_step_fun s :=
  match fst s with
  | 0 => None
  | S i => match nth_error P i with
           | Some ρ => Some (mm2_atom_fun ρ s)
           | None => None
           end
  end.

Lemma mm2_step_fun_spec s1 s2 :
  mm2_step P s1 s2 ↔ mm2_step_fun s1 = Some s2.
Proof.
split.
- case=> ρ [Hinstr /mm2_atom_fun_spec <-].
  rewrite /mm2_step_fun /=.
  case: s1 Hinstr => [[|i] [a b]] /= Hinstr.
  { case: Hinstr => l [r [_ /=]]; lia. }
  by rewrite (iffRL (nth_error_Some_mm2_instr_at_iff _ _) Hinstr).
- rewrite /mm2_step_fun.
  case: s1 => [[|i] [a b]] //=.
  case Hnth: (nth_error P i) => [ρ|] //= [<-].
  exists ρ; split.
  + by apply/(nth_error_Some_mm2_instr_at_iff i).
  + by apply/mm2_atom_fun_spec.
Qed.

Arguments mm2_step_fun_spec {_ _}.

End MM2Stepper.

Arguments mm2_step_fun_spec {_ _ _}.
