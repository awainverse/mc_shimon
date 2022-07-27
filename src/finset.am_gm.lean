import cauchy_induction

import tactic
import data.nat.basic
import data.real.basic
import analysis.special_functions.pow

open_locale classical
noncomputable theory


open_locale big_operators

open finset

def finset_am (f : ℕ → ℝ) (s : finset ℕ) : ℝ :=
(∑ i in s, f i) / finset.card(s)

def finset_gm (f : ℕ → ℝ) (s : finset ℕ) : ℝ :=
(∏ i in s, f i) ^ (1 / (finset.card(s) : ℝ))

def am_gm_prop (f : ℕ → ℝ) (n : ℕ) : Prop := ∀ (s : finset ℕ), 
(s.card = n) → finset_gm f s ≤ finset_am f s

lemma am_weighted_avg (f : ℕ → ℝ) 
{s1 s2 : finset ℕ} (hs1 : s1 ≠ ∅) (hs2 : s2 ≠ ∅) (h_disj : disjoint s1 s2): 
(finset_am f s1) * s1.card + (finset_am f s2) * s2.card =
finset_am f (s1 ∪ s2) * (s1.card + s2.card) :=

begin
  unfold finset_am,
  rw finset.sum_union h_disj,
  rw finset.card_union_eq h_disj,
  rw div_mul_cancel (∑ (i : ℕ) in s1, f i),
  swap,
  rw [ne.def, nat.cast_eq_zero, card_eq_zero, ←ne.def],
  refine hs1,

  rw div_mul_cancel (∑ (i : ℕ) in s2, f i),
  swap,
  rw [ne.def, nat.cast_eq_zero, card_eq_zero, ←ne.def],
  refine hs2,

  rw nat.cast_add,
  rw div_mul_cancel (∑ (x : ℕ) in s1, f x + ∑ (x : ℕ) in s2, f x),
  
  norm_cast,
  simp only [add_eq_zero_iff, card_eq_zero, not_and],

  intro useless,
  refine hs2,
end

lemma gm_weighted_avg {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) 
{s1 s2 : finset ℕ} (hs1 : s1 ≠ ∅) (hs2 : s2 ≠ ∅) (h_disj : disjoint s1 s2) : 
(finset_gm f s1) ^ s1.card * (finset_gm f s2) ^ s2.card =
finset_gm f (s1 ∪ s2) ^ (s1.card + s2.card) :=

begin
  unfold finset_gm,
  rw ←real.rpow_nat_cast,
  rw ←real.rpow_nat_cast,
  rw ←real.rpow_nat_cast,

  have thing1 : 0 ≤ ∏ (i : ℕ) in s1, f i,
  {
    have f_nneg_s1 : ∀ (i : ℕ), i ∈ s1 → 0 ≤ f i,
    {
      intro i,
      intro useless,
      refine f_nneg i,
    },
    refine finset.prod_nonneg f_nneg_s1,
  },
  have thing2 : 0 ≤ ∏ (i : ℕ) in s2, f i,
  {
    have f_nneg_s2 : ∀ (i : ℕ), i ∈ s2 → 0 ≤ f i,
    {
      intro i,
      intro useless,
      refine f_nneg i,
    },
    refine finset.prod_nonneg f_nneg_s2,
  },
  have thing3 : 0 ≤ ∏ (i : ℕ) in s1 ∪ s2, f i,
  {
    rw finset.prod_union h_disj,
    refine mul_nonneg thing1 thing2,
  },
  rw ←real.rpow_mul thing1,
  rw div_mul_cancel,
  swap,
  rw [ne.def, nat.cast_eq_zero, card_eq_zero, ←ne.def],
  refine hs1,
  rw real.rpow_one,
  rw ←real.rpow_mul thing2,
  rw div_mul_cancel,
  swap,
  rw [ne.def, nat.cast_eq_zero, card_eq_zero, ←ne.def],
  refine hs2,
  rw real.rpow_one,
  rw ←real.rpow_mul thing3,
  rw finset.card_union_eq h_disj,
  rw div_mul_cancel,
  swap,
  norm_cast,
  simp only [add_eq_zero_iff, card_eq_zero, not_and],
  intro useless,
  refine hs2,
  rw real.rpow_one,
  rw finset.prod_union h_disj,
end

lemma am_gm_two' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 
(x * y) ^ (1 / (2 : ℝ)) ≤ (x + y) / 2 :=

begin
  set a := x ^ (1 / (2 : ℝ)) with a_def,
  set b := y ^ (1 / (2 : ℝ)) with b_def,
  
  have ha := real.rpow_nonneg_of_nonneg hx (1 / (2 : ℝ)),
  have hb := real.rpow_nonneg_of_nonneg hy (1 / (2 : ℝ)),
  have difference_sq_nneg := sq_nonneg (a - b),
  rw [sub_sq, add_comm_sub, ←add_sub_assoc] at difference_sq_nneg,
  have refl_le_two_a_b : 2 * a * b ≤ 2 * a * b,
  {
    refl,
  },
  have new := add_le_add difference_sq_nneg refl_le_two_a_b,
  rw [sub_add_cancel, zero_add] at new,
  have divided_by_two : a * b ≤ (a ^ 2 + b ^ 2) / 2,
  {
    --REPLACE WITH "DIRECT" PROOF
    linarith, 
  },
  rw a_def at divided_by_two,
  rw b_def at divided_by_two,
  rw ←real.rpow_two (x ^ (1 / (2 : ℝ))) at divided_by_two,
  rw ←real.rpow_two (y ^ (1 / (2 : ℝ))) at divided_by_two,
  rw ←real.rpow_mul hx at divided_by_two,
  rw ←real.rpow_mul hy at divided_by_two,
  rw one_div_mul_cancel at divided_by_two,
  swap,
  refine two_ne_zero,
  rw real.rpow_one at divided_by_two,
  rw real.rpow_one at divided_by_two,
  rw ←real.mul_rpow hx hy at divided_by_two,
  refine divided_by_two,
end

lemma am_gm_two {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), (0 ≤ f k)): 
am_gm_prop f 2 :=

begin
  sorry,
end

lemma am_gm_doubling {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), (0 ≤ f k)) : 
∀ (n : ℕ), am_gm_prop f n → am_gm_prop f (2 * n) :=
--∀ (s2 : finset ℕ), s2.card = 2 * n → 

begin
  sorry,
end

lemma am_gm_pred {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), (0 ≤ f k)) : 
∀ (n : ℕ), am_gm_prop f (n + 1) → am_gm_prop f n :=

begin
--set f' : ℕ → ℝ := λ m, if m < n then f n else 1,
  sorry,
end

theorem am_gm' {f : ℕ → ℝ} (f_nneg : (∀ (k : ℕ), 0 ≤ f k)) (n : ℕ) : 
am_gm_prop f n :=
begin
  have base_case := am_gm_two f_nneg,
  have pred_step := am_gm_pred f_nneg, 
  have doubling_step := am_gm_doubling f_nneg,
  have two_lt_zero : 0 < 2,
  {
    linarith,
  },
  refine cauchy_induction pred_step doubling_step two_lt_zero base_case n,
end

theorem am_gm {f : ℕ → ℝ} (s : finset ℕ) (f_nneg : (∀ (k : ℕ), 0 ≤ f k)):
finset_gm f s ≤ finset_am f s := 

begin
  have answer := am_gm' f_nneg s.card,
  rw am_gm_prop at answer,
  have reflexivity : s.card = s.card, 
  {
    refl,
  },
  refine answer s reflexivity,
end



