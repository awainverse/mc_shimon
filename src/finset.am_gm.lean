--TO DO:
--am_gm_two (set version of it) --> sum/prod of set of card 2
--pred
--Fix names (replace prod_s1_nonneg, a with actual s1_nonempty_keywords with meaning)
--Fix formatting

import cauchy_induction

import tactic
import data.nat.basic
import data.real.basic
import analysis.special_functions.pow

open_locale classical
noncomputable theory

open_locale big_operators

open finset
  --set s := (finset.range(20)).filter( λ (k : ℕ), 3 * k + 7 < 28),
  --finset.mem filter

--Cant find in documentation
lemma finset.exists_nonmem (s : finset ℕ) : ∃ (t : ℕ), t ∉ s :=

begin
  sorry,
end

lemma finset.construct_disj (n : ℕ) : ∃ (s1 s2 : finset ℕ), 
(s1.card = n) ∧ (s2.card = n) ∧ (s1 ∩ s2 = ∅) :=
begin
  set s1 := finset.range(n) with s1_def,
  set s2 := finset.range(2 * n) \ s1 with s2_def,
  use s1,
  use s2,
  split,
  refine finset.card_range n,
  split,
  have range_n_sbset : finset.range(n) ⊆ finset.range(2 * n),
  {
    refine finset.range_subset.2 _,
    rw le_iff_exists_add,
    use n,
    rw two_mul,
  },
  have thm := finset.card_sdiff range_n_sbset,
  rw ←s1_def at thm,
  rw ←s2_def at thm,
  rw finset.card_range (2 * n) at thm,
  rw finset.card_range n at thm,
  rw thm,
  rw two_mul,
  rw nat.add_sub_cancel,
  rw ←finset.disjoint_iff_inter_eq_empty,
  rw s2_def,
  refine finset.disjoint_sdiff,
end

lemma finset.split_in_half (s : finset ℕ) (n : ℕ) : s.card = (2 * n) →
∃ (s1 s2 : finset ℕ), 
(s1 ⊆ s) ∧ (s2 ⊆ s) ∧ (s1.card = n) ∧ (s2.card = n) ∧ (s1 ∩ s2 = ∅) ∧ (s = s1 ∪ s2):=

begin
  intro s_card,
  have n_leq_s_card : n ≤ s.card,
  {
    rw s_card,
    rw le_iff_exists_add,
    use n,
    rw two_mul,
  },
  have exists_card_n_subset := finset.exists_smaller_set s n n_leq_s_card,
  rcases exists_card_n_subset with ⟨s1, s1_subset, s1_card⟩,
  set s2 := s \ s1 with s2_def,
  use s1,
  use s2,
  split,
  refine s1_subset,
  split,
  refine finset.sdiff_subset s s1,
  split,
  refine s1_card,
  split,
  rw finset.card_sdiff s1_subset,
  rw s_card,
  rw s1_card,
  rw two_mul,
  rw nat.add_sub_cancel,
  split,
  rw ←finset.disjoint_iff_inter_eq_empty,
  refine finset.disjoint_sdiff,
  rw s2_def,
  rw finset.union_sdiff_of_subset s1_subset,
end

lemma finset.sum_card_two (f : ℕ → ℝ) {x y : ℕ} (hxy : x ≠ y): ∑ (i : ℕ) in {x, y}, f i = f x + f y :=

begin
  have split : ({x, y} : finset ℕ) = {x} ∪ {y},
  {
    sorry,
  },
  rw split,
  rw finset.sum_union (finset.disjoint_singleton.2 hxy),
  rw finset.sum_singleton,
  rw finset.sum_singleton,
end

lemma finset.prod_card_two (f : ℕ → ℝ) {x y : ℕ} (hxy : x ≠ y): ∏ (i : ℕ) in {x, y}, f i = f x * f y :=

begin
    have split : ({x, y} : finset ℕ) = {x} ∪ {y},
  {
    sorry,
  },
  rw split,
  rw finset.prod_union (finset.disjoint_singleton.2 hxy),
  rw finset.prod_singleton,
  rw finset.prod_singleton,
end

def finset_am (f : ℕ → ℝ) (s : finset ℕ) : ℝ :=
(∑ i in s, f i) / finset.card(s)

def finset_gm (f : ℕ → ℝ) (s : finset ℕ) : ℝ :=
(∏ i in s, f i) ^ (1 / (finset.card(s) : ℝ))

def am_gm_prop (f : ℕ → ℝ) (n : ℕ) : Prop := ∀ (s : finset ℕ), 
(s.card = n) → finset_gm f s ≤ finset_am f s

lemma am_nneg {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) (s : finset ℕ): 
(s ≠ ∅) → 0 ≤ finset_am f s :=

begin
  rw finset_am,
  intro s_nonempty,
  have f_nneg_in_s : ∀ (k : ℕ), k ∈ s → 0 ≤ f k,
  {
    intro k,
    intro s_nonempty,
    refine f_nneg k,
  },
  have s1_nonempty_keyword : 0 < (↑s.card : ℝ),
  {
    refine nat.cast_pos.2 (finset.nonempty.card_pos (finset.nonempty_of_ne_empty s_nonempty)),
  },
  have a := (zero_le_mul_right s1_nonempty_keyword).1,
  swap,
  refine (∑ (i : ℕ) in s, f i) / ↑(s.card),
  have s_card_nonzero : (s.card : ℝ) ≠ 0,
  {
    simp only [ne.def, nat.cast_eq_zero, card_eq_zero],
    rw ne.def at s_nonempty,
    refine s_nonempty,
  },
  rw div_mul_cancel at a,
  refine a (finset.sum_nonneg f_nneg_in_s),
  refine s_card_nonzero,
end

lemma gm_nneg {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) (s : finset ℕ): 
0 ≤ finset_gm f s :=

begin
  rw finset_gm,
  refine real.rpow_nonneg_of_nonneg _ (1 / ↑(s.card)),
  have f_nneg_in_s : ∀ (k : ℕ), k ∈ s → 0 ≤ f k,
  {
    intro k,
    intro k_in_s, --useless
    refine f_nneg k,
  },
  refine finset.prod_nonneg f_nneg_in_s,
end

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
  intro s_nonempty,
  refine hs2,
end

lemma gm_weighted_avg {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) 
{s1 s2 : finset ℕ} (hs1 : s1 ≠ ∅) (hs2 : s2 ≠ ∅) (h_disj : disjoint s1 s2) : 
(finset_gm f s1) ^ (s1.card : ℝ) * (finset_gm f s2) ^ (s2.card : ℝ) =
finset_gm f (s1 ∪ s2) ^ ((s1.card + s2.card) : ℝ) :=

begin
  unfold finset_gm,
  have prod_s1_nonneg : 0 ≤ ∏ (i : ℕ) in s1, f i,
  {
    have f_nneg_s1 : ∀ (i : ℕ), i ∈ s1 → 0 ≤ f i,
    {
      intro i,
      intro s_nonempty,
      refine f_nneg i,
    },
    refine finset.prod_nonneg f_nneg_s1,
  },
  have prod_s2_nonneg : 0 ≤ ∏ (i : ℕ) in s2, f i,
  {
    have f_nneg_s2 : ∀ (i : ℕ), i ∈ s2 → 0 ≤ f i,
    {
      intro i,
      intro s_nonempty,
      refine f_nneg i,
    },
    refine finset.prod_nonneg f_nneg_s2,
  },
  have prod_s1_union_s2_nonneg : 0 ≤ ∏ (i : ℕ) in s1 ∪ s2, f i,
  {
    rw finset.prod_union h_disj,
    refine mul_nonneg prod_s1_nonneg prod_s2_nonneg,
  },
  rw ←real.rpow_mul prod_s1_nonneg,
  rw div_mul_cancel,
  swap,
  rw [ne.def, nat.cast_eq_zero, card_eq_zero, ←ne.def],
  refine hs1,
  rw real.rpow_one,
  rw ←real.rpow_mul prod_s2_nonneg,
  rw div_mul_cancel,
  swap,
  rw [ne.def, nat.cast_eq_zero, card_eq_zero, ←ne.def],
  refine hs2,
  rw real.rpow_one,
  rw ←real.rpow_mul prod_s1_union_s2_nonneg,
  rw finset.card_union_eq h_disj,
  rw nat.cast_add,
  rw div_mul_cancel,
  swap,
  norm_cast,
  simp only [add_eq_zero_iff, card_eq_zero, not_and],
  intro s_nonempty,
  refine hs2,
  rw real.rpow_one,
  rw finset.prod_union h_disj,
end

lemma am_add (f : ℕ → ℝ) {s1 s2 : finset ℕ} {n : ℕ} 
(s1_card : s1.card = n) (s2_card : s2.card = n) (h_disj : disjoint s1 s2) (n_pos : 0 < n) :
finset_am f s1 + finset_am f s2 = (finset_am f (s1 ∪ s2)) * 2 :=

begin
  have s1_nonempty : s1 ≠ ∅,
  {
    rw ←s1_card at n_pos,
    have s1_nonempty_keyword := finset.card_pos.1 n_pos,
    refine finset.nonempty_iff_ne_empty.1 s1_nonempty_keyword,
  },
  have s2_nonempty : s2 ≠ ∅,
  {
    rw ←s2_card at n_pos,
    have s2_nonempty_keyword := finset.card_pos.1 n_pos,
    refine finset.nonempty_iff_ne_empty.1 s2_nonempty_keyword,
  },
  have n_nonzero : (n : ℝ) ≠ 0,
  {
    rw nat.cast_ne_zero,
    refine ne_zero_of_lt n_pos,
  },
  have am_weighted := am_weighted_avg f s1_nonempty s2_nonempty h_disj,
  rw s1_card at am_weighted,
  rw s2_card at am_weighted,
  rw ←two_mul at am_weighted,
  rw ←mul_assoc at am_weighted,
  rw ←right_distrib at am_weighted,
  simp only [mul_eq_mul_right_iff, nat.cast_eq_zero] at am_weighted,
  cases am_weighted,
  swap,
  simp only [ne.def, nat.cast_eq_zero] at n_nonzero,
  refine false.elim(n_nonzero am_weighted),
  refine am_weighted,
end

lemma gm_prod {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) {s1 s2 : finset ℕ} {n : ℕ} 
(s1_card : s1.card = n) (s2_card : s2.card = n) (h_disj : disjoint s1 s2) (n_pos : 0 < n) :
finset_gm f s1 * finset_gm f s2 = (finset_gm f (s1 ∪ s2)) ^ (2 : ℝ) :=

begin
  have s1_nonempty : s1 ≠ ∅,
  {
    rw ←s1_card at n_pos,
    have s1_nonempty_keyword := finset.card_pos.1 n_pos,
    refine finset.nonempty_iff_ne_empty.1 s1_nonempty_keyword,
  },
  have s2_nonempty : s2 ≠ ∅,
  {
    rw ←s2_card at n_pos,
    have s2_nonempty_keyword := finset.card_pos.1 n_pos,
    refine finset.nonempty_iff_ne_empty.1 s2_nonempty_keyword,
  },
  have real_n_nonzero : (n : ℝ) ≠ 0,
  {
    rw nat.cast_ne_zero,
    refine ne_zero_of_lt n_pos,
  },
  have s1_gm_nneg := gm_nneg f_nneg s1,
  have s2_gm_nneg := gm_nneg f_nneg s2,
  have union_gm_nneg := gm_nneg f_nneg (s1 ∪ s2),
  have gm_weighted := gm_weighted_avg f_nneg s1_nonempty s2_nonempty h_disj,
  rw s1_card at gm_weighted,
  rw s2_card at gm_weighted,
  rw ←two_mul at gm_weighted,
  
  rw ←real.coe_to_nnreal (finset_gm f s1) s1_gm_nneg at gm_weighted,
  rw ←real.coe_to_nnreal (finset_gm f s2) s2_gm_nneg at gm_weighted,
  rw ←real.coe_to_nnreal (finset_gm f (s1 ∪ s2)) union_gm_nneg at gm_weighted,
  rw ←nnreal.coe_rpow at gm_weighted,
  rw ←nnreal.coe_rpow at gm_weighted,
  rw ←nnreal.coe_rpow at gm_weighted,
  rw ←nnreal.coe_mul at gm_weighted,
  rw ←nnreal.mul_rpow at gm_weighted,
  rw nnreal.rpow_mul at gm_weighted,
  rw nnreal.coe_eq at gm_weighted,

  rw nnreal.rpow_eq_rpow_iff real_n_nonzero at gm_weighted,

  rw ←nnreal.coe_eq at gm_weighted,
  rw nnreal.coe_mul at gm_weighted,
  rw nnreal.coe_rpow at gm_weighted,
  rw real.coe_to_nnreal (finset_gm f s1) s1_gm_nneg at gm_weighted,
  rw real.coe_to_nnreal (finset_gm f s2) s2_gm_nneg at gm_weighted,
  rw real.coe_to_nnreal (finset_gm f (s1 ∪ s2)) union_gm_nneg at gm_weighted,
  
  refine gm_weighted,
end

lemma sum_equiv {f g : ℕ → ℝ} {s : finset ℕ} 
(f_g_equiv : ∀ (k : ℕ), k ∈ s → f k = g k) :
∑ (i : ℕ) in s, f i = ∑ (i : ℕ) in s, g i := 

begin
  have induct_on_card : ∀ (n : ℕ), ∀ (t : finset ℕ), t.card = n → 
  (∀ (k : ℕ), k ∈ t → f k = g k) → 
  ∑ (i : ℕ) in t, f i = ∑ (i : ℕ) in t, g i,
  {
    intro n,
    induction n with k hk,
    {
      intro t,
      intro t_card,
      intro f_g_equiv_in_t,
      have t_empty := finset.card_eq_zero.1 t_card,
      rw t_empty,
      rw finset.sum_empty,
      rw finset.sum_empty,
    },
    {
      intro t,
      intro t_card,
      intro f_g_equiv_in_t,
      have t_card_pos := nat.succ_pos k,
      rw ←t_card at t_card_pos,
      have k_le_t_card := le_of_lt (nat.lt_succ_self k),
      rw ←t_card at k_le_t_card,
      rcases finset.exists_smaller_set t k k_le_t_card with ⟨t', t'_sbset, t'_card⟩,
      have sdiff_union_t'_eq_t := finset.sdiff_union_of_subset t'_sbset,
      rw ←sdiff_union_t'_eq_t,
      rw finset.sum_union finset.sdiff_disjoint,
      rw finset.sum_union finset.sdiff_disjoint,
      have sing_card := finset.card_sdiff t'_sbset,
      rw t_card at sing_card,
      rw t'_card at sing_card,
      rw nat.succ_eq_add_one at sing_card,
      rw nat.add_sub_cancel_left at sing_card,
      --
      cases finset.card_eq_one.1 sing_card with l hl,
      rw hl,
      rw finset.sum_singleton,
      rw finset.sum_singleton,
      have f_equiv_g_in_t' : ∀ (k : ℕ), k ∈ t' → f k = g k,
      {
        intro k,
        intro k_in_t',
        have k_in_t := finset.mem_of_subset t'_sbset k_in_t',
        refine f_g_equiv_in_t k k_in_t,
      },
      rw hk t' t'_card f_equiv_g_in_t',
      rw add_left_inj,
      have sing_in_t := finset.subset_union_left {l} t',
      rw ←hl at sing_in_t,
      rw finset.sdiff_union_of_subset t'_sbset at sing_in_t,
      rw hl at sing_in_t,
      have l_in_t := finset.singleton_subset_iff.1 sing_in_t,
      refine f_g_equiv_in_t l l_in_t,  
    },
  },
  have answer := induct_on_card s.card s,
  rw eq_self_iff_true at answer,
  rw forall_true_left at answer,
  refine answer f_g_equiv,
end

lemma prod_equiv {f g : ℕ → ℝ} {s : finset ℕ} 
(f_g_equiv : ∀ (k : ℕ), k ∈ s → f k = g k) :
∏ (i : ℕ) in s, f i = ∏ (i : ℕ) in s, g i := 

begin
  have induct_on_card : ∀ (n : ℕ), ∀ (t : finset ℕ), t.card = n → 
  (∀ (k : ℕ), k ∈ t → f k = g k) → 
  ∏ (i : ℕ) in t, f i = ∏ (i : ℕ) in t, g i,
  {
    intro n,
    induction n with k hk,
    {
      intro t,
      intro t_card,
      intro f_g_equiv_in_t,
      have t_empty := finset.card_eq_zero.1 t_card,
      rw t_empty,
      rw finset.prod_empty,
      rw finset.prod_empty,
    },
    {
      intro t,
      intro t_card,
      intro f_g_equiv_in_t,
      have t_card_pos := nat.succ_pos k,
      rw ←t_card at t_card_pos,
      have k_le_t_card := le_of_lt (nat.lt_succ_self k),
      rw ←t_card at k_le_t_card,
      rcases finset.exists_smaller_set t k k_le_t_card with ⟨t', t'_sbset, t'_card⟩,
      have sdiff_union_t'_eq_t := finset.sdiff_union_of_subset t'_sbset,
      rw ←sdiff_union_t'_eq_t,
      rw finset.prod_union finset.sdiff_disjoint,
      rw finset.prod_union finset.sdiff_disjoint,
      have sing_card := finset.card_sdiff t'_sbset,
      rw t_card at sing_card,
      rw t'_card at sing_card,
      rw nat.succ_eq_add_one at sing_card,
      rw nat.add_sub_cancel_left at sing_card,
      --
      cases finset.card_eq_one.1 sing_card with l hl,
      rw hl,
      rw finset.prod_singleton,
      rw finset.prod_singleton,
      have f_equiv_g_in_t' : ∀ (k : ℕ), k ∈ t' → f k = g k,
      {
        intro k,
        intro k_in_t',
        have k_in_t := finset.mem_of_subset t'_sbset k_in_t',
        refine f_g_equiv_in_t k k_in_t,
      },
      rw hk t' t'_card f_equiv_g_in_t',
      rw mul_eq_mul_right_iff,
      left, 
      have sing_in_t := finset.subset_union_left {l} t',
      rw ←hl at sing_in_t,
      rw finset.sdiff_union_of_subset t'_sbset at sing_in_t,
      rw hl at sing_in_t,
      have l_in_t := finset.singleton_subset_iff.1 sing_in_t,
      refine f_g_equiv_in_t l l_in_t,  
    },
  },
  have answer := induct_on_card s.card s,
  rw eq_self_iff_true at answer,
  rw forall_true_left at answer,
  refine answer f_g_equiv,
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
  rw am_gm_prop,
  intro s,
  intro s_card,
  rcases finset.card_eq_two.1 s_card with ⟨x, y, x_y_distinct, hxy⟩,
  rw finset_gm,
  rw finset_am,
  rw s_card,
  rw hxy,
  have x_ne_y : x ≠ y,
  {
    sorry,
  },
  have s1_sum_over_two_els := finset.sum_card_two f x_ne_y,
  have s1_prod_over_two_els := finset.prod_card_two f x_ne_y,
  rw s1_sum_over_two_els,
  rw s1_prod_over_two_els,
  simp only [nat.cast_bit0, nat.cast_one],
  refine am_gm_two' (f_nneg x) (f_nneg y),
end

lemma am_gm_doubling {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), (0 ≤ f k)) : 
∀ (n : ℕ), am_gm_prop f n → am_gm_prop f (2 * n) :=

begin
  intro n,
  cases em(0 < n) with n_pos n_not_pos,
  swap, 
  have n_eq_zero := nat.eq_zero_of_le_zero (le_of_not_lt n_not_pos),
  rw n_eq_zero,
  rw mul_zero,
  intro answer,
  refine answer,
  intro am_gm_prop_n,
  rw am_gm_prop at am_gm_prop_n,
  rw am_gm_prop,
  intro s,
  intro s_card,
  rcases finset.split_in_half s n s_card with ⟨s1, s2, s1_subset, s2_subset, s1_card, s2_card, s1_s2_disjoint, s_eq_s1_union_s2⟩,
  rw ←finset.disjoint_iff_inter_eq_empty at s1_s2_disjoint,
  have s1_nonempty : s1 ≠ ∅,
  {
    rw ←s1_card at n_pos,
    have s1_nonempty_keyword := finset.card_pos.1 n_pos,
    refine finset.nonempty_iff_ne_empty.1 s1_nonempty_keyword,
  },
  have s2_nonempty : s2 ≠ ∅,
  {
    rw ←s2_card at n_pos,
    have s2_nonempty_keyword := finset.card_pos.1 n_pos,
    refine finset.nonempty_iff_ne_empty.1 s2_nonempty_keyword,
  },
  have s_nonempty : s ≠ ∅,
  {
    have zero_lt_two_n := add_lt_add n_pos n_pos,
    rw zero_add at zero_lt_two_n,
    rw ←two_mul at zero_lt_two_n,
    rw ←s_card at zero_lt_two_n,
    have s_nonempty_keyword := finset.card_pos.1 zero_lt_two_n,
    refine finset.nonempty_iff_ne_empty.1 s_nonempty_keyword,
  },
  have am_gm_s1 := am_gm_prop_n s1 s1_card,
  have am_gm_s2 := am_gm_prop_n s2 s2_card,
  have sum := add_le_add am_gm_s1 am_gm_s2,
  rw am_add f s1_card s2_card s1_s2_disjoint n_pos at sum,
  rw ←s_eq_s1_union_s2 at sum,
  have half_le_half := le_refl (1 / (2 : ℝ)),
  have one_half_nneg : 0 ≤ (1 / (2 : ℝ)),
  {
    simp only [one_div, inv_nonneg, zero_le_bit0, zero_le_one],
  },
  have two_am_nneg : 0 ≤ finset_am f s * 2,
  {
    have am_nneg := am_nneg f_nneg s s_nonempty,
    have answer := add_le_add am_nneg am_nneg,
    rw zero_add at answer,
    rw ←mul_two at answer,
    refine answer,
  },
  have sum_div_two := mul_le_mul sum half_le_half one_half_nneg two_am_nneg,
  rw mul_one_div at sum_div_two,
  rw ←mul_div_assoc at sum_div_two,
  rw mul_one at sum_div_two,
  rw mul_div_cancel at sum_div_two,
  swap,
  refine two_ne_zero,
  have meta_am_gm := am_gm_two' (gm_nneg f_nneg s1) (gm_nneg f_nneg s2),
  have answer := le_trans meta_am_gm sum_div_two,
  rw gm_prod f_nneg s1_card s2_card s1_s2_disjoint n_pos at answer,
  rw ←real.rpow_mul (gm_nneg f_nneg (s1 ∪ s2)) at answer,
  rw ←mul_div_assoc at answer,
  rw mul_one at answer,
  rw div_self at answer,
  swap,
  refine two_ne_zero,
  rw real.rpow_one at answer,
  rw ←s_eq_s1_union_s2 at answer,
  refine answer,
end

lemma am_gm_pred {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), (0 ≤ f k)) : 
∀ (n : ℕ), am_gm_prop f (n + 1) → am_gm_prop f n :=

begin
  --DEAL WITH am_gm_prop 0 = false
--set f' : ℕ → ℝ := λ m, if m < n then f n else 1,
  have restating : ∀ (f : ℕ → ℝ), (∀ (k : ℕ), 0 ≤ f k) → 
  ∀ (n : ℕ), am_gm_prop f (n + 1) → am_gm_prop f n,
  {
    intro n,
    -- intro am_gm_prop_succ_n,
    -- rw am_gm_prop,
    -- intro s,
    -- intro s_card,
    -- have s_nonmem := finset.exists_nonmem s,
    -- cases s_nonmem with l hl,
    -- have l_disj := finset.disjoint_singleton_right.2 hl,
    -- have s'_card := finset.card_disjoint_union l_disj,
    -- rw s_card at s'_card,
    -- rw finset.card_singleton l at s'_card,
    -- rw am_gm_prop at am_gm_prop_succ_n,
    -- have answer := am_gm_prop_succ_n (s ∪ {l}) s'_card,
    -- rw finset_am at answer,
    -- rw s'_card at answer,
    -- rw finset.sum_union l_disj at answer,
    -- rw finset.sum_singleton at answer,
    -- set f' : ℕ → ℝ := λ x, if x ∈ s then f x else (finset_am f s) with f'_def,
    -- have f_equiv_f' : ∀ (k : ℕ), k ∈ s → f k = f' k,
    -- {
    --   intro k,
    --   intro k_in_s,
    --   rw f'_def,
    --   sorry,
    -- },
    -- have sum_eq := sum_equiv f_equiv_f',
    -- have prod_eq := prod_equiv f_equiv_f',
    sorry,
  },
  intro n,
  intro am_gm_prop_succ_n,
  refine restating f f_nneg n am_gm_prop_succ_n,

  --rw prop_equiv 

--   PLAN
-- Assume P(n) and get s of card n - 1.
-- Take some x ∉ s, add make s' = s ∪ {x}
-- Set f x = am s'
-- use P(n) on s' 
-- PROFIT
-- 
-- 
-- 
--   
end

theorem am_gm' {f : ℕ → ℝ} (f_nneg : (∀ (k : ℕ), 0 ≤ f k)) {n : ℕ} (n_pos : 0 < n): 
am_gm_prop f n :=
begin
  have base_case := am_gm_two f_nneg,
  have pred_step := am_gm_pred f_nneg, 
  have doubling_step := am_gm_doubling f_nneg,
  have two_lt_zero : 0 < 2,
  {
    simp only [nat.succ_pos'],
  },
  refine cauchy_induction pred_step doubling_step two_lt_zero base_case n,
end

theorem am_gm {f : ℕ → ℝ} {s : finset ℕ} (s_nonempty : 0 < s.card) (f_nneg : (∀ (k : ℕ), 0 ≤ f k)):
finset_gm f s ≤ finset_am f s := 

begin
  have answer := am_gm' f_nneg s_nonempty,
  rw am_gm_prop at answer,
  have reflexivity : s.card = s.card, 
  {
    refl,
  },
  refine answer s reflexivity,
end