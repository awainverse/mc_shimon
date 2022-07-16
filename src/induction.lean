import tactic
import data.nat.basic
import data.real.basic

open_locale classical
noncomputable theory

-- def nat.decreasing_induction {P : ℕ → Sort u_1} (h : Π (n : ℕ), P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n) (hP : P n) :
-- P m

-- theorem nat.lt_two_pow (n : ℕ) :
-- n < 2 ^ n

theorem cauchy_induction {P : ℕ → Prop} (h1 : Π (n : ℕ), P (n + 1) → P n) (h2 : Π (n : ℕ), P n → P (2 * n)) 
{m : ℕ} (hm : 0 < m) (hp : P m) : 
∀ (n : ℕ), P n :=

begin
  intro n,
  have lt_pow_two := nat.lt_two_pow n,
  have le_m_pow_two : n <= 2 ^ n * m,
  {
    have le_pow_two := nat.le_of_lt lt_pow_two,
    have hm' := nat.succ_le_of_lt hm,
    have target_times_one := nat.mul_le_mul le_pow_two hm',
    rw mul_one at target_times_one,
    refine target_times_one,
  },
  have two_pow_k_times_m : (∀ k : ℕ, P (2 ^ k * m)),
  {
    intro k,
    induction k with i hi,
    {
      rw [pow_zero, one_mul],
      refine hp,
    },
    {
      rw [pow_succ, mul_assoc],
      refine h2 (2 ^ i * m) hi,
    },
  },
  have two_pow_n_times_m := two_pow_k_times_m n,
  refine nat.decreasing_induction h1 le_m_pow_two two_pow_n_times_m,
end

noncomputable def func_am (f : ℕ → ℝ) (n : ℕ) :
  ℕ → ℝ
| 0 := 0
| (k + 1) := (k * (func_am k) + f (k + 1)) / (k + 1)

def func_gm (f : ℕ → ℝ) (n : ℕ) :
  ℕ → ℝ 
| 0 := 0
| (k + 1) := (((func_gm k) ^ k) * f (k + 1)) ^ (1 / (k + 1))

lemma gm_le_am_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 
(x * y) ^ (1 / 2) ≤ (x + y) / 2 :=

begin
  set a := x ^ (1 / 2) with a_def,
  set b := y ^ (1 / 2) with b_def,
  have ha := pow_nonneg hx (1 / 2),
  have hb := pow_nonneg hy (1 / 2),
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
  rw [a_def, b_def, ←pow_mul, ←pow_mul] at divided_by_two,
  have cancelation : 1 / 2 * 2 = 1,
  {
    --find way to do this (preferably without needing to make it a subgoal)
    sorry,
  },
  rw [cancelation, pow_one, pow_one, ←mul_pow] at divided_by_two,
  refine divided_by_two,
end

lemma gm_le_am_pred_step {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) :
 ∀ (n : ℕ), 0 < n → 
 func_gm f n ≤ func_am f n → func_gm f (n - 1) ≤ func_am f (n - 1) :=

begin
  intro n,
  intro hn,
  intro am_gm_for_n,
  sorry,
end

lemma gm_le_am_doubling_step {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) :
 ∀ (n : ℕ), func_gm f n ≤ func_am f n → func_gm f (2 * n) ≤ func_am f (2 * n) :=

begin
  intro n,
  intro am_gm_for_n,
  sorry,
end

theorem func_gm_le_am {f : ℕ → ℝ} (f_nneg : ∀ (k : ℕ), 0 ≤ f k) :
 ∀ (n : ℕ), func_gm f n ≤ func_am f n :=

begin
  intro n,
  cases em(n = 0) with eq_zero ne_zero,
  { 
    --should be easy; n = 0 -> am = gm = 0
    sorry,
  },
  {
    --base case (n = 1)
    have base_case : func_gm f 1 ≤ func_am f 1,
    {
      sorry,
    },
    have one_pos : 0 < 1,
    {
      --FIND BETTER WAY
      linarith,
    },
    --

    rw ←ne.def at ne_zero,
    have n_pos := nat.pos_of_ne_zero ne_zero,
    have pred' := gm_le_am_pred_step f_nneg,
    have pred := pred' n n_pos,
    have double := gm_le_am_doubling_step f_nneg,
    have win := cauchy_induction pred double one_pos base_case,
    sorry,
    -- have win := cauchy_induction pred double n_pos
  },
end





