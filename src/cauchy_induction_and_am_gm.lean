import tactic
import data.nat.basic
import data.real.basic

open_locale classical
noncomputable theory

open_locale big_operators
open finset

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

example (n : ℕ) : 2 * (∑ i in range (n + 1), i) = n * (n + 1) :=
begin
  induction n with k hk,
  { --base case
    rw zero_add,
    rw finset.sum_range_one,
    rw mul_zero,
    rw zero_mul,
  },
  { --inductive step
    rw finset.sum_range_succ,
    rw left_distrib,
    rw hk,
    rw nat.succ_eq_add_one,
    rw left_distrib,
    rw left_distrib,
    rw left_distrib,
    rw left_distrib,
    rw right_distrib,
    rw mul_one,
    rw mul_one,
    rw mul_one,
    rw one_mul,
    --find manual way to do it
    ring_nf,
  },
end

def func_am (f : ℕ → ℝ) (n : ℕ) := 
(∑ i in range n, f i) / n

def func_gm (f : ℕ → ℝ) (n : ℕ) := 
(∏ i in range n, f i) ^ (1 / n)

--'s are written weirdly so I can apply the assumption 
--on an arbitrary f (e.g. smaller, twice as large, etc.)

lemma func_am_gm'_pred : ∀ (f : ℕ → ℝ), ∀ (n : ℕ),  
(∀ (k : ℕ), (0 ≤ f k)) → 
func_gm f n ≤ func_am f n → 
func_gm f (n - 1) ≤ func_am f (n - 1) :=

begin
  sorry,
end

lemma func_am_gm'_doubling : ∀ (f : ℕ → ℝ), ∀ (n : ℕ),  
(∀ (k : ℕ), (0 ≤ f k)) → 
func_gm f n ≤ func_am f n → 
func_gm f (2 * n) ≤ func_am f (2 * n) :=

begin
  sorry,
end

lemma func_am_gm' : ∀ (f : ℕ → ℝ), ∀ (n : ℕ),  
(∀ (k : ℕ), (0 ≤ f k)) → func_gm f n ≤ func_am f n :=

begin
  sorry,
end

theorem func_am_gm {f : ℕ → ℝ} (n : ℕ) (f_nneg : (∀ (k : ℕ), 0 ≤ f k)) :
func_gm f n ≤ func_am f n := 

begin
  refine func_am_gm' f n f_nneg,
end