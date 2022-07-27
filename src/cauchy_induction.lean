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