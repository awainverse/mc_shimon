import tactic
import data.nat.basic
import data.real.basic
open_locale classical
noncomputable theory


-- def nat.decreasing_induction {P : ℕ → Sort u_1} (h : Π (n : ℕ), P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n) (hP : P n) :
-- P m

-- theorem nat.lt_two_pow (n : ℕ) :
-- n < 2 ^ n


lemma a_lt_b_if_a_le_b {a b : ℕ} : (a < b) → (a ≤ b) :=
begin 
  intro a_less_b,
  rw le_iff_exists_add,
  rw lt_iff_exists_add at a_less_b,
  cases a_less_b with dif h_dif,
  cases h_dif with dif_pos b_eq_a_add_dif,
  use dif,
  refine b_eq_a_add_dif,
end
-- theorem nat.le_mul_of_pos_right {m n : ℕ} (h : 0 < n) :
-- m ≤ m * n
--can use 0 < m rather than 1 ≤ m bc m : ℕ
lemma multiply_still_le {a b : ℕ} (m : ℕ) (hm : 0 < m): (a ≤ b) → (a ≤ b * m) :=
begin
  intro a,
  rw le_iff_exists_add at a,
  rw le_iff_exists_add,
  cases a with dif h_dif,
  use (m - 1) * a + m * dif,
  rw h_dif,
  rw nat.mul_sub_right_distrib,
  rw nat.right_distrib,
  rw mul_comm,
  rw one_mul,
  rw ←add_assoc (a) (m * a - a) (m * dif),
  have duh : a ≤ m * a,
  {
--         theorem nat.le_mul_of_pos_left {m n : ℕ} (h : 0 < n) :
          -- m ≤ n * m
    --want to multiply by a on both sides of hm and refine that
    sorry,
  },
  rw ←nat.add_sub_assoc duh a,
  rw add_comm a (m * a),
  rw nat.add_sub_cancel (m * a) (a),
  rw mul_comm dif m,
end

theorem cauchy_induction {P : ℕ → Prop} (h1 : Π (n : ℕ), P (n + 1) → P n) (h2 : Π (n : ℕ), P n → P (2 * n)) 
(m : ℕ) (hm : 0 < m) (hp : P m) : 
∀ (n : ℕ), P n :=

begin
  intro n,
  have less_than_pow_two := nat.lt_two_pow n,
  have leq_than_m_pow_two : n <= 2 ^ n * m,
  {
    have leq_than_pow_two := a_lt_b_if_a_le_b less_than_pow_two,
    refine multiply_still_le m hm leq_than_pow_two,
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
 --(h : Π (n : ℕ), P (n + 1) → P n) 
 -- (mn : m ≤ n) (hP : P n) :
 refine nat.decreasing_induction h1 leq_than_m_pow_two two_pow_n_times_m,
end

theorem am_gm {}