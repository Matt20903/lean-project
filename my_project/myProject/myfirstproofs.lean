import Std.Data.Nat.Lemmas
import Mathlib.Data.Nat.ModEq

-- some basic inductions

-- summation of (0),1, 3, ..., 2n+1
def summ_odd : Nat → Nat
| Nat.zero => Nat.zero
| (Nat.succ n) => 2 * n + 1 + summ_odd n

-- ... equals n²
theorem summ_odd_eq_square(n : Nat): summ_odd n = n*n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [summ_odd]
    -- applying induction hypothesis
    rw [ih]
    -- Nat rewriting
    repeat rw [Nat.succ_eq_add_one]
    rw [Nat.two_mul]
    rw [Nat.mul_add]
    rw [Nat.add_mul]
    simp
    rw [Nat.add_comm]
    rw [Nat.add_assoc, Nat.add_assoc]


-- n²+n is even
theorem square_plus_id_even(n : Nat): (n*n+n)%2=0 := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    repeat rw [Nat.succ_eq_add_one]
    -- Nat rewriting
    rw [Nat.succ_mul]
    rw [Nat.mul_succ]
    rw [Nat.add_assoc]
    rw [← Nat.two_mul]
    rw [Nat.mul_comm 2]
    rw [Nat.add_mul_mod_self_right]
    -- applying induction hypothesis
    exact ih

-- two_divides_f hepls prooving the gaussian sum
theorem two_divides_f_helper(n : Nat)(h : (n*n+n)%2=0): 2∣(n*n+n) := by
  rw [← Nat.zero_mod 2] at h
  rw [← Nat.ModEq] at h
  rw [Nat.modEq_zero_iff_dvd] at h
  exact h

theorem two_divides_f(n : Nat): 2∣(n*n+n) := by
  apply two_divides_f_helper n (square_plus_id_even n)

--prooving gaussian sum

--summation of (0),1,...,n
def summ: Nat → Nat
| Nat.zero => Nat.zero
| (Nat.succ n) => Nat.succ n + summ n

-- equals (n²+n)/2
theorem gaussian_sum(n : Nat): summ n = (n*n + n)/2 := by
  induction n with
  |zero =>
    rfl
  |succ n ih =>
    rw [summ]
    repeat rw[Nat.succ_eq_add_one]
    -- applying induction hypothesis
    rw [ih]
    -- Nat rewriting
    nth_rewrite 1 [← Nat.mul_div_cancel_left (n+1) (Nat.zero_lt_two)]
    repeat rw [Nat.mul_add]
    rw [← Nat.add_div_of_dvd_left]
    repeat rw [Nat.two_mul]
    repeat rw [Nat.add_mul]
    rw [Nat.mul_one]
    rw [Nat.add_comm]
    rw [Nat.add_assoc, Nat.add_assoc]
    simp
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
    rw [Nat.add_comm 1]
    -- prooving that 2|n*n + n, so "Nat.add_div_of_dvd_left" is valid
    apply two_divides_f
