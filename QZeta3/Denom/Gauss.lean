import QZeta3.Denom.Laurent

/-!
# Gaussian binomials

`gauss n k ∈ ℤ[X]` is the Gaussian binomial `[n, k]_X`, defined by the q-Pascal recursion
`[n+1, k+1] = [n, k] + X^{k+1} [n, k+1]`. The identity used later is
`(x;x)_k (x;x)_m [k+m, k](x) = (x;x)_{k+m}` (`gauss_mul`), where `(x;x)_m = qPoch x x m`.
-/

open Polynomial Finset

namespace QZeta3.Denom

/-- The Gaussian binomial `[n, k]_X`. -/
noncomputable def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gauss n k + X ^ (k + 1) * gauss n (k + 1)

theorem gauss_zero_right (n : ℕ) : gauss n 0 = 1 := by
  cases n <;> rfl

theorem gauss_succ_succ (n k : ℕ) :
    gauss (n + 1) (k + 1) = gauss n k + X ^ (k + 1) * gauss n (k + 1) := rfl

theorem gauss_eq_zero_of_lt : ∀ n k : ℕ, n < k → gauss n k = 0
  | n, 0, h => absurd h (Nat.not_lt_zero n)
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [gauss_succ_succ, gauss_eq_zero_of_lt n k (by omega),
      gauss_eq_zero_of_lt n (k + 1) (by omega)]
    simp

theorem qPoch_eq_prod (x : ℝ) (m : ℕ) : qPoch x x m = ∏ i ∈ range m, (1 - x ^ (i + 1)) := by
  unfold qPoch
  exact prod_congr rfl fun i _ => by rw [pow_succ']

theorem qPoch_succ (x : ℝ) (m : ℕ) : qPoch x x (m + 1) = qPoch x x m * (1 - x ^ (m + 1)) := by
  rw [qPoch_eq_prod, qPoch_eq_prod, prod_range_succ]

theorem qPoch_add (x : ℝ) (a b : ℕ) :
    qPoch x x (a + b) = qPoch x x a * ∏ i ∈ range b, (1 - x ^ (a + 1 + i)) := by
  rw [qPoch_eq_prod, qPoch_eq_prod, prod_range_add]
  congr 1
  exact prod_congr rfl fun i _ => by rw [show a + i + 1 = a + 1 + i by omega]

theorem qPoch_ne_zero {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) (m : ℕ) : qPoch x x m ≠ 0 := by
  rw [qPoch_eq_prod]
  exact prod_ne_zero_iff.2 fun i _ => one_sub_pow_ne_zero hx hx1 (by omega)

theorem gauss_mul_aux (x : ℝ) : ∀ N k m : ℕ, k + m = N →
    qPoch x x k * qPoch x x m * Polynomial.aeval x (gauss N k) = qPoch x x N := by
  intro N
  induction N with
  | zero =>
    intro k m h
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ m = 0 := by omega
    simp [gauss_zero_right, qPoch]
  | succ N ih =>
    intro k m h
    rcases k with _ | k
    · obtain rfl : m = N + 1 := by omega
      simp [gauss_zero_right, qPoch]
    · rw [gauss_succ_succ]
      simp only [map_add, map_mul, map_pow, aeval_X]
      have h1 := ih k m (by omega)
      rcases m with _ | m
      · obtain rfl : k = N := by omega
        rw [gauss_eq_zero_of_lt k (k + 1) (by omega), qPoch_succ x k]
        simp only [map_zero, mul_zero, add_zero]
        linear_combination (1 - x ^ (k + 1)) * h1
      · have h2 := ih (k + 1) m (by omega)
        rw [qPoch_succ x k] at h2 ⊢
        rw [qPoch_succ x m] at h1 ⊢
        rw [qPoch_succ x N]
        have hN : x ^ (k + 1) * x ^ (m + 1) = x ^ (N + 1) := by
          rw [← pow_add, show k + 1 + (m + 1) = N + 1 by omega]
        linear_combination (1 - x ^ (k + 1)) * h1 + x ^ (k + 1) * (1 - x ^ (m + 1)) * h2 +
          (-qPoch x x N) * hN

/-- `(x;x)_k (x;x)_m [k+m, k](x) = (x;x)_{k+m}`. -/
theorem gauss_mul (x : ℝ) (k m : ℕ) :
    qPoch x x k * qPoch x x m * Polynomial.aeval x (gauss (k + m) k) = qPoch x x (k + m) :=
  gauss_mul_aux x (k + m) k m rfl

end QZeta3.Denom
