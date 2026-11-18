import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

open scoped BigOperators RealInnerProductSpace

noncomputable section
namespace APC
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def mass (w : I → ℝ) : ℝ := ∑ i, w i
def oneCost (x : I → E) (w : I → ℝ) (c : E) : ℝ :=
  ∑ i, w i * ‖x i - c‖^2
def mean (x : I → E) (w : I → ℝ) : E :=
  (mass w)⁻¹ • ∑ i, w i • x i

theorem oneCost_nonneg (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (c : E) : 0 ≤ oneCost x w c :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem centered_sum (x : I → E) (w : I → ℝ) (hm : mass w ≠ 0) :
    ∑ i, w i • (x i - mean x w) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  change (∑ i, w i • x i) - mass w • ((mass w)⁻¹ • ∑ i, w i • x i) = 0
  rw [smul_smul, mul_inv_cancel₀ hm, one_smul, sub_self]

theorem variance_identity (x : I → E) (w : I → ℝ)
    (hm : mass w ≠ 0) (c : E) :
    oneCost x w c = oneCost x w (mean x w) + mass w * ‖mean x w - c‖^2 := by
  have hz : ∑ i, w i * inner ℝ (x i - mean x w) (mean x w - c) = 0 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner, centered_sum x w hm, inner_zero_left]
  unfold oneCost mass
  calc
    (∑ i, w i * ‖x i - c‖^2) =
        ∑ i, (w i * ‖x i - mean x w‖^2 +
          2 * (w i * inner ℝ (x i - mean x w) (mean x w - c)) +
          w i * ‖mean x w - c‖^2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show x i - c = (x i - mean x w) + (mean x w - c) by abel,
        norm_add_sq_real]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hz, ← Finset.sum_mul]
      ring

theorem mean_minimizes (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : mass w ≠ 0) (c : E) :
    oneCost x w (mean x w) ≤ oneCost x w c := by
  rw [variance_identity x w hm c]
  exact le_add_of_nonneg_right
    (mul_nonneg (Finset.sum_nonneg (fun i _ => hw i)) (sq_nonneg _))

/-- Selecting the trial closest to the weighted mean also selects the least
one-center cost, including the zero-variance case. -/
theorem closest_mean_cost (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : mass w ≠ 0) (a b : E)
    (h : ‖mean x w - a‖^2 ≤ ‖mean x w - b‖^2) :
    oneCost x w a ≤ oneCost x w b := by
  rw [variance_identity x w hm a, variance_identity x w hm b]
  exact add_le_add_left (mul_le_mul_of_nonneg_left h
    (Finset.sum_nonneg (fun i _ => hw i))) _

/-- A zero-mass cluster with nonnegative weights contributes zero cost. -/
theorem oneCost_zero_mass (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : mass w = 0) (c : E) :
    oneCost x w c = 0 := by
  have hz : ∀ i, w i = 0 := by
    intro i
    have : w i ≤ mass w := by
      exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
    exact le_antisymm (hm ▸ this) (hw i)
  simp [oneCost, hz]

end APC
