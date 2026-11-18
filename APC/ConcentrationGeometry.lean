import APC.Clustering
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
noncomputable section
namespace APC
variable {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]

def centerDist (s : K → X) (x : X) : ℝ := dist x (s (nearest s x))

theorem centerDist_nonneg (s : K → X) (x : X) : 0 ≤ centerDist s x := dist_nonneg

theorem centerDist_triangle (s : K → X) (x y : X) :
    centerDist s x ≤ dist x y + centerDist s y := by
  exact (nearest_le s x (nearest s y)).trans (dist_triangle x y _)

theorem centerDist_lipschitz (s : K → X) (x y : X) :
    |centerDist s x - centerDist s y| ≤ dist x y := by
  apply abs_le.mpr
  have h₁ := centerDist_triangle s x y
  have h₂ := centerDist_triangle s y x
  rw [dist_comm y x] at h₂
  constructor <;> linarith

/-- Explicit form of Claim A.9(i), avoiding asymptotic notation. -/
theorem pointCost_difference (s : K → X) (x a : X) :
    |pointCost s x - pointCost s a| ≤
      2 * centerDist s x * dist x a + (dist x a)^2 := by
  have h₁ := centerDist_lipschitz s x a
  have h₂ := centerDist_triangle s a x
  rw [dist_comm a x] at h₂
  have hx := centerDist_nonneg s x
  have ha := centerDist_nonneg s a
  have hd : 0 ≤ dist x a := dist_nonneg
  have hm := mul_le_mul_of_nonneg_left h₁ (add_nonneg hx ha)
  have he : |pointCost s x - pointCost s a| =
      (centerDist s x + centerDist s a) * |centerDist s x - centerDist s a| := by
    dsimp [pointCost, centerDist]
    rw [← abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg), ← abs_mul]
    congr 1
    ring
  rw [he]
  nlinarith only [hm, h₂, mul_nonneg hd (sub_nonneg.mpr h₂)]

/-- Squared residual bound needed for Claim A.10's variance estimate. -/
theorem pointCost_difference_sq (s : K → X) (x a : X) :
    (pointCost s x - pointCost s a)^2 ≤
      8 * pointCost s x * (dist x a)^2 + 2 * (dist x a)^4 := by
  have h := pointCost_difference s x a
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hs
  have hc : (centerDist s x)^2 = pointCost s x := rfl
  nlinarith [sq_nonneg (2 * centerDist s x * dist x a - (dist x a)^2)]

/-- Claim A.9(ii), with an explicit constant and no division by ε.
The hypothesis is precisely the definition of a close cluster. -/
theorem close_pointCost_difference (s : K → X) (x a : X) (ε Δ : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hΔ : 0 ≤ Δ)
    (hclose : ε^2 * pointCost s a ≤ Δ) :
    ε * |pointCost s x - pointCost s a| ≤ 2 * (Δ + (dist x a)^2) := by
  have hb := pointCost_difference s a x
  rw [dist_comm a x, abs_sub_comm] at hb
  have hm := mul_le_mul_of_nonneg_left hb hε
  have hy := sq_nonneg (ε * centerDist s a - dist x a)
  have ht := mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg (dist x a))
  change ε^2 * (centerDist s a)^2 ≤ Δ at hclose
  nlinarith only [hm, hy, ht, hclose, hΔ]

/-- Claim A.3 before applying the approximation factor of the proxy A. -/
theorem representative_cost_bound {I : Type*} [Fintype I]
    (x : I → X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (a s : K → X) :
    (∑ i, w i * pointCost s (a (nearest a (x i)))) ≤
      2 * (cost x w a + cost x w s) := by
  have hpoint : ∀ i, pointCost s (a (nearest a (x i))) ≤
      2 * (pointCost a (x i) + pointCost s (x i)) := by
    intro i
    have ht := centerDist_triangle s (a (nearest a (x i))) (x i)
    rw [dist_comm] at ht
    have hn := centerDist_nonneg s (a (nearest a (x i)))
    have hd : 0 ≤ dist (x i) (a (nearest a (x i))) := dist_nonneg
    have hs := centerDist_nonneg s (x i)
    change (centerDist s (a (nearest a (x i))))^2 ≤
      2 * ((centerDist a (x i))^2 + (centerDist s (x i))^2)
    change centerDist s (a (nearest a (x i))) ≤ centerDist a (x i) + centerDist s (x i) at ht
    have hd2 := centerDist_nonneg a (x i)
    nlinarith [sq_nonneg (centerDist a (x i) - centerDist s (x i))]
  calc
    _ ≤ ∑ i, w i * (2*(pointCost a (x i) + pointCost s (x i))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i))
    _ = _ := by
      simp only [mul_add, cost]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end APC
