import APC.Geometry
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image

open scoped BigOperators
noncomputable section
namespace APC

variable {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K]
  [PseudoMetricSpace X]

/-- Ordered center tuples permit repeated centers; the induced objective is
the usual nearest-center k-means cost. -/
def nearest (s : K → X) (x : X) : K :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun j => dist x (s j))
    Finset.univ_nonempty)

theorem nearest_le (s : K → X) (x : X) (j : K) :
    dist x (s (nearest s x)) ≤ dist x (s j) :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun j => dist x (s j)) Finset.univ_nonempty)).2 j (Finset.mem_univ j)

def pointCost (s : K → X) (x : X) : ℝ := dist x (s (nearest s x))^2
def cost (x : I → X) (w : I → ℝ) (s : K → X) : ℝ :=
  ∑ i, w i * pointCost s (x i)

theorem pointCost_le (s : K → X) (x : X) (j : K) :
    pointCost s x ≤ dist x (s j)^2 := by
  exact pow_le_pow_left₀ dist_nonneg (nearest_le s x j) 2

theorem cost_nonneg (x : I → X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (s : K → X) :
    0 ≤ cost x w s :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem cost_le_assigned (x : I → X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s : K → X) (a : I → K) :
    cost x w s ≤ ∑ i, w i * dist (x i) (s (a i))^2 := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (pointCost_le s (x i) (a i)) (hw i))

/-- Rounding each center to its nearest summary point costs at most 4.
The premise is exactly the property computed by nearest-point rounding. -/
theorem metric_rounding (x : I → X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s out : K → X)
    (hround : ∀ j i, dist (s j) (out j) ≤ dist (s j) (x i)) :
    cost x w out ≤ 4 * cost x w s := by
  unfold cost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hdist : dist (x i) (out (nearest s (x i))) ≤
      2 * dist (x i) (s (nearest s (x i))) := by
    have htri := dist_triangle (x i) (s (nearest s (x i))) (out (nearest s (x i)))
    have hr := hround (nearest s (x i)) i
    rw [dist_comm (s (nearest s (x i))) (x i)] at hr
    linarith
  have hs := pow_le_pow_left₀ dist_nonneg hdist 2
  have hp := (pointCost_le out (x i) (nearest s (x i))).trans hs
  have hh := mul_le_mul_of_nonneg_left hp (hw i)
  dsimp [pointCost] at hh ⊢
  nlinarith [hh]

end APC
