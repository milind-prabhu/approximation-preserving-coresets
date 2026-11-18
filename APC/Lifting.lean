import APC.Witnesses
import APC.Transfer

open scoped BigOperators
noncomputable section
namespace APC
variable {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def clusterWeight (w : I → ℝ) (a : I → K) (j : K) (i : I) : ℝ := by
  classical
  exact if a i = j then w i else 0

theorem clusterWeight_nonneg (w : I → ℝ) (a : I → K)
    (hw : ∀ i, 0 ≤ w i) (j : K) : ∀ i, 0 ≤ clusterWeight w a j i := by
  classical
  intro i
  simp only [clusterWeight]
  split_ifs <;> simp_all

theorem cluster_cost_sum (x : I → E) (w : I → ℝ) (a : I → K) (s : K → E) :
    (∑ j, oneCost x (clusterWeight w a j) (s j)) =
      ∑ i, w i * dist (x i) (s (a i))^2 := by
  classical
  simp only [oneCost, clusterWeight, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [dist_eq_norm_sub]

/-- Full geometric lifting statement: from any center tuple, construct a
tuple of means of exactly m summary points with cost increase ≤1+1/m.
This is an existence theorem, not a runtime claim. -/
theorem exists_structured_lift (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (s : K → E) (m : ℕ) (hm : 0 < m) :
    ∃ out : K → E, out ∈ witnessFamily x m ∧
      cost x w out ≤ (1 + (m:ℝ)⁻¹) * cost x w s := by
  classical
  let a : I → K := fun i => nearest s (x i)
  have hc : ∀ j, ∃ f : Fin m → I,
      oneCost x (clusterWeight w a j) (tupleMean x m f) ≤
        (1 + (m:ℝ)⁻¹) * oneCost x (clusterWeight w a j) (s j) := by
    intro j
    let v := clusterWeight w a j
    have hv : ∀ i, 0 ≤ v i := clusterWeight_nonneg w a hw j
    have hmass : 0 ≤ mass v := Finset.sum_nonneg (fun i _ => hv i)
    by_cases hz : mass v = 0
    · refine ⟨fun _ => Classical.arbitrary I, ?_⟩
      rw [oneCost_zero_mass x v hv hz, oneCost_zero_mass x v hv hz, mul_zero]
    · obtain ⟨f, _, hf⟩ := exists_small_mean x v hv (lt_of_le_of_ne hmass (Ne.symm hz)) m hm
      refine ⟨f, hf.trans ?_⟩
      exact mul_le_mul_of_nonneg_left (mean_minimizes x v hv hz (s j))
        (by positivity)
  choose f hf using hc
  let out : K → E := fun j => tupleMean x m (f j)
  refine ⟨out, mem_witnessFamily x m f, ?_⟩
  calc
    cost x w out ≤ ∑ i, w i * dist (x i) (out (a i))^2 := cost_le_assigned x w hw out a
    _ = ∑ j, oneCost x (clusterWeight w a j) (out j) := (cluster_cost_sum x w a out).symm
    _ ≤ ∑ j, (1 + (m:ℝ)⁻¹) * oneCost x (clusterWeight w a j) (s j) :=
      Finset.sum_le_sum (fun j _ => hf j)
    _ = (1 + (m:ℝ)⁻¹) * cost x w s := by
      rw [← Finset.mul_sum, cluster_cost_sum]
      rfl

/-- End-to-end Euclidean approximation guarantee, conditional only on
cost preservation for the finite witness family and the original optimum.
No mean-estimation or lifting hypothesis remains. -/
theorem euclidean_apc_of_preservation
    (x : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (original : (K → E) → ℝ) (opt s : K → E) (α ε : ℝ)
    (hα : 0 ≤ α) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hopt_nonneg : 0 ≤ original opt)
    (happrox : Approximate (cost x w) α s)
    (m : ℕ) (hm : 0 < m) (hmε : (m:ℝ)⁻¹ ≤ ε/10)
    (hpres : ∀ c ∈ witnessFamily (K := K) x m,
      Preserves (original c) (cost x w c) (ε/10))
    (hopt : Preserves (original opt) (cost x w opt) (ε/10)) :
    ∃ out : K → E, out ∈ witnessFamily x m ∧
      original out ≤ α * (1 + ε) * original opt := by
  obtain ⟨out, hout, hcost⟩ := exists_structured_lift x w hw s m hm
  refine ⟨out, hout, ?_⟩
  apply euclidean_transfer_rescaled original (cost x w) s out opt α ε hα hε.le hε1
    hopt_nonneg happrox ?_ (hpres out hout) hopt
  exact hcost.trans (mul_le_mul_of_nonneg_right (by linarith) (cost_nonneg x w hw s))

end APC
