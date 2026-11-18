import APC.OneCenterMoments
import APC.ImportanceMoments
import APC.SensitivityDistribution

open scoped BigOperators
noncomputable section
namespace APC
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The existing four-component sampler with the exact one-center proxy. -/
def oneCenterProbability (x : I → E) (w : I → ℝ) : I → ℝ :=
  sensitivityProbability w (fun i=>‖x i-mean x w‖^2) (fun _=>Unit.unit)

theorem oneCenterProbability_pos [Nonempty I] (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) : ∀ i,0<oneCenterProbability x w i :=
  sensitivityProbability_pos _ _ _ hw (fun i=>sq_nonneg _)

theorem oneCenterProbability_sum [Nonempty I] (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) : ∑ i,oneCenterProbability x w i=1 :=
  sensitivityProbability_sum _ _ _ hw

theorem oneCenterProbability_bounds [Nonempty I] (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) (i : I) :
    w i≤4*mass w*oneCenterProbability x w i ∧
    w i*‖x i-mean x w‖^2≤4*oneCost x w (mean x w)*oneCenterProbability x w i := by
  have hw' := sensitivity_weight_lower w (fun i=>‖x i-mean x w‖^2)
    (fun _=>Unit.unit) hw (fun i=>sq_nonneg _) i
  have hv' := sensitivity_global_cost_lower w (fun i=>‖x i-mean x w‖^2)
    (fun _=>Unit.unit) hw (fun i=>sq_nonneg _) i
  constructor
  · simpa only [Fintype.card_unique,Nat.cast_one,mul_one,groupMass,fiberWeight,ite_true,mass]
      using hw'
  · exact hv'

theorem sampled_mass_estimator (w p : I → ℝ) (m : ℕ) (z : Draws I m) :
    mass (sampledWeights w p m z)=importanceEstimate p w m z := by
  simp only [mass,sampledWeights,importanceEstimate,drawSum_eq_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sampled_oneCost_estimator (x : I → E) (w p : I → ℝ)
    (m : ℕ) (z : Draws I m) (μ : E) :
    oneCost (sampledPoints x m z) (sampledWeights w p m z) μ=
      importanceEstimate p (fun i=>w i*‖x i-μ‖^2) m z := by
  simp only [oneCost,sampledPoints,sampledWeights,importanceEstimate,drawSum_eq_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorDrawSum_eq_sum (f : I → E) (m : ℕ) (z : Draws I m) :
    drawSum f m z=∑ j,f (drawIndex m z j) := by
  induction m with
  | zero => simp [drawSum]
  | succ m ih =>
    rcases z with ⟨i,tail⟩
    simp [drawSum,drawIndex,Fin.sum_univ_succ,ih]

theorem sampled_centered_vector (x : I → E) (w p : I → ℝ)
    (m : ℕ) (z : Draws I m) (μ : E) :
    (∑ j,sampledWeights w p m z j • (sampledPoints x m z j-μ))=
      vectorImportance p (fun i=>w i • (x i-μ)) m z := by
  unfold vectorImportance
  rw [vectorDrawSum_eq_sum,Finset.smul_sum]
  simp only [sampledWeights,sampledPoints,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The vector moment used by the actual sensitivity sampler is bounded
without a dimension factor. -/
theorem oneCenter_vector_mse [Nonempty I] (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) (hM : 0<mass w) (m : ℕ) (hm : 0<m) :
    (∑ z,drawWeight (oneCenterProbability x w) m z*
      ‖vectorImportance (oneCenterProbability x w) (fun i=>w i • (x i-mean x w)) m z‖^2)≤
      4*mass w*oneCost x w (mean x w)/(m:ℝ) := by
  let p := oneCenterProbability x w
  have hp := oneCenterProbability_pos x w hw
  rw [vectorImportance_mse p _ hp (oneCenterProbability_sum x w hw)
    (centered_sum x w (ne_of_gt hM)) m hm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold oneCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  apply (div_le_iff₀ (hp i)).2
  have hb := mul_le_mul_of_nonneg_left (oneCenterProbability_bounds x w hw i).1
    (mul_nonneg (hw i).le (sq_nonneg ‖x i-mean x w‖))
  nlinarith only [hb]

end APC
