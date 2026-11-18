import APC.Partition

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

def aggregateWeights {I : Type*} (w p : I → ℝ) (m : ℕ) (sample : Draws I m) (i : I) : ℝ :=
  ∑ j,if drawIndex m sample j=i then sampledWeights w p m sample j else 0

theorem aggregateWeights_nonneg {I : Type*} (w p : I → ℝ)
    (hw : ∀ i,0≤w i) (hp : ∀ i,0≤p i) (m : ℕ) (sample : Draws I m) :
    ∀ i,0≤aggregateWeights w p m sample i := by
  intro i
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact sampledWeights_nonneg w p hw hp m sample j
  · exact le_rfl

theorem aggregate_evaluate {I : Type*} [Fintype I]
    (w p f : I → ℝ) (m : ℕ) (sample : Draws I m) :
    (∑ i,aggregateWeights w p m sample i*f i)=importanceEstimate p (fun i=>w i*f i) m sample := by
  unfold aggregateWeights
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold importanceEstimate
  rw [drawSum_eq_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [sampledWeights]
  ring

theorem aggregate_cost {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K] [PseudoMetricSpace X]
    (x : I → X) (w p : I → ℝ) (m : ℕ) (sample : Draws I m) (s : K → X) :
    cost x (aggregateWeights w p m sample) s=
      cost (sampledPoints x m sample) (sampledWeights w p m sample) s := by
  rw [sampled_cost_eq]
  exact aggregate_evaluate w p (fun i=>pointCost s (x i)) m sample

theorem aggregate_groupMass {I K : Type*} [Fintype I]
    (w p : I → ℝ) (a : I → K) (j : K) (m : ℕ) (sample : Draws I m) :
    groupMass (aggregateWeights w p m sample) a j=importanceEstimate p (fiberWeight w a j) m sample := by
  have h := aggregate_evaluate w p (fun i=>if a i=j then 1 else 0) m sample
  simpa only [groupMass,fiberWeight,mul_ite,mul_one,mul_zero] using h

theorem aggregate_groupCost {I K : Type*} [Fintype I]
    (w p c : I → ℝ) (a : I → K) (j : K) (m : ℕ) (sample : Draws I m) :
    groupMass (fun i=>aggregateWeights w p m sample i*c i) a j=
      importanceEstimate p (fiberWeight (fun i=>w i*c i) a j) m sample := by
  have h := aggregate_evaluate w p (fun i=>if a i=j then c i else 0) m sample
  simpa only [groupMass,fiberWeight,mul_ite,mul_zero] using h

theorem importanceEstimate_div {I : Type*} (p f : I → ℝ) (z : ℝ) (m : ℕ) (sample : Draws I m) :
    importanceEstimate p (fun i=>f i/z) m sample=importanceEstimate p f m sample/z := by
  have h := importanceEstimate_smul p f z⁻¹ m sample
  simpa only [div_eq_mul_inv,mul_comm] using h

theorem normalized_residual_error {I : Type*} [Fintype I]
    (w p r : I → ℝ) (C : ℝ) (m : ℕ) (sample : Draws I m) :
    importanceEstimate p (fun i=>w i*r i/C) m sample-(∑ i,w i*r i/C)=
      (∑ i,(aggregateWeights w p m sample i-w i)*r i)/C := by
  rw [importanceEstimate_div,← Finset.sum_div,← sub_div,← aggregate_evaluate w p r m sample]
  congr 1
  simp [sub_mul,Finset.sum_sub_distrib]

end APC
