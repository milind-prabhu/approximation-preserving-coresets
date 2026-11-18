import APC.SensitivityDistribution
import APC.Aggregation
import APC.ResidualFamily

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable
variable {I K : Type*} [Fintype I] [Fintype K]

def normalizedGroupLoss (w p : I → ℝ) (a : I → K) (j : K) (i : I) : ℝ :=
  if groupMass w a j=0 then p i else fiberWeight w a j i/groupMass w a j

theorem normalizedGroupLoss_sum (w p : I → ℝ) (a : I → K) (h1 : ∑ i,p i=1) (j : K) :
    ∑ i,normalizedGroupLoss w p a j i=1 := by
  by_cases hz : groupMass w a j=0
  · simp [normalizedGroupLoss,hz,h1]
  · simp only [normalizedGroupLoss,if_neg hz,← Finset.sum_div]
    exact div_self hz

theorem normalizedGroupLoss_nonneg (w p : I → ℝ) (a : I → K)
    (hw : ∀ i,0≤w i) (hp : ∀ i,0≤p i) (j : K) (i : I) :
    0≤normalizedGroupLoss w p a j i := by
  unfold normalizedGroupLoss
  split_ifs
  · exact hp i
  · exact div_nonneg (fiberWeight_nonneg w a hw j i) (groupMass_nonneg w a hw j)

theorem normalizedGroupLoss_bound (w p : I → ℝ) (a : I → K)
    (hw : ∀ i,0≤w i) (hp : ∀ i,0≤p i) (L : ℝ) (hL : 1≤L)
    (hbound : ∀ i,w i≤L*groupMass w a (a i)*p i) (j : K) (i : I) :
    normalizedGroupLoss w p a j i≤L*p i := by
  unfold normalizedGroupLoss
  split_ifs with hz
  · nlinarith only [mul_le_mul_of_nonneg_right hL (hp i)]
  · have hW : 0<groupMass w a j := lt_of_le_of_ne (groupMass_nonneg w a hw j) (Ne.symm hz)
    apply (div_le_iff₀ hW).2
    unfold fiberWeight
    split_ifs with ha
    · have hh := hbound i
      rw [ha] at hh
      nlinarith only [hh]
    · exact mul_nonneg (mul_nonneg (by linarith) (hp i)) hW.le

theorem zero_group_estimate (w p : I → ℝ) (a : I → K) (hw : ∀ i,0≤w i)
    (j : K) (hz : groupMass w a j=0) (m : ℕ) (sample : Draws I m) :
    importanceEstimate p (fiberWeight w a j) m sample=0 := by
  have hzero := groupMass_zero_terms w a hw j hz
  simp [importanceEstimate,drawSum_eq_sum,hzero]

/-- Structural preservation for all clusters, including empty and
zero-cost clusters, from a normalized importance-sampling bound. -/
theorem group_mass_concentration (w p : I → ℝ) (a : I → K)
    (hw : ∀ i,0≤w i) (hp : ∀ i,0<p i) (h1 : ∑ i,p i=1)
    (L ε δ : ℝ) (hL : 1≤L) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hK : 0<Fintype.card K)
    (hbound : ∀ i,w i≤L*groupMass w a (a i)*p i)
    (m : ℕ) (hm : 0<m)
    (hsize : (12*L)*Real.log (2*(Fintype.card K:ℝ)/δ)≤(m:ℝ)*ε^2) :
    eventMass (drawWeight p m)
      (fun sample=>∃ j,ε*groupMass w a j< |importanceEstimate p (fiberWeight w a j) m sample-groupMass w a j|)≤δ := by
  have hb := structural_family_concentration p (normalizedGroupLoss w p a) hp h1
    (normalizedGroupLoss_nonneg w p a hw (fun i=>(hp i).le))
    (normalizedGroupLoss_sum w p a h1) L ε δ (by linarith) hε hε1 hδ hK
    (normalizedGroupLoss_bound w p a hw (fun i=>(hp i).le) L hL hbound) m hm hsize
  apply le_trans (eventMass_mono _ (drawWeight_nonneg p (fun i=>(hp i).le) m) _ _ ?_) hb
  intro sample hs
  obtain ⟨j,hj⟩ := hs
  refine ⟨j,?_⟩
  by_cases hz : groupMass w a j=0
  · rw [zero_group_estimate w p a hw j hz m sample,hz] at hj
    norm_num at hj
  · have hW : 0<groupMass w a j := lt_of_le_of_ne (groupMass_nonneg w a hw j) (Ne.symm hz)
    have he : importanceEstimate p (normalizedGroupLoss w p a j) m sample-1=
        (importanceEstimate p (fiberWeight w a j) m sample-groupMass w a j)/groupMass w a j := by
      have hf : normalizedGroupLoss w p a j=(fun i=>fiberWeight w a j i/groupMass w a j) := by
        funext i
        exact if_neg hz
      rw [hf,importanceEstimate_div]
      field_simp [hz]
    rw [he,abs_div,abs_of_pos hW]
    exact (lt_div_iff₀ hW).2 hj

end APC
