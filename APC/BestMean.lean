import APC.RandomMean
import APC.Lifting
import APC.Sampler

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

abbrev MeanTrials (I : Type*) (m r : ℕ) := Draws (Draws I m) r

def meanDrawLaw {I : Type*} [Fintype I] [Nonempty I] (v : I → ℝ) (i : I) : ℝ :=
  if mass v=0 then (if i=Classical.arbitrary I then 1 else 0) else v i/mass v

theorem meanDrawLaw_nonneg {I : Type*} [Fintype I] [Nonempty I]
    (v : I → ℝ) (hv : ∀ i,0≤v i) (i : I) : 0≤meanDrawLaw v i := by
  unfold meanDrawLaw
  split_ifs
  · norm_num
  · exact le_rfl
  · exact div_nonneg (hv i) (Finset.sum_nonneg (fun j _=>hv j))

theorem meanDrawLaw_sum {I : Type*} [Fintype I] [Nonempty I]
    (v : I → ℝ) : ∑ i,meanDrawLaw v i=1 := by
  by_cases hz : mass v=0
  · simp [meanDrawLaw,hz]
  · simp only [meanDrawLaw,if_neg hz,← Finset.sum_div]
    exact div_self hz

def meanTrialsWeight {I : Type*} [Fintype I] [Nonempty I]
    (v : I → ℝ) (m r : ℕ) : MeanTrials I m r → ℝ :=
  drawWeight (drawWeight (meanDrawLaw v) m) r

theorem meanTrialsWeight_sum {I : Type*} [Fintype I] [Nonempty I]
    (v : I → ℝ) (m r : ℕ) : ∑ trials,meanTrialsWeight v m r trials=1 :=
  drawWeight_sum _ (drawWeight_sum _ (meanDrawLaw_sum v) m) r

theorem meanTrialsWeight_nonneg {I : Type*} [Fintype I] [Nonempty I]
    (v : I → ℝ) (hv : ∀ i,0≤v i) (m r : ℕ) (trials : MeanTrials I m r) :
    0≤meanTrialsWeight v m r trials :=
  drawWeight_nonneg _ (drawWeight_nonneg _ (meanDrawLaw_nonneg v hv) m) r trials

def bestTrialIndex {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (v : I → ℝ) (m r : ℕ) [NeZero r] (trials : MeanTrials I m r) : Fin r :=
  nearest (fun j : Fin r=>drawMean x m (drawIndex r trials j)) (mean x v)

def bestTrial {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (v : I → ℝ) (m r : ℕ) [NeZero r] (trials : MeanTrials I m r) : Draws I m :=
  drawIndex r trials (bestTrialIndex x v m r trials)

def bestMean {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (v : I → ℝ) (m r : ℕ) [NeZero r] (trials : MeanTrials I m r) : E :=
  drawMean x m (bestTrial x v m r trials)

/-- The selected sampled mean has no larger cluster cost than any trial.
The selection criterion is distance to the cluster's weighted centroid. -/
theorem bestMean_cost_le_trial {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (v : I → ℝ) (hv : ∀ i,0≤v i)
    (m r : ℕ) [NeZero r] (trials : MeanTrials I m r) (j : Fin r) :
    oneCost x v (bestMean x v m r trials)≤oneCost x v (drawMean x m (drawIndex r trials j)) := by
  by_cases hz : mass v=0
  · simp [oneCost_zero_mass x v hv hz]
  · apply closest_mean_cost x v hv hz
    have hn := nearest_le (fun j : Fin r=>drawMean x m (drawIndex r trials j)) (mean x v) j
    have hs := pow_le_pow_left₀ dist_nonneg hn 2
    simpa only [bestMean,bestTrial,bestTrialIndex,dist_eq_norm_sub] using hs

theorem allDraws_iff_indices {Ω : Type*} (bad : Ω → Prop) (r : ℕ) (trials : Draws Ω r) :
    allDraws bad r trials ↔ ∀ j : Fin r,bad (drawIndex r trials j) := by
  induction r with
  | zero => simp [allDraws]
  | succ r ih =>
    rcases trials with ⟨ω,tail⟩
    simp [allDraws,drawIndex,Fin.forall_fin_succ,ih]

/-- Amplified weighted mean-estimation guarantee for the actual selected
trial, including zero-mass and zero-variance clusters. -/
theorem bestMean_failure {I E : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (v : I → ℝ) (hv : ∀ i,0≤v i)
    (m r : ℕ) [NeZero r] (hm : 0<m) (ε : ℝ) (hmε : 3≤(m:ℝ)*ε) :
    eventMass (meanTrialsWeight v m r)
      (fun trials=>(1+ε)*oneCost x v (mean x v)<oneCost x v (bestMean x v m r trials))≤(1/3:ℝ)^r := by
  by_cases hz : mass v=0
  · simp only [oneCost_zero_mass x v hv hz,mul_zero,lt_self_iff_false,eventMass,if_false,Finset.sum_const_zero]
    positivity
  · have hmass : 0<mass v := lt_of_le_of_ne (Finset.sum_nonneg (fun i _=>hv i)) (Ne.symm hz)
    let bad := fun trial : Draws I m=>(1+ε)*oneCost x v (mean x v)<oneCost x v (drawMean x m trial)
    have hsingle : eventMass (drawWeight (meanDrawLaw v) m) bad≤1/3 := by
      have he : meanDrawLaw v=(fun i=>v i/mass v) := by funext i;exact if_neg hz
      rw [he]
      exact random_mean_failure_le_third x v hv hmass m hm ε hmε
    have hb : eventMass (meanTrialsWeight v m r)
        (fun trials=>(1+ε)*oneCost x v (mean x v)<oneCost x v (bestMean x v m r trials))≤
        eventMass (meanTrialsWeight v m r) (allDraws bad r) := by
      apply eventMass_mono _ (meanTrialsWeight_nonneg v hv m r)
      intro trials ht
      apply (allDraws_iff_indices bad r trials).2
      intro j
      exact ht.trans_le (bestMean_cost_le_trial x v hv m r trials j)
    have he : eventMass (meanTrialsWeight v m r) (allDraws bad r)=
        (eventMass (drawWeight (meanDrawLaw v) m) bad)^r := allDraws_mass _ bad r
    rw [he] at hb
    exact hb.trans (pow_le_pow_left₀ (eventMass_nonneg _
      (drawWeight_nonneg _ (meanDrawLaw_nonneg v hv) m) bad) hsingle r)

theorem drawSum_eq_fin_sum {I E : Type*} [AddCommMonoid E]
    (x : I → E) (m : ℕ) (trial : Draws I m) :
    drawSum x m trial=∑ j,x (drawIndex m trial j) := by
  induction m with
  | zero => simp [drawSum]
  | succ m ih =>
    rcases trial with ⟨i,tail⟩
    simp [drawSum,drawIndex,Fin.sum_univ_succ,ih]

theorem drawMean_eq_tupleMean {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (m : ℕ) (trial : Draws I m) :
    drawMean x m trial=tupleMean x m (drawIndex m trial) := by
  simp only [drawMean,tupleMean,drawSum_eq_fin_sum]

end APC
