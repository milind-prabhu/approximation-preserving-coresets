import APC.GlobalError
import APC.StructuralSampling

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable
variable {I K Q X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [Fintype Q] [PseudoMetricSpace X]

/-- Global finite-family sensitivity-sampling concentration. The probability
distribution, its normalization/lower bounds, structural events, close/far
geometry, and union bounds are all proved in the dependency chain.
Only the proxy approximation and explicit sample-size inequalities are
premises. Empty/zero-cost proxy clusters and zero-cost queries are covered. -/
theorem sensitivity_finite_family
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0<w i)
    (proxy : K → X) (solutions : Q → K → X) (a ε δ : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hQ : 0<Fintype.card Q)
    (happrox : ∀ q,cost x w proxy≤a*cost x w (solutions q))
    (m : ℕ) (hm : 0<m)
    (hstructSize : (48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ)≤(m:ℝ)*ε^2)
    (hresidualSize : (4*(64*a+8*a^2))*Real.log (4*(Fintype.card Q:ℝ)/δ)≤(m:ℝ)*ε^2) :
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun sample=>∃ q,
      (23+22*a)*ε*cost x w (solutions q)<
        |cost (sampledPoints x m sample) (sampledWeights w p m sample) (solutions q)-cost x w (solutions q)|)≤δ := by
  let f : I → K := fun i=>nearest proxy (x i)
  let c : I → ℝ := fun i=>pointCost proxy (x i)
  let p := sensitivityProbability w c f
  let Δ := clusterDelta w c f
  let loss : Q → I → ℝ := fun q=>normalizedResidual w
    (closeResidual x proxy (solutions q) ε Δ) (cost x w (solutions q))
  have hw0 : ∀ i,0≤w i := fun i=>(hw i).le
  have hc : ∀ i,0≤c i := fun i=>sq_nonneg _
  have hp : ∀ i,0<p i := sensitivityProbability_pos w c f hw hc
  have h1 : ∑ i,p i=1 := sensitivityProbability_sum w c f hw
  have hK : 0<Fintype.card K := Fintype.card_pos
  have hkR : (1:ℝ)≤Fintype.card K := by exact_mod_cast hK
  have hΔ : ∀ i,0≤Δ i := fun i=>div_nonneg
    (groupMass_nonneg _ f (fun i=>mul_nonneg (hw0 i) (hc i)) _)
    (groupMass_nonneg w f hw0 _)
  have hglobal : ∀ i,w i*c i≤4*cost x w proxy*p i := sensitivity_global_cost_lower w c f hw hc
  have hdelta : ∀ i,w i*Δ i≤4*cost x w proxy*p i := sensitivity_delta_lower w c f hw hc
  have hrange : ∀ q i,|loss q i|≤(16*a/ε)*p i := by
    intro q
    by_cases hz : cost x w (solutions q)=0
    · intro i
      dsimp [loss,normalizedResidual]
      rw [hz,div_zero,abs_zero]
      exact mul_nonneg (by positivity) (hp i).le
    · exact residual_range w (closeResidual x proxy (solutions q) ε Δ) c Δ p
        (cost x w (solutions q)) (cost x w proxy) a ε hw0
        (lt_of_le_of_ne (cost_nonneg x w hw0 _) (Ne.symm hz)) hε (happrox q)
        hglobal hdelta (fun i=>(hp i).le)
        (closeResidual_range x proxy (solutions q) ε Δ hε.le hε1 hΔ)
  have hsecond : ∀ q,∑ i,(loss q i)^2/p i≤32*a+8*a^2 := by
    intro q
    by_cases hz : cost x w (solutions q)=0
    · simp only [loss,normalizedResidual,hz,div_zero,zero_pow (by norm_num : 2≠0),zero_div,Finset.sum_const_zero]
      positivity
    · exact residual_second_moment w (closeResidual x proxy (solutions q) ε Δ)
        (fun i=>pointCost (solutions q) (x i)) c p
        (cost x w (solutions q)) (cost x w proxy) a hw0 (fun i=>sq_nonneg _) hc hp
        (lt_of_le_of_ne (cost_nonneg x w hw0 _) (Ne.symm hz)) (cost_nonneg x w hw0 proxy) ha.le
        rfl rfl (happrox q) hglobal (closeResidual_square x proxy (solutions q) ε Δ)
  let massBad := fun sample : Draws I m=>∃ j,ε*groupMass w f j<
    |importanceEstimate p (fiberWeight w f j) m sample-groupMass w f j|
  let costBad := fun sample : Draws I m=>∃ j,ε*groupMass (fun i=>w i*c i) f j<
    |importanceEstimate p (fiberWeight (fun i=>w i*c i) f j) m sample-groupMass (fun i=>w i*c i) f j|
  let residualBad := fun sample : Draws I m=>∃ q,ε< |importanceEstimate p (loss q) m sample-∑ i,loss q i|
  have hsizeS : (12*(4*(Fintype.card K:ℝ)))*Real.log (2*(Fintype.card K:ℝ)/(δ/4))≤(m:ℝ)*ε^2 := by
    have he : 2*(Fintype.card K:ℝ)/(δ/4)=8*(Fintype.card K:ℝ)/δ := by ring
    rw [he]
    convert hstructSize using 1 <;> ring
  have hmassProb : eventMass (drawWeight p m) massBad≤δ/4 :=
    group_mass_concentration w p f hw0 hp h1 (4*(Fintype.card K:ℝ)) ε (δ/4)
      (by linarith) hε hε1 (by positivity) hK (sensitivity_weight_lower w c f hw hc) m hm hsizeS
  have hcostProb : eventMass (drawWeight p m) costBad≤δ/4 :=
    group_mass_concentration (fun i=>w i*c i) p f (fun i=>mul_nonneg (hw0 i) (hc i)) hp h1
      (4*(Fintype.card K:ℝ)) ε (δ/4) (by linarith) hε hε1 (by positivity) hK
      (sensitivity_local_cost_lower w c f hw hc) m hm hsizeS
  have hsizeR : (4*(64*a+8*a^2))*Real.log (2*(Fintype.card Q:ℝ)/(δ/2))≤(m:ℝ)*ε^2 := by
    have he : 2*(Fintype.card Q:ℝ)/(δ/2)=4*(Fintype.card Q:ℝ)/δ := by ring
    rw [he]
    exact hresidualSize
  have hresProb : eventMass (drawWeight p m) residualBad≤δ/2 :=
    residual_family_concentration p loss hp h1 a ε (δ/2) ha hε (by positivity)
      hQ hrange hsecond m hm hsizeR
  have hcontain : ∀ sample, (∃ q,(23+22*a)*ε*cost x w (solutions q)<
      |cost (sampledPoints x m sample) (sampledWeights w p m sample) (solutions q)-cost x w (solutions q)|) →
      massBad sample ∨ costBad sample ∨ residualBad sample := by
    intro sample hs
    by_cases hM : massBad sample
    · exact Or.inl hM
    by_cases hA : costBad sample
    · exact Or.inr (Or.inl hA)
    by_cases hR : residualBad sample
    · exact Or.inr (Or.inr hR)
    obtain ⟨q,hq⟩ := hs
    by_cases hz : cost x w (solutions q)=0
    · rw [sampled_zero_cost x w p hw0 (solutions q) hz m sample,hz] at hq
      norm_num at hq
    have hC : 0<cost x w (solutions q) := lt_of_le_of_ne (cost_nonneg x w hw0 _) (Ne.symm hz)
    let v := aggregateWeights w p m sample
    have hv := aggregateWeights_nonneg w p hw0 (fun i=>(hp i).le) m sample
    have hMgood : ∀ j,|groupMass v f j-groupMass w f j|≤ε*groupMass w f j := by
      intro j
      rw [aggregate_groupMass]
      exact le_of_not_gt (fun hj=>hM ⟨j,hj⟩)
    have hAgood : ∀ j,groupMass (fun i=>v i*c i) f j≤(1+ε)*groupMass (fun i=>w i*c i) f j := by
      intro j
      rw [aggregate_groupCost]
      have hb := le_of_not_gt (fun hj=>hA ⟨j,hj⟩)
      have hu := (abs_le.mp hb).2
      nlinarith only [hu]
    have hRgood : |∑ i,(v i-w i)*closeResidual x proxy (solutions q) ε Δ i|≤ε*cost x w (solutions q) := by
      have hb := le_of_not_gt (fun hj=>hR ⟨q,hj⟩)
      change |importanceEstimate p (fun i=>w i*closeResidual x proxy (solutions q) ε Δ i/cost x w (solutions q)) m sample-
        ∑ i,w i*closeResidual x proxy (solutions q) ε Δ i/cost x w (solutions q)|≤ε at hb
      rw [normalized_residual_error,abs_div,abs_of_pos hC] at hb
      exact (div_le_iff₀ hC).mp hb
    have hb := global_cost_error x w v proxy (solutions q) hw0 hv a ε hε hε1
      (happrox q) hMgood hAgood hRgood
    rw [aggregate_cost] at hb
    exact False.elim (not_lt_of_ge hb hq)
  have hmono := eventMass_mono (drawWeight p m) (drawWeight_nonneg p (fun i=>(hp i).le) m) _ _ hcontain
  have hU₁ := eventMass_or_le (drawWeight p m) (drawWeight_nonneg p (fun i=>(hp i).le) m) massBad
    (fun sample=>costBad sample ∨ residualBad sample)
  have hU₂ := eventMass_or_le (drawWeight p m) (drawWeight_nonneg p (fun i=>(hp i).le) m) costBad residualBad
  change eventMass (drawWeight p m) _≤δ
  linarith only [hmono,hU₁,hU₂,hmassProb,hcostProb,hresProb]

end APC
