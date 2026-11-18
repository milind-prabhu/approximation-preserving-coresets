import APC.MetricSampling

open scoped BigOperators
noncomputable section
namespace APC

/-- Local event required by the iterative finite-metric construction. -/
def MetricStep {I J K X : Type*} [Fintype I] [Fintype J]
    [Fintype K] [Nonempty K] [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (y : J → X) (v : J → ℝ)
    (opt : K → X) (η : ℝ) : Prop :=
  ∀ s, (∀ j, s j ∈ Set.range x) ∨ s=opt →
    Preserves (cost x w s) (cost y v s) η

theorem sampledPoints_range_subset {I X : Type*} (x : I → X) (m : ℕ)
    (z : Draws I m) : Set.range (sampledPoints x m z) ⊆ Set.range x := by
  rintro y ⟨j, rfl⟩
  exact ⟨drawIndex m z j, rfl⟩

theorem sampledWeights_pos {I : Type*} (w p : I → ℝ)
    (hw : ∀ i, 0<w i) (hp : ∀ i, 0<p i) (m : ℕ) (hm : 0<m)
    (z : Draws I m) : ∀ j, 0<sampledWeights w p m z j := by
  intro j
  exact div_pos (hw _) (mul_pos (by exact_mod_cast hm) (hp _))

/-- A range-based form of the checked local concentration theorem, suited
to the recursively changing finite input types. -/
theorem metric_step_kernel
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0<w i)
    (proxy opt : K → X) (a η δ : ℝ)
    (ha : 0<a) (hη : 0<η) (hη1 : η≤1) (hδ : 0<δ)
    (hproxy : Approximate (cost x w) a proxy) :
    let m := metricStageSampleCount (Fintype.card K) (Fintype.card I) a η δ
    let p := sensitivityProbability w (fun i => pointCost proxy (x i)) (fun i => nearest proxy (x i))
    eventMass (drawWeight p m) (fun z =>
      ¬MetricStep x w (sampledPoints x m z) (sampledWeights w p m z) opt η) ≤ δ := by
  classical
  have hb := metric_sampling_stage_explicit x w hw opt proxy a η δ ha hη hη1 hδ hproxy
  let m := metricStageSampleCount (Fintype.card K) (Fintype.card I) a η δ
  let p := sensitivityProbability w (fun i => pointCost proxy (x i)) (fun i => nearest proxy (x i))
  have hp : ∀ i,0≤p i := fun i =>
    (sensitivityProbability_pos w _ _ hw (fun i => sq_nonneg _) i).le
  apply le_trans (eventMass_mono _ (drawWeight_nonneg p hp m) _ _ ?_) hb
  intro z hbad
  by_contra hgood
  apply hbad
  intro s hs
  have hmem : s∈pointWitnessFamily (K:=K) x ∨ s=opt := by
    rcases hs with hs | hs
    · choose f hf using hs
      exact Or.inl ((mem_pointWitnessFamily x s).2 ⟨f,(funext hf).symm⟩)
    · exact Or.inr hs
  exact of_not_not (fun hh => hgood ⟨s,hmem,hh⟩)

theorem metric_step_kernel_budget
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0<w i)
    (proxy opt : K → X) (a η δ : ℝ)
    (ha : 0<a) (hη : 0<η) (hη1 : η≤1) (hδ : 0<δ)
    (hproxy : Approximate (cost x w) a proxy)
    (m : ℕ) (hm : 0<m)
    (hstruct : (48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ) ≤
      (m:ℝ)*(η/(23+22*a))^2)
    (hresid : (4*(64*a+8*a^2))*(Real.log (8/δ)+
      (Fintype.card K:ℝ)*Real.log (Fintype.card I)) ≤
      (m:ℝ)*(η/(23+22*a))^2) :
    let p := sensitivityProbability w (fun i => pointCost proxy (x i)) (fun i => nearest proxy (x i))
    eventMass (drawWeight p m) (fun z =>
      ¬MetricStep x w (sampledPoints x m z) (sampledWeights w p m z) opt η) ≤ δ := by
  classical
  have hb := metric_sampling_stage x w hw opt proxy a η δ ha hη hη1 hδ hproxy m hm hstruct hresid
  let p := sensitivityProbability w (fun i => pointCost proxy (x i)) (fun i => nearest proxy (x i))
  have hp : ∀ i,0≤p i := fun i =>
    (sensitivityProbability_pos w _ _ hw (fun i => sq_nonneg _) i).le
  apply le_trans (eventMass_mono _ (drawWeight_nonneg p hp m) _ _ ?_) hb
  intro z hbad
  by_contra hgood
  apply hbad
  intro s hs
  have hmem : s∈pointWitnessFamily (K:=K) x ∨ s=opt := by
    rcases hs with hs | hs
    · choose f hf using hs
      exact Or.inl ((mem_pointWitnessFamily x s).2 ⟨f,(funext hf).symm⟩)
    · exact Or.inr hs
  exact of_not_not (fun hh => hgood ⟨s,hmem,hh⟩)

end APC
