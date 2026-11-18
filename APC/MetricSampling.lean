import APC.FiniteFamilyCoreset
import APC.SampleCounts

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

def pointWitnessFamily {B K X : Type*} [Fintype B] [Fintype K]
    (x : B → X) : Finset (K → X) :=
  Finset.univ.image (fun f : K → B => fun j => x (f j))

theorem mem_pointWitnessFamily {B K X : Type*} [Fintype B] [Fintype K]
    (x : B → X) (s : K → X) : s ∈ pointWitnessFamily (K:=K) x ↔ ∃ f : K → B, s=fun j=>x (f j) := by
  simp only [pointWitnessFamily, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr (fun f => eq_comm)

theorem card_pointWitnessFamily {B K X : Type*} [Fintype B] [Fintype K]
    (x : B → X) : (pointWitnessFamily (K:=K) x).card ≤ Fintype.card B^Fintype.card K := by
  classical
  exact Finset.card_image_le.trans (by simp)

theorem card_pointWitnessFamily_with_opt {B K X : Type*} [Fintype B] [Fintype K]
    (x : B → X) (opt : K → X) :
    (insert opt (pointWitnessFamily (K:=K) x)).card ≤ Fintype.card B^Fintype.card K+1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (card_pointWitnessFamily (K:=K) x) 1)

/-- One metric compression stage: preserve all tuples on the preceding
support, plus the fixed original optimum. Counts include repeated centers. -/
theorem metric_sampling_stage
    {B K X : Type*} [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : B → X) (w : B → ℝ) (hw : ∀ i,0<w i)
    (opt proxy : K → X) (a ε δ : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hproxy : Approximate (cost x w) a proxy)
    (m : ℕ) (hm : 0<m)
    (hstruct : (48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ)≤
      (m:ℝ)*(ε/(23+22*a))^2)
    (hresidual : (4*(64*a+8*a^2))*(Real.log (8/δ)+
      (Fintype.card K:ℝ)*Real.log (Fintype.card B))≤
      (m:ℝ)*(ε/(23+22*a))^2) :
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun sample => ∃ s,
      (s ∈ pointWitnessFamily (K:=K) x ∨ s=opt) ∧
      ¬Preserves (cost x w s)
        (cost (sampledPoints x m sample) (sampledWeights w p m sample) s) ε) ≤ δ := by
  classical
  let F := insert opt (pointWitnessFamily (K:=K) x)
  let Query := {s : K → X // s∈F}
  have hcard : Fintype.card Query=F.card := Fintype.card_coe F
  have hN : 0<F.card := Finset.card_pos.mpr ⟨opt,Finset.mem_insert_self _ _⟩
  have hNQ : 0<Fintype.card Query := by rw [hcard];exact hN
  have hcount : F.card≤Fintype.card B^Fintype.card K+1 := card_pointWitnessFamily_with_opt x opt
  have hlog := log_solution_count F.card (Fintype.card B) (Fintype.card K)
    hN Fintype.card_pos hcount (δ/2) (by positivity)
  have hb : (4*(64*a+8*a^2))*Real.log (4*(Fintype.card Query:ℝ)/δ)≤
      (m:ℝ)*(ε/(23+22*a))^2 := by
    rw [hcard]
    have he₁ : 2*(F.card:ℝ)/(δ/2)=4*(F.card:ℝ)/δ := by ring
    have he₂ : (4:ℝ)/(δ/2)=8/δ := by ring
    rw [he₁,he₂] at hlog
    exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hresidual
  have h := finite_family_coreset x w hw proxy (fun q : Query=>q.val) a ε δ ha hε hε1 hδ
    hNQ (fun q=>hproxy q.val) m hm hstruct hb
  let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
  have hp : ∀ i,0≤p i := fun i=>(sensitivityProbability_pos w _ _ hw (fun i=>sq_nonneg _) i).le
  apply le_trans (eventMass_mono _ (drawWeight_nonneg p hp m) _ _ ?_) h
  intro sample hs
  obtain ⟨s,hs,hbad⟩ := hs
  have hsF : s∈F := by
    rcases hs with hs | hs
    · exact Finset.mem_insert_of_mem hs
    · exact hs ▸ Finset.mem_insert_self _ _
  exact ⟨⟨s,hsF⟩,hbad⟩

def metricStageSampleCount (k B : ℕ) (a ε δ : ℝ) : ℕ :=
  budgetSampleCount ((48*(k:ℝ))*Real.log (8*(k:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(k:ℝ)*Real.log B)) (ε/(23+22*a))

/-- The local sampler with a prescribed positive integer count. No
cost-preservation or concentration event is assumed here. -/
theorem metric_sampling_stage_explicit
    {B K X : Type*} [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : B → X) (w : B → ℝ) (hw : ∀ i,0<w i)
    (opt proxy : K → X) (a ε δ : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hproxy : Approximate (cost x w) a proxy) :
    let m := metricStageSampleCount (Fintype.card K) (Fintype.card B) a ε δ
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun sample => ∃ s,
      (s ∈ pointWitnessFamily (K:=K) x ∨ s=opt) ∧
      ¬Preserves (cost x w s)
        (cost (sampledPoints x m sample) (sampledWeights w p m sample) s) ε) ≤ δ := by
  have hm := budgetSampleCount_valid
    ((48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(Fintype.card K:ℝ)*Real.log (Fintype.card B)))
    (ε/(23+22*a)) (ne_of_gt (div_pos hε (by linarith)))
  exact metric_sampling_stage x w hw opt proxy a ε δ ha hε hε1 hδ hproxy
    (metricStageSampleCount _ _ a ε δ) hm.1 hm.2.1 hm.2.2

end APC
