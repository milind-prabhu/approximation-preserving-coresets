import APC.MetricSampling
import APC.WitnessBudget

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- Preservation is required only for means of t input points and one
fixed reference optimum; no strong-coreset premise is used. -/
def EuclideanStep {I J K E : Type*} [Fintype I] [Fintype J] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (w : I → ℝ) (y : J → E) (v : J → ℝ) (opt : K → E) (t : ℕ) (η : ℝ) : Prop :=
  ∀ s,s∈witnessFamily (K:=K) x t ∨ s=opt → Preserves (cost x w s) (cost y v s) η

/-- Enlarging the structural center-count budget pays for the t-point
witness family. This deliberately oversamples by at most a t factor. -/
theorem euclidean_step_kernel
    {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0<w i) (proxy opt : K → E)
    (t : ℕ) (ht : 0<t) (a η δ : ℝ) (ha : 0<a) (hη : 0<η) (hη1 : η≤1)
    (hδ : 0<δ) (hδ1 : δ≤1) (hproxy : Approximate (cost x w) a proxy) :
    let m := metricStageSampleCount (t*Fintype.card K) (Fintype.card I) a η δ
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun z=>¬EuclideanStep x w (sampledPoints x m z)
      (sampledWeights w p m z) opt t η)≤δ := by
  classical
  let F := insert opt (witnessFamily (K:=K) x t)
  let Query := {s : K → E // s∈F}
  have hcard : Fintype.card Query=F.card := Fintype.card_coe F
  have hN : 0<F.card := Finset.card_pos.mpr ⟨opt,Finset.mem_insert_self _ _⟩
  have hcount := card_witnessFamily_with_opt x t opt
  have hlog := log_solution_count F.card (Fintype.card I) (t*Fintype.card K)
    hN Fintype.card_pos hcount (δ/2) (by positivity)
  have he₁ : 2*(F.card:ℝ)/(δ/2)=4*(F.card:ℝ)/δ := by ring
  have he₂ : (4:ℝ)/(δ/2)=8/δ := by ring
  rw [he₁,he₂] at hlog
  have hkk : Fintype.card K≤t*Fintype.card K := by nlinarith
  have hkr : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hkkR : (Fintype.card K:ℝ)≤(t*Fintype.card K:ℕ) := Nat.cast_le.mpr hkk
  have hlogpos : 0≤Real.log (8*(Fintype.card K:ℝ)/δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).2 (by nlinarith))
  have hlogmono : Real.log (8*(Fintype.card K:ℝ)/δ)≤
      Real.log (8*((t*Fintype.card K:ℕ):ℝ)/δ) := Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right (by nlinarith) hδ.le)
  have hstructmono : 48*(Fintype.card K:ℝ)*Real.log (8*(Fintype.card K:ℝ)/δ)≤
      48*((t*Fintype.card K:ℕ):ℝ)*Real.log (8*((t*Fintype.card K:ℕ):ℝ)/δ) :=
    mul_le_mul (by nlinarith) hlogmono hlogpos (by positivity)
  have hb := budgetSampleCount_valid
    ((48*((t*Fintype.card K:ℕ):ℝ))*Real.log (8*((t*Fintype.card K:ℕ):ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+((t*Fintype.card K:ℕ):ℝ)*Real.log (Fintype.card I)))
    (η/(23+22*a)) (by positivity)
  have hres := (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤4*(64*a+8*a^2))).trans hb.2.2
  rw [←hcard] at hres
  have hsample := finite_family_coreset x w hw proxy (fun q : Query=>q.val) a η δ ha hη hη1 hδ
    (by rw [hcard];exact hN) (fun q=>hproxy q.val) _ hb.1 (hstructmono.trans hb.2.1) hres
  let m := metricStageSampleCount (t*Fintype.card K) (Fintype.card I) a η δ
  let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
  apply le_trans (eventMass_mono _
    (drawWeight_nonneg p (fun i=>(sensitivityProbability_pos w _ _ hw (fun i=>sq_nonneg _) i).le) m) _ _ ?_) hsample
  intro z hbad
  by_contra hg
  apply hbad
  intro s hs
  have hmem : s∈F := by
    rcases hs with hs | hs
    · exact Finset.mem_insert_of_mem hs
    · exact hs ▸ Finset.mem_insert_self _ _
  exact of_not_not (fun hn=>hg ⟨⟨s,hmem⟩,hn⟩)

end APC
