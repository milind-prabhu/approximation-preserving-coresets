import APC.ProductProbability

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- Multiplicative success composition for a conditional finite law. It
requires no independence between the first sample and the later law. -/
theorem kernel_event_bound_sharp {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (p : Ω → ℝ) (q : Ω → Λ → ℝ) (hp : ∀ ω,0≤p ω) (hpsum : ∑ ω,p ω=1)
    (hq : ∀ ω z,0≤q ω z) (hqsum : ∀ ω,∑ z,q ω z=1)
    (good : Ω → Prop) (bad : Ω → Λ → Prop) (δ η : ℝ)
    (hη : 0≤η) (hη1 : η≤1) (hfirst : eventMass p (fun ω=>¬good ω)≤δ)
    (hsecond : ∀ ω,good ω→eventMass (q ω) (bad ω)≤η) :
    eventMass (kernelWeight p q) (fun sample=>bad sample.1 sample.2)≤η+(1-η)*δ := by
  have he : eventMass (kernelWeight p q) (fun sample=>bad sample.1 sample.2)=
      ∑ ω,p ω*eventMass (q ω) (bad ω) := by
    unfold eventMass kernelWeight
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> ring
  rw [he]
  have hle : ∀ ω,eventMass (q ω) (bad ω)≤(if good ω then η else 1) := by
    intro ω
    by_cases hg : good ω
    · simpa [hg] using hsecond ω hg
    · have hh := eventMass_mono (q ω) (hq ω) (bad ω) (fun _=>True) (fun _ _=>True.intro)
      simpa [eventMass,hqsum ω,hg] using hh
  calc
    _≤∑ ω,p ω*(if good ω then η else 1) :=
      Finset.sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hle ω) (hp ω))
    _=η*(∑ ω,p ω)+(1-η)*eventMass p (fun ω=>¬good ω) := by
      unfold eventMass
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hg : good ω <;> simp [hg] <;> ring
    _≤_ := by
      rw [hpsum,mul_one]
      exact add_le_add_left (mul_le_mul_of_nonneg_left hfirst (by linarith)) η

end APC
