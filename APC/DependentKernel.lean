import APC.ProductProbability

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- Conditional finite randomness whose outcome type may depend on the
first outcome, as for a random coreset with a varying number of points. -/
def dependentKernelWeight {Ω : Type*} {Λ : Ω → Type*}
    (p : Ω → ℝ) (q : (ω : Ω) → Λ ω → ℝ) (sample : Sigma Λ) : ℝ :=
  p sample.1*q sample.1 sample.2

theorem dependentKernelWeight_nonneg {Ω : Type*} {Λ : Ω → Type*}
    (p : Ω → ℝ) (q : (ω : Ω) → Λ ω → ℝ)
    (hp : ∀ ω,0≤p ω) (hq : ∀ ω z,0≤q ω z) :
    ∀ sample,0≤dependentKernelWeight p q sample :=
  fun sample => mul_nonneg (hp sample.1) (hq sample.1 sample.2)

theorem dependentKernelWeight_sum {Ω : Type*} {Λ : Ω → Type*}
    [Fintype Ω] [∀ ω,Fintype (Λ ω)]
    (p : Ω → ℝ) (q : (ω : Ω) → Λ ω → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∀ ω,∑ z,q ω z=1) :
    ∑ sample,dependentKernelWeight p q sample=1 := by
  unfold dependentKernelWeight
  rw [Fintype.sum_sigma]
  simp_rw [←Finset.mul_sum,hq,mul_one]
  exact hp

theorem dependentKernel_event_identity {Ω : Type*} {Λ : Ω → Type*}
    [Fintype Ω] [∀ ω,Fintype (Λ ω)]
    (p : Ω → ℝ) (q : (ω : Ω) → Λ ω → ℝ)
    (bad : (ω : Ω) → Λ ω → Prop) :
    eventMass (dependentKernelWeight p q) (fun sample => bad sample.1 sample.2)=
      ∑ ω,p ω*eventMass (q ω) (bad ω) := by
  unfold eventMass dependentKernelWeight
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

/-- Failure composition with no fixed-size or unconditional-independence
assumption on the later finite random experiment. -/
theorem dependentKernel_event_bound {Ω : Type*} {Λ : Ω → Type*}
    [Fintype Ω] [∀ ω,Fintype (Λ ω)]
    (p : Ω → ℝ) (q : (ω : Ω) → Λ ω → ℝ)
    (hp : ∀ ω,0≤p ω) (hpsum : ∑ ω,p ω=1)
    (hq : ∀ ω z,0≤q ω z) (hqsum : ∀ ω,∑ z,q ω z=1)
    (good : Ω → Prop) (bad : (ω : Ω) → Λ ω → Prop) (δ η : ℝ)
    (hη : 0≤η) (hfirst : eventMass p (fun ω=>¬good ω)≤δ)
    (hsecond : ∀ ω,good ω→eventMass (q ω) (bad ω)≤η) :
    eventMass (dependentKernelWeight p q) (fun sample=>bad sample.1 sample.2)≤δ+η := by
  rw [dependentKernel_event_identity]
  have hle : ∀ ω,eventMass (q ω) (bad ω)≤(if good ω then η else 1) := by
    intro ω
    by_cases hg : good ω
    · simpa [hg] using hsecond ω hg
    · rw [if_neg hg]
      have hh := eventMass_mono (q ω) (hq ω) (bad ω) (fun _=>True) (fun _ _=>True.intro)
      simpa [eventMass,hqsum ω] using hh
  calc
    _ ≤ ∑ ω,p ω*(if good ω then η else 1) :=
      Finset.sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hle ω) (hp ω))
    _ ≤ eventMass p (fun ω=>¬good ω)+η*(∑ ω,p ω) := by
      unfold eventMass
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hg : good ω <;> simp [hg] <;> nlinarith only [mul_nonneg hη (hp ω)]
    _ ≤ δ+η := by rw [hpsum,mul_one]; linarith only [hfirst]

end APC
