import APC.Amplification
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

def productWeight {K Ω : Type*} [Fintype K] (p : K → Ω → ℝ) (sample : K → Ω) : ℝ :=
  ∏ j,p j (sample j)

theorem productWeight_nonneg {K Ω : Type*} [Fintype K] (p : K → Ω → ℝ)
    (hp : ∀ j ω,0≤p j ω) (sample : K → Ω) : 0≤productWeight p sample :=
  Finset.prod_nonneg (fun j _=>hp j (sample j))

theorem productWeight_sum {K Ω : Type*} [Fintype K] [Fintype Ω]
    (p : K → Ω → ℝ) (h1 : ∀ j,∑ ω,p j ω=1) : ∑ sample,productWeight p sample=1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [h1]

/-- Exact marginal of a coordinate in the joint independent-cluster law. -/
theorem productWeight_marginal {K Ω : Type*} [Fintype K] [Fintype Ω]
    (p : K → Ω → ℝ) (h1 : ∀ j,∑ ω,p j ω=1) (j : K) (bad : Ω → Prop) :
    eventMass (productWeight p) (fun sample=>bad (sample j))=eventMass (p j) bad := by
  classical
  let g : K → Ω → ℝ := fun k ω=>if k=j then (if bad ω then p k ω else 0) else p k ω
  have he : ∀ sample : K → Ω,
      (if bad (sample j) then productWeight p sample else 0)=∏ k,g k (sample k) := by
    intro sample
    by_cases hb : bad (sample j)
    · rw [if_pos hb]
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k=j
      · subst k
        simp [g,hb]
      · simp [g,hk]
    · rw [if_neg hb]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [g,hb])
  unfold eventMass
  simp_rw [he]
  rw [← Fintype.prod_sum]
  have hs : ∀ k,(∑ ω,g k ω)=if k=j then eventMass (p j) bad else 1 := by
    intro k
    by_cases hk : k=j
    · subst k
      simp [g,eventMass]
    · simp [g,hk,h1]
  simp_rw [hs]
  simp [eventMass]

/-- A finite conditional experiment: the second draw may depend on the
first. This models randomized lifting after solving a sampled coreset. -/
def kernelWeight {Ω Λ : Type*} (p : Ω → ℝ) (q : Ω → Λ → ℝ) (sample : Ω × Λ) : ℝ :=
  p sample.1*q sample.1 sample.2

theorem kernelWeight_nonneg {Ω Λ : Type*} (p : Ω → ℝ) (q : Ω → Λ → ℝ)
    (hp : ∀ ω,0≤p ω) (hq : ∀ ω z,0≤q ω z) (sample : Ω × Λ) :
    0≤kernelWeight p q sample := mul_nonneg (hp sample.1) (hq sample.1 sample.2)

theorem kernelWeight_sum {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (p : Ω → ℝ) (q : Ω → Λ → ℝ) (hp : ∑ ω,p ω=1) (hq : ∀ ω,∑ z,q ω z=1) :
    ∑ sample,kernelWeight p q sample=1 := by
  unfold kernelWeight
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hq,mul_one]
  exact hp

theorem kernel_event_bound {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (p : Ω → ℝ) (q : Ω → Λ → ℝ) (hp : ∀ ω,0≤p ω) (hpsum : ∑ ω,p ω=1)
    (hq : ∀ ω z,0≤q ω z) (hqsum : ∀ ω,∑ z,q ω z=1)
    (good : Ω → Prop) (bad : Ω → Λ → Prop) (δ η : ℝ)
    (hη : 0≤η) (hfirst : eventMass p (fun ω=>¬good ω)≤δ)
    (hsecond : ∀ ω,good ω→eventMass (q ω) (bad ω)≤η) :
    eventMass (kernelWeight p q) (fun sample=>bad sample.1 sample.2)≤δ+η := by
  classical
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
    · rw [if_neg hg]
      have hh := eventMass_mono (q ω) (hq ω) (bad ω) (fun _=>True) (fun _ _=>True.intro)
      simpa [eventMass,hqsum ω] using hh
  calc
    _≤∑ ω,p ω*(if good ω then η else 1) :=
      Finset.sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hle ω) (hp ω))
    _≤eventMass p (fun ω=>¬good ω)+η*(∑ ω,p ω) := by
      unfold eventMass
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hg : good ω <;> simp [hg] <;> nlinarith only [mul_nonneg hη (hp ω)]
    _≤δ+η := by rw [hpsum,mul_one];linarith only [hfirst]

end APC
