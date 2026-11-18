import APC.ResidualSampling
import APC.SamplingBudgets

open scoped BigOperators
noncomputable section
namespace APC

/-- Claim A.7's finite-family conclusion from the explicit residual moment
and range inequalities proved in ResidualSampling. The family may be
chosen after fixing a first-stage sample, but before these draws. -/
theorem residual_family_concentration {I Q : Type*} [Fintype I] [Fintype Q]
    (p : I → ℝ) (loss : Q → I → ℝ)
    (hp : ∀ i, 0 < p i) (h1 : ∑ i, p i = 1)
    (a ε δ : ℝ) (ha : 0 < a) (hε : 0 < ε) (hδ : 0 < δ)
    (hQ : 0 < Fintype.card Q)
    (hrange : ∀ q i, |loss q i| ≤ (16*a/ε)*p i)
    (hsecond : ∀ q, ∑ i, (loss q i)^2/p i ≤ 32*a+8*a^2)
    (m : ℕ) (hm : 0 < m)
    (hsize : (4*(64*a+8*a^2))*Real.log (2*(Fintype.card Q:ℝ)/δ) ≤ (m:ℝ)*ε^2) :
    eventMass (drawWeight p m)
      (fun sample => ∃ q, ε < |importanceEstimate p (loss q) m sample-∑ i,loss q i|) ≤ δ := by
  apply finite_family_exponential_bound (drawWeight p m) (drawWeight_nonneg p (fun i => (hp i).le) m)
    (fun q sample => ε < |importanceEstimate p (loss q) m sample-∑ i,loss q i|)
    (4*(64*a+8*a^2)) ε δ (by positivity) hδ hQ m ?_ hsize
  intro q
  have hb := importance_sampling_concentration p (loss q) hp h1 (16*a/ε)
    (32*a+8*a^2) ε (by positivity) (by positivity) hε (hrange q) (hsecond q) m hm
  have he : 32*a+8*a^2+2*(16*a/ε)*ε = 64*a+8*a^2 := by field_simp; ring
  simpa only [he] using hb

/-- Simultaneous structural preservation of a finite family of normalized
nonnegative cluster quantities, with the k log(k/δ) budget made explicit. -/
theorem structural_family_concentration {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (loss : J → I → ℝ)
    (hp : ∀ i, 0 < p i) (h1 : ∑ i,p i=1)
    (hloss : ∀ j i,0≤loss j i) (hsum : ∀ j,∑ i,loss j i=1)
    (L ε δ : ℝ) (hL : 0<L) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hJ : 0<Fintype.card J)
    (hbound : ∀ j i,loss j i≤L*p i)
    (m : ℕ) (hm : 0<m)
    (hsize : (12*L)*Real.log (2*(Fintype.card J:ℝ)/δ)≤(m:ℝ)*ε^2) :
    eventMass (drawWeight p m)
      (fun sample => ∃ j, ε< |importanceEstimate p (loss j) m sample-1|)≤δ := by
  apply finite_family_exponential_bound (drawWeight p m) (drawWeight_nonneg p (fun i=>(hp i).le) m)
    (fun j sample=>ε< |importanceEstimate p (loss j) m sample-1|)
    (12*L) ε δ (by positivity) hδ hJ m ?_ hsize
  intro j
  exact nonnegative_importance_concentration p (loss j) hp h1 (hloss j) (hsum j)
    L ε hL hε hε1 (hbound j) m hm

end APC
