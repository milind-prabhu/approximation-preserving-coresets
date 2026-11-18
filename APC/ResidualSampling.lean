import APC.ImportanceSampling
import APC.ConcentrationGeometry

open scoped BigOperators
noncomputable section
namespace APC

def normalizedResidual {I : Type*} (w residual : I → ℝ) (C : ℝ) : I → ℝ :=
  fun i => w i * residual i / C

/-- Claim A.10's second-moment calculation. A zero proxy-point cost causes
no division by zero: only the strictly positive sampling probabilities are
divided by. -/
theorem residual_second_moment {I : Type*} [Fintype I]
    (w residual s c p : I → ℝ) (C A a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i) (hc : ∀ i, 0 ≤ c i)
    (hp : ∀ i, 0 < p i) (hC : 0 < C) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hsumS : ∑ i, w i * s i = C) (hsumA : ∑ i, w i * c i = A)
    (happrox : A ≤ a*C)
    (hsens : ∀ i, w i*c i ≤ 4*A*p i)
    (hdiff : ∀ i, (residual i)^2 ≤ 8*s i*c i + 2*(c i)^2) :
    (∑ i, (normalizedResidual w residual C i)^2 / p i) ≤ 32*a + 8*a^2 := by
  have hpoint : ∀ i, (normalizedResidual w residual C i)^2 / p i ≤
      (4*A/C^2) * (w i * (8*s i + 2*c i)) := by
    intro i
    have h₁ := mul_le_mul_of_nonneg_left (hdiff i) (sq_nonneg (w i))
    have h₂ := mul_le_mul_of_nonneg_left (hsens i)
      (mul_nonneg (hw i) (by linarith [hs i, hc i] : 0 ≤ 8*s i+2*c i))
    have hn : (w i)^2 * (residual i)^2 ≤
        (4*A*p i) * (w i * (8*s i+2*c i)) := by nlinarith only [h₁, h₂]
    apply (div_le_iff₀ (hp i)).2
    dsimp [normalizedResidual]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hC)).2
    convert hn using 1 <;> field_simp <;> ring
  have hsum : (∑ i, w i * (8*s i+2*c i)) = 8*C+2*A := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have h₁ : (∑ i, w i*(8*s i)) = 8*∑ i, w i*s i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    have h₂ : (∑ i, w i*(2*c i)) = 2*∑ i, w i*c i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h₁, h₂, hsumS, hsumA]
  have hr : 0 ≤ A/C := div_nonneg hA hC.le
  have hrat : A/C ≤ a := (div_le_iff₀ hC).2 happrox
  calc
    _ ≤ ∑ i, (4*A/C^2) * (w i*(8*s i+2*c i)) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = 32*(A/C) + 8*(A/C)^2 := by rw [← Finset.mul_sum, hsum]; field_simp; ring
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hrat) (add_nonneg ha hr)]

theorem residual_range {I : Type*}
    (w residual c Δ p : I → ℝ) (C A a ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hC : 0 < C) (hε : 0 < ε)
    (happrox : A ≤ a*C)
    (hsensC : ∀ i, w i*c i ≤ 4*A*p i)
    (hsensΔ : ∀ i, w i*Δ i ≤ 4*A*p i)
    (hp : ∀ i, 0 ≤ p i)
    (hclose : ∀ i, ε*|residual i| ≤ 2*(Δ i+c i)) :
    ∀ i, |normalizedResidual w residual C i| ≤ (16*a/ε)*p i := by
  intro i
  have h₁ := mul_le_mul_of_nonneg_left (hclose i) (hw i)
  have h₂ := hsensC i
  have h₃ := hsensΔ i
  have h₄ := mul_le_mul_of_nonneg_right happrox (hp i)
  have hraw : ε * (w i*|residual i|) ≤ 16*a*C*p i := by nlinarith only [h₁,h₂,h₃,h₄]
  have he : |normalizedResidual w residual C i| = w i*|residual i|/C := by
    simp [normalizedResidual, abs_div, abs_mul, abs_of_nonneg (hw i), abs_of_pos hC]
  rw [he]
  apply (div_le_iff₀ hC).2
  have h : w i*|residual i| ≤ (16*a*C*p i)/ε :=
    (le_div_iff₀ hε).2 (by nlinarith only [hraw])
  convert h using 1 <;> ring

/-- Close-cluster residual concentration with no k in the exponent.
The hypotheses are the explicit geometric and sensitivity inequalities
used in Appendix A; no concentration conclusion is assumed. -/
theorem close_residual_concentration {I : Type*} [Fintype I]
    (w residual s c Δ p : I → ℝ) (C A a ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i) (hc : ∀ i, 0 ≤ c i)
    (hp : ∀ i, 0 < p i) (h1 : ∑ i, p i = 1)
    (hC : 0 < C) (hA : 0 ≤ A) (ha : 0 < a) (hε : 0 < ε)
    (hsumS : ∑ i, w i*s i = C) (hsumA : ∑ i, w i*c i = A)
    (happrox : A ≤ a*C)
    (hsensC : ∀ i, w i*c i ≤ 4*A*p i)
    (hsensΔ : ∀ i, w i*Δ i ≤ 4*A*p i)
    (hdiff : ∀ i, (residual i)^2 ≤ 8*s i*c i + 2*(c i)^2)
    (hclose : ∀ i, ε*|residual i| ≤ 2*(Δ i+c i))
    (m : ℕ) (hm : 0 < m) :
    eventMass (drawWeight p m)
      (fun sample => ε < |importanceEstimate p (normalizedResidual w residual C) m sample -
        ∑ i, normalizedResidual w residual C i|) ≤
      2 * Real.exp (-(m:ℝ)*ε^2 / (4*(64*a+8*a^2))) := by
  have hsecond := residual_second_moment w residual s c p C A a hw hs hc hp hC hA ha.le
    hsumS hsumA happrox hsensC hdiff
  have hrange := residual_range w residual c Δ p C A a ε hw hC hε happrox
    hsensC hsensΔ (fun i => (hp i).le) hclose
  have hb := importance_sampling_concentration p (normalizedResidual w residual C) hp h1
    (16*a/ε) (32*a+8*a^2) ε (by positivity) (by positivity) hε hrange hsecond m hm
  have he : 32*a+8*a^2+2*(16*a/ε)*ε = 64*a+8*a^2 := by field_simp; ring
  simpa only [he] using hb

end APC
