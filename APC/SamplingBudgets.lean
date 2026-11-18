import APC.ImportanceSampling
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators
noncomputable section
namespace APC

theorem exponential_union_budget (N m : ℕ) (hN : 0 < N)
    (D ε δ : ℝ) (hD : 0 < D) (hδ : 0 < δ)
    (hsize : D * Real.log (2*(N:ℝ)/δ) ≤ (m:ℝ)*ε^2) :
    (N:ℝ) * (2 * Real.exp (-(m:ℝ)*ε^2/D)) ≤ δ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < 2*(N:ℝ)/δ := by positivity
  have hlog : Real.log (2*(N:ℝ)/δ) ≤ (m:ℝ)*ε^2/D :=
    (le_div_iff₀ hD).2 (by nlinarith only [hsize])
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hlog)
  have hb := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2*(N:ℝ))
  simp only [Real.exp_neg] at hb
  rw [Real.exp_log hx] at hb
  have he : (2*(N:ℝ)) * (2*(N:ℝ)/δ)⁻¹ = δ := by field_simp
  rw [he] at hb
  have hearg : -(m:ℝ)*ε^2/D = -((m:ℝ)*ε^2/D) := by ring
  rw [hearg, Real.exp_neg]
  convert hb using 1 <;> ring

/-- A finite-family tail bound, with the logarithmic sample budget
derived rather than assumed as a probability statement. -/
theorem finite_family_exponential_bound {Ω Q : Type*} [Fintype Ω] [Fintype Q]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (bad : Q → Ω → Prop)
    (D ε δ : ℝ) (hD : 0 < D) (hδ : 0 < δ)
    (hQ : 0 < Fintype.card Q) (m : ℕ)
    (hpoint : ∀ q, eventMass p (bad q) ≤ 2*Real.exp (-(m:ℝ)*ε^2/D))
    (hsize : D*Real.log (2*(Fintype.card Q:ℝ)/δ) ≤ (m:ℝ)*ε^2) :
    eventMass p (fun ω => ∃ q, bad q ω) ≤ δ := by
  calc
    _ ≤ ∑ q, eventMass p (bad q) := finite_union_bound p hp bad
    _ ≤ ∑ _q : Q, 2*Real.exp (-(m:ℝ)*ε^2/D) :=
      Finset.sum_le_sum (fun q _ => hpoint q)
    _ = (Fintype.card Q:ℝ) * (2*Real.exp (-(m:ℝ)*ε^2/D)) := by simp
    _ ≤ δ := exponential_union_budget _ m hQ D ε δ hD hδ hsize

/-- Structural cluster quantities are nonnegative normalized losses.
Their second moment is controlled by their range, saving a factor k
compared with applying a range-only inequality. -/
theorem nonnegative_importance_concentration {I : Type*} [Fintype I]
    (p loss : I → ℝ) (hp : ∀ i, 0 < p i) (h1 : ∑ i, p i = 1)
    (hloss : ∀ i, 0 ≤ loss i) (hsum : ∑ i, loss i = 1)
    (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : ∀ i, loss i ≤ L*p i) (m : ℕ) (hm : 0 < m) :
    eventMass (drawWeight p m) (fun a => ε < |importanceEstimate p loss m a - 1|) ≤
      2*Real.exp (-(m:ℝ)*ε^2/(12*L)) := by
  have hsecond : (∑ i, (loss i)^2 / p i) ≤ L := by
    calc
      _ ≤ ∑ i, L*loss i := by
        apply Finset.sum_le_sum
        intro i _
        apply (div_le_iff₀ (hp i)).2
        nlinarith only [mul_le_mul_of_nonneg_left (hbound i) (hloss i)]
      _ = L := by rw [← Finset.mul_sum, hsum, mul_one]
  have hb := importance_sampling_concentration p loss hp h1 L L ε hL.le hL hε
    (fun i => by simpa [abs_of_nonneg (hloss i)] using hbound i) hsecond m hm
  rw [hsum] at hb
  have hden : 0 < 4*(L+2*L*ε) := by positivity
  have hd : 4*(L+2*L*ε) ≤ 12*L := by nlinarith only [mul_le_mul_of_nonneg_left hε1 hL.le]
  have hrate : -(m:ℝ)*ε^2/(4*(L+2*L*ε)) ≤ -(m:ℝ)*ε^2/(12*L) := by
    apply (div_le_div_iff₀ hden (by positivity : 0 < 12*L)).2
    have hn : 0 ≤ (m:ℝ)*ε^2 := mul_nonneg (Nat.cast_nonneg m) (sq_nonneg ε)
    nlinarith only [mul_le_mul_of_nonneg_left hd hn]
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by norm_num))

end APC
