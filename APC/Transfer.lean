import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The deterministic witness-family reduction. No sampling theorem is assumed
as an axiom: every cost-preservation premise is visible in the theorem type. -/
namespace APC

def Preserves (p q : ℝ) (ε : ℝ) : Prop :=
  (1 - ε) * p ≤ q ∧ q ≤ (1 + ε) * p

/-- Approximation is comparison with every feasible solution; this avoids
assuming that an optimum exists for the summary. -/
def Approximate {Solution : Type*} (cost : Solution → ℝ)
    (α : ℝ) (s : Solution) : Prop :=
  ∀ c, cost s ≤ α * cost c

theorem witness_transfer {Solution : Type*} (p q : Solution → ℝ)
    (s out opt : Solution) (α β η : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hη : η < 1)
    (happrox : Approximate q α s)
    (hlift : q out ≤ β * q s)
    (hout : (1 - η) * p out ≤ q out)
    (hopt : q opt ≤ (1 + η) * p opt) :
    p out ≤ α * β * ((1 + η) / (1 - η)) * p opt := by
  have hden : 0 < 1 - η := by linarith
  have hchain : (1 - η) * p out ≤ β * (α * ((1 + η) * p opt)) :=
    hout.trans (hlift.trans ((mul_le_mul_of_nonneg_left (happrox opt) hβ).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hopt hα) hβ)))
  calc
    p out ≤ (β * (α * ((1 + η) * p opt))) / (1-η) :=
      (le_div_iff₀ hden).2 (by nlinarith [hchain])
    _ = _ := by ring

theorem euclidean_factor (η : ℝ) (hη : 0 ≤ η) (hsmall : η ≤ 1/2) :
    (1 + η)^2 / (1 - η) ≤ 1 + 10 * η := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - η)).2
  have : η * (1/2 - η) ≥ 0 := mul_nonneg hη (by linarith)
  nlinarith

theorem euclidean_transfer {Solution : Type*} (p q : Solution → ℝ)
    (s out opt : Solution) (α η : ℝ)
    (hα : 0 ≤ α) (hη : 0 ≤ η) (hsmall : η ≤ 1/2)
    (hcost : 0 ≤ p opt) (happrox : Approximate q α s)
    (hlift : q out ≤ (1 + η) * q s)
    (hout : Preserves (p out) (q out) η)
    (hopt : Preserves (p opt) (q opt) η) :
    p out ≤ α * (1 + 10 * η) * p opt := by
  have ht := witness_transfer p q s out opt α (1+η) η hα (by linarith)
    (by linarith) happrox hlift hout.1 hopt.2
  calc
    p out ≤ α * ((1+η)^2 / (1-η)) * p opt := by
      convert ht using 1 <;> ring
    _ ≤ α * (1+10*η) * p opt :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (euclidean_factor η hη hsmall) hα) hcost

theorem euclidean_transfer_rescaled {Solution : Type*} (p q : Solution → ℝ)
    (s out opt : Solution) (α ε : ℝ)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hsmall : ε ≤ 1)
    (hcost : 0 ≤ p opt) (happrox : Approximate q α s)
    (hlift : q out ≤ (1 + ε/10) * q s)
    (hout : Preserves (p out) (q out) (ε/10))
    (hopt : Preserves (p opt) (q opt) (ε/10)) :
    p out ≤ α * (1 + ε) * p opt := by
  have h := euclidean_transfer p q s out opt α (ε/10) hα (by linarith)
    (by linarith) hcost happrox hlift hout hopt
  convert h using 1 <;> ring

/-- Two sampling stages have error 2η+η². This explicitly accounts for
the strong coreset stage, which cannot simply be omitted. -/
theorem preserves_compose {p q r η : ℝ} (hp : 0 ≤ p)
    (hη : 0 ≤ η) (hsmall : η ≤ 1)
    (h₁ : Preserves p q η) (h₂ : Preserves q r η) :
    Preserves p r (2*η + η^2) := by
  constructor
  · have h := (mul_le_mul_of_nonneg_left h₁.1 (by linarith : 0 ≤ 1-η)).trans h₂.1
    have : 0 ≤ η^2 * p := mul_nonneg (sq_nonneg η) hp
    nlinarith
  · have h := h₂.2.trans (mul_le_mul_of_nonneg_left h₁.2 (by linarith : 0 ≤ 1+η))
    nlinarith

theorem preserves_mono {p q a b : ℝ} (hp : 0 ≤ p) (hab : a ≤ b)
    (h : Preserves p q a) : Preserves p q b := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hp, h.1, h.2]

end APC
