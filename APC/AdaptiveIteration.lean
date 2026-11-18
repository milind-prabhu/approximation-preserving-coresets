import APC.ProductProbability

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- Histories are in chronological order. The transition law may depend on
all preceding draws, as required by iterative coreset sampling. -/
def History (Ω : Type*) : ℕ → Type _
  | 0 => PUnit
  | n+1 => History Ω n × Ω

instance historyFintype (Ω : Type*) [Fintype Ω] (n : ℕ) : Fintype (History Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History Ω n × Ω))

def historyWeight {Ω : Type*} (q : (n : ℕ) → History Ω n → Ω → ℝ) :
    (n : ℕ) → History Ω n → ℝ
  | 0, _ => 1
  | n+1, h => historyWeight q n h.1 * q n h.1 h.2

def historyGood {Ω : Type*} (good : (n : ℕ) → History Ω n → Ω → Prop) :
    (n : ℕ) → History Ω n → Prop
  | 0, _ => True
  | n+1, h => historyGood good n h.1 ∧ good n h.1 h.2

theorem historyWeight_nonneg {Ω : Type*}
    (q : (n : ℕ) → History Ω n → Ω → ℝ)
    (hq : ∀ n h ω, 0 ≤ q n h ω) (n : ℕ) : ∀ h, 0 ≤ historyWeight q n h := by
  induction n with
  | zero => intro h; exact zero_le_one
  | succ n ih => intro h; exact mul_nonneg (ih h.1) (hq n h.1 h.2)

theorem historyWeight_sum {Ω : Type*} [Fintype Ω]
    (q : (n : ℕ) → History Ω n → Ω → ℝ)
    (hqsum : ∀ n h, ∑ ω, q n h ω = 1) (n : ℕ) : ∑ h, historyWeight q n h = 1 := by
  induction n with
  | zero => simp [History, historyWeight]
  | succ n ih =>
    change (∑ h : History Ω n × Ω, kernelWeight (historyWeight q n) (q n) h) = 1
    exact kernelWeight_sum _ _ ih (hqsum n)

/-- Adaptive union bound. A stage bound is required only on histories where
all preceding preservation events held. No independence across stages is
assumed. The finite outcome alphabet is arbitrary. -/
theorem adaptive_failure_bound {Ω : Type*} [Fintype Ω]
    (q : (n : ℕ) → History Ω n → Ω → ℝ)
    (hq : ∀ n h ω, 0 ≤ q n h ω) (hqsum : ∀ n h, ∑ ω, q n h ω = 1)
    (good : (n : ℕ) → History Ω n → Ω → Prop)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hstage : ∀ n h, historyGood good n h →
      eventMass (q n h) (fun ω => ¬good n h ω) ≤ δ n) (n : ℕ) :
    eventMass (historyWeight q n) (fun h => ¬historyGood good n h) ≤
      ∑ i ∈ Finset.range n, δ i := by
  induction n with
  | zero => simp [History, historyGood, eventMass]
  | succ n ih =>
    have hb := kernel_event_bound (historyWeight q n) (q n)
      (historyWeight_nonneg q hq n) (historyWeight_sum q hqsum n)
      (hq n) (hqsum n) (historyGood good n)
      (fun h ω => ¬(historyGood good n h ∧ good n h ω))
      (∑ i ∈ Finset.range n, δ i) (δ n) (hδ n) ih (by
        intro h hh
        simpa only [hh, true_and] using hstage n h hh)
    simpa only [Finset.sum_range_succ] using hb

/-- Any final guarantee implied by all local events inherits the same
adaptive failure bound. This also allows an adaptively computed solver. -/
theorem adaptive_consequence_bound {Ω : Type*} [Fintype Ω]
    (q : (n : ℕ) → History Ω n → Ω → ℝ)
    (hq : ∀ n h ω, 0 ≤ q n h ω) (hqsum : ∀ n h, ∑ ω, q n h ω = 1)
    (good : (n : ℕ) → History Ω n → Ω → Prop)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hstage : ∀ n h, historyGood good n h →
      eventMass (q n h) (fun ω => ¬good n h ω) ≤ δ n)
    (n : ℕ) (result : History Ω n → Prop)
    (hresult : ∀ h, historyGood good n h → result h) :
    eventMass (historyWeight q n) (fun h => ¬result h) ≤ ∑ i ∈ Finset.range n, δ i := by
  apply le_trans (eventMass_mono _ (historyWeight_nonneg q hq n) _ _ ?_)
    (adaptive_failure_bound q hq hqsum good δ hδ hstage n)
  intro h hh hg
  exact hh (hresult h hg)

end APC
