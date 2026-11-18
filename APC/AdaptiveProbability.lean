import APC.ProductProbability

open scoped BigOperators
noncomputable section
namespace APC.Adaptive

/-- A finite history of adaptive draws. Each stage may have a different
finite outcome type and a law depending on its complete preceding history. -/
def History (Ω : ℕ → Type*) : ℕ → Type _
  | 0 => PUnit
  | n+1 => History Ω n × Ω n

instance historyFintype (Ω : ℕ → Type*) [∀ i, Fintype (Ω i)] (n : ℕ) :
    Fintype (History Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History Ω n × Ω n))

def historyWeight {Ω : ℕ → Type*} (q : (i : ℕ) → History Ω i → Ω i → ℝ) :
    (n : ℕ) → History Ω n → ℝ
  | 0, _ => 1
  | n+1, h => kernelWeight (historyWeight q n) (q n) h

def historyGood {Ω : ℕ → Type*} (good : (i : ℕ) → History Ω i → Ω i → Prop) :
    (n : ℕ) → History Ω n → Prop
  | 0, _ => True
  | n+1, h => historyGood good n h.1 ∧ good n h.1 h.2

theorem historyWeight_nonneg {Ω : ℕ → Type*}
    (q : (i : ℕ) → History Ω i → Ω i → ℝ) (hq : ∀ i h z, 0 ≤ q i h z)
    (n : ℕ) : ∀ h, 0 ≤ historyWeight q n h := by
  induction n with
  | zero => intro h; exact zero_le_one
  | succ n ih => exact kernelWeight_nonneg _ _ ih (hq n)

theorem historyWeight_sum {Ω : ℕ → Type*} [∀ i, Fintype (Ω i)]
    (q : (i : ℕ) → History Ω i → Ω i → ℝ)
    (hq : ∀ i h, ∑ z, q i h z = 1) (n : ℕ) :
    ∑ h, historyWeight q n h = 1 := by
  induction n with
  | zero => simp [History, historyWeight]
  | succ n ih => exact kernelWeight_sum _ _ ih (hq n)

/-- Adaptive union bound. The step bound is needed only after good
histories; no unconditional independence of stages is assumed. -/
theorem adaptive_failure_bound {Ω : ℕ → Type*} [∀ i, Fintype (Ω i)]
    (q : (i : ℕ) → History Ω i → Ω i → ℝ)
    (hq : ∀ i h z, 0 ≤ q i h z) (hqsum : ∀ i h, ∑ z, q i h z = 1)
    (good : (i : ℕ) → History Ω i → Ω i → Prop) (δ : ℕ → ℝ)
    (hδ : ∀ i, 0 ≤ δ i)
    (hstep : ∀ i h, historyGood good i h →
      eventMass (q i h) (fun z => ¬good i h z) ≤ δ i) (n : ℕ) :
    eventMass (historyWeight q n) (fun h => ¬historyGood good n h) ≤
      ∑ i ∈ Finset.range n, δ i := by
  induction n with
  | zero => simp [History, historyGood, eventMass]
  | succ n ih =>
    have hb := kernel_event_bound (historyWeight q n) (q n)
      (historyWeight_nonneg q hq n) (historyWeight_sum q hqsum n)
      (hq n) (hqsum n) (historyGood good n)
      (fun h z => ¬(historyGood good n h ∧ good n h z))
      (∑ i ∈ Finset.range n, δ i) (δ n) (hδ n) ih
      (by intro h hh; simpa only [hh, true_and] using hstep n h hh)
    simpa only [historyWeight, historyGood, Finset.sum_range_succ] using hb

/-- Any output guarantee established on all-good histories inherits the
adaptive failure budget. -/
theorem adaptive_output_bound {Ω : ℕ → Type*} [∀ i, Fintype (Ω i)]
    (q : (i : ℕ) → History Ω i → Ω i → ℝ)
    (hq : ∀ i h z, 0 ≤ q i h z) (hqsum : ∀ i h, ∑ z, q i h z = 1)
    (good : (i : ℕ) → History Ω i → Ω i → Prop) (δ : ℕ → ℝ)
    (hδ : ∀ i, 0 ≤ δ i)
    (hstep : ∀ i h, historyGood good i h →
      eventMass (q i h) (fun z => ¬good i h z) ≤ δ i)
    (n : ℕ) (result : History Ω n → Prop)
    (hresult : ∀ h, historyGood good n h → result h) :
    eventMass (historyWeight q n) (fun h => ¬result h) ≤
      ∑ i ∈ Finset.range n, δ i := by
  apply le_trans (eventMass_mono _ (historyWeight_nonneg q hq n) _ _ ?_)
    (adaptive_failure_bound q hq hqsum good δ hδ hstep n)
  intro h hbad hgood
  exact hbad (hresult h hgood)

end APC.Adaptive
