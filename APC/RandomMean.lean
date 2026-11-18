import APC.Amplification

open scoped BigOperators
noncomputable section
namespace APC
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def drawMean (x : I → E) (m : ℕ) (f : Draws I m) : E :=
  (m:ℝ)⁻¹ • drawSum x m f

theorem drawSum_centered (x : I → E) (μ : E) (m : ℕ) (f : Draws I m) :
    drawSum (fun i => x i - μ) m f = drawSum x m f - (m:ℝ) • μ := by
  induction m with
  | zero => simp [drawSum]
  | succ m ih =>
    rcases f with ⟨i, tail⟩
    simp only [drawSum, ih tail, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

theorem drawMean_centered (x : I → E) (μ : E) (m : ℕ) (hm : 0 < m) (f : Draws I m) :
    drawMean x m f - μ = (m:ℝ)⁻¹ • drawSum (fun i => x i - μ) m f := by
  rw [drawSum_centered, smul_sub, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hm), one_smul]
  rfl

/-- Exact excess-cost formula for the mean of a sample drawn with replacement. -/
theorem drawMean_cost (x : I → E) (w : I → ℝ) (hmass : mass w ≠ 0)
    (m : ℕ) (hm : 0 < m) (f : Draws I m) :
    oneCost x w (drawMean x m f) = oneCost x w (mean x w) +
      mass w * ((m:ℝ)⁻¹)^2 * ‖drawSum (fun i => x i - mean x w) m f‖^2 := by
  rw [variance_identity x w hmass, norm_sub_rev, drawMean_centered x _ m hm,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Weighted form of Lemma 3.3. With mε≥3, the failure probability is at
most 1/3. No uniform-weight or positive-variance assumption is required. -/
theorem random_mean_failure_le_third (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : 0 < mass w)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hmε : 3 ≤ (m:ℝ)*ε) :
    eventMass (drawWeight (fun i => w i / mass w) m)
      (fun f => (1+ε) * oneCost x w (mean x w) < oneCost x w (drawMean x m f)) ≤ 1/3 := by
  let p : I → ℝ := fun i => w i / mass w
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (hw i) hmass.le
  have h1 : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div]
    exact div_self (ne_of_gt hmass)
  have hz : ∑ i, p i • (x i - mean x w) = 0 := by
    simp only [p, div_eq_mul_inv, mul_comm (w _) (mass w)⁻¹, mul_smul]
    rw [← Finset.smul_sum, centered_sum x w (ne_of_gt hmass), smul_zero]
  have hv : (∑ i, p i * ‖x i - mean x w‖^2) = oneCost x w (mean x w) / mass w := by
    simp [p, oneCost, div_mul_eq_mul_div, Finset.sum_div]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  apply le_trans (eventMass_mono (drawWeight p m) (drawWeight_nonneg p hp m) _ _ ?_)
    (sample_sum_failure_le_third p (fun i => x i - mean x w) hp h1 hz m hm)
  intro f hf
  by_contra hn
  have hb : ‖drawSum (fun i => x i - mean x w) m f‖^2 ≤
      3 * (m:ℝ) * (oneCost x w (mean x w) / mass w) := by
    simpa only [hv] using le_of_not_gt hn
  have hscaled := mul_le_mul_of_nonneg_left hb
    (mul_nonneg hmass.le (sq_nonneg ((m:ℝ)⁻¹)))
  have he : (mass w * ((m:ℝ)⁻¹)^2) *
      (3 * (m:ℝ) * (oneCost x w (mean x w) / mass w)) =
      (3/(m:ℝ)) * oneCost x w (mean x w) := by
    field_simp [ne_of_gt hmass, ne_of_gt hmR]
  rw [he] at hscaled
  have heps : 3/(m:ℝ) ≤ ε := (div_le_iff₀ hmR).2 (by nlinarith [hmε])
  have hlast := mul_le_mul_of_nonneg_right heps (oneCost_nonneg x w hw (mean x w))
  rw [drawMean_cost x w (ne_of_gt hmass) m hm f] at hf
  nlinarith only [hscaled, hlast, hf]

end APC
