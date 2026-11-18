import APC.Bernstein
import APC.RandomMean

open scoped BigOperators
noncomputable section
namespace APC

def expectation {I : Type*} [Fintype I] (p f : I → ℝ) : ℝ := ∑ i, p i * f i

theorem centered_expectation {I : Type*} [Fintype I]
    (p f : I → ℝ) (h1 : ∑ i, p i = 1) :
    (∑ i, p i * (f i - expectation p f)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul, expectation]
  ring

theorem centered_second_moment {I : Type*} [Fintype I]
    (p f : I → ℝ) (h1 : ∑ i, p i = 1) :
    (∑ i, p i * (f i - expectation p f)^2) =
      (∑ i, p i * (f i)^2) - (expectation p f)^2 := by
  have he : ∀ i, p i * (f i - expectation p f)^2 =
      p i * (f i)^2 - (2 * expectation p f) * (p i * f i) +
        (expectation p f)^2 * p i := by intro i; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, h1]
  change (∑ i, p i * f i^2) - (2*expectation p f)*expectation p f +
    expectation p f^2 * 1 = _
  ring

theorem expectation_abs_le {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (R : ℝ) (hbound : ∀ i, |f i| ≤ R) : |expectation p f| ≤ R := by
  calc
    _ ≤ ∑ i, |p i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i * |f i| := by simp [abs_mul, abs_of_nonneg, hp]
    _ ≤ ∑ i, p i * R := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbound i) (hp i))
    _ = R := by rw [← Finset.sum_mul, h1, one_mul]

/-- Bernstein concentration for an uncentered empirical average. -/
theorem empirical_average_concentration {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (R V r : ℝ) (hR : 0 ≤ R) (hV : 0 < V) (hr : 0 < r)
    (hbound : ∀ i, |f i| ≤ R) (hsecond : ∑ i, p i * (f i)^2 ≤ V)
    (m : ℕ) (hm : 0 < m) :
    eventMass (drawWeight p m)
      (fun a => r < |drawSum f m a / (m:ℝ) - expectation p f|) ≤
        2 * Real.exp (-(m:ℝ)*r^2 / (4*(V+2*R*r))) := by
  have hmean := expectation_abs_le p f hp h1 R hbound
  have hcenter : ∀ i, |f i - expectation p f| ≤ 2*R := by
    intro i
    exact (abs_sub _ _).trans (by linarith [hbound i, hmean])
  have hvariance : (∑ i, p i * (f i - expectation p f)^2) ≤ V := by
    rw [centered_second_moment p f h1]
    nlinarith only [hsecond, sq_nonneg (expectation p f)]
  have hb := finite_bernstein p (fun i => f i - expectation p f) hp h1
    (centered_expectation p f h1) (2*R) V r (by positivity) hV hr hcenter hvariance m
  have hmono : eventMass (drawWeight p m)
      (fun a => r < |drawSum f m a / (m:ℝ) - expectation p f|) ≤
      eventMass (drawWeight p m)
        (fun a => (m:ℝ)*r < |drawSum (fun i => f i - expectation p f) m a|) := by
    apply eventMass_mono _ (drawWeight_nonneg p hp m)
    intro a ha
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have he : drawSum (fun i => f i - expectation p f) m a =
        (m:ℝ) * (drawSum f m a / (m:ℝ) - expectation p f) := by
      rw [drawSum_centered]
      simp only [smul_eq_mul]
      field_simp
    rw [he, abs_mul, abs_of_pos hmR]
    exact mul_lt_mul_of_pos_left ha hmR
  exact hmono.trans hb

/-- An importance-weighted sample average, allowing signed residual losses. -/
def importanceEstimate {I : Type*} (p loss : I → ℝ) (m : ℕ) (a : Draws I m) : ℝ :=
  drawSum (fun i => loss i / p i) m a / (m:ℝ)

theorem importance_unbiased {I : Type*} [Fintype I]
    (p loss : I → ℝ) (hp : ∀ i, 0 < p i) :
    expectation p (fun i => loss i / p i) = ∑ i, loss i := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (hp i)]

theorem importance_second_moment {I : Type*} [Fintype I]
    (p loss : I → ℝ) (hp : ∀ i, 0 < p i) :
    (∑ i, p i * (loss i / p i)^2) = ∑ i, (loss i)^2 / p i := by
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (hp i)]

theorem importance_sampling_concentration {I : Type*} [Fintype I]
    (p loss : I → ℝ) (hp : ∀ i, 0 < p i) (h1 : ∑ i, p i = 1)
    (R V r : ℝ) (hR : 0 ≤ R) (hV : 0 < V) (hr : 0 < r)
    (hbound : ∀ i, |loss i| ≤ R * p i)
    (hsecond : ∑ i, (loss i)^2 / p i ≤ V)
    (m : ℕ) (hm : 0 < m) :
    eventMass (drawWeight p m)
      (fun a => r < |importanceEstimate p loss m a - ∑ i, loss i|) ≤
        2 * Real.exp (-(m:ℝ)*r^2 / (4*(V+2*R*r))) := by
  have hrange : ∀ i, |loss i / p i| ≤ R := by
    intro i
    rw [abs_div, abs_of_pos (hp i)]
    exact (div_le_iff₀ (hp i)).2 (hbound i)
  have hb := empirical_average_concentration p (fun i => loss i / p i)
    (fun i => (hp i).le) h1 R V r hR hV hr hrange
    (by rw [importance_second_moment p loss hp]; exact hsecond) m hm
  simpa only [importance_unbiased p loss hp, importanceEstimate] using hb

end APC
