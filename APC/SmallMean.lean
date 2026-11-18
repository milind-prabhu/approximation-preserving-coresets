import APC.Geometry
import Mathlib.Tactic.Positivity

open scoped BigOperators
noncomputable section
namespace APC

theorem exists_le_weighted_average {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    ∃ i, 0 < p i ∧ f i ≤ ∑ j, p j * f j := by
  classical
  by_contra hn
  push_neg at hn
  have hpos : (∑ i : I, (0:ℝ)) < ∑ i, p i := by simp [h1]
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hpos
  have hs := Finset.sum_lt_sum
    (s := Finset.univ)
    (f := fun j => p j * (∑ l, p l * f l))
    (g := fun j => p j * f j)
    (fun j _ => by
      by_cases hz : p j = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hn j (lt_of_le_of_ne (hp j) (Ne.symm hz)))) (hp j))
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hn i hi) hi⟩
  rw [← Finset.sum_mul, h1, one_mul] at hs
  exact (lt_irrefl _ hs)

variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact expectation identity for adding one independent centered draw. -/
theorem centered_step_average (p : I → ℝ) (v : I → E)
    (h1 : ∑ i, p i = 1) (hz : ∑ i, p i • v i = 0) (z : E) :
    (∑ i, p i * ‖z + v i‖^2) = ‖z‖^2 + ∑ i, p i * ‖v i‖^2 := by
  have hc : ∑ i, p i * inner ℝ z (v i) = 0 := by
    simp_rw [← real_inner_smul_right]
    rw [← inner_sum, hz, inner_zero_right]
  simp_rw [norm_add_sq_real, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul]
  have ht : (∑ i, p i * (2 * inner ℝ z (v i))) = 0 := by
    calc
      _ = 2 * ∑ i, p i * inner ℝ z (v i) := by rw [Finset.mul_sum]; congr 1; ext i; ring
      _ = 0 := by rw [hc, mul_zero]
  rw [ht, add_zero]

/-- Conditional expectation gives a supported m-tuple whose mean-square
error is at most variance/m. Repetitions are allowed. -/
theorem exists_small_sum (p : I → ℝ) (v : I → E)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (hz : ∑ i, p i • v i = 0) (m : ℕ) :
    ∃ f : Fin m → I, (∀ j, 0 < p (f j)) ∧
      ‖∑ j, v (f j)‖^2 ≤ (m:ℝ) * ∑ i, p i * ‖v i‖^2 := by
  classical
  induction m with
  | zero => exact ⟨Fin.elim0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨f, hf, hb⟩ := ih
    obtain ⟨i, hi, hc⟩ := exists_le_weighted_average p
      (fun i => ‖(∑ j, v (f j)) + v i‖^2) hp h1
    rw [centered_step_average p v h1 hz] at hc
    refine ⟨Fin.snoc f i, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hi
      · simpa using hf j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      push_cast
      nlinarith

/-- Weighted subset-mean approximation, proved without a probability or
mean-estimation oracle. The tuple has exactly m entries, with replacement. -/
theorem exists_small_mean (x : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < mass w)
    (m : ℕ) (hmpos : 0 < m) :
    ∃ f : Fin m → I, (∀ j, 0 < w (f j)) ∧
      oneCost x w ((m:ℝ)⁻¹ • ∑ j, x (f j)) ≤
        (1 + (m:ℝ)⁻¹) * oneCost x w (mean x w) := by
  classical
  let p : I → ℝ := fun i => w i / mass w
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (hw i) hm.le
  have h1 : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div]
    exact div_self (ne_of_gt hm)
  have hz : ∑ i, p i • (x i - mean x w) = 0 := by
    simp only [p, div_eq_mul_inv, mul_comm (w _) (mass w)⁻¹, mul_smul]
    rw [← Finset.smul_sum, centered_sum x w (ne_of_gt hm), smul_zero]
  obtain ⟨f, hf, hb⟩ := exists_small_sum p (fun i => x i - mean x w) hp h1 hz m
  refine ⟨f, fun j => ((div_pos_iff.mp (hf j)).resolve_right (by rintro ⟨_, h⟩; linarith)).1, ?_⟩
  have hmR : (0:ℝ) < m := by exact_mod_cast hmpos
  have hrepr : (m:ℝ)⁻¹ • (∑ j, (x (f j) - mean x w)) =
      (m:ℝ)⁻¹ • (∑ j, x (f j)) - mean x w := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul]
    rw [inv_mul_cancel₀ (ne_of_gt hmR), one_smul]
  have hv : (∑ i, p i * ‖x i - mean x w‖^2) = oneCost x w (mean x w) / mass w := by
    simp [p, oneCost, div_mul_eq_mul_div, Finset.sum_div]
  rw [hv] at hb
  have hnorm : ‖(m:ℝ)⁻¹ • ∑ j, x (f j) - mean x w‖^2 ≤
      oneCost x w (mean x w) / (mass w * m) := by
    rw [← hrepr, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h := mul_le_mul_of_nonneg_left hb (sq_nonneg ((m:ℝ)⁻¹))
    convert h using 1 <;> field_simp [ne_of_gt hm, ne_of_gt hmR] <;> ring
  rw [variance_identity x w (ne_of_gt hm)]
  rw [norm_sub_rev] at hnorm
  have h := mul_le_mul_of_nonneg_left hnorm hm.le
  have he : mass w * (oneCost x w (mean x w) / (mass w * m)) =
      (m:ℝ)⁻¹ * oneCost x w (mean x w) := by field_simp
  rw [he] at h
  nlinarith

end APC
