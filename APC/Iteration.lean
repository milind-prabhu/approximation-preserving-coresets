import APC.Metric
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
noncomputable section
namespace APC

/-- The sum of the first n local relative errors. -/
def errorBudget (e : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, e i

theorem errorBudget_nonneg (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (n : ℕ) :
    0 ≤ errorBudget e n := Finset.sum_nonneg (fun i _ => he i)

theorem errorBudget_mono (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) :
    Monotone (errorBudget e) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [errorBudget, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (he n)

/-- Division-free product bounds. Unlike repeated equal-error composition,
these bounds depend only on the sum of the local errors. -/
theorem iteration_product_bounds (c e : ℕ → ℝ) (n : ℕ)
    (hc : 0 ≤ c 0) (he : ∀ i, 0 ≤ e i)
    (hbudget : errorBudget e n ≤ 1/2)
    (hstep : ∀ i, i < n → Preserves (c i) (c (i+1)) (e i)) :
    0 ≤ c n ∧ (1-errorBudget e n)*c 0 ≤ c n ∧
      (1-errorBudget e n)*c n ≤ c 0 := by
  induction n with
  | zero => simpa [errorBudget] using And.intro hc (And.intro (le_refl (c 0)) (le_refl (c 0)))
  | succ n ih =>
    have hS := errorBudget_nonneg e he n
    have hrec : errorBudget e (n+1) = errorBudget e n + e n := by
      simp [errorBudget, Finset.sum_range_succ]
    have hbn : errorBudget e n ≤ 1/2 := by rw [hrec] at hbudget; linarith [he n]
    obtain ⟨hcn, hlo, hup⟩ := ih hbn (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨hnextlo, hnexthi⟩ := hstep n (Nat.lt_succ_self n)
    have hen : e n ≤ 1/2 := by rw [hrec] at hbudget; linarith
    have hnonneg : 0 ≤ c (n+1) := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-e n) hcn]
    rw [hrec]
    refine ⟨hnonneg, ?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ 1-e n)
      have hextra := mul_nonneg (mul_nonneg (he n) hS) hc
      nlinarith only [h, hnextlo, hextra]
    · have h := mul_le_mul_of_nonneg_left hnexthi
        (by rw [hrec] at hbudget; linarith : 0 ≤ 1-(errorBudget e n+e n))
      have hcross := mul_nonneg (he n) hS
      have hsq := sq_nonneg (e n)
      have hx := mul_nonneg (by nlinarith : 0 ≤ e n*errorBudget e n+(e n)^2) hcn
      nlinarith only [h, hup, hx]

/-- Standard relative preservation after an arbitrary number of stages. -/
theorem iteration_preserves (c e : ℕ → ℝ) (n : ℕ)
    (hc : 0 ≤ c 0) (he : ∀ i, 0 ≤ e i)
    (hbudget : errorBudget e n ≤ 1/2)
    (hstep : ∀ i, i < n → Preserves (c i) (c (i+1)) (e i)) :
    Preserves (c 0) (c n) (2*errorBudget e n) := by
  obtain ⟨hcn, hlo, hup⟩ := iteration_product_bounds c e n hc he hbudget hstep
  have hS := errorBudget_nonneg e he n
  constructor
  · nlinarith [mul_nonneg hS hc]
  · have h := mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 1+2*errorBudget e n)
    have hextra : 0 ≤ (errorBudget e n*(1-2*errorBudget e n))*c n :=
      mul_nonneg (mul_nonneg hS (by linarith)) hcn
    nlinarith only [h, hextra]

/-- A tuple supported by the final summary is supported by every earlier
summary, even when the supports and weights change between stages. -/
theorem final_centers_supported {K X : Type*} (support : ℕ → Set X)
    (hnest : ∀ i, support (i+1) ⊆ support i) (n i : ℕ) (hi : i ≤ n)
    (s : K → X) (hs : ∀ j, s j ∈ support n) : ∀ j, s j ∈ support i := by
  have hanti : Antitone support := antitone_nat_of_succ_le hnest
  exact fun j => hanti hi (hs j)

/-- Section 4's deterministic telescoping argument for both final-support
queries and the fixed optimum. Local preservation is needed only on the
preceding support, together with that optimum. -/
theorem metric_iteration_preserves {K X : Type*}
    (support : ℕ → Set X) (hnest : ∀ i, support (i+1) ⊆ support i)
    (c : ℕ → (K → X) → ℝ) (hc : ∀ s, 0 ≤ c 0 s)
    (opt : K → X) (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (n : ℕ)
    (hbudget : errorBudget e n ≤ 1/2)
    (hstep : ∀ i, i < n → ∀ s, (∀ j, s j ∈ support i) ∨ s=opt →
      Preserves (c i s) (c (i+1) s) (e i)) :
    ∀ s, (∀ j, s j ∈ support n) ∨ s=opt →
      Preserves (c 0 s) (c n s) (2*errorBudget e n) := by
  intro s hs
  apply iteration_preserves (fun i => c i s) e n (hc s) he hbudget
  intro i hi
  apply hstep i hi s
  rcases hs with hs | hs
  · exact Or.inl (final_centers_supported support hnest n i (Nat.le_of_lt hi) s hs)
  · exact Or.inr hs

/-- Final-center guarantee from the complete chain of local events. The
only remaining iteration premises are its local events and summed budget;
there is no assumed final preservation guarantee. -/
theorem metric_apc_of_iteration
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (support : ℕ → Set X) (hnest : ∀ i, support (i+1) ⊆ support i)
    (c : ℕ → (K → X) → ℝ) (hc : ∀ s, 0 ≤ c 0 s)
    (opt s : K → X) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (n : ℕ)
    (hbudget : errorBudget e n ≤ ε/40)
    (hfinal : ∀ s, c n s = cost x w s)
    (hsupport : ∀ i, x i ∈ support n)
    (hstep : ∀ i, i < n → ∀ s, (∀ j, s j ∈ support i) ∨ s=opt →
      Preserves (c i s) (c (i+1) s) (e i))
    (happrox : Approximate (cost x w) α s) :
    ∃ f : K → I, c 0 (fun j => x (f j)) ≤ α*(4+ε)*c 0 opt := by
  have hchain := metric_iteration_preserves support hnest c hc opt e he n
    (by linarith : errorBudget e n ≤ 1/2) hstep
  have hpres : ∀ u, (∀ j, u j ∈ support n) ∨ u=opt →
      Preserves (c 0 u) (cost x w u) (ε/20) := by
    intro u hu
    rw [← hfinal u]
    exact preserves_mono (hc u) (by linarith) (hchain u hu)
  exact metric_apc_of_preservation x w hw (c 0) opt s α ε hα hε hε1 (hc opt)
    happrox (fun f => hpres _ (Or.inl (fun j => hsupport (f j))))
    (hpres opt (Or.inr rfl))

end APC
