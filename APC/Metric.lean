import APC.Clustering
import APC.Transfer

noncomputable section
namespace APC

theorem metric_factor (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    4 * ((1 + ε/20) / (1 - ε/20)) ≤ 4 + ε := by
  have hden : 0 < 1 - ε/20 := by linarith
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hε1)]

/-- General-metric APC reduction after cost preservation has been proved.
The iterative sampling construction that supplies hpres is not assumed as
an axiom and is not proved in this file. -/
theorem metric_apc_of_preservation
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (original : (K → X) → ℝ) (opt s : K → X) (α ε : ℝ)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hopt_nonneg : 0 ≤ original opt)
    (happrox : Approximate (cost x w) α s)
    (hpres : ∀ f : K → I,
      Preserves (original (fun j => x (f j))) (cost x w (fun j => x (f j))) (ε/20))
    (hopt : Preserves (original opt) (cost x w opt) (ε/20)) :
    ∃ f : K → I,
      original (fun j => x (f j)) ≤ α * (4 + ε) * original opt := by
  let f : K → I := fun j => nearest x (s j)
  let out : K → X := fun j => x (f j)
  have hlift : cost x w out ≤ 4 * cost x w s := by
    apply metric_rounding x w hw s out
    intro j i
    exact nearest_le x (s j) i
  have hb := witness_transfer original (cost x w) s out opt α 4 (ε/20)
    hα (by norm_num) (by linarith) happrox hlift (hpres f).1 hopt.2
  refine ⟨f, hb.trans ?_⟩
  calc
    α * 4 * ((1+ε/20)/(1-ε/20)) * original opt =
        α * (4 * ((1+ε/20)/(1-ε/20))) * original opt := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (metric_factor ε hε hε1) hα) hopt_nonneg

end APC
