import APC.TwoStage

noncomputable section
namespace APC

/-- A fixed lifting map, uniform over all α-approximate summary solutions.
This definition specifies a mathematical guarantee, not computational cost. -/
def APCWithLift {Solution : Type*} (p q : Solution → ℝ) (β : ℝ)
    (lift : Solution → Solution) : Prop :=
  ∀ α, 1 ≤ α → ∀ s, Approximate q α s → Approximate p (α*β) (lift s)

variable {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The choice uses only the summary, the input solution, and m.
It has no access to the original input, optimum, or approximation factor. -/
def geometricLift (x : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (hm : 0 < m) (s : K → E) : K → E :=
  Classical.choose (exists_structured_lift x w hw s m hm)

theorem geometricLift_spec (x : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (hm : 0 < m) (s : K → E) :
    geometricLift x w hw m hm s ∈ witnessFamily x m ∧
      cost x w (geometricLift x w hw m hm s) ≤ (1+(m:ℝ)⁻¹)*cost x w s :=
  Classical.choose_spec (exists_structured_lift x w hw s m hm)

/-- Definition 1.1's approximation guarantee follows from preservation.
The lifting map is fixed before α and s are quantified. -/
theorem euclidean_apc_fixed_lift
    (x : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (p : (K → E) → ℝ) (opt : K → E)
    (hopt_nonneg : 0 ≤ p opt) (hoptimal : ∀ c, p opt ≤ p c)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (hm : 0 < m) (hmε : (m:ℝ)⁻¹ ≤ ε/10)
    (hpres : ∀ c ∈ witnessFamily (K := K) x m, Preserves (p c) (cost x w c) (ε/10))
    (hopt : Preserves (p opt) (cost x w opt) (ε/10)) :
    APCWithLift p (cost x w) (1+ε) (geometricLift x w hw m hm) := by
  intro α hα s hs c
  obtain ⟨hmemb, hbound⟩ := geometricLift_spec x w hw m hm s
  have hb := euclidean_transfer_rescaled p (cost x w) s (geometricLift x w hw m hm s) opt
    α ε (by linarith) hε.le hε1 hopt_nonneg hs
    (hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (cost_nonneg x w hw s)))
    (hpres _ hmemb) hopt
  exact hb.trans (mul_le_mul_of_nonneg_left (hoptimal c) (by positivity))

end APC
