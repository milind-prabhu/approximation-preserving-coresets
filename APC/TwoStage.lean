import APC.Lifting

noncomputable section
namespace APC

/-- The main Euclidean reduction with the two sampling stages kept separate.
Theorems 2.1 and 2.2 must supply hstrong, hsecond, and hsecond_opt.
This theorem does not assert their probability or the sample-size bound. -/
theorem euclidean_two_stage
    {I B K E : Type*} [Fintype I] [Nonempty I] [Fintype B]
    [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (b : B → E) (embed : I → B) (he : ∀ i, b (embed i) = x i)
    (original intermediate : (K → E) → ℝ)
    (hnonneg : ∀ c, 0 ≤ original c)
    (opt s : K → E) (α ε : ℝ)
    (hα : 0 ≤ α) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : Approximate (cost x w) α s)
    (m : ℕ) (hm : 0 < m) (hmε : (m:ℝ)⁻¹ ≤ ε/10)
    (hstrong : ∀ c, Preserves (original c) (intermediate c) (ε/100))
    (hsecond : ∀ c ∈ witnessFamily (K := K) b m,
      Preserves (intermediate c) (cost x w c) (ε/100))
    (hsecond_opt : Preserves (intermediate opt) (cost x w opt) (ε/100)) :
    ∃ out : K → E, out ∈ witnessFamily b m ∧
      original out ≤ α * (1 + ε) * original opt := by
  have herr : 2*(ε/100) + (ε/100)^2 ≤ ε/10 := by
    have : ε * (1-ε) ≥ 0 := mul_nonneg hε.le (by linarith)
    nlinarith
  have hcompose : ∀ c, Preserves (intermediate c) (cost x w c) (ε/100) →
      Preserves (original c) (cost x w c) (ε/10) := by
    intro c hc
    exact preserves_mono (hnonneg c) herr
      (preserves_compose (hnonneg c) (by linarith) (by linarith) (hstrong c) hc)
  obtain ⟨out, hout, hb⟩ := euclidean_apc_of_preservation x w hw original opt s α ε
    hα hε hε1 (hnonneg opt) happrox m hm hmε
    (fun c hc => hcompose c (hsecond c (witnessFamily_mono x b embed he m c hc)))
    (hcompose opt hsecond_opt)
  exact ⟨out, witnessFamily_mono x b embed he m out hout, hb⟩

end APC
