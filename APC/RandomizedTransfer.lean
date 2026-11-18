import APC.LiftingCounts
import APC.Transfer

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable
variable {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Approximation preservation for the actual joint randomized output.
The original objective is used only in the guarantee, not by randomLift. -/
theorem randomized_apc_failure
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (original : (K → E) → ℝ) (opt s : K → E) (α ε : ℝ)
    (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1) (hopt_nonneg : 0≤original opt)
    (happrox : Approximate (cost x w) α s)
    (m r : ℕ) [NeZero r] (hm : 0<m) (hmε : 3≤(m:ℝ)*(ε/10))
    (hpres : ∀ c∈witnessFamily (K:=K) x m,Preserves (original c) (cost x w c) (ε/10))
    (hopt : Preserves (original opt) (cost x w opt) (ε/10)) :
    eventMass (liftingTrialsLaw x w s m r)
      (fun sample=>α*(1+ε)*original opt<original (randomLift x w s m r sample))≤
      (Fintype.card K:ℝ)*(1/3:ℝ)^r := by
  have hp := liftingTrialsLaw_nonneg x w hw s m r
  have hc : ∀ sample,α*(1+ε)*original opt<original (randomLift x w s m r sample)→
      (1+ε/10)*cost x w s<cost x w (randomLift x w s m r sample) := by
    intro sample hs
    by_contra hn
    have hb := euclidean_transfer_rescaled original (cost x w) s (randomLift x w s m r sample) opt
      α ε hα hε.le hε1 hopt_nonneg happrox (le_of_not_gt hn)
      (hpres _ (randomLift_mem_witness x w s m r sample)) hopt
    exact not_lt_of_ge hb hs
  exact (eventMass_mono _ hp _ _ hc).trans
    (randomized_lifting_failure x w hw s m r hm (ε/10) (by positivity) hmε)

theorem randomized_apc_explicit
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (original : (K → E) → ℝ) (opt s : K → E) (α ε : ℝ)
    (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1) (hopt_nonneg : 0≤original opt)
    (happrox : Approximate (cost x w) α s)
    (hpres : ∀ c∈witnessFamily (K:=K) x (liftingSampleCount (ε/10)),
      Preserves (original c) (cost x w c) (ε/10))
    (hopt : Preserves (original opt) (cost x w opt) (ε/10)) :
    let m := liftingSampleCount (ε/10)
    let r := liftingRepetitions (Fintype.card K)
    eventMass (liftingTrialsLaw x w s m r)
      (fun sample=>α*(1+ε)*original opt<original (randomLift x w s m r sample))≤1/3 := by
  have hm := liftingSampleCount_valid (ε/10) (by positivity)
  exact (randomized_apc_failure x w hw original opt s α ε hα hε hε1 hopt_nonneg happrox
    (liftingSampleCount (ε/10)) (liftingRepetitions _) hm.1 hm.2 hpres hopt).trans
      (liftingRepetitions_bound _)

end APC
