import APC.EuclideanCompletion
import APC.SharpKernel

open scoped BigOperators
noncomputable section
namespace APC.EuclideanIteration
local instance (T : Type*) : DecidableEq T := Classical.decEq T
open MetricIteration (Cloud size outcomes)

section
variable {K E : Type*} [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : ℕ} [NeZero N] {a : ℝ} {e δ : ℕ → ℝ} {t : ℕ}

/-- Actual randomized lifting after the iterative Euclidean sampler.
The solver and lifting law may depend on the entire sampling history. -/
theorem randomized_compression (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=E) N a e δ t)
    (opt : K → E) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n) (hδ1 : ∀ n,δ n≤1)
    (hproxy : ∀ n c,(∀ j,0<c.weights j)→Approximate (cost c.points c.weights) a (proxy n c))
    (α ε : ℝ) (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1) (ht : 0<t)
    (htε : 3≤(t:ℝ)*(ε/10)) (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (solve : Adaptive.History (outcomes N (t*Fintype.card K) a e δ) n → K → E)
    (hsolve : ∀ h,Approximate
      (cost (cloud N a e δ t initial proxy n h).points (cloud N a e δ t initial proxy n h).weights) α (solve h)) :
    let r := liftingRepetitions (Fintype.card K)
    let liftLaw := fun h=>liftingTrialsLaw (cloud N a e δ t initial proxy n h).points
      (cloud N a e δ t initial proxy n h).weights (solve h) t r
    eventMass (kernelWeight (Adaptive.historyWeight (transition initial proxy) n) liftLaw)
      (fun sample=>α*(1+ε)*cost initial.points initial.weights opt<cost initial.points initial.weights
        (randomLift (cloud N a e δ t initial proxy n sample.1).points
          (cloud N a e δ t initial proxy n sample.1).weights (solve sample.1) t r sample.2))≤
      1/3+(1-1/3)*errorBudget δ n := by
  classical
  dsimp only
  let r := liftingRepetitions (Fintype.card K)
  let liftLaw := fun h=>liftingTrialsLaw (cloud N a e δ t initial proxy n h).points
    (cloud N a e δ t initial proxy n h).weights (solve h) t r
  have hfirst := all_stages_failure initial hw proxy opt ha he he1 hδ hδ1 ht hproxy n
  apply kernel_event_bound_sharp _ liftLaw
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n)
    (Adaptive.historyWeight_sum _ (transition_sum initial hw proxy) n)
    (fun h=>liftingTrialsLaw_nonneg _ _ (fun i=>(cloud_pos initial hw proxy n h i).le) _ t r)
    (fun h=>liftingTrialsLaw_sum _ _ _ t r)
    (Adaptive.historyGood (good initial proxy opt) n)
    (fun h z=>α*(1+ε)*cost initial.points initial.weights opt<cost initial.points initial.weights
      (randomLift (cloud N a e δ t initial proxy n h).points
        (cloud N a e δ t initial proxy n h).weights (solve h) t r z)) (errorBudget δ n) (1/3)
    (by norm_num) (by norm_num) hfirst
  intro h hh
  let c := cloud N a e δ t initial proxy n h
  have hp := final_witness_preservation initial hw proxy opt (fun i=>(he i).le)
    ε hε.le hε1 n hbudget h hh
  exact (randomized_apc_failure c.points c.weights (fun i=>(cloud_pos initial hw proxy n h i).le)
    (cost initial.points initial.weights) opt (solve h) α ε hα hε hε1
    (cost_nonneg _ _ (fun i=>(hw i).le) opt) (hsolve h) t r ht htε
    (fun u hu=>hp u (Or.inl hu)) (hp opt (Or.inr rfl))).trans (liftingRepetitions_bound _)

end

/-- Unconditional returned-center guarantee for arbitrary-k Euclidean APCs,
using the alternative iterative sampler. No strong-coreset or proxy oracle
is assumed. The only solver premise is its stated approximation guarantee
on the final summary. The size is independent of input cardinality and
ambient dimension, and the actual returned-center success is at least 1/3. -/
theorem unconditional_randomized_euclidean_apc
    {K E : Type*} [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (α ε : ℝ) (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1)
    (solve : Adaptive.History (outcomes N (liftingSampleCount (ε/10)*Fintype.card K) 4
      (logStageError (N:ℝ) 14400 ε) (MetricIteration.scheduledFailure N))
      (logStop (N:ℝ) 14400) → K → E)
    (hsolve : ∀ h,
      let t := liftingSampleCount (ε/10)
      let e := logStageError (N:ℝ) 14400 ε
      let δ := MetricIteration.scheduledFailure N
      let proxy := searchProxy (K:=K) (E:=E) N e δ t
      let c := cloud N 4 e δ t initial proxy (logStop (N:ℝ) 14400) h
      Approximate (cost c.points c.weights) α (solve h)) :
    let t := liftingSampleCount (ε/10)
    let e := logStageError (N:ℝ) 14400 ε
    let δ := MetricIteration.scheduledFailure N
    let proxy := searchProxy (K:=K) (E:=E) N e δ t
    let n := logStop (N:ℝ) 14400
    let r := liftingRepetitions (Fintype.card K)
    let liftLaw := fun h=>liftingTrialsLaw (cloud N 4 e δ t initial proxy n h).points
      (cloud N 4 e δ t initial proxy n h).weights (solve h) t r
    (size N (t*Fintype.card K) 4 e δ n:ℝ)≤metricSizeGamma (t*Fintype.card K) 4 ε*14400^2 ∧
    eventMass (kernelWeight (Adaptive.historyWeight (transition initial proxy) n) liftLaw)
      (fun sample=>¬Approximate (cost initial.points initial.weights) (α*(1+ε))
        (randomLift (cloud N 4 e δ t initial proxy n sample.1).points
          (cloud N 4 e δ t initial proxy n sample.1).weights (solve sample.1) t r sample.2))≤2/3 := by
  classical
  dsimp only
  let t := liftingSampleCount (ε/10)
  let e := logStageError (N:ℝ) 14400 ε
  let δ := MetricIteration.scheduledFailure N
  let proxy := searchProxy (K:=K) (E:=E) N e δ t
  let n := logStop (N:ℝ) 14400
  let r := liftingRepetitions (Fintype.card K)
  let liftLaw := fun h=>liftingTrialsLaw (cloud N 4 e δ t initial proxy n h).points
    (cloud N 4 e δ t initial proxy n h).weights (solve h) t r
  let opt := euclideanOptimal (K:=K) initial.points initial.weights
  have ho := euclideanOptimal_spec (K:=K) initial.points initial.weights (fun i=>(hw i).le)
  have ht := liftingSampleCount_valid (ε/10) (by positivity)
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hb := randomized_compression initial hw proxy opt (by norm_num)
    (MetricIteration.scheduledError_pos N ε hε) (MetricIteration.scheduledError_le_one N ε hε1)
    (MetricIteration.scheduledFailure_pos N) (MetricIteration.scheduledFailure_le_one N)
    (searchProxy_spec N e δ t) α ε hα hε hε1 ht.1 ht.2 n
    (logStageError_rescaled_budget (N:ℝ) ε hN hε.le) solve hsolve
  have hfail : 1/3+(1-1/3)*errorBudget δ n≤(2:ℝ)/3 := by
    have hh := MetricIteration.scheduledFailure_budget N
    change errorBudget δ n≤1/2 at hh
    linarith
  refine ⟨MetricIteration.terminal_size_bound N (t*Fintype.card K)
    (Nat.mul_pos ht.1 Fintype.card_pos) 4 ε (by norm_num) hε hε1,?_⟩
  apply le_trans (eventMass_mono _
    (kernelWeight_nonneg _ liftLaw
      (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n)
      (fun h=>liftingTrialsLaw_nonneg _ _ (fun i=>(cloud_pos initial hw proxy n h i).le) _ t r)) _ _ ?_)
    (hb.trans hfail)
  intro sample hbad
  by_contra hn
  apply hbad
  intro u
  have hopt : cost initial.points initial.weights opt≤cost initial.points initial.weights u := by
    simpa only [one_mul] using ho u
  exact (le_of_not_gt hn).trans (mul_le_mul_of_nonneg_left hopt (by positivity))

end APC.EuclideanIteration
