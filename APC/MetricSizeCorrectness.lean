import APC.MetricSize

open scoped BigOperators
noncomputable section
namespace APC

/-- The constant-factor-one specialization displays the exact near-linear
parameter dependence, without an asymptotic convention. -/
theorem metricSizeBase_one (k : ℕ) (ε : ℝ) :
    metricSizeBase k 1 ε = 2025*(289+336*(k:ℝ))/ε^2 := by
  unfold metricSizeBase
  ring

end APC
namespace APC.MetricIteration

/-- Distinct support size is bounded by the same parameter-only envelope
as the number of draws; repeated sampled points only reduce the support. -/
theorem terminal_support_bound
    {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X] [DecidableEq X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X) (a ε : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (proxy : Proxy (K:=K) (X:=X) N a
      (logStageError (N:ℝ) 14400 ε) (scheduledFailure N))
    (h : Adaptive.History
      (outcomes N (Fintype.card K) a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N))
      (logStop (N:ℝ) 14400)) :
    let c := cloud N a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
      initial proxy (logStop (N:ℝ) 14400) h
    ((Finset.univ.image c.points).card:ℝ) ≤ metricSizeGamma (Fintype.card K) a ε*14400^2 := by
  classical
  have hc : (Finset.univ.image
      (cloud N a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
        initial proxy (logStop (N:ℝ) 14400) h).points).card ≤
      size N (Fintype.card K) a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
        (logStop (N:ℝ) 14400) := by
    exact Finset.card_image_le.trans (by simp)
  exact (Nat.cast_le.mpr hc).trans
    (terminal_size_bound N (Fintype.card K) Fintype.card_pos a ε ha hε hε1)

/-- Size and returned-center correctness of one and the same finite-metric
construction. No preservation, sample-budget or proxy premise is supplied.
The proxy is exact finite search, so no efficient-runtime claim is made. -/
theorem finite_metric_size_and_correctness
    {K X : Type*} [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    let e := logStageError (N:ℝ) 14400 ε
    let δ := scheduledFailure N
    let proxy := exactProxy (K:=K) (X:=X) N e δ
    let t := logStop (N:ℝ) 14400
    (size N (Fintype.card K) 1 e δ t:ℝ) ≤
      metricSizeGamma (Fintype.card K) 1 ε*14400^2 ∧
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h =>
      let c := cloud N 1 e δ initial proxy t h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        ¬Approximate (cost initial.points initial.weights) (α*(4+ε)) (rounded c s)) ≤ 1/2 := by
  exact ⟨terminal_size_bound N (Fintype.card K) Fintype.card_pos 1 ε (by norm_num) hε hε1,
    finite_metric_correctness N initial hw ε hε hε1⟩

end APC.MetricIteration
