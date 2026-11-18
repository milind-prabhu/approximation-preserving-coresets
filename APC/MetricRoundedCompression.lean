import APC.IteratedMetricSampling
import APC.MetricSchedule

open scoped BigOperators
noncomputable section
namespace APC.MetricIteration

/-- A level-based failure schedule. Unlike a geometrically decreasing
schedule in the forward iteration index, its terminal budgets do not
shrink as the log-star stopping index increases. -/
def scheduledFailure (N : ℕ) : ℕ → ℝ := metricStageFailure 1 (N:ℝ) 14400

theorem scheduledFailure_pos (N : ℕ) [NeZero N] (i : ℕ) :
    0<scheduledFailure N i := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold scheduledFailure metricStageFailure
  split_ifs
  · positivity
  · unfold metricCountFailure
    have hp := metricIterationCount_pos 1 (N:ℝ) 14400 (by norm_num) (by norm_num) (i-1)
    exact one_div_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hp))

theorem scheduledFailure_budget (N : ℕ) [NeZero N] :
    errorBudget (scheduledFailure N) (logStop (N:ℝ) 14400) ≤ 1/2 := by
  have hN : (1:ℝ)≤N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact metricStageFailure_half 1 (N:ℝ) 14400 hN (by norm_num) (by norm_num) (by norm_num)

theorem scheduledError_pos (N : ℕ) (ε : ℝ) (hε : 0<ε) (i : ℕ) :
    0<logStageError (N:ℝ) 14400 ε i := by
  have hp : 0<logLevel (N:ℝ) 14400 i := lt_of_lt_of_le (by norm_num) (logLevel_lower _ _ _)
  exact div_pos hε (Real.sqrt_pos.mpr hp)

theorem scheduledError_le_one (N : ℕ) (ε : ℝ) (hε : ε≤1) (i : ℕ) :
    logStageError (N:ℝ) 14400 ε i≤1 := by
  have hl := logLevel_lower (N:ℝ) 14400 i
  have hr : (1:ℝ)≤Real.sqrt (logLevel (N:ℝ) 14400 i) := by
    have hh := Real.sqrt_le_sqrt (by linarith : (1:ℝ)≤logLevel (N:ℝ) 14400 i)
    simpa only [Real.sqrt_one] using hh
  apply (div_le_iff₀ (by linarith : 0<Real.sqrt (logLevel (N:ℝ) 14400 i))).2
  linarith

/-- Concrete stopping rule, concrete counts and concrete failure schedule,
with a bound on the actual rounded output, uniformly over input solutions.
The near-linear, input-size-independent size bound is still separate. -/
theorem scheduled_rounded_compression
    {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (a ε : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (proxy : Proxy (K:=K) (X:=X) N a
      (logStageError (N:ℝ) 14400 ε) (scheduledFailure N))
    (hproxy : ∀ n c, (∀ j,0<c.weights j) →
      Approximate (cost c.points c.weights) a (proxy n c)) (opt : K → X) :
    let e := logStageError (N:ℝ) 14400 ε
    let δ := scheduledFailure N
    let t := logStop (N:ℝ) 14400
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h =>
      let c := cloud N a e δ initial proxy t h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        α*(4+ε)*cost initial.points initial.weights opt <
          cost initial.points initial.weights (rounded c s)) ≤ 1/2 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact (rounded_compression initial hw proxy opt ha (scheduledError_pos N ε hε)
    (scheduledError_le_one N ε hε1) (scheduledFailure_pos N) hproxy ε hε.le hε1
    (logStop (N:ℝ) 14400) (logStageError_rescaled_budget (N:ℝ) ε hN hε.le)).trans
    (scheduledFailure_budget N)

section FiniteAmbient
variable {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K]
  [Fintype X] [Nonempty X] [PseudoMetricSpace X]

/-- An exact finite search proxy removes the approximation-oracle premise.
This definition asserts mathematical correctness, with no runtime claim. -/
def optimalProxy (c : Cloud I X) : K → X := by
  classical
  exact Classical.choose (Finset.exists_min_image Finset.univ (cost c.points c.weights)
    Finset.univ_nonempty)

theorem optimalProxy_spec (c : Cloud I X) :
    Approximate (cost c.points c.weights) 1 (optimalProxy (K:=K) c) := by
  classical
  intro s
  have hh := (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (cost c.points c.weights) Finset.univ_nonempty)).2 s (Finset.mem_univ s)
  simpa only [one_mul] using hh

end FiniteAmbient

def exactProxy {K X : Type*} [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (N : ℕ) (e δ : ℕ → ℝ) : Proxy (K:=K) (X:=X) N 1 e δ := fun _ c => optimalProxy c

/-- Finite-metric construction with no supplied proxy or cost-preservation
premise. Exhaustive finite proxies and the actual repeated sensitivity
sampling produce a uniformly valid summary-only rounding guarantee with
failure at most 1/2. The size asymptotics and runtime are not asserted. -/
theorem finite_metric_correctness
    {K X : Type*} [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    let e := logStageError (N:ℝ) 14400 ε
    let δ := scheduledFailure N
    let proxy := exactProxy (K:=K) (X:=X) N e δ
    let t := logStop (N:ℝ) 14400
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h =>
      let c := cloud N 1 e δ initial proxy t h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        ¬Approximate (cost initial.points initial.weights) (α*(4+ε)) (rounded c s)) ≤ 1/2 := by
  classical
  let e := logStageError (N:ℝ) 14400 ε
  let δ := scheduledFailure N
  let proxy := exactProxy (K:=K) (X:=X) N e δ
  let opt := optimalProxy (K:=K) initial
  have hb := scheduled_rounded_compression N initial hw 1 ε (by norm_num) hε hε1 proxy
    (fun _ c _ => optimalProxy_spec c) opt
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) _) _ _ ?_) hb
  intro h hbad
  obtain ⟨α,s,hα,happrox,hno⟩ := hbad
  refine ⟨α,s,hα,happrox,?_⟩
  by_contra hn
  apply hno
  intro u
  have hbest : cost initial.points initial.weights opt ≤ cost initial.points initial.weights u := by
    simpa only [one_mul] using optimalProxy_spec initial u
  exact (le_of_not_gt hn).trans (mul_le_mul_of_nonneg_left hbest (by positivity))

end APC.MetricIteration
