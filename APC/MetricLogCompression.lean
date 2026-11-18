import APC.IteratedMetricSampling
import APC.MetricSchedule

open scoped BigOperators
noncomputable section
namespace APC

/-- A fully specified summable failure schedule for the recursive-count
implementation. It deliberately differs from Algorithm 4's size-based
schedule, whose sample-size domination remains separate. -/
def geometricStageFailure (i : ℕ) : ℝ := (1/4)*(1/2)^i

theorem geometricStageFailure_pos (i : ℕ) : 0<geometricStageFailure i := by
  unfold geometricStageFailure
  positivity

theorem geometricStageFailure_sum (n : ℕ) :
    errorBudget geometricStageFailure n = (1/2)*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp [errorBudget]
  | succ n ih =>
    change (∑ i ∈ Finset.range (n+1), geometricStageFailure i)=_
    rw [Finset.sum_range_succ]
    change errorBudget geometricStageFailure n + geometricStageFailure n = _
    rw [ih]
    simp only [geometricStageFailure,pow_succ]
    ring

theorem geometricStageFailure_budget (n : ℕ) : errorBudget geometricStageFailure n≤1/2 := by
  rw [geometricStageFailure_sum]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]

theorem logStageError_pos (x B ε : ℝ) (hB : 0<B) (hε : 0<ε) (i : ℕ) :
    0<logStageError x B ε i :=
  div_pos hε (Real.sqrt_pos.mpr (lt_of_lt_of_le hB (logLevel_lower x B i)))

theorem logStageError_le_one (x B ε : ℝ) (hB : 1≤B) (hε1 : ε≤1) (i : ℕ) :
    logStageError x B ε i≤1 := by
  have hL := logLevel_lower x B i
  have hroot : (1:ℝ)≤Real.sqrt (logLevel x B i) := by
    have hs := Real.sqrt_le_sqrt (le_trans hB hL)
    simpa using hs
  apply (div_le_iff₀ (by linarith : 0<Real.sqrt (logLevel x B i))).2
  linarith

end APC

namespace APC.MetricIteration

/-- A complete finite random experiment for iterated metric compression:
use the verified exact recursive sample counts, stop at the first clamped
iterated logarithm, and round each supplied solution to the final support.
The probability that any supplied α-solution lacks a (4+ε)α lift is ≤1/2.
The near-linear, input-size-independent bound for these recursive counts
is not asserted by this theorem. -/
theorem log_schedule_compression
    {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (a ε : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (proxy : Proxy (K:=K) (X:=X) N a
      (logStageError (N:ℝ) 14400 ε) geometricStageFailure)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) →
      Approximate (cost c.points c.weights) a (proxy n c)) (opt : K → X) :
    let e := logStageError (N:ℝ) 14400 ε
    let δ := geometricStageFailure
    let t := logStop (N:ℝ) 14400
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h =>
      let c := cloud N a e δ initial proxy t h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        ¬∃ f : K → Fin (size N (Fintype.card K) a e δ t),
          cost initial.points initial.weights (fun j => c.points (f j)) ≤
            α*(4+ε)*cost initial.points initial.weights opt) ≤ 1/2 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact (compression initial hw proxy opt ha
    (logStageError_pos (N:ℝ) 14400 ε (by norm_num) hε)
    (logStageError_le_one (N:ℝ) 14400 ε (by norm_num) hε1)
    geometricStageFailure_pos hproxy ε hε.le hε1 (logStop (N:ℝ) 14400)
    (logStageError_rescaled_budget (N:ℝ) ε hN hε.le)).trans
      (geometricStageFailure_budget _)

/-- The same bound for the explicitly defined nearest-point lifting output,
uniformly over every solver solution and approximation factor. -/
theorem log_schedule_rounded_compression
    {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i, 0 < initial.weights i) (a ε : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (proxy : Proxy (K:=K) (X:=X) N a
      (logStageError (N:ℝ) 14400 ε) geometricStageFailure)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) →
      Approximate (cost c.points c.weights) a (proxy n c)) (opt : K → X) :
    let e := logStageError (N:ℝ) 14400 ε
    let δ := geometricStageFailure
    let t := logStop (N:ℝ) 14400
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h =>
      let c := cloud N a e δ initial proxy t h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        α*(4+ε)*cost initial.points initial.weights opt <
          cost initial.points initial.weights (rounded c s)) ≤ 1/2 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact (rounded_compression initial hw proxy opt ha
    (logStageError_pos (N:ℝ) 14400 ε (by norm_num) hε)
    (logStageError_le_one (N:ℝ) 14400 ε (by norm_num) hε1)
    geometricStageFailure_pos hproxy ε hε.le hε1 (logStop (N:ℝ) 14400)
    (logStageError_rescaled_budget (N:ℝ) ε hN hε.le)).trans
      (geometricStageFailure_budget _)

end APC.MetricIteration
