import APC.EuclideanRandomCompletion
import APC.EuclideanSize

open scoped BigOperators
noncomputable section
namespace APC

/-- Explicit inverse-cubic envelope, with conservative absolute constants. -/
def euclideanCubicBase (k : ℕ) (ε : ℝ) : ℝ := 643464225*(k:ℝ)/ε^3

def euclideanCubicSize (k : ℕ) (ε : ℝ) : ℝ :=
  Real.exp 16*euclideanCubicBase k ε*(1+Real.log (euclideanCubicBase k ε))*14400^2

/-- The only extra center-count factor is the lifting witness length,
which is at most 32/ε. Hence the actual envelope is inverse-cubic. -/
theorem euclideanCubicBase_dominates (k : ℕ) (hk : 0<k)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    metricSizeBase (liftingSampleCount (ε/10)*k) 4 ε≤euclideanCubicBase k ε := by
  let t := liftingSampleCount (ε/10)
  have ht := liftingSampleCount_scaled_upper ε hε hε1
  have htε : (t:ℝ)*ε≤32 := (le_div_iff₀ hε).mp ht
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hprod := mul_le_mul_of_nonneg_right htε (Nat.cast_nonneg k : (0:ℝ)≤k)
  have hεk : ε≤(k:ℝ) := by linarith
  have he : metricSizeBase (t*k) 4 ε*ε^3=
      12321*(1537*ε+1584*(t:ℝ)*(k:ℝ)*ε) := by
    unfold metricSizeBase
    push_cast
    field_simp
    ring
  unfold euclideanCubicBase
  apply (le_div_iff₀ (pow_pos hε 3)).2
  change metricSizeBase (t*k) 4 ε*ε^3≤_
  nlinarith only [he,hprod,hεk]

theorem euclideanCubicSize_dominates (k : ℕ) (hk : 0<k)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    metricSizeGamma (liftingSampleCount (ε/10)*k) 4 ε*14400^2≤euclideanCubicSize k ε := by
  let H := metricSizeBase (liftingSampleCount (ε/10)*k) 4 ε
  let J := euclideanCubicBase k ε
  have hH : 1≤H := (metricSizeBase_bounds _ 4 ε (by norm_num) hε hε1).1
  have hHp : 0<H := by linarith
  have hHJ : H≤J := euclideanCubicBase_dominates k hk ε hε hε1
  have hJ : 0≤J := by linarith
  have hlog : 1+Real.log H≤1+Real.log J := add_le_add_left (Real.log_le_log hHp hHJ) 1
  have hT : 0≤1+Real.log H := by linarith [Real.log_nonneg hH]
  have hh := mul_le_mul hHJ hlog hT hJ
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (Real.exp_pos 16).le) (sq_nonneg (14400:ℝ))
  simpa only [metricSizeGamma,euclideanCubicSize,H,J,mul_assoc] using hm

end APC
namespace APC.EuclideanIteration
local instance (T : Type*) : DecidableEq T := Classical.decEq T
open MetricIteration (Cloud size outcomes)

/-- Final unconditional approximation-and-size theorem. The finite input
is compressed to a positive weighted sample of its own points, with a fixed
summary-only lift valid for all approximation factors and solutions. No
strong-coreset, concentration, geometry, or proxy theorem is assumed. This
alternative iterative algorithm does not verify the paper's fast two-stage
preprocessing implementation. -/
theorem euclidean_approximation_preserving_coreset
    {K E : Type*} [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    let t := liftingSampleCount (ε/10)
    let ht := (liftingWitnessCount_valid ε hε).1
    let e := logStageError (N:ℝ) 14400 ε
    let δ := MetricIteration.scheduledFailure N
    let proxy := searchProxy (K:=K) (E:=E) N e δ t
    let n := logStop (N:ℝ) 14400
    (size N (t*Fintype.card K) 4 e δ n:ℝ)≤euclideanCubicSize (Fintype.card K) ε ∧
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h=>
      ¬SummaryAPC (K:=K) initial (cloud N 4 e δ t initial proxy n h)
        (fun i=>(cloud_pos initial hw proxy n h i).le) ε t ht)≤1/2 := by
  have hb := unconditional_euclidean_apc (K:=K) N initial hw ε hε hε1
  exact ⟨hb.1.trans (euclideanCubicSize_dominates (Fintype.card K) Fintype.card_pos ε hε hε1),hb.2⟩

/-- Actual returned centers with the same explicit inverse-cubic size bound. -/
theorem euclidean_randomized_apc
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
    (size N (t*Fintype.card K) 4 e δ n:ℝ)≤euclideanCubicSize (Fintype.card K) ε ∧
    eventMass (kernelWeight (Adaptive.historyWeight (transition initial proxy) n) liftLaw)
      (fun sample=>¬Approximate (cost initial.points initial.weights) (α*(1+ε))
        (randomLift (cloud N 4 e δ t initial proxy n sample.1).points
          (cloud N 4 e δ t initial proxy n sample.1).weights (solve sample.1) t r sample.2))≤2/3 := by
  have hb := unconditional_randomized_euclidean_apc N initial hw α ε hα hε hε1 solve hsolve
  exact ⟨hb.1.trans (euclideanCubicSize_dominates (Fintype.card K) Fintype.card_pos ε hε hε1),hb.2⟩

end APC.EuclideanIteration
