import APC.MetricRoundedCompression

/-!
# Parameter-only bounds for the actual recursive metric sampler

The previous size is used inside a logarithm by the concentration count.
We control that logarithm using the preceding level's quadratic envelope.
The auxiliary failure schedule uses ceil(L²), so its reciprocal contributes
only another logarithm of the level, without dependence on the forward
iteration number. The slack in exp(16) absorbs rounding and all constants.
-/

set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace APC

def metricSizeBase (k : ℕ) (a ε : ℝ) : ℝ :=
  (1+48*(k:ℝ)+(4*(64*a+8*a^2))*(1+(k:ℝ)))*(23+22*a)^2/ε^2

def metricSizeGamma (k : ℕ) (a ε : ℝ) : ℝ :=
  Real.exp 16 * metricSizeBase k a ε * (1+Real.log (metricSizeBase k a ε))

theorem metricSizeBase_bounds (k : ℕ) (a ε : ℝ) (ha : 0<a)
    (hε : 0<ε) (hε1 : ε≤1) :
    1≤metricSizeBase k a ε ∧ (k:ℝ)≤metricSizeBase k a ε := by
  have hD : 1≤(23+22*a)^2 := by nlinarith
  have hE : ε^2≤1 := by nlinarith
  have hR : 0≤4*(64*a+8*a^2) := by positivity
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have hC : 1+(k:ℝ)≤1+48*(k:ℝ)+(4*(64*a+8*a^2))*(1+(k:ℝ)) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hD
    (show 0≤1+48*(k:ℝ)+(4*(64*a+8*a^2))*(1+(k:ℝ)) by positivity)
  unfold metricSizeBase
  constructor <;> apply (le_div_iff₀ (sq_pos_of_pos hε)).2 <;> nlinarith

theorem metricSizeGamma_bounds (k : ℕ) (a ε : ℝ) (ha : 0<a)
    (hε : 0<ε) (hε1 : ε≤1) :
    58*metricSizeBase k a ε*(1+Real.log (metricSizeBase k a ε)) ≤ metricSizeGamma k a ε ∧
    Real.log (metricSizeGamma k a ε) ≤ 18*(1+Real.log (metricSizeBase k a ε)) := by
  let H := metricSizeBase k a ε
  have hH : 1≤H := (metricSizeBase_bounds k a ε ha hε hε1).1
  have hHp : 0<H := by linarith
  have hl : 0≤Real.log H := Real.log_nonneg hH
  have hT : 0<1+Real.log H := by positivity
  have hexp := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ)≤16)
  constructor
  · change 58*H*(1+Real.log H) ≤ Real.exp 16*H*(1+Real.log H)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num at hexp ⊢; linarith) hHp.le) hT.le
  · change Real.log (Real.exp 16*H*(1+Real.log H)) ≤ 18*(1+Real.log H)
    rw [Real.log_mul (ne_of_gt (mul_pos (Real.exp_pos _) hHp)) (ne_of_gt hT),
      Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hHp), Real.log_exp]
    have ht := Real.log_le_sub_one_of_pos hT
    linarith

theorem log_logLevel_le (x B : ℝ) (hB : 1≤B) (i : ℕ) :
    Real.log (logLevel x B i) ≤ logLevel x B (i+1) := by
  unfold logLevel
  by_cases h : iteratedLog x (i+1)≤B
  · rw [max_eq_right h]
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans
      (by linarith [le_max_right (iteratedLog x (i+1+1)) B])
  · rw [max_eq_left (le_of_not_ge h)]
    exact le_max_left _ _

/-- A one-stage envelope for the actual prescribed count. -/
theorem metricStageSampleCount_envelope
    (k n : ℕ) (a ε L v : ℝ) (hk : 0<k) (hn : 0<n)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hL : 1≤L) (hv : 1≤v)
    (hlogn : Real.log (n:ℝ) ≤ 18*(1+Real.log (metricSizeBase k a ε))+2*L)
    (hlogv : Real.log v≤3*L) :
    (metricStageSampleCount k n a (ε/Real.sqrt L) (1/(4*v)):ℝ) ≤
      metricSizeGamma k a ε*L^2 := by
  let H := metricSizeBase k a ε
  let T := 1+Real.log H
  let D := 23+22*a
  let R := 4*(64*a+8*a^2)
  have hHb := metricSizeBase_bounds k a ε ha hε hε1
  have hH : 1≤H := hHb.1
  have hT : 1≤T := by dsimp [T]; linarith [Real.log_nonneg hH]
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hnp : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hvp : 0<v := by linarith
  have hLp : 0<L := by linarith
  have hDp : 0<D := by dsimp [D]; linarith
  have hRp : 0≤R := by dsimp [R]; positivity
  have hlogk : Real.log (k:ℝ) ≤ T := by
    have hh := Real.log_le_log hkp hHb.2
    dsimp [T]; linarith
  have heq : 8/(1/(4*v)) = 32*v := by field_simp; ring
  have heqk : 8*(k:ℝ)/(1/(4*v)) = 32*(k:ℝ)*v := by field_simp; ring
  have hlog32 : Real.log (32:ℝ)≤32 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<32)]
  have hb : Real.log (8/(1/(4*v)))≤35*L := by
    rw [heq,Real.log_mul (by norm_num : (32:ℝ)≠0) (ne_of_gt hvp)]
    linarith
  have hbk : Real.log (8*(k:ℝ)/(1/(4*v)))≤36*T*L := by
    rw [heqk,Real.log_mul (ne_of_gt (mul_pos (by norm_num) hkp)) (ne_of_gt hvp),
      Real.log_mul (by norm_num : (32:ℝ)≠0) (ne_of_gt hkp)]
    have hTL : T≤T*L := le_mul_of_one_le_right (by linarith) hL
    have hLT : L≤T*L := le_mul_of_one_le_left hLp.le hT
    nlinarith only [hlog32,hlogv,hlogk,hTL,hLT,hL]
  have hnlog : Real.log (n:ℝ)≤20*T*L := by
    change Real.log (n:ℝ)≤18*T+2*L at hlogn
    have hTL : T≤T*L := le_mul_of_one_le_right (by linarith) hL
    have hLT : L≤T*L := le_mul_of_one_le_left hLp.le hT
    linarith
  let S := (48*(k:ℝ))*Real.log (8*(k:ℝ)/(1/(4*v)))
  let Q := R*(Real.log (8/(1/(4*v)))+(k:ℝ)*Real.log (n:ℝ))
  have hS : 0≤S := by
    dsimp [S]
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    rw [heqk]
    nlinarith [show (1:ℝ)≤k by exact_mod_cast hk]
  have hQ : 0≤Q := by
    dsimp [Q]
    apply mul_nonneg hRp
    apply add_nonneg
    · apply Real.log_nonneg; rw [heq]; linarith
    · exact mul_nonneg hkp.le (Real.log_nonneg (by exact_mod_cast hn))
  have hsum : S+Q≤56*(48*(k:ℝ)+R*(1+(k:ℝ)))*T*L := by
    have hs := mul_le_mul_of_nonneg_left hbk (by positivity : 0≤48*(k:ℝ))
    have hn' := mul_le_mul_of_nonneg_left hnlog hkp.le
    have hLT : L≤T*L := le_mul_of_one_le_left hLp.le hT
    have hq := mul_le_mul_of_nonneg_left (show
        Real.log (8/(1/(4*v)))+(k:ℝ)*Real.log (n:ℝ) ≤
          56*(1+(k:ℝ))*T*L by nlinarith only [hb,hn',hLT, mul_nonneg (by linarith : 0≤T) hLp.le, mul_nonneg hkp.le (mul_nonneg (by linarith : 0≤T) hLp.le)]) hRp
    dsimp [S,Q]
    nlinarith [mul_nonneg (by positivity : 0≤48*(k:ℝ)) (by nlinarith : 0≤20*T*L)]
  have hz : (ε/Real.sqrt L)/D≠0 := ne_of_gt (div_pos (div_pos hε (Real.sqrt_pos.mpr hLp)) hDp)
  have hc := budgetSampleCount_upper S Q ((ε/Real.sqrt L)/D) hS hQ hz
  have hidentity : H*((ε/Real.sqrt L)/D)^2*L = 1+48*(k:ℝ)+R*(1+(k:ℝ)) := by
    dsimp [H,metricSizeBase,D,R]
    field_simp
    nlinarith [Real.sq_sqrt hLp.le]
  have hscale : (S+Q)/((ε/Real.sqrt L)/D)^2 ≤ 56*H*T*L^2 := by
    apply (div_le_iff₀ (sq_pos_of_ne_zero hz)).2
    calc
      S+Q ≤ 56*(48*(k:ℝ)+R*(1+(k:ℝ)))*T*L := hsum
      _ ≤ 56*(1+48*(k:ℝ)+R*(1+(k:ℝ)))*T*L := by
        nlinarith [mul_nonneg (by linarith : 0≤T) hLp.le]
      _ = _ := by rw [←hidentity]; ring
  have hG := (metricSizeGamma_bounds k a ε ha hε hε1).1
  change 58*H*T≤metricSizeGamma k a ε at hG
  have hG' := mul_le_mul_of_nonneg_right hG (sq_nonneg L)
  have hmin : 1≤H*T*L^2 := by
    have hh : 1≤H*T := one_le_mul_of_one_le_of_one_le hH hT
    exact one_le_mul_of_one_le_of_one_le hh (by nlinarith)
  change (budgetSampleCount S Q ((ε/Real.sqrt L)/D):ℝ)≤_
  nlinarith only [hc,hscale,hG',hmin]

end APC

namespace APC

theorem log_metricIterationCount_one (x B : ℝ) (hB : 1≤B) (i : ℕ) :
    Real.log (metricIterationCount 1 x B i : ℝ) ≤ 1+2*Real.log (logLevel x B i) := by
  let U := logLevel x B i
  have hU : 1≤U := hB.trans (logLevel_lower x B i)
  have hUp : 0<U := by linarith
  have hm : (0:ℝ)<metricIterationCount 1 x B i := Nat.cast_pos.mpr
    (metricIterationCount_pos 1 x B (by norm_num) (by linarith) i)
  have hu := metricIterationCount_upper 1 x B (by norm_num) i
  have hb : (metricIterationCount 1 x B i:ℝ) ≤ 2*U^2 := by
    change (metricIterationCount 1 x B i:ℝ)<1*U^2+1 at hu
    nlinarith
  have hl := Real.log_le_log hm hb
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt (sq_pos_of_pos hUp)),Real.log_pow] at hl
  norm_num at hl
  dsimp only [U] at hl
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

theorem scheduledFailure_log_data (N : ℕ) [NeZero N] (i : ℕ) :
    ∃ v : ℝ, 1≤v ∧ MetricIteration.scheduledFailure N i=1/(4*v) ∧
      Real.log v≤3*logLevel (N:ℝ) 14400 i := by
  have hN : (1:ℝ)≤N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  cases i with
  | zero =>
    refine ⟨N,hN,by simp [MetricIteration.scheduledFailure,metricStageFailure],?_⟩
    have hb : Real.log (N:ℝ) ≤ logLevel (N:ℝ) 14400 0 := le_max_left _ _
    linarith [logLevel_lower (N:ℝ) 14400 0]
  | succ i =>
    refine ⟨metricIterationCount 1 (N:ℝ) 14400 i,?_,?_,?_⟩
    · exact_mod_cast metricIterationCount_pos 1 (N:ℝ) 14400 (by norm_num) (by norm_num) i
    · simp [MetricIteration.scheduledFailure,metricStageFailure,metricCountFailure]
    · have hb := log_metricIterationCount_one (N:ℝ) 14400 (by norm_num) i
      have hl := log_logLevel_le (N:ℝ) 14400 (by norm_num) i
      have hm := logLevel_lower (N:ℝ) 14400 (i+1)
      linarith

end APC

namespace APC.MetricIteration

/-- The actual recursive counts have one parameter-only envelope. The
proof uses the checked local count, without replacing the sampling law. -/
theorem recursive_size_envelope (N k : ℕ) [NeZero N] (hk : 0<k)
    (a ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (i : ℕ) :
    (size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N) (i+1):ℝ) ≤
      metricSizeGamma k a ε*(logLevel (N:ℝ) 14400 i)^2 := by
  have hT : 1≤1+Real.log (metricSizeBase k a ε) := by
    linarith [Real.log_nonneg (metricSizeBase_bounds k a ε ha hε hε1).1]
  have hΓ : 0<metricSizeGamma k a ε := by
    have hb := (metricSizeGamma_bounds k a ε ha hε hε1).1
    have hH := (metricSizeBase_bounds k a ε ha hε hε1).1
    nlinarith
  induction i with
  | zero =>
    obtain ⟨v,hv,hδ,hlv⟩ := scheduledFailure_log_data N 0
    have hl : Real.log (N:ℝ)≤18*(1+Real.log (metricSizeBase k a ε))+
        2*logLevel (N:ℝ) 14400 0 := by
      have hh : Real.log (N:ℝ)≤logLevel (N:ℝ) 14400 0 := le_max_left _ _
      linarith [logLevel_lower (N:ℝ) 14400 0]
    simpa only [size,logStageError,hδ] using metricStageSampleCount_envelope k N a ε
      (logLevel (N:ℝ) 14400 0) v hk (Nat.pos_of_ne_zero (NeZero.ne N)) ha hε hε1
      (by linarith [logLevel_lower (N:ℝ) 14400 0]) hv hl hlv
  | succ i ih =>
    obtain ⟨v,hv,hδ,hlv⟩ := scheduledFailure_log_data N (i+1)
    have hpos := size_pos N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N) (i+1)
    have hU : 0<logLevel (N:ℝ) 14400 i := by linarith [logLevel_lower (N:ℝ) 14400 i]
    have hlog := Real.log_le_log (Nat.cast_pos.mpr hpos) ih
    rw [Real.log_mul (ne_of_gt hΓ) (ne_of_gt (sq_pos_of_pos hU)),Real.log_pow] at hlog
    norm_num at hlog
    have hl : Real.log (size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N) (i+1):ℝ) ≤
        18*(1+Real.log (metricSizeBase k a ε))+2*logLevel (N:ℝ) 14400 (i+1) := by
      linarith [(metricSizeGamma_bounds k a ε ha hε hε1).2,
        log_logLevel_le (N:ℝ) 14400 (by norm_num) i]
    simpa only [size,logStageError,hδ] using metricStageSampleCount_envelope k
      (size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N) (i+1)) a ε
      (logLevel (N:ℝ) 14400 (i+1)) v hk hpos ha hε hε1
      (by linarith [logLevel_lower (N:ℝ) 14400 (i+1)]) hv hl hlv

/-- Input-size-independent terminal sample count, for the actual sampler
already used by finite_metric_correctness. -/
theorem terminal_size_bound (N k : ℕ) [NeZero N] (hk : 0<k)
    (a ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) :
    (size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
      (logStop (N:ℝ) 14400):ℝ) ≤ metricSizeGamma k a ε*14400^2 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hb := recursive_size_envelope N k hk a ε ha hε hε1 (logStop (N:ℝ) 14400-1)
  rwa [Nat.sub_add_cancel (logStop_pos (N:ℝ) 14400),
    logLevel_terminal (N:ℝ) 14400 hN (by norm_num)] at hb

end APC.MetricIteration
