import APC.SubsetSearch
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators
noncomputable section
namespace APC

/-- The verified structural budget always leaves at least k draw slots.
This permits exact-size subset search, including when k exceeds input size. -/
theorem metricStageSampleCount_ge_centers (k B : ℕ) (a ε δ : ℝ)
    (hk : 0<k) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ≤1) :
    k≤metricStageSampleCount k B a ε δ := by
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hx : (2:ℝ)≤8*(k:ℝ)/δ := (le_div_iff₀ hδ).2 (by nlinarith)
  have hxp : 0<8*(k:ℝ)/δ := by positivity
  have hi : (8*(k:ℝ)/δ)⁻¹≤(1:ℝ)/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hx
  have hlog : (1:ℝ)/2≤Real.log (8*(k:ℝ)/δ) := by
    linarith [Real.one_sub_inv_le_log_of_pos hxp]
  have hD : 1≤23+22*a := by linarith
  have hz : 0≤ε/(23+22*a) := by positivity
  have hz1 : ε/(23+22*a)≤1 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hz2 : (ε/(23+22*a))^2≤1 := by nlinarith
  have hb := budgetSampleCount_valid
    ((48*(k:ℝ))*Real.log (8*(k:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(k:ℝ)*Real.log B))
    (ε/(23+22*a)) (by positivity)
  have hs := mul_le_mul_of_nonneg_left hlog (by positivity : 0≤48*(k:ℝ))
  have hm := mul_le_mul_of_nonneg_left hz2
    (Nat.cast_nonneg (metricStageSampleCount k B a ε δ) : (0:ℝ)≤metricStageSampleCount k B a ε δ)
  have hfinal : (k:ℝ)≤metricStageSampleCount k B a ε δ := by
    have hbs := hb.2.1
    change _≤(metricStageSampleCount k B a ε δ:ℝ)*(ε/(23+22*a))^2 at hbs
    nlinarith only [hbs,hs,hm,hkr]
  exact_mod_cast hfinal

/-- An elementary exponential-series argument removes the factorial from
the binomial bound; no Stirling asymptotic is assumed. -/
theorem choose_le_exp_ratio_pow (m k : ℕ) (hk : 0<k) :
    (m.choose k:ℝ)≤(Real.exp 1*(m:ℝ)/(k:ℝ))^k := by
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hfact : (0:ℝ)<k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hf := Real.pow_div_factorial_le_exp (k:ℝ) (Nat.cast_nonneg k) k
  have hf' := (div_le_iff₀ hfact).mp hf
  have hmul := mul_le_mul_of_nonneg_left hf' (show 0≤(m:ℝ)^k/(k:ℝ)^k by positivity)
  have he : Real.exp (k:ℝ)=(Real.exp 1)^k := by simpa only [mul_one] using Real.exp_nat_mul 1 k
  calc
    (m.choose k:ℝ)≤(m:ℝ)^k/(k.factorial:ℝ) := Nat.choose_le_pow_div k m
    _≤_ := by
      apply (div_le_iff₀ hfact).2
      calc
        (m:ℝ)^k=((m:ℝ)^k/(k:ℝ)^k)*(k:ℝ)^k := by field_simp
        _≤_ := hmul
        _=(Real.exp 1*(m:ℝ)/(k:ℝ))^k*(k.factorial:ℝ) := by
          rw [he,div_pow,mul_pow]
          ring

end APC
namespace APC.MetricIteration

theorem scheduledFailure_le_one (N : ℕ) [NeZero N] (i : ℕ) : scheduledFailure N i≤1 := by
  have hN : (1:ℝ)≤N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold scheduledFailure metricStageFailure metricCountFailure
  split_ifs
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<4*N)).2
    linarith
  · have hc : (1:ℝ)≤metricIterationCount 1 (N:ℝ) 14400 (i-1) := by
      exact_mod_cast metricIterationCount_pos 1 (N:ℝ) 14400 (by norm_num) (by norm_num) (i-1)
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(metricIterationCount 1 (N:ℝ) 14400 (i-1):ℝ))).2
    linarith

theorem terminal_size_ge_centers (N k : ℕ) [NeZero N] (hk : 0<k)
    (a ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) :
    k≤size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N) (logStop (N:ℝ) 14400) := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (logStop_pos (N:ℝ) 14400))
  rw [hn,size]
  exact metricStageSampleCount_ge_centers _ _ _ _ _ hk ha
    (scheduledError_pos N ε hε n) (scheduledError_le_one N ε hε1 n)
    (scheduledFailure_pos N n) (scheduledFailure_le_one N n)

/-- Exact binomial bound for the same terminal draw count used by the
adaptive sampler, now with the factorial cancellation made explicit. -/
theorem terminal_binomial_count_bound (N k : ℕ) [NeZero N] (hk : 0<k)
    (a ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) :
    ((size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
      (logStop (N:ℝ) 14400)).choose k:ℝ)≤
      (Real.exp 1*metricSizeGamma k a ε*14400^2/(k:ℝ))^k := by
  have hs := terminal_size_bound N k hk a ε ha hε hε1
  refine (choose_le_exp_ratio_pow _ k hk).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le) (Nat.cast_nonneg k)
  convert hh using 1 <;> ring

/-- A parameter-only FPT candidate bound: the linear k factor in summary
size cancels against the factorial in subset enumeration. -/
theorem terminal_binomial_parameter_bound (N k : ℕ) [NeZero N] (hk : 0<k)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ((size N k 1 (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
      (logStop (N:ℝ) 14400)).choose k:ℝ)≤
      (Real.exp 17*1265625*14400^2*(1+Real.log (metricSizeBase k 1 ε))/ε^2)^k := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hkp : (0:ℝ)<k := by linarith
  have hT : 0≤1+Real.log (metricSizeBase k 1 ε) := by
    linarith [Real.log_nonneg (metricSizeBase_bounds k 1 ε (by norm_num) hε hε1).1]
  have hH : metricSizeBase k 1 ε/(k:ℝ)≤1265625/ε^2 := by
    apply (div_le_div_iff₀ hkp (sq_pos_of_pos hε)).2
    rw [metricSizeBase_one]
    have hid : (2025*(289+336*(k:ℝ))/ε^2)*ε^2=2025*(289+336*(k:ℝ)) := by field_simp
    rw [hid]
    nlinarith only [hkR]
  have hHpos := (metricSizeBase_bounds k 1 ε (by norm_num) hε hε1).1
  have hΓ : 0≤metricSizeGamma k 1 ε := by unfold metricSizeGamma;positivity
  have hb := terminal_binomial_count_bound N k hk 1 ε (by norm_num) hε hε1
  refine hb.trans (pow_le_pow_left₀ (by positivity) ?_ k)
  have hh := mul_le_mul_of_nonneg_left hH
    (show 0≤Real.exp 17*14400^2*(1+Real.log (metricSizeBase k 1 ε)) by positivity)
  have he : Real.exp (17:ℝ)=Real.exp 1*Real.exp 16 := by rw [←Real.exp_add];norm_num
  dsimp only [metricSizeGamma]
  rw [he] at hh ⊢
  convert hh using 1 <;> ring

end APC.MetricIteration
