import APC.MetricRoundedCompression
import APC.MetricSampling

open scoped BigOperators
noncomputable section
namespace APC

/-- Strong finite-metric coreset: all ambient center tuples are queried,
not merely tuples on the current input support. -/
theorem finite_metric_strong_sampling
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0<w i)
    (proxy : K → X) (a ε δ : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hproxy : Approximate (cost x w) a proxy) :
    let m := metricStageSampleCount (Fintype.card K) (Fintype.card X) a ε δ
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun z=>∃ s : K → X,¬Preserves (cost x w s)
      (cost (sampledPoints x m z) (sampledWeights w p m z) s) ε)≤δ := by
  classical
  have hb := budgetSampleCount_valid
    ((48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(Fintype.card K:ℝ)*Real.log (Fintype.card X)))
    (ε/(23+22*a)) (ne_of_gt (div_pos hε (by linarith)))
  have hcount : Fintype.card (K → X)≤Fintype.card X^Fintype.card K+1 := by
    simp only [Fintype.card_fun];omega
  have hlog := log_solution_count (Fintype.card (K → X)) (Fintype.card X)
    (Fintype.card K) Fintype.card_pos Fintype.card_pos hcount (δ/2) (by positivity)
  have he₁ : 2*(Fintype.card (K → X):ℝ)/(δ/2)=4*(Fintype.card (K → X):ℝ)/δ := by ring
  have he₂ : (4:ℝ)/(δ/2)=8/δ := by ring
  rw [he₁,he₂] at hlog
  have hres := (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤4*(64*a+8*a^2))).trans hb.2.2
  exact finite_family_coreset x w hw proxy (fun s : K → X=>s) a ε δ ha hε hε1 hδ
    Fintype.card_pos (fun s=>hproxy s) _ hb.1 hb.2.1 hres

/-- An exact finite-search proxy removes the approximation-oracle premise.
The theorem is mathematical correctness, without an efficient runtime claim. -/
theorem finite_metric_strong_coreset
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0<w i)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) :
    let proxy := MetricIteration.optimalProxy (K:=K) (MetricIteration.Cloud.mk x w)
    let m := metricStageSampleCount (Fintype.card K) (Fintype.card X) 1 ε δ
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun z=>∃ s : K → X,¬Preserves (cost x w s)
      (cost (sampledPoints x m z) (sampledWeights w p m z) s) ε)≤δ :=
  finite_metric_strong_sampling x w hw _ 1 ε δ (by norm_num) hε hε1 hδ
    (MetricIteration.optimalProxy_spec (K:=K) (MetricIteration.Cloud.mk x w))

/-- An explicit sample bound for the exact-proxy finite-metric theorem.
The logarithmic factor includes k explicitly; no asymptotic convention is used. -/
theorem finite_metric_strong_count_bound (k n : ℕ) (ε δ : ℝ)
    (hk : 0<k) (hn : 0<n) (hε : 0<ε) (hδ : 0<δ) (hδ1 : δ≤1) :
    (metricStageSampleCount k n 1 ε δ:ℝ)<
      680400*(k:ℝ)*(Real.log (8*(k:ℝ)/δ)+Real.log (n:ℝ))/ε^2+2 := by
  let S := (48*(k:ℝ))*Real.log (8*(k:ℝ)/δ)
  let R := (4*(64*(1:ℝ)+8*1^2))*(Real.log (8/δ)+(k:ℝ)*Real.log (n:ℝ))
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hlog : 0≤Real.log (8*(k:ℝ)/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by nlinarith))
  have hnlog : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog8 : 0≤Real.log (8/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hcomp : Real.log (8/δ)≤Real.log (8*(k:ℝ)/δ) := Real.log_le_log (by positivity)
    (div_le_div_of_nonneg_right (by nlinarith) hδ.le)
  have hklog := mul_le_mul_of_nonneg_right hkr hlog
  have hs : 0≤S := by dsimp [S];positivity
  have hr : 0≤R := by dsimp [R];positivity
  have hsum : S+R≤336*(k:ℝ)*(Real.log (8*(k:ℝ)/δ)+Real.log (n:ℝ)) := by
    dsimp [S,R]
    nlinarith only [hcomp,hklog,mul_nonneg (by positivity : (0:ℝ)≤k) hnlog]
  have hb := budgetSampleCount_upper S R (ε/(23+22*(1:ℝ))) hs hr (by positivity)
  have hh := div_le_div_of_nonneg_right hsum (sq_nonneg (ε/(23+22*(1:ℝ))))
  have hid : (336*(k:ℝ)*(Real.log (8*(k:ℝ)/δ)+Real.log (n:ℝ)))/(ε/(23+22*(1:ℝ)))^2=
      680400*(k:ℝ)*(Real.log (8*(k:ℝ)/δ)+Real.log (n:ℝ))/ε^2 := by ring
  rw [hid] at hh
  exact hb.trans_le (add_le_add_right hh 2)

/-- When k≤n, the extra log k is absorbed into the ambient-size term.
This is the exact-constant form of the finite-metric strong bound. -/
theorem finite_metric_strong_count_bound_le_ambient (k n : ℕ) (ε δ : ℝ)
    (hk : 0<k) (hkn : k≤n) (hε : 0<ε) (hδ : 0<δ) (hδ1 : δ≤1) :
    (metricStageSampleCount k n 1 ε δ:ℝ)<
      1360800*(k:ℝ)*(Real.log (8/δ)+Real.log (n:ℝ))/ε^2+2 := by
  have hn : 0<n := hk.trans_le hkn
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hlog := Real.log_le_log hkp (Nat.cast_le.mpr hkn)
  have hlog8 : 0≤Real.log (8/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have he : Real.log (8*(k:ℝ)/δ)=Real.log (8/δ)+Real.log (k:ℝ) := by
    rw [show 8*(k:ℝ)/δ=(8/δ)*(k:ℝ) by ring,
      Real.log_mul (ne_of_gt (by positivity : (0:ℝ)<8/δ)) (ne_of_gt hkp)]
  have hsum : Real.log (8*(k:ℝ)/δ)+Real.log (n:ℝ)≤
      2*(Real.log (8/δ)+Real.log (n:ℝ)) := by rw [he];linarith
  have hs := mul_le_mul_of_nonneg_left hsum (show 0≤680400*(k:ℝ) by positivity)
  have hd := div_le_div_of_nonneg_right hs (sq_nonneg ε)
  have hb := finite_metric_strong_count_bound k n ε δ hk hn hε hδ hδ1
  exact hb.trans_le (add_le_add_right (by convert hd using 1 <;> ring) 2)

end APC
