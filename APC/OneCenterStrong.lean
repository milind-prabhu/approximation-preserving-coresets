import APC.OneCenterSampling

open scoped BigOperators
noncomputable section
namespace APC
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def oneCenterMomentEnergy (x : I → E) (w : I → ℝ) (m : ℕ) (z : Draws I m) : ℝ :=
  let p := oneCenterProbability x w
  let y := sampledPoints x m z
  let v := sampledWeights w p m z
  (mass v-mass w)^2/(mass w)^2+
    (oneCost y v (mean x w)-oneCost x w (mean x w))^2/(oneCost x w (mean x w))^2+
    ‖∑ j,v j • (y j-mean x w)‖^2/(mass w*oneCost x w (mean x w))

theorem oneCenterMomentEnergy_nonneg (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (m : ℕ) (z : Draws I m) : 0≤oneCenterMomentEnergy x w m z := by
  unfold oneCenterMomentEnergy
  apply add_nonneg
  · exact add_nonneg (by positivity) (by positivity)
  · exact div_nonneg (sq_nonneg _) (mul_nonneg
      (Finset.sum_nonneg (fun i _=>hw i)) (oneCost_nonneg x w hw _))

/-- Expected normalized error is O(1/m), independently of dimension. -/
theorem oneCenterMomentEnergy_expectation [Nonempty I]
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0<w i)
    (hM : 0<mass w) (hV : 0<oneCost x w (mean x w)) (m : ℕ) (hm : 0<m) :
    (∑ z,drawWeight (oneCenterProbability x w) m z*oneCenterMomentEnergy x w m z)≤12/(m:ℝ) := by
  let p := oneCenterProbability x w
  let M := mass w
  let V := oneCost x w (mean x w)
  have hp := oneCenterProbability_pos x w hw
  have h1 := oneCenterProbability_sum x w hw
  have hA := importance_estimator_mse_bound p w hp h1 (fun i=>(hw i).le) (4*M)
    (fun i=>(oneCenterProbability_bounds x w hw i).1) m hm
  have hB := importance_estimator_mse_bound p (fun i=>w i*‖x i-mean x w‖^2) hp h1
    (fun i=>mul_nonneg (hw i).le (sq_nonneg _)) (4*V)
    (fun i=>(oneCenterProbability_bounds x w hw i).2) m hm
  have hZ := oneCenter_vector_mse x w hw hM m hm
  change (∑ z,drawWeight p m z*(importanceEstimate p w m z-M)^2)≤4*M*M/(m:ℝ) at hA
  change (∑ z,drawWeight p m z*(importanceEstimate p (fun i=>w i*‖x i-mean x w‖^2) m z-V)^2)≤4*V*V/(m:ℝ) at hB
  have hA' := div_le_div_of_nonneg_right hA (sq_nonneg M)
  have hB' := div_le_div_of_nonneg_right hB (sq_nonneg V)
  have hZ' := div_le_div_of_nonneg_right hZ (mul_nonneg hM.le hV.le)
  have hMA : (4*M*M/(m:ℝ))/M^2=4/(m:ℝ) := by dsimp [M];field_simp [ne_of_gt hM] <;> ring
  have hVB : (4*V*V/(m:ℝ))/V^2=4/(m:ℝ) := by dsimp [V];field_simp [ne_of_gt hV] <;> ring
  have hVZ : (4*mass w*oneCost x w (mean x w)/(m:ℝ))/(mass w*oneCost x w (mean x w))=4/(m:ℝ) := by
    field_simp [ne_of_gt hM,ne_of_gt hV] <;> ring
  rw [hMA] at hA'
  rw [hVB] at hB'
  rw [hVZ] at hZ'
  unfold oneCenterMomentEnergy
  simp_rw [sampled_mass_estimator,sampled_oneCost_estimator,sampled_centered_vector,
    mul_add,←mul_div_assoc,Finset.sum_add_distrib,←Finset.sum_div]
  change _≤_
  convert add_le_add (add_le_add hA' hB') hZ' using 1 <;> ring

/-- A small joint moment error implies uniform strong preservation. -/
theorem oneCenterMomentEnergy_preserves
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (hM : 0<mass w) (hV : 0<oneCost x w (mean x w))
    (m : ℕ) (z : Draws I m) (η : ℝ) (hη : 0≤η)
    (henergy : oneCenterMomentEnergy x w m z≤η^2) :
    ∀ c,Preserves (oneCost x w c)
      (oneCost (sampledPoints x m z) (sampledWeights w (oneCenterProbability x w) m z) c) (2*η) := by
  let y := sampledPoints x m z
  let v := sampledWeights w (oneCenterProbability x w) m z
  let M := mass w
  let V := oneCost x w (mean x w)
  let A := mass v-M
  let B := oneCost y v (mean x w)-V
  let Z := ∑ j,v j • (y j-mean x w)
  change A^2/M^2+B^2/V^2+‖Z‖^2/(M*V)≤η^2 at henergy
  have hA0 : 0≤A^2/M^2 := by positivity
  have hB0 : 0≤B^2/V^2 := by positivity
  have hZ0 : 0≤‖Z‖^2/(M*V) := div_nonneg (sq_nonneg _) (mul_nonneg hM.le hV.le)
  have hA : A^2≤η^2*M^2 := (div_le_iff₀ (sq_pos_of_pos hM)).mp (by linarith)
  have hB : B^2≤η^2*V^2 := (div_le_iff₀ (sq_pos_of_pos hV)).mp (by linarith)
  have hZ : ‖Z‖^2≤η^2*M*V := by
    have hh := (div_le_iff₀ (mul_pos hM hV)).mp (show ‖Z‖^2/(M*V)≤η^2 by linarith)
    nlinarith only [hh]
  apply oneCenter_strong_of_moments x w hw hM y v η hη
  · change |A|≤η*M
    nlinarith [sq_abs A,abs_nonneg A,mul_nonneg hη hM.le]
  · change |B|≤η*V
    nlinarith [sq_abs B,abs_nonneg B,mul_nonneg hη hV.le]
  · exact hZ

/-- Uniform concentration over the entire (possibly infinite-dimensional)
space of one-center queries. No finite query net is assumed. -/
theorem oneCenter_strong_failure_positive_variance [Nonempty I]
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0<w i)
    (hM : 0<mass w) (hV : 0<oneCost x w (mean x w))
    (m : ℕ) (hm : 0<m) (η : ℝ) (hη : 0<η) (hbudget : 36≤(m:ℝ)*η^2) :
    eventMass (drawWeight (oneCenterProbability x w) m) (fun z=>∃ c,
      ¬Preserves (oneCost x w c)
        (oneCost (sampledPoints x m z) (sampledWeights w (oneCenterProbability x w) m z) c) (2*η))≤1/3 := by
  have hp := drawWeight_nonneg _ (fun i=>(oneCenterProbability_pos x w hw i).le) m
  have hb := finite_markov (drawWeight (oneCenterProbability x w) m)
    (oneCenterMomentEnergy x w m) hp (oneCenterMomentEnergy_nonneg x w (fun i=>(hw i).le) m) (η^2)
  have he := oneCenterMomentEnergy_expectation x w hw hM hV m hm
  have hmass := eventMass_nonneg _ hp (fun z=>η^2<oneCenterMomentEnergy x w m z)
  have hscaled := mul_le_mul_of_nonneg_left (hb.trans he) (Nat.cast_nonneg m : (0:ℝ)≤m)
  have hid : (m:ℝ)*(12/(m:ℝ))=12 := by field_simp
  rw [hid] at hscaled
  have hbudget' := mul_le_mul_of_nonneg_right hbudget hmass
  have hprob : eventMass (drawWeight (oneCenterProbability x w) m)
      (fun z=>η^2<oneCenterMomentEnergy x w m z)≤1/3 := by nlinarith only [hscaled,hbudget']
  apply le_trans (eventMass_mono _ hp _ _ ?_) hprob
  rintro z ⟨c,hc⟩
  by_contra hn
  exact hc (oneCenterMomentEnergy_preserves x w (fun i=>(hw i).le) hM hV m z η hη.le (le_of_not_gt hn) c)

end APC
