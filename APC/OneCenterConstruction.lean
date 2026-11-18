import APC.OneCenterStrong
import Mathlib.Data.Real.Archimedean

open scoped BigOperators
noncomputable section
namespace APC
variable {I E : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem oneCenter_mass_pos (w : I → ℝ) (hw : ∀ i,0<w i) : 0<mass w := by
  classical
  let i := Classical.arbitrary I
  exact (hw i).trans_le (Finset.single_le_sum (fun j _=>(hw j).le) (Finset.mem_univ i))

theorem oneCenter_zero_variance_points (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) (hV : oneCost x w (mean x w)=0) : ∀ i,x i=mean x w := by
  intro i
  have hh : w i*‖x i-mean x w‖^2≤oneCost x w (mean x w) :=
    Finset.single_le_sum (f:=fun j=>w j*‖x j-mean x w‖^2)
      (fun j _=>mul_nonneg (hw j).le (sq_nonneg _)) (Finset.mem_univ i)
  rw [hV] at hh
  have hs : ‖x i-mean x w‖^2≤0 := (mul_le_mul_left (hw i)).mp (by simpa using hh)
  have hz : ‖x i-mean x w‖=0 := by nlinarith [norm_nonneg (x i-mean x w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem oneCenterProbability_zero_variance (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) (hV : oneCost x w (mean x w)=0) :
    ∀ i,oneCenterProbability x w i=w i/mass w := by
  have hx := oneCenter_zero_variance_points x w hw hV
  have hM : (∑ i,w i)≠0 := ne_of_gt (oneCenter_mass_pos w hw)
  intro i
  simp [oneCenterProbability,sensitivityProbability,clusterLaw,localCostLaw,globalCostLaw,
    deltaLaw,activeMass,groupMass,fiberWeight,hx,hM,mass]
  ring

/-- The zero-variance branch is exact on every draw, not merely with high
probability, and still uses the same sensitivity distribution. -/
theorem oneCenter_zero_variance_exact (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) (hV : oneCost x w (mean x w)=0)
    (m : ℕ) (hm : 0<m) (z : Draws I m) (c : E) :
    oneCost (sampledPoints x m z) (sampledWeights w (oneCenterProbability x w) m z) c=oneCost x w c := by
  have hx := oneCenter_zero_variance_points x w hw hV
  have hp := oneCenterProbability_zero_variance x w hw hV
  have hM := oneCenter_mass_pos w hw
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hv : ∀ j,sampledWeights w (oneCenterProbability x w) m z j=mass w/(m:ℝ) := by
    intro j
    unfold sampledWeights
    rw [hp]
    field_simp [ne_of_gt hM,ne_of_gt (hw (drawIndex m z j))]
  have hy : ∀ j,sampledPoints x m z j=mean x w := fun j=>hx _
  calc
    _=(m:ℝ)*(mass w/(m:ℝ)*‖mean x w-c‖^2) := by simp [oneCost,hv,hy]
    _=mass w*‖mean x w-c‖^2 := by field_simp
    _=oneCost x w c := by rw [variance_identity x w (ne_of_gt hM) c,hV,zero_add]

def oneCenterStrongSampleCount (ε : ℝ) : ℕ := Nat.ceil (144/ε^2)+1

theorem oneCenterStrongSampleCount_valid (ε : ℝ) (hε : 0<ε) :
    0<oneCenterStrongSampleCount ε ∧
      36≤(oneCenterStrongSampleCount ε:ℝ)*(ε/2)^2 := by
  have hc := Nat.le_ceil (144/ε^2)
  have hb : (Nat.ceil (144/ε^2):ℝ)≤oneCenterStrongSampleCount ε := by simp [oneCenterStrongSampleCount]
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp (hc.trans hb)
  exact ⟨Nat.zero_lt_succ _,by nlinarith only [hh]⟩

theorem oneCenterStrongSampleCount_upper (ε : ℝ) (hε : 0<ε) :
    (oneCenterStrongSampleCount ε:ℝ)<144/ε^2+2 := by
  have hh := Nat.ceil_lt_add_one (by positivity : 0≤(144:ℝ)/ε^2)
  simpa only [oneCenterStrongSampleCount,Nat.cast_add,Nat.cast_one] using (by linarith : (Nat.ceil (144/ε^2):ℝ)+1<144/ε^2+2)

/-- An unconditional dimension- and input-size-independent strong coreset
construction for k=1. The actual sensitivity sampler and importance weights
preserve the cost of every center simultaneously with probability ≥2/3.
This is a special case, not the cited general-k strong-coreset primitive. -/
theorem oneCenter_strong_coreset (x : I → E) (w : I → ℝ)
    (hw : ∀ i,0<w i) (ε : ℝ) (hε : 0<ε) :
    let m := oneCenterStrongSampleCount ε
    eventMass (drawWeight (oneCenterProbability x w) m) (fun z=>∃ c,
      ¬Preserves (oneCost x w c)
        (oneCost (sampledPoints x m z) (sampledWeights w (oneCenterProbability x w) m z) c) ε)≤1/3 := by
  classical
  dsimp only
  have hm := oneCenterStrongSampleCount_valid ε hε
  have hM := oneCenter_mass_pos w hw
  by_cases hV : oneCost x w (mean x w)=0
  · have hz : eventMass (drawWeight (oneCenterProbability x w) (oneCenterStrongSampleCount ε))
        (fun z=>∃ c,¬Preserves (oneCost x w c)
          (oneCost (sampledPoints x (oneCenterStrongSampleCount ε) z)
            (sampledWeights w (oneCenterProbability x w) (oneCenterStrongSampleCount ε) z) c) ε)=0 := by
      unfold eventMass
      apply Finset.sum_eq_zero
      intro z _
      rw [if_neg]
      rintro ⟨c,hc⟩
      rw [oneCenter_zero_variance_exact x w hw hV _ hm.1 z c] at hc
      have hn := oneCost_nonneg x w (fun i=>(hw i).le) c
      apply hc
      constructor <;> nlinarith [mul_nonneg hε.le hn]
    rw [hz]
    norm_num
  · have hVp : 0<oneCost x w (mean x w) := lt_of_le_of_ne
      (oneCost_nonneg x w (fun i=>(hw i).le) _) (Ne.symm hV)
    simpa only [show 2*(ε/2)=ε by ring] using
      oneCenter_strong_failure_positive_variance x w hw hM hVp (oneCenterStrongSampleCount ε)
        hm.1 (ε/2) (by positivity) hm.2

end APC
