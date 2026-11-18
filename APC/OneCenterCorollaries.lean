import APC.OneCenterConstruction

open scoped BigOperators
noncomputable section
namespace APC
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_cost_eq_oneCost (x : I → E) (w : I → ℝ) (s : Unit → E) :
    cost x w s=oneCost x w (s ()) := by
  unfold cost pointCost oneCost
  have h : ∀ j : Unit,j=() := fun j=>Subsingleton.elim _ _
  simp only [h,dist_eq_norm]

/-- The one-center construction in the center-tuple interface used by
the two-stage Euclidean compression theorems. -/
theorem oneCenter_strong_coreset_tuples [Nonempty I]
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0<w i) (ε : ℝ) (hε : 0<ε) :
    let m := oneCenterStrongSampleCount ε
    eventMass (drawWeight (oneCenterProbability x w) m) (fun z=>∃ s : Unit → E,
      ¬Preserves (cost x w s)
        (cost (sampledPoints x m z) (sampledWeights w (oneCenterProbability x w) m z) s) ε)≤1/3 := by
  have hb := oneCenter_strong_coreset x w hw ε hε
  apply le_trans (eventMass_mono _
    (drawWeight_nonneg _ (fun i=>(oneCenterProbability_pos x w hw i).le) _) _ _ ?_) hb
  rintro z ⟨s,hs⟩
  exact ⟨s (),by simpa only [unit_cost_eq_oneCost] using hs⟩

/-- Existence of a positively weighted supported coreset, with all-center
preservation and an explicit dimension-free cardinality bound. -/
theorem exists_oneCenter_strong_coreset [Nonempty I]
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0<w i) (ε : ℝ) (hε : 0<ε) :
    let m := oneCenterStrongSampleCount ε
    (m:ℝ)<144/ε^2+2 ∧ ∃ (f : Fin m → I) (v : Fin m → ℝ),
      (∀ j,0<v j) ∧ ∀ c,Preserves (oneCost x w c) (oneCost (fun j=>x (f j)) v c) ε := by
  classical
  dsimp only
  refine ⟨oneCenterStrongSampleCount_upper ε hε,?_⟩
  let m := oneCenterStrongSampleCount ε
  let p := oneCenterProbability x w
  have hp := oneCenterProbability_pos x w hw
  have hm := oneCenterStrongSampleCount_valid ε hε
  have hex : ∃ z : Draws I m,∀ c,Preserves (oneCost x w c)
      (oneCost (sampledPoints x m z) (sampledWeights w p m z) c) ε := by
    by_contra hn
    push_neg at hn
    have hb := oneCenter_strong_coreset x w hw ε hε
    have he : eventMass (drawWeight p m) (fun z=>∃ c,
      ¬Preserves (oneCost x w c) (oneCost (sampledPoints x m z) (sampledWeights w p m z) c) ε)=1 := by
      unfold eventMass
      simp only [if_pos (hn _)]
      exact drawWeight_sum p (oneCenterProbability_sum x w hw) m
    change eventMass (drawWeight p m) _≤1/3 at hb
    linarith
  obtain ⟨z,hz⟩ := hex
  refine ⟨drawIndex m z,sampledWeights w p m z,?_,hz⟩
  intro j
  exact div_pos (hw _) (mul_pos (Nat.cast_pos.mpr hm.1) (hp _))

end APC
