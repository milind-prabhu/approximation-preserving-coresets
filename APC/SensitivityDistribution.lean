import APC.Partition

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

variable {I K : Type*} [Fintype I] [Nonempty I] [Fintype K]

def activeMass (w : I → ℝ) (a : I → K) : ℝ := by
  classical
  exact ∑ j,if groupMass w a j=0 then 0 else 1

theorem activeMass_pos (w : I → ℝ) (a : I → K) (hw : ∀ i,0<w i) : 0<activeMass w a := by
  classical
  let i := Classical.arbitrary I
  have hj : groupMass w a (a i)≠0 := ne_of_gt ((hw i).trans_le (own_le_groupMass w a (fun i=>(hw i).le) i))
  have hh : (if groupMass w a (a i)=0 then (0:ℝ) else 1)≤activeMass w a :=
    Finset.single_le_sum (f:=fun j=>if groupMass w a j=0 then (0:ℝ) else 1)
      (fun j _=>by dsimp; split_ifs <;> norm_num) (Finset.mem_univ (a i))
  simpa [hj] using (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (by simpa [hj] using hh))

theorem activeMass_le_card (w : I → ℝ) (a : I → K) : activeMass w a≤Fintype.card K := by
  classical
  calc
    _≤∑ _j : K,(1:ℝ) := Finset.sum_le_sum (fun j _=>by split_ifs <;> norm_num)
    _=_ := by simp

def clusterLaw (w : I → ℝ) (a : I → K) (i : I) : ℝ :=
  (w i/groupMass w a (a i))/activeMass w a

def localCostLaw (w c : I → ℝ) (a : I → K) (i : I) : ℝ := by
  classical
  exact (if groupMass (fun i=>w i*c i) a (a i)=0 then w i/groupMass w a (a i)
    else w i*c i/groupMass (fun i=>w i*c i) a (a i))/activeMass w a

def globalCostLaw (w c : I → ℝ) (a : I → K) (i : I) : ℝ := by
  classical
  exact if (∑ l,w l*c l)=0 then clusterLaw w a i else w i*c i/(∑ l,w l*c l)

def clusterDelta (w c : I → ℝ) (a : I → K) (i : I) : ℝ :=
  groupMass (fun l=>w l*c l) a (a i)/groupMass w a (a i)

def deltaLaw (w c : I → ℝ) (a : I → K) (i : I) : ℝ := by
  classical
  exact if (∑ l,w l*c l)=0 then clusterLaw w a i else w i*clusterDelta w c a i/(∑ l,w l*c l)

/-- Four-component sensitivity sampler. Empty proxy clusters are ignored
by activeMass. A zero-cost component falls back to clusterLaw. -/
def sensitivityProbability (w c : I → ℝ) (a : I → K) (i : I) : ℝ :=
  (clusterLaw w a i+localCostLaw w c a i+globalCostLaw w c a i+deltaLaw w c a i)/4

theorem clusterLaw_sum (w : I → ℝ) (a : I → K) (hw : ∀ i,0<w i) :
    ∑ i,clusterLaw w a i=1 := by
  classical
  simp only [clusterLaw,← Finset.sum_div]
  rw [group_div_sum]
  have he : (∑ j,groupMass w a j/groupMass w a j)=activeMass w a := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : groupMass w a j=0 <;> simp [hz]
  rw [he,div_self (ne_of_gt (activeMass_pos w a hw))]

theorem localCostLaw_sum (w c : I → ℝ) (a : I → K) (hw : ∀ i,0<w i) :
    ∑ i,localCostLaw w c a i=1 := by
  classical
  have he : ∀ j, (∑ i,if a i=j then
      (if groupMass (fun i=>w i*c i) a j=0 then w i/groupMass w a j
        else w i*c i/groupMass (fun i=>w i*c i) a j) else 0)=
      groupMass w a j/groupMass w a j := by
    intro j
    by_cases hz : groupMass (fun i=>w i*c i) a j=0
    · simp only [if_pos hz]
      simp [groupMass,fiberWeight,Finset.sum_div,ite_div]
    · have hW : groupMass w a j≠0 := by
        intro hW
        exact hz (groupMass_mul_zero w c a (fun i=>(hw i).le) j hW)
      have hc : (∑ i,if a i=j then w i*c i/groupMass (fun i=>w i*c i) a j else 0)=
          groupMass (fun i=>w i*c i) a j/groupMass (fun i=>w i*c i) a j := by
        simp [groupMass,fiberWeight,Finset.sum_div,ite_div]
      simp only [if_neg hz]
      rw [hc,div_self hz,div_self hW]
  simp only [localCostLaw,← Finset.sum_div]
  have hg := group_sum a (fun j i=>if groupMass (fun i=>w i*c i) a j=0
    then w i/groupMass w a j else w i*c i/groupMass (fun i=>w i*c i) a j)
  rw [← hg]
  simp_rw [he]
  have hh : (∑ j,groupMass w a j/groupMass w a j)=activeMass w a := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : groupMass w a j=0 <;> simp [hz]
  rw [hh,div_self (ne_of_gt (activeMass_pos w a hw))]

theorem clusterDelta_total (w c : I → ℝ) (a : I → K) (hw : ∀ i,0≤w i) :
    (∑ i,w i*clusterDelta w c a i)=∑ i,w i*c i := by
  unfold clusterDelta
  rw [group_mul_sum w a (fun j=>groupMass (fun i=>w i*c i) a j/groupMass w a j)]
  calc
    _=∑ j,groupMass (fun i=>w i*c i) a j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : groupMass w a j=0
      · rw [hz,zero_mul,groupMass_mul_zero w c a hw j hz]
      · field_simp
    _=_ := groupMass_total (fun i=>w i*c i) a

theorem globalCostLaw_sum (w c : I → ℝ) (a : I → K) (hw : ∀ i,0<w i) :
    ∑ i,globalCostLaw w c a i=1 := by
  classical
  by_cases hz : (∑ i,w i*c i)=0
  · simpa [globalCostLaw,hz] using clusterLaw_sum w a hw
  · simp [globalCostLaw,hz,← Finset.sum_div]

theorem deltaLaw_sum (w c : I → ℝ) (a : I → K) (hw : ∀ i,0<w i) :
    ∑ i,deltaLaw w c a i=1 := by
  classical
  by_cases hz : (∑ i,w i*c i)=0
  · simpa [deltaLaw,hz] using clusterLaw_sum w a hw
  · simp only [deltaLaw,if_neg hz,← Finset.sum_div]
    rw [clusterDelta_total w c a (fun i=>(hw i).le),div_self hz]

theorem sensitivityProbability_sum (w c : I → ℝ) (a : I → K) (hw : ∀ i,0<w i) :
    ∑ i,sensitivityProbability w c a i=1 := by
  simp only [sensitivityProbability,← Finset.sum_div,Finset.sum_add_distrib]
  rw [clusterLaw_sum w a hw,localCostLaw_sum w c a hw,globalCostLaw_sum w c a hw,deltaLaw_sum w c a hw]
  norm_num

theorem sampling_components_nonneg (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) :
    0<clusterLaw w a i ∧ 0≤localCostLaw w c a i ∧
      0≤globalCostLaw w c a i ∧ 0≤deltaLaw w c a i := by
  have hW : 0<groupMass w a (a i) := (hw i).trans_le (own_le_groupMass w a (fun i=>(hw i).le) i)
  have hR := activeMass_pos w a hw
  have hA : 0≤∑ i,w i*c i := Finset.sum_nonneg (fun i _=>mul_nonneg (hw i).le (hc i))
  have hlocal : 0≤groupMass (fun i=>w i*c i) a (a i) :=
    groupMass_nonneg _ a (fun i=>mul_nonneg (hw i).le (hc i)) _
  have hcl : 0<clusterLaw w a i := div_pos (div_pos (hw i) hW) hR
  refine ⟨hcl,?_,?_,?_⟩
  · unfold localCostLaw
    split_ifs <;> apply div_nonneg ?_ hR.le
    · exact div_nonneg (hw i).le hW.le
    · exact div_nonneg (mul_nonneg (hw i).le (hc i)) hlocal
  · unfold globalCostLaw
    split_ifs
    · exact hcl.le
    · exact div_nonneg (mul_nonneg (hw i).le (hc i)) hA
  · unfold deltaLaw
    split_ifs
    · exact hcl.le
    · exact div_nonneg (mul_nonneg (hw i).le (div_nonneg hlocal hW.le)) hA

theorem sensitivityProbability_pos (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) : 0<sensitivityProbability w c a i := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := sampling_components_nonneg w c a hw hc i
  unfold sensitivityProbability
  linarith

theorem sampling_component_bounds (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) :
    clusterLaw w a i≤4*sensitivityProbability w c a i ∧
    localCostLaw w c a i≤4*sensitivityProbability w c a i ∧
    globalCostLaw w c a i≤4*sensitivityProbability w c a i ∧
    deltaLaw w c a i≤4*sensitivityProbability w c a i := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := sampling_components_nonneg w c a hw hc i
  unfold sensitivityProbability
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem divide_component_bound (u D R p : ℝ) (hD : 0<D) (hR : 0<R)
    (h : u/D/R≤4*p) : u≤4*R*D*p := by
  have h₁ := (div_le_iff₀ hR).mp h
  have h₂ := (div_le_iff₀ hD).mp h₁
  nlinarith only [h₂]

theorem sensitivity_weight_lower (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) :
    w i≤4*(Fintype.card K:ℝ)*groupMass w a (a i)*sensitivityProbability w c a i := by
  have hW : 0<groupMass w a (a i) := (hw i).trans_le (own_le_groupMass w a (fun i=>(hw i).le) i)
  have hR := activeMass_pos w a hw
  have hcomp := (sampling_component_bounds w c a hw hc i).1
  have hb := divide_component_bound (w i) (groupMass w a (a i)) (activeMass w a)
    (sensitivityProbability w c a i) hW hR hcomp
  have hh := mul_le_mul_of_nonneg_right (activeMass_le_card w a)
    (mul_nonneg hW.le (sensitivityProbability_pos w c a hw hc i).le)
  nlinarith only [hb,hh]

theorem sensitivity_local_cost_lower (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) :
    w i*c i≤4*(Fintype.card K:ℝ)*groupMass (fun i=>w i*c i) a (a i)*sensitivityProbability w c a i := by
  let A := groupMass (fun i=>w i*c i) a (a i)
  have hA : 0≤A := groupMass_nonneg _ a (fun i=>mul_nonneg (hw i).le (hc i)) _
  by_cases hz : A=0
  · have hle := own_le_groupMass (fun i=>w i*c i) a (fun i=>mul_nonneg (hw i).le (hc i)) i
    change w i*c i≤4*(Fintype.card K:ℝ)*A*sensitivityProbability w c a i
    change w i*c i≤A at hle
    rw [hz] at hle ⊢
    nlinarith only [hle]
  · have hcomp := (sampling_component_bounds w c a hw hc i).2.1
    have hprob : (w i*c i/A)/activeMass w a≤4*sensitivityProbability w c a i := by
      change (if A=0 then w i/groupMass w a (a i) else w i*c i/A)/activeMass w a≤_ at hcomp
      rw [if_neg hz] at hcomp
      exact hcomp
    have hb := divide_component_bound (w i*c i) A (activeMass w a)
      (sensitivityProbability w c a i) (lt_of_le_of_ne hA (Ne.symm hz)) (activeMass_pos w a hw) hprob
    have hh := mul_le_mul_of_nonneg_right (activeMass_le_card w a)
      (mul_nonneg hA (sensitivityProbability_pos w c a hw hc i).le)
    nlinarith only [hb,hh]

theorem sensitivity_global_cost_lower (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) :
    w i*c i≤4*(∑ j,w j*c j)*sensitivityProbability w c a i := by
  let A := ∑ j,w j*c j
  have hA : 0≤A := Finset.sum_nonneg (fun i _=>mul_nonneg (hw i).le (hc i))
  by_cases hz : A=0
  · have hle : w i*c i≤A := Finset.single_le_sum
      (fun j _=>mul_nonneg (hw j).le (hc j)) (Finset.mem_univ i)
    change w i*c i≤4*A*sensitivityProbability w c a i
    rw [hz] at hle ⊢
    nlinarith only [hle]
  · have hcomp := (sampling_component_bounds w c a hw hc i).2.2.1
    have hh : w i*c i/A≤4*sensitivityProbability w c a i := by
      change (if A=0 then clusterLaw w a i else w i*c i/A)≤_ at hcomp
      rw [if_neg hz] at hcomp
      exact hcomp
    have hb := (div_le_iff₀ (lt_of_le_of_ne hA (Ne.symm hz))).mp hh
    nlinarith only [hb]

theorem sensitivity_delta_lower (w c : I → ℝ) (a : I → K)
    (hw : ∀ i,0<w i) (hc : ∀ i,0≤c i) (i : I) :
    w i*clusterDelta w c a i≤4*(∑ j,w j*c j)*sensitivityProbability w c a i := by
  let A := ∑ j,w j*c j
  have hA : 0≤A := Finset.sum_nonneg (fun i _=>mul_nonneg (hw i).le (hc i))
  have hΔ : ∀ j,0≤w j*clusterDelta w c a j := by
    intro j
    exact mul_nonneg (hw j).le (div_nonneg
      (groupMass_nonneg _ a (fun i=>mul_nonneg (hw i).le (hc i)) _)
      (groupMass_nonneg w a (fun i=>(hw i).le) _))
  by_cases hz : A=0
  · have hle : w i*clusterDelta w c a i≤A := by
      change w i*clusterDelta w c a i≤∑ j,w j*c j
      rw [← clusterDelta_total w c a (fun i=>(hw i).le)]
      exact Finset.single_le_sum (fun j _=>hΔ j) (Finset.mem_univ i)
    change w i*clusterDelta w c a i≤4*A*sensitivityProbability w c a i
    rw [hz] at hle ⊢
    nlinarith only [hle]
  · have hcomp := (sampling_component_bounds w c a hw hc i).2.2.2
    have hh : w i*clusterDelta w c a i/A≤4*sensitivityProbability w c a i := by
      change (if A=0 then clusterLaw w a i else w i*clusterDelta w c a i/A)≤_ at hcomp
      rw [if_neg hz] at hcomp
      exact hcomp
    have hb := (div_le_iff₀ (lt_of_le_of_ne hA (Ne.symm hz))).mp hh
    nlinarith only [hb]

theorem activeMass_eq_card (w : I → ℝ) (a : I → K)
    (hW : ∀ j,groupMass w a j≠0) : activeMass w a=Fintype.card K := by
  simp [activeMass,hW]

/-- Agreement with the paper's four-term formula when no denominator is
zero. The other branches are its explicit zero-cost/empty-cluster extension. -/
theorem sensitivityProbability_formula (w c : I → ℝ) (a : I → K) (i : I)
    (hW : ∀ j,groupMass w a j≠0)
    (hC : ∀ j,groupMass (fun i=>w i*c i) a j≠0)
    (hA : (∑ i,w i*c i)≠0) :
    sensitivityProbability w c a i=(1/4)*(
      w i/((Fintype.card K:ℝ)*groupMass w a (a i))+
      w i*c i/((Fintype.card K:ℝ)*groupMass (fun i=>w i*c i) a (a i))+
      w i*c i/(∑ i,w i*c i)+w i*clusterDelta w c a i/(∑ i,w i*c i)) := by
  simp only [sensitivityProbability,clusterLaw,localCostLaw,globalCostLaw,deltaLaw,
    if_neg (hC (a i)),if_neg hA,activeMass_eq_card w a hW]
  ring

end APC
