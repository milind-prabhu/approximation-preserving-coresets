import APC.PartitionGeometry
import APC.KMeansResidual
import APC.SensitivityDistribution

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable
variable {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K] [PseudoMetricSpace X]

def closeGroup (w : I → ℝ) (x : I → X) (proxy s : K → X) (ε : ℝ) (j : K) : Prop :=
  ε^2*pointCost s (proxy j)≤
    groupMass (fun i=>w i*pointCost proxy (x i)) (fun i=>nearest proxy (x i)) j /
      groupMass w (fun i=>nearest proxy (x i)) j

/-- Deterministic global assembly of Appendix A. Structural guarantees
and the signed close-residual error imply preservation of the whole cost. -/
theorem global_cost_error (x : I → X) (w v : I → ℝ) (proxy s : K → X)
    (hw : ∀ i,0≤w i) (hv : ∀ i,0≤v i)
    (a ε : ℝ) (hε : 0<ε) (hε1 : ε≤1)
    (happrox : cost x w proxy≤a*cost x w s)
    (hmass : ∀ j,|groupMass v (fun i=>nearest proxy (x i)) j-
      groupMass w (fun i=>nearest proxy (x i)) j|≤ε*groupMass w (fun i=>nearest proxy (x i)) j)
    (hproxy : ∀ j,groupMass (fun i=>v i*pointCost proxy (x i)) (fun i=>nearest proxy (x i)) j≤
      (1+ε)*groupMass (fun i=>w i*pointCost proxy (x i)) (fun i=>nearest proxy (x i)) j)
    (hresidual : |∑ i,(v i-w i)*closeResidual x proxy s ε
      (clusterDelta w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))) i|≤ε*cost x w s) :
    |cost x v s-cost x w s|≤(23+22*a)*ε*cost x w s := by
  let f : I → K := fun i=>nearest proxy (x i)
  let close := closeGroup w x proxy s ε
  let R : K → ℝ := fun j=>pointCost s (proxy j)
  let W : K → ℝ := groupMass w f
  let B := ∑ j,W j*R j
  have hW : ∀ j,0≤W j := groupMass_nonneg w f hw
  have hR : ∀ j,0≤R j := fun j=>sq_nonneg _
  have hres : |∑ i,(v i-w i)*partitionResidual x f proxy s close i|≤ε*cost x w s := by
    simpa only [partitionResidual,closeResidual,closeGroup,clusterDelta,f,close] using hresidual
  have hcenter : |∑ j,if close j then (groupMass v f j-W j)*R j else 0|≤ε*B := by
    calc
      _≤∑ j,|if close j then (groupMass v f j-W j)*R j else 0| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ j,ε*(W j*R j) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : close j
        · rw [if_pos hj,abs_mul,abs_of_nonneg (hR j)]
          have hh := mul_le_mul_of_nonneg_right (hmass j) (hR j)
          convert hh using 1 <;> ring
        · rw [if_neg hj,abs_zero]
          exact mul_nonneg hε.le (mul_nonneg (hW j) (hR j))
      _=ε*B := by rw [← Finset.mul_sum]
  have hfar : |∑ j,if close j then 0 else cost x (fiberWeight v f j) s-cost x (fiberWeight w f j) s|≤10*ε*B := by
    calc
      _≤∑ j,|if close j then 0 else cost x (fiberWeight v f j) s-cost x (fiberWeight w f j) s| :=
        Finset.abs_sum_le_sum_abs _ _
      _≤∑ j,10*ε*(W j*R j) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : close j
        · rw [if_pos hj,abs_zero]
          exact mul_nonneg (by positivity) (mul_nonneg (hW j) (hR j))
        · rw [if_neg hj]
          have hfarj : proxyCost x (fiberWeight w f j) (proxy j)≤ε^2*(W j*R j) := by
            rw [fiber_proxy_cost]
            by_cases hz : W j=0
            · have hzero := groupMass_mul_zero w (fun i=>pointCost proxy (x i)) f hw j hz
              change _≤ε^2*(W j*R j)
              rw [hzero,hz]
              simp
            · have hWp : 0<W j := lt_of_le_of_ne (hW j) (Ne.symm hz)
              have hnot : groupMass (fun i=>w i*pointCost proxy (x i)) f j/W j<ε^2*R j :=
                lt_of_not_ge hj
              have hh := (div_lt_iff₀ hWp).mp hnot
              nlinarith only [hh]
          have hpj : proxyCost x (fiberWeight v f j) (proxy j)≤(1+ε)*proxyCost x (fiberWeight w f j) (proxy j) := by
            rw [fiber_proxy_cost,fiber_proxy_cost]
            exact hproxy j
          exact far_cluster_cost_preservation x (fiberWeight w f j) x (fiberWeight v f j)
            (fiberWeight_nonneg w f hw j) (fiberWeight_nonneg v f hv j) s (proxy j) ε hε hε1
            (hmass j) hpj hfarj
      _=10*ε*B := by rw [← Finset.mul_sum]
  have hdecomp := global_error_decomposition x w v f proxy s close
  rw [hdecomp]
  have habs : |(∑ i,(v i-w i)*partitionResidual x f proxy s close i)+
      (∑ j,if close j then (groupMass v f j-W j)*R j else 0)+
      (∑ j,if close j then 0 else cost x (fiberWeight v f j) s-cost x (fiberWeight w f j) s)|≤
      ε*cost x w s+11*ε*B := by
    have h₁ := abs_add_le (∑ i,(v i-w i)*partitionResidual x f proxy s close i)
      (∑ j,if close j then (groupMass v f j-W j)*R j else 0)
    have h₂ := abs_add_le ((∑ i,(v i-w i)*partitionResidual x f proxy s close i)+
      (∑ j,if close j then (groupMass v f j-W j)*R j else 0))
      (∑ j,if close j then 0 else cost x (fiberWeight v f j) s-cost x (fiberWeight w f j) s)
    linarith only [h₁,h₂,hres,hcenter,hfar]
  have hB : B≤2*(cost x w proxy+cost x w s) := representative_group_bound x w hw proxy s
  have hB₂ : B≤2*(a+1)*cost x w s := by nlinarith only [hB,happrox]
  have hh := mul_le_mul_of_nonneg_left hB₂ (by positivity : 0≤11*ε)
  exact habs.trans (by nlinarith only [hh])

end APC
