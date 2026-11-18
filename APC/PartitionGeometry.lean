import APC.Partition
import APC.FarClusters

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable
variable {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K] [PseudoMetricSpace X]

theorem fiber_cost_total (x : I → X) (w : I → ℝ) (a : I → K) (s : K → X) :
    (∑ j,cost x (fiberWeight w a j) s)=cost x w s := by
  simp only [cost,fiberWeight,ite_mul,zero_mul]
  exact group_sum a (fun _ i=>w i*pointCost s (x i))

theorem fiber_proxy_cost (x : I → X) (w : I → ℝ) (proxy : K → X) (j : K) :
    proxyCost x (fiberWeight w (fun i=>nearest proxy (x i)) j) (proxy j)=
      groupMass (fun i=>w i*pointCost proxy (x i)) (fun i=>nearest proxy (x i)) j := by
  unfold proxyCost groupMass
  apply Finset.sum_congr rfl
  intro i _
  simp only [fiberWeight,pointCost]
  split_ifs with h
  · rw [h]
  · simp

def partitionResidual (x : I → X) (a : I → K) (proxy s : K → X)
    (close : K → Prop) (i : I) : ℝ :=
  if close (a i) then pointCost s (x i)-pointCost s (proxy (a i)) else 0

theorem partition_residual_sum (x : I → X) (w v : I → ℝ) (a : I → K)
    (proxy s : K → X) (close : K → Prop) :
    (∑ i,(v i-w i)*partitionResidual x a proxy s close i)=
    ∑ j,if close j then cost x (fiberWeight v a j) s-cost x (fiberWeight w a j) s-
      (groupMass v a j-groupMass w a j)*pointCost s (proxy j) else 0 := by
  unfold partitionResidual
  rw [← group_sum a (fun j i=>(v i-w i)*(if close j then pointCost s (x i)-pointCost s (proxy j) else 0))]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : close j
  · simp only [if_pos hj,cost,groupMass,fiberWeight,Finset.sum_sub_distrib,Finset.sum_mul]
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  · simp [hj]

theorem global_error_decomposition (x : I → X) (w v : I → ℝ) (a : I → K)
    (proxy s : K → X) (close : K → Prop) :
    cost x v s-cost x w s=
      (∑ i,(v i-w i)*partitionResidual x a proxy s close i)+
      (∑ j,if close j then (groupMass v a j-groupMass w a j)*pointCost s (proxy j) else 0)+
      (∑ j,if close j then 0 else cost x (fiberWeight v a j) s-cost x (fiberWeight w a j) s) := by
  rw [partition_residual_sum]
  have htotal : cost x v s-cost x w s=
      ∑ j,(cost x (fiberWeight v a j) s-cost x (fiberWeight w a j) s) := by
    rw [Finset.sum_sub_distrib,fiber_cost_total,fiber_cost_total]
  rw [htotal,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : close j <;> simp [h] <;> ring

theorem representative_group_bound (x : I → X) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (proxy s : K → X) :
    (∑ j,groupMass w (fun i=>nearest proxy (x i)) j*pointCost s (proxy j))≤
      2*(cost x w proxy+cost x w s) := by
  rw [← group_mul_sum w (fun i=>nearest proxy (x i)) (fun j=>pointCost s (proxy j))]
  exact representative_cost_bound x w hw proxy s

end APC
