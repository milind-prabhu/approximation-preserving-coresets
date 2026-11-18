import APC.ConcentrationGeometry

open scoped BigOperators
noncomputable section
namespace APC
variable {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K] [PseudoMetricSpace X]

def proxyCost (x : I → X) (w : I → ℝ) (a : X) : ℝ := ∑ i, w i*(dist (x i) a)^2

theorem pointCost_young (s : K → X) (x a : X) (ε : ℝ) (hε : 0 ≤ ε) :
    ε*|pointCost s x-pointCost s a| ≤
      ε^2*pointCost s a + (1+ε)*(dist x a)^2 := by
  have hb := pointCost_difference s a x
  rw [dist_comm a x, abs_sub_comm] at hb
  have hm := mul_le_mul_of_nonneg_left hb hε
  have hy := sq_nonneg (ε*centerDist s a-dist x a)
  change _ ≤ ε^2*(centerDist s a)^2 + _
  nlinarith only [hm,hy]

/-- Deterministic cluster deviation bound, obtained by Young's inequality.
It avoids any nonzero-variance or nonempty-cluster requirement. -/
theorem weighted_center_deviation (x : I → X) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (s : K → X) (a : X) (ε : ℝ) (hε : 0 ≤ ε) :
    ε*|cost x w s-mass w*pointCost s a| ≤
      ε^2*(mass w*pointCost s a)+(1+ε)*proxyCost x w a := by
  have he : cost x w s-mass w*pointCost s a =
      ∑ i, w i*(pointCost s (x i)-pointCost s a) := by
    simp [cost,mass,mul_sub,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [he]
  have habs := Finset.abs_sum_le_sum_abs
    (fun i => w i*(pointCost s (x i)-pointCost s a)) Finset.univ
  calc
    _ ≤ ε*∑ i, |w i*(pointCost s (x i)-pointCost s a)| :=
      mul_le_mul_of_nonneg_left habs hε
    _ = ∑ i, w i*(ε*|pointCost s (x i)-pointCost s a|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul,abs_of_nonneg (hw i)]
      ring
    _ ≤ ∑ i, w i*(ε^2*pointCost s a+(1+ε)*(dist (x i) a)^2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (pointCost_young s (x i) a ε hε) (hw i))
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,proxyCost,mass]
      rw [Finset.mul_sum]
      have hfirst : (∑ i, w i*(ε^2*pointCost s a)) =
          ε^2*((∑ i,w i)*pointCost s a) := by rw [← Finset.sum_mul]; ring
      rw [hfirst]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem far_center_deviation (x : I → X) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (s : K → X) (a : X) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfar : proxyCost x w a ≤ ε^2*(mass w*pointCost s a)) :
    |cost x w s-mass w*pointCost s a| ≤ 3*ε*(mass w*pointCost s a) := by
  have hb := weighted_center_deviation x w hw s a ε hε.le
  have hf := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 1+ε)
  have hH : 0 ≤ mass w*pointCost s a := mul_nonneg
    (Finset.sum_nonneg (fun i _ => hw i)) (sq_nonneg _)
  have hh := mul_nonneg (sub_nonneg.mpr hε1) (mul_nonneg (sq_nonneg ε) hH)
  nlinarith only [hb,hf,hh,hε]

/-- Claim A.11 with constant 10. Structural weight/proxy-cost guarantees
are visible premises; no probabilistic conclusion is assumed. -/
theorem far_cluster_cost_preservation {J : Type*} [Fintype J]
    (x : I → X) (w : I → ℝ) (y : J → X) (v : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (s : K → X) (a : X) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmass : |mass v-mass w| ≤ ε*mass w)
    (hproxy : proxyCost y v a ≤ (1+ε)*proxyCost x w a)
    (hfar : proxyCost x w a ≤ ε^2*(mass w*pointCost s a)) :
    |cost y v s-cost x w s| ≤ 10*ε*(mass w*pointCost s a) := by
  let H := mass w*pointCost s a
  have hH : 0 ≤ H := mul_nonneg
    (Finset.sum_nonneg (fun i _ => hw i)) (sq_nonneg _)
  have hpc : 0 ≤ pointCost s a := sq_nonneg _
  have hmass_up : mass v ≤ 2*mass w := by
    have hm := (abs_le.mp hmass).2
    have hwM : 0 ≤ mass w := Finset.sum_nonneg (fun i _ => hw i)
    nlinarith only [hm,mul_le_mul_of_nonneg_right hε1 hwM]
  have hcenter_up : mass v*pointCost s a ≤ 2*H := by
    exact (mul_le_mul_of_nonneg_right hmass_up hpc).trans_eq (by dsimp [H];ring)
  have hp0 : 0 ≤ proxyCost x w a := Finset.sum_nonneg
    (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have hp_up : proxyCost y v a ≤ 2*ε^2*H := by
    have hh := mul_le_mul_of_nonneg_right hε1 hp0
    have hf := mul_le_mul_of_nonneg_left hfar (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [hproxy,hh,hf]
  have hbnew := weighted_center_deviation y v hv s a ε hε.le
  have h₁ := mul_le_mul_of_nonneg_left hcenter_up (sq_nonneg ε)
  have h₂ := mul_le_mul_of_nonneg_left hp_up (by positivity : 0 ≤ 1+ε)
  have h₃ := mul_nonneg (sub_nonneg.mpr hε1) (mul_nonneg (sq_nonneg ε) hH)
  have hnew : |cost y v s-mass v*pointCost s a| ≤ 6*ε*H := by
    nlinarith only [hbnew,h₁,h₂,h₃,hε]
  have hold := far_center_deviation x w hw s a ε hε hε1 hfar
  have hmiddle : |mass v*pointCost s a-mass w*pointCost s a| ≤ ε*H := by
    rw [← sub_mul,abs_mul,abs_of_nonneg hpc]
    have hh := mul_le_mul_of_nonneg_right hmass hpc
    convert hh using 1 <;> dsimp [H] <;> ring
  have ht₁ := abs_sub_le (cost y v s) (mass v*pointCost s a) (cost x w s)
  have ht₂ := abs_sub_le (mass v*pointCost s a) (mass w*pointCost s a) (cost x w s)
  rw [abs_sub_comm (mass w*pointCost s a) (cost x w s)] at ht₂
  change |cost x w s-mass w*pointCost s a| ≤ 3*ε*H at hold
  nlinarith only [ht₁,ht₂,hnew,hold,hmiddle]

end APC
