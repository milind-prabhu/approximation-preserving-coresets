import APC.Sampler
import APC.Transfer

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace APC
variable {I J E : Type*} [Fintype I] [Fintype J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expansion around any reference point, without assuming it is the
weighted centroid of the second cloud. -/
theorem oneCost_reference_expansion (y : J → E) (v : J → ℝ) (μ c : E) :
    oneCost y v c = oneCost y v μ + mass v*‖μ-c‖^2 +
      2*inner ℝ (∑ j,v j • (y j-μ)) (μ-c) := by
  have he : ∀ j,v j*‖y j-c‖^2 = v j*‖y j-μ‖^2+
      v j*‖μ-c‖^2+2*(v j*inner ℝ (y j-μ) (μ-c)) := by
    intro j
    rw [show y j-c=(y j-μ)+(μ-c) by abel,norm_add_sq_real]
    ring
  unfold oneCost mass
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  have hc : (∑ j,v j*inner ℝ (y j-μ) (μ-c)) = inner ℝ (∑ j,v j • (y j-μ)) (μ-c) := by
    simp_rw [←real_inner_smul_left]
    rw [sum_inner]
  rw [hc]

/-- Cauchy--Schwarz and a scalar square control the centered first moment
uniformly over every possible query center. -/
theorem inner_moment_bound (z d : E) (M V η : ℝ)
    (hM : 0≤M) (hV : 0≤V) (hη : 0≤η)
    (hz : ‖z‖^2≤η^2*M*V) :
    |2*inner ℝ z d|≤η*(V+M*‖d‖^2) := by
  have hi := abs_real_inner_le_norm z d
  have hi2 : |inner ℝ z d|^2≤‖z‖^2*‖d‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hs := mul_le_mul_of_nonneg_right hz (sq_nonneg ‖d‖)
  have hgap : 0≤η^2*(V-M*‖d‖^2)^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hright : 0≤η*(V+M*‖d‖^2) := by positivity
  rw [abs_mul]
  norm_num
  nlinarith only [hi2,hs,hgap,hright,abs_nonneg (inner ℝ z d)]

/-- Three normalized moment estimates suffice for a strong coreset for
one-center Euclidean clustering; the conclusion quantifies over all E. -/
theorem oneCenter_strong_of_moments
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i) (hM : 0<mass w)
    (y : J → E) (v : J → ℝ) (η : ℝ) (hη : 0≤η)
    (hMass : |mass v-mass w|≤η*mass w)
    (hVariance : |oneCost y v (mean x w)-oneCost x w (mean x w)|≤η*oneCost x w (mean x w))
    (hMean : ‖∑ j,v j • (y j-mean x w)‖^2≤η^2*mass w*oneCost x w (mean x w)) :
    ∀ c,Preserves (oneCost x w c) (oneCost y v c) (2*η) := by
  intro c
  let V := oneCost x w (mean x w)
  let d := mean x w-c
  have hV : 0≤V := oneCost_nonneg x w hw _
  have hb := inner_moment_bound (∑ j,v j • (y j-mean x w)) d (mass w) V η hM.le hV hη hMean
  have hcost := variance_identity x w (ne_of_gt hM) c
  have hy := oneCost_reference_expansion y v (mean x w) c
  have hmass := (abs_le.mp hMass)
  have hvar := (abs_le.mp hVariance)
  have hcross := abs_le.mp hb
  have hml := mul_le_mul_of_nonneg_right hmass.1 (sq_nonneg ‖d‖)
  have hmu := mul_le_mul_of_nonneg_right hmass.2 (sq_nonneg ‖d‖)
  dsimp [V,d] at hV hb hcross hml hmu
  have hcostη := congrArg (fun z : ℝ=>η*z) hcost
  constructor <;> dsimp [Preserves] <;>
    nlinarith only [hcost,hcostη,hy,hvar.1,hvar.2,hcross.1,hcross.2,hml,hmu]

end APC
