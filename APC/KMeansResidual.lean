import APC.ResidualFamily
import APC.Sampler

open scoped BigOperators
noncomputable section
namespace APC
variable {I K X : Type*} [Fintype I] [Fintype K] [Nonempty K] [PseudoMetricSpace X]

def closeResidual (x : I → X) (proxy s : K → X) (ε : ℝ) (Δ : I → ℝ) : I → ℝ := by
  classical
  exact fun i => if ε^2*pointCost s (proxy (nearest proxy (x i))) ≤ Δ i
    then pointCost s (x i)-pointCost s (proxy (nearest proxy (x i))) else 0

theorem closeResidual_square (x : I → X) (proxy s : K → X) (ε : ℝ) (Δ : I → ℝ) :
    ∀ i, (closeResidual x proxy s ε Δ i)^2 ≤
      8*pointCost s (x i)*pointCost proxy (x i)+2*(pointCost proxy (x i))^2 := by
  classical
  intro i
  unfold closeResidual
  split_ifs
  · simpa only [pointCost,pow_mul,← pow_mul] using
      pointCost_difference_sq s (x i) (proxy (nearest proxy (x i)))
  · have h₁ : 0≤pointCost s (x i) := sq_nonneg _
    have h₂ : 0≤pointCost proxy (x i) := sq_nonneg _
    nlinarith [mul_nonneg h₁ h₂,sq_nonneg (pointCost proxy (x i))]

theorem closeResidual_range (x : I → X) (proxy s : K → X) (ε : ℝ) (Δ : I → ℝ)
    (hε : 0≤ε) (hε1 : ε≤1) (hΔ : ∀ i,0≤Δ i) :
    ∀ i, ε*|closeResidual x proxy s ε Δ i|≤2*(Δ i+pointCost proxy (x i)) := by
  classical
  intro i
  unfold closeResidual
  split_ifs with h
  · exact close_pointCost_difference s (x i) (proxy (nearest proxy (x i))) ε (Δ i)
      hε hε1 (hΔ i) h
  · have hc : 0≤pointCost proxy (x i) := sq_nonneg _
    simp only [abs_zero,mul_zero]
    linarith [hΔ i]

/-- Concrete k-means instantiation of Claim A.7. The residual is defined
from the actual near/far predicate and nearest-center objective. -/
theorem kmeans_close_residual_concentration
    (x : I → X) (w p Δ : I → ℝ) (proxy s : K → X) (a ε : ℝ)
    (hw : ∀ i,0≤w i) (hp : ∀ i,0<p i) (h1 : ∑ i,p i=1)
    (hΔ : ∀ i,0≤Δ i) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (hC : 0<cost x w s) (happrox : cost x w proxy≤a*cost x w s)
    (hsensC : ∀ i,w i*pointCost proxy (x i)≤4*cost x w proxy*p i)
    (hsensΔ : ∀ i,w i*Δ i≤4*cost x w proxy*p i)
    (m : ℕ) (hm : 0<m) :
    eventMass (drawWeight p m)
      (fun sample=>ε< |importanceEstimate p
        (normalizedResidual w (closeResidual x proxy s ε Δ) (cost x w s)) m sample-
        ∑ i,normalizedResidual w (closeResidual x proxy s ε Δ) (cost x w s) i|)≤
      2*Real.exp (-(m:ℝ)*ε^2/(4*(64*a+8*a^2))) := by
  exact close_residual_concentration w (closeResidual x proxy s ε Δ)
    (fun i=>pointCost s (x i)) (fun i=>pointCost proxy (x i)) Δ p
    (cost x w s) (cost x w proxy) a ε hw
    (fun i=>sq_nonneg _) (fun i=>sq_nonneg _) hp h1 hC (cost_nonneg x w hw proxy) ha hε
    rfl rfl happrox hsensC hsensΔ (closeResidual_square x proxy s ε Δ)
    (closeResidual_range x proxy s ε Δ hε.le hε1 hΔ) m hm

/-- A zero-cost solution is preserved exactly by inverse-probability
sampling, so the positive-cost concentration branch loses no cases. -/
theorem sampled_zero_cost (x : I → X) (w p : I → ℝ) (hw : ∀ i,0≤w i)
    (s : K → X) (hz : cost x w s=0) (m : ℕ) (sample : Draws I m) :
    cost (sampledPoints x m sample) (sampledWeights w p m sample) s=0 := by
  have hzero : ∀ i,w i*pointCost s (x i)=0 := by
    intro i
    have hle : w i*pointCost s (x i)≤cost x w s :=
      Finset.single_le_sum (fun j _=>mul_nonneg (hw j)
        (show 0≤pointCost s (x j) from sq_nonneg _)) (Finset.mem_univ i)
    exact le_antisymm (hz ▸ hle) (mul_nonneg (hw i) (sq_nonneg _))
  rw [sampled_cost_eq]
  simp [importanceEstimate,drawSum_eq_sum,hzero]

end APC
