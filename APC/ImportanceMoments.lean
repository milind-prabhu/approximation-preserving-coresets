import APC.ImportanceSampling
import APC.Sampler

open scoped BigOperators
noncomputable section
namespace APC
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem importance_expectation (p f : I → ℝ) (hp : ∀ i,0<p i) :
    expectation p (fun i=>f i/p i)=∑ i,f i := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (hp i)]

/-- Exact mean-square error of an importance-weighted scalar estimator. -/
theorem importance_estimator_mse (p f : I → ℝ) (hp : ∀ i,0<p i)
    (h1 : ∑ i,p i=1) (m : ℕ) (hm : 0<m) :
    (∑ z,drawWeight p m z*(importanceEstimate p f m z-(∑ i,f i))^2)=
      ((∑ i,p i*(f i/p i)^2)-(∑ i,f i)^2)/(m:ℝ) := by
  let T := ∑ i,f i
  let g := fun i=>f i/p i-T
  have hE := importance_expectation p f hp
  have hz : ∑ i,p i • g i=0 := by
    simpa only [g,smul_eq_mul,hE] using centered_expectation p (fun i=>f i/p i) h1
  have hv := centered_second_moment p (fun i=>f i/p i) h1
  rw [hE] at hv
  have hd := draw_second_moment p g h1 hz m
  have he : ∀ z,importanceEstimate p f m z-T=drawSum g m z/(m:ℝ) := by
    intro z
    have hc := drawSum_centered (fun i=>f i/p i) T m z
    simp only [smul_eq_mul] at hc
    dsimp only [importanceEstimate,g]
    rw [hc]
    field_simp
  change (∑ z,drawWeight p m z*(importanceEstimate p f m z-T)^2)=_
  simp_rw [he,div_pow,←mul_div_assoc]
  rw [←Finset.sum_div]
  have hd' : (∑ z,drawWeight p m z*(drawSum g m z)^2)=(m:ℝ)*(∑ i,p i*g i^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hd
  rw [hd']
  change (m:ℝ)*(∑ i,p i*(f i/p i-T)^2)/(m:ℝ)^2=_
  rw [hv]
  dsimp [T]
  field_simp

/-- Sensitivity domination controls the scalar estimator's variance. -/
theorem importance_estimator_mse_bound (p f : I → ℝ) (hp : ∀ i,0<p i)
    (h1 : ∑ i,p i=1) (hf : ∀ i,0≤f i) (R : ℝ)
    (hbound : ∀ i,f i≤R*p i) (m : ℕ) (hm : 0<m) :
    (∑ z,drawWeight p m z*(importanceEstimate p f m z-(∑ i,f i))^2)≤
      R*(∑ i,f i)/(m:ℝ) := by
  rw [importance_estimator_mse p f hp h1 m hm]
  have hs : (∑ i,p i*(f i/p i)^2)≤R*(∑ i,f i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb := mul_le_mul_of_nonneg_left (hbound i) (hf i)
    apply (mul_le_mul_right (hp i)).mp
    have hid : (p i*(f i/p i)^2)*p i=f i^2 := by field_simp [ne_of_gt (hp i)] <;> ring
    rw [hid]
    nlinarith only [hb]
  exact div_le_div_of_nonneg_right (by nlinarith only [hs,sq_nonneg (∑ i,f i)]) (by positivity)

def vectorImportance (p : I → ℝ) (v : I → E) (m : ℕ) (z : Draws I m) : E :=
  (m:ℝ)⁻¹ • drawSum (fun i=>(p i)⁻¹ • v i) m z

/-- Exact vector second moment, including arbitrary Hilbert dimensions. -/
theorem vectorImportance_mse (p : I → ℝ) (v : I → E) (hp : ∀ i,0<p i)
    (h1 : ∑ i,p i=1) (hv : ∑ i,v i=0) (m : ℕ) (hm : 0<m) :
    (∑ z,drawWeight p m z*‖vectorImportance p v m z‖^2)=
      (∑ i,‖v i‖^2/p i)/(m:ℝ) := by
  have hz : ∑ i,p i • ((p i)⁻¹ • v i)=0 := by
    simp only [smul_smul,mul_inv_cancel₀ (ne_of_gt (hp _)),one_smul]
    exact hv
  have h := draw_second_moment p (fun i=>(p i)⁻¹ • v i) h1 hz m
  have he : ∑ i,p i*‖(p i)⁻¹ • v i‖^2=∑ i,‖v i‖^2/p i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    field_simp [ne_of_gt (hp i)]
  rw [he] at h
  simp only [vectorImportance,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  calc
    _ = ((m:ℝ)⁻¹)^2*(∑ z,drawWeight p m z*‖drawSum (fun i=>(p i)⁻¹ • v i) m z‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [h];field_simp

end APC
