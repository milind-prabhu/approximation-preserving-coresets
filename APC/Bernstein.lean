import APC.Amplification
import Mathlib.Analysis.Complex.Exponential

open scoped BigOperators
noncomputable section
namespace APC

/-- Local exponential estimate used to prove the moment-generating bound. -/
theorem exp_le_quadratic (z : ℝ) (hz : |z| ≤ 1) :
    Real.exp z ≤ 1 + z + z^2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hz)).2
  linarith

theorem finite_centered_mgf {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (hzero : ∑ i, p i * f i = 0) (θ V : ℝ)
    (hsmall : ∀ i, |θ * f i| ≤ 1)
    (hvar : ∑ i, p i * (f i)^2 ≤ V) :
    (∑ i, p i * Real.exp (θ * f i)) ≤ Real.exp (θ^2 * V) := by
  have h₁ : (∑ i, p i * Real.exp (θ * f i)) ≤
      ∑ i, p i * (1 + θ * f i + (θ * f i)^2) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (exp_le_quadratic _ (hsmall i)) (hp i))
  have he : (∑ i, p i * (1 + θ * f i + (θ * f i)^2)) =
      1 + θ^2 * ∑ i, p i * (f i)^2 := by
    simp_rw [mul_add, mul_one, mul_pow]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1]
    have ha : (∑ i, p i * (θ * f i)) = θ * ∑ i, p i * f i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    have hb : (∑ i, p i * (θ^2 * f i^2)) = θ^2 * ∑ i, p i * f i^2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [ha, hb, hzero]
    ring
  rw [he] at h₁
  calc
    _ ≤ 1 + θ^2 * V := h₁.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left hvar (sq_nonneg θ)) 1)
    _ ≤ Real.exp (θ^2 * V) := by linarith [Real.add_one_le_exp (θ^2 * V)]

/-- Exact factorization of the exponential moment for independent draws. -/
theorem draw_exp_moment {I : Type*} [Fintype I]
    (p f : I → ℝ) (θ : ℝ) (m : ℕ) :
    (∑ a, drawWeight p m a * Real.exp (θ * drawSum f m a)) =
      (∑ i, p i * Real.exp (θ * f i))^m := by
  induction m with
  | zero => simp [Draws, drawWeight, drawSum]
  | succ m ih =>
    change (∑ a : I × Draws I m,
      (p a.1 * drawWeight p m a.2) * Real.exp (θ * (f a.1 + drawSum f m a.2))) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_add, Real.exp_add]
    have he : ∀ i, (∑ tail : Draws I m,
        (p i * drawWeight p m tail) *
          (Real.exp (θ*f i) * Real.exp (θ*drawSum f m tail))) =
        (p i * Real.exp (θ*f i)) *
          ∑ tail, drawWeight p m tail * Real.exp (θ*drawSum f m tail) := by
      intro i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      ring
    simp_rw [he]
    rw [← Finset.sum_mul, ih, pow_succ]
    ring

/-- Chernoff bound on a finite probability space. -/
theorem finite_chernoff {Ω : Type*} [Fintype Ω]
    (p f : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (θ t : ℝ) (hθ : 0 < θ) :
    eventMass p (fun ω => t < f ω) ≤
      Real.exp (-θ*t) * ∑ ω, p ω * Real.exp (θ*f ω) := by
  have he : eventMass p (fun ω => t < f ω) ≤
      eventMass p (fun ω => Real.exp (θ*t) < Real.exp (θ*f ω)) := by
    apply eventMass_mono p hp
    intro ω h
    exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hθ)
  have hm := finite_markov p (fun ω => Real.exp (θ*f ω)) hp
    (fun ω => (Real.exp_pos _).le) (Real.exp (θ*t))
  have hb : eventMass p (fun ω => t < f ω) ≤
      (∑ ω, p ω * Real.exp (θ*f ω)) / Real.exp (θ*t) :=
    he.trans ((le_div_iff₀ (Real.exp_pos _)).2 (by nlinarith only [hm]))
  calc
    _ ≤ _ := hb
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]; ring

/-- One-sided Bernstein estimate in parameter form. The variance, rather
than the squared range, controls the quadratic exponential term. -/
theorem draw_upper_tail_mgf {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (hzero : ∑ i, p i * f i = 0) (θ V t : ℝ) (hθ : 0 < θ)
    (hsmall : ∀ i, |θ*f i| ≤ 1)
    (hvar : ∑ i, p i * (f i)^2 ≤ V) (m : ℕ) :
    eventMass (drawWeight p m) (fun a => t < drawSum f m a) ≤
      Real.exp (-θ*t + (m:ℝ)*θ^2*V) := by
  have hb := finite_chernoff (drawWeight p m) (drawSum f m)
    (drawWeight_nonneg p hp m) θ t hθ
  rw [draw_exp_moment] at hb
  have hpows := pow_le_pow_left₀
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (Real.exp_pos _).le))
    (finite_centered_mgf p f hp h1 hzero θ V hsmall hvar) m
  calc
    _ ≤ Real.exp (-θ*t) * (Real.exp (θ^2*V))^m :=
      hb.trans (mul_le_mul_of_nonneg_left hpows (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem eventMass_or_le {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (e f : Ω → Prop) :
    eventMass p (fun ω => e ω ∨ f ω) ≤ eventMass p e + eventMass p f := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : e ω <;> by_cases hf : f ω <;> simp [he, hf, hp]

theorem drawSum_neg {I : Type*} (f : I → ℝ) (m : ℕ) (a : Draws I m) :
    drawSum (fun i => -f i) m a = -drawSum f m a := by
  induction m with
  | zero => simp [drawSum]
  | succ m ih =>
    rcases a with ⟨i, tail⟩
    simp [drawSum, ih, add_comm]

theorem draw_two_sided_tail_mgf {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (hzero : ∑ i, p i * f i = 0) (θ V t : ℝ) (hθ : 0 < θ)
    (hsmall : ∀ i, |θ*f i| ≤ 1)
    (hvar : ∑ i, p i * (f i)^2 ≤ V) (m : ℕ) :
    eventMass (drawWeight p m) (fun a => t < |drawSum f m a|) ≤
      2 * Real.exp (-θ*t + (m:ℝ)*θ^2*V) := by
  have hupper := draw_upper_tail_mgf p f hp h1 hzero θ V t hθ hsmall hvar m
  have hzneg : (∑ i, p i * (-f i)) = 0 := by simp [Finset.sum_neg_distrib, hzero]
  have hneg := draw_upper_tail_mgf p (fun i => -f i) hp h1 hzneg θ V t hθ
    (fun i => by simpa using hsmall i) (by simpa using hvar) m
  simp_rw [drawSum_neg] at hneg
  have hu := eventMass_or_le (drawWeight p m) (drawWeight_nonneg p hp m)
    (fun a => t < drawSum f m a) (fun a => t < -drawSum f m a)
  have he : eventMass (drawWeight p m) (fun a => t < |drawSum f m a|) =
      eventMass (drawWeight p m) (fun a => t < drawSum f m a ∨ t < -drawSum f m a) := by
    congr 1
    funext a
    exact propext lt_abs
  rw [he]
  linarith

/-- A Bernstein inequality for the average of independent finite draws.
Its constants differ from the textbook formula but yield the same rate:
2 exp(-m r² / (4(V+Mr))). No tail estimate is taken as an assumption. -/
theorem finite_bernstein {I : Type*} [Fintype I]
    (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (hzero : ∑ i, p i * f i = 0) (M V r : ℝ)
    (hM : 0 ≤ M) (hV : 0 < V) (hr : 0 < r)
    (hbound : ∀ i, |f i| ≤ M)
    (hvar : ∑ i, p i * (f i)^2 ≤ V) (m : ℕ) :
    eventMass (drawWeight p m) (fun a => (m:ℝ)*r < |drawSum f m a|) ≤
      2 * Real.exp (-(m:ℝ)*r^2 / (4*(V+M*r))) := by
  let D := V + M*r
  have hD : 0 < D := by dsimp [D]; positivity
  let θ := r / (2*D)
  have hθ : 0 < θ := div_pos hr (by positivity)
  have hθM : θ*M ≤ 1 := by
    dsimp [θ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    dsimp [D]
    nlinarith [mul_nonneg hM hr.le]
  have hsmall : ∀ i, |θ*f i| ≤ 1 := by
    intro i
    rw [abs_mul, abs_of_pos hθ]
    exact (mul_le_mul_of_nonneg_left (hbound i) hθ.le).trans hθM
  have hscalar : -θ*r + θ^2*V ≤ -r^2/(4*D) := by
    have he : -θ*r + θ^2*V = -r^2/(4*D) - (M*r)*r^2/(4*D^2) := by
      dsimp [θ, D]
      field_simp
      ring
    rw [he]
    exact sub_le_self _ (by positivity)
  have hrate : -θ*((m:ℝ)*r) + (m:ℝ)*θ^2*V ≤ -(m:ℝ)*r^2/(4*D) := by
    convert mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg m) using 1 <;> ring
  exact (draw_two_sided_tail_mgf p f hp h1 hzero θ V ((m:ℝ)*r) hθ hsmall hvar m).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by norm_num))

end APC
