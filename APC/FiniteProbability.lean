import APC.SmallMean

open scoped BigOperators
noncomputable section
namespace APC

universe u
def Draws (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | m+1 => I × Draws I m

instance drawsFintype (I : Type*) [Fintype I] (m : ℕ) : Fintype (Draws I m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ m ih =>
    letI := ih
    exact inferInstanceAs (Fintype (I × Draws I m))

def drawWeight {I : Type*} (p : I → ℝ) : (m : ℕ) → Draws I m → ℝ
  | 0, _ => 1
  | m+1, (i, tail) => p i * drawWeight p m tail

def drawSum {I E : Type*} [AddCommMonoid E] (v : I → E) :
    (m : ℕ) → Draws I m → E
  | 0, _ => 0
  | m+1, (i, tail) => v i + drawSum v m tail

theorem drawWeight_nonneg {I : Type*} (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (m : ℕ) : ∀ f : Draws I m, 0 ≤ drawWeight p m f := by
  induction m with
  | zero => intro f; exact zero_le_one
  | succ m ih => intro f; exact mul_nonneg (hp f.1) (ih f.2)

theorem drawWeight_sum {I : Type*} [Fintype I] (p : I → ℝ)
    (h1 : ∑ i, p i = 1) (m : ℕ) : ∑ f, drawWeight p m f = 1 := by
  induction m with
  | zero => simp [Draws, drawWeight]
  | succ m ih =>
    change (∑ f : I × Draws I m, p f.1 * drawWeight p m f.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact h1

/-- The exact second moment for m independent draws, before dividing by m². -/
theorem draw_second_moment {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : I → ℝ) (v : I → E) (h1 : ∑ i, p i = 1)
    (hz : ∑ i, p i • v i = 0) (m : ℕ) :
    (∑ f, drawWeight p m f * ‖drawSum v m f‖^2) =
      (m:ℝ) * ∑ i, p i * ‖v i‖^2 := by
  induction m with
  | zero => simp [Draws, drawSum]
  | succ m ih =>
    change (∑ f : I × Draws I m,
      (p f.1 * drawWeight p m f.2) * ‖v f.1 + drawSum v m f.2‖^2) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have he : ∀ tail : Draws I m,
        (∑ i, (p i * drawWeight p m tail) * ‖v i + drawSum v m tail‖^2) =
        drawWeight p m tail * (‖drawSum v m tail‖^2 + ∑ i, p i * ‖v i‖^2) := by
      intro tail
      calc
        _ = drawWeight p m tail * ∑ i, p i * ‖drawSum v m tail + v i‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [add_comm (v i)]
          ring
        _ = _ := by rw [centered_step_average p v h1 hz]
    simp_rw [he, mul_add]
    rw [Finset.sum_add_distrib, ih, ← Finset.sum_mul, drawWeight_sum p h1]
    push_cast
    ring

def eventMass {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (event : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if event ω then p ω else 0

/-- Markov's inequality on a finite probability space, in a division-free form. -/
theorem finite_markov {Ω : Type*} [Fintype Ω] (p f : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hf : ∀ ω, 0 ≤ f ω) (c : ℝ) :
    c * eventMass p (fun ω => c < f ω) ≤ ∑ ω, p ω * f ω := by
  classical
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with h
  · nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h) (hp ω)]
  · simp only [mul_zero]
    exact mul_nonneg (hp ω) (hf ω)

/-- The 2/3-success estimate for the centered sample sum, including zero
variance. It is the probabilistic ingredient of Lemma 3.3. -/
theorem sample_sum_failure_le_third {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : I → ℝ) (v : I → E) (hp : ∀ i, 0 ≤ p i)
    (h1 : ∑ i, p i = 1) (hz : ∑ i, p i • v i = 0)
    (m : ℕ) (hm : 0 < m) :
    eventMass (drawWeight p m)
      (fun f => 3 * (m:ℝ) * (∑ i, p i * ‖v i‖^2) < ‖drawSum v m f‖^2) ≤ 1/3 := by
  classical
  let V : ℝ := ∑ i, p i * ‖v i‖^2
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
  have hmoment := draw_second_moment p v h1 hz m
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  by_cases hzV : V = 0
  · have he : ∀ f : Draws I m,
        drawWeight p m f * ‖drawSum v m f‖^2 = 0 := by
      intro f
      have hh : drawWeight p m f * ‖drawSum v m f‖^2 ≤
          ∑ g, drawWeight p m g * ‖drawSum v m g‖^2 :=
        Finset.single_le_sum (fun g _ => mul_nonneg
          (drawWeight_nonneg p hp m g) (sq_nonneg ‖drawSum v m g‖)) (Finset.mem_univ f)
      have hzero : (∑ g, drawWeight p m g * ‖drawSum v m g‖^2) = 0 := by
        rw [hmoment]; change (m:ℝ) * V = 0; rw [hzV, mul_zero]
      exact le_antisymm (hzero ▸ hh)
        (mul_nonneg (drawWeight_nonneg p hp m f) (sq_nonneg _))
    have hprob : eventMass (drawWeight p m)
        (fun f => 3 * (m:ℝ) * (∑ i, p i * ‖v i‖^2) < ‖drawSum v m f‖^2) = 0 := by
      unfold eventMass
      apply Finset.sum_eq_zero
      intro f _
      split_ifs with h
      · change 3 * (m:ℝ) * V < _ at h
        rw [hzV, mul_zero] at h
        exact (mul_eq_zero.mp (he f)).resolve_right (ne_of_gt h)
      · rfl
    rw [hprob]; norm_num
  · have hpos : 0 < (m:ℝ) * V := mul_pos hmR (lt_of_le_of_ne hV (Ne.symm hzV))
    have hb := finite_markov (drawWeight p m) (fun f => ‖drawSum v m f‖^2)
      (drawWeight_nonneg p hp m) (fun f => sq_nonneg _) (3 * (m:ℝ) * V)
    rw [hmoment] at hb
    change (3 * (m:ℝ) * V) * _ ≤ (m:ℝ) * V at hb
    change eventMass _ (fun f => 3 * (m:ℝ) * V < _) ≤ _
    nlinarith

end APC
