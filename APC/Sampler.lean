import APC.ImportanceSampling
import APC.Clustering

open scoped BigOperators
noncomputable section
namespace APC

def drawIndex {I : Type*} : (m : ℕ) → Draws I m → Fin m → I
  | 0, _ => Fin.elim0
  | m+1, (i, tail) => Fin.cons i (drawIndex m tail)

theorem drawSum_eq_sum {I : Type*} (f : I → ℝ) (m : ℕ) (a : Draws I m) :
    drawSum f m a = ∑ j, f (drawIndex m a j) := by
  induction m with
  | zero => simp [drawSum]
  | succ m ih =>
    rcases a with ⟨i, tail⟩
    simp [drawSum, drawIndex, Fin.sum_univ_succ, ih]

def sampledPoints {I X : Type*} (x : I → X) (m : ℕ) (a : Draws I m) : Fin m → X :=
  fun j => x (drawIndex m a j)

def sampledWeights {I : Type*} (w p : I → ℝ) (m : ℕ) (a : Draws I m) : Fin m → ℝ :=
  fun j => w (drawIndex m a j) / ((m:ℝ)*p (drawIndex m a j))

theorem sampledWeights_nonneg {I : Type*} (w p : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (m : ℕ) (a : Draws I m) :
    ∀ j, 0 ≤ sampledWeights w p m a j := by
  intro j
  exact div_nonneg (hw _) (mul_nonneg (Nat.cast_nonneg _) (hp _))

/-- The finite random experiment is exactly inverse-probability weighted
sampling, with repeated draws represented as separate weighted entries. -/
theorem sampled_cost_eq {I K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]
    (x : I → X) (w p : I → ℝ) (m : ℕ) (a : Draws I m) (s : K → X) :
    cost (sampledPoints x m a) (sampledWeights w p m a) s =
      importanceEstimate p (fun i => w i * pointCost s (x i)) m a := by
  unfold cost importanceEstimate
  rw [drawSum_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [sampledPoints, sampledWeights]
  ring

theorem importanceEstimate_add {I : Type*} (p f g : I → ℝ) (m : ℕ) (a : Draws I m) :
    importanceEstimate p (fun i => f i+g i) m a =
      importanceEstimate p f m a + importanceEstimate p g m a := by
  unfold importanceEstimate
  simp only [drawSum_eq_sum, add_div, Finset.sum_add_distrib]

theorem importanceEstimate_smul {I : Type*} (p f : I → ℝ) (z : ℝ) (m : ℕ) (a : Draws I m) :
    importanceEstimate p (fun i => z*f i) m a = z*importanceEstimate p f m a := by
  unfold importanceEstimate
  simp only [drawSum_eq_sum]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end APC
