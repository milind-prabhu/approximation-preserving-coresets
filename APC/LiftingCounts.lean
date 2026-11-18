import APC.RandomLifting
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

def liftingSampleCount (ε : ℝ) : ℕ := Nat.ceil (3/ε)+1
def liftingRepetitions (k : ℕ) : ℕ := Nat.clog 3 (3*k)+1

instance liftingRepetitions_neZero (k : ℕ) : NeZero (liftingRepetitions k) :=
  ⟨Nat.succ_ne_zero _⟩

theorem liftingSampleCount_valid (ε : ℝ) (hε : 0<ε) :
    0<liftingSampleCount ε ∧ 3≤(liftingSampleCount ε:ℝ)*ε := by
  have hc := Nat.le_ceil (3/ε)
  have hm : (Nat.ceil (3/ε):ℝ)≤liftingSampleCount ε := by simp [liftingSampleCount]
  exact ⟨Nat.zero_lt_succ _,(div_le_iff₀ hε).mp (hc.trans hm)⟩

theorem liftingRepetitions_bound (k : ℕ) :
    (k:ℝ)*(1/3:ℝ)^(liftingRepetitions k)≤1/3 := by
  have hN : 3*k≤3^(liftingRepetitions k) :=
    (Nat.le_pow_clog (by decide : 1<3) (3*k)).trans
      (Nat.pow_le_pow_right (by decide : 0<3) (Nat.le_succ _))
  have hR : 3*(k:ℝ)≤(3:ℝ)^(liftingRepetitions k) := by exact_mod_cast hN
  have he : (k:ℝ)*(1/3:ℝ)^(liftingRepetitions k)=
      (k:ℝ)/(3:ℝ)^(liftingRepetitions k) := by rw [div_pow,one_pow];ring
  rw [he]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<3) _)).2
  nlinarith only [hR]

/-- Algorithm 3 with explicit sample/repetition counts has failure
probability at most 1/3 for every fixed input center tuple. -/
theorem randomized_lifting_explicit
    {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i) (s : K → E) (ε : ℝ) (hε : 0<ε) :
    let m := liftingSampleCount ε
    let r := liftingRepetitions (Fintype.card K)
    eventMass (liftingTrialsLaw x w s m r)
      (fun sample=>(1+ε)*cost x w s<cost x w (randomLift x w s m r sample))≤1/3 := by
  have hm := liftingSampleCount_valid ε hε
  exact (randomized_lifting_failure x w hw s (liftingSampleCount ε)
    (liftingRepetitions _) hm.1 ε hε.le hm.2).trans (liftingRepetitions_bound _)

end APC
