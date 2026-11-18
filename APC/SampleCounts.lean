import APC.EuclideanCompression
import Mathlib.Data.Real.Archimedean

open scoped BigOperators
noncomputable section
namespace APC

def meanSampleCount (ε : ℝ) : ℕ := Nat.ceil (10/ε)+1
def budgetSampleCount (S R z : ℝ) : ℕ := Nat.ceil (max S R/z^2)+1

theorem meanSampleCount_valid (ε : ℝ) (hε : 0<ε) :
    0<meanSampleCount ε ∧ ((meanSampleCount ε:ℕ):ℝ)⁻¹≤ε/10 := by
  have ht : 0<meanSampleCount ε := Nat.zero_lt_succ _
  have htR : (0:ℝ)<meanSampleCount ε := by exact_mod_cast ht
  have hc := Nat.le_ceil (10/ε)
  have hmore : (Nat.ceil (10/ε):ℝ)≤meanSampleCount ε := by
    simp only [meanSampleCount,Nat.cast_add,Nat.cast_one]
    linarith
  have hb : 10/ε≤meanSampleCount ε := hc.trans hmore
  have hh := (div_le_iff₀ hε).mp hb
  refine ⟨ht,?_⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ htR).2
  nlinarith only [hh]

theorem budgetSampleCount_valid (S R z : ℝ) (hz : z≠0) :
    0<budgetSampleCount S R z ∧
      S≤(budgetSampleCount S R z:ℝ)*z^2 ∧ R≤(budgetSampleCount S R z:ℝ)*z^2 := by
  have hc := Nat.le_ceil (max S R/z^2)
  have hmore : (Nat.ceil (max S R/z^2):ℝ)≤budgetSampleCount S R z := by
    simp only [budgetSampleCount,Nat.cast_add,Nat.cast_one]
    linarith
  have hb := (div_le_iff₀ (sq_pos_of_ne_zero hz)).mp (hc.trans hmore)
  exact ⟨Nat.zero_lt_succ _,(le_max_left S R).trans hb,(le_max_right S R).trans hb⟩

theorem meanSampleCount_upper (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    (meanSampleCount ε:ℝ)≤12/ε := by
  have hc := Nat.ceil_lt_add_one (by positivity : 0≤(10:ℝ)/ε)
  have he : (meanSampleCount ε:ℝ)=(Nat.ceil (10/ε):ℝ)+1 := by simp [meanSampleCount]
  calc
    (meanSampleCount ε:ℝ)≤10/ε+2 := by linarith only [hc,he]
    _≤12/ε := by
      apply (le_div_iff₀ hε).2
      rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hε)]
      nlinarith only [hε1]

theorem budgetSampleCount_upper (S R z : ℝ) (hS : 0≤S) (hR : 0≤R) (hz : z≠0) :
    (budgetSampleCount S R z:ℝ)<(S+R)/z^2+2 := by
  have hc := Nat.ceil_lt_add_one (div_nonneg (le_trans hS (le_max_left S R)) (sq_nonneg z))
  have he : (budgetSampleCount S R z:ℝ)=(Nat.ceil (max S R/z^2):ℝ)+1 := by simp [budgetSampleCount]
  rw [he]
  have hh : max S R≤S+R := max_le (by linarith) (by linarith)
  have hdiv := div_le_div_of_nonneg_right hh (sq_nonneg z)
  linarith

/-- Explicit integer sample count for the second-stage Euclidean sampler. -/
def compressionSampleCount (k B : ℕ) (a ε δ : ℝ) : ℕ :=
  budgetSampleCount
    ((48*(k:ℝ))*Real.log (8*(k:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(meanSampleCount ε*k:ℕ)*Real.log B))
    ((ε/100)/(23+22*a))

/-- Euclidean compression with both integer sample counts prescribed.
There are no sample-size or second-stage cost-preservation premises. -/
theorem euclidean_compression_explicit
    {B K E : Type*} [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : B → E) (w : B → ℝ) (hw : ∀ i,0<w i)
    (original : (K → E) → ℝ) (hnonneg : ∀ s,0≤original s)
    (opt proxy : K → E) (a ε δ : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hstrong : ∀ s,Preserves (original s) (cost b w s) (ε/100))
    (hproxy : Approximate (cost b w) a proxy) :
    let t := meanSampleCount ε
    let m := compressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ
    let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
    eventMass (drawWeight p m) (fun sample=>∃ (α : ℝ) (s : K → E),0≤α ∧
      Approximate (cost (sampledPoints b m sample) (sampledWeights w p m sample)) α s ∧
      ¬∃ out : K → E,out∈witnessFamily b t ∧ original out≤α*(1+ε)*original opt)≤δ := by
  have ht := meanSampleCount_valid ε hε
  have hz : (ε/100)/(23+22*a)≠0 := ne_of_gt (div_pos (by positivity) (by linarith))
  have hm := budgetSampleCount_valid
    ((48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(meanSampleCount ε*Fintype.card K:ℕ)*Real.log (Fintype.card B)))
    ((ε/100)/(23+22*a)) hz
  exact euclidean_compression b w hw original hnonneg opt proxy a ε δ ha hε hε1 hδ hstrong hproxy
    (meanSampleCount ε) ht.1 ht.2 (compressionSampleCount _ _ a ε δ) hm.1 hm.2.1 hm.2.2

end APC
