import APC.RandomizedCompression
import APC.SampleCounts

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- The coreset count uses the witness family of the actual randomized
lifting means, whose size is ceil(30/ε)+1. -/
def randomizedCompressionSampleCount (k B : ℕ) (a ε δ : ℝ) : ℕ :=
  budgetSampleCount
    ((48*(k:ℝ))*Real.log (8*(k:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(liftingSampleCount (ε/10)*k:ℕ)*Real.log B))
    ((ε/100)/(23+22*a))

instance randomizedCompressionSampleCount_neZero (k B : ℕ) (a ε δ : ℝ) :
    NeZero (randomizedCompressionSampleCount k B a ε δ) := ⟨Nat.succ_ne_zero _⟩

/-- Fully specified sampling and randomized lifting from a supplied
strong coreset. The failure bound concerns the actual returned solution.
The solver may depend on the sampled coreset. -/
theorem randomized_euclidean_compression_explicit
    {B K E : Type*} [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : B → E) (w : B → ℝ) (hw : ∀ i,0<w i)
    (original : (K → E) → ℝ) (hnonneg : ∀ c,0≤original c)
    (opt proxy : K → E) (a α ε δ : ℝ)
    (ha : 0<a) (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hstrong : ∀ c,Preserves (original c) (cost b w c) (ε/100))
    (hproxy : Approximate (cost b w) a proxy)
    (solve : Draws B (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ) → K → E)
    (hsolve : ∀ sample,
      let n := randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ
      let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
      Approximate (cost (sampledPoints b n sample) (sampledWeights w p n sample)) α (solve sample)) :
    let n := randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ
    let m := liftingSampleCount (ε/10)
    let r := liftingRepetitions (Fintype.card K)
    let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
    let liftLaw := fun sample=>liftingTrialsLaw (sampledPoints b n sample)
      (sampledWeights w p n sample) (solve sample) m r
    eventMass (kernelWeight (drawWeight p n) liftLaw)
      (fun sample=>α*(1+ε)*original opt<original
        (randomLift (sampledPoints b n sample.1) (sampledWeights w p n sample.1)
          (solve sample.1) m r sample.2))≤δ+1/3 := by
  have hm := liftingSampleCount_valid (ε/10) (by positivity)
  have hz : (ε/100)/(23+22*a)≠0 := ne_of_gt (div_pos (by positivity) (by linarith))
  have hn := budgetSampleCount_valid
    ((48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(liftingSampleCount (ε/10)*Fintype.card K:ℕ)*Real.log (Fintype.card B)))
    ((ε/100)/(23+22*a)) hz
  have hb := randomized_euclidean_compression b w hw original hnonneg opt proxy a α ε δ
    ha hα hε hε1 hδ hstrong hproxy
    (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ)
    (liftingSampleCount (ε/10)) (liftingRepetitions (Fintype.card K)) hm.1 hm.2 solve hsolve hn.2.1 hn.2.2
  exact hb.trans (add_le_add_left (liftingRepetitions_bound _) δ)

end APC
