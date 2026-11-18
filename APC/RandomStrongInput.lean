import APC.EuclideanSize
import APC.DependentKernel

open scoped BigOperators
noncomputable section
namespace APC.RandomStrongInput
attribute [local instance] Classical.propDecidable

/-- Second sampling and lifting outcomes for one supplied first summary. -/
abbrev Outcomes (B K : Type*) [Fintype B] [Fintype K] (a ε δ : ℝ) :=
  Draws B (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ) ×
    LiftOutcome (Fin (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ)) K
      (liftingSampleCount (ε/10)) (liftingRepetitions (Fintype.card K))

section OneSummary
variable {B K E : Type*} [Fintype B] [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Conditional law of the actual compression and randomized lifting. -/
def law (b : B → E) (w : B → ℝ) (proxy : K → E) (a ε δ : ℝ)
    (solve : Draws B (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ) → K → E) :
    Outcomes B K a ε δ → ℝ :=
  let n := randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ
  let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
  kernelWeight (drawWeight p n) (fun sample => liftingTrialsLaw (sampledPoints b n sample)
    (sampledWeights w p n sample) (solve sample) (liftingSampleCount (ε/10))
      (liftingRepetitions (Fintype.card K)))

def output (b : B → E) (w : B → ℝ) (proxy : K → E) (a ε δ : ℝ)
    (solve : Draws B (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ) → K → E)
    (sample : Outcomes B K a ε δ) : K → E :=
  let n := randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ
  let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
  randomLift (sampledPoints b n sample.1) (sampledWeights w p n sample.1) (solve sample.1)
    (liftingSampleCount (ε/10)) (liftingRepetitions (Fintype.card K)) sample.2

theorem law_nonneg [Nonempty B] (b : B → E) (w : B → ℝ) (hw : ∀ i,0<w i)
    (proxy : K → E) (a ε δ : ℝ)
    (solve : Draws B (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ) → K → E) :
    ∀ sample,0≤law b w proxy a ε δ solve sample := by
  let n := randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ
  let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
  have hp : ∀ i,0≤p i := fun i => (sensitivityProbability_pos w _ _ hw (fun i=>sq_nonneg _) i).le
  exact kernelWeight_nonneg _ _ (drawWeight_nonneg p hp n)
    (fun sample=>liftingTrialsLaw_nonneg _ _
      (sampledWeights_nonneg w p (fun i=>(hw i).le) hp n sample) _ _ _)

theorem law_sum [Nonempty B] (b : B → E) (w : B → ℝ) (hw : ∀ i,0<w i)
    (proxy : K → E) (a ε δ : ℝ)
    (solve : Draws B (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card B) a ε δ) → K → E) :
    ∑ sample,law b w proxy a ε δ solve sample=1 := by
  exact kernelWeight_sum _ _
    (drawWeight_sum _ (sensitivityProbability_sum w _ _ hw) _)
    (fun sample=>liftingTrialsLaw_sum _ _ _ _ _)

theorem law_failure [Nonempty B]
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
    eventMass (law b w proxy a ε δ solve)
      (fun sample=>α*(1+ε)*original opt<original (output b w proxy a ε δ solve sample))≤δ+1/3 :=
  randomized_euclidean_compression_explicit b w hw original hnonneg opt proxy a α ε δ
    ha hα hε hε1 hδ hstrong hproxy solve hsolve

end OneSummary

/-- A randomized first stage may have a varying summary index type and
size. Its strong-preservation/size success event is explicit. All later
sampling and lifting probabilities and the final inverse-cubic size bound
are proved, for the returned centers of the combined experiment. -/
theorem randomized_first_stage_size_and_output
    {Ω : Type*} [Fintype Ω] {B : Ω → Type*}
    [∀ ω,Fintype (B ω)] [∀ ω,Nonempty (B ω)]
    {K E : Type*} [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : Ω → ℝ) (hρ : ∀ ω,0≤ρ ω) (hρsum : ∑ ω,ρ ω=1)
    (b : (ω : Ω) → B ω → E) (w : (ω : Ω) → B ω → ℝ) (hw : ∀ ω i,0<w ω i)
    (original : (K → E) → ℝ) (hnonneg : ∀ c,0≤original c) (opt : K → E)
    (proxy : Ω → K → E) (a α ε δ₁ δ₂ C : ℝ) (p q : ℕ)
    (ha : 0<a) (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1)
    (hδ₂ : 0<δ₂) (hδ₂1 : δ₂≤1) (hC : 1≤C)
    (hproxy : ∀ ω,Approximate (cost (b ω) (w ω)) a (proxy ω))
    (solve : (ω : Ω) → Draws (B ω)
      (randomizedCompressionSampleCount (Fintype.card K) (Fintype.card (B ω)) a ε δ₂) → K → E)
    (hsolve : ∀ ω sample,
      let n := randomizedCompressionSampleCount (Fintype.card K) (Fintype.card (B ω)) a ε δ₂
      let d := sensitivityProbability (w ω) (fun i=>pointCost (proxy ω) (b ω i))
        (fun i=>nearest (proxy ω) (b ω i))
      Approximate (cost (sampledPoints (b ω) n sample) (sampledWeights (w ω) d n sample)) α (solve ω sample))
    (hfirst : eventMass ρ (fun ω=>¬((∀ c,Preserves (original c)
      (cost (b ω) (w ω) c) (ε/100)) ∧
      (Fintype.card (B ω):ℝ)≤C*(Fintype.card K:ℝ)^p*(1/ε)^q))≤δ₁) :
    eventMass (dependentKernelWeight ρ (fun ω=>law (b ω) (w ω) (proxy ω) a ε δ₂ (solve ω)))
      (fun sample=>
        α*(1+ε)*original opt<original
          (output (b sample.1) (w sample.1) (proxy sample.1) a ε δ₂ (solve sample.1) sample.2) ∨
        ¬(randomizedCompressionSampleCount (Fintype.card K) (Fintype.card (B sample.1)) a ε δ₂:ℝ)<
          euclideanSizeEnvelope (Fintype.card K) a 32 C p q ε δ₂) ≤ δ₁+δ₂+1/3 := by
  classical
  let good := fun ω => (∀ c,Preserves (original c) (cost (b ω) (w ω) c) (ε/100)) ∧
    (Fintype.card (B ω):ℝ)≤C*(Fintype.card K:ℝ)^p*(1/ε)^q
  have hb := dependentKernel_event_bound ρ
    (fun ω=>law (b ω) (w ω) (proxy ω) a ε δ₂ (solve ω)) hρ hρsum
    (fun ω=>law_nonneg (b ω) (w ω) (hw ω) (proxy ω) a ε δ₂ (solve ω))
    (fun ω=>law_sum (b ω) (w ω) (hw ω) (proxy ω) a ε δ₂ (solve ω)) good
    (fun ω z=>α*(1+ε)*original opt<original (output (b ω) (w ω) (proxy ω) a ε δ₂ (solve ω) z) ∨
      ¬(randomizedCompressionSampleCount (Fintype.card K) (Fintype.card (B ω)) a ε δ₂:ℝ)<
        euclideanSizeEnvelope (Fintype.card K) a 32 C p q ε δ₂)
    δ₁ (δ₂+1/3) (by positivity) hfirst (by
      intro ω hg
      have hs := randomizedCompressionSampleCount_polynomial_bound
        (Fintype.card K) (Fintype.card (B ω)) a C p q ε δ₂
        Fintype.card_pos Fintype.card_pos ha hC hε hε1 hδ₂ hδ₂1 hg.2
      simpa only [hs,not_true_eq_false,or_false] using law_failure (b ω) (w ω) (hw ω)
        original hnonneg opt (proxy ω) a α ε δ₂ ha hα hε hε1 hδ₂ hg.1 (hproxy ω) (solve ω) (hsolve ω))
  simpa only [add_assoc] using hb

end APC.RandomStrongInput
