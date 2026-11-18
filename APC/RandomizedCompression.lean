import APC.RandomizedTransfer
import APC.FiniteFamilyCoreset
import APC.WitnessBudget

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- The complete finite experiment: sensitivity-sample a supplied strong
input, solve the summary, then independently sample candidate cluster
means and return the best means. The second law depends on the first
outcome and its computed solution. This theorem bounds failure of the
actual returned center tuple, not merely existence of a good tuple.
It does not assert a machine/runtime cost model. -/
theorem randomized_euclidean_compression
    {B K E : Type*} [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : B → E) (w : B → ℝ) (hw : ∀ i,0<w i)
    (original : (K → E) → ℝ) (hnonneg : ∀ c,0≤original c)
    (opt proxy : K → E) (a α ε δ : ℝ)
    (ha : 0<a) (hα : 0≤α) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hstrong : ∀ c,Preserves (original c) (cost b w c) (ε/100))
    (hproxy : Approximate (cost b w) a proxy)
    (n : ℕ) [NeZero n] (m r : ℕ) [NeZero r]
    (hm : 0<m) (hmε : 3≤(m:ℝ)*(ε/10))
    (solve : Draws B n → K → E)
    (hsolve : ∀ sample,
      let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
      Approximate (cost (sampledPoints b n sample) (sampledWeights w p n sample)) α (solve sample))
    (hstructSize : (48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ)≤
      (n:ℝ)*((ε/100)/(23+22*a))^2)
    (hresidualSize : (4*(64*a+8*a^2))*(Real.log (8/δ)+
      (m*Fintype.card K:ℕ)*Real.log (Fintype.card B))≤
      (n:ℝ)*((ε/100)/(23+22*a))^2) :
    let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
    let liftLaw := fun sample=>liftingTrialsLaw (sampledPoints b n sample)
      (sampledWeights w p n sample) (solve sample) m r
    eventMass (kernelWeight (drawWeight p n) liftLaw)
      (fun sample=>α*(1+ε)*original opt<original
        (randomLift (sampledPoints b n sample.1) (sampledWeights w p n sample.1)
          (solve sample.1) m r sample.2))≤δ+(Fintype.card K:ℝ)*(1/3:ℝ)^r := by
  classical
  let F : Finset (K → E) := insert opt (witnessFamily b m)
  let Query := {c : K → E // c∈F}
  have hcard : Fintype.card Query=F.card := Fintype.card_coe F
  have hN : 0<F.card := Finset.card_pos.mpr ⟨opt,Finset.mem_insert_self _ _⟩
  have hcount : F.card≤Fintype.card B^(m*Fintype.card K)+1 := card_witnessFamily_with_opt b m opt
  have hlog := log_solution_count F.card (Fintype.card B) (m*Fintype.card K) hN Fintype.card_pos hcount (δ/2) (by positivity)
  have hbudget : (4*(64*a+8*a^2))*Real.log (4*(Fintype.card Query:ℝ)/δ)≤
      (n:ℝ)*((ε/100)/(23+22*a))^2 := by
    rw [hcard]
    have he₁ : 2*(F.card:ℝ)/(δ/2)=4*(F.card:ℝ)/δ := by ring
    have he₂ : (4:ℝ)/(δ/2)=8/δ := by ring
    rw [he₁,he₂] at hlog
    exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hresidualSize
  have hsample := finite_family_coreset b w hw proxy (fun q : Query=>q.val) a (ε/100) δ ha
    (by positivity) (by linarith) hδ (by rw [hcard];exact hN) (fun q=>hproxy q.val)
    n (Nat.pos_of_ne_zero (NeZero.ne n)) hstructSize hbudget
  let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
  have hp : ∀ i,0≤p i := fun i=>(sensitivityProbability_pos w _ _ hw (fun i=>sq_nonneg _) i).le
  let good := fun sample : Draws B n=>¬∃ q : Query,¬Preserves (cost b w q.val)
    (cost (sampledPoints b n sample) (sampledWeights w p n sample) q.val) (ε/100)
  have hfirst : eventMass (drawWeight p n) (fun sample=>¬good sample)≤δ := by
    apply le_trans (eventMass_mono _ (drawWeight_nonneg p hp n) _ _ ?_) hsample
    intro sample hs
    exact of_not_not hs
  let liftLaw := fun sample : Draws B n=>liftingTrialsLaw (sampledPoints b n sample)
    (sampledWeights w p n sample) (solve sample) m r
  let bad := fun (sample : Draws B n) (trials : LiftOutcome (Fin n) K m r)=>
    α*(1+ε)*original opt<original
      (randomLift (sampledPoints b n sample) (sampledWeights w p n sample) (solve sample) m r trials)
  have hwout : ∀ sample i,0≤sampledWeights w p n sample i :=
    fun sample=>sampledWeights_nonneg w p (fun i=>(hw i).le) hp n sample
  have hsecond : ∀ sample,good sample→eventMass (liftLaw sample) (bad sample)≤
      (Fintype.card K:ℝ)*(1/3:ℝ)^r := by
    intro sample hg
    have herr : 2*(ε/100)+(ε/100)^2≤ε/10 := by
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
    have hc : ∀ c∈F,Preserves (original c)
        (cost (sampledPoints b n sample) (sampledWeights w p n sample) c) (ε/10) := by
      intro c hmem
      have hpres : Preserves (cost b w c)
          (cost (sampledPoints b n sample) (sampledWeights w p n sample) c) (ε/100) :=
        of_not_not (fun hn=>hg ⟨⟨c,hmem⟩,hn⟩)
      exact preserves_mono (hnonneg c) herr
        (preserves_compose (hnonneg c) (by positivity) (by linarith) (hstrong c) hpres)
    have hlocal : ∀ c∈witnessFamily (K:=K) (sampledPoints b n sample) m,Preserves (original c)
        (cost (sampledPoints b n sample) (sampledWeights w p n sample) c) (ε/10) := by
      intro c hmem
      exact hc c (Finset.mem_insert_of_mem (witnessFamily_mono (sampledPoints b n sample) b
        (drawIndex n sample) (fun _=>rfl) m c hmem))
    exact randomized_apc_failure (sampledPoints b n sample) (sampledWeights w p n sample)
      (hwout sample) original opt (solve sample) α ε hα hε hε1 (hnonneg opt) (hsolve sample)
      m r hm hmε hlocal (hc opt (Finset.mem_insert_self _ _))
  exact kernel_event_bound (drawWeight p n) liftLaw (drawWeight_nonneg p hp n)
    (drawWeight_sum p (sensitivityProbability_sum w _ _ hw) n)
    (fun sample=>liftingTrialsLaw_nonneg _ _ (hwout sample) (solve sample) m r)
    (fun sample=>liftingTrialsLaw_sum _ _ (solve sample) m r)
    good bad δ ((Fintype.card K:ℝ)*(1/3:ℝ)^r) (by positivity) hfirst hsecond

end APC
