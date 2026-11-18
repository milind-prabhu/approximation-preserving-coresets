import APC.FiniteFamilyCoreset
import APC.TwoStage
import APC.WitnessBudget

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

/-- Probabilistic Euclidean APC compression of a supplied strong coreset.
All second-stage sampling and lifting guarantees are proved. The supplied
strong-coreset guarantee is an explicit premise, corresponding to the
paper's separate Theorem 2.1 primitive. -/
theorem euclidean_compression
    {B K E : Type*} [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : B → E) (w : B → ℝ) (hw : ∀ i,0<w i)
    (original : (K → E) → ℝ) (hnonneg : ∀ s,0≤original s)
    (opt proxy : K → E) (a ε δ : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hstrong : ∀ s,Preserves (original s) (cost b w s) (ε/100))
    (hproxy : Approximate (cost b w) a proxy)
    (t : ℕ) (ht : 0<t) (htε : (t:ℝ)⁻¹≤ε/10)
    (m : ℕ) (hm : 0<m)
    (hstructSize : (48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ)≤
      (m:ℝ)*((ε/100)/(23+22*a))^2)
    (hresidualSize : (4*(64*a+8*a^2))*(Real.log (8/δ)+
      (t*Fintype.card K:ℕ)*Real.log (Fintype.card B))≤
      (m:ℝ)*((ε/100)/(23+22*a))^2) :
    let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
    eventMass (drawWeight p m) (fun sample=>∃ (α : ℝ) (s : K → E),0≤α ∧
      Approximate (cost (sampledPoints b m sample) (sampledWeights w p m sample)) α s ∧
      ¬∃ out : K → E,out∈witnessFamily b t ∧ original out≤α*(1+ε)*original opt)≤δ := by
  classical
  let F : Finset (K → E) := insert opt (witnessFamily b t)
  let Query := {s : K → E // s∈F}
  have hcard : Fintype.card Query=F.card := Fintype.card_coe F
  have hN : 0<F.card := Finset.card_pos.mpr ⟨opt,Finset.mem_insert_self _ _⟩
  have hB : 0<Fintype.card B := Fintype.card_pos
  have hNQ : 0<Fintype.card Query := by rw [hcard];exact hN
  have hcount : F.card≤Fintype.card B^(t*Fintype.card K)+1 := card_witnessFamily_with_opt b t opt
  have hlog := log_solution_count F.card (Fintype.card B) (t*Fintype.card K) hN hB hcount (δ/2) (by positivity)
  have hbudget : (4*(64*a+8*a^2))*Real.log (4*(Fintype.card Query:ℝ)/δ)≤
      (m:ℝ)*((ε/100)/(23+22*a))^2 := by
    rw [hcard]
    have harg₁ : 2*(F.card:ℝ)/(δ/2)=4*(F.card:ℝ)/δ := by ring
    have harg₂ : (4:ℝ)/(δ/2)=8/δ := by ring
    rw [harg₁,harg₂] at hlog
    exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hresidualSize
  have hb := finite_family_coreset b w hw proxy (fun q : Query=>q.val) a (ε/100) δ ha
    (by positivity) (by linarith) hδ hNQ (fun q=>hproxy q.val) m hm hstructSize hbudget
  let p := sensitivityProbability w (fun i=>pointCost proxy (b i)) (fun i=>nearest proxy (b i))
  have hp : ∀ i,0≤p i := fun i=>(sensitivityProbability_pos w _ _ hw (fun i=>sq_nonneg _) i).le
  apply le_trans (eventMass_mono (drawWeight p m) (drawWeight_nonneg p hp m) _ _ ?_) hb
  intro sample hs
  obtain ⟨α,s,hα,happrox,hno⟩ := hs
  by_contra hgood
  have hsecond : ∀ c∈witnessFamily (K:=K) b t,
      Preserves (cost b w c) (cost (sampledPoints b m sample) (sampledWeights w p m sample) c) (ε/100) := by
    intro c hc
    exact of_not_not (fun hh=>hgood ⟨⟨c,Finset.mem_insert_of_mem hc⟩,hh⟩)
  have hopt : Preserves (cost b w opt)
      (cost (sampledPoints b m sample) (sampledWeights w p m sample) opt) (ε/100) :=
    of_not_not (fun hh=>hgood ⟨⟨opt,Finset.mem_insert_self _ _⟩,hh⟩)
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hout := euclidean_two_stage (sampledPoints b m sample) (sampledWeights w p m sample)
    (sampledWeights_nonneg w p (fun i=>(hw i).le) hp m sample) b (drawIndex m sample) (fun _=>rfl)
    original (cost b w) hnonneg opt s α ε hα hε hε1 happrox t ht htε hstrong hsecond hopt
  exact hno hout

end APC
