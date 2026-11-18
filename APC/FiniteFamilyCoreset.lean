import APC.GlobalSampling
import APC.Transfer

open scoped BigOperators
noncomputable section
namespace APC

theorem preserves_iff_abs (u v ε : ℝ) : Preserves u v ε ↔ |v-u|≤ε*u := by
  unfold Preserves
  rw [abs_le]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor <;> nlinarith only [h₁,h₂]
  · rintro ⟨h₁,h₂⟩
    constructor <;> nlinarith only [h₁,h₂]

/-- A finite-family strong-coreset guarantee from the fully verified
sensitivity sampler. For fixed proxy factor a, the two budgets have
orders k ε^-2 log(k/δ) and ε^-2 log(N/δ), respectively. -/
theorem finite_family_coreset
    {I K Q X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [Fintype Q] [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0<w i)
    (proxy : K → X) (solutions : Q → K → X) (a ε δ : ℝ)
    (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ)
    (hQ : 0<Fintype.card Q)
    (happrox : ∀ q,cost x w proxy≤a*cost x w (solutions q))
    (m : ℕ) (hm : 0<m)
    (hstructSize : (48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ)≤
      (m:ℝ)*(ε/(23+22*a))^2)
    (hresidualSize : (4*(64*a+8*a^2))*Real.log (4*(Fintype.card Q:ℝ)/δ)≤
      (m:ℝ)*(ε/(23+22*a))^2) :
    let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
    eventMass (drawWeight p m) (fun sample=>∃ q,¬Preserves (cost x w (solutions q))
      (cost (sampledPoints x m sample) (sampledWeights w p m sample) (solutions q)) ε)≤δ := by
  let D := 23+22*a
  have hD : 0<D := by dsimp [D];linarith
  have hη : 0<ε/D := div_pos hε hD
  have hη1 : ε/D≤1 := (div_le_iff₀ hD).2 (by dsimp [D];linarith)
  have hb := sensitivity_finite_family x w hw proxy solutions a (ε/D) δ ha hη hη1 hδ hQ
    happrox m hm hstructSize hresidualSize
  let p := sensitivityProbability w (fun i=>pointCost proxy (x i)) (fun i=>nearest proxy (x i))
  have hp : ∀ i,0≤p i := fun i=>(sensitivityProbability_pos w _ _ hw (fun i=>sq_nonneg _) i).le
  apply le_trans (eventMass_mono (drawWeight p m) (drawWeight_nonneg p hp m) _ _ ?_) hb
  intro sample hs
  obtain ⟨q,hq⟩ := hs
  refine ⟨q,?_⟩
  rw [preserves_iff_abs] at hq
  have hradius : (23+22*a)*(ε/D)*cost x w (solutions q)=ε*cost x w (solutions q) := by
    change D*(ε/D)*_= _
    field_simp
  rw [hradius]
  exact lt_of_not_ge hq

end APC
