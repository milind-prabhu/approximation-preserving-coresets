import APC.MetricEnumeration
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators
noncomputable section
namespace APC.MetricIteration
local instance (T : Type*) : DecidableEq T := Classical.decEq T

section
variable {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [PseudoMetricSpace X]

def centerSubsets (I : Type*) [Fintype I] (k : ℕ) : Finset (Finset I) :=
  (Finset.univ : Finset I).powersetCard k

theorem centerSubsets_nonempty (hkm : Fintype.card K≤Fintype.card I) :
    (centerSubsets I (Fintype.card K)).Nonempty := by
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq
    (show Fintype.card K≤(Finset.univ : Finset I).card by simpa using hkm)
  exact ⟨S,Finset.mem_powersetCard.mpr ⟨hS,hcard⟩⟩

def subsetEquiv (S : Finset I) (hS : S.card=Fintype.card K) : K ≃ S :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe S,hS])

/-- A total tuple representation, with arbitrary values off the search
family. Every evaluated candidate has exactly the required cardinality. -/
def subsetTuple (S : Finset I) : K → I :=
  if hS : S.card=Fintype.card K then fun j=>(subsetEquiv S hS j).val
  else fun _=>Classical.arbitrary I

theorem subsetTuple_mem (S : Finset I) (hS : S.card=Fintype.card K) (j : K) :
    subsetTuple (K:=K) S j∈S := by
  simp only [subsetTuple,dif_pos hS]
  exact (subsetEquiv S hS j).property

theorem subsetTuple_hits (S : Finset I) (hS : S.card=Fintype.card K) (i : I) (hi : i∈S) :
    ∃ j : K,subsetTuple (K:=K) S j=i := by
  obtain ⟨j,hj⟩ := (subsetEquiv (K:=K) S hS).surjective ⟨i,hi⟩
  refine ⟨j,?_⟩
  simp only [subsetTuple,dif_pos hS]
  exact congrArg Subtype.val hj

def subsetSearch (c : Cloud I X) (hkm : Fintype.card K≤Fintype.card I) : Finset I :=
  Classical.choose (Finset.exists_min_image (centerSubsets I (Fintype.card K))
    (fun S=>cost c.points c.weights (fun j : K=>c.points (subsetTuple S j)))
    (centerSubsets_nonempty hkm))

def subsetSearchCenters (c : Cloud I X) (hkm : Fintype.card K≤Fintype.card I) : K → X :=
  fun j=>c.points (subsetTuple (subsetSearch (K:=K) c hkm) j)

theorem subsetSearch_spec (c : Cloud I X) (hkm : Fintype.card K≤Fintype.card I) :
    subsetSearch (K:=K) c hkm∈centerSubsets I (Fintype.card K) ∧
      ∀ S∈centerSubsets I (Fintype.card K),
        cost c.points c.weights (subsetSearchCenters c hkm)≤
          cost c.points c.weights (fun j : K=>c.points (subsetTuple S j)) :=
  Classical.choose_spec (Finset.exists_min_image (centerSubsets I (Fintype.card K))
    (fun S=>cost c.points c.weights (fun j : K=>c.points (subsetTuple S j)))
    (centerSubsets_nonempty hkm))

/-- Adding available centers cannot increase nearest-center cost. -/
theorem cost_le_of_centers_cover (c : Cloud I X) (hw : ∀ i,0≤c.weights i)
    (s t : K → X) (hcover : ∀ j,∃ l,t l=s j) :
    cost c.points c.weights t≤cost c.points c.weights s := by
  unfold cost
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨l,hl⟩ := hcover (nearest s (c.points i))
  have hb := pointCost_le t (c.points i) l
  rw [hl] at hb
  exact mul_le_mul_of_nonneg_left hb (hw i)

/-- Every possibly repeated tuple can be covered by a size-k subset.
Thus subset enumeration loses no solution quality compared with tuples. -/
theorem subsetSearch_le_tuple (c : Cloud I X) (hw : ∀ i,0≤c.weights i)
    (hkm : Fintype.card K≤Fintype.card I) (f : K → I) :
    cost c.points c.weights (subsetSearchCenters c hkm)≤
      cost c.points c.weights (fun j=>c.points (f j)) := by
  let A := Finset.univ.image f
  have hA : A.card≤Fintype.card K := Finset.card_image_le.trans (by simp)
  obtain ⟨S,hAS,hS,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ A) hA (show Fintype.card K≤(Finset.univ : Finset I).card by simpa using hkm)
  have hmem : S∈centerSubsets I (Fintype.card K) := Finset.mem_powersetCard.mpr ⟨hS,hcard⟩
  refine ((subsetSearch_spec c hkm).2 S hmem).trans ?_
  apply cost_le_of_centers_cover c hw
  intro j
  have hfj : f j∈S := hAS (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩)
  obtain ⟨l,hl⟩ := subsetTuple_hits S hcard (f j) hfj
  exact ⟨l,congrArg c.points hl⟩

theorem subsetSearch_le_four (c : Cloud I X) (hw : ∀ i,0≤c.weights i)
    (hkm : Fintype.card K≤Fintype.card I) (s : K → X) :
    cost c.points c.weights (subsetSearchCenters c hkm)≤4*cost c.points c.weights s :=
  (subsetSearch_le_tuple c hw hkm (fun j=>nearest c.points (s j))).trans
    (metric_rounding c.points c.weights hw s (rounded c s) (fun j i=>nearest_le c.points (s j) i))

theorem subsetSearch_supported (c : Cloud I X) (hkm : Fintype.card K≤Fintype.card I) :
    ∀ j,subsetSearchCenters (K:=K) c hkm j∈Set.range c.points := fun j=>⟨_,rfl⟩

/-- The search has exactly binomial(m,k) candidates even when the sampled
cloud has repeated locations; using distinct locations can reduce it further. -/
theorem subsetSearch_candidate_count :
    (centerSubsets I (Fintype.card K)).card=(Fintype.card I).choose (Fintype.card K) := by
  simp [centerSubsets]

end
end APC.MetricIteration
