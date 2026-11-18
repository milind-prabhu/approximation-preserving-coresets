import APC.SmallMean
import APC.Clustering

open scoped BigOperators
noncomputable section
namespace APC

variable {B E : Type*} [Fintype B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tupleMean (b : B → E) (m : ℕ) (f : Fin m → B) : E :=
  (m:ℝ)⁻¹ • ∑ j, b (f j)

def smallMeans (b : B → E) (m : ℕ) : Finset E := by
  classical
  exact Finset.univ.image (tupleMean b m)

theorem mem_smallMeans (b : B → E) (m : ℕ) (f : Fin m → B) :
    tupleMean b m f ∈ smallMeans b m := by
  classical
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩

theorem card_smallMeans (b : B → E) (m : ℕ) :
    (smallMeans b m).card ≤ Fintype.card B ^ m := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin m → B)).card := Finset.card_image_le
    _ = _ := by simp [Fintype.card_fun]

variable {K : Type*} [Fintype K]

def witnessFamily (b : B → E) (m : ℕ) : Finset (K → E) := by
  classical
  exact Finset.univ.image (fun f : K → Fin m → B => fun j => tupleMean b m (f j))

theorem mem_witnessFamily (b : B → E) (m : ℕ) (f : K → Fin m → B) :
    (fun j => tupleMean b m (f j)) ∈ witnessFamily (K := K) b m := by
  classical
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩

/-- Exact exponent includes the 3 in m=ceil(3/ε). -/
theorem card_witnessFamily (b : B → E) (m : ℕ) :
    (witnessFamily (K := K) b m).card ≤ Fintype.card B ^ (m * Fintype.card K) := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (K → Fin m → B)).card := Finset.card_image_le
    _ = _ := by simp [Fintype.card_fun, ← pow_mul]

theorem card_witnessFamily_with_opt [DecidableEq E] (b : B → E) (m : ℕ) (opt : K → E) :
    (insert opt (witnessFamily (K := K) b m)).card ≤ Fintype.card B ^ (m * Fintype.card K) + 1 := by
  classical
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (card_witnessFamily b m) 1)

/-- The final summary's witnesses belong to the family defined by the first
summary. This is what makes conditioning before the second sample sound. -/
theorem witnessFamily_mono {I : Type*} [Fintype I]
    (x : I → E) (b : B → E) (embed : I → B)
    (he : ∀ i, b (embed i) = x i) (m : ℕ) (out : K → E)
    (hout : out ∈ witnessFamily x m) : out ∈ witnessFamily b m := by
  classical
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hout
  apply Finset.mem_image.mpr
  refine ⟨fun j l => embed (f j l), Finset.mem_univ _, ?_⟩
  rw [← hf]
  funext j
  simp [tupleMean, he]

end APC
