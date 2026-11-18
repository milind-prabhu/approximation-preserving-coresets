import APC.Sampler

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

def fiberWeight {I K : Type*} (w : I → ℝ) (a : I → K) (j : K) (i : I) : ℝ := by
  classical
  exact if a i=j then w i else 0

def groupMass {I K : Type*} [Fintype I] (w : I → ℝ) (a : I → K) (j : K) : ℝ :=
  ∑ i,fiberWeight w a j i

theorem fiberWeight_nonneg {I K : Type*} (w : I → ℝ) (a : I → K)
    (hw : ∀ i,0≤w i) (j : K) : ∀ i,0≤fiberWeight w a j i := by
  classical
  intro i
  simp only [fiberWeight]
  split_ifs <;> simp_all

theorem groupMass_nonneg {I K : Type*} [Fintype I] (w : I → ℝ) (a : I → K)
    (hw : ∀ i,0≤w i) (j : K) : 0≤groupMass w a j :=
  Finset.sum_nonneg (fun i _=>fiberWeight_nonneg w a hw j i)

theorem own_le_groupMass {I K : Type*} [Fintype I] (w : I → ℝ) (a : I → K)
    (hw : ∀ i,0≤w i) (i : I) : w i≤groupMass w a (a i) := by
  classical
  have h := Finset.single_le_sum (fun j _=>fiberWeight_nonneg w a hw (a i) j) (Finset.mem_univ i)
  simpa only [fiberWeight,if_pos rfl] using h

theorem group_sum {I K : Type*} [Fintype I] [Fintype K]
    (a : I → K) (f : K → I → ℝ) :
    (∑ j,∑ i,if a i=j then f j i else 0)=∑ i,f (a i) i := by
  classical
  rw [Finset.sum_comm]
  simp

theorem groupMass_total {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (a : I → K) : ∑ j,groupMass w a j=mass w := by
  classical
  exact group_sum a (fun _ i=>w i)

theorem groupMass_zero_terms {I K : Type*} [Fintype I]
    (w : I → ℝ) (a : I → K) (hw : ∀ i,0≤w i) (j : K)
    (hz : groupMass w a j=0) : ∀ i,fiberWeight w a j i=0 := by
  intro i
  have hle : fiberWeight w a j i≤groupMass w a j :=
    Finset.single_le_sum (fun l _=>fiberWeight_nonneg w a hw j l) (Finset.mem_univ i)
  exact le_antisymm (hz ▸ hle) (fiberWeight_nonneg w a hw j i)

theorem groupMass_mul_zero {I K : Type*} [Fintype I]
    (w c : I → ℝ) (a : I → K) (hw : ∀ i,0≤w i) (j : K)
    (hz : groupMass w a j=0) : groupMass (fun i=>w i*c i) a j=0 := by
  classical
  have ht := groupMass_zero_terms w a hw j hz
  unfold groupMass
  apply Finset.sum_eq_zero
  intro i _
  have he : fiberWeight (fun i=>w i*c i) a j i=fiberWeight w a j i*c i := by
    simp [fiberWeight,ite_mul]
  rw [he,ht i,zero_mul]

theorem group_div_sum {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (a : I → K) (d : K → ℝ) :
    (∑ i,w i/d (a i))=∑ j,groupMass w a j/d j := by
  classical
  simp only [groupMass,fiberWeight,Finset.sum_div,ite_div,zero_div]
  exact (group_sum a (fun j i=>w i/d j)).symm

theorem group_mul_sum {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (a : I → K) (d : K → ℝ) :
    (∑ i,w i*d (a i))=∑ j,groupMass w a j*d j := by
  classical
  simp only [groupMass,fiberWeight,Finset.sum_mul,ite_mul,zero_mul]
  exact (group_sum a (fun j i=>w i*d j)).symm

end APC
