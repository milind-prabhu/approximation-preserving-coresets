import APC.Lifting
import APC.MetricEnumeration

open scoped BigOperators
noncomputable section
namespace APC
local instance (T : Type*) : DecidableEq T := Classical.decEq T
variable {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def assignmentCenters (x : I → E) (w : I → ℝ) (a : I → K) : K → E :=
  fun j=>mean x (clusterWeight w a j)

/-- Exact centroids of the nearest-center clusters improve every tuple,
including empty clusters, so an optimum exists without compactness. -/
theorem assignmentCenters_improve (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (s : K → E) :
    cost x w (assignmentCenters x w (fun i=>nearest s (x i)))≤cost x w s := by
  let a := fun i=>nearest s (x i)
  have hc : ∀ j,oneCost x (clusterWeight w a j) (assignmentCenters x w a j)≤
      oneCost x (clusterWeight w a j) (s j) := by
    intro j
    have hv := clusterWeight_nonneg w a hw j
    by_cases hz : mass (clusterWeight w a j)=0
    · rw [oneCost_zero_mass x _ hv hz,oneCost_zero_mass x _ hv hz]
    · exact mean_minimizes x _ hv hz (s j)
  calc
    _≤∑ i,w i*dist (x i) (assignmentCenters x w a (a i))^2 := cost_le_assigned x w hw _ a
    _=∑ j,oneCost x (clusterWeight w a j) (assignmentCenters x w a j) := (cluster_cost_sum _ _ _ _).symm
    _≤∑ j,oneCost x (clusterWeight w a j) (s j) := Finset.sum_le_sum (fun j _=>hc j)
    _=cost x w s := by rw [cluster_cost_sum];rfl

def euclideanOptimal (x : I → E) (w : I → ℝ) : K → E :=
  assignmentCenters x w (Classical.choose (Finset.exists_min_image Finset.univ
    (fun a : I → K=>cost x w (assignmentCenters x w a)) Finset.univ_nonempty))

theorem euclideanOptimal_spec (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i) :
    Approximate (cost x w) 1 (euclideanOptimal (K:=K) x w) := by
  intro s
  have hh := (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun a : I → K=>cost x w (assignmentCenters x w a)) Finset.univ_nonempty)).2
      (fun i=>nearest s (x i)) (Finset.mem_univ _)
  exact (by simpa only [one_mul] using hh.trans (assignmentCenters_improve x w hw s))

end APC
