import APC.BestMean
import APC.ProductProbability

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable
variable {I K E : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev LiftOutcome (I K : Type*) (m r : ℕ) := K → MeanTrials I m r

def liftingWeights (x : I → E) (w : I → ℝ) (s : K → E) (j : K) : I → ℝ :=
  clusterWeight w (fun i=>nearest s (x i)) j

def liftingTrialsLaw (x : I → E) (w : I → ℝ) (s : K → E) (m r : ℕ) :
    LiftOutcome I K m r → ℝ :=
  productWeight (fun j=>meanTrialsWeight (liftingWeights x w s j) m r)

def randomLift (x : I → E) (w : I → ℝ) (s : K → E) (m r : ℕ) [NeZero r]
    (sample : LiftOutcome I K m r) : K → E :=
  fun j=>bestMean x (liftingWeights x w s j) m r (sample j)

theorem liftingTrialsLaw_sum (x : I → E) (w : I → ℝ) (s : K → E) (m r : ℕ) :
    ∑ sample,liftingTrialsLaw x w s m r sample=1 :=
  productWeight_sum _ (fun j=>meanTrialsWeight_sum (liftingWeights x w s j) m r)

theorem liftingTrialsLaw_nonneg (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (s : K → E) (m r : ℕ) (sample : LiftOutcome I K m r) :
    0≤liftingTrialsLaw x w s m r sample :=
  productWeight_nonneg _ (fun j trials=>meanTrialsWeight_nonneg _
    (clusterWeight_nonneg w _ hw j) m r trials) sample

/-- Every output is in the finite m-point-mean witness family, including
outcomes with probability zero and zero-mass clusters. -/
theorem randomLift_mem_witness (x : I → E) (w : I → ℝ) (s : K → E)
    (m r : ℕ) [NeZero r] (sample : LiftOutcome I K m r) :
    randomLift x w s m r sample∈witnessFamily x m := by
  have he : randomLift x w s m r sample=
      (fun j=>tupleMean x m (drawIndex m (bestTrial x (liftingWeights x w s j) m r (sample j)))) := by
    funext j
    exact drawMean_eq_tupleMean x m _
  rw [he]
  exact mem_witnessFamily x m _

theorem randomLift_cost_of_cluster_good (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (s : K → E) (m r : ℕ) [NeZero r] (ε : ℝ) (hε : 0≤ε)
    (sample : LiftOutcome I K m r)
    (hgood : ∀ j,oneCost x (liftingWeights x w s j) (randomLift x w s m r sample j)≤
      (1+ε)*oneCost x (liftingWeights x w s j) (mean x (liftingWeights x w s j))) :
    cost x w (randomLift x w s m r sample)≤(1+ε)*cost x w s := by
  let a : I → K := fun i=>nearest s (x i)
  have hmin : ∀ j,oneCost x (liftingWeights x w s j) (mean x (liftingWeights x w s j))≤
      oneCost x (liftingWeights x w s j) (s j) := by
    intro j
    have hv := clusterWeight_nonneg w a hw j
    by_cases hz : mass (liftingWeights x w s j)=0
    · simp only [oneCost_zero_mass x (liftingWeights x w s j) hv hz]
      exact le_rfl
    · exact mean_minimizes x _ hv hz (s j)
  calc
    _≤∑ i,w i*dist (x i) (randomLift x w s m r sample (a i))^2 :=
      cost_le_assigned x w hw _ a
    _=∑ j,oneCost x (liftingWeights x w s j) (randomLift x w s m r sample j) :=
      (cluster_cost_sum x w a _).symm
    _≤∑ j,(1+ε)*oneCost x (liftingWeights x w s j) (mean x (liftingWeights x w s j)) :=
      Finset.sum_le_sum (fun j _=>hgood j)
    _≤∑ j,(1+ε)*oneCost x (liftingWeights x w s j) (s j) :=
      Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hmin j) (by linarith))
    _=(1+ε)*cost x w s := by
      rw [← Finset.mul_sum]
      change (1+ε)*(∑ j,oneCost x (clusterWeight w a j) (s j))=(1+ε)*cost x w s
      rw [cluster_cost_sum]
      rfl

/-- Lemma 3.4 for the joint output of Algorithm 3. Independence is encoded
by the product law, and the best sampled trial is the actual returned
center. The bound is k*(1/3)^r, before choosing r. -/
theorem randomized_lifting_failure (x : I → E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (s : K → E) (m r : ℕ) [NeZero r] (hm : 0<m)
    (ε : ℝ) (hε : 0≤ε) (hmε : 3≤(m:ℝ)*ε) :
    eventMass (liftingTrialsLaw x w s m r)
      (fun sample=>(1+ε)*cost x w s<cost x w (randomLift x w s m r sample))≤
      (Fintype.card K:ℝ)*(1/3:ℝ)^r := by
  let bad := fun j (sample : LiftOutcome I K m r)=>
    (1+ε)*oneCost x (liftingWeights x w s j) (mean x (liftingWeights x w s j))<
      oneCost x (liftingWeights x w s j) (randomLift x w s m r sample j)
  have hpoint : ∀ j,eventMass (liftingTrialsLaw x w s m r) (bad j)≤(1/3:ℝ)^r := by
    intro j
    have he : eventMass (liftingTrialsLaw x w s m r) (bad j)=
        eventMass (meanTrialsWeight (liftingWeights x w s j) m r)
          (fun trials=>(1+ε)*oneCost x (liftingWeights x w s j) (mean x (liftingWeights x w s j))<
            oneCost x (liftingWeights x w s j) (bestMean x (liftingWeights x w s j) m r trials)) :=
      productWeight_marginal (fun k=>meanTrialsWeight (liftingWeights x w s k) m r)
        (fun k=>meanTrialsWeight_sum (liftingWeights x w s k) m r) j
        (fun trials=>(1+ε)*oneCost x (liftingWeights x w s j) (mean x (liftingWeights x w s j))<
          oneCost x (liftingWeights x w s j) (bestMean x (liftingWeights x w s j) m r trials))
    rw [he]
    exact bestMean_failure x _ (clusterWeight_nonneg w _ hw j) m r hm ε hmε
  have hc : ∀ sample,(1+ε)*cost x w s<cost x w (randomLift x w s m r sample)→∃ j,bad j sample := by
    intro sample hs
    by_contra hn
    have hb := randomLift_cost_of_cluster_good x w hw s m r ε hε sample
      (fun j=>le_of_not_gt (fun hj=>hn ⟨j,hj⟩))
    exact not_lt_of_ge hb hs
  have hp := liftingTrialsLaw_nonneg x w hw s m r
  calc
    _≤eventMass (liftingTrialsLaw x w s m r) (fun sample=>∃ j,bad j sample) :=
      eventMass_mono _ hp _ _ hc
    _≤∑ j,eventMass (liftingTrialsLaw x w s m r) (bad j) := finite_union_bound _ hp bad
    _≤∑ _j : K,(1/3:ℝ)^r := Finset.sum_le_sum (fun j _=>hpoint j)
    _=(Fintype.card K:ℝ)*(1/3:ℝ)^r := by simp

end APC
