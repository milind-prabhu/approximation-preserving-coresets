import APC.Guarantee
import APC.EuclideanIteration
import APC.EuclideanOptimum
import APC.MetricSize
import APC.BinomialBudget
import APC.RandomizedTransfer

open scoped BigOperators
noncomputable section
namespace APC.EuclideanIteration
open MetricIteration (Cloud size outcomes)

section
variable {K E : Type*} [Fintype K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- This fixed lift uses only the final summary and the input solution. -/
def SummaryAPC {I : Type*} [Fintype I] [Nonempty I] {N : ℕ}
    (initial : Cloud (Fin N) E) (c : Cloud I E) (hwc : ∀ i,0≤c.weights i)
    (ε : ℝ) (t : ℕ) (ht : 0<t) : Prop :=
  APCWithLift (cost (K:=K) initial.points initial.weights) (cost (K:=K) c.points c.weights) (1+ε)
    (geometricLift (K:=K) c.points c.weights hwc t ht)

theorem liftingWitnessCount_valid (ε : ℝ) (hε : 0<ε) :
    0<liftingSampleCount (ε/10) ∧ ((liftingSampleCount (ε/10):ℕ):ℝ)⁻¹≤ε/10 := by
  have hm := liftingSampleCount_valid (ε/10) (by positivity)
  refine ⟨hm.1,?_⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm.1)).2
  nlinarith only [hm.2]

variable {N : ℕ} [NeZero N] {a : ℝ} {e δ : ℕ → ℝ} {t : ℕ}

theorem final_witness_preservation (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=E) N a e δ t)
    (opt : K → E) (he : ∀ i,0≤e i) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (h : Adaptive.History (outcomes N (t*Fintype.card K) a e δ) n)
    (hh : Adaptive.historyGood (good initial proxy opt) n h) :
    ∀ u,u∈witnessFamily (cloud N a e δ t initial proxy n h).points t ∨ u=opt →
      Preserves (cost initial.points initial.weights u)
        (cost (cloud N a e δ t initial proxy n h).points
          (cloud N a e δ t initial proxy n h).weights u) (ε/10) := by
  have hp := chain_preserves initial hw proxy opt he n (by linarith) h hh
  intro u hu
  exact preserves_mono (cost_nonneg _ _ (fun i=>(hw i).le) u) (by linarith) (hp u hu)

theorem summary_apc_of_good (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=E) N a e δ t)
    (opt : K → E) (hoptimal : Approximate (cost initial.points initial.weights) 1 opt)
    (he : ∀ i,0≤e i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1)
    (ht : 0<t) (htε : (t:ℝ)⁻¹≤ε/10)
    (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (h : Adaptive.History (outcomes N (t*Fintype.card K) a e δ) n)
    (hh : Adaptive.historyGood (good initial proxy opt) n h) :
    SummaryAPC (K:=K) initial (cloud N a e δ t initial proxy n h)
      (fun i=>(cloud_pos initial hw proxy n h i).le) ε t ht := by
  let c := cloud N a e δ t initial proxy n h
  have hp := final_witness_preservation initial hw proxy opt he ε hε.le hε1 n hbudget h hh
  exact euclidean_apc_fixed_lift c.points c.weights (fun i=>(cloud_pos initial hw proxy n h i).le)
    (cost initial.points initial.weights) opt (cost_nonneg _ _ (fun i=>(hw i).le) opt)
    (fun u=>by simpa only [one_mul] using hoptimal u) ε hε hε1 t ht htε
    (fun u hu=>hp u (Or.inl hu)) (hp opt (Or.inr rfl))

theorem compression (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=E) N a e δ t)
    (opt : K → E) (hoptimal : Approximate (cost initial.points initial.weights) 1 opt)
    (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n) (hδ1 : ∀ n,δ n≤1)
    (hproxy : ∀ n c,(∀ j,0<c.weights j)→Approximate (cost c.points c.weights) a (proxy n c))
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) (ht : 0<t) (htε : (t:ℝ)⁻¹≤ε/10)
    (n : ℕ) (hbudget : errorBudget e n≤ε/40) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h=>
      ¬SummaryAPC (K:=K) initial (cloud N a e δ t initial proxy n h)
        (fun i=>(cloud_pos initial hw proxy n h i).le) ε t ht)≤errorBudget δ n := by
  have hb := all_stages_failure initial hw proxy opt ha he he1 hδ hδ1 ht hproxy n
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n) _ _ ?_) hb
  intro h hbad hgood
  exact hbad (summary_apc_of_good initial hw proxy opt hoptimal (fun i=>(he i).le)
    ε hε hε1 ht htε n hbudget h hgood)

end

/-- A concrete factor-four proxy obtained by finite support search. Its
correctness is verified; its preprocessing cost is not near-linear. -/
def searchProxy {K E : Type*} [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) [NeZero N] (e δ : ℕ → ℝ) (t : ℕ) : Proxy (K:=K) (X:=E) N 4 e δ t :=
  fun n c=>MetricIteration.supportCenters c

theorem searchProxy_spec {K E : Type*} [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) [NeZero N] (e δ : ℕ → ℝ) (t : ℕ) :
    ∀ n c,(∀ j,0<c.weights j)→Approximate (cost c.points c.weights) 4
      (searchProxy (K:=K) (E:=E) N e δ t n c) := by
  intro n c hw
  exact MetricIteration.supportSearch_approximate c (fun i=>(hw i).le)

/-- Unconditional Euclidean approximation and size theorem, for arbitrary
k and unrestricted real inner-product spaces. It uses an alternative
iterative construction, not the paper's unverified strong-coreset primitive.
The lift is fixed independently of the approximation factor and solution. -/
theorem unconditional_euclidean_apc
    {K E : Type*} [Fintype K] [Nonempty K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) E)
    (hw : ∀ i,0 < initial.weights i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    let t := liftingSampleCount (ε/10)
    let ht := (liftingWitnessCount_valid ε hε).1
    let e := logStageError (N:ℝ) 14400 ε
    let δ := MetricIteration.scheduledFailure N
    let proxy := searchProxy (K:=K) (E:=E) N e δ t
    let n := logStop (N:ℝ) 14400
    (size N (t*Fintype.card K) 4 e δ n:ℝ)≤metricSizeGamma (t*Fintype.card K) 4 ε*14400^2 ∧
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h=>
      ¬SummaryAPC (K:=K) initial (cloud N 4 e δ t initial proxy n h)
        (fun i=>(cloud_pos initial hw proxy n h i).le) ε t ht)≤1/2 := by
  dsimp only
  let t := liftingSampleCount (ε/10)
  let e := logStageError (N:ℝ) 14400 ε
  let δ := MetricIteration.scheduledFailure N
  let proxy := searchProxy (K:=K) (E:=E) N e δ t
  have ht := liftingWitnessCount_valid ε hε
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨MetricIteration.terminal_size_bound N (t*Fintype.card K) (Nat.mul_pos ht.1 Fintype.card_pos)
    4 ε (by norm_num) hε hε1,?_⟩
  exact (compression initial hw proxy (euclideanOptimal initial.points initial.weights)
    (euclideanOptimal_spec initial.points initial.weights (fun i=>(hw i).le)) (by norm_num)
    (MetricIteration.scheduledError_pos N ε hε) (MetricIteration.scheduledError_le_one N ε hε1)
    (MetricIteration.scheduledFailure_pos N) (MetricIteration.scheduledFailure_le_one N)
    (searchProxy_spec N e δ t) ε hε hε1 ht.1 ht.2 (logStop (N:ℝ) 14400)
    (logStageError_rescaled_budget (N:ℝ) ε hN hε.le)).trans (MetricIteration.scheduledFailure_budget N)

end APC.EuclideanIteration
