import APC.BinomialBudget

open scoped BigOperators
noncomputable section
namespace APC.MetricIteration
local instance (T : Type*) : DecidableEq T := Classical.decEq T

section Output
variable {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]

def subsetOutput {m : ℕ} [NeZero m] (c : Cloud (Fin m) X)
    (hkm : Fintype.card K≤m) : K → X :=
  subsetSearchCenters c (by simpa using hkm)

theorem subsetOutput_supported {m : ℕ} [NeZero m] (c : Cloud (Fin m) X)
    (hkm : Fintype.card K≤m) : ∀ j,subsetOutput c hkm j∈Set.range c.points :=
  subsetSearch_supported c (by simpa using hkm)

theorem subsetOutput_le_four {m : ℕ} [NeZero m] (c : Cloud (Fin m) X)
    (hw : ∀ i,0≤c.weights i) (hkm : Fintype.card K≤m) (s : K → X) :
    cost c.points c.weights (subsetOutput c hkm)≤4*cost c.points c.weights s :=
  subsetSearch_le_four c hw (by simpa using hkm) s

end Output

section Compression
variable {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]
variable {N : ℕ} [NeZero N] {a : ℝ} {e δ : ℕ → ℝ}

theorem subset_enumeration_chain_bound (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (he : ∀ i,0≤e i) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (hkm : Fintype.card K≤size N (Fintype.card K) a e δ n)
    (h : Adaptive.History (outcomes N (Fintype.card K) a e δ) n)
    (hh : Adaptive.historyGood (good initial proxy opt) n h) :
    cost initial.points initial.weights (subsetOutput (cloud N a e δ initial proxy n h) hkm)≤
      (4+ε)*cost initial.points initial.weights opt := by
  let c := cloud N a e δ initial proxy n h
  have hc : ∀ i,0≤c.weights i := fun i=>(cloud_pos initial hw proxy n h i).le
  have hp := chain_preserves initial hw proxy opt he n (by linarith) h hh
  have hpres : ∀ u,(∀ j,u j∈Set.range c.points) ∨ u=opt →
      Preserves (cost initial.points initial.weights u) (cost c.points c.weights u) (ε/20) := by
    intro u hu
    exact preserves_mono (cost_nonneg _ _ (fun i=>(hw i).le) u) (by linarith) (hp u hu)
  have hs := hpres (subsetOutput c hkm) (Or.inl (subsetOutput_supported c hkm))
  have ho := hpres opt (Or.inr rfl)
  have hb := witness_transfer (cost initial.points initial.weights) (cost c.points c.weights)
    (subsetOutput c hkm) (subsetOutput c hkm) opt 4 1 (ε/20) (by norm_num) (by norm_num)
    (by linarith) (subsetOutput_le_four c hc hkm) (by simp) hs.1 ho.2
  calc
    _≤4*((1+ε/20)/(1-ε/20))*cost initial.points initial.weights opt := by simpa using hb
    _≤_ := mul_le_mul_of_nonneg_right (metric_factor ε hε hε1)
      (cost_nonneg _ _ (fun i=>(hw i).le) opt)

/-- Every history is sampled exactly as before. The returned centers now
come from the best size-k subset, and the approximation factor is unchanged. -/
theorem subset_enumeration_compression (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n)
    (hproxy : ∀ n c,(∀ j,0<c.weights j)→Approximate (cost c.points c.weights) a (proxy n c))
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (hkm : Fintype.card K≤size N (Fintype.card K) a e δ n) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h=>
      (4+ε)*cost initial.points initial.weights opt<
        cost initial.points initial.weights (subsetOutput (cloud N a e δ initial proxy n h) hkm))≤errorBudget δ n := by
  have hb := all_stages_failure initial hw proxy opt ha he he1 hδ hproxy n
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n) _ _ ?_) hb
  intro h hbad hgood
  exact not_lt_of_ge (subset_enumeration_chain_bound initial hw proxy opt (fun i=>(he i).le)
    ε hε hε1 n hbudget hkm h hgood) hbad

end Compression

/-- Actual subset-search output, the same adaptive sampler, and the sharp
binomial candidate envelope in one statement. Exact finite-search proxies
remove premises but do not verify near-linear preprocessing runtime. -/
theorem finite_metric_subset_enumeration_correctness
    {K X : Type*} [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    let k := Fintype.card K
    let e := logStageError (N:ℝ) 14400 ε
    let δ := scheduledFailure N
    let proxy := exactProxy (K:=K) (X:=X) N e δ
    let t := logStop (N:ℝ) 14400
    let m := size N k 1 e δ t
    let hkm := terminal_size_ge_centers N k Fintype.card_pos 1 ε (by norm_num) hε hε1
    (m.choose k:ℝ)≤(Real.exp 17*1265625*14400^2*(1+Real.log (metricSizeBase k 1 ε))/ε^2)^k ∧
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h=>
      ¬Approximate (cost initial.points initial.weights) (4+ε)
        (subsetOutput (cloud N 1 e δ initial proxy t h) hkm))≤1/2 := by
  classical
  dsimp only
  let e := logStageError (N:ℝ) 14400 ε
  let δ := scheduledFailure N
  let proxy := exactProxy (K:=K) (X:=X) N e δ
  let opt := optimalProxy (K:=K) initial
  have hkm := terminal_size_ge_centers N (Fintype.card K) Fintype.card_pos 1 ε (by norm_num) hε hε1
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hb := (subset_enumeration_compression initial hw proxy opt (by norm_num)
    (scheduledError_pos N ε hε) (scheduledError_le_one N ε hε1) (scheduledFailure_pos N)
    (fun n c _=>optimalProxy_spec c) ε hε.le hε1 (logStop (N:ℝ) 14400)
    (logStageError_rescaled_budget (N:ℝ) ε hN hε.le) hkm).trans (scheduledFailure_budget N)
  refine ⟨terminal_binomial_parameter_bound N (Fintype.card K) Fintype.card_pos ε hε hε1,?_⟩
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) _) _ _ ?_) hb
  intro h hbad
  by_contra hn
  apply hbad
  intro u
  have ho : cost initial.points initial.weights opt≤cost initial.points initial.weights u := by
    simpa only [one_mul] using optimalProxy_spec initial u
  exact (le_of_not_gt hn).trans (mul_le_mul_of_nonneg_left ho (by linarith))

end APC.MetricIteration
