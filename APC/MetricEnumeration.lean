import APC.MetricSizeCorrectness

open scoped BigOperators
noncomputable section
namespace APC.MetricIteration
local instance (T : Type*) : DecidableEq T := Classical.decEq T

section Search
variable {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
  [PseudoMetricSpace X]

/-- Exhaustive summary-only search. Ordered tuples allow repeated centers;
no center outside the summary is inspected by this final search. -/
def supportSearch (c : Cloud I X) : K → I :=
  Classical.choose (Finset.exists_min_image Finset.univ
    (fun f : K → I=>cost c.points c.weights (fun j=>c.points (f j))) Finset.univ_nonempty)

def supportCenters (c : Cloud I X) : K → X := fun j=>c.points (supportSearch c j)

theorem supportSearch_spec (c : Cloud I X) (f : K → I) :
    cost c.points c.weights (supportCenters (K:=K) c)≤
      cost c.points c.weights (fun j=>c.points (f j)) :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun f : K → I=>cost c.points c.weights (fun j=>c.points (f j))) Finset.univ_nonempty)).2 f
      (Finset.mem_univ f)

theorem supportCenters_supported (c : Cloud I X) :
    ∀ j,supportCenters (K:=K) c j∈Set.range c.points := fun j=>⟨supportSearch c j,rfl⟩

/-- Support search is a factor-four solution even when comparison centers
are allowed anywhere in the ambient metric. -/
theorem supportSearch_le_four (c : Cloud I X) (hw : ∀ i,0≤c.weights i) (s : K → X) :
    cost c.points c.weights (supportCenters (K:=K) c)≤4*cost c.points c.weights s := by
  calc
    _≤cost c.points c.weights (rounded c s) := supportSearch_spec c (fun j=>nearest c.points (s j))
    _≤_ := metric_rounding c.points c.weights hw s (rounded c s) (fun j i=>nearest_le c.points (s j) i)

theorem supportSearch_approximate (c : Cloud I X) (hw : ∀ i,0≤c.weights i) :
    Approximate (cost c.points c.weights) 4 (supportCenters (K:=K) c) :=
  supportSearch_le_four c hw

/-- Exact candidate count for this tuple-based final search, before
identifying permutations, repeated centers or duplicate summary points. -/
theorem supportSearch_candidate_count :
    (Finset.univ : Finset (K → I)).card=Fintype.card I^Fintype.card K := by
  simp

end Search

section Compression
variable {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]
variable {N : ℕ} [NeZero N] {a : ℝ} {e δ : ℕ → ℝ}

/-- On a good chain, directly returning the best summary-supported tuple
avoids applying the rounding factor a second time. -/
theorem enumeration_chain_bound (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (he : ∀ i,0≤e i) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (h : Adaptive.History (outcomes N (Fintype.card K) a e δ) n)
    (hh : Adaptive.historyGood (good initial proxy opt) n h) :
    cost initial.points initial.weights (supportCenters (K:=K) (cloud N a e δ initial proxy n h))≤
      (4+ε)*cost initial.points initial.weights opt := by
  let c := cloud N a e δ initial proxy n h
  have hc : ∀ i,0≤c.weights i := fun i=>(cloud_pos initial hw proxy n h i).le
  have hp := chain_preserves initial hw proxy opt he n (by linarith) h hh
  have hpres : ∀ u,(∀ j,u j∈Set.range c.points) ∨ u=opt →
      Preserves (cost initial.points initial.weights u) (cost c.points c.weights u) (ε/20) := by
    intro u hu
    exact preserves_mono (cost_nonneg _ _ (fun i=>(hw i).le) u) (by linarith) (hp u hu)
  have hs := hpres (supportCenters (K:=K) c) (Or.inl (supportCenters_supported c))
  have ho := hpres opt (Or.inr rfl)
  have hb := witness_transfer (cost initial.points initial.weights) (cost c.points c.weights)
    (supportCenters (K:=K) c) (supportCenters (K:=K) c) opt 4 1 (ε/20) (by norm_num) (by norm_num)
    (by linarith) (supportSearch_approximate c hc) (by simp) hs.1 ho.2
  calc
    _≤4*((1+ε/20)/(1-ε/20))*cost initial.points initial.weights opt := by simpa using hb
    _≤_ := mul_le_mul_of_nonneg_right (metric_factor ε hε hε1)
      (cost_nonneg _ _ (fun i=>(hw i).le) opt)

/-- Actual repeated sensitivity sampling followed by exhaustive final
support search, with failure bounded by the sum of stage failure budgets. -/
theorem enumeration_compression (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n)
    (hproxy : ∀ n c,(∀ j,0<c.weights j)→Approximate (cost c.points c.weights) a (proxy n c))
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (n : ℕ) (hbudget : errorBudget e n≤ε/40) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h=>
      (4+ε)*cost initial.points initial.weights opt<
        cost initial.points initial.weights (supportCenters (K:=K) (cloud N a e δ initial proxy n h)))≤errorBudget δ n := by
  have hb := all_stages_failure initial hw proxy opt ha he he1 hδ hproxy n
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n) _ _ ?_) hb
  intro h hbad hgood
  exact not_lt_of_ge (enumeration_chain_bound initial hw proxy opt (fun i=>(he i).le)
    ε hε hε1 n hbudget h hgood) hbad

end Compression

/-- The finite-metric construction with the final support solver specified.
Size and approximation refer to the same sampler and returned center tuple.
Exhaustive proxies ensure correctness, but their efficient construction and
full runtime are not asserted here. -/
theorem finite_metric_enumeration_correctness
    {K X : Type*} [Fintype K] [Nonempty K]
    [Fintype X] [Nonempty X] [PseudoMetricSpace X]
    (N : ℕ) [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    let e := logStageError (N:ℝ) 14400 ε
    let δ := scheduledFailure N
    let proxy := exactProxy (K:=K) (X:=X) N e δ
    let t := logStop (N:ℝ) 14400
    (size N (Fintype.card K) 1 e δ t:ℝ)≤metricSizeGamma (Fintype.card K) 1 ε*14400^2 ∧
    eventMass (Adaptive.historyWeight (transition initial proxy) t) (fun h=>
      ¬Approximate (cost initial.points initial.weights) (4+ε)
        (supportCenters (K:=K) (cloud N 1 e δ initial proxy t h)))≤1/2 := by
  classical
  dsimp only
  let e := logStageError (N:ℝ) 14400 ε
  let δ := scheduledFailure N
  let proxy := exactProxy (K:=K) (X:=X) N e δ
  let opt := optimalProxy (K:=K) initial
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hb := (enumeration_compression initial hw proxy opt (by norm_num)
    (scheduledError_pos N ε hε) (scheduledError_le_one N ε hε1) (scheduledFailure_pos N)
    (fun n c _=>optimalProxy_spec c) ε hε.le hε1 (logStop (N:ℝ) 14400)
    (logStageError_rescaled_budget (N:ℝ) ε hN hε.le)).trans (scheduledFailure_budget N)
  refine ⟨terminal_size_bound N (Fintype.card K) Fintype.card_pos 1 ε (by norm_num) hε hε1,?_⟩
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) _) _ _ ?_) hb
  intro h hbad
  by_contra hn
  apply hbad
  intro u
  have ho : cost initial.points initial.weights opt≤cost initial.points initial.weights u := by
    simpa only [one_mul] using optimalProxy_spec initial u
  exact (le_of_not_gt hn).trans (mul_le_mul_of_nonneg_left ho (by linarith))

/-- An explicit input-size-independent bound on the number of ordered
candidate tuples examined by the final solver. This is not a full runtime
bound nor the sharper binomial enumeration bound in the paper. -/
theorem terminal_enumeration_count_bound (N k : ℕ) [NeZero N] (hk : 0<k)
    (a ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) :
    ((size N k a (logStageError (N:ℝ) 14400 ε) (scheduledFailure N)
      (logStop (N:ℝ) 14400):ℝ)^k)≤(metricSizeGamma k a ε*14400^2)^k :=
  pow_le_pow_left₀ (Nat.cast_nonneg _) (terminal_size_bound N k hk a ε ha hε hε1) k

end APC.MetricIteration
