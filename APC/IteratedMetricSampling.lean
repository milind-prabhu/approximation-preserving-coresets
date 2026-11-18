import APC.MetricStageKernel
import APC.AdaptiveProbability
import APC.Iteration

open scoped BigOperators
noncomputable section
namespace APC.MetricIteration

/-- Explicit recursive sample counts. Every stage uses the verified local
finite-family sampling budget for the preceding stage's size. -/
def size (N k : ℕ) (a : ℝ) (e δ : ℕ → ℝ) : ℕ → ℕ
  | 0 => N
  | n+1 => metricStageSampleCount k (size N k a e δ n) a (e n) (δ n)

theorem size_pos (N k : ℕ) [NeZero N] (a : ℝ) (e δ : ℕ → ℝ) (n : ℕ) :
    0<size N k a e δ n := by
  cases n with
  | zero => exact Nat.pos_of_ne_zero (NeZero.ne N)
  | succ n => exact Nat.zero_lt_succ _

instance sizeNeZero (N k : ℕ) [NeZero N] (a : ℝ) (e δ : ℕ → ℝ) (n : ℕ) :
    NeZero (size N k a e δ n) := ⟨Nat.ne_of_gt (size_pos N k a e δ n)⟩

structure Cloud (I X : Type*) where
  points : I → X
  weights : I → ℝ

def outcomes (N k : ℕ) (a : ℝ) (e δ : ℕ → ℝ) (n : ℕ) : Type :=
  Draws (Fin (size N k a e δ n)) (size N k a e δ (n+1))

instance outcomesFintype (N k : ℕ) (a : ℝ) (e δ : ℕ → ℝ) (n : ℕ) :
    Fintype (outcomes N k a e δ n) := inferInstanceAs (Fintype (Draws _ _))

section
variable {K X : Type*} [Fintype K] [Nonempty K] [PseudoMetricSpace X]

def probability {I : Type*} [Fintype I] (c : Cloud I X) (proxy : K → X) : I → ℝ :=
  sensitivityProbability c.weights (fun i => pointCost proxy (c.points i))
    (fun i => nearest proxy (c.points i))

def sample {I : Type*} [Fintype I] (c : Cloud I X) (proxy : K → X)
    (m : ℕ) (z : Draws I m) : Cloud (Fin m) X :=
  ⟨sampledPoints c.points m z, sampledWeights c.weights (probability c proxy) m z⟩

theorem sample_pos {I : Type*} [Fintype I] [Nonempty I]
    (c : Cloud I X) (hc : ∀ i,0<c.weights i) (proxy : K → X)
    (m : ℕ) (hm : 0<m) (z : Draws I m) : ∀ j,0<(sample c proxy m z).weights j := by
  exact sampledWeights_pos c.weights (probability c proxy) hc
    (sensitivityProbability_pos _ _ _ hc (fun i => sq_nonneg _)) m hm z

variable (N : ℕ) (a : ℝ) (e δ : ℕ → ℝ)

abbrev Proxy := (n : ℕ) → Cloud (Fin (size N (Fintype.card K) a e δ n)) X → K → X

def cloud (initial : Cloud (Fin N) X) (proxy : Proxy (K:=K) (X:=X) N a e δ) :
    (n : ℕ) → Adaptive.History (outcomes N (Fintype.card K) a e δ) n →
      Cloud (Fin (size N (Fintype.card K) a e δ n)) X
  | 0, _ => initial
  | n+1, h => sample (cloud initial proxy n h.1) (proxy n (cloud initial proxy n h.1))
      (size N (Fintype.card K) a e δ (n+1)) h.2

variable {N a e δ}

theorem cloud_pos [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ) (n : ℕ) :
    ∀ h j,0<(cloud N a e δ initial proxy n h).weights j := by
  induction n with
  | zero => intro h; exact hw
  | succ n ih =>
    intro h
    exact sample_pos _ (ih h.1) _ _ (size_pos _ _ _ _ _ _) h.2

def transition (initial : Cloud (Fin N) X) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (n : ℕ) (h : Adaptive.History (outcomes N (Fintype.card K) a e δ) n) :
    outcomes N (Fintype.card K) a e δ n → ℝ :=
  drawWeight (probability (cloud N a e δ initial proxy n h)
    (proxy n (cloud N a e δ initial proxy n h))) (size N (Fintype.card K) a e δ (n+1))

theorem transition_nonneg [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ) :
    ∀ n h z,0≤transition initial proxy n h z := by
  intro n h z
  exact drawWeight_nonneg _
    (fun i => (sensitivityProbability_pos _ _ _ (cloud_pos initial hw proxy n h)
      (fun i => sq_nonneg _) i).le) _ z

theorem transition_sum [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ) :
    ∀ n h,∑ z,transition initial proxy n h z=1 := by
  intro n h
  exact drawWeight_sum _ (sensitivityProbability_sum _ _ _ (cloud_pos initial hw proxy n h)) _

def good (initial : Cloud (Fin N) X) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (n : ℕ) (h : Adaptive.History (outcomes N (Fintype.card K) a e δ) n)
    (z : outcomes N (Fintype.card K) a e δ n) : Prop :=
  let c := cloud N a e δ initial proxy n h
  let c' := sample c (proxy n c) (size N (Fintype.card K) a e δ (n+1)) z
  MetricStep c.points c.weights c'.points c'.weights opt (e n)

/-- Every conditional stage bound follows from sensitivity sampling with
the prescribed integer count, after an arbitrary previous history. -/
theorem good_failure [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) → Approximate (cost c.points c.weights) a (proxy n c)) :
    ∀ n h,eventMass (transition initial proxy n h) (fun z => ¬good initial proxy opt n h z) ≤ δ n := by
  intro n h
  let c := cloud N a e δ initial proxy n h
  have hc := cloud_pos initial hw proxy n h
  have hb := budgetSampleCount_valid
    ((48*(Fintype.card K:ℝ))*Real.log (8*(Fintype.card K:ℝ)/δ n))
    ((4*(64*a+8*a^2))*(Real.log (8/δ n)+
      (Fintype.card K:ℝ)*Real.log (size N (Fintype.card K) a e δ n)))
    (e n/(23+22*a)) (ne_of_gt (div_pos (he n) (by linarith)))
  exact metric_step_kernel_budget c.points c.weights hc (proxy n c) opt a (e n) (δ n)
    ha (he n) (he1 n) (hδ n) (hproxy n c hc) _ hb.1 hb.2.1
    (by simpa only [Fintype.card_fin] using hb.2.2)

theorem all_stages_failure [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) → Approximate (cost c.points c.weights) a (proxy n c))
    (n : ℕ) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n)
      (fun h => ¬Adaptive.historyGood (good initial proxy opt) n h) ≤ errorBudget δ n := by
  exact Adaptive.adaptive_failure_bound _ (transition_nonneg initial hw proxy)
    (transition_sum initial hw proxy) _ δ (fun n => (hδ n).le)
    (fun n h _ => good_failure initial hw proxy opt ha he he1 hδ hproxy n h) n

/-- Deterministic bounds for every query supported by the final summary,
or equal to the original optimum, on a good adaptive history. -/
theorem chain_bounds [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (he : ∀ i,0≤e i) (n : ℕ) (hbudget : errorBudget e n≤1/2) :
    ∀ h,Adaptive.historyGood (good initial proxy opt) n h → ∀ s,
      ((∀ j,s j∈Set.range (cloud N a e δ initial proxy n h).points) ∨ s=opt) →
      let q := cost (cloud N a e δ initial proxy n h).points (cloud N a e δ initial proxy n h).weights s
      (1-errorBudget e n)*cost initial.points initial.weights s≤q ∧
        (1-errorBudget e n)*q≤cost initial.points initial.weights s := by
  induction n with
  | zero => intro h hh s hs; simp [cloud,errorBudget]
  | succ n ih =>
    intro h hh s hs
    have hrec : errorBudget e (n+1)=errorBudget e n+e n := Finset.sum_range_succ e n
    have hS := errorBudget_nonneg e he n
    have hbn : errorBudget e n≤1/2 := by rw [hrec] at hbudget; linarith [he n]
    have hen : e n≤1/2 := by rw [hrec] at hbudget; linarith
    change Adaptive.historyGood (good initial proxy opt) n h.1 ∧ good initial proxy opt n h.1 h.2 at hh
    let c := cloud N a e δ initial proxy n h.1
    have hs' : (∀ j,s j∈Set.range c.points) ∨ s=opt := by
      rcases hs with hs | hs
      · exact Or.inl (fun j => sampledPoints_range_subset c.points _ h.2 (hs j))
      · exact Or.inr hs
    obtain ⟨hlo,hup⟩ := ih hbn h.1 hh.1 s hs'
    obtain ⟨hnextlo,hnexthi⟩ := hh.2 s hs'
    have hc0 := cost_nonneg initial.points initial.weights (fun i => (hw i).le) s
    have hcn := cost_nonneg c.points c.weights (fun i => (cloud_pos initial hw proxy n h.1 i).le) s
    change (1-errorBudget e (n+1))*cost initial.points initial.weights s ≤
        cost (sample c (proxy n c) _ h.2).points (sample c (proxy n c) _ h.2).weights s ∧ _
    rw [hrec]
    constructor
    · have hm := mul_le_mul_of_nonneg_left hlo (by linarith : 0≤1-e n)
      have hx := mul_nonneg (mul_nonneg (he n) hS) hc0
      nlinarith only [hm,hnextlo,hx]
    · have hm := mul_le_mul_of_nonneg_left hnexthi
        (by rw [hrec] at hbudget; linarith : 0≤1-(errorBudget e n+e n))
      have hx := mul_nonneg (mul_nonneg (he n) (add_nonneg hS (he n))) hcn
      dsimp only [c, cloud] at hm hup hx ⊢
      nlinarith only [hm,hup,hx]

theorem chain_preserves [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (he : ∀ i,0≤e i) (n : ℕ) (hbudget : errorBudget e n≤1/2) :
    ∀ h,Adaptive.historyGood (good initial proxy opt) n h → ∀ s,
      ((∀ j,s j∈Set.range (cloud N a e δ initial proxy n h).points) ∨ s=opt) →
      Preserves (cost initial.points initial.weights s)
        (cost (cloud N a e δ initial proxy n h).points (cloud N a e δ initial proxy n h).weights s)
        (2*errorBudget e n) := by
  intro h hh s hs
  obtain ⟨hlo,hup⟩ := chain_bounds initial hw proxy opt he n hbudget h hh s hs
  have hc0 := cost_nonneg initial.points initial.weights (fun i => (hw i).le) s
  have hcn := cost_nonneg (cloud N a e δ initial proxy n h).points
    (cloud N a e δ initial proxy n h).weights (fun i => (cloud_pos initial hw proxy n h i).le) s
  have hS := errorBudget_nonneg e he n
  constructor
  · nlinarith [mul_nonneg hS hc0]
  · have hm := mul_le_mul_of_nonneg_left hup (by positivity : 0≤1+2*errorBudget e n)
    have hx := mul_nonneg (mul_nonneg hS (by linarith : 0≤1-2*errorBudget e n)) hcn
    nlinarith only [hm,hx]

/-- The prescribed adaptive sampling experiment returns an APC, for any
finite horizon whose local errors have total at most ε/40. The only
algorithmic primitive supplied is the approximation proxy at each stage. -/
theorem compression [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) → Approximate (cost c.points c.weights) a (proxy n c))
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (n : ℕ) (hbudget : errorBudget e n≤ε/40) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h =>
      let c := cloud N a e δ initial proxy n h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        ¬∃ f : K → Fin (size N (Fintype.card K) a e δ n),
          cost initial.points initial.weights (fun j => c.points (f j)) ≤
            α*(4+ε)*cost initial.points initial.weights opt) ≤ errorBudget δ n := by
  have hb := all_stages_failure initial hw proxy opt ha he he1 hδ hproxy n
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n) _ _ ?_) hb
  intro h hbad hgood
  obtain ⟨α,s,hα,happrox,hno⟩ := hbad
  let c := cloud N a e δ initial proxy n h
  have hp := chain_preserves initial hw proxy opt (fun i => (he i).le) n (by linarith) h hgood
  have hpres : ∀ u, (∀ j,u j∈Set.range c.points) ∨ u=opt →
      Preserves (cost initial.points initial.weights u) (cost c.points c.weights u) (ε/20) := by
    intro u hu
    exact preserves_mono (cost_nonneg _ _ (fun i => (hw i).le) u) (by linarith) (hp u hu)
  apply hno
  exact metric_apc_of_preservation c.points c.weights (fun i => (cloud_pos initial hw proxy n h i).le)
    (cost initial.points initial.weights) opt s α ε hα hε hε1
    (cost_nonneg _ _ (fun i => (hw i).le) opt) happrox
    (fun f => hpres _ (Or.inl (fun j => ⟨f j,rfl⟩))) (hpres opt (Or.inr rfl))

/-- The actual summary-only nearest-point lifting map. -/
def rounded {I : Type*} [Fintype I] [Nonempty I] (c : Cloud I X) (s : K → X) : K → X :=
  fun j => c.points (nearest c.points (s j))

theorem rounded_chain_bound [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (he : ∀ i,0≤e i) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (n : ℕ) (hbudget : errorBudget e n≤ε/40)
    (h : Adaptive.History (outcomes N (Fintype.card K) a e δ) n)
    (hh : Adaptive.historyGood (good initial proxy opt) n h)
    (s : K → X) (α : ℝ) (hα : 0≤α)
    (happrox : Approximate (cost (cloud N a e δ initial proxy n h).points
      (cloud N a e δ initial proxy n h).weights) α s) :
    cost initial.points initial.weights (rounded (cloud N a e δ initial proxy n h) s) ≤
      α*(4+ε)*cost initial.points initial.weights opt := by
  let c := cloud N a e δ initial proxy n h
  have hc : ∀ i,0≤c.weights i := fun i => (cloud_pos initial hw proxy n h i).le
  have hp := chain_preserves initial hw proxy opt he n (by linarith) h hh
  have hpres : ∀ u, (∀ j,u j∈Set.range c.points) ∨ u=opt →
      Preserves (cost initial.points initial.weights u) (cost c.points c.weights u) (ε/20) := by
    intro u hu
    exact preserves_mono (cost_nonneg _ _ (fun i => (hw i).le) u) (by linarith) (hp u hu)
  have hout := hpres (rounded c s) (Or.inl (fun j => ⟨nearest c.points (s j),rfl⟩))
  have hopt := hpres opt (Or.inr rfl)
  have hlift : cost c.points c.weights (rounded c s) ≤ 4*cost c.points c.weights s :=
    metric_rounding c.points c.weights hc s (rounded c s) (fun j i => nearest_le c.points (s j) i)
  have hb := witness_transfer (cost initial.points initial.weights) (cost c.points c.weights)
    s (rounded c s) opt α 4 (ε/20) hα (by norm_num) (by linarith) happrox hlift hout.1 hopt.2
  calc
    _ ≤ α*4*((1+ε/20)/(1-ε/20))*cost initial.points initial.weights opt := hb
    _ = α*(4*((1+ε/20)/(1-ε/20)))*cost initial.points initial.weights opt := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (metric_factor ε hε hε1) hα)
      (cost_nonneg _ _ (fun i => (hw i).le) opt)

/-- Guarantee for the actual returned centers. The event is uniform over
all approximation factors and all input solutions, so a solver may depend
arbitrarily on the entire sampled summary. -/
theorem rounded_compression [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) → Approximate (cost c.points c.weights) a (proxy n c))
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (n : ℕ) (hbudget : errorBudget e n≤ε/40) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n) (fun h =>
      let c := cloud N a e δ initial proxy n h
      ∃ (α : ℝ) (s : K → X),0≤α ∧ Approximate (cost c.points c.weights) α s ∧
        α*(4+ε)*cost initial.points initial.weights opt <
          cost initial.points initial.weights (rounded c s)) ≤ errorBudget δ n := by
  have hb := all_stages_failure initial hw proxy opt ha he he1 hδ hproxy n
  apply le_trans (eventMass_mono _
    (Adaptive.historyWeight_nonneg _ (transition_nonneg initial hw proxy) n) _ _ ?_) hb
  intro h hbad hgood
  obtain ⟨α,s,hα,happrox,ht⟩ := hbad
  exact not_lt_of_ge (rounded_chain_bound initial hw proxy opt (fun i => (he i).le)
    ε hε hε1 n hbudget h hgood s α hα happrox) ht

end
end APC.MetricIteration
