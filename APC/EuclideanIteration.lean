import APC.EuclideanStage
import APC.IteratedMetricSampling

open scoped BigOperators
noncomputable section
namespace APC.EuclideanIteration
open MetricIteration (Cloud size size_pos outcomes probability sample sample_pos)

section
variable {K X : Type*} [Fintype K] [Nonempty K] [NormedAddCommGroup X] [InnerProductSpace ℝ X]

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

variable (N : ℕ) (a : ℝ) (e δ : ℕ → ℝ) (t : ℕ)

abbrev Proxy := (n : ℕ) → Cloud (Fin (size N (t*Fintype.card K) a e δ n)) X → K → X

def cloud (initial : Cloud (Fin N) X) (proxy : Proxy (K:=K) (X:=X) N a e δ t) :
    (n : ℕ) → Adaptive.History (outcomes N (t*Fintype.card K) a e δ) n →
      Cloud (Fin (size N (t*Fintype.card K) a e δ n)) X
  | 0, _ => initial
  | n+1, h => sample (cloud initial proxy n h.1) (proxy n (cloud initial proxy n h.1))
      (size N (t*Fintype.card K) a e δ (n+1)) h.2

variable {N a e δ t}

theorem cloud_pos [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t) (n : ℕ) :
    ∀ h j,0<(cloud N a e δ t initial proxy n h).weights j := by
  induction n with
  | zero => intro h; exact hw
  | succ n ih =>
    intro h
    exact sample_pos _ (ih h.1) _ _ (size_pos _ _ _ _ _ _) h.2

/-- Every retained point comes from the original input, on every history. -/
theorem cloud_support_subset [NeZero N] (initial : Cloud (Fin N) X)
    (proxy : Proxy (K:=K) (X:=X) N a e δ t) (n : ℕ) :
    ∀ h,Set.range (cloud N a e δ t initial proxy n h).points⊆Set.range initial.points := by
  induction n with
  | zero => intro h;exact Set.Subset.refl _
  | succ n ih =>
    intro h
    exact (sampledPoints_range_subset (cloud N a e δ t initial proxy n h.1).points _ h.2).trans (ih h.1)

def transition (initial : Cloud (Fin N) X) (proxy : Proxy (K:=K) (X:=X) N a e δ t)
    (n : ℕ) (h : Adaptive.History (outcomes N (t*Fintype.card K) a e δ) n) :
    outcomes N (t*Fintype.card K) a e δ n → ℝ :=
  drawWeight (probability (cloud N a e δ t initial proxy n h)
    (proxy n (cloud N a e δ t initial proxy n h))) (size N (t*Fintype.card K) a e δ (n+1))

theorem transition_nonneg [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t) :
    ∀ n h z,0≤transition initial proxy n h z := by
  intro n h z
  exact drawWeight_nonneg _
    (fun i => (sensitivityProbability_pos _ _ _ (cloud_pos initial hw proxy n h)
      (fun i => sq_nonneg _) i).le) _ z

theorem transition_sum [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t) :
    ∀ n h,∑ z,transition initial proxy n h z=1 := by
  intro n h
  exact drawWeight_sum _ (sensitivityProbability_sum _ _ _ (cloud_pos initial hw proxy n h)) _

def good (initial : Cloud (Fin N) X) (proxy : Proxy (K:=K) (X:=X) N a e δ t)
    (opt : K → X) (n : ℕ) (h : Adaptive.History (outcomes N (t*Fintype.card K) a e δ) n)
    (z : outcomes N (t*Fintype.card K) a e δ n) : Prop :=
  let c := cloud N a e δ t initial proxy n h
  let c' := sample c (proxy n c) (size N (t*Fintype.card K) a e δ (n+1)) z
  EuclideanStep c.points c.weights c'.points c'.weights opt t (e n)

/-- Every conditional stage bound follows from sensitivity sampling with
the prescribed integer count, after an arbitrary previous history. -/
theorem good_failure [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n) (hδ1 : ∀ n,δ n≤1) (ht : 0<t)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) → Approximate (cost c.points c.weights) a (proxy n c)) :
    ∀ n h,eventMass (transition initial proxy n h) (fun z => ¬good initial proxy opt n h z) ≤ δ n := by
  intro n h
  let c := cloud N a e δ t initial proxy n h
  have hc := cloud_pos initial hw proxy n h
  have hb := euclidean_step_kernel c.points c.weights hc (proxy n c) opt t ht a
    (e n) (δ n) ha (he n) (he1 n) (hδ n) (hδ1 n) (hproxy n c hc)
  dsimp only at hb
  have hI : Fintype.card (Fin (size N (t*Fintype.card K) a e δ n))=size N (t*Fintype.card K) a e δ n := Fintype.card_fin _
  rw [hI] at hb
  exact hb

theorem all_stages_failure [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t)
    (opt : K → X) (ha : 0<a) (he : ∀ n,0<e n) (he1 : ∀ n,e n≤1)
    (hδ : ∀ n,0<δ n) (hδ1 : ∀ n,δ n≤1) (ht : 0<t)
    (hproxy : ∀ n c, (∀ j,0<c.weights j) → Approximate (cost c.points c.weights) a (proxy n c))
    (n : ℕ) :
    eventMass (Adaptive.historyWeight (transition initial proxy) n)
      (fun h => ¬Adaptive.historyGood (good initial proxy opt) n h) ≤ errorBudget δ n := by
  exact Adaptive.adaptive_failure_bound _ (transition_nonneg initial hw proxy)
    (transition_sum initial hw proxy) _ δ (fun n => (hδ n).le)
    (fun n h _ => good_failure initial hw proxy opt ha he he1 hδ hδ1 ht hproxy n h) n

/-- Deterministic bounds for every query supported by the final summary,
or equal to the original optimum, on a good adaptive history. -/
theorem chain_bounds [NeZero N] (initial : Cloud (Fin N) X)
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t)
    (opt : K → X) (he : ∀ i,0≤e i) (n : ℕ) (hbudget : errorBudget e n≤1/2) :
    ∀ h,Adaptive.historyGood (good initial proxy opt) n h → ∀ s,
      (s∈witnessFamily (cloud N a e δ t initial proxy n h).points t ∨ s=opt) →
      let q := cost (cloud N a e δ t initial proxy n h).points (cloud N a e δ t initial proxy n h).weights s
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
    let c := cloud N a e δ t initial proxy n h.1
    have hs' : s∈witnessFamily c.points t ∨ s=opt := by
      rcases hs with hs | hs
      · exact Or.inl (witnessFamily_mono (sampledPoints c.points _ h.2) c.points
          (drawIndex _ h.2) (fun _=>rfl) t s hs)
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
    (hw : ∀ i,0 < initial.weights i) (proxy : Proxy (K:=K) (X:=X) N a e δ t)
    (opt : K → X) (he : ∀ i,0≤e i) (n : ℕ) (hbudget : errorBudget e n≤1/2) :
    ∀ h,Adaptive.historyGood (good initial proxy opt) n h → ∀ s,
      (s∈witnessFamily (cloud N a e δ t initial proxy n h).points t ∨ s=opt) →
      Preserves (cost initial.points initial.weights s)
        (cost (cloud N a e δ t initial proxy n h).points (cloud N a e δ t initial proxy n h).weights s)
        (2*errorBudget e n) := by
  intro h hh s hs
  obtain ⟨hlo,hup⟩ := chain_bounds initial hw proxy opt he n hbudget h hh s hs
  have hc0 := cost_nonneg initial.points initial.weights (fun i => (hw i).le) s
  have hcn := cost_nonneg (cloud N a e δ t initial proxy n h).points
    (cloud N a e δ t initial proxy n h).weights (fun i => (cloud_pos initial hw proxy n h i).le) s
  have hS := errorBudget_nonneg e he n
  constructor
  · nlinarith [mul_nonneg hS hc0]
  · have hm := mul_le_mul_of_nonneg_left hup (by positivity : 0≤1+2*errorBudget e n)
    have hx := mul_nonneg (mul_nonneg hS (by linarith : 0≤1-2*errorBudget e n)) hcn
    nlinarith only [hm,hx]


end
end APC.EuclideanIteration
