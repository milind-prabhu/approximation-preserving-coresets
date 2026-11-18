import APC.LogSchedule
import APC.AdaptiveIteration

open scoped BigOperators
noncomputable section
namespace APC

/-- Integer rounding of Algorithm 4's Γ L_i² count. -/
def metricIterationCount (Γ x B : ℝ) (i : ℕ) : ℕ := Nat.ceil (Γ*(logLevel x B i)^2)

theorem metricIterationCount_lower (Γ x B : ℝ) (i : ℕ) :
    Γ*(logLevel x B i)^2 ≤ (metricIterationCount Γ x B i:ℝ) := Nat.le_ceil _

theorem metricIterationCount_upper (Γ x B : ℝ) (hΓ : 0≤Γ) (i : ℕ) :
    (metricIterationCount Γ x B i:ℝ) < Γ*(logLevel x B i)^2+1 :=
  Nat.ceil_lt_add_one (mul_nonneg hΓ (sq_nonneg _))

theorem metricIterationCount_pos (Γ x B : ℝ) (hΓ : 0<Γ) (hB : 0<B) (i : ℕ) :
    0<metricIterationCount Γ x B i := by
  apply Nat.ceil_pos.mpr
  exact mul_pos hΓ (sq_pos_of_pos (lt_of_lt_of_le hB (logLevel_lower x B i)))

theorem metricIterationCount_terminal (Γ x B : ℝ) (hx : 0<x) (hB : 1≤B) :
    metricIterationCount Γ x B (logStop x B-1) = Nat.ceil (Γ*B^2) := by
  simp only [metricIterationCount,logLevel_terminal x B hx hB]

/-- The final support cardinality is independent of x, given the sampler's
cardinality bound. This is an exact ceiling statement, not an asymptotic. -/
theorem metric_terminal_support_bound {X : Type*} (support : Finset X)
    (Γ x B : ℝ) (hx : 0<x) (hB : 1≤B)
    (hsize : support.card≤metricIterationCount Γ x B (logStop x B-1)) :
    support.card≤Nat.ceil (Γ*B^2) := by
  rwa [metricIterationCount_terminal Γ x B hx hB] at hsize

/-- Ceiling rounding retains more than the factor-two decrease needed by
our probability budget. -/
theorem metricIterationCount_backward (Γ x B : ℝ) (hx : 0<x)
    (hB : 8≤B) (hΓ : 0<Γ) (hbase : 1≤Γ*B^2)
    (i : ℕ) (hi : i+2<logStop x B) :
    2*(metricIterationCount Γ x B (i+1):ℝ) ≤ metricIterationCount Γ x B i := by
  have hL := logLevel_lower x B (i+1)
  have hU := logLevel_lower x B i
  have hg := logLevel_backward_growth x B hx hB i hi
  have hsq : 16*(logLevel x B (i+1))^2 ≤ (logLevel x B i)^2 := by
    nlinarith [mul_nonneg (by linarith : 0≤logLevel x B i-4*logLevel x B (i+1))
      (by linarith : 0≤logLevel x B i+4*logLevel x B (i+1))]
  have hmin : B^2≤(logLevel x B (i+1))^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hmin hΓ.le
  have hs := mul_le_mul_of_nonneg_left hsq hΓ.le
  have hlow := metricIterationCount_lower Γ x B i
  have hupp := metricIterationCount_upper Γ x B hΓ.le (i+1)
  nlinarith only [hm,hs,hlow,hupp,hbase]

def metricCountFailure (Γ x B : ℝ) (i : ℕ) : ℝ :=
  1/(4*(metricIterationCount Γ x B i:ℝ))

theorem metricCountFailure_nonneg (Γ x B : ℝ) (i : ℕ) :
    0≤metricCountFailure Γ x B i := by unfold metricCountFailure; positivity

theorem metricCountFailure_sum (Γ x B : ℝ) (hx : 0<x)
    (hB : 8≤B) (hΓ : 0<Γ) (hbase : 1≤Γ*B^2) :
    (∑ i ∈ Finset.range (logStop x B),metricCountFailure Γ x B i) ≤ 3/(4*Γ*B^2) := by
  have hBpos : 0<B := by linarith
  have hpos : ∀ i,(0:ℝ)<metricIterationCount Γ x B i :=
    fun i=>Nat.cast_pos.mpr (metricIterationCount_pos Γ x B hΓ hBpos i)
  have hb := terminal_geometric_sum (metricCountFailure Γ x B)
    (metricCountFailure_nonneg Γ x B) (logStop x B) (1/(4*Γ*B^2)) (by positivity) (by
      intro i _
      have hL := logLevel_lower x B i
      have hsq : B^2≤(logLevel x B i)^2 := by nlinarith
      have hm := (mul_le_mul_of_nonneg_left hsq hΓ.le).trans (metricIterationCount_lower Γ x B i)
      exact one_div_le_one_div_of_le (by positivity : 0<4*Γ*B^2) (by nlinarith)) (by
      intro i hi
      have h := metricIterationCount_backward Γ x B hx hB hΓ hbase i hi
      unfold metricCountFailure
      rw [mul_one_div]
      apply (div_le_div_iff₀ (mul_pos (by norm_num) (hpos i))
        (mul_pos (by norm_num) (hpos (i+1)))).2
      nlinarith)
  simpa only [mul_one_div] using hb

/-- δ_0 uses the original input size; every later δ_i uses the preceding
rounded sample count. This matches the indexing in Lemma 4.2. -/
def metricStageFailure (Γ x B : ℝ) (i : ℕ) : ℝ :=
  if i=0 then 1/(4*x) else metricCountFailure Γ x B (i-1)

theorem metricStageFailure_nonneg (Γ x B : ℝ) (hx : 0≤x) (i : ℕ) :
    0≤metricStageFailure Γ x B i := by
  unfold metricStageFailure
  split_ifs
  · positivity
  · exact metricCountFailure_nonneg Γ x B _

theorem metricStageFailure_sum (Γ x B : ℝ) (hx : 0<x)
    (hB : 8≤B) (hΓ : 0<Γ) (hbase : 1≤Γ*B^2) :
    (∑ i ∈ Finset.range (logStop x B),metricStageFailure Γ x B i) ≤
      1/(4*x)+3/(4*Γ*B^2) := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (logStop_pos x B))
  have he : (∑ i ∈ Finset.range (t+1),metricStageFailure Γ x B i) =
      (∑ i ∈ Finset.range t,metricCountFailure Γ x B i)+1/(4*x) := by
    rw [Finset.sum_range_succ']
    simp [metricStageFailure]
  rw [ht,he]
  have hsub : (∑ i ∈ Finset.range t,metricCountFailure Γ x B i) ≤
      ∑ i ∈ Finset.range (logStop x B),metricCountFailure Γ x B i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => metricCountFailure_nonneg Γ x B i)
  have hb := metricCountFailure_sum Γ x B hx hB hΓ hbase
  linarith

theorem metricStageFailure_half (Γ x B : ℝ) (hx : 1≤x)
    (hB : 8≤B) (hΓ : 0<Γ) (hbase : 3≤Γ*B^2) :
    (∑ i ∈ Finset.range (logStop x B),metricStageFailure Γ x B i) ≤ 1/2 := by
  have hb := metricStageFailure_sum Γ x B (by linarith) hB hΓ (by linarith)
  have hxbound : 1/(4*x)≤(1:ℝ)/4 :=
    (div_le_iff₀ (by positivity : 0<4*x)).2 (by linarith)
  have htail : 3/(4*Γ*B^2)≤(1:ℝ)/4 :=
    (div_le_iff₀ (by nlinarith : 0<4*Γ*B^2)).2 (by nlinarith)
  linarith

/-- The real iterated-log schedule supplies the complete deterministic
error budget. Local preservation events are the remaining hypotheses. -/
theorem metric_apc_log_schedule
    {I K X : Type*} [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [PseudoMetricSpace X]
    (x : I → X) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (N : ℝ) (hN : 0<N)
    (support : ℕ → Set X) (hnest : ∀ i,support (i+1)⊆support i)
    (c : ℕ → (K → X) → ℝ) (hc : ∀ s,0≤c 0 s)
    (opt s : K → X) (α ε : ℝ) (hα : 0≤α) (hε : 0≤ε) (hε1 : ε≤1)
    (hfinal : ∀ s,c (logStop N 14400) s=cost x w s)
    (hsupport : ∀ i,x i∈support (logStop N 14400))
    (hstep : ∀ i,i<logStop N 14400 → ∀ s,(∀ j,s j∈support i) ∨ s=opt →
      Preserves (c i s) (c (i+1) s) (logStageError N 14400 ε i))
    (happrox : Approximate (cost x w) α s) :
    ∃ f : K → I,c 0 (fun j=>x (f j))≤α*(4+ε)*c 0 opt := by
  exact metric_apc_of_iteration x w hw support hnest c hc opt s α ε hα hε hε1
    (logStageError N 14400 ε) (logStageError_nonneg N 14400 ε hε) (logStop N 14400)
    (logStageError_rescaled_budget N ε hN hε) hfinal hsupport hstep happrox

/-- A constant overall failure bound for fully adaptive sampling, provided
its conditional stage failures satisfy Algorithm 4's prescribed budgets. -/
theorem metric_adaptive_failure_half {Ω : Type*} [Fintype Ω]
    (q : (n : ℕ) → History Ω n → Ω → ℝ)
    (hq : ∀ n h ω,0≤q n h ω) (hqsum : ∀ n h,∑ ω,q n h ω=1)
    (good : (n : ℕ) → History Ω n → Ω → Prop)
    (Γ N B : ℝ) (hN : 1≤N) (hB : 8≤B) (hΓ : 0<Γ) (hbase : 3≤Γ*B^2)
    (hstage : ∀ n h,historyGood good n h →
      eventMass (q n h) (fun ω=>¬good n h ω)≤metricStageFailure Γ N B n) :
    eventMass (historyWeight q (logStop N B))
      (fun h=>¬historyGood good (logStop N B) h)≤1/2 :=
  (adaptive_failure_bound q hq hqsum good (metricStageFailure Γ N B)
    (metricStageFailure_nonneg Γ N B (by linarith)) hstage (logStop N B)).trans
      (metricStageFailure_half Γ N B hN hB hΓ hbase)

end APC
