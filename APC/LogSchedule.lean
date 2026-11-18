import APC.Iteration
import APC.SampleCounts

open scoped BigOperators
noncomputable section
namespace APC
attribute [local instance] Classical.propDecidable

def iteratedLog (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => Real.log (iteratedLog x n)

def logLevel (x B : ℝ) (i : ℕ) : ℝ := max (iteratedLog x (i+1)) B

/-- The stopping set in Algorithm 4 is nonempty. The crude ceiling bound is
used only to prove termination, not as an estimate of the log-star runtime. -/
theorem iteratedLog_stops (x B : ℝ) (hx : 0<x) (hB : 1≤B) :
    ∃ i : ℕ, iteratedLog x (i+1) ≤ B := by
  by_contra h
  push_neg at h
  have hb : ∀ i, iteratedLog x i ≤ x-(i:ℝ) := by
    intro i
    induction i with
    | zero => simp [iteratedLog]
    | succ i ih =>
      have hpos : 0 < iteratedLog x i := by
        cases i with
        | zero => exact hx
        | succ j => exact lt_trans (by linarith : 0<B) (h j)
      have hl := Real.log_le_sub_one_of_pos hpos
      change Real.log (iteratedLog x i) ≤ x-((i+1:ℕ):ℝ)
      push_cast
      linarith
  have hc := Nat.le_ceil x
  have hh := hb (Nat.ceil x+1)
  have hn := h (Nat.ceil x)
  push_cast at hh
  linarith

/-- Least positive stopping index, with a total definition for all inputs. -/
def logStop (x B : ℝ) : ℕ :=
  if h : ∃ i : ℕ, iteratedLog x (i+1) ≤ B then Nat.find h+1 else 1

theorem logStop_pos (x B : ℝ) : 0<logStop x B := by
  unfold logStop
  split_ifs <;> omega

theorem logStop_spec (x B : ℝ) (hx : 0<x) (hB : 1≤B) :
    iteratedLog x (logStop x B) ≤ B := by
  have h := iteratedLog_stops x B hx hB
  simpa only [logStop, dif_pos h] using Nat.find_spec h

theorem logStop_minimal (x B : ℝ) (hx : 0<x) (hB : 1≤B)
    (i : ℕ) (hi : 0 < i) (hit : i < logStop x B) : B < iteratedLog x i := by
  have h := iteratedLog_stops x B hx hB
  simp only [logStop, dif_pos h] at hit
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact lt_of_not_ge (Nat.find_min h (by omega))

theorem logLevel_lower (x B : ℝ) (i : ℕ) : B≤logLevel x B i := le_max_right _ _

theorem logLevel_terminal (x B : ℝ) (hx : 0<x) (hB : 1≤B) :
    logLevel x B (logStop x B-1)=B := by
  unfold logLevel
  have ht := logStop_pos x B
  rw [Nat.sub_add_cancel ht]
  exact max_eq_right (logStop_spec x B hx hB)

/-- Before the last pair, levels grow at least fourfold when read backwards.
The last transition is excluded because the terminal level is clamped to B. -/
theorem logLevel_backward_growth (x B : ℝ) (hx : 0<x) (hB : 8≤B)
    (i : ℕ) (hi : i+2<logStop x B) :
    4*logLevel x B (i+1) ≤ logLevel x B i := by
  have hprev := logStop_minimal x B hx (by linarith) (i+1) (by omega) (by omega)
  have hnext := logStop_minimal x B hx (by linarith) (i+2) (by omega) hi
  have hprevpos : 0 < iteratedLog x (i+1) := by linarith
  have hexp := Real.quadratic_le_exp_of_nonneg (by linarith : 0≤ iteratedLog x (i+2))
  have hid : Real.exp (iteratedLog x (i+2))=iteratedLog x (i+1) := by
    change Real.exp (Real.log (iteratedLog x (i+1)))=_
    exact Real.exp_log hprevpos
  rw [hid] at hexp
  have hquad := mul_nonneg (by linarith : 0≤ iteratedLog x (i+2))
    (by linarith : 0≤ iteratedLog x (i+2)-8)
  simp only [logLevel, show i+1+1=i+2 by omega,
    max_eq_left hprev.le, max_eq_left hnext.le]
  nlinarith

/-- A reverse geometric series, without converting to a logarithmic index. -/
theorem reverse_geometric_sum (f : ℕ → ℝ) (hf : ∀ i,0≤f i) (n : ℕ)
    (hcontract : ∀ i,i<n → 2*f i≤f (i+1)) :
    (∑ i ∈ Finset.range (n+1),f i)≤2*f n := by
  induction n with
  | zero => simpa using (by linarith [hf 0] : f 0≤2*f 0)
  | succ n ih =>
    have hsum := ih (fun i hi=>hcontract i (Nat.lt_succ_of_lt hi))
    rw [Finset.sum_range_succ]
    linarith [hcontract n (Nat.lt_succ_self n)]

/-- At most one terminal transition need fail the geometric contraction. -/
theorem terminal_geometric_sum (f : ℕ → ℝ) (hf : ∀ i,0≤f i)
    (n : ℕ) (c : ℝ) (hc : 0≤c) (hbound : ∀ i,i<n → f i≤c)
    (hcontract : ∀ i,i+2<n → 2*f i≤f (i+1)) :
    (∑ i ∈ Finset.range n,f i)≤3*c := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    cases n with
    | zero => simpa using (by linarith [hbound 0 (by omega)] : f 0≤3*c)
    | succ n =>
      have hsum := reverse_geometric_sum f hf n (fun i hi => hcontract i (by omega))
      rw [Finset.sum_range_succ]
      have hlast := hbound (n+1) (by omega)
      have hpenult := hbound n (by omega)
      linarith

theorem inverse_sqrt_contraction (u v : ℝ) (hu : 0<u) (hv : 0<v)
    (hgrowth : 4*v≤u) : 2/(Real.sqrt u)≤1/(Real.sqrt v) := by
  have hsu := Real.sqrt_pos.mpr hu
  have hsv := Real.sqrt_pos.mpr hv
  have hu2 := Real.sq_sqrt hu.le
  have hv2 := Real.sq_sqrt hv.le
  have hs : 2*Real.sqrt v≤Real.sqrt u := by nlinarith
  apply (div_le_div_iff₀ hsu hsv).2
  simpa using hs

/-- The actual inverse-square-root schedule has bounded total error,
independently of the input size and number of iterations. -/
theorem logSchedule_sum (x B : ℝ) (hx : 0<x) (hB : 8≤B) :
    (∑ i ∈ Finset.range (logStop x B),1/Real.sqrt (logLevel x B i))≤3/Real.sqrt B := by
  have hBpos : 0<B := by linarith
  have hlevel : ∀ i,0<logLevel x B i := fun i=>lt_of_lt_of_le hBpos (logLevel_lower x B i)
  have hb := terminal_geometric_sum (fun i=>1/Real.sqrt (logLevel x B i))
    (fun i=>by positivity) (logStop x B) (1/Real.sqrt B) (by positivity)
    (fun i _ => one_div_le_one_div_of_le (Real.sqrt_pos.mpr hBpos)
      (Real.sqrt_le_sqrt (logLevel_lower x B i))) (by
      intro i hi
      simpa only [mul_one_div] using inverse_sqrt_contraction
        (logLevel x B i) (logLevel x B (i+1)) (hlevel i) (hlevel (i+1))
        (logLevel_backward_growth x B hx hB i hi))
  simpa only [mul_one_div] using hb

def logStageError (x B ε : ℝ) (i : ℕ) : ℝ := ε/Real.sqrt (logLevel x B i)

theorem logStageError_nonneg (x B ε : ℝ) (hε : 0≤ε) (i : ℕ) :
    0≤logStageError x B ε i := div_nonneg hε (Real.sqrt_nonneg _)

theorem logStageError_budget (x B ε : ℝ) (hx : 0<x) (hB : 8≤B) (hε : 0≤ε) :
    errorBudget (logStageError x B ε) (logStop x B) ≤ 3*ε/Real.sqrt B := by
  calc
    _ = ε*(∑ i ∈ Finset.range (logStop x B),1/Real.sqrt (logLevel x B i)) := by
      simp [errorBudget,logStageError,Finset.mul_sum,div_eq_mul_inv]
    _ ≤ ε*(3/Real.sqrt B) := mul_le_mul_of_nonneg_left (logSchedule_sum x B hx hB) hε
    _ = _ := by ring

/-- A concrete rescaling sufficient for the final (4+ε) transfer.
B=14400 is deliberately conservative and is not an optimized constant. -/
theorem logStageError_rescaled_budget (x ε : ℝ) (hx : 0<x) (hε : 0≤ε) :
    errorBudget (logStageError x 14400 ε) (logStop x 14400) ≤ ε/40 := by
  have h := logStageError_budget x 14400 ε hx (by norm_num) hε
  have hs : Real.sqrt (14400:ℝ)=120 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0≤(14400:ℝ)), Real.sqrt_nonneg (14400:ℝ)]
  rw [hs] at h
  linarith

end APC
