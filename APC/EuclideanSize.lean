import APC.RandomizedCounts

open scoped BigOperators
noncomputable section
namespace APC

/-- Logarithmic budget for a first-stage cardinality at most
C k^p (1/ε)^q. It is independent of the original input cardinality. -/
def polynomialLogBudget (k : ℕ) (C : ℝ) (p q : ℕ) (ε δ : ℝ) : ℝ :=
  1+Real.log (8*(k:ℝ)/δ)+Real.log C+(p:ℝ)*Real.log k+(q:ℝ)*Real.log (1/ε)

def witnessCompressionCount (k B t : ℕ) (a ε δ : ℝ) : ℕ :=
  budgetSampleCount ((48*(k:ℝ))*Real.log (8*(k:ℝ)/δ))
    ((4*(64*a+8*a^2))*(Real.log (8/δ)+(t*k:ℕ)*Real.log B))
    ((ε/100)/(23+22*a))

def euclideanSizeEnvelope (k : ℕ) (a c C : ℝ) (p q : ℕ) (ε δ : ℝ) : ℝ :=
  10000*(23+22*a)^2*(48+(1+c)*(4*(64*a+8*a^2)))*(k:ℝ)*
    polynomialLogBudget k C p q ε δ/ε^3+2

theorem log_polynomial_cardinality (k B : ℕ) (C : ℝ) (p q : ℕ) (ε : ℝ)
    (hk : 0<k) (hB : 0<B) (hC : 1≤C) (hε : 0<ε)
    (hsize : (B:ℝ)≤C*(k:ℝ)^p*(1/ε)^q) :
    Real.log (B:ℝ) ≤ Real.log C+(p:ℝ)*Real.log k+(q:ℝ)*Real.log (1/ε) := by
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hCp : 0<C := by linarith
  have hep : 0<1/ε := by positivity
  have h := Real.log_le_log (Nat.cast_pos.mpr hB) hsize
  rw [Real.log_mul (ne_of_gt (mul_pos hCp (pow_pos hkp _)))
    (ne_of_gt (pow_pos hep _)),Real.log_mul (ne_of_gt hCp)
    (ne_of_gt (pow_pos hkp _)),Real.log_pow,Real.log_pow] at h
  exact h

theorem polynomialLogBudget_bounds (k B : ℕ) (C : ℝ) (p q : ℕ) (ε δ : ℝ)
    (hk : 0<k) (hB : 0<B) (hC : 1≤C) (hε : 0<ε) (hε1 : ε≤1)
    (hδ : 0<δ) (hδ1 : δ≤1) (hsize : (B:ℝ)≤C*(k:ℝ)^p*(1/ε)^q) :
    1≤polynomialLogBudget k C p q ε δ ∧
    Real.log (8*(k:ℝ)/δ)≤polynomialLogBudget k C p q ε δ ∧
    Real.log (8/δ)≤polynomialLogBudget k C p q ε δ ∧
    Real.log (B:ℝ)≤polynomialLogBudget k C p q ε δ := by
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hlogk : 0≤Real.log (k:ℝ) := Real.log_nonneg hkr
  have hlogC : 0≤Real.log C := Real.log_nonneg hC
  have hloge : 0≤Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).2 (by linarith))
  have hlogd : 0≤Real.log (8*(k:ℝ)/δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).2 (by nlinarith))
  have hpoly := log_polynomial_cardinality k B C p q ε hk hB hC hε hsize
  have hlog8 : Real.log (8/δ)≤Real.log (8*(k:ℝ)/δ) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  unfold polynomialLogBudget
  have hp : 0≤(p:ℝ)*Real.log k := mul_nonneg (Nat.cast_nonneg _) hlogk
  have hq : 0≤(q:ℝ)*Real.log (1/ε) := mul_nonneg (Nat.cast_nonneg _) hloge
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Exact inverse-cubic bound after substituting a supplied polynomial
first-stage size. This proves no first-stage construction. -/
theorem witnessCompressionCount_polynomial_bound
    (k B t : ℕ) (a c C : ℝ) (p q : ℕ) (ε δ : ℝ)
    (hk : 0<k) (hB : 0<B) (ha : 0<a) (hc : 0≤c) (hC : 1≤C)
    (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ≤1)
    (ht : (t:ℝ)≤c/ε) (hsize : (B:ℝ)≤C*(k:ℝ)^p*(1/ε)^q) :
    (witnessCompressionCount k B t a ε δ:ℝ) < euclideanSizeEnvelope k a c C p q ε δ := by
  let L := polynomialLogBudget k C p q ε δ
  let R := 4*(64*a+8*a^2)
  let D := 23+22*a
  have hL := polynomialLogBudget_bounds k B C p q ε δ hk hB hC hε hε1 hδ hδ1 hsize
  have hLp : 0≤L := by dsimp [L]; linarith [hL.1]
  have hRp : 0≤R := by dsimp [R]; positivity
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hratio : 1≤(k:ℝ)/ε := (le_div_iff₀ hε).2 (by linarith)
  have hlogB : 0≤Real.log (B:ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hlog8 : 0≤Real.log (8/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  let S := (48*(k:ℝ))*Real.log (8*(k:ℝ)/δ)
  let Q := R*(Real.log (8/δ)+(t*k:ℕ)*Real.log B)
  have hS : 0≤S := by
    dsimp [S]
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg ((le_div_iff₀ hδ).2 (by nlinarith [show (1:ℝ)≤k by exact_mod_cast hk]))
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have ht' : (t*k:ℕ)≤c*((k:ℝ)/ε) := by
    push_cast
    have hh := mul_le_mul_of_nonneg_right ht hkp.le
    calc
      (t:ℝ)*(k:ℝ)≤c/ε*(k:ℝ) := hh
      _=c*((k:ℝ)/ε) := by ring
  have htk := mul_le_mul_of_nonneg_right ht' hlogB
  have hBL := mul_le_mul_of_nonneg_left hL.2.2.2
    (mul_nonneg hc (div_nonneg hkp.le hε.le))
  have h8L := hL.2.2.1
  have hratioL := mul_le_mul_of_nonneg_right hratio hLp
  have hres : Q≤R*(1+c)*((k:ℝ)/ε)*L := by
    calc
      Q≤R*((1+c)*((k:ℝ)/ε)*L) := mul_le_mul_of_nonneg_left (by
        change Real.log (8/δ)+(t*k:ℕ)*Real.log B≤_
        nlinarith only [htk,hBL,h8L,hratioL]) hRp
      _=_ := by ring
  have hS0 := mul_le_mul_of_nonneg_left hL.2.1 (by positivity : 0≤48*(k:ℝ))
  have hS1 : (k:ℝ)≤(k:ℝ)/ε := (le_div_iff₀ hε).2 (by nlinarith)
  have hS2 := mul_le_mul_of_nonneg_right hS1 hLp
  have hsum : S+Q≤(48+(1+c)*R)*((k:ℝ)/ε)*L := by
    dsimp [S]
    nlinarith only [hS0,hS2,hres]
  have hz : (ε/100)/D≠0 := ne_of_gt (div_pos (by positivity) (by dsimp [D]; linarith))
  have hb := budgetSampleCount_upper S Q ((ε/100)/D) hS hQ hz
  have hscale : (S+Q)/((ε/100)/D)^2≤
      10000*D^2*(48+(1+c)*R)*(k:ℝ)*L/ε^3 := by
    have hdiv := div_le_div_of_nonneg_right hsum (sq_nonneg ((ε/100)/D))
    calc
      _ ≤ ((48+(1+c)*R)*((k:ℝ)/ε)*L)/((ε/100)/D)^2 := hdiv
      _ = _ := by field_simp; ring
  change (budgetSampleCount S Q ((ε/100)/D):ℝ)<_
  change (budgetSampleCount S Q ((ε/100)/D):ℝ)<
    10000*D^2*(48+(1+c)*R)*(k:ℝ)*L/ε^3+2
  linarith only [hb,hscale]

/-- Ceiling rounding for the means actually sampled by randomized lifting. -/
theorem liftingSampleCount_scaled_upper (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    (liftingSampleCount (ε/10):ℝ)≤32/ε := by
  have hh := Nat.ceil_lt_add_one (by positivity : 0≤3/(ε/10))
  have he : (liftingSampleCount (ε/10):ℝ)=(Nat.ceil (3/(ε/10)):ℝ)+1 := by simp [liftingSampleCount]
  rw [he]
  apply (le_div_iff₀ hε).2
  have h := (mul_lt_mul_of_pos_right hh hε)
  have hid : (3/(ε/10))*ε=30 := by field_simp; ring
  rw [add_mul,hid] at h
  nlinarith

/-- Deterministic-lifting compression count after a polynomial strong input. -/
theorem compressionSampleCount_polynomial_bound
    (k B : ℕ) (a C : ℝ) (p q : ℕ) (ε δ : ℝ)
    (hk : 0<k) (hB : 0<B) (ha : 0<a) (hC : 1≤C)
    (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ≤1)
    (hsize : (B:ℝ)≤C*(k:ℝ)^p*(1/ε)^q) :
    (compressionSampleCount k B a ε δ:ℝ)<euclideanSizeEnvelope k a 12 C p q ε δ :=
  witnessCompressionCount_polynomial_bound k B (meanSampleCount ε) a 12 C p q ε δ
    hk hB ha (by norm_num) hC hε hε1 hδ hδ1 (meanSampleCount_upper ε hε hε1) hsize

/-- Randomized-lifting compression count, with the larger actual witness
length and all ceiling roundings accounted for. -/
theorem randomizedCompressionSampleCount_polynomial_bound
    (k B : ℕ) (a C : ℝ) (p q : ℕ) (ε δ : ℝ)
    (hk : 0<k) (hB : 0<B) (ha : 0<a) (hC : 1≤C)
    (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ≤1)
    (hsize : (B:ℝ)≤C*(k:ℝ)^p*(1/ε)^q) :
    (randomizedCompressionSampleCount k B a ε δ:ℝ)<euclideanSizeEnvelope k a 32 C p q ε δ :=
  witnessCompressionCount_polynomial_bound k B (liftingSampleCount (ε/10)) a 32 C p q ε δ
    hk hB ha (by norm_num) hC hε hε1 hδ hδ1 (liftingSampleCount_scaled_upper ε hε hε1) hsize

end APC
