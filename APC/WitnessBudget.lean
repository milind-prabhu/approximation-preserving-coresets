import APC.Witnesses
import APC.SamplingBudgets

noncomputable section
namespace APC

theorem log_solution_count (N B d : ℕ) (hN : 0<N) (hB : 0<B)
    (hcount : N≤B^d+1) (δ : ℝ) (hδ : 0<δ) :
    Real.log (2*(N:ℝ)/δ)≤Real.log (4/δ)+(d:ℝ)*Real.log B := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hBR : (0:ℝ)<B := by exact_mod_cast hB
  have hB1 : (1:ℝ)≤B := by exact_mod_cast hB
  have hc : (N:ℝ)≤(B:ℝ)^d+1 := by exact_mod_cast hcount
  have hp : (1:ℝ)≤(B:ℝ)^d := one_le_pow₀ hB1
  have hratio : 2*(N:ℝ)/δ≤(4/δ)*(B:ℝ)^d := by
    apply (div_le_iff₀ hδ).2
    field_simp
    nlinarith only [hc,hp]
  calc
    _≤Real.log ((4/δ)*(B:ℝ)^d) := Real.log_le_log (by positivity) hratio
    _=_ := by rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]

/-- Concrete logarithmic budget from the m-point-mean witness count.
It exposes the k*m factor responsible for ε^-3 in Euclidean APCs. -/
theorem witness_family_budget
    {B K E : Type*} [Fintype B] [Fintype K] [DecidableEq E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : B → E) (t : ℕ) (opt : K → E) (hB : 0<Fintype.card B)
    (D ε δ : ℝ) (hD : 0≤D) (hδ : 0<δ) (m : ℕ)
    (hsize : D*(Real.log (4/δ)+(t*Fintype.card K:ℕ)*Real.log (Fintype.card B))≤(m:ℝ)*ε^2) :
    D*Real.log (2*((insert opt (witnessFamily (K := K) b t)).card:ℝ)/δ)≤(m:ℝ)*ε^2 := by
  have hN : 0<(insert opt (witnessFamily (K := K) b t)).card := Finset.card_pos.mpr
    ⟨opt,Finset.mem_insert_self _ _⟩
  have hc := log_solution_count (insert opt (witnessFamily (K := K) b t)).card (Fintype.card B)
    (t*Fintype.card K) hN hB (card_witnessFamily_with_opt b t opt) δ hδ
  exact (mul_le_mul_of_nonneg_left hc hD).trans hsize

end APC
