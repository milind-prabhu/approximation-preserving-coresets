import APC.FiniteProbability

open scoped BigOperators
noncomputable section
namespace APC

theorem eventMass_nonneg {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (e : Ω → Prop) : 0 ≤ eventMass p e := by
  classical
  unfold eventMass
  exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp_all)

theorem eventMass_mono {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (e f : Ω → Prop) (hef : ∀ ω, e ω → f ω) :
    eventMass p e ≤ eventMass p f := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro ω _
  split_ifs <;> simp_all

theorem eventMass_complement {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (h1 : ∑ ω, p ω = 1) (e : Ω → Prop) :
    eventMass p (fun ω => ¬e ω) = 1 - eventMass p e := by
  classical
  have h : eventMass p (fun ω => ¬e ω) + eventMass p e = ∑ ω, p ω := by
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases he : e ω <;> simp [he]
  linarith

theorem finite_union_bound {Ω K : Type*} [Fintype Ω] [Fintype K]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (bad : K → Ω → Prop) :
    eventMass p (fun ω => ∃ j, bad j ω) ≤ ∑ j, eventMass p (bad j) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ j, bad j ω
  · rw [if_pos h]
    obtain ⟨j, hj⟩ := h
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun k => if bad k ω then p ω else 0)
      (fun k _ => by dsimp; split_ifs <;> simp_all) (Finset.mem_univ j)
    simpa [hj] using hle
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp_all)

def allDraws {Ω : Type*} (bad : Ω → Prop) : (t : ℕ) → Draws Ω t → Prop
  | 0, _ => True
  | t+1, (ω, rest) => bad ω ∧ allDraws bad t rest

/-- Exact independent-repetition failure probability. Independence is
encoded by the product distribution, rather than left as an assumption. -/
theorem allDraws_mass {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (bad : Ω → Prop) (t : ℕ) :
    eventMass (drawWeight p t) (allDraws bad t) = (eventMass p bad)^t := by
  classical
  induction t with
  | zero => simp [eventMass, Draws, drawWeight, allDraws]
  | succ t ih =>
    unfold eventMass
    change (∑ a : Ω × Draws Ω t,
      if allDraws bad (t+1) a then drawWeight p (t+1) a else 0) = _
    rw [Fintype.sum_prod_type]
    simp only [drawWeight, allDraws]
    have he : ∀ ω, (∑ tail : Draws Ω t,
        if bad ω ∧ allDraws bad t tail then p ω * drawWeight p t tail else 0) =
        (if bad ω then p ω else 0) * eventMass (drawWeight p t) (allDraws bad t) := by
      intro ω
      unfold eventMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      by_cases h : bad ω <;> by_cases ht : allDraws bad t tail <;> simp [h, ht]
    simp_rw [he]
    rw [← Finset.sum_mul, ih, pow_succ]
    change eventMass p bad * eventMass p bad ^ t = _
    unfold eventMass
    ring

/-- Union over clusters does not require independence between clusters. -/
theorem amplified_cluster_failure {Ω K : Type*} [Fintype Ω] [Fintype K]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (bad : K → Ω → Prop)
    (t : ℕ) (hbad : ∀ j, eventMass p (bad j) ≤ (1/3:ℝ)^t)
    (ht : (Fintype.card K : ℝ) * (1/3:ℝ)^t ≤ 1/3) :
    eventMass p (fun ω => ∃ j, bad j ω) ≤ 1/3 := by
  calc
    _ ≤ ∑ j, eventMass p (bad j) := finite_union_bound p hp bad
    _ ≤ ∑ _j : K, (1/3:ℝ)^t := Finset.sum_le_sum (fun j _ => hbad j)
    _ = (Fintype.card K : ℝ) * (1/3:ℝ)^t := by simp
    _ ≤ 1/3 := ht

end APC
