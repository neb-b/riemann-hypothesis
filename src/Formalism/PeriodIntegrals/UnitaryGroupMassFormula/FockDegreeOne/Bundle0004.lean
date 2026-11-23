module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.HighestWeightExists
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.HwC


open Classical in
theorem exists_wtvec {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s))
    (hU : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U) :
    ∀ (n : ℕ) (u : Pol p q r s), u ∈ U → u ≠ 0 → (u.support.image wtv).card ≤ n →
      ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ v ≠ 0 ∧ IsWt ν v ∧ v.support ⊆ u.support := by
  intro n
  induction n with
  | zero =>
    intro u _ hu0 hcard
    exfalso
    apply hu0
    have h0 := Nat.le_zero.1 hcard
    rw [Finset.card_eq_zero, Finset.image_eq_empty] at h0
    exact MvPolynomial.support_eq_empty.1 h0
  | succ n ih =>
    intro u hu hu0 hcard
    by_cases hall : ∀ β₁ ∈ u.support, ∀ β₂ ∈ u.support, wtv β₁ = wtv β₂
    · obtain ⟨β₀, hβ₀⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hu0 (MvPolynomial.support_eq_empty.1 h))
      exact ⟨wtv β₀, u, hu, hu0, fun β hβ c => by rw [hall β hβ β₀ hβ₀], subset_rfl⟩
    · push_neg at hall
      obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := hall
      obtain ⟨c, hc⟩ := Function.ne_iff.1 hne

      have hcoeff : ∀ β, AddMonoidAlgebra.coeff (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) β =
          (((wtv β c : ℚ) : ℂ) - ((wtv β₁ c : ℚ) : ℂ)) * AddMonoidAlgebra.coeff u β := by
        intro β
        rw [coeff_sub, coeff_Ecc, coeff_smul, smul_eq_mul]
        ring
      have hsub : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support ⊆ u.support := by
        intro β hβ
        rw [MvPolynomial.mem_support_iff] at hβ ⊢
        intro h0
        apply hβ
        rw [hcoeff, h0, mul_zero]
      have hmem : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ∈ U :=
        U.sub_mem (hU c u hu) (U.smul_mem _ hu)
      have hβ₂ : β₂ ∈ (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        refine mul_ne_zero ?_ (MvPolynomial.mem_support_iff.1 h₂)
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hc)
      have hne0 : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ≠ 0 := by
        intro h
        rw [h, MvPolynomial.support_zero] at hβ₂
        simp at hβ₂
      have himg : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv ⊆
          (u.support.image wtv).erase (wtv β₁) := by
        intro w hw
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hw
        refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_image_of_mem _ (hsub hβ)⟩
        have h0 : AddMonoidAlgebra.coeff (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) β = 0 := by
          rw [hcoeff, heq, sub_self, zero_mul]
        exact (MvPolynomial.mem_support_iff.1 hβ) h0
      have hcard' : ((fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv).card ≤ n := by
        have h1 := Finset.card_le_card himg
        have h2 := Finset.card_erase_of_mem (Finset.mem_image_of_mem wtv h₁)
        omega
      obtain ⟨ν, v, hv, hv0, hvw, hvs⟩ := ih _ hmem hne0 hcard'
      exact ⟨ν, v, hv, hv0, hvw, hvs.trans hsub⟩

theorem exists_cover {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ U] :
    ∃ S : Finset (Ln p q r s →₀ ℕ), ∀ u ∈ U, u.support ⊆ S := by
  classical
  let bs := Module.finBasis ℂ U
  refine ⟨Finset.univ.biUnion fun k => ((bs k : U) : Pol p q r s).support, fun u hu => ?_⟩
  have e : (⟨u, hu⟩ : U) = ∑ k, (bs.repr ⟨u, hu⟩ k) • bs k := (bs.sum_repr _).symm
  have e' : u = ∑ k, (bs.repr ⟨u, hu⟩ k) • ((bs k : U) : Pol p q r s) := by
    have h := congrArg Subtype.val e
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    exact h
  rw [e']
  exact MvPolynomial.support_sum.trans (Finset.biUnion_mono fun k _ => MvPolynomial.support_smul)

def tw {p q : ℕ} : Ix p q → ℚ
  | .inl i => -((i : ℕ) : ℚ)
  | .inr j => -((j : ℕ) : ℚ)

def fw {p q : ℕ} (ν : Ix p q → ℚ) : ℚ := ∑ c, tw c * ν c

theorem fw_shift {p q : ℕ} (ν : Ix p q → ℚ) (a b : Ix p q) :
    fw (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) =
      fw ν + tw a - tw b := by
  unfold fw
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem posC_facts {p q : ℕ} {a b : Ix p q} (h : posC a b) :
    sameBlock a b ∧ a ≠ b ∧ tw b < tw a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inl.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inr.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')

end PI.FockOneDegW.HwC

namespace PI.FockOneDegW

open HwC

open Classical in
theorem hwExist : HwExist := by
  intro p q r s U hfd hU0 hstab
  haveI := hfd
  obtain ⟨S, hS⟩ := exists_cover U
  have hdiag : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U :=
    fun c => hstab c c (by cases c <;> trivial)

  have hwtS : ∀ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U → v ≠ 0 → IsWt ν v → ν ∈ S.image wtv := by
    intro ν v hv hv0 hw
    obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hv0 (MvPolynomial.support_eq_empty.1 h))
    exact Finset.mem_image.2 ⟨β, hS v hv hβ, funext fun c => hw β hβ c⟩
  have hT : ((S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v)).Nonempty := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨ν, v, hv, hv0, hvw, -⟩ := exists_wtvec U hdiag _ u hu hu0 le_rfl
    exact ⟨ν, Finset.mem_filter.2 ⟨hwtS ν v hv hv0 hvw, v, hv, hv0, hvw⟩⟩

  obtain ⟨ν₀, hν₀, hmax⟩ := Finset.exists_max_image _ fw hT
  obtain ⟨-, v, hv, hv0, hvw⟩ := Finset.mem_filter.1 hν₀
  refine ⟨ν₀, v, hv, ?_⟩
  unfold IsHW hwSub
  refine ⟨hv0, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    intro a
    rw [Ecc_of_wt hvw a, sub_self]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    obtain ⟨hsame, hne, htw⟩ := posC_facts hab
    by_contra hw0
    have hwU := hstab a b hsame v hv
    have hw' := wt_Eab_of hvw a b hsame hne
    have hmemT : (fun c => ν₀ c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) ∈
        (S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v) :=
      Finset.mem_filter.2 ⟨hwtS _ _ hwU hw0 hw', _, hwU, hw0, hw'⟩
    have h1 := hmax _ hmemT
    rw [fw_shift] at h1
    linarith

end PI.FockOneDegW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KernelHarmonic
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_Xd (c d : Ix r s) (l l' : Ln p q r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (X l * pderiv l' P) =
      X l * pderiv l' (lowOp (p := p) (q := q) c d P) +
      ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
        ((if ((a, d) : Ln p q r s) = l then pderiv ((a, c) : Ln p q r s) (pderiv l' P) else 0) +
         (if ((a, c) : Ln p q r s) = l then pderiv ((a, d) : Ln p q r s) (pderiv l' P) else 0))
        else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : linePos ((a, d) : Ln p q r s) = true
  · simp only [h, ↓reduceIte]
    have hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) =
        pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P)) := by
      rw [PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P,
        PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]
    rw [dd_X_mul, hc]
    abel
  · simp [h]

theorem sum_rows (c d e : Ix r s) (a : Ix p q) (F G : Ix p q → Pol p q r s) :
    ∑ a' : Ix p q, (if linePos ((a', d) : Ln p q r s) = true then
      ((if ((a', d) : Ln p q r s) = (a, e) then F a' else 0) +
       (if ((a', c) : Ln p q r s) = (a, e) then G a' else 0)) else 0) =
    if linePos ((a, d) : Ln p q r s) = true then
      ((if d = e then F a else 0) + (if c = e then G a else 0)) else 0 := by
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro b _ hb
    simp [Prod.mk.injEq, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem not_both (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False :=
  hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))

theorem lowOp_posOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (posOp a b P) =
      posOp a b (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [posOp_apply, posOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) P else 0) =
      (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P) else 0) +
      (if linePos ((a, e) : Ln p q r s) = true then
        (if linePos ((a, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((a, c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((a, d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0))
          else 0) else 0) := by
    intro e
    by_cases h : linePos ((a, e) : Ln p q r s) = true
    · simp only [h, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e a (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))]
    · simp [h]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single d]
  · by_cases h : linePos ((a, d) : Ln p q r s) = true
    · simp [h, hcd']
    · simp [h]
  · intro e _ hed
    by_cases h1 : linePos ((a, e) : Ln p q r s) = true
    · by_cases h2 : linePos ((a, d) : Ln p q r s) = true
      · have hce : c ≠ e := by
          rintro rfl; exact not_both c d hcd a h1 h2
        simp [h1, h2, Ne.symm hed, hce]
      · simp [h1, h2]
    · simp [h1]
  · simp

theorem lowOp_negOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (hab : sameBlock a b)
    (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (negOp b a P) =
      negOp b a (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  have hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s) :=
    (FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [negOp_apply, negOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) =
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) +
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        (if linePos ((b, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((b, c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((b, d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0))
          else 0)) := by
    intro e
    by_cases h : linePos ((b, e) : Ln p q r s) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases h : linePos ((b, d) : Ln p q r s) = true
    · have hbc : linePos ((b, c) : Ln p q r s) = false := by
        cases h' : linePos ((b, c) : Ln p q r s)
        · rfl
        · exact (not_both c d hcd b h' h).elim
      rw [← hba]
      simp [h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]
    · rw [← hba]
      simp [h]
  · intro e _ hec
    by_cases h1 : linePos ((b, e) : Ln p q r s) = true
    · simp [h1]
    · by_cases h2 : linePos ((b, d) : Ln p q r s) = true
      · have hde : d ≠ e := by
          rintro rfl; exact h1 h2
        simp [h1, h2, hde, Ne.symm hec]
      · simp [h1, h2]
  · simp

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem kernel_harmonic : KHarm := by
  intro p q r s a b hab P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  rw [fock_operators_kernel p q r s a b hab]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add (f := _), map_sub, lowOp_posOp c d hcd,
    lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]
  split_ifs <;> simp [hP c d hcd]

end PI.FockOneDegW
end
end

