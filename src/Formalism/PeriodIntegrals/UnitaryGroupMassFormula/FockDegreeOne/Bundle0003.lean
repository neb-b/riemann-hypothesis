module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.CoeffXMulPderivSelf
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.HwC

def sgnL {p q r s : ℕ} (l : Ln p q r s) : ℚ := if linePos l = true then 1 else -1

def wtv {p q r s : ℕ} (β : Ln p q r s →₀ ℕ) (c : Ix p q) : ℚ :=
  ∑ d : Ix r s, sgnL ((c, d) : Ln p q r s) * (β (c, d) : ℚ) + kShift r s c

theorem coeff_X_mul_pderiv_self {σ : Type*} (l : σ) (P : MvPolynomial σ ℂ) (β : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (X l * pderiv l P) β = (β l : ℂ) * AddMonoidAlgebra.coeff P β := by
  classical
  rw [coeff_X_mul']
  by_cases h : l ∈ β.support
  · rw [if_pos h, coeff_pderiv]
    have h1 : 1 ≤ β l := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
    have hle : Finsupp.single l 1 ≤ β := Finsupp.single_le_iff.mpr h1
    rw [tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same, mul_comm]
    congr 1
    rw [Nat.cast_sub h1]
    push_cast
    ring
  · rw [if_neg h]
    have h0 : β l = 0 := by simpa [Finsupp.mem_support_iff] using h
    simp [h0]

theorem coeff_X_mul_pderiv_ne {σ : Type*} (l l' : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ)
    (h : AddMonoidAlgebra.coeff (X l * pderiv l' P) γ ≠ 0) :
    ∃ β ∈ P.support, β + Finsupp.single l 1 = γ + Finsupp.single l' 1 := by
  classical
  rw [coeff_X_mul'] at h
  by_cases hs : l ∈ γ.support
  · rw [if_pos hs, coeff_pderiv] at h
    refine ⟨γ - Finsupp.single l 1 + Finsupp.single l' 1, ?_, ?_⟩
    · rw [mem_support_iff]
      exact left_ne_zero_of_mul h
    · have hle : Finsupp.single l 1 ≤ γ :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
      rw [add_right_comm, tsub_add_cancel_of_le hle]
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem wtv_add {p q r s : ℕ} (β γ : Ln p q r s →₀ ℕ) (c : Ix p q) :
    wtv (β + γ) c = wtv β c + wtv γ c - kShift r s c := by
  unfold wtv
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  ring

theorem wtv_single {p q r s : ℕ} (l : Ln p q r s) (c : Ix p q) :
    wtv (Finsupp.single l 1) c = (if l.1 = c then sgnL l else 0) + kShift r s c := by
  unfold wtv
  congr 1
  have key : ∀ d : Ix r s, sgnL ((c, d) : Ln p q r s) * ((Finsupp.single l 1 ((c, d) : Ln p q r s) : ℕ) : ℚ) =
      if d = l.2 ∧ l.1 = c then sgnL l else 0 := by
    intro d
    by_cases h1 : d = l.2 ∧ l.1 = c
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · rw [if_neg h1]
      have hne : l ≠ ((c, d) : Ln p q r s) := fun he => h1 ⟨by rw [he], by rw [he]⟩
      simp [Finsupp.single_apply, hne]
  simp_rw [key]
  by_cases h : l.1 = c <;> simp [h]

theorem wtv_shift {p q r s : ℕ} (l l' : Ln p q r s) (β γ : Ln p q r s →₀ ℕ)
    (h : β + Finsupp.single l 1 = γ + Finsupp.single l' 1) (c : Ix p q) :
    wtv γ c = wtv β c + (if l.1 = c then sgnL l else 0) - (if l'.1 = c then sgnL l' else 0) := by
  have h1 := wtv_add β (Finsupp.single l 1) c
  have h2 := wtv_add γ (Finsupp.single l' 1) c
  rw [h] at h1
  rw [h2, wtv_single, wtv_single] at h1
  linarith

theorem sameBlock_refl' {p q : ℕ} (c : Ix p q) : sameBlock c c := by
  cases c <;> trivial

theorem coeff_Ecc {p q r s : ℕ} (c : Ix p q) (P : Pol p q r s) (β : Ln p q r s →₀ ℕ) :
    AddMonoidAlgebra.coeff (fockAct1 p q r s (Eab c c) P) β = ((wtv β c : ℚ) : ℂ) * AddMonoidAlgebra.coeff P β := by
  classical
  have hline : ∀ l : Ln p q r s, AddMonoidAlgebra.coeff (omE l l P) β =
      (((sgnL l * β l + sgnL l / 2 : ℚ)) : ℂ) * AddMonoidAlgebra.coeff P β := by
    intro l
    by_cases hl : linePos l = true
    · simp only [omE, raiB, lowB, hl, if_true, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.mulLeft_apply, Derivation.coeFn_coe, LinearMap.smul_apply,
        Module.End.one_apply, MvPolynomial.coeff_add, coeff_smul, smul_eq_mul, coeff_X_mul_pderiv_self, sgnL]
      push_cast
      ring
    · have hl' : linePos l = false := by simpa using hl
      have e : AddMonoidAlgebra.coeff (pderiv l (X l * P)) β = ((β l : ℂ) + 1) * AddMonoidAlgebra.coeff P β := by
        rw [coeff_pderiv, add_comm β, coeff_X_mul, mul_comm]
      simp only [omE, raiB, lowB, hl', Bool.false_eq_true, if_false, if_true, LinearMap.add_apply,
        Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe,
        LinearMap.smul_apply, Module.End.one_apply, MvPolynomial.coeff_add, coeff_neg, coeff_smul, smul_eq_mul, e, sgnL]
      push_cast
      ring
  rw [fockAct1_Eab_apply, coeff_sum]
  simp_rw [hline]
  rw [← Finset.sum_mul]
  congr 1
  unfold wtv
  push_cast
  rw [Finset.sum_add_distrib]
  congr 1
  cases c with
  | inl i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring
  | inr i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring

theorem wt_Eab {p q r s : ℕ} (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b)
    (P : Pol p q r s) (γ : Ln p q r s →₀ ℕ) (hγ : γ ∈ (fockAct1 p q r s (Eab a b) P).support) :
    ∃ β ∈ P.support, ∀ c, wtv γ c =
      wtv β c + (if a = c then 1 else 0) - (if b = c then 1 else 0) := by
  classical
  rw [fockAct1_Eab_apply, mem_support_iff, coeff_sum] at hγ
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  have hne' : ((a, d) : Ln p q r s) ≠ (b, d) := fun h => hne (Prod.ext_iff.mp h).1
  have hpos : linePos ((a, d) : Ln p q r s) = linePos ((b, d) : Ln p q r s) := by
    cases a <;> cases b <;> cases d <;> simp_all [sameBlock, linePos]
  simp only [omE, if_neg hne', add_zero, Module.End.mul_apply] at hd
  by_cases hl : linePos ((a, d) : Ln p q r s) = true
  · have hl2 : linePos ((b, d) : Ln p q r s) = true := hpos ▸ hl
    simp only [raiB, lowB, hl, hl2, if_true, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe] at hd
    obtain ⟨β, hβ, hsum⟩ := coeff_X_mul_pderiv_ne _ _ P γ hd
    refine ⟨β, hβ, fun c => ?_⟩
    rw [wtv_shift _ _ β γ hsum c]
    simp [sgnL, hl, hl2]
  · have hl1 : linePos ((a, d) : Ln p q r s) = false := by simpa using hl
    have hl2 : linePos ((b, d) : Ln p q r s) = false := hpos ▸ hl1
    have e : pderiv ((a, d) : Ln p q r s) (X ((b, d) : Ln p q r s) * P) =
        X ((b, d) : Ln p q r s) * pderiv ((a, d) : Ln p q r s) P := by
      rw [Derivation.leibniz, pderiv_X, Pi.single_apply, if_neg hne'.symm]
      simp [mul_comm]
    simp only [raiB, lowB, hl1, hl2, Bool.false_eq_true, if_false, LinearMap.mulLeft_apply,
      LinearMap.neg_apply, Derivation.coeFn_coe, e, coeff_neg, ne_eq, neg_eq_zero] at hd
    obtain ⟨β, hβ, hsum⟩ := coeff_X_mul_pderiv_ne _ _ P γ hd
    refine ⟨β, hβ, fun c => ?_⟩
    rw [wtv_shift _ _ β γ hsum c]
    simp [sgnL, hl1, hl2]
    split_ifs <;> ring

def IsWt {p q r s : ℕ} (ν : Ix p q → ℚ) (P : Pol p q r s) : Prop :=
  ∀ β ∈ P.support, ∀ c, wtv β c = ν c

theorem Ecc_of_wt {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P) (c : Ix p q) :
    fockAct1 p q r s (Eab c c) P = ((ν c : ℚ) : ℂ) • P := by
  ext β
  rw [coeff_Ecc, coeff_smul, smul_eq_mul]
  by_cases hβ : β ∈ P.support
  · rw [hP β hβ c]
  · have h0 : AddMonoidAlgebra.coeff P β = 0 := by simpa [mem_support_iff] using hβ
    rw [h0, mul_zero, mul_zero]

theorem wt_Eab_of {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P)
    (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b) :
    IsWt (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0))
      (fockAct1 p q r s (Eab a b) P) := by
  intro γ hγ c
  obtain ⟨β, hβ, h⟩ := wt_Eab a b hab hne P γ hγ
  rw [h c, hP β hβ c]

end PI.FockOneDegW.HwC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedOps
section
noncomputable section

open Matrix FockH1Action MvPolynomial FockRaiseLowInner

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_apply (c d : Ix r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d P = ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
      pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P) else 0) := by
  unfold lowOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl

theorem hc_lowOp (c d : Ix r s) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (lowOp (p := p) (q := q) c d P) =
      lowOp (p := p) (q := q) c d (homogeneousComponent (e + 2) P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lowOp_apply, lowOp_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [FockRL.hc_pderiv, FockRL.hc_pderiv]
  · exact map_zero _

theorem hc_comm_of_homog {σ : Type} (T : Module.End ℂ (MvPolynomial σ ℂ))
    (hT : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → T P ∈ homog σ d) (e : ℕ)
    (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (T P) = T (homogeneousComponent e P) := by
  have key : ∀ d, homogeneousComponent e (T (homogeneousComponent d P)) =
      if e = d then T (homogeneousComponent d P) else 0 := fun d =>
    homogeneousComponent_of_mem (hT d _ ((mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous d P)))
  conv_lhs => rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [key]
  rw [Finset.sum_ite_eq]
  split_ifs with he
  · rfl
  · simp only [Finset.mem_range, not_lt] at he
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem inner_posOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (posOp a b Q) = fockInner (posOp b a P) Q := by
  rw [posOp_apply, posOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_mul_X, fockInner_X_mul]
  · rw [fockInner_zero_right, fockInner_zero_left]

theorem inner_negOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (negOp a b Q) = fockInner (negOp b a P) Q := by
  rw [negOp_apply, negOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_zero_right, fockInner_zero_left]
  · rw [fockInner_mul_X, fockInner_X_mul]

theorem dd_X_mul (m m' l : Ln p q r s) (Q : Pol p q r s) :
    pderiv m (pderiv m' (X l * Q)) = X l * pderiv m (pderiv m' Q) +
      (if m' = l then pderiv m Q else 0) + (if m = l then pderiv m' Q else 0) := by
  classical
  by_cases h1 : m' = l <;> by_cases h2 : m = l <;>
    simp [h1, h2, Derivation.leibniz, pderiv_X, Pi.single_apply, eq_comm] <;> ring

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem harmonic_submodule : HarmSub := by
  intro p q r s
  refine ⟨?_, ?_, ?_⟩
  · rw [harmIff]; intro c d _; exact map_zero _
  · intro P Q hP hQ
    rw [harmIff] at hP hQ ⊢
    intro c d hcd
    rw [map_add (f := _), hP c d hcd, hQ c d hcd, add_zero]
  · intro k P hP
    rw [harmIff] at hP ⊢
    intro c d hcd
    rw [map_smul, hP c d hcd, smul_zero]

theorem highest_weight_harmonic : HcHarm := by
  intro p q r s e P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  apply FockRaiseLowGrade.eq_zero_of_hc
  intro e'
  rw [hc_lowOp, FockRaiseLowGrade.hc_hc]
  split_ifs with h
  · subst h
    rw [← hc_lowOp, hP c d hcd, map_zero]
  · exact map_zero _

theorem kernel_highest_weight : KHc := by
  intro p q r s a b hab e P
  refine hc_comm_of_homog _ (fun d P hP => ?_) e P
  have hKC : IsKC (Eab a b) := by
    intro x y hxy
    simp only [Eab, Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd hab hxy
    · rfl
  exact (gradedOscillatorProperty p q r s).1 (Eab a b) hKC d P hP

theorem fock_kernel_adjoint : KAdj := by
  intro p q r s a b hab P Q
  have hba : sameBlock b a := FockRL.sameBlock_symm hab
  rw [fock_operators_kernel p q r s a b hab, fock_operators_kernel p q r s b a hba]
  simp only [sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply, fockInner_add_right,
    fockInner_add_left, fockInner_neg_right, fockInner_neg_left, inner_posOp a b hab,
    inner_negOp b a hba]
  by_cases h : a = b
  · subst h
    simp [fockInner_smul_right, fockInner_smul_left]
  · simp [h, Ne.symm h, fockInner_zero_right, fockInner_zero_left]

end PI.FockOneDegW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.SameBlockOfPosC
section
noncomputable section

open Matrix FockH1Action MvPolynomial FockRaiseLowInner

namespace PI.FockOneDegW

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro x y hxy
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h hxy
  · rfl

def harmSub (hS : HarmSub) (p q r s : ℕ) : Submodule ℂ (Pol p q r s) where
  carrier := {P | Harm2 P}
  zero_mem' := (hS p q r s).1
  add_mem' := fun ha hb => (hS p q r s).2.1 _ _ ha hb
  smul_mem' := fun c _ h => (hS p q r s).2.2 c _ h

def innerL {σ : Type} (x : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun Q := fockInner x Q
  map_add' Q Q' := fockInner_add_right x Q Q'
  map_smul' c Q := by simp [fockInner_smul_right]

theorem exists_orth {σ : Type} {V N : Submodule ℂ (MvPolynomial σ ℂ)} [FiniteDimensional ℂ V]
    (hNV : N < V) : ∃ c ∈ V, c ≠ 0 ∧ ∀ n ∈ N, fockInner n c = 0 := by
  classical
  have : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  set k := Module.finrank ℂ N
  let b := Module.finBasis ℂ N
  let Φ : MvPolynomial σ ℂ →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i => innerL ((b i : N) : MvPolynomial σ ℂ))
  let Ψ := Φ.domRestrict V
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 : Module.finrank ℂ (LinearMap.range Ψ) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    simpa [Module.finrank_fin_fun] using this
  have h3 : k < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  have h4 : LinearMap.ker Ψ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨(x : MvPolynomial σ ℂ), x.2, fun h => hx0 (Subtype.ext h), fun n hn => ?_⟩
  have hx' : ∀ i, fockInner ((b i : N) : MvPolynomial σ ℂ) (x : MvPolynomial σ ℂ) = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [Ψ, Φ, innerL] using this
  have hsum := b.sum_repr ⟨n, hn⟩
  have hn' : n = ∑ i, (b.repr ⟨n, hn⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    conv_lhs => rw [show n = ((⟨n, hn⟩ : N) : MvPolynomial σ ℂ) from rfl, ← hsum]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [hn', fockInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [fockInner_smul_left, hx' i, mul_zero]

theorem key_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) (hT : HwHarmDeg)
    {p q r s : ℕ} (μ : Ix p q → ℚ) (W : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ W]
    (hWK : KStable (fockAct1 p q r s) W)
    (hWhw : ∀ (ν : Ix p q → ℚ) (w : Pol p q r s), w ∈ W → IsHW (fockAct1 p q r s) ν w → ν = μ)
    (P : Pol p q r s) (hPW : P ∈ W) (hH : Harm2 P) (e : ℕ)
    (he : homogeneousComponent e P ≠ 0) :
    (e : ℚ) = degW (cPair r s) μ := by
  classical
  let V : Submodule ℂ (Pol p q r s) := W ⊓ harmSub hS p q r s
  let N : Submodule ℂ (Pol p q r s) :=
    V ⊓ LinearMap.ker (homogeneousComponent e : Pol p q r s →ₗ[ℂ] Pol p q r s)
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ V, fockAct1 p q r s (Eab a b) u ∈ V := by
    intro a b hab u hu
    exact ⟨hWK _ (isKC_Eab hab) u hu.1, hKh p q r s a b hab u hu.2⟩
  have hNst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ N, fockAct1 p q r s (Eab a b) u ∈ N := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, ?_⟩
    have h0 : homogeneousComponent e u = 0 := hu.2
    show homogeneousComponent e (fockAct1 p q r s (Eab a b) u) = 0
    rw [hKc p q r s a b hab e u, h0, map_zero]
  let C : Submodule ℂ (Pol p q r s) :=
    { carrier := {c | c ∈ V ∧ ∀ n ∈ N, fockInner n c = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨V.add_mem hx hy, fun n hn => ?_⟩
        rw [fockInner_add_right, hx' n hn, hy' n hn, add_zero]
      zero_mem' := ⟨V.zero_mem, fun n _ => fockInner_zero_right n⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨V.smul_mem c hx, fun n hn => ?_⟩
        rw [fockInner_smul_right, hx' n hn, mul_zero] }
  have hPV : P ∈ V := ⟨hPW, hH⟩
  have hPN : P ∉ N := fun h => he h.2
  have hNV : N < V := lt_of_le_of_ne inf_le_left (fun h => hPN (h ▸ hPV))
  obtain ⟨c0, hc0V, hc0, hc0N⟩ := exists_orth hNV
  have hCne : C ≠ ⊥ := by
    intro h
    have : c0 ∈ C := ⟨hc0V, hc0N⟩
    rw [h, Submodule.mem_bot] at this
    exact hc0 this
  haveI : FiniteDimensional ℂ C :=
    Submodule.finiteDimensional_of_le (show C ≤ V from fun x hx => hx.1)
  have hCst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ C, fockAct1 p q r s (Eab a b) u ∈ C := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, fun n hn => ?_⟩
    rw [hA p q r s a b hab n u]
    have hba : sameBlock b a := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
    exact hu.2 _ (hNst b a hba n hn)
  obtain ⟨ν, v, hvC, hv0, hvhw⟩ := hE p q r s C inferInstance hCne hCst
  have hνμ : ν = μ := hWhw ν v hvC.1.1 ⟨hv0, hvhw⟩
  subst hνμ

  have hve : homogeneousComponent e v ≠ 0 := by
    intro h
    have hvN : v ∈ N := ⟨hvC.1, h⟩
    have := hvC.2 v hvN
    exact hv0 ((hI _ v v v 0).2.2.2.2.1 this)
  have hwt : ∀ a : Ix p q, fockAct1 p q r s (Eab a a) v = ((ν a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).mp hvhw.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have hraise : ∀ a b : Ix p q, posC a b → fockAct1 p q r s (Eab a b) v = 0 := by
    intro a b hab
    have h1 := (Submodule.mem_iInf _).mp hvhw.2 a
    have h2 := (Submodule.mem_iInf _).mp h1 b
    have h3 := (Submodule.mem_iInf _).mp h2 hab
    exact LinearMap.mem_ker.mp h3
  have hsame : ∀ a : Ix p q, sameBlock a a := by
    intro a; rcases a with a | a <;> simp [sameBlock]
  have hHW : IsHW (fockAct1 p q r s) ν (homogeneousComponent e v) := by
    refine ⟨hve, ?_, ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun a => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, ← hKc p q r s a a (hsame a) e v, hwt a,
        map_smul, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
    · refine (Submodule.mem_iInf _).mpr fun a => (Submodule.mem_iInf _).mpr fun b =>
        (Submodule.mem_iInf _).mpr fun hab => ?_
      rw [LinearMap.mem_ker, ← hKc p q r s a b (sameBlock_of_posC hab) e v, hraise a b hab, map_zero]
  have hhom : homogeneousComponent e v ∈ homog (Ix p q × Ix r s) e :=
    (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e v)
  exact hT p q r s ν e _ hhom hHW (hHc p q r s e v hvC.1.2)

theorem reduction_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) : Reduction := by
  intro hT p q r s μ P hP0 hOT hH
  obtain ⟨W, hWfd, hPW, hWK, hWhw⟩ := hOT
  have key := fun e he => key_of hI hKc hKh hHc hS hA hE hT μ W hWK hWhw P hPW hH e he
  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (FockRaiseLowGrade.eq_zero_of_hc P h)
  refine ⟨e, key e he, ?_⟩
  have hother : ∀ e', e' ≠ e → homogeneousComponent e' P = 0 := by
    intro e' hne
    by_contra h
    have h1 := key e' h
    rw [← key e he] at h1
    exact hne (by exact_mod_cast h1)
  have hPe : P = homogeneousComponent e P := by
    have : P - homogeneousComponent e P = 0 := by
      apply FockRaiseLowGrade.eq_zero_of_hc
      intro e'
      rw [map_sub, FockRaiseLowGrade.hc_hc]
      by_cases h : e' = e
      · subst h; simp
      · rw [if_neg h, hother e' h, sub_zero]
    exact sub_eq_zero.mp this
  rw [hPe]
  exact (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e P)

end PI.FockOneDegW
end
end

