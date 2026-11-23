module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyBinetColumnFrameProdDetPowEqSum
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
section
open Classical MvPolynomial

noncomputable section

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem eval_rsub_frameMat {a d : ℕ} (x₀ : Var ι d a → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (rsub (frameMat x₀) P) = eval x₀ (colSub g P) := by
  have h : (eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2)).comp
        (rsub (frameMat x₀) : Pol ι d a →ₐ[ℂ] _).toRingHom
      = (eval x₀).comp (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      obtain ⟨τ, r, j⟩ := v
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rsub_X, colSub, aeval_X,
        map_sum, map_mul, eval_C, eval_X]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single j]
        · simp [frameMat, mul_comm]
        · intro b _ hb; simp [frameMat, hb]
        · simp
      · intro b _ hb; simp [frameMat, hb]
      · simp
  exact congrArg (fun φ : Pol ι d a →+* ℂ => φ P) h

theorem rsub_frameMat_of_mem_inv {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by
  rw [← sub_eq_zero]
  apply _root_.GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense
  intro g
  rw [map_sub, eval_rsub_frameMat x₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P, hP g, smul_eval, smul_eval,
    eval_detG a n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))]
  ring

theorem inv_le_span_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  intro ι _ a d n P hP
  set c := Formalism.L2.DIV.fockS (detG (ι := ι) a n) (detG a n) with hc
  have hc0 : c ≠ 0 := fun h => by
    have := fockS_self_re_pos (detG_ne_zero (ι := ι) a n)
    rw [← hc, h] at this
    simp at this
  have key : c • P = ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    apply MvPolynomial.funext
    intro x₀
    have h1 := _root_.GlobalTheory.MinorFrame.fockS_rsub_adj (frameMat x₀).conjTranspose (detG a n) P
    rw [Matrix.conjTranspose_conjTranspose, rsub_frameMat_of_mem_inv x₀ hP, _root_.GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, map_sum, map_smul, LinearMap.sum_apply] at h1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, smul_eq_mul,
      starRingEnd_apply, star_star] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eval, map_sum]
    simp only [smul_eval]
    rw [mul_comm, ← h1]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hP' : P = c⁻¹ • ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    rw [← key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hP']
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun T _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩))

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.HarmStable

section General

variable {σ : Type}

def DegZero (K : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → K P ∈ homog σ d

theorem hc_hc (d e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (homogeneousComponent e P) =
      if d = e then homogeneousComponent e P else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_mem e P)

theorem DegZero.comm {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (d : ℕ)
    (P : MvPolynomial σ ℂ) : homogeneousComponent d (K P) = K (homogeneousComponent d P) := by
  rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [homogeneousComponent_of_mem (hK e _ (homogeneousComponent_mem e P)), hc_hc]
  split_ifs <;> simp

theorem minusPart_eq_zero_iff (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = 0 ↔
      ∀ d, homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0 := by
  constructor
  · intro h d
    have hfin : (Function.support fun e : ℕ =>
        homogeneousComponent e (A (homogeneousComponent (e + 2) P))) ⊆
        ((Finset.range (P.totalDegree + 1) ∪ {d} : Finset ℕ) : Set ℕ) := by
      intro e he
      by_contra hne
      apply he
      have : P.totalDegree < e + 2 := by
        simp only [Finset.coe_union, Finset.coe_range, Set.mem_union, Set.mem_Iio, not_or] at hne
        omega
      simp [homogeneousComponent_eq_zero _ _ this]
    rw [minusPart, finsum_eq_sum_of_support_subset _ hfin] at h
    have h2 := congrArg (homogeneousComponent d) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    simp only [hc_hc] at h2
    rw [Finset.sum_ite_eq] at h2
    simpa using h2
  · intro h
    rw [minusPart]
    simp [h]

def lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ Z, ⨅ (_ : c Z), ⨅ d : ℕ,
    LinearMap.ker (homogeneousComponent d ∘ₗ A Z ∘ₗ homogeneousComponent (d + 2))

theorem mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} : P ∈ lowKer A c ↔
      ∀ Z, c Z → ∀ d, homogeneousComponent d (A Z (homogeneousComponent (d + 2) P)) = 0 := by
  simp [lowKer, Submodule.mem_iInf]

theorem coe_lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    (lowKer A c : Set (MvPolynomial σ ℂ)) = {P | ∀ Z, c Z → minusPart (A Z) P = 0} := by
  ext P
  simp only [SetLike.mem_coe, mem_lowKer, Set.mem_setOf_eq, minusPart_eq_zero_iff]

theorem hc_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) (e : ℕ) :
    homogeneousComponent e P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hc_hc]
  split_ifs with h
  · rw [← h]; exact hP Z hZ d
  · simp

theorem map_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K)
    (hc : ∀ Z, c Z → A Z * K = K * A Z ∨ ∃ Z', c Z' ∧ A Z' = A Z * K - K * A Z)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) : K P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hK.comm, ← Module.End.mul_apply (A Z) K]
  rcases hc Z hZ with h | ⟨Z', hZ', h⟩
  · rw [h, Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero]
  · rw [← sub_add_cancel (A Z * K) (K * A Z), ← h, LinearMap.add_apply, map_add (f := _), hP Z' hZ' d,
      Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero, add_zero]

theorem X_mul_pderiv_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    X u * pderiv v P ∈ homog σ d := by
  rcases d with _ | d
  · rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hP), pderiv_C,
      mul_zero]
    exact Submodule.zero_mem _
  · have := (isHomogeneous_X ℂ u).mul (IsHomogeneous.pderiv (i := v) hP)
    rwa [Nat.add_sub_cancel, add_comm] at this

theorem pderiv_X_mul_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    pderiv v (X u * P) ∈ homog σ d := by
  have := IsHomogeneous.pderiv (i := v) ((isHomogeneous_X ℂ u).mul hP)
  rwa [Nat.add_sub_cancel_left] at this

end General

variable {p q r s : ℕ}

theorem degZero_omE {l l' : Ln p q r s} (h : linePos l = linePos l') : DegZero (omE l l') := by
  intro d P hP
  rw [omE, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [raiB, lowB, ← h]
    split_ifs
    · exact X_mul_pderiv_mem l l' hP
    · exact Submodule.neg_mem _ (pderiv_X_mul_mem l' l hP)
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem degZero_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (h : ∀ l l', linePos l ≠ linePos l' → M l l' = 0) : DegZero (omAct p q r s M) := by
  intro d P hP
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  by_cases hl : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (degZero_omE hl d P hP)
  · rw [h l l' hl, zero_smul]; exact Submodule.zero_mem _

theorem degZero_fockAct1 {Y : Mat p q} (hY : IsKC Y) : DegZero (fockAct1 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show Y a b * (1 : Mat r s) c e = 0
  by_cases hce : c = e
  · subst hce
    rw [hY a b, zero_mul]
    revert h
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hce, mul_zero]

theorem degZero_fockAct2 {Y : Mat r s} (hY : IsKC Y) : DegZero (fockAct2 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show (1 : Mat p q) a b * Y c e = 0
  by_cases hab : a = b
  · subst hab
    rw [hY c e, mul_zero]
    revert h
    rcases a with a | a <;> rcases e with e | e <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hab, zero_mul]

theorem isPC_bracket {Y Z : Mat p q} (hY : IsKC Y) (hZ : IsPC Z) : IsPC (Z * Y - Y * Z) := by
  intro a b hab
  have h1 : (Z * Y) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ a c hc, zero_mul]
    · rw [hY c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
  have h2 : (Y * Z) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
    · rw [hY a c hc, zero_mul]
  rw [Matrix.sub_apply, h1, h2, sub_zero]

def sub1 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat r s => fockAct2 p q r s Z) IsPC

def sub2 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat p q => fockAct1 p q r s Z) IsPC

theorem coe_fockHarmonicsFirstMemberSubspace : (sub1 p q r s : Set (Pol p q r s)) = harm1 p q r s := coe_lowKer _ _

theorem coe_fockHarmonicsSecondMemberSubmodule : (sub2 p q r s : Set (Pol p q r s)) = harm2 p q r s := coe_lowKer _ _

theorem fockHarmonicsFirstMember_kStable : KStable (fockAct1 p q r s) (sub1 p q r s) ∧
    KStable (fockAct2 p q r s) (sub1 p q r s) := by
  obtain ⟨-, -, h2, h3⟩ := _root_.GlobalTheory.FockAlg.fock_lie_and_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z _ => Or.inl (h3 Y Z).symm) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h2 Z Y⟩) hw⟩

theorem fockHarmonicsSecondMember_kStable : KStable (fockAct1 p q r s) (sub2 p q r s) ∧
    KStable (fockAct2 p q r s) (sub2 p q r s) := by
  obtain ⟨-, h1, -, h3⟩ := _root_.GlobalTheory.FockAlg.fock_lie_and_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h1 Z Y⟩) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z _ => Or.inl (h3 Z Y)) hw⟩

end GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.FockAlg

open HarmStable

theorem harm_graded_stable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)),
    (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) →
    (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧
      KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧
      KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧
      ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  intro p q r s S hS
  rcases hS with rfl | rfl | rfl
  · rw [← coe_fockHarmonicsFirstMemberSubspace, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsFirstMember_kStable.1, fockHarmonicsFirstMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [← coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsSecondMember_kStable.1, fockHarmonicsSecondMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [jointHarm, ← coe_fockHarmonicsFirstMemberSubspace, ← coe_fockHarmonicsSecondMemberSubmodule, ← Submodule.coe_inf, Submodule.span_eq]
    exact ⟨rfl,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, fockHarmonicsFirstMember_kStable.1 Y hY w hw.2⟩,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, fockHarmonicsFirstMember_kStable.2 Y hY w hw.2⟩,
      fun P hP d => ⟨hc_mem_lowKer hP.1 d, hc_mem_lowKer hP.2 d⟩⟩

end GlobalTheory.FockAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditive
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.LowLaw

theorem eq_single_of_degree_eq_one {σ : Type} {e : σ →₀ ℕ} (h : e.degree = 1) :
    ∃ j, e = Finsupp.single j 1 := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at h
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single j 1 ≤ e := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  refine ⟨j, ?_⟩
  have hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
  have hd : (e - Finsupp.single j 1).degree = 0 := by
    have h2 := congrArg Finsupp.degree hsum
    rw [map_add (f := _), Finsupp.degree_single, h] at h2
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hsum, hd, zero_add]

theorem coeff_addLaw (R : Type) [CommRing R] (d : ℕ) (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) :
    coeff α (addLaw R d i) =
      if α = Finsupp.single (Sum.inl i) 1 ∨ α = Finsupp.single (Sum.inr i) 1 then 1 else 0 := by
  classical
  simp only [addLaw, map_add (f := _), coeff_X]
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · have h2 : α ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h
      exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · rw [if_pos h2, if_pos (Or.inr h2)]
    · rw [if_neg h2, if_neg (by tauto)]

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_inl {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hu := congrArg (coeff (Finsupp.single j 1)) (congrFun h.unit i)
  simp only [op, at2] at hu
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hu
  simpa [coeff_X, Finsupp.single_left_inj] using hu

theorem coeff_inr {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hc := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (h.comm i)
  simp only [swap, at2] at hc
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hc
  rw [← hc, ← coeff_inl h i j]
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.Katz.LowLaw

namespace GlobalTheory.Katz


open LowLaw in
theorem coeff_law_of_degree_le_one (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ)
    (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) (hα : α.degree ≤ 1) :
    coeff α (μ i) = coeff α (addLaw k d i) ∧
      coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  classical
  have h1 : coeff α (μ i) = coeff α (addLaw k d i) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1
    · rw [(Finsupp.degree_eq_zero_iff α).1 h0, coeff_zero_eq_constantCoeff_apply, h.const,
        coeff_addLaw, if_neg]
      rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm
    · obtain ⟨s, rfl⟩ := eq_single_of_degree_eq_one h1
      rcases s with j | j
      · rw [coeff_inl h, coeff_addLaw]; simp [Finsupp.single_left_inj]
      · rw [coeff_inr h, coeff_addLaw]; simp [Finsupp.single_left_inj]
  refine ⟨h1, ?_⟩
  rw [coeff_lift, h1, coeff_addLaw, coeff_addLaw]
  split_ifs <;> simp

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FpTiedIffExistsLeafFP
section
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesCompare

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

omit [NumberField K] in
theorem localization_mono' {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    {L L' : Submodule (𝓞 K) W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem primePow_anti (w : HeightOneSpectrum (𝓞 K)) {n n' : ℤ} (h : n' ≤ n) : primePow w n ≤ primePow w n' := by
  have hP : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  obtain ⟨k, rfl⟩ := Int.le.dest h
  have h1 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one
  have h2 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (n' + (k : ℤ)) ≤
      (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' := by
    rw [zpow_add₀ hP, zpow_natCast]
    calc _ ≤ (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' * 1 := by gcongr
      _ = _ := mul_one _
  exact FractionalIdeal.coe_le_coe.mpr h2

theorem scaledAt_anti {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) {n n' : ℤ}
    (h : n' ≤ n) : scaledAt w n B ≤ scaledAt w n' B := by
  refine localization_mono' _ (Submodule.span_mono ?_)
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, primePow_anti w h ha, x, hx, rfl⟩

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end GlobalTheory.FinitePlacesCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirection
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem jet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have h1 := _root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ (v * c) (v * t) κ hk ha hτ
  have h2 := (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ).mul_left (v ^ (∑ i, κ i))
  refine h1.unique (HasSum.congr_fun h2 fun ξ ↦ ?_)
  have hp : (∏ i : Emb F, lag k (κ i) (v * c) ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t))) =
      v ^ (∑ i, κ i) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show (2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t) = v * ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) by ring]
    exact (lag_homogeneous k (κ i) c _ v).1
  rw [hp]; ring

end GlobalTheory.HilbFam
end

