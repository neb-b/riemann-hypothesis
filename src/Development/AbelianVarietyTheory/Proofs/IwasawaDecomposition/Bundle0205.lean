module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartanExchangeUnimodularInertPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitaryExchangeUnimodularLatticesIner
section
noncomputable section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.InertExchange

open Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

private theorem isFullLattice_of_unimodular {L : Submodule (𝓞 E) (Sp E n)}
    (hL : Submodule.IsLattice E L) (hu : IsUnimodular (hStd E n) L) :
    Submodule.IsFullLattice E L := by
  let := hL
  refine { span_eq_top := ?_ }
  let W := Submodule.span E (L : Set (Sp E n))
  change W = ⊤
  by_contra h
  let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
  let g : Sp E n →ₗ[E] Module.Dual E W :=
    (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
  have hdim : finrank E (Module.Dual E W) < finrank E (Sp E n) := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt h
  obtain ⟨x, hx, hx₀⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
  -- Every multiple of the orthogonal vector lies in the self-dual lattice.
  have hsmul (a : E) : a • e x ∈ L := by
    rw [← hu, dualBasic_mem_dual]
    intro y hy
    apply hStd_mem_one_symm
    have hxy : hStd E n (e x) y = 0 :=
      congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
    simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
  let i : E →ₗ[𝓞 E] L :=
    ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
  let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))


theorem exchange : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)),
  conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
  ∀ (X Z : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E X → Submodule.IsLattice E Z →
    IsUnimodular (hStd E n) X → IsUnimodular (hStd E n) Z →
    (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z) →
    ∃ σ : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n), σ X = Z ∧ σ Z = X ∧
      (∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) →
        Submodule.IsLattice E (σ Y) ∧ IsUnimodular (hStd E n) (σ Y) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (σ Y)) ∧
      (∀ Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        ∃ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
          (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) ∧ σ Y = Y') ∧
      (∀ Y Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') → σ Y = σ Y' → Y = Y') ∧
      ∀ (s : List ℕ) (Y Y' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        (IsInertNbr P.asIdeal s (σ Y) (σ Y') ↔ IsInertNbr P.asIdeal s Y Y') := by
  intro E _ _ _ n P hP hin X Z hXl hZl hXu hZu hXZ
  obtain ⟨g, hg, hgX, hgZ⟩ := _root_.GlobalTheory.CartanInertPf.cartanInert n P hP hin X Z hXl hZl hXu hZu hXZ
  have hcc : ∀ Q : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ Q) = Q := fun Q => by
    apply HeightOneSpectrum.ext
    ext r
    change cO E (cO E r) ∈ Q.asIdeal ↔ r ∈ Q.asIdeal
    rw [cO_cO]
  have locg : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E)) (M N : Submodule (𝓞 E) (Sp E n)),
      localization₂ Q.asIdeal M = localization₂ Q.asIdeal N → localization₂ Q.asIdeal (gmap h M) = localization₂ Q.asIdeal (gmap h N) := by
    intro h Q M N e
    ext x
    rw [mem_localization_gmap, mem_localization_gmap, e]
  have locg_inv : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E)) (M N : Submodule (𝓞 E) (Sp E n)),
      localization₂ Q.asIdeal (gmap h M) = localization₂ Q.asIdeal (gmap h N) → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N := by
    intro h Q M N e
    ext x
    have h1 := (mem_localization_gmap Q h M (h x)).symm
    have h2 := (mem_localization_gmap Q h N (h x)).symm
    simp only [LinearEquiv.symm_apply_apply] at h1 h2
    rw [h1, h2, e]
  have ginv : ∀ M : Submodule (𝓞 E) (Sp E n), gmap g⁻¹ (gmap g M) = M := by
    intro M
    ext x
    rw [mem_gmap, mem_gmap]
    have e : g⁻¹ = g.symm := rfl
    rw [e, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  have hginv : g⁻¹ ∈ UF E n := inv_mem hg
  have unimodG : ∀ (h : Sp E n ≃ₗ[E] Sp E n), h ∈ UF E n → ∀ M : Submodule (𝓞 E) (Sp E n),
      IsUnimodular (hStd E n) M → IsUnimodular (hStd E n) (gmap h M) := by
    intro h hh M hM
    have hM' : dual (hStd E n) M = M := hM
    show dual (hStd E n) (gmap h M) = gmap h M
    rw [dual_gmap h hh, hM']
  have unimod : ∀ A B C : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E A → Submodule.IsLattice E B →
      Submodule.IsLattice E C → IsUnimodular (hStd E n) B → IsUnimodular (hStd E n) C →
      localization₂ P.asIdeal A = localization₂ P.asIdeal B → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal C) →
      IsUnimodular (hStd E n) A := by
    intro A B C hA hB hC hBu hCu hAP hAQ
    have hBu' : dual (hStd E n) B = B := hBu
    have hCu' : dual (hStd E n) C = C := hCu
    show dual (hStd E n) A = A
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    by_cases hQ : Q = P
    · rw [hQ]
      have h1 : localization₂ (conjPrime₂ P).asIdeal A = localization₂ (conjPrime₂ P).asIdeal B := by rw [hP]; exact hAP
      rw [GlobalTheory.T.localization_hermitianDual_eq P A B hA hB h1, hBu', hAP]
    · have hQ' : conjPrime₂ Q ≠ P := fun h => hQ (by rw [← hcc Q, h, hP])
      rw [GlobalTheory.T.localization_hermitianDual_eq Q A C hA hC (hAQ _ hQ'), hCu', hAQ Q hQ]
  have patch_lat_loc : ∀ (h : Sp E n ≃ₗ[E] Sp E n), h ∈ UF E n →
      ∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y →
      Submodule.IsLattice E (patchAt P (gmap h Y) Y) ∧ ∀ Q : HeightOneSpectrum (𝓞 E),
        localization₂ Q.asIdeal (patchAt P (gmap h Y) Y) = localization₂ Q.asIdeal (if Q = P then gmap h Y else Y) := by
    intro h hh Y hY hu
    exact GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap h Y) Y
      (isFullLattice_of_unimodular (gmap_lattice h Y hY) (unimodG h hh Y hu))
      (isFullLattice_of_unimodular hY hu)
  have locσ := fun Y hY hu => (patch_lat_loc g hg Y hY hu).2
  have latσ := fun Y hY hu => (patch_lat_loc g hg Y hY hu).1
  refine ⟨fun Y => patchAt P (gmap g Y) Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show patchAt P (gmap g X) X = Z
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    rw [locσ X hXl hXu Q]
    split_ifs with hQ
    · rw [hQ]; exact hgX.localization_eq.symm
    · exact (hXZ Q hQ).localization_eq.symm
  · show patchAt P (gmap g Z) Z = X
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    rw [locσ Z hZl hZu Q]
    split_ifs with hQ
    · rw [hQ]; exact hgZ.localization_eq.symm
    · exact (hXZ Q hQ).localization_eq
  · intro Y hYl hYu hYS
    show Submodule.IsLattice E (patchAt P (gmap g Y) Y) ∧ IsUnimodular (hStd E n) (patchAt P (gmap g Y) Y) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (patchAt P (gmap g Y) Y)
    refine ⟨latσ Y hYl hYu, ?_, ?_⟩
    · refine unimod _ (gmap g Y) X (latσ Y hYl hYu) (gmap_lattice g Y hYl) hXl (unimodG g hg Y hYu) hXu ?_ ?_
      · rw [locσ Y hYl hYu P, if_pos rfl]
      · intro Q hQ
        rw [locσ Y hYl hYu Q, if_neg hQ]
        exact (hYS Q hQ).localization_eq
    · intro Q hQ
      apply _root_.GlobalTheory.sameAt_of_localized_eq Q X _ hXl (latσ Y hYl hYu)
      rw [locσ Y hYl hYu Q, if_neg hQ]
      exact (hYS Q hQ).localization_eq.symm
  · intro Y' hl' hu' hS'
    obtain ⟨hYl, hYloc⟩ := patch_lat_loc g⁻¹ hginv Y' hl' hu'
    have hYu : IsUnimodular (hStd E n) (patchAt P (gmap g⁻¹ Y') Y') := by
      refine unimod _ (gmap g⁻¹ Y') Y' hYl (gmap_lattice _ _ hl') hl' (unimodG _ hginv Y' hu') hu' ?_ ?_
      · rw [hYloc P, if_pos rfl]
      · intro Q hQ
        rw [hYloc Q, if_neg hQ]
    refine ⟨patchAt P (gmap g⁻¹ Y') Y', hYl, hYu, ?_, ?_⟩
    · intro Q hQ
      apply _root_.GlobalTheory.sameAt_of_localized_eq Q X _ hXl hYl
      rw [hYloc Q, if_neg hQ]
      exact (hS' Q hQ).localization_eq.symm
    · show patchAt P (gmap g (patchAt P (gmap g⁻¹ Y') Y')) (patchAt P (gmap g⁻¹ Y') Y') = Y'
      apply Formalism.L2.DIV.eq_of_forall_localized_eq
      intro Q
      rw [locσ _ hYl hYu Q]
      split_ifs with hQ
      · rw [hQ]
        ext x
        rw [mem_localization_gmap, hYloc P, if_pos rfl, mem_localization_gmap]
        have e : g⁻¹ = g.symm := rfl
        rw [e, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
      · rw [hYloc Q, if_neg hQ]
  · intro Y Y' hYl hYu hYS hY'l hY'u hY'S he
    have he' : patchAt P (gmap g Y) Y = patchAt P (gmap g Y') Y' := he
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    by_cases hQ : Q = P
    · rw [hQ]
      apply locg_inv g P
      have h1 := congrArg (localization₂ P.asIdeal) he'
      rw [locσ Y hYl hYu P, locσ Y' hY'l hY'u P, if_pos rfl, if_pos rfl] at h1
      exact h1
    · rw [(hYS Q hQ).localization_eq, (hY'S Q hQ).localization_eq]
  · intro s Y Y' hYl hYu hYS hY'l hY'u hY'S
    show IsInertNbr P.asIdeal s (patchAt P (gmap g Y) Y) (patchAt P (gmap g Y') Y') ↔ IsInertNbr P.asIdeal s Y Y'
    have hAl := gmap_lattice g Y hYl
    have hBl := gmap_lattice g Y' hY'l
    have hAA' := _root_.GlobalTheory.sameAt_of_localized_eq P (gmap g Y) _ hAl (latσ Y hYl hYu) (by rw [locσ Y hYl hYu P, if_pos rfl])
    have hBB' := _root_.GlobalTheory.sameAt_of_localized_eq P (gmap g Y') _ hBl (latσ Y' hY'l hY'u) (by rw [locσ Y' hY'l hY'u P, if_pos rfl])
    have hAB : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal (gmap g Y) = localization₂ Q.asIdeal (gmap g Y') :=
      fun Q hQ => locg g Q Y Y' ((hYS Q hQ).localization_eq.trans (hY'S Q hQ).localization_eq.symm)
    have hA'B' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P →
        localization₂ Q.asIdeal (patchAt P (gmap g Y) Y) = localization₂ Q.asIdeal (patchAt P (gmap g Y') Y') := by
      intro Q hQ
      rw [locσ Y hYl hYu Q, locσ Y' hY'l hY'u Q, if_neg hQ, if_neg hQ, (hYS Q hQ).localization_eq, (hY'S Q hQ).localization_eq]
    obtain ⟨k1, hk1, hk1'⟩ := _root_.GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq P _ _ hAl hBl hAB
    obtain ⟨k2, hk2, hk2'⟩ := _root_.GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq P _ _ (latσ Y hYl hYu) (latσ Y' hY'l hY'u) hA'B'
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hAA'
    obtain ⟨b, hb, b', hb', h3, h4⟩ := hBB'
    have hα0 : a * a' * b * b' ∉ P.asIdeal :=
      Formalism.L2.DIV.lc_mul_notMem P (Formalism.L2.DIV.lc_mul_notMem P (Formalism.L2.DIV.lc_mul_notMem P ha ha') hb) hb'
    obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hα0
    have hgeom := geom_sum_mul p (k1 + k2)
    have hgd : t * (∑ i ∈ Finset.range (k1 + k2), p ^ i) * (a * a' * b * b') + p ^ (k1 + k2) = 1 := by
      linear_combination (∑ i ∈ Finset.range (k1 + k2), p ^ i) * e - hgeom
    have hδ : p ^ (k1 + k2) ∈ P.asIdeal ^ (k1 + k2) := Ideal.pow_mem_pow hp _
    set S := ∑ i ∈ Finset.range (k1 + k2), p ^ i
    have rAA' : HiRel (t * S * (a * a' * b * b')) (gmap g Y) (patchAt P (gmap g Y) Y) := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * b * b') • (a' • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h2 x hx)
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a' * b * b') • (a • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h1 x hx)
    have rBB' : HiRel (t * S * (a * a' * b * b')) (gmap g Y') (patchAt P (gmap g Y') Y') := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * a' * b) • (b' • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h4 x hx)
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * a' * b') • (b • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h3 x hx)
    have le1 : P.asIdeal ^ (k1 + k2) ≤ P.asIdeal ^ k1 := Ideal.pow_le_pow_right (by omega)
    have le2 : P.asIdeal ^ (k1 + k2) ≤ P.asIdeal ^ k2 := Ideal.pow_le_pow_right (by omega)
    have rAB : HiRel (p ^ (k1 + k2)) (gmap g Y) (gmap g Y') :=
      HiRel.of_ideal ((Submodule.smul_mono_left le1).trans hk1) ((Submodule.smul_mono_left le1).trans hk1') hδ
    have rA'B' : HiRel (p ^ (k1 + k2)) (patchAt P (gmap g Y) Y) (patchAt P (gmap g Y') Y') :=
      HiRel.of_ideal ((Submodule.smul_mono_left le2).trans hk2) ((Submodule.smul_mono_left le2).trans hk2') hδ
    constructor
    · intro h
      have h5 := isInertNbr_par hgd rAA'.symm rBB'.symm rA'B' rAB h
      have h6 := h5.gmap g⁻¹
      rwa [ginv, ginv] at h6
    · intro h
      exact isInertNbr_par hgd rAA' rBB' rAB rA'B' (h.gmap g)

end GlobalTheory.InertExchange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BVal

open Formalism.L2.Host
open scoped nonZeroDivisors

section General

variable {L : Type} [Field L] [NumberField L]

theorem onId_mul (χ : HChar L) {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0) :
    χ.onId (I * J) = χ.onId I * χ.onId J := by
  have hf : ∀ K : FractionalIdeal (𝓞 L)⁰ L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v K).Finite := fun K => by
    refine (FractionalIdeal.finite_factors (K := L) K).subset fun v hv h => hv ?_
    have h' : FractionalIdeal.count L v K = 0 := h
    simp [h']
  unfold HChar.onId
  rw [← finprod_mul_distrib (hf I) (hf J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v hI hJ, _root_.zpow_add]

theorem onId_one (χ : HChar L) : χ.onId 1 = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v fun w hw => by rw [FractionalIdeal.count_maximal_coprime L w hw.symm, zpow_zero],
    FractionalIdeal.count_self, zpow_one]

theorem mem_of_primes (χ : HChar L) (M : IntermediateField ℚ ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      ((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M)
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    ((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) ∈ M := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have := mul_mem (h v hb) (ih ha ha1)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      show χ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = χ.val v from onId_prime χ v]
    convert this using 1
    push_cast
    ring

theorem val_mul_sqrt (α β γ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (((α * β * γ⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) =
      α.valTw 0 v * β.valTw 0 v * (γ.valTw (1 / 2) v)⁻¹ := by
  have e : (α * β * γ⁻¹).val v = α.val v * β.val v * (γ.val v)⁻¹ := rfl
  have e2 : ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [e, e2]
  simp only [HChar.valTw, Complex.cpow_neg, Complex.ofReal_zero, Complex.cpow_zero, inv_one, mul_one, mul_inv, inv_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

end General

theorem exists_field_BIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i t
  obtain ⟨M₁, hM₁, -, -, hmu, heta, -⟩ := GlobalTheory.Mem.FrameVal.frame_values D.R D.host (eExp D)
    ⟨R.C.P, R.C.W, R.C.mu0, R.C.eta, R.C.chiPsi, R.C.del, R.C.del', R.C.isMu0, R.C.isEta, R.C.isChi, R.C.isDel, R.C.isDel'⟩
    fun j τ => (D.hc _).e_int j
  obtain ⟨M₂, hM₂, hxi⟩ := GlobalTheory.Mem.FrameVal.exists_of_order (hL.xi_fin t)
  refine ⟨M₁ ⊔ M₂, inferInstance, fun M' hM bad hg hQ => ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M' := by
    intro v hv
    have u1 : (R.C.mu0 i).UnrAt v := (R.C.isMu0 i).unr v fun k hk => hv (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
      have hd : D.host.g k ∣ bad := by
        refine dvd_trans ?_ hg
        fin_cases k
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hk')
    have u2 : (R.xiH t).UnrAt v := by
      by_contra h
      rcases (hL.Q_ram t v).1 h with h | ⟨P', hP', h⟩
      · exact hv (hQ v h)
      · obtain ⟨c', hc', e⟩ := h _ (hQ P' hP')
        have e' : c' = (bad : 𝓞 D.host.E) := RingOfIntegers.ext (by
          rw [e]
          change star ((bad : 𝓞 D.host.E) : D.host.E) = ((bad : 𝓞 D.host.E) : D.host.E)
          rw [show ((bad : 𝓞 D.host.E) : D.host.E) = (bad : D.host.E) from
            map_natCast (algebraMap (𝓞 D.host.E) D.host.E) bad, star_natCast])
        exact hv (e' ▸ hc')
    obtain ⟨y1, hy1⟩ := hmu i v u1
    obtain ⟨y2, hy2⟩ := hxi v u2
    obtain ⟨y3, hy3⟩ := heta v (R.C.isEta.unr v)
    rw [val_mul_sqrt, ← hy1, ← hy2, ← hy3]
    exact mul_mem (mul_mem (hM (le_sup_left (b := M₂) y1.2)) (hM (le_sup_right (a := M₁) y2.2)))
      (inv_mem (hM (le_sup_left (b := M₂) y3.2)))
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, mem_of_primes _ M' _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

end GlobalTheory.Mem.BVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
section
noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

theorem valuation_eq_iff_ord {x y : kˣ} : valuation k (x : k) = valuation k (y : k) ↔ ord k x = ord k y := by
  rw [le_antisymm_iff, valuation_le_iff_ord, valuation_le_iff_ord]; omega

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

theorem valuation_of_shell {c r : kˣ} {a : ℕ} (hr : ord k r = ord k c - a) :
    valuation k (c : k) = uniformizer k ^ a * valuation k (r : k) := by
  obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
  rw [← hp, ← map_mul, ← Units.val_mul, valuation_eq_iff_ord, ord_mul]; omega

theorem IsShellReps.sum_eq {c : kˣ} {a : ℕ} {R R' : Finset kˣ} (h : IsShellReps c a R) (h' : IsShellReps c a R')
    {g : kˣ → ℂ} (hg : ∀ y r : kˣ, ord k y = ord k c - a → ord k r = ord k c - a →
      valuation k ((y : k) - r) ≤ valuation k (c : k) → g y = g r) :
    ∑ r ∈ R, g r = ∑ r ∈ R', g r := by
  choose i hi hi' using fun r hr => h'.2 r (h.1 r hr)
  refine Finset.sum_bij i (fun r hr => (hi r hr).1) (fun r₁ h₁ r₂ h₂ e => ?_) (fun r' hr' => ?_)
    (fun r hr => hg _ _ (h.1 r hr) (h'.1 _ (hi r hr).1) (hi r hr).2)
  · refine (h.2 _ (h'.1 _ (hi r₁ h₁).1)).unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · rw [Valuation.map_sub_swap]; exact (hi r₁ h₁).2
    · rw [Valuation.map_sub_swap, e]; exact (hi r₂ h₂).2
  · obtain ⟨r, hr, -⟩ := h.2 r' (h'.1 r' hr')
    exact ⟨r, hr.1, (hi' r hr.1 r' ⟨hr', by rw [Valuation.map_sub_swap]; exact hr.2⟩).symm⟩


variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

theorem addChar_eq_of_sub (hψ : HasConductor ψ c) {y z : k} (h : valuation k (y - z) ≤ valuation k (c : k)) :
    ψ y = ψ z := by
  have : y = z + (y - z) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.eq_one h, mul_one]

theorem gaussTerm_eq (hψ : HasConductor ψ c) (hχ : HasExponent χ a) {x : k} (hx : valuation k x ≤ 1) (y r : kˣ)
    (hy : ord k y = ord k c - a) (hr : ord k r = ord k c - a)
    (h : valuation k ((y : k) - r) ≤ valuation k (c : k)) :
    (((χ y)⁻¹ : ℂˣ) : ℂ) * (ψ (x * y) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  have h1 : ψ (x * y) = ψ (x * r) := addChar_eq_of_sub hψ (by
    rw [← mul_sub, map_mul]
    exact (mul_le_mul' hx h).trans_eq (one_mul _))
  have hr0 : 0 < valuation k (r : k) := by simp [zero_lt_iff]
  have h2 : χ (y * r⁻¹) = 1 := hχ.1 _ ⟨by
    rw [Units.val_mul, map_mul, valuation_eq_iff_ord.2 (hy.trans hr.symm), ← map_mul]; simp, by
    have : ((y * r⁻¹ : kˣ) : k) - 1 = ((y : k) - r) * (r : k)⁻¹ := by simp [sub_mul]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ hr0, ← valuation_of_shell hr]
    exact h⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h1, h2]

theorem IsTateEps.unique {e e' : ℂ} (h : IsTateEps ψ χ e) (h' : IsTateEps ψ χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [IsShellReps, valuation_eq_iff_ord.1 h1, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this]

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelOpenCompactSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelSmooth

theorem level_open_compact_smooth (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((levA V (lev D.sp.cm V.gram β L) : Subgroup (GA D V)) : Set (GA D V)) ∧
    levS V β L ⊆ (GfC V : Set (GA D V)) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L ∧ levChi V β L k = 1 :=
  ⟨GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L, GlobalTheory.ParahoricCompact.isCompact_levG V β L, fun _ hk => hk.1,
    GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L⟩

end GlobalTheory.Mem.LevelSmooth
end

