module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import GroundTheory.LocalFields.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits


open GlobalTheory.LocAcyc in
open CategoryTheory in
theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_under p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_under p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.under_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have key : DivConst T' O := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial

  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hle
  intro b c s hs hbc
  have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  rw [IsScalarTower.algebraMap_apply T T' O] at hbc
  obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
  obtain ⟨v, hv⟩ := hunit u
  refine ⟨a, v⁻¹ * w, ?_⟩
  rw [hb, Units.val_mul, ← mul_assoc]
  congr 1
  rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
    IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOrigin
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO
  unfold GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'

end GlobalTheory.VertUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemAllPowers
section
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_v_le {c : L}
    (hc : ∀ m : ℕ, Valued.v c ≤ ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    c = 0 := by
  by_contra h0
  have hv : Valued.v c ≠ 0 := (_root_.map_ne_zero _).2 h0
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.1 hv
  have := hc (1 - Multiplicative.toAdd g).toNat
  rw [← hg, WithZero.coe_le_coe] at this
  have h2 : Multiplicative.toAdd g ≤ -(((1 - Multiplicative.toAdd g).toNat : ℕ) : ℤ) := by
    have := Multiplicative.toAdd_le.2 this
    simpa using this
  omega

theorem int_eq_zero_of_forall_dvd {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c : intL L}
    (hc : ∀ m : ℕ, piO h ^ m ∣ c) : c = 0 := by
  refine Subtype.ext (eq_zero_of_forall_v_le fun m => ?_)
  obtain ⟨d, hd⟩ := hc m
  have hd' : (c : L) = ϖ ^ m * (d : L) := by
    rw [hd]; simp
  have hdv : Valued.v (d : L) ≤ 1 := d.2
  rw [hd', map_mul, map_pow, h.2.2.2.1]
  calc ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * Valued.v (d : L)
      ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * 1 := by gcongr
    _ = _ := by
      rw [mul_one, ← WithZero.coe_pow, ← ofAdd_nsmul]
      congr 2
      simp

theorem eq_zero_of_forall_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) (ha : ∀ m, a ∈ piPow h P m) : a = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_dvd h fun m => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (ha m)
  refine ⟨(GlobalTheory.UTr.powBasis P).repr b i, ?_⟩
  have he : b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m =
      (piO h ^ m) • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  change b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m = a at hb
  rw [← hb, he, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem sep : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ)
    (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P),
    (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 :=
  fun _ _ _ _ _ _ h P a ha => eq_zero_of_forall_mem_piPow h P a ha

end GlobalTheory.NormEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfLowHeightStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  first | (exact @GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (exact GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (intros; apply GlobalTheory.GoodEtale.etale_localization_of_etaleLow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationOfInjectiveCokernelKilledStatement
section
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localization_of_injective_cokernel_killed : ∀ (S : Type) [CommRing S] (A B : Type) [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B), Function.Injective ι → ∀ (p : Ideal S) [p.IsPrime] (s : S), s ∉ p → (∀ y : B, s • y ∈ ι.range) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  first | exact @GlobalTheory.etale_localization_of_cokernel_killed | exact GlobalTheory.etale_localization_of_cokernel_killed | (intros; apply GlobalTheory.etale_localization_of_cokernel_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePunctured
section
open IsLocalRing

namespace GlobalTheory

theorem etale_quotient_of_etale_punctured :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R)
      [IsLocalRing (R ⧸ Ideal.span {f})],
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) →
        Algebra.Etale (Localization.AtPrime P)
          (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P)
            (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  intro R A _ _ _ _ f _ H P _ hP
  set S := R ⧸ Ideal.span {f}
  set T := Localization.AtPrime P
  set p : Ideal R := P.comap (algebraMap R S) with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hx (hu.map _)
    rw [← h] at hr
    exact hr
  haveI := H p hp
  let φ : Localization.AtPrime p →+* T := Localization.localRingHom p P (algebraMap R S) rfl
  letI : Algebra (Localization.AtPrime p) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) T :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show algebraMap R T r = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S T])
  haveI : Algebra.Etale T (TensorProduct (Localization.AtPrime p) T
      (TensorProduct R (Localization.AtPrime p) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) T T A
  let e2 := Algebra.TensorProduct.cancelBaseChange R S T T A
  let e3 : (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[S] TensorProduct R S A :=
    AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {f})).restrictScalars R).trans
        (Algebra.TensorProduct.comm R A S))
  let e4 : TensorProduct S T (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[T]
      TensorProduct S T (TensorProduct R S A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e3
  exact Algebra.Etale.of_equiv (e1.trans (e4.trans e2).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatComplete
section
namespace GlobalTheory.AdicPackage

theorem adicCompletion_package : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B),
    ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧
      IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  intro B _ _ I
  have fg : I.FG := IsNoetherian.noetherian I
  refine ⟨AdicCompletion I B, inferInstance, algebraMap B (AdicCompletion I B),
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I),
    AdicCompletion.isAdicComplete_self I fg, ?_⟩
  intro m a h
  refine le_antisymm ?_ Ideal.le_comap_map
  have key : ∀ y : B, (AdicCompletion.evalₐ I m) (algebraMap B (AdicCompletion I B) y) =
      Ideal.Quotient.mk (I ^ m) y := fun y => (AdicCompletion.evalₐ I m).commutes y
  have hle : a.map (algebraMap B (AdicCompletion I B)) ≤
      (a.map (Ideal.Quotient.mk (I ^ m))).comap (AdicCompletion.evalₐ I m) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [key]
    exact Ideal.mem_map_of_mem _ hy
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h2 := hle hx
  rw [Ideal.mem_comap, key] at h2
  exact (Ideal.mem_quotient_iff_mem h).1 h2

end GlobalTheory.AdicPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDual
section
namespace GlobalTheory.UnitLemma.TwistUnitAny

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← TwistUnit.trace_σ_mem B (β * x * a * B.σ b),
      show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  simp only [InvAlg.herm, ← hT, ← hR] at hU
  have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
    intro y hy
    rw [hU]
    intro y' hy'
    rw [hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by
      linear_combination (β * x * y * B.σ y') * hg]
    exact (hU y').1 hy' y hy
  intro y hy
  rw [hU]
  intro y' hy'
  have hb : B.σ B.g * (B.σ B.g * y') ∈ L := h1 _ (h1 y' hy')
  have := (hU _).1 hb y hy
  rw [hsym] at this
  rw [show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by
    rw [map_mul]; linear_combination (-(β * x * y' * B.σ B.g * B.σ y)) * hg]
  exact this

theorem twisted_unit_eq_unit_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable →
    ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs ε hε
  by_cases hi : IsIntegral K.O B.g
  · exact TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hu : (ε * B.g) * B.σ (ε * B.g) = 1 := by
    rw [map_mul, hσε]; linear_combination B.g * B.σ B.g * hεε + hg
  obtain ⟨β₀, hβ⟩ := GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hLat, hU⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g
      (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi
  · rintro ⟨hLat, h2, -⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi

end GlobalTheory.UnitLemma.TwistUnitAny
end

