module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfFiniteType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.EndLoc.HomFixProper

theorem lbIso_pull_eq {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) := h ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL f)

theorem lbIso_pull_pull {X Y : Scheme.{0}} {L L' : LB X} (h : LBIso L L') (f : Y ⟶ X) :
    LBIso (L.pull f) (L'.pull f) :=
  LBIso.chartPull (chartPullPull L f) (chartPullPull L' f) h

theorem isProper_of_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → QuasiCompact R.π → IsSeparated R.π → LocallyOfFiniteType R.π → IsProper R.π := by
  intro S _ A B _ _ _ _ L M R hA hB hL hM _ _ hqc hsep hlft
  have hex : ValuativeCriterion.Existence R.π := by
    refine _root_.GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing R.π hlft hqc hsep fun V _ _ _ x y hxy => ?_
    haveI := R.hom

    let AV := (Over.pullback y).obj A
    let ψA : AV.left ⟶ A.left := pullback.fst A.hom y
    have hVA : IsGrpPullback AV A y ψA := isGrpPullback_pullback A y
    have hAV : IsAbelianScheme AV := GlobalTheory.isAbelianScheme_pullback_obj y A hA
    let BV := (Over.pullback y).obj B
    let ψB : BV.left ⟶ B.left := pullback.fst B.hom y
    have hVB : IsGrpPullback BV B y ψB := isGrpPullback_pullback B y
    have hBV : IsAbelianScheme BV := GlobalTheory.isAbelianScheme_pullback_obj y B hB

    let AK := (Over.pullback x).obj R.AH
    let pA : AK.left ⟶ R.AH.left := pullback.fst R.AH.hom x
    have hK1A : IsGrpPullback AK R.AH x pA := isGrpPullback_pullback R.AH x
    have hKA : IsGrpPullback AK A (x ≫ R.π) (pA ≫ R.φA) := hK1A.comp R.pbA
    have hKA' : IsGrpPullback AK A (Out.jK V ≫ y) (pA ≫ R.φA) := hKA.congr hxy rfl
    let BK := (Over.pullback x).obj R.BH
    let pB : BK.left ⟶ R.BH.left := pullback.fst R.BH.hom x
    have hK1B : IsGrpPullback BK R.BH x pB := isGrpPullback_pullback R.BH x
    have hKB : IsGrpPullback BK B (x ≫ R.π) (pB ≫ R.φB) := hK1B.comp R.pbB
    have hKB' : IsGrpPullback BK B (Out.jK V ≫ y) (pB ≫ R.φB) := hKB.congr hxy rfl
    let κA : AK.left ⟶ AV.left := hVA.1.lift (pA ≫ R.φA) (AK.hom ≫ Out.jK V)
      ((Category.assoc _ _ _).symm.trans (hKA'.1.w.trans (Category.assoc _ _ _).symm))
    have hκA1 : κA ≫ ψA = pA ≫ R.φA := hVA.1.lift_fst _ _ _
    have hκA2 : κA ≫ AV.hom = AK.hom ≫ Out.jK V := hVA.1.lift_snd _ _ _
    have hκA : IsGrpPullback AK AV (Out.jK V) κA := IsGrpPullback.cancel hVA (hKA'.congr rfl hκA1.symm) hκA2
    let κB : BK.left ⟶ BV.left := hVB.1.lift (pB ≫ R.φB) (BK.hom ≫ Out.jK V)
      ((Category.assoc _ _ _).symm.trans (hKB'.1.w.trans (Category.assoc _ _ _).symm))
    have hκB1 : κB ≫ ψB = pB ≫ R.φB := hVB.1.lift_fst _ _ _
    have hκB2 : κB ≫ BV.hom = BK.hom ≫ Out.jK V := hVB.1.lift_snd _ _ _
    have hκB : IsGrpPullback BK BV (Out.jK V) κB := IsGrpPullback.cancel hVB (hKB'.congr rfl hκB1.symm) hκB2

    let ΦK : AK ⟶ BK := (Over.pullback x).map R.Φ
    have hΦK : IsMonHom ΦK := inferInstance
    have hΦK1 : ΦK.left ≫ pB = pA ≫ R.Φ.left := pullback.lift_fst _ _ _
    obtain ⟨ΦV, hΦV, hΦV1, -⟩ := GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback
      GlobalTheory.homExtension_semiAbelian_dvr V (FractionRing V) AV BV AK BK κA κB hAV hBV hκA hκB ΦK hΦK

    have iso : LBIso (L.pull ψA) ((M.pull ψB).pull ΦV.left) := by
      have hS := GlobalTheory.isSemiAbelian_of_isAbelianScheme AV hAV
      refine GlobalTheory.Poinc.Eq8.StalkPow.lbIso_of_generic_fibre V AV hS _ _ (pull_isLB hL _)
        (pull_isLB (pull_isLB hM _) _) ?_
      have P := hκA.1
      have e : pullback.fst AV.hom (Out.jK V) = P.isoPullback.inv ≫ κA := by simp
      rw [e]
      set u := P.isoPullback.inv
      have i0 := lbIso_pull_pull R.iso (u ≫ pA)
      have hm := pull_isLB hM R.φB
      have eqM : ((u ≫ pA) ≫ R.Φ.left) ≫ R.φB = ((u ≫ κA) ≫ ΦV.left) ≫ ψB := by
        calc ((u ≫ pA) ≫ R.Φ.left) ≫ R.φB = u ≫ (ΦK.left ≫ pB) ≫ R.φB := by
                rw [hΦK1]; simp only [Category.assoc]
            _ = u ≫ ΦK.left ≫ κB ≫ ψB := by rw [hκB1]; simp only [Category.assoc]
            _ = ((u ≫ κA) ≫ ΦV.left) ≫ ψB := by
                rw [← Category.assoc ΦK.left, hΦV1]; simp only [Category.assoc]
      refine LBIso.trans (B := L.pull ((u ≫ κA) ≫ ψA)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := L.pull ((u ≫ pA) ≫ R.φA)) ?_ ?_ ?_
        (lbIso_pull_eq hL (by simp only [Category.assoc, hκA1])) ?_
      rotate_left 3
      refine LBIso.trans (B := (L.pull R.φA).pull (u ≫ pA)) ?_ ?_ ?_
        (LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _)) ?_
      rotate_left 3
      refine LBIso.trans (B := ((M.pull R.φB).pull R.Φ.left).pull (u ≫ pA)) ?_ ?_ ?_ i0 ?_
      rotate_left 3
      refine LBIso.trans (B := (M.pull R.φB).pull ((u ≫ pA) ≫ R.Φ.left)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hm _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull (((u ≫ pA) ≫ R.Φ.left) ≫ R.φB)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull (((u ≫ κA) ≫ ΦV.left) ≫ ψB)) ?_ ?_ ?_
        (lbIso_pull_eq hM eqM) ?_
      rotate_left 3
      refine LBIso.symm (LBIso.trans (B := (M.pull ψB).pull ((u ≫ κA) ≫ ΦV.left)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (pull_isLB hM _) _ _) ?_)
      rotate_left 3
      exact GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _
      all_goals (first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; assumption))))

    obtain ⟨g, ⟨hg, χA, χB, hχA, hχB, hχA1, hχB1, hχΦ⟩, -⟩ :=
      R.rep (Sp V) y AV BV ψA ψB ΦV hVA hVB hΦV iso
    have isoK : LBIso (L.pull (pA ≫ R.φA)) ((M.pull (pB ≫ R.φB)).pull ΦK.left) := by
      have hm := pull_isLB hM R.φB
      refine LBIso.trans (B := (L.pull R.φA).pull pA) ?_ ?_ ?_
        (LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _)) ?_
      rotate_left 3
      refine LBIso.trans (B := ((M.pull R.φB).pull R.Φ.left).pull pA) ?_ ?_ ?_
        (lbIso_pull_pull R.iso pA) ?_
      rotate_left 3
      refine LBIso.trans (B := (M.pull R.φB).pull (pA ≫ R.Φ.left)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hm _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull ((pA ≫ R.Φ.left) ≫ R.φB)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull (ΦK.left ≫ pB ≫ R.φB)) ?_ ?_ ?_
        (lbIso_pull_eq hM (by rw [← Category.assoc, hΦK1])) ?_
      rotate_left 3
      exact LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _)
      all_goals (first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; assumption))))
    obtain ⟨g0, -, huniq⟩ := R.rep (Sp (FractionRing V)) (x ≫ R.π) AK BK (pA ≫ R.φA) (pB ≫ R.φB) ΦK hKA hKB hΦK isoK
    have e1 : x = g0 := huniq x ⟨rfl, pA, pB, hK1A, hK1B, rfl, rfl, hΦK1⟩
    have e2 : Out.jK V ≫ g = g0 := huniq _ ⟨by rw [Category.assoc, hg, hxy], κA ≫ χA, κB ≫ χB,
      hκA.comp hχA, hκB.comp hχB,
      by rw [Category.assoc, hχA1, hκA1], by rw [Category.assoc, hχB1, hκB1],
      by rw [← Category.assoc, hΦV1, Category.assoc, hχΦ, Category.assoc]⟩
    exact ⟨g, e2.trans e1.symm, hg⟩
  haveI : UniversallyClosed R.π := UniversallyClosed.of_valuativeCriterion R.π hex
  exact IsProper.mk

end GlobalTheory.EndLoc.HomFixProper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionRadical

theorem isRadical_map_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] (I : Ideal A) (hI : I.IsRadical)
    (hfib : ∀ (P : Ideal A) [P.IsPrime], _root_.IsReduced (B ⊗[A] P.ResidueField)) :
    (I.map (algebraMap A B)).IsRadical := by
  classical
  haveI : Finite I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).to_subtype
  haveI : Fintype I.minimalPrimes := Fintype.ofFinite _
  haveI hpr : ∀ P : I.minimalPrimes, P.1.IsPrime := fun P => P.2.1.1
  have hle : ∀ P : I.minimalPrimes, I ≤ P.1 := fun P => P.2.1.2
  let g : ∀ P : I.minimalPrimes, (A ⧸ I) →ₐ[A] P.1.ResidueField := fun P =>
    Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom A A P.1.ResidueField) (fun a ha => by
      change algebraMap A P.1.ResidueField a = 0
      exact Ideal.algebraMap_residueField_eq_zero.2 (hle P ha))
  let f : (A ⧸ I) →ₗ[A] ∀ P : I.minimalPrimes, P.1.ResidueField := LinearMap.pi fun P => (g P).toLinearMap
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hI (Ideal.sInf_minimalPrimes (I := I) ▸ ?_)
    refine Ideal.mem_sInf.2 fun P hP => ?_
    have h0 := congrFun hy ⟨P, hP⟩
    haveI : P.IsPrime := hP.1.1
    exact Ideal.algebraMap_residueField_eq_zero.1 h0
  have hfB := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  intro x ⟨n, hn⟩

  have hz : (x ⊗ₜ[A] (1 : A ⧸ I) : B ⊗[A] (A ⧸ I)) = 0 := by
    apply hfB
    rw [map_zero]
    apply (TensorProduct.piRight A A B fun P : I.minimalPrimes => P.1.ResidueField).injective
    rw [map_zero]
    funext P
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, Pi.zero_apply]
    change x ⊗ₜ[A] (g P 1) = 0
    rw [map_one]
    have hnil : IsNilpotent (x ⊗ₜ[A] (1 : P.1.ResidueField) : B ⊗[A] P.1.ResidueField) := by
      refine ⟨n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      change Algebra.TensorProduct.includeLeft (S := A) (x ^ n) = 0
      have hk : I.map (algebraMap A B) ≤ RingHom.ker
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := P.1.ResidueField)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeft_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
          Ideal.algebraMap_residueField_eq_zero.2 (hle P ha), TensorProduct.tmul_zero]
      exact hk hn
    exact hnil.eq_zero
  have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm hz
  rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.EtaleCompletionRadical

namespace GlobalTheory.EtaleCompletionRadical


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_adicCompletion_tensor_residueField (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra.EssFiniteType ℤ A] (P : Ideal A) [P.IsPrime] :
    _root_.IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] P.ResidueField) := by
  have h := GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int
    GlobalTheory.qeRing_of_finiteType_int A P P.ResidueField (IntermediateField.fg_of_noetherian _)
  obtain ⟨-, hreg⟩ := h
  refine isReduced_ofLocalizationMaximal _ fun Q hQ => ?_
  haveI := hreg Q
  infer_instance

theorem isRadical_map_of_isEtaleCompletion : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (φ : A →+* R), IsAdicComplete (maximalIdeal R) R →
    IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → ∀ I : Ideal A, I.IsRadical →
    (I.map φ).IsRadical := by
  intro A R _ _ _ _ _ _ φ hc het hfu I hI
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  haveI := hc
  letI : Algebra A R := φ.toAlgebra
  obtain ⟨g, hg, het'⟩ := GlobalTheory.NormalBaseChange.exists_etale_of_isEtaleCompletion A R het hfu
  letI : Algebra (AdicCompletion (maximalIdeal A) A) R := g.toAlgebra
  have h1 : (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).IsRadical :=
    isRadical_map_of_flat I hI fun P _ => isReduced_adicCompletion_tensor_residueField A P
  have h2 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := R) _ h1
  rw [Ideal.map_map] at h2
  change (I.map (g.comp _)).IsRadical at h2
  rwa [hg] at h2

end GlobalTheory.EtaleCompletionRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVariety
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

theorem crt_split {G : Type} [CommGroup G] {a b : ℕ} {u v : ℤ} (huv : u * a + v * b = 1) (x : G)
    (hx : x ^ (a * b) = 1) : (x ^ (v * b)) ^ a = 1 ∧ (x ^ (u * a)) ^ b = 1 ∧ x ^ (v * b) * x ^ (u * a) = x := by
  have hx' : x ^ ((a : ℤ) * b) = 1 := by
    rw [← Nat.cast_mul, zpow_natCast, hx]
  refine ⟨?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, show v * (b : ℤ) * a = a * b * v by ring, zpow_mul, hx', one_zpow]
  · rw [← zpow_natCast, ← zpow_mul, show u * (a : ℤ) * b = a * b * u by ring, zpow_mul, hx', one_zpow]
  · rw [← zpow_add, show v * (b : ℤ) + u * a = 1 by linarith, zpow_one]

theorem crt_unique {G : Type} [CommGroup G] {a b : ℕ} {u v : ℤ} (huv : u * a + v * b = 1) {y₁ y₂ : G}
    (h₁ : y₁ ^ a = 1) (h₂ : y₂ ^ b = 1) : (y₁ * y₂) ^ (v * b) = y₁ ∧ (y₁ * y₂) ^ (u * a) = y₂ := by
  have h₁' : y₁ ^ (a : ℤ) = 1 := by rw [zpow_natCast, h₁]
  have h₂' : y₂ ^ (b : ℤ) = 1 := by rw [zpow_natCast, h₂]
  have e₁ : y₁ = y₁ ^ (u * a) * y₁ ^ (v * b) := by rw [← zpow_add, huv, zpow_one]
  have e₂ : y₂ = y₂ ^ (u * a) * y₂ ^ (v * b) := by rw [← zpow_add, huv, zpow_one]
  have a₁ : y₁ ^ (u * (a : ℤ)) = 1 := by rw [mul_comm, zpow_mul, h₁', one_zpow]
  have b₂ : y₂ ^ (v * (b : ℤ)) = 1 := by rw [mul_comm, zpow_mul, h₂', one_zpow]
  refine ⟨?_, ?_⟩
  · rw [mul_zpow, b₂, mul_one]
    conv_rhs => rw [e₁, a₁, one_mul]
  · rw [mul_zpow, a₁, one_mul]
    conv_rhs => rw [e₂, b₂, mul_one]

variable {k : Type} [Field k] {A B : AbVar k}

def postHom {T : Over (Sp k)} (f : A ⟶ B) : (T ⟶ A.X) →* (T ⟶ B.X) :=
  MonoidHom.mk' (fun x => x ≫ f.hom) fun x y => MonObj.mul_comp x y f.hom

theorem spMap_comp_left_iff {H R : Type} [CommRing H] [Algebra k H] [CommRing R] [Algebra k R] (φ : H →ₐ[k] R)
    (i : ptOver k H ⟶ A.X) (x : ptOver k R ⟶ A.X) : spMap φ.toRingHom ≫ i.left = x.left ↔ spOver φ ≫ i = x :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => by subst h; rfl⟩

theorem kerPow_mul_of_coprime : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (a b : ℕ), a.Coprime b →
    ∀ (H₁ : Type) [CommRing H₁] [Algebra k H₁] (i₁ : ptOver k H₁ ⟶ A.X) (H₂ : Type) [CommRing H₂] [Algebra k H₂]
    (i₂ : ptOver k H₂ ⟶ A.X), KerPow f a H₁ i₁ → KerPow f b H₂ i₂ → ∃ (H : Type) (_ : CommRing H)
    (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f (a * b) H i ∧
      Module.finrank k H = Module.finrank k H₁ * Module.finrank k H₂ := by
  intro k _ A B f a b hab H₁ _ _ i₁ H₂ _ _ i₂ h₁ h₂
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hab
  let inl : H₁ →ₐ[k] H₁ ⊗[k] H₂ := Algebra.TensorProduct.includeLeft
  let inr : H₂ →ₐ[k] H₁ ⊗[k] H₂ := Algebra.TensorProduct.includeRight
  refine ⟨H₁ ⊗[k] H₂, inferInstance, inferInstance, (spOver inl ≫ i₁) * (spOver inr ≫ i₂),
    ⟨⟨?_, ?_⟩, ?_⟩, Module.finrank_tensorProduct⟩
  · rw [MonObj.mul_comp, Category.assoc, Category.assoc, h₁.1.1, h₂.1.1, MonObj.comp_one, MonObj.comp_one, mul_one]
  · rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, pow_mul, h₁.1.2, one_pow, mul_comm a b, pow_mul, h₂.1.2,
      one_pow, MonObj.comp_one, MonObj.comp_one, mul_one]
  · intro R _ _ x hx hxab
    obtain ⟨hx₁, hx₂, hx12⟩ := crt_split huv x hxab
    have hf : ∀ n : ℤ, (x ^ n) ≫ f.hom = 1 := fun n => by
      change postHom f (x ^ n) = 1
      rw [map_zpow]
      change (x ≫ f.hom) ^ n = 1
      rw [hx, one_zpow]
    obtain ⟨φ₁, hφ₁, hu₁⟩ := h₁.2 R _ (hf _) hx₁
    obtain ⟨φ₂, hφ₂, hu₂⟩ := h₂.2 R _ (hf _) hx₂
    rw [spMap_comp_left_iff] at hφ₁ hφ₂
    refine ⟨Algebra.TensorProduct.productMap φ₁ φ₂, ?_, fun ψ hψ => ?_⟩
    · refine (spMap_comp_left_iff _ _ _).2 ?_
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
      change spOver ((Algebra.TensorProduct.productMap φ₁ φ₂).comp Algebra.TensorProduct.includeLeft) ≫ i₁ *
        spOver ((Algebra.TensorProduct.productMap φ₁ φ₂).comp Algebra.TensorProduct.includeRight) ≫ i₂ = x
      rw [Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right, hφ₁, hφ₂, hx12]
    · replace hψ := (spMap_comp_left_iff _ _ _).1 hψ
      have hy : (spOver (ψ.comp inl) ≫ i₁) * (spOver (ψ.comp inr) ≫ i₂) = x := by
        rw [← spOver_comp, ← spOver_comp, Category.assoc, Category.assoc, ← MonObj.comp_mul]
        exact hψ
      have hy₁ : (spOver (ψ.comp inl) ≫ i₁) ^ a = 1 := by rw [← MonObj.comp_pow, h₁.1.2, MonObj.comp_one]
      have hy₂ : (spOver (ψ.comp inr) ≫ i₂) ^ b = 1 := by rw [← MonObj.comp_pow, h₂.1.2, MonObj.comp_one]
      obtain ⟨e₁, e₂⟩ := crt_unique huv hy₁ hy₂
      rw [hy] at e₁ e₂
      have k₁ : ψ.comp inl = φ₁ := hu₁ _ ((spMap_comp_left_iff _ _ _).2 e₁.symm)
      have k₂ : ψ.comp inr = φ₂ := hu₂ _ ((spMap_comp_left_iff _ _ _).2 e₂.symm)
      apply Algebra.TensorProduct.ext
      · rw [Algebra.TensorProduct.productMap_left]; exact k₁
      · exact k₂.trans (Algebra.TensorProduct.productMap_right φ₁ φ₂).symm

end GlobalTheory.AV.KerPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverImageOpenFiniteOverModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OpenLev

theorem exists_open_finite : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (fM : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → MinorAt S X M U₀ EE fM Xab → (abLocus Zh.G : Set M.Z) = fM ⁻¹' (Xab : Set X.Z) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ abLocus Zh.G := by
  intro g n _ _ _ F W _ o Ω _ _ _ _ β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin hab hd hdo
  obtain ⟨-, -, -, h0, -, hfM, -, hiso⟩ := hmin
  have hsurj := GlobalTheory.T.surjective_functionFieldModelHom_of_projective o Ω X M fM hfM h0.proj
  have hrange : Set.range d ⊆ Xab := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hsurj (d y)
    obtain ⟨V, _, _, _, ξ, τ, κ, hzξ, h1, h2⟩ := _root_.GlobalTheory.DvrTrait.exists_trait o Ω Y X M fM d hfM hd hdo z ⟨y, hz.symm⟩
    have hzab : z ∈ (abLocus Zh.G : Set M.Z) :=
      _root_.GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait g n F W o Ω β S ρ u hsys Y M q U₀ EE Zh hlev h0 V ξ τ κ h1 h2 hzξ
    rw [hab] at hzab
    show d y ∈ (Xab : Set X.Z)
    rw [← hz]
    exact hzab
  obtain ⟨U, c, hc, hU⟩ := _root_.GlobalTheory.SiegTh.exists_openAt_of_levAt g n F o Ω β S u Y X M q fM Xab d hlev hfM hiso hd hdo hrange
  exact ⟨U, c, hc, hab ▸ hU⟩

end GlobalTheory.OpenLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormGradedLengthSubLogUnitNormSq
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leviForm_neg_log_unit_sub_log_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i c hy
  obtain ⟨W, hW, a, rfl⟩ := hu.regAt.exists_fnOf
  have hyW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 hW
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hm := ChartGlue.mem_over c.e hy hyW
  have hg := c.holo W a
  have hf : ContDiffAt ℂ 2 (ev X.str σ W a ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn hg (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev X.str σ W a ∘ c.e.symm) (c.e y) ≠ 0 := by
    have := ratVal_ne_zero hu
    rw [ratVal_fnOf hyW] at this
    simpa [Function.comp, c.e.left_inv hy] using this
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have hsm := ((_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m k E H hH y A hA τ).2 c hy).self_of_nhds
  have hG := (ldPart_grD_smooth _ _ _ _ hsm.1 hsm.2).2 i
  have hpos := ((_root_.GlobalTheory.ChernCalc.ldPart_posDef_spec _ _ hsm.2).2.1 i).1
  have hD : ContDiffAt ℝ 2 (fun v => Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) :=
    (hG.log hpos.ne').of_le (WithTop.coe_le_coe.2 le_top)
  rw [leviForm_congr (u' := fun v => -Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2) +
      -Real.log (grD (H A (c.e.symm v) τ) i)), leviForm_add hlog.neg hD.neg,
    leviForm_neg (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)), leviForm_log_normSq_eq_zero hf h0,
    neg_zero, zero_add]
  filter_upwards [ho.mem_nhds hm] with v hv
  simp only [Function.comp, sub_eq_add_neg]
  rw [ratVal_fnOf hv.2]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLoci
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.HSAmp.pow_sec_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p P e
  have hR : P.Rep ((e : ℤ) * 1) ((e : ℤ) * 0) (P.L.pow e) :=
    GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L e (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  rw [mul_one, mul_zero] at hR
  obtain ⟨g, -, hrange, -, hloc⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P (e : ℤ) 0 (P.L.pow e) hR
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have key : ∀ u : (lbPow P.L.B e).Sec, NV P e 0 (g u) = (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X) := by
    intro u
    ext x
    obtain ⟨i, hi⟩ := hcov P.L.isLB x
    obtain ⟨j, hj⟩ := hcov P.A.isLB x
    constructor
    · intro h
      exact (hloc u x i j hi hj).2 (h i j hi hj)
    · intro h i' j' hi' hj'
      exact (hloc u x i' j' hi' hj').1 h
  refine ⟨fun u => ⟨g u, ?_, key u⟩, fun f hf => ?_⟩
  · have : g u ∈ Set.range g := ⟨u, rfl⟩
    rw [hrange] at this
    exact this
  · have : f ∈ Set.range g := by rw [hrange]; exact hf
    obtain ⟨u, rfl⟩ := this
    exact ⟨u, key u⟩
end
end

