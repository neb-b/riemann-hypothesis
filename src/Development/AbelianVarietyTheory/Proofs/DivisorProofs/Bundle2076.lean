module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormIffLevelCoverPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoiding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem isJacobsonRing_int_of_dim_one : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_trait_finite_residueField_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  intro B _ _ _ _ m h hm hh
  classical

  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : IsJacobsonRing ℤ := isJacobsonRing_int_of_dim_one
  haveI : Algebra.FiniteType ℤ (B ⧸ m) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m)
  set p := ringChar (B ⧸ m) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (B ⧸ m) 0 := h0 ▸ ringChar.charP (B ⧸ m)
    haveI : CharZero (B ⧸ m) := CharP.charP_to_charZero _
    haveI : Algebra.IsIntegral ℤ (B ⧸ m) := Algebra.IsIntegral.of_finite ℤ _
    exact Int.not_isField
      (isField_of_isIntegral_of_isField (algebraMap ℤ (B ⧸ m)).injective_int (Field.toIsField _))
  haveI : CharP (B ⧸ m) p := ringChar.charP (B ⧸ m)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (B ⧸ m) p).resolve_right hp0⟩
  letI : Algebra (ZMod p) (B ⧸ m) := ZMod.algebra (B ⧸ m) p
  haveI : IsScalarTower ℤ (ZMod p) (B ⧸ m) := AddCommGroup.intIsScalarTower
  haveI : Algebra.FiniteType (ZMod p) (B ⧸ m) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (B ⧸ m)
  haveI : Module.Finite (ZMod p) (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing (ZMod p) (B ⧸ m)
  haveI hfin : Finite (B ⧸ m) := Module.finite_of_finite (ZMod p)
  have hpm : (p : B) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ p
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.mpr hp0

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let R := Localization.AtPrime m
  haveI hRn : IsNoetherianRing R := IsLocalization.isNoetherianRing m.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors m)
  have hx0 : algebraMap B R (h * p) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B R)]; exact fun e => mul_ne_zero hh hpB (hinj e)
  have hxm : algebraMap B R (h * p) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R m _).mpr (m.mul_mem_left h hpm)
  obtain ⟨q, hq, hnq, hdim⟩ := _root_.GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one R (algebraMap B R (h * p)) hx0 hxm
  let D := R ⧸ q
  haveI : IsDomain D := Ideal.Quotient.isDomain q
  haveI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let φ : B →+* D := (Ideal.Quotient.mk q).comp (algebraMap B R)
  have hcompR : Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hcomp : Ideal.comap φ (IsLocalRing.maximalIdeal D) = m := by
    rw [← Ideal.comap_comap, hcompR]; exact Localization.AtPrime.under_maximalIdeal
  have hφh : φ h ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_right _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  have hφp : φ (p : B) ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_left _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  haveI hD0 : CharZero D := by
    haveI : CharP D (ringChar D) := ringChar.charP D
    rcases CharP.char_is_prime_or_zero D (ringChar D) with hl | hl
    · exfalso
      have hlm' : ((ringChar D : ℕ) : B) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal D) := by
        rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]; exact zero_mem _
      have hlm : ((ringChar D : ℕ) : B) ∈ m := hcomp.le hlm'
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hlm
      have hdvd : p ∣ ringChar D := (CharP.cast_eq_zero_iff (B ⧸ m) p _).mp hlm
      have hpl : p = ringChar D :=
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hl).mp hdvd)
      apply hφp; rw [map_natCast, hpl, CharP.cast_eq_zero]
    · haveI : CharP D 0 := hl ▸ ringChar.charP D
      exact CharP.charP_to_charZero D

  have hsurj : Function.Surjective ((IsLocalRing.residue D).comp φ) := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hsR := IsLocalization.surjective_quotientMap_of_maximal_of_localization m.primeCompl R
      (I := IsLocalRing.maximalIdeal R) (J := m)
      (H := le_of_eq Localization.AtPrime.under_maximalIdeal.symm)
      (by rw [Localization.AtPrime.under_maximalIdeal]; exact hm)
    obtain ⟨bb, hb⟩ := hsR (Ideal.Quotient.mk _ r)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bb
    refine ⟨b, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hb
    simp only [RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hb' : algebraMap B R b - r ∈ Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) :=
      hcompR ▸ hb
    simpa [φ, map_sub] using hb'
  have hker : ∀ b ∈ m, ((IsLocalRing.residue D).comp φ) b = 0 := by
    intro b hb
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_comap, hcomp]; exact hb
  haveI hresfin : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_surjective (Ideal.Quotient.lift m _ hker) (by
      intro y; obtain ⟨b, rfl⟩ := hsurj y; exact ⟨Ideal.Quotient.mk m b, rfl⟩)
  obtain ⟨V, _, _, _, hcV, g, hg, hgl, hVfin⟩ :=
    GlobalTheory.exists_complete_dvr_finite_residueField D inferInstance hdim hresfin
  haveI : CharZero V := ⟨fun a b e => by
    apply Nat.cast_injective (R := D); apply hg; rw [map_natCast, map_natCast]; exact e⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, g.comp φ, hcV, hVfin, ?_, ?_⟩
  · rw [RingHom.comp_apply]; intro e; apply hφh; apply hg; rw [e, map_zero]
  · have hgm : Ideal.comap g (IsLocalRing.maximalIdeal V) = IsLocalRing.maximalIdeal D := by
      ext x; simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    rw [← Ideal.comap_comap, hgm, hcomp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.TransNZ

open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec

theorem eq_projectionPullbackSection_of_inverseImage {S : Scheme.{0}} (P : PolAV S) (s : P.L.Sec)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S))) (h : IsPolAVSectionInverseImage P (baseOver S) s th) :
    th = thSec P s := by
  have key : ∀ j : Fin 1 → P.L.ι, th.f j = (thSec P s).f j := by
    intro j
    have hj : j = fun _ => j 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hj, h (j 0) (chart_le P _), projectionPullbackSectionBaseProduct_isInverseImage P s (j 0) (chart_le P _)]
  cases th; cases hth : thSec P s
  simp only [hth] at key
  congr
  exact funext key

end GlobalTheory.TransNZ


open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec in
theorem GlobalTheory.TransNZ.exists_ne : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  have hm1 : 1 ≤ m := by omega
  obtain ⟨i₀, -⟩ := hpt 1 (one_pow _)
  obtain ⟨-, α, s₁, hα, -, hs₁, ht⟩ := hUt i₀
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨a, -, ha⟩ := x.th_ne p₀
  have e := GlobalTheory.TransNZ.eq_projectionPullbackSection_of_inverseImage x.P x.th th hth
  have hp₁ := nonzero_thSec x.P x.th a ha
  rw [← e] at hp₁
  obtain ⟨q, hq⟩ := mulT_surjective x.P m hm1 ((λ_ x.P.A).inv.left.base a)
  have hq' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ α th s₁ hs₁ q (hq ▸ hp₁)
  obtain ⟨r, hr⟩ := translT_surjective x.P.A (U i₀).pt q
  have hr' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ (U i₀).φ s₁ (t i₀) ht r (hr ▸ hq')
  refine ⟨i₀, fun h0 => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hr'
  have hz : (t i₀).f k = 0 := (GlobalTheory.UU.SecMod.eq_zero_iff_coord _).1 h0 k
  rw [hz, Scheme.basicOpen_zero] at hk
  exact hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslateSurj

theorem surjective_of_factor {X Y Z : Scheme.{0}} (p : X ⟶ Y) (O : X.Opens) (g : Z ⟶ X) (q : Z ⟶ Y)
    (hg : g ≫ p = q) (hq : Surjective q) (hO : ∀ z, g z ∈ O) : Surjective (O.ι ≫ p) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hq.surj y
  refine ⟨⟨g z, hO z⟩, ?_⟩
  rw [← hg]
  rfl

end GlobalTheory.TranslateSurj

namespace GlobalTheory.TranslateSurj

theorem exists_translates_surjective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  intro S A _ hA V B j hjV hBs hBg
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI := hBs
  haveI := hBg
  haveI : GeometricallyConnected B.hom := GlobalTheory.geometricallyConnected_of_geometricallyIntegral _
  haveI : Smooth (fst (A ⊗ A) B ≫ fst A A).left := by
    show Smooth (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom); infer_instance
  haveI : GeometricallyConnected (fst (A ⊗ A) B ≫ fst A A).left := by
    show GeometricallyConnected (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    exact GeometricallyConnected.comp _ _
  haveI : GeometricallyIntegral (fst (A ⊗ A) B ≫ fst A A).left := GlobalTheory.geometricallyIntegral_of_smooth _
  have hq : Surjective (fst A B).left := by
    show Surjective (pullback.fst A.hom B.hom); infer_instance
  have key : ∀ (a₀ : A ⊗ B ⟶ A) (w : (A ⊗ A) ⊗ B ⟶ A),
      lift (lift (fst A B) a₀) (snd A B) ≫ w = snd A B ≫ j →
      Surjective ((w.left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
    intro a₀ w hw
    refine surjective_of_factor _ _ (lift (lift (fst A B) a₀) (snd A B)).left (fst A B).left ?_ hq ?_
    · rw [← Over.comp_left]; congr 1; simp
    · intro z
      show w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) ∈ V
      have e : w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) = j.left ((snd A B).left z) := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw, Over.comp_left, Scheme.Hom.comp_apply]
      rw [e]; exact hjV _
  refine _root_.GlobalTheory.surjective_inf_of_geometricallyIntegral _ _ _ _ _ (_root_.GlobalTheory.surjective_inf_of_geometricallyIntegral _ _ _ _ _ (_root_.GlobalTheory.surjective_inf_of_geometricallyIntegral _ _ _ _ _ ?_ ?_) ?_) ?_
  · refine key ((fst A B)⁻¹ * (snd A B ≫ j)) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key ((snd A B ≫ j)⁻¹ * fst A B) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]

end GlobalTheory.TranslateSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularFrameInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_frame_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.InertFrameUnimod.exists_frame_unimod | exact GlobalTheory.InertFrameUnimod.exists_frame_unimod | (intros; apply GlobalTheory.InertFrameUnimod.exists_frame_unimod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCover
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CoverPull

theorem cusp_pullback_existsUnique : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  intro D T j Y e o hT hj hG hu hm a n hD f hf
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  obtain ⟨hL', hbc⟩ := _root_.GlobalTheory.LawsFieldChange.laws_fieldChange D j _ _ _ _ _ Y.c' Y.hle _ _ hL
  obtain ⟨hf', -⟩ := hbc a n hD ⟨f, hf⟩
  obtain ⟨hL₂, -, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hu hm
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  rw [cuspW_wtZ] at hf hf'
  have hs := cusp_le_sec _ _ _ a n hf
  have hs' := cusp_le_sec _ _ _ a n hf'
  obtain ⟨g, ⟨hg, hgP⟩, huniq⟩ := (GlobalTheory.CoverSec.section_pullback_existsUnique _ _ _ _ _ _ Y.d hpq.2 hG.lev.1
    (Or.inl ⟨hpq.1, hL.levA⟩) a n).1 _ hs'
  refine ⟨g, ⟨?_, (hP a n f hs g).2 hgP⟩, fun g' hg' => huniq g' ⟨?_, (hP a n f hs g').1 hg'.2⟩⟩
  · rw [Deep.V, cuspW_wtZ]
    exact (_root_.GlobalTheory.LevCusp.cusp_iff_pull D j _ _ _ _ _ _ _ Y.d _ _ hL' hL₂ hG.lev.1 a n hD hD.2 _ hs' g hg hgP).2 hf'
  · have h := hg'.1
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h

end GlobalTheory.CoverPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitBasicOpenOfCoboundaryIdentity
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

namespace GlobalTheory.LBDescent

theorem coboundary_unit_basicOpen : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (V V₀ : Y.Opens)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
    (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ)
    (r : Γ(Y, V₀)) (m s : Γ(X, f ⁻¹ᵁ V₀)) (n : ℕ),
    ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m →
    m * s = (f.app V₀).hom r ^ n →
    ∃ u : Γ(X, f ⁻¹ᵁ Y.basicOpen r)ˣ, ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ Y.basicOpen r →
      gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  intro X Y f V V₀ h hle c r m s n hm hs
  have hD : Y.basicOpen r ≤ V₀ := Y.basicOpen_le r
  have hfD : f ⁻¹ᵁ Y.basicOpen r ≤ f ⁻¹ᵁ V₀ := fun x hx => hD hx
  have hB : f ⁻¹ᵁ Y.basicOpen r ≤ X.basicOpen ((f.app V₀).hom r) := (Scheme.preimage_basicOpen f r).le
  have hunitA : IsUnit ((X.presheaf.map (homOfLE hfD).op).hom ((f.app V₀).hom r)) := by
    have h1 : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le ((f.app V₀).hom r))).op).hom ((f.app V₀).hom r)) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace _
    have h2 := h1.map (X.presheaf.map (homOfLE hB).op).hom
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at h2
    exact h2
  have hunit : IsUnit ((X.presheaf.map (homOfLE hfD).op).hom m) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hfD).op).hom s)
    rw [← map_mul, hs, map_pow]
    exact hunitA.pow n
  refine ⟨hunit.unit, fun z hz => ?_⟩
  have e : f (pullback.snd f f z) = f (pullback.fst f f z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hz1 : pullback.fst f f z ∈ f ⁻¹ᵁ Y.basicOpen r := hz
  have hz2 : pullback.snd f f z ∈ f ⁻¹ᵁ Y.basicOpen r := by
    show f (pullback.snd f f z) ∈ Y.basicOpen r
    rw [e]; exact hz
  have hz0 : z ∈ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := hD hz
  have hzV : z ∈ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V := hle hz0
  apply Units.ext
  rw [Units.val_mul, gm_val _ z _ hz1, gm_val _ z _ hzV, gm_val _ z _ hz2, IsUnit.unit_spec]
  have k1 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r) z hz1).hom
      (((pullback.fst f f).app (f ⁻¹ᵁ Y.basicOpen r)).hom ((X.presheaf.map (homOfLE hfD).op).hom m)) =
      ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom
        (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    have e1 := congrArg (fun q => q.hom m) ((pullback.fst f f).naturality (homOfLE hfD).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hz0' : z ∈ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := h hz0
  have k2 : ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r) z hz2).hom
      (((pullback.snd f f).app (f ⁻¹ᵁ Y.basicOpen r)).hom ((X.presheaf.map (homOfLE hfD).op).hom m)) =
      ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0').hom
        (((pullback.snd f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    have e1 := congrArg (fun q => q.hom m) ((pullback.snd f f).naturality (homOfLE hfD).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have k4 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom
      (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m) =
      ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0').hom
        (((pullback.snd f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have k3 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom ((res hle c).val) =
      ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) z hzV).hom c.val := by
    simp only [res, Units.coe_map, MonoidHom.coe_coe]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hm' := congrArg ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom hm
  rw [map_mul, k3, k4] at hm'
  rw [k1, k2, ← hm']
  congr 1

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfPinchingSquareGluedUnits
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem germ_appLE_eq_gm_val {Y X : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (O : Y.Opens) (hle : O ≤ f ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ O) (a : Γ(X, U)ˣ) :
    (Y.presheaf.germ O y hy).hom ((f.appLE U O hle).hom a.val) = (gm f y U a).val := by
  rw [gm_val f y U (hle hy)]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y hy _

theorem exists_unit_of_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ), (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) → ∃ u : Γ(X, V)ˣ, (∀ x' : X', p x' ∈ V → gm p x' V u = gm (𝟙 X') x' (p ⁻¹ᵁ V) a) ∧ (∀ z : Z, i z ∈ V → gm i z V u = gm (𝟙 Z) z (i ⁻¹ᵁ V) b) := by
  intro X X' Z Z' p i i' p' _ hG V a b hab
  have key : ∀ (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ),
      (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) →
      ∃! s : Γ(X, V), (p.app V).hom s = a.val ∧ (i.app V).hom s = b.val := by
    intro a b hab
    apply hG V
    apply TopCat.Presheaf.section_ext Z'.sheaf
    intro z hz
    exact (germ_appLE_eq_gm_val i' _ _ inf_le_left z hz a).trans
      ((congrArg Units.val (hab z hz.1)).trans (germ_appLE_eq_gm_val p' _ _ inf_le_right z hz b).symm)
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := key a b hab
  obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := key a⁻¹ b⁻¹ (fun z hz => by rw [map_inv, map_inv, hab z hz])
  have h₁ := key 1 1 (fun z _ => by rw [map_one, map_one])
  have e : s * t = 1 := by
    apply h₁.unique
    · constructor
      · rw [map_mul, hs₁, ht₁, Units.mul_inv, Units.val_one]
      · rw [map_mul, hs₂, ht₂, Units.mul_inv, Units.val_one]
    · constructor
      · rw [map_one, Units.val_one]
      · rw [map_one, Units.val_one]
  refine ⟨⟨s, t, e, (mul_comm _ _).trans e⟩, fun x hx => ?_, fun x hx => ?_⟩
  · apply Units.ext
    rw [gm_val p x V hx, gm_val (𝟙 X') x (p ⁻¹ᵁ V) hx]
    exact congrArg (X'.presheaf.germ (p ⁻¹ᵁ V) x hx).hom hs₁
  · apply Units.ext
    rw [gm_val i x V hx, gm_val (𝟙 Z) x (i ⁻¹ᵁ V) hx]
    exact congrArg (Z.presheaf.germ (i ⁻¹ᵁ V) x hx).hom hs₂

end GlobalTheory.PinchLift
end

