module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealElementPullbackClosedFibreZero
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreScalar

theorem appLE_eq_of_eq {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem fromSpec_appLE_top {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

theorem spMap_chart_appLE_top {X : Scheme.{0}} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (e : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1) :
    (spMap (Ideal.Quotient.mk m) ≫ chart U).appLE U.1 ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk m) := by
  have e1 : (⊤ : (Sp Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤ := le_top
  have hk := fromSpec_appLE_top U.2 e1
  change (spMap (Ideal.Quotient.mk m) ≫ U.2.fromSpec).appLE U.1 ⊤ e ≫ _ = _
  have hk' : U.2.fromSpec.appLE U.1 ⊤ e1 ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U.1))).hom = 𝟙 _ := hk
  rw [← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) U.2.fromSpec _ ⊤ _ e1 e2, Category.assoc,
    specMap_appLE_top, ← Category.assoc, hk', Category.id_comp]

theorem fibre_scalar_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O) (r : Γ(X, U.1)), r ∈ m → (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom r) = 0 := by
  intro E _ _ _ H X t U m A _ ι hpb O hO O' hO' r hr
  set g := spMap (Ideal.Quotient.mk m) ≫ chart U with hg
  have hw : ι ≫ t.G.hom = A.hom ≫ g := hpb.1.w
  have e5 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ g ⁻¹ᵁ U.1 := by
    intro x _
    change g x ∈ U.1
    rw [hg, Scheme.Hom.comp_apply]
    exact U.2.fromSpec_preimage_self.ge (Set.mem_univ _)
  have hz : (g.appLE U.1 ⊤ e5).hom r = 0 := by
    have h := congrArg (fun φ => φ.hom r) (spMap_chart_appLE_top U m e5)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr hr] at h
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom).1
    exact hinj (h.trans (map_zero _).symm)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hw,
    ← Scheme.Hom.appLE_comp_appLE A.hom g U.1 ⊤ O' e5 (fun x _ => trivial), CommRingCat.comp_apply, hz, map_zero]

end GlobalTheory.FibreScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralFiniteAdelesOfMemCompletion
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

theorem mem_hatId_of_inHat : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D,
  InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (GlobalTheory.BotFormula.toFinE D x) → x ∈ hatId D 𝔪 := by
  intro D 𝔪 h𝔪 x hx
  have hI : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔪)
  obtain ⟨a, s, hs, e⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx x hN
  have hNm : ((Ideal.absNorm 𝔪 : ℕ) : D.host.E) ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem 𝔪, map_natCast _ _⟩
  have ha : a ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    refine (GlobalTheory.NumeratorIdeal.mem_iff_valuation D.host.E hI a).2 fun w => ?_
    rw [← GlobalTheory.Mem.Col2.SplitChar.vl_inc, eq_sub_of_add_eq e.symm]
    refine Valuation.map_sub_le _ ?_ ?_
    · rw [GlobalTheory.Mem.Col2.SplitChar.vl_apply, GlobalTheory.NormRatio.ChrFin.adEquiv_eq]
      exact hx w
    · rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat]
      exact (mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs w)).trans
        ((GlobalTheory.NumeratorIdeal.mem_iff_valuation D.host.E hI _).1 hNm w)
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩)
    (AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, s, hs, ?_⟩)
  exact congrArg (· * s) (map_natCast ((Formalism.MainNotions.StandardLatticesGL3.inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)) _).symm

end GlobalTheory.CosetOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtVert

theorem isEmpty_cxPts {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k) (σ : k →+* ℂ) (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : κ →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (y.1.appTop.hom.comp (algebraMap κ Γ(Z, ⊤)))
  have : CharZero κ := f.charZero
  exact not_finite κ

theorem mixArch_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  have h0 : ∀ (L' : HermLB q), L'.archInt M e hr = 0 := by
    intro L'
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    have := h σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  simp [mixArch, FibreProj.pol, h0]

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem finite_Γ {Z : Scheme.{0}} [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] [IsAffine Z]
    (hp : IsProjOver (strHom κ (X := Z))) (φ : Γ(Z, ⊤) →+* Z.residueField (genericPoint Z)) (hφ : Function.Bijective φ) :
    Finite Γ(Z, ⊤) := by
  have : IsProper (strHom κ (X := Z)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have h1 : (strHom κ Z).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) |>.1 inferInstance
  have h2 : (algebraMap κ Γ(Z, ⊤)).FiniteType := by
    have e : algebraMap κ Γ(Z, ⊤) = (strHom κ Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom :=
      RingHom.ext (algebraMap_eq_strHom κ Z)
    rw [e]
    exact h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hft : Algebra.FiniteType κ Γ(Z, ⊤) := RingHom.finiteType_algebraMap.1 h2
  letI : Algebra κ (Z.residueField (genericPoint Z)) := (φ.comp (algebraMap κ Γ(Z, ⊤))).toAlgebra
  let ψ : Γ(Z, ⊤) →ₐ[κ] Z.residueField (genericPoint Z) := { φ with commutes' := fun _ => rfl }
  have : Algebra.FiniteType κ (Z.residueField (genericPoint Z)) := Algebra.FiniteType.of_surjective ψ hφ.2
  have : Module.Finite κ (Z.residueField (genericPoint Z)) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Finite (Z.residueField (genericPoint Z)) := Module.finite_of_finite κ
  exact Finite.of_injective φ hφ.1

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem hasDim_iff {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ) :
    HasDim (i (genericPoint Z)) d ↔ topologicalKrullDim Z = d := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [HasDim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm]

theorem dim_zero {X : Scheme.{0}} {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (h0 : topologicalKrullDim Z = (0 : ℕ))
    (hp : IsProjOver (strHom κ (X := Z))) :
    Real.log (Nat.card (X.residueField (i (genericPoint Z)))) = chi κ (structureModule Z) * Real.log (Nat.card κ) := by
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hZ : ({genericPoint Z} : Set Z) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint Z} : Set Z) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (Z.fromSpecResidueField (genericPoint Z)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (Z.fromSpecResidueField (genericPoint Z))
  have : IsAffine Z := .of_isIso (inv (Z.fromSpecResidueField (genericPoint Z)))
  have : IsIso (Z.fromSpecResidueField (genericPoint Z)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (i.residueFieldMap (genericPoint Z)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := Z.residue_surjective _ a
    obtain ⟨b, rfl⟩ := i.stalkMap_surjective _ a
    exact ⟨X.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((Z.fromSpecResidueField (genericPoint Z)).appTop ≫
      (Scheme.ΓSpecIso (Z.residueField (genericPoint Z))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(Z, ⊤) ≃ X.residueField (i (genericPoint Z)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  have : Finite Γ(Z, ⊤) := finite_Γ κ hp _ b₂
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, Module.natCard_eq_pow_finrank (K := κ)]
  simp

theorem isProjOver_strHom {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hX : IsAmb p) {Z : Scheme.{0}}
    (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)] : IsProjOver (strHom κ (X := Z)) := by
  have := hX.finite
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have hpr' : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2 ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem mixHt_pow_eq_topSelf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  intro k _ X p hA m T hT N d
  induction d with
  | zero =>
    intro _ Z i _ _ κ _ _ _ hd
    rw [hT.zero _ _ ((hasDim_iff i 0).2 hd), dim_zero i κ hd (isProjOver_strHom hA i κ), topSelf_def,
      interNum_of_isEmpty]
  | succ e ih =>
    intro hm Z i _ _ κ _ _ _ hd
    have hZa : IsAmb (i ≫ p) := hA.sub i
    have : IsNoetherian Z := hZa.isNoetherian
    have hp := isProjOver_strHom hA i κ
    have : IsProper (strHom κ (X := Z)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    obtain ⟨r, hr⟩ := exists_isRatSec (N.restr i).isLB
    have hL : (N.B.pull i).IsLB := (N.restr i).isLB
    have hrec := hT.recur Z (i ≫ p) i rfl e hm hd N (fun _ => N) (N.restr i) (fun _ => N.restr i)
      (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
    have ec : (Fin.cons N (fun _ => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec] at hrec
    rw [hrec, recVal, mixArch_eq_zero (fun σ => isEmpty_cxPts (i ≫ p) σ κ), sub_zero]
    have key := GlobalTheory.ratSec_cycle_formula κ Z hp e hd.le (N.B.pull i) hL (fun _ => N.B.pull i) (fun _ => hL) r hr
    have ec' : (Fin.cons (N.B.pull i) (fun _ => N.B.pull i) : Fin (e + 1) → LB Z) = fun _ => N.B.pull i :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec', ← topSelf_def] at key
    have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hL hr).mult w *
        interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) fun _ : Fin e => N.B.pull i :=
      (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
    rw [key]
    have em := (AddMonoidHom.mulRight (Real.log (Nat.card κ))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
    refine .trans (finsum_congr fun z => ?_) em.symm
    change ((divOfRatSec hL hr).mult z : ℝ) * _ = (((divOfRatSec hL hr).mult z * _ : ℤ) : ℝ) * _
    by_cases hz : (divOfRatSec hL hr).mult z = 0
    · simp [hz]
    rw [Int.cast_mul, mul_assoc]
    refine congrArg _ ?_
    have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Z) hd
      (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
    obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have hrange : Set.range j = closure {j (genericPoint W)} := by
      rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
    letI := algebraΓAlong κ j
    have hW : topologicalKrullDim W = e :=
      (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
    rw [← Scheme.Hom.comp_apply, ih (by omega) W (j ≫ i) κ hW, InterModel.interNumRed_eq_interNumOn _ j _ hrange,
      interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun _ => hL), topSelf_def]
    congr 2
    refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull N.isLB _) (fun _ => LB.isLB_pull hL _) fun _ => ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull N.isLB, CechPic.cls_pull N.isLB, CechPic.pull_comp]

end GlobalTheory.MixHtVert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.MixVacBig

open GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem isIdemSum_atPl (hL : L.Is μ₀) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) : IsIdemSum (atPl w 1) {w} := by
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  have h := hes w hw
  rw [← GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h]
  exact ⟨⟨fun _ => es w, fun P hP => by rw [Finset.mem_singleton.1 hP]; exact h, by simp⟩, h.1.2.1⟩

theorem aa_unit_of_standing {t : T} (hst : SquareStanding G t) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
  have h := hst.2 w hw
  rw [Nat.cast_mul] at h
  exact GlobalTheory.AAUnit.aa_unit D w (fun h' => h (w.asIdeal.mul_mem_right _ h')) fun h' => h (w.asIdeal.mul_mem_left _ h')

theorem coord_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ}
    (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (B.coord t w hX hY (z.map (atW w))) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) := by
  have e : z.map (atW w) = (z.map (toEAf D)).map (cpt (D := D) w) := rfl
  rw [e, Comparison₂.coord_map]
  refine ⟨fun H a b => ?_, fun H a b => H _ _⟩
  have := H (b.cast (rank_vertex G t w hY).symm) (a.cast (rank_vertex G t w hX).symm)
  simpa only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.cast_cast, Fin.cast_eq_self] using this

theorem mem_lat_iff (hL : L.Is μ₀) (B : Frames G) (t : T) (hst : SquareStanding G t) {i j : Fin D.R.m} (e : Num G i j)
    {w : Pl D.host.E} (hw : w ∈ locPl G t) {x : Pt G i j} (hx : x ∈ mixHalf e (atPl w 1)) :
    (mapV e x ∈ latV G i j ∧ mapW e x ∈ latW G i j) ↔
      ∀ r s, mixCo B t e w x r s ∈ (ValuativeRel.valuation (Kw w)).integer := by
  have hI := isIdemSum_atPl hL t hw
  have hA : ∀ w' ∈ ({w} : Finset (Pl D.host.E)), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w') a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w') a) = 1) := fun w' hw' => by
    rw [Finset.mem_singleton.1 hw']
    exact aa_unit_of_standing hst hw
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg hT₁
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have fW := B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2
  have fV := B.isFrame_β hL (i := (i : ℕ)) (j := (j : ℕ) + 1) i.2.le j.2
  have fV₁ := B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ)) i.2 j.2.le
  have k₁ := GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT fW fV hI hA (mapV e x) hx.1
  have k₂ := GlobalTheory.ColLatDict.mem_latO_iff_intM hS₁ hT₁ fV₁ fW hI hA (mapW e x) hx.2
  simp only [Finset.mem_singleton, forall_eq] at k₁ k₂
  have c₁ := coord_int_iff B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ (mapV e x)
  have c₂ := coord_int_iff B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ (mapW e x)
  refine (and_congr (k₁.trans c₁.symm) (k₂.trans c₂.symm)).trans ?_
  rw [mixCo_eq]
  refine ⟨fun H r s => ?_, fun H => ⟨fun r s => H r (.inl s), fun r s => H s (.inr r)⟩⟩
  rcases s with s | s
  · exact H.1 r s
  · exact H.2 s r


set_option maxHeartbeats 800000 in
theorem mix_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToA G t i j w, IsMixModelA W B t e Γ w ι →
      ι (Γ.M.vac _) = ι (Γ.M.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti w hw ι hι
  classical
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hid, -⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := GlobalTheory.BigDat.lagr_vac hι (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _
      (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 hh.2.2.2.1
  funext z
  obtain ⟨x, hx, rfl⟩ := (hco w).2.1 z
  have key := mem_lat_iff hL B t hst e hw hx
  rw [hv.2 x hx, Pi.smul_apply, smul_eq_mul]
  by_cases hl : mapV e x ∈ latV G i j ∧ mapW e x ∈ latW G i j
  · rw [Set.indicator_of_mem (show x ∈ (latPt e (w.under (𝓞 D.host.F)) : Set _) from ⟨hh.1 x hx, hl⟩),
      Set.indicator_of_mem (show mixCo B t e w x ∈ {Z : MatA G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer}
        from key.1 hl), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (show x ∉ (latPt e (w.under (𝓞 D.host.F)) : Set _) from fun h' => hl h'.2),
      Set.indicator_of_notMem (show mixCo B t e w x ∉ {Z : MatA G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer}
        from fun h' => hl (key.2 h')), mul_zero]

end GlobalTheory.MixVacBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem VS.mul : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  intro R Ω _ _ _ φ Y L hL x g k l s s' h h'
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  obtain ⟨r', σ', ω', hr', hv', he'⟩ := h'
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 Y) (fun _ : Fin 1 => 𝟙 Y))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) (fun _ : Fin 1 => (l : ℤ)))
      (fun _ : Fin 1 => 𝟙 Y) (fun _ => ((k + l : ℕ) : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
    push_cast
    rw [zpow_add]
  obtain ⟨σ'', hσ''⟩ := exists_sec hL hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec σ σ')
  refine ⟨r * r', σ'', ω * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z q z J hJ
    rw [hσ'' Z (q ≫ x) z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec σ σ' (q ≫ x) z hJ, hv Z q z J hJ, hv' Z q z J hJ,
      map_mul, gs_mul q z ⊤ trivial, pow_add, Units.val_mul]
    ring
  · rw [map_mul, map_mul, map_mul, he, he']
    ring

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordSectionsMultiplierThickenings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, 3 ≤ k → ∃ S : H0 U.LG.L k → H0 U.LG.L (N * k), ∃ c : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'), (∀ (e : ℕ) (s : H0 U.LG.L k) (i i' : Fin 1 → U.LG.L.ι), ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_right : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')).op).hom (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((S s).f i')) = c e i i' * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i') := by
  have hA := _root_.GlobalTheory.MumMult.chart_main
  have hU := _root_.GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, m, hm, y, hy1, hy2⟩ := hA R hB D A G hG U a a' h h' hE b hb
  refine ⟨N, hN, fun k hk => ?_⟩
  choose F hF using hm k hk
  have hNk : 1 ≤ N * k := Nat.mul_pos hN (by omega)
  choose σ hσ using fun s => _root_.GlobalTheory.Mum.IntFam.exists_expandsAt R hB D A G U hG (N * k) hNk (F s)
  refine ⟨σ, fun e i i' => m e i i' ^ k, fun e s i i' => ?_, y, hy1, fun i i' hyW => ?_⟩
  · exact hU R _ D A G U.toUnifPre e (N * k) (σ s) (F s).f i' _ inf_le_right _ (hσ s e) (hF s e i i')
  · show y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i' ^ k)
    have hk0 : 0 < k := by omega
    first
      | (rw [Scheme.basicOpen_pow _ _ hk0]; exact hy2 i i' hyW)
      | (rw [Scheme.basicOpen_pow _ hk0]; exact hy2 i i' hyW)
      | (rw [Scheme.basicOpen_pow _ _ _ hk0]; exact hy2 i i' hyW)
      | (simpa [Scheme.basicOpen_pow, hk0] using hy2 i i' hyW)

end GlobalTheory.MumMult
end

