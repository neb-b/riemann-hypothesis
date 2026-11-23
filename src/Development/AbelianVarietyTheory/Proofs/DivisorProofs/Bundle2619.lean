module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem famTw_eq_of_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  intro R _ _ I D N σ F₀ s hs
  have hL := D.P.isLB
  refine fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (sec_ext' hL fun y J hJ => ?_)
  show sval (termPull D (Kb R) (TwF σ) N α (s.s α)) (𝟙 _) y J = _
  refine (sval_pullOver _ _ _ _ hJ).trans ?_
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, ← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ]
  congr 1
  have e : (famMap D (Kb R) (TwF σ)).left ≫ (DegPre.prB D (Kb R)).left = (DegPre.prB D (TwF σ)).left :=
    congrArg (fun q => q.left) (famMap_snd D (Kb R) (TwF σ))
  exact (Category.assoc _ _ _).trans (congrArg (fun q => 𝟙 _ ≫ q) e)

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem famTw_isSmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N),
    Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  intro R _ _ D N σ c s s' h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff] at h
  subst h
  intro α j
  have e := map_smulₛₗ (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N) c s
  exact congrArg (fun q : Fam D (TwF σ) N => (q.s α).f j) e

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_twK (σ τ : Kb R →ₐ[FractionRing R] Kb R) (h : τ.comp σ = AlgHom.id _ _) :
    twK τ ≫ twK σ = 𝟙 _ := by
  ext1
  rw [Over.comp_left, twK_left, twK_left, Over.id_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [this]
  exact Spec.map_id _

theorem mTw_comp_mTw_left (A : PolAV (Sp (FractionRing R))) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) : (mTw A τ).left ≫ (mTw A σ).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : mTw A τ ≫ mTw A σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_twK σ τ h,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]
  rw [this]; rfl

theorem secTw_secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    secTw A N τ (secTw A N σ t) = t := by
  refine GlobalTheory.FieldBaseChange.sec_ext' A.isLB fun y J hJ => ?_
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
    ((GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_)
  rw [Category.assoc, mTw_comp_mTw_left A σ τ h, Category.comp_id]

theorem secTw_bijective (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (secTw A N σ) := by
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have h1 : τ.comp σ = AlgHom.id _ _ := by
    ext x; exact e.symm_apply_apply x
  have h2 : σ.comp τ = AlgHom.id _ _ := by
    ext x; exact e.apply_symm_apply x
  exact ⟨Function.LeftInverse.injective (g := secTw A N τ) (secTw_secTw A N σ τ h1),
    Function.RightInverse.surjective (g := secTw A N τ) (secTw_secTw A N τ σ h2)⟩

end GlobalTheory.Mum.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_add_chart : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  intro R _ _ A N σ t t' t'' h j
  show GlobalTheory.FieldBaseChange.pullFn _ _ (t''.f j) =
    GlobalTheory.FieldBaseChange.pullFn _ _ (t.f j) + GlobalTheory.FieldBaseChange.pullFn _ _ (t'.f j)
  rw [h j]
  exact map_add _ _ _

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_chart_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) →
    ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  intro R _ _ A N σ c t t' h j
  have ht : @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' =
      c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t :=
    GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun i => h i
  have e : secTw A N σ t' = σ c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ))))
      (secTw A N σ t) := by
    unfold secTw
    rw [show t' = @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' from rfl,
      ht, map_smulₛₗ]
    rfl
  rw [e]
  rfl

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem comp_mTw_left_eq {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))
    (σ : Kb R →ₐ[FractionRing R] Kb R) {Z : Scheme.{0}} {p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left}
    (h₂ : p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left)
    (h₁ : p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom) :
    p ≫ (mTw A σ).left = p' := by
  refine pullback.hom_ext (f := (TFK (R := R) (Kb R)).hom) (g := A.A.hom) ?_ ?_
  · change (p ≫ (mTw A σ).left) ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_fst_left, h₁]
  · change (p ≫ (mTw A σ).left) ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_snd_left, h₂]

theorem secTw_isTwist (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    SecTw σ t (secTw A N σ t) := by
  intro Z p p' h₂ h₁ z J hJ
  rw [← comp_mTw_left_eq A σ h₂ h₁]
  exact GlobalTheory.FieldBaseChange.sval_pullOver (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t p hJ

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QeRingOfFiniteTypeInt
section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem qeRing_of_finiteType_int : ∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], FinalTheorems.QERing A := by
  intro A _ _
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  refine ⟨hN, fun P _ => ⟨?_, ?_⟩, fun B _ _ _ => ?_⟩
  · exact AdicCompletion.flat_of_isNoetherian _
  · apply _root_.GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType
    intro K _ _ _
    haveI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
      Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime P) :=
      Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime P)
    have hZ : @Algebra.EssFiniteType ℤ (Localization.AtPrime P) _ _ (Ring.toIntAlgebra _) := by
      convert this
      exact Subsingleton.elim _ _
    exact @_root_.GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int (Localization.AtPrime P) K _ _ hZ _ _ _
  · haveI : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A) ‹_›
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    exact _root_.GlobalTheory.isOpen_regularLocus_of_nagata B (fun p _ => _root_.GlobalTheory.generically_regular_quotient_of_finiteType_int B p)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratioGeneration_mod_maxIdeal_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k : ℕ) (s₀ : H0 L k) (i : Fin 1 → L.ι), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (e : ℕ) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.ratio_gen_mod_of_closedFibre | exact GlobalTheory.Mum.ratio_gen_mod_of_closedFibre | (intros; apply GlobalTheory.Mum.ratio_gen_mod_of_closedFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.refine_monomial_of_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ _ Q m t δ hCN hmono htm ht0 hsymm hnn hdef
  obtain ⟨R₁, _, _, _, ρ₁, P, β, β₂, hCN₁, hinj₁, hfin₁, hloc₁, hpb, hsq, hiso⟩ := GlobalTheory.T.exists_symmetricPolarisation_finiteExtension R Q hCN
  haveI : IsNoetherianRing R₁ := hCN₁.1
  obtain ⟨D, e, f, hD⟩ := GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function R R₁ Q ρ₁ P β β₂ hinj₁ hpb hsq hiso
  obtain ⟨hfs, hfc⟩ := _root_.GlobalTheory.PolDeg.half_symm_cocycle R R₁ Q ρ₁ D e f hinj₁ hD
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.symm_cocycle_isCoboundary D.X _ f hfs hfc
  have hD₁ : Half Q ρ₁ (rescale D g) e (fun _ _ => 1) :=
    _root_.GlobalTheory.PolDeg.half_rescale R R₁ Q ρ₁ D e f (fun _ _ => 1) g hD (fun a b => by rw [hg a b, _root_.mul_one])
  have hb₁ : (rescale D g).TauBimult := _root_.GlobalTheory.PolDeg.tauBimult_of_half R R₁ Q ρ₁ (rescale D g) e hinj₁ hD₁
  obtain ⟨h, hhom, hev⟩ := _root_.GlobalTheory.DefectHom.exists_evenDefect_hom R₁ (rescale D g) hb₁
  obtain ⟨R₂, _, _, _, σ, gam, r, et, hCN₂, hinj₂, hfin₂, hloc₂, hgam, hr, hη, hη2⟩ :=
    _root_.GlobalTheory.RootHom.exists_sqrt_hom R₁ (rescale D g).X h m (fun i => ρ₁ (t i)) hCN₁ hhom
  haveI : IsNoetherianRing R₂ := hCN₂.1
  obtain ⟨D₂, β', v, xe, hpb', hv, hc', hrig, hpsi⟩ := _root_.GlobalTheory.BaseChangeDeg.exists_baseChange R₁ R₂ σ (rescale D g) gam hgam
  have hD₂ := _root_.GlobalTheory.HalfBC.half_baseChange R Q R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi ρ₁ e hinj₁ hD₁
  have hev₂ := _root_.GlobalTheory.PolDeg.evenDefect_baseChange R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi h hev
  have hinj : Function.Injective (σ.comp ρ₁) := hinj₂.comp hinj₁
  have hηx : ∀ a b : D₂.X, et (xe (a + b)) = et (xe a) * et (xe b) := fun a b => by rw [map_add (f := _), hη]
  have hD₃ : Half Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) (fun _ _ => 1) :=
    _root_.GlobalTheory.PolDeg.half_rescale R R₂ Q (σ.comp ρ₁) D₂ (xe.trans e) (fun _ _ => 1) (fun _ _ => 1) (fun χ => et (xe χ)) hD₂
      (fun a b => by rw [hηx, _root_.mul_one, mul_right_comm (et (xe a)), mul_inv_cancel, _root_.one_mul, mul_inv_cancel])
  have hev₃ : (rescale D₂ fun χ => et (xe χ)).PsiEven :=
    _root_.GlobalTheory.PolDeg.rescale_psiEven R₂ D₂ _ (fun χ => et (xe χ)) hev₂ hηx (fun a => hη2 (xe a))
  have hb₃ : (rescale D₂ fun χ => et (xe χ)).TauBimult :=
    _root_.GlobalTheory.PolDeg.tauBimult_of_half R R₂ Q (σ.comp ρ₁) _ (xe.trans e) hinj hD₃
  have hr' : ∀ i, r i ^ 2 = (σ.comp ρ₁) (t i) := fun i => hr i
  have hmon := _root_.GlobalTheory.MonoTriv.main R R₂ Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) m t r δ hCN₂ hinj hD₃
    hev₃ hb₃ hmono hnn ht0 hr'
  have hrm : ∀ i, r i ∈ maximalIdeal R₂ := by
    intro i
    refine (inferInstance : (maximalIdeal R₂).IsPrime).mem_of_pow_mem 2 ?_
    rw [hr' i, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).1 (htm i) ((isUnit_map_iff (σ.comp ρ₁) _).1 hu)
  have key : ∀ (D₃ : DegPre R₂) (e' : D₃.X ≃+ Q.X), D₃.PsiEven → D₃.TauBimult →
      Half Q (σ.comp ρ₁) D₃ e' (fun _ _ => 1) →
      IsMonomial D₃ r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i)) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
        (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
        IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧
        IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
    intro D₃ e' h1 h2 h3 h4
    obtain ⟨DD, rfl⟩ := _root_.GlobalTheory.DegFromMonomial.main R₂ D₃ m r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i))
      h1 h2 h4 hrm (fun i y z => by simp [pull, hsymm i (e' y) (e' z)])
      (fun y hy => by
        obtain ⟨i, hi⟩ := hdef (e' y) (by simpa using hy)
        exact ⟨i, by simpa [pull] using hi⟩)
    exact ⟨R₂, inferInstance, inferInstance, inferInstance, σ.comp ρ₁, r, DD, e', hCN₂, hinj,
      hfin₂.comp hfin₁, inferInstance, hr', h3.refines, h4⟩
  exact key _ _ hev₃ hb₃ hD₃ hmon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleDiagSubring

theorem relAmple_diag_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  intro R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hA₁ hP hP₁ hφ sq e hamp
  classical
  have := hA₁.proper
  have := hA₁.smooth
  let M : LB A₁.left := diagPull A₁ P₁
  have hM : M.IsLB := pull_isLB hP₁ _
  have hL : (diagPull A P).IsLB := pull_isLB hP _
  have e' : LBIso (diagPull A P) (M.pull φ) := GlobalTheory.SiegelPull.diag_iso sq e
  have hspan := GlobalTheory.CompanionTheory.PolSpread.span_good R₁.subtype A A₁ hM hL hφ.1 e' hamp
  have h1 : (1 : R) ∈ Ideal.span (R₁.subtype '' GlobalTheory.CompanionTheory.PolSpread.good A₁ M) := by rw [hspan]; trivial
  obtain ⟨c, hc, hs⟩ := Submodule.mem_span_set.1 h1
  choose! t ht hty using fun y (hy : y ∈ c.support) => hc hy
  refine ⟨c.support.image c, fun R₂ h hF A₂ _ π π₂ hπ sq₂ => ?_⟩
  let τ : R₁ →+* R₂ := Subring.inclusion h
  have hmem : ∀ y ∈ c.support, c y ∈ R₂ := fun y hy =>
    hF (Finset.mem_coe.2 (Finset.mem_image_of_mem c hy))
  have hT : Ideal.span (τ '' (t '' (c.support : Set R))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : R₂) = ∑ y ∈ c.support.attach, (⟨c y.1, hmem y.1 y.2⟩ : R₂) * τ (t y.1) := by
      apply Subtype.ext
      refine (OneMemClass.coe_one R₂).trans (hs.symm.trans ?_)
      rw [Finsupp.sum, ← Finset.sum_attach]
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : ((τ (t y.1) : R₂) : R) = y.1 := hty y.1 y.2
      rw [this]
    rw [e1]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨t y.1, ⟨y.1, y.2, rfl⟩, rfl⟩)
  have hB := GlobalTheory.CompanionTheory.PolSpread.relAmple_of_span τ A₁ hM _
    (by rintro _ ⟨y, hy, rfl⟩; exact ht y hy) hT
  have hπ' : Out.RelAmple (Over.mk A₂.hom) (M.pull π) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₁.hom (spMap τ)) hπ.1 (𝟙 _)
      (Category.id_comp _) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hB
  have : IsProper (Over.mk A₂.hom).hom := MorphismProperty.of_isPullback (P := @IsProper) hπ.1 ‹_›
  have hMπ : (M.pull π).IsLB := pull_isLB hM π
  have hL₂ : (diagPull A₂ (P₁.pull π₂)).IsLB := pull_isLB (pull_isLB hP₁ π₂) _
  have e₂ : LBIso (diagPull A₂ (P₁.pull π₂)) (M.pull π) :=
    GlobalTheory.SiegelPull.diag_iso sq₂ (GlobalTheory.lbIso_refl (pull_isLB hP₁ π₂))
  have e₃ : LBIso (M.pull π) ((M.pull π).pull (𝟙 _)) :=
    GlobalTheory.FibreAmple.lbIso_pull_comp (Category.id_comp π).symm (GlobalTheory.lbIso_refl hMπ)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (A := Over.mk A₂.hom) (A' := A₂) (f := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hMπ hL₂
    (LBIso.trans hL₂ hMπ (pull_isLB hMπ _) e₂ e₃) hπ'

end GlobalTheory.AmpleDiagSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensRos

theorem main_alg {F : Type} [Field F] (a1 a2 P1 P2 s1 s2 A Bv C Dd E' G one : F) (hA : A ≠ 0) (hB : Bv ≠ 0)
    (hE : E' ≠ 0) (hG : G ≠ 0) (hD : Dd ≠ 0)
    (h1 : a2 * (A * Bv * C) = a1 * (Dd * E' * G)) (h2 : a2 * P1 = P2) (h3 : s1 * A * Bv = P1 * Dd * one)
    (h4 : s2 * E' * G = P2 * C * one) : s2 = s1 * a1 := by
  have hK : A * Bv * E' * G * Dd ≠ 0 := by positivity
  apply mul_right_cancel₀ hK
  linear_combination (A*Bv*Dd)*h4 - (a1*E'*G*Dd)*h3 - (A*Bv*Dd*C*one)*h2 + (P1*one*Dd)*h1

theorem rosGt_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact x ρ' hρ' v' w' vs hv hw
  letI := H.starRing
  obtain ⟨ρ'', hT, hmove⟩ := _root_.GlobalTheory.Mum.TensRosMove.rosVT_move R hB D D' W T F N N' ν ν' (𝓞 E) o.onB x ρ' hρ'
  obtain ⟨-, hbij, -, -, -, hwv0, -, -⟩ := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hB D D' W T F N N' ν ν'
  rw [GtRel, gtRelV_iff] at hv hw
  intro χ
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x v'.b := by
    apply hbij.1
    funext j
    rw [hw.1 j, cmp_actV T ν ν' o ρ hact x v'.b j, ← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, NumD.projB_apply, hv.1 k]
  have h1 := hmove (N'.c χ) v'.b
  rw [c_actV ν' o] at h1
  have h2 := GlobalTheory.T.rosatiGenerator_components_torusExtension R hB D D' W T F N N' ν ν' E H ρ hρ o hact x ρ'' hT χ v'.b vs hv.1
  have h3 := hv.2 (ν'.eX.symm (star x • ν'.eX χ))
  have h4 := hw.2 χ
  rw [hb] at h4
  exact main_alg _ _ _ _ _ _ _ _ _ _ _ _ _ (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) h1 h2 h3 h4

end GlobalTheory.Mum.TensRos
end
end

