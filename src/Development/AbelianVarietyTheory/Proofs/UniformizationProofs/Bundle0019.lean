module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecRelationDefect
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_smul_sub_smul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (c' c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval d r z J = gs r z ⊤ c' * sval s r z J - gs r z ⊤ c * sval t r z J := by
  have gsub : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (_ : r z ∈ U) (a b : Γ(Y, U)),
      gs r z U (a - b) = gs r z U a - gs r z U b := fun Z r z U h a b => by
    simp only [gs_eq r z U h, map_sub]
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j)
        ((Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j)) =
      gs r z ⊤ c' * gs r z (LB.wchart L φ j) (s.f j) - gs r z ⊤ c * gs r z (LB.wchart L φ j) (t.f j) :=
    fun Z r z j hj => (gsub Z r z _ hj _ _).trans (congrArg₂ (· - ·)
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _)))
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _))))
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j),
      fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [sec_trans s (𝟙 Y) y hy.1 hy.2, sec_trans t (𝟙 Y) y hy.1 hy.2]
  simp only [trF]
  ring

theorem exists_sec_relation_defect : ∀ (Y : Scheme.{0}) (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y ⟶ X)) (εu : K'' → ℤ) (τ : Y ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → ∃ d : LB.Sec (LB.LinComb L φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval d r z J = gs r z ⊤ c' * sval s' r z J - gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val) := by
  intro Y X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF
  obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => (hF U h).symm : FormEq _ _ φ' ε') (pullMulSec s τ u hu)
  obtain ⟨d, hd⟩ := exists_sec_smul_sub_smul s' t c' c
  exact ⟨d, fun Z r z J hJ => by rw [hd Z r z J hJ, ht Z r z J hJ, sval_pullMulSec s τ u hu r z hJ]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocalizationOfIsStandardSmooth
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.StabFlat

theorem flat_of_regular {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] {ϖ : V}
    (hϖ : Irreducible ϖ) (σ : V →+* C) (h : IsSMulRegular C (σ ϖ)) : σ.Flat := by
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, mul_assoc, map_pow] at h1
  exact (h.pow n).right_eq_zero_of_smul (((u.isUnit.map σ).mul_right_eq_zero).1 h1)

theorem flat_of_ideals : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → ∃ I : Ideal (X.presheaf.stalk (j h)), IsSMulRegular (X.presheaf.stalk (j h) ⧸ I) (σ ϖ) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ _ ϖ hϖ X H f j hj hI
  refine Flat.of_stalkMap _ fun h => ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have reg : IsSMulRegular (H.presheaf.stalk h) ((j.stalkMap h).hom (σ.hom ϖ)) := by
    by_cases hu : IsUnit (σ.hom ϖ)
    · exact (hu.map _).isRegular.left.isSMulRegular
    obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hu
    have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
      (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
        ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
    have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
    have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have e : y (IsLocalRing.closedPoint _) = h := by
      apply j.isClosedEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
      exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
    have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
    refine IsSMulRegular.of_right_eq_zero_of_smul fun b hb => ?_
    obtain ⟨a, rfl⟩ := j.stalkMap_surjective h b
    refine h₁ (Ideal.Quotient.eq_zero_iff_mem.1 (hr.right_eq_zero_of_smul ?_))
    have := congrArg ψ.hom hb
    rw [smul_eq_mul, map_mul, hψ', hψ', map_zero] at this
    exact this
  have fl : (σ ≫ j.stalkMap h).hom.Flat := flat_of_regular hϖ _ reg
  have e : σ ≫ j.stalkMap h = StructureSheaf.toStalk V ((j ≫ f) h) ≫ (j ≫ f).stalkMap h := by
    apply Spec.map_injective
    refine Eq.trans ?_ (Spec.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Spec.fromSpecStalk_eq' (CommRingCat.of V) ((j ≫ f) h)))
    rw [Spec.map_comp, hσ, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (j ≫ f)).symm
  let S := (Spec (CommRingCat.of V)).presheaf.stalk ((j ≫ f) h)
  letI : Algebra V S := StructureSheaf.stalkAlgebra V ((j ≫ f) h)
  have : ((j ≫ f) h).asIdeal.IsPrime := PrimeSpectrum.isPrime (R := V) _
  have : IsLocalization.AtPrime S ((j ≫ f) h).asIdeal := StructureSheaf.IsLocalization.to_stalk V _
  letI : Algebra V (H.presheaf.stalk h) := (σ ≫ j.stalkMap h).hom.toAlgebra
  letI : Algebra S (H.presheaf.stalk h) := ((j ≫ f).stalkMap h).hom.toAlgebra
  have : IsScalarTower V S (H.presheaf.stalk h) := IsScalarTower.of_algebraMap_eq' (congrArg (·.hom) e)
  exact (Module.flat_iff_of_isLocalization S ((j ≫ f) h).asIdeal.primeCompl (H.presheaf.stalk h)).2 fl

theorem height_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] (g : ℕ)
    [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] (m : Ideal B) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = g := by
  have : Nontrivial B := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hm.ne_top (Subsingleton.elim _ _)
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime.trans
    (SmoothDim.ringKrullDim_of_etale_mvPolynomial K B g).le) ?_
  letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
    (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
    (S := MvPolynomial (Fin g) K) inferInstance inferInstance
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI hp := SmoothDim.isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
    (m.under (MvPolynomial (Fin g) K))
  letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
  rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
  rw [← h1, WithBot.coe_le_coe, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (m.under (MvPolynomial (Fin g) K)) m]
  exact le_self_add

theorem localization_of_isStandardSmooth {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R] [CommRing A]
    {ϖ : V} (h₀ : ϖ ∈ nonZeroDivisors V) [(Ideal.span {ϖ}).IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : ρ ϖ ∈ n) :
    IsNoetherianRing A ∧ algebraMap R A (ρ ϖ) ∈ nonZeroDivisors A ∧
      IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) ∧
      ringKrullDim (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) = g := by
  have hq : (Ideal.quotientMap ((Ideal.span {ϖ}).map ρ) ρ Ideal.le_comap_map).IsStandardSmoothOfRelativeDimension g := by
    have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange.{0} g)
    exact MorphismProperty.of_isPushout
      (P := RingHom.toMorphismProperty (@RingHom.IsStandardSmoothOfRelativeDimension g))
      (NilpotentLift.isPushout_quotient_map (Ideal.span {ϖ}) (CommRingCat.ofHom ρ)).flip hρ
  letI := ρ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g V R := hρ
  have : Algebra.IsStandardSmooth V R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing V R
  refine ⟨IsLocalization.isNoetherianRing n.primeCompl A inferInstance, ?_, ?_⟩
  · have h₁ : IsSMulRegular R ϖ := Module.Flat.isSMulRegular_of_nonZeroDivisors h₀
    refine IsLocalization.map_nonZeroDivisors_le n.primeCompl A ⟨ρ ϖ, ?_, rfl⟩
    exact mem_nonZeroDivisors_iff_left.2 fun x hx => h₁.right_eq_zero_of_smul hx
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  set J := (Ideal.span {ϖ}).map ρ with hJ
  obtain ⟨φ, -, hφ⟩ := hq.exists_etale_mvPolynomial
  have hJ' : J = Ideal.span {ρ ϖ} := by rw [hJ, Ideal.map_span, Set.image_singleton]
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker, hJ', Ideal.span_singleton_le_iff_mem]
  letI := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) (R ⧸ J) := hφ.toAlgebra
  have : IsRegularRing (R ⧸ J) := isRegularRing_of_etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) _
  have hm : (n.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (Ideal.span {algebraMap R A (ρ ϖ)}).comap (algebraMap R A) := by
    rw [hJ', Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self _
  letI : Algebra (R ⧸ J) (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ Ideal.span {algebraMap R A (ρ ϖ)})
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ', Ideal.map_span, Set.image_singleton])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  refine ⟨?_, (IsLocalization.AtPrime.ringKrullDim_eq_height (n.map (Ideal.Quotient.mk J)) _).trans
    (height_of_etale_mvPolynomial (V ⧸ Ideal.span {ϖ}) (R ⧸ J) g _)⟩
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem stalk_of_smooth : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → IsNoetherianRing (X.presheaf.stalk x) ∧ σ ϖ ∈ nonZeroDivisors (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) ∧ ringKrullDim (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) = g := by
  intro V _ _ _ ϖ hϖ X f g hg x hx σ hσ hn
  obtain ⟨U, hU, W, hW, hxW, e, H⟩ := hg.exists_isStandardSmoothOfRelativeDimension x
  have hfx : f x = IsLocalRing.closedPoint V := by
    refine ((congrArg f Scheme.fromSpecStalk_closedPoint.symm).trans
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ)).trans ?_
    refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
      (PrimeSpectrum.isPrime _).ne_top ?_))
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hn
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 (hfx ▸ e hxW)
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ f.appLE ⊤ W e
  have hρ : ρ.hom.IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).2 H
  have hc : ρ ≫ X.presheaf.germ W x hxW = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [← hσ, ← hW.fromSpecStalk_eq_fromSpecStalk hxW, Spec.map_comp, Spec.map_comp, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hW e, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hl : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  have hs : algebraMap Γ(X, W) (X.presheaf.stalk x) (ρ.hom ϖ) = σ ϖ := congrArg (fun q => q.hom ϖ) hc
  haveI : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal V
  rw [← hs]
  refine localization_of_isStandardSmooth (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hρ
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal ?_
  by_contra hm
  exact hn (hs ▸ IsLocalization.map_units (X.presheaf.stalk x)
    (⟨_, hm⟩ : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl))

end GlobalTheory.StabFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemPowOfFlatQuotient
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatThickenings

theorem mem_pow_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [CommRing C] (σ : V →+* C)
    {ϖ : V} (hϖ : ϖ ≠ 0) (I : Ideal V) (hI : I = Ideal.span {ϖ}) (e : ℕ)
    (h : (Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1)))).Flat)
    {a : C} (ha : σ ϖ * a = 0) : a ∈ Ideal.span {σ ϖ} ^ e := by
  set φ := Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1))) with hφ
  let _ := φ.toAlgebra
  have : Module.Flat (V ⧸ I ^ (e + 1)) (C ⧸ (I ^ (e + 1)).map σ) := h
  have hsm : ∀ (v : V) (c : C), (Ideal.Quotient.mk (I ^ (e + 1)) v) •
      (Ideal.Quotient.mk ((I ^ (e + 1)).map σ) c) = Ideal.Quotient.mk _ (σ v * c) := by
    intro v c
    rw [Algebra.smul_def, map_mul]
    rfl
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := V ⧸ I ^ (e + 1)) (M := C ⧸ (I ^ (e + 1)).map σ)
    (f := fun _ : Unit => Ideal.Quotient.mk _ ϖ) (x := fun _ => Ideal.Quotient.mk _ a)
    (by rw [Fintype.sum_unique, hsm, ha, map_zero])
  choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c () j)
  choose y' hy' using fun j => Ideal.Quotient.mk_surjective (y j)
  have hd : ∀ j, ϖ ^ e ∣ c' j := by
    intro j
    have h1 := hc j
    rw [Fintype.sum_unique, ← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ'] at h1
    exact (mul_dvd_mul_iff_left hϖ).1 h1
  have h2 : a - ∑ j, σ (c' j) * y' j ∈ (I ^ (e + 1)).map σ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq, map_sum]
    refine (hy ()).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc', ← hy', hsm]
  rw [hI, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
  have h3 : ∑ j, σ (c' j) * y' j ∈ Ideal.span {σ ϖ} ^ e := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    exact map_dvd σ (hd j)
  simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) h2) h3

theorem flat_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsNoetherianRing C] (σ : V →+* C)
    (h : ∀ e : ℕ, (Ideal.quotientMap ((IsLocalRing.maximalIdeal V ^ (e + 1)).map σ) σ
      (Ideal.le_comap_map (I := IsLocalRing.maximalIdeal V ^ (e + 1)))).Flat) : σ.Flat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ a : C, σ ϖ * a = 0 → a = 0 := by
    intro a ha
    have hm : a ∈ ⨅ i : ℕ, (Ideal.span {σ ϖ} ^ i • ⊤ : Submodule C C) := by
      rw [Submodule.mem_iInf]
      intro e
      rw [smul_eq_mul, Ideal.mul_top]
      exact mem_pow_of_flat_quotient σ hϖ.ne_zero _ hϖ.maximalIdeal_eq e (h e) ha
    obtain ⟨⟨r, hr⟩, hra⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ a).1 hm
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [← hra]
    change c * σ ϖ * a = 0
    rw [_root_.mul_assoc, ha, mul_zero]
  have keyn : ∀ (n : ℕ) (a : C), σ ϖ ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact key a (ih _ (by rw [← ha]; ring))
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, _root_.mul_assoc, map_pow] at h1
  exact keyn n a (((u.isUnit.map σ).mul_right_eq_zero).1 h1)

theorem flat_chart {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {B : Scheme.{0}} (f : B ⟶ Spec (CommRingCat.of V)) [LocallyOfFiniteType f]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (b : ∀ e, (Y e).left ⟶ B)
    (hb : ∀ e, IsPullback (b e) (Y e).hom f (thick V (IsLocalRing.maximalIdeal V) e))
    (hY : ∀ e, Flat (Y e).hom) {C : CommRingCat.{0}} (u : Spec C ⟶ B) [IsOpenImmersion u] :
    Flat (u ≫ f) := by
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (u ≫ f)
  have hft : LocallyOfFiniteType (Spec.map σ) := by rw [hσ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{0})] at hft
  have hN : IsNoetherianRing C := by
    let _ : Algebra V C := σ.hom.toAlgebra
    have : Algebra.FiniteType V C := hft
    exact Algebra.FiniteType.isNoetherianRing V C
  rw [← hσ, HasRingHomProperty.Spec_iff (P := @Flat.{0})]
  refine flat_of_flat_quotient σ.hom fun e => ?_
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (NilpotentLift.isPushout_quotient_map (IsLocalRing.maximalIdeal V ^ (e + 1)) σ)
  have H' := (IsPullback.of_hasPullback (b e) u).flip.paste_vert (hb e)
  rw [← hσ] at H'
  have := hY e
  have hf : Flat ((H.isoIsPullback _ _ H').hom ≫ pullback.fst (b e) u ≫ (Y e).hom) := inferInstance
  rw [IsPullback.isoIsPullback_hom_snd, HasRingHomProperty.Spec_iff (P := @Flat.{0})] at hf
  exact hf

theorem flat_of_flat_thickenings :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [LocallyOfFiniteType B.hom] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → Flat B.hom := by
  intro V _ _ _ B _ Y b hb hY
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{0})
  exact IsZariskiLocalAtSource.of_openCover (P := @Flat) B.left.affineOpenCover.openCover
    fun i =>
      have : IsOpenImmersion (B.left.affineOpenCover.f i) := B.left.affineOpenCover.map_prop i
      flat_chart B.hom Y b hb hY (B.left.affineOpenCover.f i)

end GlobalTheory.FlatThickenings
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ThickeningDetermines in
theorem sec_eq_zero_of_thickenings_of_section (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [Smooth H.hom] [GeometricallyConnected H.hom] (e : 𝟙_ _ ⟶ H) (N : LB H.left) (hN : N.IsLB)
    (s : LB.Sec N) (hs : ∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) (j) :
    s.f j = 0 := by
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H e (fun p ↦ inferInstance)
  refine eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have := key _ (secIdeal hN s).subschemeι fun n ↦ by
    have : IsClosedImmersion (thick R I n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : QuasiCompact (fstG I n H).left :=
      inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
    exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this

theorem app_sec_eq_zero_of_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j) : (r.app _).hom (d.f j) = 0 := by
  apply TopCat.Presheaf.section_ext Z.sheaf _
  intro z hz
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := sec_trans d r z (j := j) hz (Good.mem hI φ r)
  have e' : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    e.trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  exact ((gs_eq r z _ hz _).symm.trans e').trans (map_zero _).symm

theorem sec_eq_zero_of_sval_finite_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ j, d.f j = 0 := by
  intro R _ I T B _ _ _ _ _ hI X L hL K _ φ ε d hd j
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop
  have hψ : T.left.isoSpec.hom ≫ Spec.map ψ = T.hom := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let H : Over (Spec (CommRingCat.of Γ(T.left, ⊤))) :=
    Over.mk (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom)
  have : Smooth H.hom := inferInstanceAs (Smooth (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom))
  have : GeometricallyConnected H.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_iso (IsPullback.of_hasPullback T.hom B.hom).flip (Iso.refl _) (Iso.refl _)
        T.left.isoSpec (Iso.refl _) (fst' := pullback.snd T.hom B.hom) (snd' := H.hom)
        (f' := B.hom) (g' := Spec.map ψ) (by simp) (Category.id_comp _).symm (by simp)
        (by simp [hψ])) ‹GeometricallyConnected B.hom›
  let σ : T ⟶ T ⊗ B := lift (𝟙 T) (toUnit T ≫ η[B])
  have hσ : σ.left ≫ pullback.fst T.hom B.hom = 𝟙 _ :=
    congrArg CommaMorphism.left (lift_fst (𝟙 T) (toUnit T ≫ η[B]))
  let e : 𝟙_ _ ⟶ H := Over.homMk (T.left.isoSpec.inv ≫ σ.left) (by
    change (T.left.isoSpec.inv ≫ σ.left) ≫ pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom = 𝟙 _
    rw [Category.assoc, reassoc_of% hσ, Iso.inv_hom_id])
  refine sec_eq_zero_of_thickenings_of_section Γ(T.left, ⊤) (I.map ψ.hom)
    (Ideal.map_le_iff_le_comap.2 hI) H e (LB.LinComb L φ ε) (DVR.linComb_isLB L hL φ ε) d
    (fun n j ↦ app_sec_eq_zero_of_sval hL d _ (hd n _ _ ⟨pullback.snd H.hom (thick _ (I.map ψ.hom) n) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map ψ.hom) ^ (n + 1)) ψ.hom
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))), ?_⟩) j) j
  change _ = pullback.fst H.hom (thick _ (I.map ψ.hom) n) ≫ pullback.fst T.hom B.hom ≫ T.hom
  have h1 : pullback.fst T.hom B.hom ≫ T.hom = H.hom ≫ Spec.map ψ :=
    (congrArg (pullback.fst T.hom B.hom ≫ ·) hψ.symm).trans (Category.assoc _ _ _).symm
  rw [h1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_comp_stalkMap {Y Z Z' : Scheme.{0}} (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (U : Y.Opens)
    (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h a, gs_eq r (ρ z) U h, gs_eq ρ z (r ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ U) z h _).symm

theorem values_natural : ∀ (X Y Z Z' : Scheme.{0}) (L : LB X) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) ∧ (∀ s : LB.Sec (LB.LinComb L φ ε), sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ)))) ∧ (∀ t : LB.Gen (LB.LinComb L φ ε), (val t (ρ ≫ r) z J).val = (ρ.stalkMap z).hom (val t r (ρ z) (fun ψ => J (ρ ≫ ψ))).val) ∧ ∀ c : Γ(Y, ⊤), gs (ρ ≫ r) z ⊤ c = (ρ.stalkMap z).hom (gs r (ρ z) ⊤ c) := by
  intro X Y Z Z' L K _ φ ε r ρ z J hJ
  have hJ' : Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) := fun ψ => hJ (ρ ≫ ψ)
  have hm := hJ'.mem φ r
  refine ⟨hJ', fun s => ?_, fun t => ?_, fun c => gs_comp_stalkMap r ρ z ⊤ trivial c⟩
  · rw [sval_of s (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact gs_comp_stalkMap r ρ z _ hm _
  · rw [val_of t (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact (gs_unit (ρ ≫ r) z _ hm _).symm.trans ((gs_comp_stalkMap r ρ z _ hm _).trans
      (congrArg (ρ.stalkMap z).hom (gs_unit r (ρ z) _ hm _)))

end GlobalTheory
end

