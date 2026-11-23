module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.smooth_iSup_comp (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  set U := ⨆ i, V i with hUdef
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{0}) (fun i => U.ι ⁻¹ᵁ V i) ?_ ?_
  · apply top_unique
    intro x _
    have hx : (U.ι x : P') ∈ (⨆ i, V i : P'.Opens) := x.2
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have hrange : Set.range ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) = Set.range (V i).ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Scheme.Hom.mem_preimage]
      exact ⟨by rintro ⟨x, hx, rfl⟩; exact hx, fun hy => ⟨⟨y, hle i hy⟩, hy, rfl⟩⟩
    rw [← Category.assoc, ← IsOpenImmersion.isoOfRangeEq_hom_fac ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) (V i).ι hrange,
      Category.assoc]
    haveI := h i
    infer_instance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusAction

theorem smoothOfRelativeDimension_of_holUnif (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    {g : ℕ} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ A hA
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  obtain ⟨u₀⟩ := RealMultChart.exists_holUnif_of_compact A d hd (RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => RealMultChart.exists_pow_eq A hA a n hn)
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u₀ hd
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ d g u₀ h₁ h₂
    u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  rw [Obj.holUnif_dim_eq_of_linear u u₀ T hT]
  exact hd


end GlobalTheory.TorusAction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapClosedPointOfFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dense_of_closedFibre_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G],
    IsSemiAbelian G → ∀ O : G.left.Opens, (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → Dense (O : Set G.left) := by
  intro R _ _ _ G _ hG O hO
  haveI := hG.smooth
  haveI := hG.geomConnected
  let g₀ : G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left (closedPoint R)
  have hg₀ : G.hom g₀ = closedPoint R := by
    have := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
    change ((1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
    rw [this]; rfl
  have : IrreducibleSpace G.left := _root_.GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R G inferInstance inferInstance ⟨g₀⟩
  exact O.isOpen.dense ⟨g₀, hO g₀ hg₀⟩

theorem spMap_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) : spMap ρ (closedPoint R') = closedPoint R := by
  algebraize [ρ]
  have : Algebra.IsIntegral R R' := ⟨fun x => hf.to_isIntegral x⟩
  apply PrimeSpectrum.ext
  show Ideal.comap ρ (maximalIdeal R') = maximalIdeal R
  have : (Ideal.comap (algebraMap R R') (maximalIdeal R')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R')
  exact IsLocalRing.eq_maximalIdeal this

theorem comp_eq_of_near {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) (G' : Over (Sp R')) [GrpObj G'] (hG' : IsSemiAbelian G') (N : Near (spMap ρ) G')
    (G : Over (Sp R)) [GrpObj G] (hG : IsSeparated G.hom) (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ)
    (i : N.U ⟶ G) (hu : N.u ≫ β = pullback.fst _ _ ≫ i.left) (σ : Gal ρ) (g : G'.left ⟶ G'.left)
    (hg : g ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ))
    (hinv : ∀ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x →
      N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ g)) : g ≫ β = β := by
  haveI := hG'.smooth
  haveI := N.isOpen
  have hred : IsReduced G'.left := GlobalTheory.isReduced_of_smooth_of_isReduced G'.hom
  have hd := dense_of_closedFibre_sub R' G' hG' N.u.opensRange (fun x hx => by
    obtain ⟨y, hy⟩ := N.all x (by rw [hx]; exact spMap_closedPoint_of_finite ρ hf)
    exact ⟨y, hy⟩)
  haveI : IsDominant N.u := ⟨by simpa [DenseRange] using hd⟩
  have hσ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.2 r
  refine ext_of_isDominant_of_isSeparated G.hom ?_ N.u ?_
  · rw [Category.assoc, hβ, ← Category.assoc, hg, Category.assoc, hσ]
  · obtain ⟨x₁, h1, -, h3⟩ := hinv _ (pullback.snd _ _) (pullback.fst _ _) N.u ⟨𝟙 _, by simp, by simp, by simp⟩
    rw [← Category.assoc, ← h3, Category.assoc, hu, ← Category.assoc, h1]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem spMap_factor_residueField_of_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω]
    (g : Sp Ω ⟶ Sp R) (hg : ∀ w, g w = closedPoint R) :
    ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage g).hom with hφ
  have hgφ : g = spMap φ := by
    simp only [spMap, hφ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hker : ∀ x ∈ maximalIdeal R, φ x = 0 := by
    intro x hx
    let w : Sp Ω := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := hg w
    rw [hgφ] at h1
    have h2 : (spMap φ w).asIdeal = Ideal.comap φ ⊥ := rfl
    rw [h1, closedPoint] at h2
    have : x ∈ Ideal.comap φ ⊥ := h2 ▸ hx
    simpa using this
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ hker, ?_⟩
  rw [hgφ]
  congr 2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def TwoTorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x : Over.mk (spMap (algebraMap (FractionRing R) F) ≫ jK R) ⟶ G),
    x * x = 1 → ∃ y : Over.mk (jK R) ⟶ G, x.left = spMap (algebraMap (FractionRing R) F) ≫ y.left

def SplitClosed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitPow

theorem splitExtensionModuloIdeal_eighth_power : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R),
    GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  intro R _ G₀ _ _ I ⟨E, ⟨D⟩⟩
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  obtain ⟨p, -⟩ := GlobalTheory.isPowGrp_baseChange _ _ (spMap (Ideal.Quotient.mk I)) (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8)
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Sp (R ⧸ I)) E.X (Fin 8 → E.X) 8 (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ _ _ (powObj E.B 8) E.B 8 p (powIsPowGrp E.B 8) D.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ _ _ 8 pT p D.i
  have hB : IsAbelianScheme (powObj E.B 8) := (GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp E.B 8)).2.2.2.1 E.isAbelian
  have hk := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ 8 pT p (powIsPowGrp E.B 8) D.i D.q i' q' hi hq D.isKernel
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G₀) := inferInstance
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj (powObj G₀ 8)) := inferInstance
  have hqc : QuasiCompact D.q.left := by
    have := D.q_affine
    infer_instance
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ (Fin 8 → E.X) _ (powObj E.B 8) hB q' i'
    (hq1 D.q_hom) (hi1 D.i_hom) (hq2 D.q_flat) (hq3 D.q_surjective) (hq4 hqc) hk
  obtain ⟨d, -, -⟩ := h hB
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory.SplitPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HtGen

attribute [local instance] Over.cartesianMonoidalCategory

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev TorsK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Subgroup (Over.mk ξ ⟶ t.G) := (powMonoidHom q).ker



variable {t} in
def InducedBy {K : Type} [Field K] {ξ : Sp K ⟶ X} {q : ℕ} (χ : TorsK t ξ q →* Kˣ) {R : Type} [CommRing R]
    (x : Sp R ⟶ X) (u : R →+* K) {O : Type} [CommRing O] (ψ : R →+* O) {z : Sp O ⟶ X} (c : TorsChar t z q) : Prop :=
  ∀ (σ : Over.mk x ⟶ t.G) (k : TorsK t ξ q) (a : R) (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G),
    σ ^ q = 1 → k.1.left = spMap u ≫ σ.left → w.left = spMap ψ ≫ σ.left → u a = χ k → (c.χ O w : O) = ψ a

end Chars

end GlobalTheory.HtGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomEqOfNilpotent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem splitTorus_hom_eq_of_nilpotent : ∀ (A κ : Type) [CommRing A] [IsLocalRing A] [CommRing κ]
    (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (X : Type)
    [AddCommGroup X] (H : Over (Sp A)) [GrpObj H] [IsCommMonObj H]
    (i₁ i₂ : splitTorus (Sp A) X ⟶ H), IsMonHom i₁ → IsMonHom i₂ →
    GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₁.left = GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₂.left →
    i₁ = i₂ := by
  intro A κ _ _ _ π hπ hJ X _ H _ _ i₁ i₂ h₁ h₂ h
  set J := RingHom.ker π
  haveI : IsMonHom i₂⁻¹ := inferInstance
  haveI hf : IsMonHom (i₁ * i₂⁻¹) := GlobalTheory.Serre.isMonHom_mul _ _
  set r : Sp (A ⧸ J) ⟶ Sp A := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let e : A ⧸ J ≃+* κ := RingHom.quotientKerEquivOfSurjective hπ
  have hr : r = spMap e.symm.toRingHom ≫ spMap π := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, Ideal.Quotient.mk_eq_mk]
    rw [RingEquiv.eq_symm_apply]
    rfl

  obtain ⟨l, hl⟩ : ∃ l, l ≫ SplitTorus.bcMap (spMap π) X = pullback.fst (splitTorus (Sp A) X).hom r :=
    ⟨_, (SplitTorus.isPullback_bcMap (spMap π) X).lift_fst (pullback.fst (splitTorus (Sp A) X).hom r)
      (pullback.snd (splitTorus (Sp A) X).hom r ≫ spMap e.symm.toRingHom)
      (by rw [pullback.condition, Category.assoc, ← hr])⟩
  let t : Over.mk (pullback.fst (splitTorus (Sp A) X).hom r ≫ (splitTorus (Sp A) X).hom) ⟶ splitTorus (Sp A) X := Over.homMk (pullback.fst (splitTorus (Sp A) X).hom r)
  have ht : t ≫ i₁ = t ≫ i₂ := by
    ext
    simp only [t, Over.comp_left, Over.homMk_left]
    simp only [← hl, Category.assoc, h]
  have ht1 : t ≫ (i₁ * i₂⁻¹) = t ≫ (toUnit _ ≫ η[H]) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ht, mul_inv_cancel, ← Category.assoc,
      Hom.one_def]
    congr 1
  have key := splitTorus_hom_eq_one_of_nilpotent A J hJ X H (i₁ * i₂⁻¹) hf (by
    ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, pullback.lift_fst]
        exact congrArg CommaMorphism.left ht1
      · simp only [Over.pullback_map_left, pullback.lift_snd])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPowStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R))), IsSeparated B.hom → ∀ (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B), (∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) → f = g := by
  first | exact @GlobalTheory.splitTorus_hom_ext_of_forall_pow | exact GlobalTheory.splitTorus_hom_ext_of_forall_pow | (intros; apply GlobalTheory.splitTorus_hom_ext_of_forall_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPowStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G), IsMonHom f → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1 → ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  first | exact @GlobalTheory.splitTorus_hom_trivial_mod_pow | exact GlobalTheory.splitTorus_hom_trivial_mod_pow | (intros; apply GlobalTheory.splitTorus_hom_trivial_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem surjective_of_range_sup_smul_top_eq_top (R : Type) [CommRing R] (M : Type 1)
    [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N)
    (h : ∀ I : Ideal R, I.IsMaximal → LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective f := by
  set S := LinearMap.range f

  have key : ∀ I : Ideal R, I.IsMaximal → ¬ Module.annihilator R (N ⧸ S) ≤ I := by
    intro I hI hle
    have hle' : (⊤ : Submodule R (N ⧸ S)) ≤ I • (⊤ : Submodule R (N ⧸ S)) := by
      have h1 := congrArg (Submodule.map S.mkQ) (h I hI)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
      have h2 : Submodule.map S.mkQ S = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        simpa [Submodule.mem_bot] using (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [h2, bot_sup_eq] at h1
      rw [h1]
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.Finite.fg_top) hle'
    have hrA : r ∈ Module.annihilator R (N ⧸ S) :=
      Module.mem_annihilator.mpr fun m => hr m trivial
    have hrI : r ∈ I := hle hrA
    have h1I : (1 : R) ∈ I := by
      have := I.sub_mem hrI hr1
      simpa using this
    exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr h1I)
  have htop : Module.annihilator R (N ⧸ S) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    exact key I hI hle
  have hS : S = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ S) := htop ▸ Submodule.mem_top
    have h2 := Module.mem_annihilator.mp h1 (S.mkQ n)
    rw [one_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  exact LinearMap.range_eq_top.mp hS

end GlobalTheory
end

