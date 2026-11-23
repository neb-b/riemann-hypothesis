module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfPowEqInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
section
noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Dominates

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
  (hb : β'.comp b = β)

end Dominates

section Dense

variable (Y : Model Xo c β)

theorem densePart (h : IsDedFrac β) : IsLocallyNoetherian Y.X ∧ IsReduced Y.X ∧ Y.X.IsSeparated ∧
    IsPreimmersion Y.j ∧ Flat Y.j ∧ IsDominant Y.j ∧ QuasiCompact Y.j := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := h
  letI := β.toAlgebra
  obtain ⟨h₁, -, h₂, h₃⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x ↦
    have := (Y.normal x).1
    inferInstance
  exact ⟨h₁, isReduced_of_isReduced_stalk Y.X, h₂, h₃⟩

end Dense

section Transition

variable {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O₂ : Type} [CommRing O₂] {β₂ : O₂ →+* c₂.F}
  (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (hl : l.Dvd l₂) (hF : c.F ≤ c₂.F) (b : O →+* O₂)
  (hb : β₂.comp b = (IntermediateField.inclusion hF).toRingHom.comp β) (π : Y₂.X ⟶ Y.X)

end Transition

section Algebra

end Algebra

section Action

variable (Y : Model Xo c β)

variable {Y}

variable (Y)

end Action

end GlobalTheory.ModelRelCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.KernelNoTorsion IsLocalRing
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Gt : Over (Sp R)} [GrpObj Gt]
  {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ =>
    (val_corr hJ (h.2 χ) (𝟙 _)).trans (val_corr hJ (h'.2 χ) (𝟙 _)).symm

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e' : th D y J (cP D T χ) g.b g.b = 1 := by
    rw [hb1, C.face₃]
  have e := hv χ y J hJ
  rw [e', _root_.mul_one] at e
  have e₂ : cv g χ y J = 1 := mul_eq_left.1 e.symm
  exact e₂.trans (val_one _).symm

theorem isZero_one (hΦ : Represents Φ) (T : Over (Sp R)) : (Φ T 1).IsZero := by
  have h := hΦ.2 T 1 1
  rw [_root_.mul_one] at h
  exact isZero_of_isAdd h

theorem tors_iff (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) :
    FlatIsoUnitGenerator.GtTors k (Φ T x) ↔ x ^ k = 1 := by
  constructor
  · rintro ⟨_, ⟨u, u0, us, rfl⟩, hz⟩
    have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
      induction i using Fin.induction with
      | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
      | succ i ih =>
        have h := us i
        rw [ih] at h
        rw [Fin.val_succ, pow_succ]
        exact isAdd_unique h (hΦ.2 T _ _)
    exact (Φ T).injective ((this (Fin.last k)).symm.trans (isZero_unique hz (isZero_one hΦ T)))
  · intro hx
    refine ⟨Φ T (x ^ k), ⟨fun i => Φ T (x ^ (i : ℕ)), by simpa using isZero_one hΦ T, fun i => ?_, rfl⟩,
      hx ▸ isZero_one hΦ T⟩
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    exact hΦ.2 T _ _

theorem isPull_iff_comp (hΦ : Represents Φ) {T T' : Over (Sp R)} (h : T' ⟶ T) (x : T ⟶ Gt) (x' : T' ⟶ Gt) :
    GtPt.IsPull h.left (Φ T x) (Φ T' x') ↔ h ≫ x = x' :=
  ⟨fun H => (Φ T').injective (isPull_unique (hΦ.1 _ _ h x) H), fun H => H ▸ hΦ.1 _ _ h x⟩

theorem exists_represents [IsNoetherianRing R] (D : DegPre R) :
    ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), Represents Φ ∧
      ∀ k : ℕ, 1 ≤ k → IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ, fun k hk => ?_⟩
  obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.P k hk
  have h₁' : IsFinite (𝟙 D.P.A ^ k).left := h₁
  have h₂' : Flat (𝟙 D.P.A ^ k).left := h₂
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
  have P := MulEtaleDvr.isPullback_torsion D.P.A k
  exact isFinite_flat_torsion_of_isGt _ (splitExt D) H hH k hk (MorphismProperty.of_isPullback (P := @IsFinite) P h₁')
    (MorphismProperty.of_isPullback (P := @Flat) P h₂')

end Points

theorem isAdicColimit_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] (hc : IsAdicComplete (maximalIdeal R) R)
    (N : Over (Sp R)) [IsFinite N.hom] [Flat N.hom] : IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hl : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hl
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : Module.Flat R Γ(N.left, ⊤) := hl
  have H := isAdicColimit_of_finite_flat (maximalIdeal R) (RingHom.id R) (by rwa [Ideal.map_id])
    (fun a ha => ⟨1, by rwa [Ideal.map_id, pow_one]⟩) Γ(N.left, ⊤)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem formalEq_iff {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : GtPt D.toPre T) :
    FlatIsoUnitGenerator.FormalEq U x g ↔ IsPointOf U g x := by
  rw [isPointOf_iff_thick]
  refine forall_congr' fun e => and_congr eq_comm (forall_congr' fun χ => ⟨fun h => ?_, fun h => ?_⟩) <;>
  exact corr_of_val D.toPre.P.isLB fun _ _ hJ => (val_corr hJ h (𝟙 _)).symm

end GlobalTheory.TorsionFormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcInputCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Classes

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

variable (hB : D.TauBimult) (oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F]

variable {F} {k : ℕ}

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem isRatio_ext {p p' : QkPt D F k} {z : F} (h : QkPairing.IsRatio p p' z) :
    QkPairing.IsRatio (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  intro T σ y J hJ
  have e := h T (σ ≫ extMap f hf) y J hJ
  have v : ∀ (g : GtPtF D F) χ, val ((gtExt D f hf g).s χ) σ.left y J = val (g.s χ) (σ ≫ extMap f hf).left y J :=
    fun g χ => (val_corr hJ (((eq_gtExt_iff f hf g _).1 rfl).2 χ) _).trans (val_pull hJ _ _ _)
  have w : gs σ.left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (f z)) =
      gs (σ ≫ extMap f hf).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
    refine Eq.trans (congrArg (gs σ.left y ⊤) ?_) (gs_pull σ.left (spMap f) y ⊤ trivial _)
    exact congrArg (fun g => g.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  dsimp only [qkExt, qkMk]
  rw [v, v, w, gtExt_b, gtExt_b, ← Category.assoc, ← Category.assoc]
  exact e

theorem weil_ext (k : ℕ) (hk : 1 ≤ k) (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  obtain ⟨u, hu⟩ := QkPairing.exists_ratio p p'
  obtain rfl := QkPairing.weil_unique globalFns_holds abelianSchemeLaws_all.2.secTwist hB hk p p' h
    (QkPairing.weil_of_ratio globalFns_holds p p' hu)
  exact QkPairing.weil_of_ratio globalFns_holds _ _ (ζ := Units.map f.toMonoidHom u) (isRatio_ext hB f hf hu)

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]


variable (hB : P.TauBimult)


end Data

section Lev

variable (D : Datum H) (l : Level H)

end Lev

section Level

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (hB : P.TauBimult)


variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')


end Level

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}


end ThetaShiftProofs

section Main

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

end Main

end GlobalTheory.ArcInputCompare
end
end

