module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfComplexPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgebraicSectionOfHolomorphicTheta
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersions
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ProjSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private theorem isImmersion_coprod_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsImmersion f] [IsImmersion g] : IsImmersion (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{0, 0} X' Y') ?_
  rintro (⟨⟩ | ⟨⟩)
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inl)
    have h := (isPullback_inl_inl_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inr)
    have h := (isPullback_inr_inr_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.ProjSpace.isQProjOver_of_isCompl : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0})
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ →
    IsCompl (Set.range f₁) (Set.range f₂) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₁ ≫ s) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₂ ≫ s) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s := by
  intro R _ X X₁ X₂ f₁ f₂ s h₁ h₂ hc q₁ q₂
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at q₁ q₂ ⊢
  obtain ⟨N₁, i₁, hi₁, hq₁, e₁⟩ := q₁
  obtain ⟨N₂, i₂, hi₂, hq₂, e₂⟩ := q₂
  have hP := _root_.GlobalTheory.ProjSpace.isProjOver_coprodDesc (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₁)
    (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₂)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at hP
  obtain ⟨M, j, hj, ej⟩ := hP
  have hc' : IsCompl f₁.opensRange f₂.opensRange :=
    ⟨disjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.inf_eq_bot)),
      codisjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.sup_eq_top))⟩
  obtain ⟨hX⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f₁ f₂ hc'
  let e : X₁ ⨿ X₂ ≅ X := (coprodIsCoprod X₁ X₂).coconePointUniqueUpToIso hX
  have he₁ : coprod.inl ≫ e.hom = f₁ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.left⟩
  have he₂ : coprod.inr ≫ e.hom = f₂ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.right⟩
  have hcomp : (e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M = s := by
    rw [Category.assoc, Category.assoc, ej, Iso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, ← Category.assoc, he₁, e₁]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, he₂, e₂]
  haveI := isImmersion_coprod_map i₁ i₂
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R M
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₁
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₂
  haveI : CompactSpace X₁ := (quasiCompact_iff_compactSpace (f₁ ≫ s)).mp (by rw [← e₁]; infer_instance)
  haveI : CompactSpace X₂ := (quasiCompact_iff_compactSpace (f₂ ≫ s)).mp (by rw [← e₂]; infer_instance)
  haveI : CompactSpace X := ⟨by
    rw [← Set.top_eq_univ, ← hc.sup_eq_top]
    exact (isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)⟩
  haveI : QuasiCompact s := (quasiCompact_iff_compactSpace s).mpr inferInstance
  haveI : QuasiCompact ((e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M) := by
    rw [hcomp]; infer_instance
  exact ⟨M, e.inv ≫ coprod.map i₁ i₂ ≫ j, inferInstance,
    QuasiCompact.of_comp _ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M), hcomp⟩

end GlobalTheory.ProjSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfRelAmpleRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.InhabZOn


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.Models.InhabZOn.exists_dim_triple {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
    [ConnectedSpace S] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H S) : ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyIntegral t.G.hom :=
    _root_.GlobalTheory.geometricallyIntegral_of_isSemiAbelian (h := t.semi) _
  let e : S ⟶ t.G.left := (η[t.G]).left
  have he : e ≫ t.G.hom = 𝟙 S := Over.w (η[t.G])
  have hes : ∀ s, t.G.hom (e s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfib : ∀ s : S, _root_.IsPreconnected (t.G.hom ⁻¹' {s}) := fun s => by
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  have hsec : _root_.IsPreconnected (Set.range e) :=
    isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  haveI : PreconnectedSpace t.G.left := by
    refine ⟨isPreconnected_of_forall (e s₀) fun x _ => ?_⟩
    refine ⟨Set.range e ∪ t.G.hom ⁻¹' {t.G.hom x}, Set.subset_univ _, Or.inl ⟨s₀, rfl⟩,
      Or.inr rfl, ?_⟩
    exact hsec.union (e (t.G.hom x)) ⟨_, rfl⟩ (hes _) (hfib _)
  exact _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected t.G.hom (e s₀)

end GlobalTheory.Models.InhabZOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LamPull

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) :
    IsSquare φ (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left :=
  ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem lbIso_lam_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ))
    {φ₂ : (G2 G').left ⟶ (G2 G).left} (hφ : IsSquare φ φ₂) : LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain rfl := isSquare_unique hφ (exists_isSquare h.1.w)
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB L hL _ _
  have h₁ : LBIso (abelian₂ G' L') (abelian₂ G' (L.pull φ)) := by
    obtain ⟨w, hw⟩ := H
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have h₂ : LBIso (abelian₂ G' (L.pull φ)) ((abelian₂ G L).pull U.left) := by
    refine LBIso.chartPull
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (Geo.Tor.chartPullPull (abelian₂ G L) _ U.left rfl) ⟨idIso _, idIso_isGen hΛ⟩
    fin_cases i <;> simp [U, x2]
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ (LB.isLB_pull hL φ) _ _) (LB.isLB_pull hΛ _) h₁ h₂

theorem lam_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), (∀ φ : t'.G.left ⟶ t.G.left, φ ≫ t.G.hom = t'.G.hom ≫ f → ∃ φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left, IsSquare φ φ₂) ∧ ∀ (ν : SABMap t' t f) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsSquare ν.φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) := by
  intro E _ _ _ H S S' t t' f
  refine ⟨fun φ w => ⟨_, exists_isSquare w⟩, fun ν φ₂ hφ => ?_⟩
  obtain ⟨w, hw, -⟩ := ν.lin
  exact lbIso_lam_pull ν.cart t.PP.isLB t'.PP.isLB ⟨w, hw⟩ hφ

end GlobalTheory.LamPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SameFactor

variable {A : Over (Sp ℂ)} [GrpObj A] {M M' : LB A.left} {g : ℕ}

theorem valAt'_div_g {X : Scheme.{0}} (M M' : LB X) (x : Sp ℂ ⟶ X) (p q : (LB.div M' M).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M' M).U p ⊓ (LB.div M' M).U q)) :
    valAt' x ((LB.div M' M).U p ⊓ (LB.div M' M).U q) ((LB.div M' M).g p q).val =
      valAt' x (M'.U p.1 ⊓ M'.U q.1) (M'.g p.1 q.1).val * (valAt' x (M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2).val)⁻¹ := by
  dsimp only [LB.div] at h ⊢
  rw [Units.val_mul, valAt'_mul, valAt'_units_inv x h, GlobalTheory.HolSecAlg.val_res_unit x _ _ h,
    GlobalTheory.HolSecAlg.val_res_unit x _ _ h]

def divUnif (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex) : HolUnif A (LB.div M' M) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun p z => u'.fr p.1 z * (u.fr p.2 z)⁻¹
  fr_hol := fun p => by
    have h1 := u'.fr_hol p.1
    rw [hex] at h1
    refine DifferentiableOn.mul (h1.mono fun z hz => ?_)
      (DifferentiableOn.inv ((u.fr_hol p.2).mono fun z hz => ?_) fun z hz => u.fr_ne _ _ ?_)
    · exact ((top_le_preimage_inf _ _ _).1 hz).1
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne := fun p z hz => by
    obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    exact mul_ne_zero (u'.fr_ne _ _ (by rw [hex]; exact h1)) (inv_ne_zero (u.fr_ne _ _ h2))
  fr_compat := fun p q z hz => by
    obtain ⟨hp, hq⟩ := (top_le_preimage_inf _ _ _).1 hz
    obtain ⟨hp1, hp2⟩ := (top_le_preimage_inf _ _ _).1 hp
    obtain ⟨hq1, hq2⟩ := (top_le_preimage_inf _ _ _).1 hq
    have e1 := u'.fr_compat p.1 q.1 z (by rw [hex]; exact (top_le_preimage_inf _ _ _).2 ⟨hp1, hq1⟩)
    rw [hex] at e1
    have e2 := u.fr_compat p.2 q.2 z ((top_le_preimage_inf _ _ _).2 ⟨hp2, hq2⟩)
    rw [valAt'_div_g M M' _ p q hz, e1, e2, mul_inv]
    ring

theorem exists_gen_of_isFn [LocallyOfFiniteType A.hom] (u : HolUnif A M g) (s : M.Sec) (θ : (Fin g → ℂ) → ℂ)
    (hs : u.IsFn s θ) (hθ : ∀ z, θ z ≠ 0) : ∃ t : LB.Gen M, t.IsGen := by

  have hunit : ∀ i, IsUnit (s.f i) := fun i =>
    GlobalTheory.ThetaBundleSym.isUnit_of_complex_points u.ex_onto (s.f i) fun z hz => by
      rw [hs i z hz]
      exact mul_ne_zero (hθ z) (u.fr_ne i z hz)
  refine ⟨⟨fun i => (hunit i).unit⟩, fun i j => Units.ext ?_⟩
  rw [Units.val_mul]
  exact s.compat i j

end SameFactor

theorem lbIso_of_same_factor : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (M M' : LB P.A.left) (u : HolUnif P.A M P.g) (u' : HolUnif P.A M' P.g), M.IsLB → M'.IsLB → u'.ex = u.ex → (∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ M'.U j → u.fr i z * u'.fr j (z + l) = u.fr i (z + l) * u'.fr j z) → LBIso M M' := by
  intro hL hL2 hTh hU P M M' u u' hM hM' hex hfac
  have : LocallyOfFiniteType P.A.hom := by
    have := P.isAb.proper
    infer_instance

  obtain ⟨s, hs⟩ := _root_.GlobalTheory.exists_sec_isFn_of_differentiable hL hL2 hTh hU P (LB.div M' M) (SameFactor.divUnif u u' hex) (fun _ => 1)
    (LB.isLB_div hM' hM) (differentiable_const 1) (by
      intro l p z hz
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have hl : u.ex (z + l) = u.ex z := GlobalTheory.HolSecAlg.ex_add_lattice u z l.2
      have n0 : u.fr p.2 z ≠ 0 := u.fr_ne _ _ h2
      have n1 : u.fr p.2 (z + l) ≠ 0 := u.fr_ne _ _ (by rw [hl]; exact h2)
      have key := hfac l p.2 p.1 z h2 h1
      show (1 : ℂ) * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (u'.fr p.1 z * (u.fr p.2 z)⁻¹)
      rw [_root_.one_mul, _root_.one_mul, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff n1 n0]
      linear_combination key)
  obtain ⟨t, ht⟩ := SameFactor.exists_gen_of_isFn _ s (fun _ => 1) hs fun _ => one_ne_zero
  exact ⟨t, ht⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDvdFormOfCubWeilOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.Coisotropic

theorem eq_one_of_unitOn_eq_one {R : Type} [CommRing R] {u : Rˣ} (h : unitOn u = 1) : u = 1 := by
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact congrArg Units.val h

theorem level_dvd_form_of_cubWeil_one : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ∀ (K : Type) [Field K] [IsAlgClosed K] (u : Sp K ⟶ U) (a a' : D.La) (p p' : Over.mk (u ≫ j) ⟶ t.G), p.left = u ≫ (o.etaA a).left ≫ μ₀.φ → p'.left = u ≫ (o.etaA a').left ≫ μ₀.φ → CubWeil t.cub l.A p p' 1 → (l.A : ℤ) ∣ D.EF a a' := by
  intro hL E _ _ _ H D l B _ b X U j s o t μ₀ K _ _ u a a' p p' hp hp' h
  have hβ : u ≫ s = spMap (Spec.preimage (u ≫ s)).hom := (Spec.map_preimage (u ≫ s)).symm
  obtain ⟨-, I, -, hI, -⟩ := o.geom K u _ hβ
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have kill : ∀ c, I.ev l.A c ^ l.A = 1 := fun c => (I.onto l.A l.A_pos _).2 ⟨c, rfl⟩
  have h₁ : CubWeil o.t.cub l.A (I.ev l.A a) (I.ev l.A a') (unitOn (I.ζ l.A ^ D.EF a a')) :=
    (cubWeil_iff_weilIs hL.globalFns hA (kill a) (kill a') _).2 (I.isom l.A l.A_pos a a')
  have h₂ := _root_.GlobalTheory.UU.cubWeil_of_isPullCubical X U j t.G o.t.G μ₀.cm μ₀.cart.1.w
    (fun T x y => Over.OverMorphism.ext (μ₀.cart.2 T x y _ _ rfl rfl).symm) _ _ _ _ μ₀.lin l.A _ _ _ _ h₁
  have e : ∀ (c : D.La) (q : Over.mk (u ≫ j) ⟶ t.G), q.left = u ≫ (o.etaA c).left ≫ μ₀.φ →
      Out.toBase μ₀.cart.1.w (I.ev l.A c) = q := fun c q hq => Over.OverMorphism.ext (by
    rw [hq, ← hI c]
    show ((toUnit (Over.mk u)).left ≫ (o.etaA c).left) ≫ μ₀.φ = _
    rw [Category.assoc]
    rfl)
  rw [e a p hp, e a' p' hp'] at h₂
  exact ((I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd _).1 (eq_one_of_unitOn_eq_one (h₂.unique h))

end GlobalTheory.Coisotropic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfGLiesOfHasTh
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem level_eq_of_gLies_of_hasTh : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (S S₁ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g ((n ^ j) ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ S₁) (w : Ix g ((n ^ j) ^ 2) → K), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ c = y' ≫ c → y ≫ s₁ = y' ≫ s₁ → t₁.HasTh y w → t₁.HasTh y' w → ∀ i, y ≫ (t₁.pt i).left ≫ ψ₁ = y' ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro hL hL2 g n j J hn hodd hj o _ b S S₁ A _ L act Q c s₁ t₁ ψ₁ K _ _ y y' w hLB hG hI hc hs T T'
  obtain ⟨u, ψ, m, ⟨a₁, -, a₃⟩, l, p⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y (y ≫ s₁) hLB hG hI rfl
  obtain ⟨u', ψ', m', ⟨a₁', -, a₃'⟩, l', p'⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y' (y ≫ s₁) hLB hG hI hs.symm
  rw [← hc] at a₁' a₃'
  have U : u.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u _ K _ _ m).2 (by rwa [Category.id_comp])
  have U' : u'.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u' _ K _ _ m').2 (by rwa [Category.id_comp])
  have hp := a₁.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom a₁'.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  have c₁ : IsGrpPullback u'.A u.A (𝟙 _) χ :=
    a₁.cancel (a₁'.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id])
  have c₀ : LBIso (u.L.pull χ) (L.pull ψ') :=
    l.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull u.L χ χ rfl)
      (chartPullSame L (fun _ : PUnit => ψ') (fun _ : PUnit => ψ) (fun _ => 1) χ (fun _ => e₁.symm))
  have c₂ : LBIso u'.L (u.L.pull χ) :=
    LBIso.trans u'.isLB (pull_isLB hLB _) (pull_isLB u.isLB _) l' c₀.symm
  have c₃ : ∀ i, (u'.pt i ^ n ^ j).left ≫ χ = (u.pt i ^ n ^ j).left := fun i => by
    apply hp.hom_ext
    · rw [Category.assoc, e₁, a₃', a₃]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ U U'
  intro i
  rw [← p, ← p', ← c₅, Category.assoc, e₁]

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBas
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

theorem exists_pull_LPow_sec {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (N : ℕ) {T T' : Over Z}
    (h : T' ⟶ T) (b : LB.Sec (Out.LPow G L (N : ℤ) T)) :
    ∃ b' : LB.Sec (Out.LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) b' r z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (r ≫ (h ▷ G).left) z J := by
  have hu : (LB.oneGen L (Y := (T' ⊗ G).left)).IsGen := by
    intro (i : PEmpty → L.ι) (j : PEmpty → L.ι)
    simp [LB.oneGen, LB.LinComb, res]
    ext
    erw [Units.val_mul, Units.coe_map, Units.coe_map, Units.val_one, _root_.one_mul, map_one, map_one]
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (h ▷ G).left ≫ (snd T G).left)
      (PEmpty.elim : PEmpty → ((T' ⊗ G).left ⟶ G.left))) (Sum.elim (fun _ => (N : ℤ)) PEmpty.elim)
      (fun _ : Fin 1 => (snd T' G).left) (fun _ => (N : ℤ)) := by
    intro U _ f
    simp [Fintype.prod_sum_type]
  obtain ⟨b', hb'⟩ := exists_sec hL hf
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (h ▷ G).left
      (LB.oneGen L (Y := (T' ⊗ G).left)) hu)
  refine ⟨b', fun Y r z J hJ => (hb' Y r z J hJ).trans ((sval_pullMulSec _ _ _ hu r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem basisAlong_id_of_basisAlong : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  intro Z G L N n T T' h b hL hB
  choose b' hb' using fun i => exists_pull_LPow_sec G L hL N h (b i)
  have key : ∀ s c, GlobalTheory.LN.Lin G L N (𝟙 T') b' c s ↔ GlobalTheory.LN.Lin G L N h b c s := by
    intro s c
    have e : ∀ i (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (b' i) ((𝟙 T') ▷ G).left z J =
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro i z J hJ
      rw [hb' i _ _ z J hJ]
      simp
    unfold GlobalTheory.LN.Lin
    refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun hJ => ?_
    simp only [e _ z J hJ]
  unfold GlobalTheory.LN.BasisAlong at hB ⊢
  refine ⟨b', fun s => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB s
  exact ⟨c, (key s c).2 hc, fun c' hc' => hu c' ((key s c').1 hc')⟩

end GlobalTheory.ModelSum
end

