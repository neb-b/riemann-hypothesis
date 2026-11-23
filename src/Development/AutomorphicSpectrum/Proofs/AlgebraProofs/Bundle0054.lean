module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinright
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealArithmeticVarietyImage
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegree

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRestrictPreimageOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict

theorem opensRange_homOfLE_eq {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) :
    (X.homOfLE h).opensRange = V.ι ⁻¹ᵁ U := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    show V.ι (X.homOfLE h y) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact y.2
  · intro x hx
    exact ⟨⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply h _)⟩

theorem isChart_of_le {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
    (h : IsChart a b V q) (D : Y.Opens) (W : X.Opens) (hle : W ≤ V)
    (hW : ∀ u : V.toScheme, V.ι u ∈ W ↔ q u ∈ D) :
    ∃ q' : W.toScheme ⟶ D.toScheme, IsChart a b W q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  obtain ⟨hst, hfin, hflat, hlfp, hsurj, a', ha', hpbV⟩ := h

  have hrange : Set.range (X.homOfLE hle ≫ q) ⊆ Set.range D.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show q (X.homOfLE hle w) ∈ D
    rw [← hW, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact w.2
  let q' : W.toScheme ⟶ D.toScheme := IsOpenImmersion.lift D.ι (X.homOfLE hle ≫ q) hrange
  have hq' : q' ≫ D.ι = X.homOfLE hle ≫ q := IsOpenImmersion.lift_fac _ _ _

  have hS2 : IsPullback q' (X.homOfLE hle) D.ι q := by
    refine IsOpenImmersion.isPullback q' (X.homOfLE hle) D.ι q hq'.symm ?_
    rw [Scheme.Opens.opensRange_ι, opensRange_homOfLE_eq hle]
    ext u
    exact (hW u).symm

  have hstW : a ⁻¹ᵁ W = b ⁻¹ᵁ W := by
    ext p
    show a p ∈ W ↔ b p ∈ W
    by_cases hpa : a p ∈ V
    · have hpb : b p ∈ V := by
        have : p ∈ a ⁻¹ᵁ V := hpa
        rw [hst] at this
        exact this
      obtain ⟨u, hu⟩ : a p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hpa
      obtain ⟨u', hu'⟩ : b p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hpb
      have hq : q u = q u' :=
        (IsChart.apply_eq_iff ⟨hst, hfin, hflat, hlfp, hsurj, a', ha', hpbV⟩ u u').mpr ⟨p, hu.symm, hu'.symm⟩
      have e1 := hW u
      have e2 := hW u'
      rw [hu] at e1
      rw [hu'] at e2
      rw [e1, e2, hq]
    · have hpb : b p ∉ V := fun hb => hpa (by
        have : p ∈ b ⁻¹ᵁ V := hb
        rw [← hst] at this
        exact this)
      exact ⟨fun hw => absurd (hle hw) hpa, fun hw => absurd (hle hw) hpb⟩

  have hrange' : Set.range ((b ⁻¹ᵁ W).ι ≫ a) ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : p.1 ∈ a ⁻¹ᵁ W := by rw [hstW]; exact p.2
    exact this
  let a'' : (b ⁻¹ᵁ W).toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι ((b ⁻¹ᵁ W).ι ≫ a) hrange'
  have ha'' : a'' ≫ W.ι = (b ⁻¹ᵁ W).ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  let ιK : (b ⁻¹ᵁ W).toScheme ⟶ (b ⁻¹ᵁ V).toScheme := P.homOfLE (b.preimage_mono hle)
  have hL : IsPullback (b ∣_ W) ιK (X.homOfLE hle) (b ∣_ V) := by
    refine IsOpenImmersion.isPullback (b ∣_ W) ιK (X.homOfLE hle) (b ∣_ V) ?_ ?_
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι,
        morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    · rw [opensRange_homOfLE_eq hle, opensRange_homOfLE_eq (b.preimage_mono hle)]
      ext p
      show (b ∣_ V) p ∈ V.ι ⁻¹ᵁ W ↔ (b ⁻¹ᵁ V).ι p ∈ b ⁻¹ᵁ W
      rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
        morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hcomm : ιK ≫ a' = a'' ≫ X.homOfLE hle := by
    rw [← cancel_mono V.ι, Category.assoc, ha', Category.assoc, Scheme.homOfLE_ι, ha'',
      ← Category.assoc, Scheme.homOfLE_ι]
  have hs : IsPullback (a'' ≫ X.homOfLE hle) (b ∣_ W) q (q' ≫ D.ι) := by
    have := hL.flip.paste_horiz hpbV
    rw [hcomm, ← hq'] at this
    exact this
  have hpW : IsPullback a'' (b ∣_ W) q' q' := by
    refine hs.of_right ?_ hS2.flip
    rw [← cancel_mono D.ι, Category.assoc, Category.assoc, hq']
    simpa [hq'] using hs.w
  exact ⟨q', ⟨hstW, MorphismProperty.of_isPullback hS2.flip hfin,
    MorphismProperty.of_isPullback hS2.flip hflat, MorphismProperty.of_isPullback hS2.flip hlfp,
    MorphismProperty.of_isPullback hS2.flip hsurj, a'', ha'', hpW⟩, hq'⟩

end GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem isChart_restrict_quotient_open :
    ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y},
      IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V)
        (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme),
        IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  intro P X Y a b V q h D
  have hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V := V.ι_image_le _
  have hW : ∀ u : V.toScheme, V.ι u ∈ V.ι ''ᵁ (q ⁻¹ᵁ D) ↔ q u ∈ D := fun u =>
    (Scheme.Opens.mem_ι_image_iff (x := u) (V := q ⁻¹ᵁ D))
  obtain ⟨q', hq', hfac⟩ := ChartRestrict.isChart_of_le h D _ hle hW
  exact ⟨hle, q', hq', hfac⟩

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualTowerHodgeTateDatumStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tower_hodge_tate_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum | exact GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum | (intros; apply GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteSetBasicOpenAffineStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_set_basic_open_affine : ∀ {X : Scheme.{0}} (U V₀ : X.Opens), IsAffineOpen U → V₀ ≤ U → ∀ K : Set X, K.Finite → K ⊆ V₀ → ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  first | exact @GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between | exact GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between | (intros; apply GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRight
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback _root_.GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCover
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue


set_option backward.isDefEq.respectTransparency false in
theorem exists_colimit_of_quotient_charts : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by
  intro X R 𝒰 hbas hc Y q hepi hsurj hfib hst k hko hqk
  have hr (U : 𝒰) : U.1.ι.opensRange = U.1 := Scheme.Opens.opensRange_ι _
  have hmem (U : 𝒰) (x : U.1.toScheme) : U.1.ι x ∈ U.1 := by
    have : U.1.ι x ∈ U.1.ι.opensRange := ⟨x, rfl⟩
    rwa [hr U] at this
  have hex (U : 𝒰) (x : X) (hx : x ∈ U.1) : ∃ y, U.1.ι y = x := by
    rw [← hr U] at hx; exact hx
  have hinj (U : 𝒰) : Function.Injective U.1.ι := U.1.ι.isOpenEmbedding.injective
  have hm {U V : 𝒰} (h : U.1 ≤ V.1) : X.homOfLE h ≫ V.1.ι = U.1.ι := X.homOfLE_ι h
  have hm' {U V : 𝒰} (h : U.1 ≤ V.1) (x : U.1.toScheme) : V.1.ι (X.homOfLE h x) = U.1.ι x :=
    congr($(hm h) x)
  have hmo {U V : 𝒰} (h : U.1 ≤ V.1) : IsOpenImmersion (X.homOfLE h) := by
    have : IsOpenImmersion (X.homOfLE h ≫ V.1.ι) := by rw [hm]; infer_instance
    exact .of_comp _ V.1.ι
  let F : 𝒰 ⥤ Scheme.{0} :=
    { obj := Y
      map {U V} f := k U V f.le
      map_id U := by
        have := hepi U
        rw [← cancel_epi (q U), hqk]
        have : X.homOfLE (show U.1 ≤ U.1 from (𝟙 U : U ⟶ U).le) = 𝟙 _ := by
          rw [← cancel_mono U.1.ι, hm, Category.id_comp]
        rw [this, Category.id_comp]
        exact (Category.comp_id _).symm
      map_comp {U V W} f g := by
        have := hepi U
        rw [← cancel_epi (q U), hqk, reassoc_of% (hqk U V f.le), hqk]
        have : X.homOfLE (show U.1 ≤ W.1 from (f ≫ g).le) =
            X.homOfLE (show U.1 ≤ V.1 from f.le) ≫ X.homOfLE (show V.1 ≤ W.1 from g.le) := by
          rw [← cancel_mono W.1.ι, Category.assoc, hm, hm, hm]
        rw [this, Category.assoc] }
  let e (U : 𝒰) : U.1.toScheme ⟶ F.obj U := q U
  have hnat {U V : 𝒰} (f : U ⟶ V) :
      e U ≫ F.map f = X.homOfLE (show U.1 ≤ V.1 from f.le) ≫ e V := hqk U V f.le
  have hnat' {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme) :
      F.map f (e U x) = e V (X.homOfLE (show U.1 ≤ V.1 from f.le) x) := congr($(hnat f) x)
  have hF {U V : 𝒰} (f : U ⟶ V) : IsOpenImmersion (F.map f) := hko U V f.le
  have hsurj' (U : 𝒰) : Function.Surjective (e U) := hsurj U
  have hfib' (U : 𝒰) (x y : U.1.toScheme) : e U x = e U y ↔ R (U.1.ι x) (U.1.ι y) := hfib U x y
  have key {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme) (h : U.1.ι x = V.1.ι y) :
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U x) (h ▸ hmem V y)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ z, ?_, ?_⟩
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz]
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz, h]
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨x, rfl⟩ := hsurj' U x
    obtain ⟨y, rfl⟩ := hsurj' V y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    have hR := (hfib' _ _ _).mp h'
    rw [hm', hm'] at hR
    obtain ⟨y', hy'⟩ := hex U _ (hst U _ _ hR (hmem U x))
    have hxy : e U x = e U y' := (hfib' U _ _).mpr (by rw [hy']; exact hR)
    have := key _ _ hy'
    rwa [← hxy] at this
  have key2 {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme)
      (h : colimit.ι F U (e U x) = colimit.ι F V (e V y)) : V.1.ι y ∈ U.1 := by
    obtain ⟨W, f, g, z, -, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := hsurj' W z
    rw [hnat'] at h2
    have hR := (hfib' _ _ _).mp h2
    rw [hm'] at hR
    exact hst U _ _ hR ((show W.1 ≤ U.1 from f.le) (hmem W _))
  let 𝒱 : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰 (fun U ↦ U.1.toScheme) (fun U ↦ U.1.ι)
    (fun x ↦ by
      obtain ⟨U, hU⟩ := hc x
      exact ⟨U, hex U x hU⟩)
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    change 𝒰 at U V
    change pullback.fst U.1.ι V.1.ι ≫ (e U ≫ colimit.ι F U) =
      pullback.snd U.1.ι V.1.ι ≫ (e V ≫ colimit.ι F V)
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : U.1.ι (pullback.fst U.1.ι V.1.ι x) = V.1.ι (pullback.snd U.1.ι V.1.ι x) :=
      congr($(pullback.condition (f := U.1.ι) (g := V.1.ι)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U _) (hx ▸ hmem V _)
    let α : W.toScheme ⟶ pullback U.1.ι V.1.ι :=
      pullback.lift (X.homOfLE h1) (X.homOfLE h2) ((hm (U := ⟨W, hW⟩) h1).trans (hm (U := ⟨W, hW⟩) h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = X.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = X.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; exact hmo (U := ⟨W, hW⟩) _
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨α.opensRange, ⟨z, ?_⟩, ?_⟩
    · apply (pullback.fst U.1.ι V.1.ι).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      apply hinj
      rw [hm' (U := ⟨W, hW⟩), hz]
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      change α ≫ pullback.fst U.1.ι V.1.ι ≫ e U ≫ colimit.ι F U =
        α ≫ pullback.snd U.1.ι V.1.ι ≫ e V ≫ colimit.ι F V
      rw [reassoc_of% hα1, reassoc_of% hα2,
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) (homOfLE h1)),
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) (homOfLE h2)), colimit.w, colimit.w])
  have hj (U : 𝒰) : U.1.ι ≫ j = e U ≫ colimit.ι F U := 𝒱.ι_glueMorphisms _ _ U
  have hj' (U : 𝒰) (x : U.1.toScheme) : j (U.1.ι x) = colimit.ι F U (e U x) := congr($(hj U) x)
  have hpre (U : 𝒰) : j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hsurj' U y
      obtain ⟨V, hV⟩ := hc x
      obtain ⟨z, rfl⟩ := hex V x hV
      exact key2 y z (hy.trans (hj' V z))
    · intro hx
      obtain ⟨z, rfl⟩ := hex U x hx
      exact ⟨_, (hj' U z).symm⟩
  refine ⟨colimit F, j, fun U ↦ colimit.ι F U, fun U ↦ inferInstance, hj, hpre, fun y ↦ ?_⟩
  obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
  exact ⟨U, x, rfl⟩

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  classical
  intro E _ _ _ H D I _ _ e hcard hli
  haveI := D.fin
  have T : ∀ (c : 𝓞 E) (x y : D.La), Algebra.trace ℚ E (algebraMap (𝓞 E) E c * sesq D x y) = ((D.EF (c • x) y : ℤ) : ℚ) := by
    intro c x y
    have key : ∀ j, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * sesq D x y) = ((D.EF (RingOfIntegers.basis E j • x) y : ℤ) : ℚ) := by
      intro j
      have hterm : ∀ k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * (((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : E) * HT.dualInt E k)) = ((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : ℚ) * (if j = k then 1 else 0) := by
        intro k
        rw [← HT.LatBasic.trace_dualInt k j, ← map_intCast (algebraMap ℚ E), mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (algebraMap (𝓞 E) E _), ← NumberField.integralBasis_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [sesq, Finset.mul_sum, map_sum, hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact mul_one _
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_mul, Finset.sum_smul, LinearMap.sum_apply, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, smul_mul_assoc, map_zsmul, key j, smul_assoc, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    norm_cast
  have hy : ∀ y : D.La, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    by_contra hne
    push_neg at hne
    have hli' : LinearIndependent (𝓞 E) (fun o : Option I => Option.elim o y e) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fintype.sum_option] at hg
      simp only [Option.elim] at hg
      have hnone : g none = 0 := by
        by_contra h0
        apply hne (g none) h0
        have : g none • y = -∑ i, g (some i) • e i := eq_neg_of_add_eq_zero_left hg
        rw [this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)))
      rw [hnone, zero_smul, zero_add] at hg
      intro o
      cases o with
      | none => exact hnone
      | some i => exact (Fintype.linearIndependent_iff.mp hli) _ hg i
    have := hli'.fintype_card_le_finrank
    rw [Fintype.card_option, hcard, D.rank] at this
    omega
  have hfin : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ y : D.La, c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule (𝓞 E) D.La).FG)
    choose f hf0 hfm using hy
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr (fun y _ => hf0 y), ?_⟩
    intro y
    have hy' : y ∈ Submodule.span (𝓞 E) (s : Set D.La) := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
    · intro z hz
      rw [← Finset.mul_prod_erase s f hz, mul_comm (f z), mul_smul]
      exact Submodule.smul_mem _ _ (hfm z)
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨c, hc0, hc⟩ := hfin
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  have hN0 : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  have hNy : ∀ y : D.La, Ideal.absNorm (Ideal.span {c}) • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← ht, mul_smul]
    exact Submodule.smul_mem _ _ (hc y)
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ v
    choose a ha using fun i => RingHom.mem_rangeS.mp (hb i (Finset.mem_univ i))
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv0
    have hai0 : a i0 ≠ 0 := by
      intro h0
      have := ha i0
      rw [h0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
      rcases this with h | h
      · exact nonZeroDivisors.coe_ne_zero b ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h)
      · exact hi0 h
    have hx0 : (∑ i, a i • e i) ≠ 0 := fun h => hai0 ((Fintype.linearIndependent_iff.mp hli) a h i0)
    have hEFc : ∀ (c : 𝓞 E) (n : I), D.EF (c • ∑ i, a i • e i) (e n) = 0 := by
      intro c n
      have h1 : c • ∑ i, a i • e i = ∑ m, (c * a m) • e m := by simp only [Finset.smul_sum, mul_smul]
      apply Int.cast_injective (α := ℚ)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum, LinearMap.sum_apply, Int.cast_sum, Int.cast_zero]
      simp only [← T]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      have h2 : ∑ m, algebraMap (𝓞 E) E (c * a m) * sesq D (e m) (e n) = algebraMap (𝓞 E) E c * (algebraMap (𝓞 E) E b * (v ᵥ* gramE D e) n) := by
        simp only [Matrix.vecMul, dotProduct, gramE, Matrix.of_apply, map_mul, ha, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => by ring)
      rw [h2, hv, Pi.zero_apply, mul_zero, mul_zero, map_zero]
    have hEF : ∀ y, D.EF (∑ i, a i • e i) y = 0 := by
      intro y
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp (hNy y)
      have h2 : D.EF (∑ i, a i • e i) (Ideal.absNorm (Ideal.span {c}) • y) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hg, map_sum]
        refine Finset.sum_eq_zero (fun n _ => ?_)
        have := D.adj (H.bar.symm (g n)) (∑ i, a i • e i) (e n)
        rw [RingEquiv.apply_symm_apply] at this
        rw [← this]
        exact hEFc _ n
      rw [map_nsmul] at h2
      exact (smul_eq_zero.mp h2).resolve_left hN0
    apply hx0
    apply D.unimod.1
    rw [map_zero]
    exact LinearMap.ext hEF
  · apply Set.Finite.subset ((Nat.divisors (Ideal.absNorm (Ideal.span {c}))).finite_toSet.preimage (f := ((↑) : Nat.Primes → ℕ)) (Set.injOn_of_injective Subtype.val_injective))
    intro ℓ hℓ
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hN0⟩
    by_contra hd
    exact hℓ (by unfold IsLocBasis; exact ⟨hli, _, hd, hNy⟩)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHolds
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graphStatement : GraphStatement := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.graphIdeal_isArithVar K ι K₂ ι₂ P d g δ hP hg hne
  refine ⟨h1, h2, ?_⟩
  intro G J hJ
  have hP' : IsArithVar (imageZ inlV (graphIdeal P g)) d := by rw [h2]; exact hP
  have hF : IsProjVarF (fibreIdeal Sum.inl G) 0 :=
    GlobalTheory.CompanionTheory.Ar.Giv.fibreDim K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV (graphIdeal P g) d 0 G
      isBlockMap_inl h1 hP'
  have hrel := hF.1.2.2
  let i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k := fun k => (hrel k).choose
  have hi : IsChart (fibreIdeal Sum.inl G) i := fun k => (hrel k).choose_spec
  rw [hJ.1 _ _ i hF hi]
  exact_mod_cast _root_.GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg K ι K₂ ι₂ P g hP.2.1.1 hne h2 G i hi

end GlobalTheory.CompanionTheory.Ar.Giv
end

