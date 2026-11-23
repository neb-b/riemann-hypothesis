module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiser
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitArcMatch

open GlobalTheory.TraitArc GlobalTheory.TauTwist GlobalTheory.ArcBuild GlobalTheory.ArcOfPoint Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {T : CDVR}

theorem genRel_psi_twist (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing T.V) F] (y : D.toPre.X) :
    GenRel (isoPullId (idIso D.toPre.P.L) rfl)
      (LB.pullGen _ _ _ (D.toPre.psi y) (jFK (R := T.V) F))
      (LB.pullGen _ _ _ ((D0 (H := H) D hϖ).psi y) (jFK (R := T.V) F))
      ((algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2)) := by
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hq : beF D hϖ y y / 2 = qv D hϖ y := by rw [beF_self]; omega
  let u : Fˣ := Units.mk0 _ h0 ^ (beF D hϖ y y / 2)
  have hu : ((u : Fˣ) : F) = (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2) := by
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← hu]
  refine ArcOfPoint.genRel_id_of_val D.toPre.P.isLB (DVR.pullGen_isGen _ _ _ _ (D.toPre.psi_gen y) _) fun z J hJ => ?_
  have ht : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (TraitArc.tF D hϖ y (H.w0 • y)) = u⁻¹ := by
    apply Units.ext
    simp only [u, TraitArc.tF, beF_w0 D oD, hq, Units.coe_map, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, zpow_neg]
    show (algebraMap (FractionRing T.V) F) ((((piK hϖ : (FractionRing T.V)ˣ) : FractionRing T.V) ^ qv D hϖ y)⁻¹) = _
    rw [map_inv₀, map_zpow₀]; rfl
  letI := H.starRing
  rw [val_pull hJ, val_pull hJ, Category.id_comp]
  erw [val_psi_twist H.w0 (TraitArc.tF D hϖ) y (jFK (R := T.V) F) hJ]
  rw [show jFK (R := T.V) F = 𝟙 _ ≫ spMap (algebraMap (FractionRing T.V) F) from (Category.id_comp _).symm,
    unitAt_spMap, ht, map_inv, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

theorem exists_isPullDeg_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  intro E _ _ _ H Dm l c O _ β T b D _ oD ϖ hϖ hX hw hdiv pA pM hLie hTate Xo Y y hY
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, -, h5, h6⟩ := hY
  refine ⟨t, m, P, ?_⟩
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := Spec.map_id _
  have he0 : eSec D.toPre.P.A ≫ 𝟙 _ = spMap (RingHom.id T.V) ≫ eSec D.toPre.P.A := by
    rw [hid, Category.comp_id]; exact (Category.id_comp _).symm
  have p : IsGrpPullback D.toPre.P.A D.toPre.P.A (spMap (RingHom.id T.V)) (𝟙 _) := by
    have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
    exact (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr hid.symm rfl
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  let F := AlgebraicClosure (FractionRing T.V)
  have k6 := (h6 F (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) (fun _ => rfl) rfl).1
  have r := (maps_iff (idW D.toPre.P.L) _ (fun _ => eSec D.toPre.P.A) _ D.toPre.rig D.toPre.rig _ _
    (rigPull_le (𝟙 _) _ he0 D.toPre.P.L) (fun _ => rfl)).1 (maps_rig_id D.toPre he0)
  have r' := (maps_iff w _ (fun _ => eSec D.toPre.P.A) _ P.D.toPre.rig D.toPre.rig _ _
    (rigPull_le φ _ he D.toPre.P.L) (fun _ => rfl)).1 h3
  let xe : P.D.toPre.X ≃+ D.toPre.X := e.symm.toAddEquiv
  have hxe : ∀ y, xe (e y) = y := fun y => e.symm_apply_apply y
  obtain ⟨hD, -⟩ := GlobalTheory.ArcData.exists_isPullDeg_id D.toPre P.D.toPre (A₀ := D.toPre.P.A) (M₀ := D.toPre.P.L)
    D.toPre.P.isLB D.toPre.rig p h1 (idW D.toPre.P.L) w
    ((isGen_iff _).1 ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) rfl))) ((isGen_iff _).1 h2)
    r r' xe (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      refine (h5 y).trans ?_
      rw [hid, Category.id_comp, Category.comp_id, hxe]; rfl)
    Wo hWo ψW (jFK (R := T.V) F) (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hxe]
      exact ⟨_, _, _, genRel_psi_twist D oD hϖ F y, k6 y⟩)
  exact ⟨hD⟩

end GlobalTheory.TraitArcMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DegPullId

theorem exists_isPullDeg_id_self : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  intro R _ _ I hR D
  have hgen {F : D.toPre.P.A.left ⟶ D.toPre.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.toPre.P.L.U a → f y ∈ D.toPre.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.toPre.P.L) rfl) f y a b =
          gm f y _ (D.toPre.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.toPre.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.toPre.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) (D.toPre.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U j') (D.toPre.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U k ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g j' k') :=
      (idIso_isGen D.toPre.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, h₁, -, h₃⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  refine ⟨hD, fun x => ?_, ?_⟩
  · rw [h₃]; rfl
  · rw [h₁]; exact hF'

end GlobalTheory.DegPullId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem exists_sec_nonzero_on_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  intro Y Y' Z' k hk p' hpc hps V hV y hy _ M hM hloc
  classical
  obtain ⟨hfin, hdisc⟩ := _root_.GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite Y Y' k hk y
  have hU : IsAffineOpen (k ⁻¹ᵁ V) := hV.preimage k
  let F : Finset Y' := hfin.toFinset
  have hF : ∀ a, a ∈ F ↔ k a = y := fun a => by simp [F]
  have hW : ∀ a : Y', ∃ W : Y'.Opens, (k a = y → a ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) := by
    intro a
    by_cases h : k a = y
    · obtain ⟨W, hW, t, ht⟩ := hloc a h
      exact ⟨W, fun _ => ⟨hW, t, ht⟩⟩
    · exact ⟨⊤, fun h' => absurd h' h⟩
  choose W hW using hW
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.exists_separating_basicOpen_functions Y' (k ⁻¹ᵁ V) hU F (fun a ha => by
      show k a ∈ V
      rw [(hF a).1 ha]; exact hy) (fun a ha b hb hab => hdisc a b ((hF a).1 ha) ((hF b).1 hb) hab)
    W (fun a ha => ((hW a) ((hF a).1 ha)).1)
  let q : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme ⟶ Y' := (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι ≫ p'
  have hq : (⊤ : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.Opens) ≤ q ⁻¹ᵁ (k ⁻¹ᵁ V) := by
    intro z _
    show p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z) ∈ k ⁻¹ᵁ V
    have h : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z ∈ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := (Scheme.Opens.range_ι (p' ⁻¹ᵁ (k ⁻¹ᵁ V))).subset ⟨z, rfl⟩
    exact h
  let r : Y' → Γ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, ⊤) := fun a => (q.appLE (k ⁻¹ᵁ V) ⊤ hq).hom (f a)
  have hr : ∀ a (z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme), z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ↔ q z ∈ Y'.basicOpen (f a) := by
    intro a z
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  haveI : CompactSpace (k ⁻¹ᵁ V).toScheme := isCompact_iff_compactSpace.1 hU.isCompact
  haveI : CompactSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := by
    have := hpc.isCompact_preimage _ (k ⁻¹ᵁ V).isOpen hU.isCompact
    exact isCompact_iff_compactSpace.1 this
  haveI : IsAffine (k ⁻¹ᵁ V).toScheme := hU
  haveI : QuasiSeparatedSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := quasiSeparatedSpace_of_quasiSeparated (p' ∣_ (k ⁻¹ᵁ V))
  have hσ : ∀ a : F, ∃ σ : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ≤ nonzeroLocus σ := by
    rintro ⟨a, ha⟩
    obtain ⟨-, t, ht⟩ := hW a ((hF a).1 ha)
    exact _root_.GlobalTheory.GenNearExtend.exists_sec_of_gen_near Z' _ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι inferInstance ‹_› ‹_› M hM (r a) (p' ⁻¹ᵁ W a)
      (fun x hx => (hf a ha).2.1 ((hr a x).1 hx)) t ht
  choose σ hσ using hσ
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.exists_sec_sum_nonzero _ (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι) F (fun a => r a) σ
  refine ⟨s, fun z hz => ?_⟩
  have ha : q z ∈ F := (hF _).2 hz
  have h1 : z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r (q z)) := (hr _ z).2 (hf _ ha).1
  refine hs z ⟨q z, ha⟩ h1 (hσ _ h1) (fun j hj => ?_)
  rw [hr]
  exact (hf j.1 j.2).2.2 (q z) ha (fun h => hj (Subtype.ext h.symm))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoveNear

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π G' _ _ _ N e he hPt Ω _ s g hT hs
  haveI := N.isOpen
  haveI := hR.1
  let xR := s ≫ π
  let UΩ := pullback N.U.hom xR
  let T := pullback G'.hom s
  let m : UΩ ⟶ pullback N.U.hom π := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [Category.assoc]; exact pullback.condition)
  let k : UΩ ⟶ T := pullback.lift (m ≫ N.u) (pullback.snd _ _)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd])
  have sqP : IsPullback m (pullback.snd N.U.hom xR) (pullback.snd N.U.hom π) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback N.U.hom π)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback N.U.hom xR
  have sqk : IsPullback m k N.u (pullback.fst G'.hom s) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G'.hom s) (v₂₂ := G'.hom) (h₃₁ := s) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback G'.hom s)
    rw [pullback.lift_snd, N.u_over]
    exact sqP
  have hk : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqk N.isOpen
  let TO : Over S := Over.mk (pullback.snd G'.hom s ≫ s)
  let yT : TO ⟶ G' := Over.homMk (pullback.fst G'.hom s) pullback.condition
  let qT : TO ⟶ Over.mk s := Over.homMk (pullback.snd G'.hom s) rfl
  let zT : TO ⟶ G' := (qT ≫ g) * yT
  let UO : Over S := Over.mk (pullback.snd N.U.hom xR ≫ s)
  let kO : UO ⟶ TO := Over.homMk k (by
    change k ≫ pullback.snd _ _ ≫ s = _
    rw [pullback.lift_snd_assoc]
    rfl)
  have sec : ∀ h : Over.mk s ⟶ G', ∃ σ : Over.mk s ⟶ TO, σ ≫ yT = h ∧ σ ≫ qT = 𝟙 _ := fun h =>
    ⟨Over.homMk (pullback.lift h.left (𝟙 _) ((Over.w h).trans (Category.id_comp _).symm))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd G'.hom s ≫ s = s
        rw [pullback.lift_snd_assoc]
        exact Category.id_comp _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  have hone : ∀ p, (1 : Over.mk s ⟶ G').left p ∈ Set.range N.u := by
    obtain ⟨x₀, -, -, hx₀⟩ := hPt
    have e₁ : (1 : Over.mk s ⟶ G').left = s ≫ (1 : Over.mk (𝟙 S) ⟶ G').left := congrArg (fun f => f.left)
      (MonObj.comp_one (M := G') (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))).symm
    intro p
    rw [e₁, ← hx₀]
    exact ⟨x₀ (s p), rfl⟩
  have hoU : IsOpen (Set.range N.u) := N.u.isOpenEmbedding.isOpen_range
  obtain ⟨σ₁, h₁, -⟩ := sec 1
  obtain ⟨σ₂, h₂, h₂'⟩ := sec g⁻¹
  have e₂ : σ₂ ≫ zT = 1 := by
    rw [MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]
  have : IrreducibleSpace T := hT
  obtain ⟨t, ⟨p₀, hp₀⟩, ht⟩ := nonempty_preirreducible_inter (hoU.preimage (pullback.fst G'.hom s).continuous)
    (hoU.preimage zT.left.continuous)
    ⟨σ₁.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← h₁] at this
      exact this⟩
    ⟨σ₂.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← e₂] at this
      exact this⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback sqk p₀ t hp₀
  let O : UΩ.Opens := ⟨(kO ≫ zT).left ⁻¹' Set.range N.u, hoU.preimage (kO ≫ zT).left.continuous⟩
  have hwO : w ∈ O := by
    show (kO ≫ zT).left w ∈ Set.range N.u
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change zT.left (k w) ∈ Set.range N.u
    rw [hw]; exact ht
  have hirr : IrreducibleSpace UΩ := by
    refine (irreducibleSpace_def _).2 ⟨⟨w, trivial⟩, ?_⟩
    have := (IrreducibleSpace.isIrreducible_univ T).2.preimage k.isOpenEmbedding
    simpa using this
  obtain ⟨a, aΩ, ha, haf, has, hao⟩ := _root_.GlobalTheory.DenseSec.dense_sections R hR.2.2.2 N.U N.smooth e he Ω xR hs hirr O ⟨w, hwO⟩
  let x : Over.mk (𝟙 S) ⟶ G' := Over.homMk
    (pullback.lift (π ≫ a) (𝟙 S) (by rw [Category.assoc, ha, Category.comp_id]; exact (Category.id_comp π).symm) ≫ N.u)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
  refine ⟨a, x, ha, ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ?_⟩
  let rO : Over.mk s ⟶ UO := Over.homMk aΩ (by
    change aΩ ≫ pullback.snd _ _ ≫ s = s
    rw [← Category.assoc, has, Category.id_comp])
  have hq : rO ≫ kO ≫ qT = 𝟙 _ := by
    ext
    change aΩ ≫ k ≫ pullback.snd _ _ = 𝟙 _
    rw [pullback.lift_snd, has]
  have hy : rO ≫ kO ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
    ext
    change aΩ ≫ k ≫ pullback.fst _ _ = s ≫ pullback.lift (π ≫ a) (𝟙 S) _ ≫ N.u
    rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      show aΩ ≫ pullback.lift (pullback.fst N.U.hom xR) _ _ ≫ pullback.fst N.U.hom π = s ≫ π ≫ a
      rw [pullback.lift_fst, haf]
      simp only [xR, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, has,
        Category.id_comp, Category.comp_id]
  have hz : g * ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x) = rO ≫ kO ≫ zT := by
    have hq' : (rO ≫ kO) ≫ qT = 𝟙 _ := by rw [Category.assoc]; exact hq
    have hy' : (rO ≫ kO) ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
      rw [Category.assoc]; exact hy
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, hq', Category.id_comp, hy']
  rintro _ ⟨p, rfl⟩
  rw [hz]
  exact hao ⟨p, rfl⟩

end GlobalTheory.MoveNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslatesCoverSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Cover

theorem comp_one_pt {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] (f : X ⟶ Y) : f ≫ (1 : Y ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : G.left.Opens), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → ∀ x : G.left, ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, (𝟙 G * (toUnit G ≫ a)).left x ∈ O := by
  intro R _ _ _ hB G _ _ hG O hO x
  obtain ⟨hN, -, -, hC⟩ := hB
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom

  have hη : ∀ P : Sp R, (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left P ∈ O := by
    intro P
    have hc : G.hom ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left (closedPoint R)) = closedPoint R := by
      change ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
      rw [Over.w]
      rfl
    exact ((IsLocalRing.specializes_closedPoint P).map (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left.continuous).mem_open
      O.2 (hO _ hc)
  by_cases hx : G.hom x = closedPoint R
  · refine ⟨η[G], ?_⟩
    have : toUnit G ≫ (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := (Hom.one_def).symm
    rw [this, _root_.mul_one]
    exact hO x hx

  haveI := hN
  let k := G.left.residueField x
  let xp : Sp k ⟶ G.left := G.left.fromSpecResidueField x
  let s : Sp k ⟶ Sp R := xp ≫ G.hom
  have hrange : Set.range xp = {x} := Scheme.range_fromSpecResidueField x
  have hxp : ∀ p, xp p = x := fun p => by
    have h : xp p ∈ Set.range xp := ⟨p, rfl⟩
    rw [hrange] at h
    exact h
  obtain ⟨p0⟩ : Nonempty (Sp k) := inferInstance
  have hs : closedPoint R ∉ Set.range s := by
    rintro ⟨p, hp⟩
    apply hx
    rw [← hp, ← hxp p]
    rfl
  have hirr : IrreducibleSpace (pullback G.hom s : Scheme.{0}) := by
    have : IsIntegral (pullback G.hom s) := hGI.geometrically_isIntegral s _ _ (IsPullback.of_hasPullback _ _)
    infer_instance
  let Sx : Over (Sp R) := Over.mk s
  let T : Over (Sp R) := Over.mk (pullback.snd G.hom s ≫ s)
  let X' : Sx ⟶ G := Over.homMk xp rfl
  let p1 : T ⟶ G := Over.homMk (pullback.snd G.hom s ≫ xp) (by simp [T, s])
  let p2 : T ⟶ G := Over.homMk (pullback.fst G.hom s) (by simp [T, pullback.condition])
  let m : T ⟶ G := p1 * p2
  let l : Sp k ⟶ pullback G.hom s := pullback.lift (X'⁻¹).left (𝟙 _) (by simpa [Sx] using Over.w (X'⁻¹))
  have hl1 : l ≫ pullback.fst G.hom s = (X'⁻¹).left := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd G.hom s = 𝟙 _ := pullback.lift_snd _ _ _
  let σ : Sx ⟶ T := Over.homMk l (by
    change l ≫ pullback.snd G.hom s ≫ s = s
    rw [reassoc_of% hl2])
  have hσ : σ ≫ m = 1 := by
    have e1 : σ ≫ p1 = X' := by
      ext
      change l ≫ pullback.snd G.hom s ≫ xp = xp
      rw [reassoc_of% hl2]
    have e2 : σ ≫ p2 = X'⁻¹ := by
      ext
      exact hl1
    rw [comp_mul, e1, e2, _root_.mul_inv_cancel]
  have hne : ((m.left ⁻¹ᵁ O : (pullback G.hom s).Opens) : Set (pullback G.hom s : Scheme.{0})).Nonempty := by
    refine ⟨σ.left p0, ?_⟩
    change (σ.left ≫ m.left) p0 ∈ O
    rw [← Over.comp_left, hσ, Hom.one_def, Over.comp_left]
    exact hη _
  have he : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 _ := (Over.w _).trans (by simp)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := _root_.GlobalTheory.DenseSec.dense_sections R hC G ‹_› _ he k s hs hirr _ hne
  let A : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a (ha.trans (by simp))
  let AΩ : Sx ⟶ T := Over.homMk aΩ (by simp [T, Sx, reassoc_of% h2])
  have f1 : AΩ ≫ p1 = X' := by ext; simp [AΩ, p1, X', reassoc_of% h2]
  have f2 : AΩ ≫ p2 = toUnit Sx ≫ A := by ext; simp [AΩ, p2, A, h1, Sx]
  have key : X' ≫ (𝟙 G * (toUnit G ≫ A)) = AΩ ≫ m := by
    rw [comp_mul, comp_mul, f1, f2, Category.comp_id, comp_toUnit_assoc]
  refine ⟨A, ?_⟩
  rw [← hxp p0]
  change (X' ≫ (𝟙 G * (toUnit G ≫ A))).left p0 ∈ O
  rw [key]
  exact h3 ⟨p0, rfl⟩

end GlobalTheory.Mum.Cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProjectiveModel
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.BirModel

theorem exists_smooth_projective_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  intro hP k _ _ X _ p n hp hdim
  obtain ⟨Y, s, U, hY, hsm, hpr, hU, hiso⟩ := GlobalTheory.WeakRes.weak_resolution hP k X p n hp hdim
  have hdom : IsDominant s := GlobalTheory.T.isDominant_of_isIso_restrict' X Y s U hU hiso
  exact ⟨Y, hY, s, hdom, hsm, hpr, _root_.GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict X Y s U hU hiso⟩

end GlobalTheory.BirModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ), evA k x hx (X i) = x i := by
  first | exact @GlobalTheory.Katz.evA_X | exact GlobalTheory.Katz.evA_X | (intros; apply GlobalTheory.Katz.evA_X <;> assumption)
end

