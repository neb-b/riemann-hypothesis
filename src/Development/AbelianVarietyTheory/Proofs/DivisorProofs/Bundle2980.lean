module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphism
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.PullAutConst

theorem gm_pullChart {X Z T : Scheme.{0}} (L : LB X) (F : Z ⟶ X) (f : T ⟶ Z) (y : T) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y _ ((L.pull F).g (fun _ => j) (fun _ => j')) = gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

theorem exists_glued {X Y B : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β))
    (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hL : L.IsLB) (hM : M₀.IsLB)
    (hF : PGen wF) (hw : PGen w) (hβ : π₁ ≫ β = π₂ ≫ β) :
    ∃ s : Γ(B, ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (j₀ : M₀.ι) (j₁ j₂ : L.ι),
      β (π₁ (f z)) ∈ M₀.U j₀ → π₁ (f z) ∈ L.U j₁ → π₂ (f z) ∈ L.U j₂ →
      gm f z ⊤ s = gw wF (f ≫ π₂) z j₀ j₂ * gw w f z j₂ (fun _ => j₁) * (gw wF (f ≫ π₁) z j₀ j₁)⁻¹ := by
  have hpt : ∀ x, β (π₁ x) = β (π₂ x) := fun x => congrArg (fun g : B ⟶ Y => g x) hβ
  obtain ⟨W, hW⟩ : ∃ W : M₀.ι × L.ι × L.ι → B.Opens, ∀ t x,
      x ∈ W t ↔ β (π₁ x) ∈ M₀.U t.1 ∧ π₁ x ∈ L.U t.2.1 ∧ π₂ x ∈ L.U t.2.2 :=
    ⟨fun t => π₁ ⁻¹ᵁ (β ⁻¹ᵁ M₀.U t.1) ⊓ (π₁ ⁻¹ᵁ L.U t.2.1 ⊓ π₂ ⁻¹ᵁ L.U t.2.2), fun _ _ => Iff.rfl⟩
  have l₂ : ∀ t, W t ≤ π₂ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.2) := fun t x hx =>
    ⟨mem_pull.2 (show β (π₂ x) ∈ _ by rw [← hpt]; exact ((hW t x).1 hx).1), ((hW t x).1 hx).2.2⟩
  have lw : ∀ t, W t ≤ (L.pull π₂).U (fun _ => t.2.2) ⊓ (L.pull π₁).U (fun _ => t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).2.2, mem_pull.2 ((hW t x).1 hx).2.1⟩
  have l₁ : ∀ t, W t ≤ π₁ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).1, ((hW t x).1 hx).2.1⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ t, Γ(B, W t)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t : M₀.ι × L.ι × L.ι), f z ∈ W t →
      gm f z (W t) (u t) =
        gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ :=
    ⟨fun t => res (l₂ t) (pullU π₂ _ (wF.s (fun _ => t.1, t.2.2))) * res (lw t) (w.s (fun _ => t.2.2, fun _ => t.2.1)) *
        (res (l₁ t) (pullU π₁ _ (wF.s (fun _ => t.1, t.2.1))))⁻¹, fun Z f z t hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res f z (l₂ t) hz _).trans (gm_pull f π₂ z _ (l₂ t hz) _)) (gm_res f z (lw t) hz _)))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ t) hz _).trans (gm_pull f π₁ z _ (l₁ t hz) _)))))⟩
  have indep : ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t t' : M₀.ι × L.ι × L.ι), f z ∈ W t → f z ∈ W t' →
      gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ =
      gw wF (f ≫ π₂) z t'.1 t'.2.2 * gw w f z t'.2.2 (fun _ => t'.2.1) * (gw wF (f ≫ π₁) z t'.1 t'.2.1)⁻¹ := by
    rintro Z f z ⟨a, b, c⟩ ⟨a', b', c'⟩ h h'
    obtain ⟨ha, hb, hc⟩ := (hW _ _).1 h
    obtain ⟨ha', hb', hc'⟩ := (hW _ _).1 h'
    have e₂ := hF Z (f ≫ π₂) z a a' c c' (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha)
      (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha') hc hc'
    have e₁ := hF Z (f ≫ π₁) z a a' b b' ha ha' hb hb'
    have ew := hw Z f z c c' (fun _ => b) (fun _ => b') hc hc' (mem_pull.2 hb) (mem_pull.2 hb')
    rw [gm_pullChart L π₁ f z b b' hb hb'] at ew
    have hg : gm ((f ≫ π₂) ≫ β) z _ (M₀.g a a') = gm ((f ≫ π₁) ≫ β) z _ (M₀.g a a') := by
      simp only [Category.assoc, hβ]
    dsimp only
    rw [e₂, e₁, ew, hg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j₁, h₁⟩ := exists_chart hL (π₁ x)
      obtain ⟨j₂, h₂⟩ := exists_chart hL (π₂ x)
      obtain ⟨j₀, h₀⟩ := exists_chart hM (β (π₁ x))
      exact Opens.mem_iSup.2 ⟨(j₀, j₁, j₂), (hW _ x).2 ⟨h₀, h₁, h₂⟩⟩) u
    (fun t t' x hx => (hu _ (𝟙 B) x t hx.1).trans ((indep _ (𝟙 B) x t t' hx.1 hx.2).trans (hu _ (𝟙 B) x t' hx.2).symm))
  refine ⟨s, fun Z f z j₀ j₁ j₂ h₀ h₁ h₂ => ?_⟩
  have hz : f z ∈ W (j₀, j₁, j₂) := (hW _ _).2 ⟨h₀, h₁, h₂⟩
  exact (gm_res f z le_top hz s).symm.trans ((congrArg (gm f z _) (hs _)).trans (hu Z f z _ hz))

theorem exists_unit : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  intro A _ B' _ hB X Y L M₀ β wF π₁ π₂ w hL hM hwF hw hβ
  obtain ⟨s, hs⟩ := exists_glued L M₀ β wF π₁ π₂ w hL hM ((isGen_iff wF).1 hwF) ((isGen_iff w).1 hw) hβ
  have hbij := GlobalTheory.globalFns_holds _ B' hB
  let e := RingEquiv.ofBijective B'.hom.appTop.hom hbij
  let a : Γ(Sp A, ⊤)ˣ := Units.map e.symm.toMonoidHom s
  have ha : Units.map B'.hom.appTop.hom.toMonoidHom a = s := by
    ext
    exact e.apply_symm_apply _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a, ?_⟩
  intro p hp zz J J₀ hJ hJ₀
  have hua : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a) = a := by
    ext
    simp [unitOn]
  have k₁ := gm_pull p B'.hom zz ⊤ trivial a
  rw [hp] at k₁
  have key : gm p zz ⊤ s = gm (𝟙 _) zz ⊤ a := by
    rw [← ha]
    exact k₁
  have hs' := hs (Sp A) p zz (J₀ (p ≫ π₁ ≫ β)) (J (p ≫ π₁)) (J (p ≫ π₂)) (hJ₀ _) (hJ _) (hJ _)
  rw [hua, ← key, show p ≫ π₂ ≫ β = p ≫ π₁ ≫ β by rw [hβ], hs']
  exact (inv_mul_cancel_right _ _).symm

end GlobalTheory.PullAutConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.CorrCover

theorem exists_corr : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  intro Z M S₁ _ _ sM p₁ g J h1 h2 h3 hN h5 h6 hEC U₁ hU z₁ R _ _ ev hev ξ₁ hξ
  haveI := h1; haveI := h2; haveI := h3; haveI := h5; haveI := h6; haveI := hev
  set I := J.comap (p₁ ≫ g) with hIdef
  set x₁ := ξ₁ (closedPoint R)
  set ψ := (Scheme.stalkClosedPointTo ξ₁).hom
  obtain ⟨W, f₀, hx, -, hI⟩ := hEC x₁
  have st : ∀ k : ℕ, FinalTheorems.stalkId (I ^ k) x₁ = Ideal.span {(S₁.presheaf.germ _ x₁ hx).hom f₀ ^ k} := fun k => by
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ W x₁ hx, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI,
      Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  refine ⟨ψ ((S₁.presheaf.germ _ x₁ hx).hom f₀), ?_, ?_⟩
  · have := st 1
    rw [pow_one, pow_one] at this
    rw [idlAlong, this, Ideal.map_span, Set.image_singleton]
  intro D e
  obtain ⟨E, hE⟩ := EffCartierData.exists_idealSheaf_eq (CoverElements.effCartier_pow hEC D)
  obtain ⟨e', he'⟩ := _root_.GlobalTheory.ApproxCorr.exists_correction M S₁ sM p₁ hN U₁ hU E z₁ e
  refine ⟨e', fun f hf => ?_⟩
  have hm := he' f (fun V _ _ _ _ hc ξ' ev' hl hc' hr => by
    rw [hE, TorRef.idlAlong_pow]
    exact hf V hc ξ' ev' hl hc' hr)
  obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨u, hu, hψ⟩ := CoverElements.exists_stalk_of_map p₁ E.idealSheaf ξ₁ ev hξ hf₁
  rw [hE, st D] at hu
  obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.1 hu
  refine ⟨ψ h', ⟨h', rfl⟩, ?_⟩
  have hmR : (maximalIdeal (M.presheaf.stalk z₁)).map ev ≤ maximalIdeal R :=
    Ideal.map_le_iff_le_comap.2 fun x hx => (IsLocalRing.mem_maximalIdeal _).2 fun hu => hx (isUnit_of_map_unit ev x hu)
  have : ev r ∈ maximalIdeal R ^ e :=
    Ideal.pow_right_mono hmR e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ev hr)
  rw [map_add (f := _), ← hψ, map_mul, map_pow]
  convert this using 1
  exact add_sub_cancel_left _ _

end GlobalTheory.CorrCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmul
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

theorem exists_equiv_y_eq_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  intro R _ _ D₀ hB F _ _ n _ p
  constructor
  · rintro ⟨q, hq, hy⟩
    obtain ⟨z, hz, -⟩ := (GlobalTheory.TorusExt.equiv_iff hB p q).1 hq
    refine ⟨-z, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero, ← hz, hy]
  · rintro ⟨e, he⟩
    refine ⟨GlobalTheory.TorusExt.qkShift hB p (-e), GlobalTheory.TorusExt.equiv_qkShift hB p (-e), ?_⟩
    show p.y + n • (-e) = 0
    rw [he, smul_neg, add_neg_cancel]

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixGlue

theorem homFix_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  refine _root_.GlobalTheory.EndLoc.HomGlue.homFixRep_glue _root_.GlobalTheory.HomFixLocal.lbIso_pull_of_local S A B L M hA hB hL hM rA rB S.affineOpens (fun U => Sp Γ(S, U)) (fun U => U.2.fromSpec)
    (fun U => IsAffineOpen.isOpenImmersion_fromSpec U.2) ?_ ?_
  · intro s
    obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hU.range_fromSpec.ge hs⟩
  · intro U
    haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨A', _, _, φA, gA, hA', hL', rA', aA'⟩ := _root_.GlobalTheory.OpenRestrictPol.exists_restrict_open S A L hA hL rA aA _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨B', _, _, φB, gB, hB', hM', rB', aB'⟩ := _root_.GlobalTheory.OpenRestrictPol.exists_restrict_open S B M hB hM rB aB _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms Γ(S, U) A' B' (L.pull φA) (M.pull φB) hA' hB' hL' hM' rA' rB' aA' aB'
    exact ⟨A', B', _, _, φA, φB, R, gA, gB, h1, h2, h3⟩

end GlobalTheory.HomFixGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.IntPointFn

theorem comp_padd_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0)).left = b.left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero]
  simp only [padd, comp_one]
  show (b ≫ (𝟙 D.P.A * 1)).left = b.left
  rw [_root_.mul_one, Category.comp_id]

theorem comp_toUnit_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ D.c 0).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq, ← Category.assoc,
    toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem comp_toUnit_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, ← Category.assoc, toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

end GlobalTheory.IntPointFn

namespace GlobalTheory.IntPointFn

theorem fn_of_theta : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  intro V _ _ D θ b t ht ρ₀ hρ
  have hL := D.P.isLB
  have hu := mulGen_isGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀) ht (invGen_isGen _ _ _ _ hρ)
  have hF : FormEq (Sum.elim (fun k => b.left ≫ D.famφB 0 k)
      (Sum.elim ![(η[D.P.A]).left, b.left] (fun _ : PUnit => eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (DegPre.lineε 1) (fun _ : PUnit => -(1 : ℤ))))
      (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → ℤ) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
      Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
      comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    abel
  obtain ⟨s', hs'⟩ := exists_sec hL hF (pullMulSec (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) b.left
    (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀)) hu)
  have hle : (⊤ : (Sp V).Opens) ≤ LB.wchart D.P.L (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → D.P.L.ι) :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
    (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))), fun Z r z J hJ => ?_⟩
  have e1 := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ hu r z hJ)
  rw [val_mul hJ, val_inv,
    sval_of s' r z J (PEmpty.elim : PEmpty → D.P.L.ι) (fun k => k.elim)] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
      (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)))) =
      ((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)) := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have e3 := gs_res r z hle (by trivial) (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))
  rw [e2]
  erw [e3, e1]
  rw [Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel,
    Units.val_one, _root_.mul_one]

end GlobalTheory.IntPointFn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTriple
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBaseData

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  intro E _ _ _ H W _ _ _ t hp hA hK ⟨g, hg⟩ X _ _ _ _ x₀ hadd hlin
  letI := H.starRing
  let P := GlobalTheory.GenericPol.toPolAV t g hg hp hA hK
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ t.PP).1 t.sym
  have hψ0 : ∀ y : X, ∃ ψ : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (x₀ y)) (fun _ => -1)), ψ.IsGen :=
    fun y => ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := FractionRing W) P.L P.isLB _ _
  choose ψ hψ using hψ0
  let D₀ : DegPre W :=
    { P := P, rig := t.PP.rig, rig_gen := t.PP.rigGen, cub := t.cub, sym := sym, sym_gen := hsym, sym_rig := hsym',
      X := X, c := x₀, c_add := hadd, psi := ψ, psi_gen := hψ }
  letI : Module (𝓞 E) D₀.X := ‹Module (𝓞 E) X›
  haveI : Module.Projective (𝓞 E) D₀.X := GlobalTheory.PointStepCompare.projective_of_free E (X := X)
  haveI : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  have := t.act.hom H.w0
  let onB : D₀.P.OAct (𝓞 E) := ⟨t.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj t⟩
  obtain ⟨u, hu, hu0⟩ := GlobalTheory.ArcCM.CxFibre.exists_primGen t.PP (t.act.act H.w0) t.prim
  obtain ⟨ψ', hψ', oa, hoa, he, hb, hw, hU⟩ := GlobalTheory.UTau0.exists_symmetric_balanced_generator_psi_zero_localRing W D₀ (𝓞 E) onB hlin H.w0
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) ⟨u, hu, hu0⟩
  refine ⟨{ D₀ with psi := ψ', psi_gen := hψ' }, ‹Module (𝓞 E) X›, oa, 𝟙 _, LinearEquiv.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he
  · exact hb
  · exact hU
  · exact hw
  · refine ⟨GlobalTheory.PolDeg.Wit.grpPullback_id t.G, fun a => ?_, GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen t.PP.isLB⟩
    rw [hoa]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro y
    exact Category.comp_id _

end GlobalTheory.UBaseData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTranslatedBundleIntegralPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GenLocal

theorem exists_gen_unit_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen := by
  intro V _ _ _ D b
  choose i hi using fun k : Fin 2 =>
    exists_chart D.P.isLB ((![(η[D.P.A]).left, b.left] k) (closedPoint V))
  exact AbSquare.exists_gen_of_mem_chart D.P.isLB _ _ i fun k y => by
    have : (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k) = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
    exact (this.ge trivial : y ∈ (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k))

end GlobalTheory.GenLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatumStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gradedTateIso_lowerDatum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  first | exact @GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | exact GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | (intros; apply GlobalTheory.LowDat.GradedTate.exists_gradedTateIso <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (ξ : Sp V ⟶ S) (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left) (γ : GK.left ⟶ G.left), IsGrpPullback GK G₁ (jK V) φ → IsGrpPullback GK G (jK V ≫ ξ) γ → ∃ β : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ β ∧ φ ≫ β = γ ∧ ∀ (f₁ : G₁ ⟶ G₁) (f : G ⟶ G) (fK : GK ⟶ GK), fK.left ≫ φ = φ ≫ f₁.left → fK.left ≫ γ = γ ≫ f.left → f₁.left ≫ β = β ≫ f.left := by
  intro V _ _ _ hV G₁ _ _ hG₁ S G _ _ hG ξ GK _ φ γ hφ hγ
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  have hid : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨β, hβ, e⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 S) G G (𝟙 G.left) hG hid G₁ hG₁ ξ
    (jK V ≫ ξ) (Category.comp_id _) GK φ γ hφ hγ
  rw [Category.comp_id] at e
  refine ⟨β, hβ, e, fun f₁ f fK h₁ h₂ => ?_⟩
  have hj : GlobalTheory.IsGenericPointHom (S := Sp V) (ReciprocityTheory.ChartRestriction.G.Out.jK V) := .fractionField V (FractionRing V)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hφ.1.flip
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ φ ?_
  · rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hβ.1.w]
  · rw [← Category.assoc, ← h₁, Category.assoc, e, h₂, ← Category.assoc, e]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeBundleTrivialGeometricFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_bundle_trivial_geometric_fibre : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  first | (exact @GlobalTheory.HeckeFibre.fibre_triv) | (exact GlobalTheory.HeckeFibre.fibre_triv) | (intros; apply GlobalTheory.HeckeFibre.fibre_triv <;> assumption)
end

