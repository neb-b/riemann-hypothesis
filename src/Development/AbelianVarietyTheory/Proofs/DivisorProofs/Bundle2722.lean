module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0185
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAtHeightOneVerticalPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSectionExtendsNonzeroOfIntegralThetaConstan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmExt

theorem thList_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {x y : Sp K ⟶ S} (e : x = y) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) (H : ThList G L ρ m x θ pt c) : ∃ pt' : Fin N → (Over.mk y ⟶ G), ThList G L ρ m y (e ▸ θ) pt' c := by
  subst e; exact ⟨pt, H⟩

theorem inj_comp {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem exists_fracMap {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsFractionRing.lift (inj_comp φ hφ), RingHom.ext fun r => by
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩

theorem secAt_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R : Type} [CommRing R] {x : Sp R ⟶ S}
    {τ₁ τ₂ : SecAt G L x} (h : SecM.ofSec G τ₁ = SecM.ofSec G τ₂) : τ₁ = τ₂ :=
  ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val h) j

theorem cast_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {Z : Scheme.{0}} {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {y₁ y₂ : Z ⟶ S} (e : y₁ = y₂) (u₁ : Over.mk y₁ ⟶ T) (u₂ : Over.mk y₂ ⟶ T)
    (hu : u₁.left = u₂.left) :
    SecM.ofSec G (VVRank.pullS G _ u₂ σ) = SecM.ofSec G (e ▸ VVRank.pullS G _ u₁ σ) := by
  subst e
  obtain rfl : u₁ = u₂ := Over.OverMorphism.ext hu
  rfl

theorem pull_pull_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R V K K' : Type} [CommRing R]
    [CommRing V] [CommRing K] [CommRing K'] (χ : Sp R ⟶ S) (σ : SecAt G L χ) (φ : R →+* V) (a : R →+* K)
    (b : V →+* K') (φK : K →+* K') (h : spMap φK ≫ spMap a ≫ χ = spMap b ≫ spMap φ ≫ χ)
    (hc : φK.comp a = b.comp φ) :
    SecM.ofSec G (SecAt.pull G L (SecAt.pull G L σ φ) b) = SecM.ofSec G (h ▸ SecAt.pull G L (SecAt.pull G L σ a) φK) := by
  simp only [SecAt.pull]
  rw [ThetaRuleCompare.pullS_comp, ThetaRuleCompare.pullS_comp]
  refine cast_pullS G L σ h _ _ ?_
  simp only [Over.comp_left, Over.homMk_left]
  rw [← spMap_comp, ← spMap_comp, hc]

theorem secAt_eq_of_generic {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) {V : Type}
    [CommRing V] [IsDomain V] (x : Sp V ⟶ S) (τ₁ τ₂ : SecAt G L x)
    (h : SecAt.pull G L τ₁ (algebraMap V (FractionRing V)) = SecAt.pull G L τ₂ (algebraMap V (FractionRing V))) :
    τ₁ = τ₂ := by
  have hDom : IsDominant (spMap (algebraMap V (FractionRing V))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).trans_le bot_le)⟩
  have hSD : IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    (isSchemeTheoreticallyDominant_iff_isDominant _).2 hDom
  have hFl : Flat (fst (Over.mk x) G).left := inferInstanceAs (Flat (pullback.fst x G.hom))
  let ιK : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ Over.mk x :=
    Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
  have hP := ThetaRuleCompare.isPullback_whisker (A := G) ιK
  refine ThetaRuleCompare.sec_ext fun j => BundleExt.fn_ext_dense (spMap (algebraMap V (FractionRing V)))
    (fst (Over.mk x) G).left fun Z ρ r z hrz hz => ?_
  let ρ' : Z ⟶ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⊗ G).left := hP.lift ρ r hrz.symm
  have hfac : ρ' ≫ (ιK ▷ G).left = ρ := hP.lift_fst _ _ _
  have hz' : ρ' z ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x))).U j :=
    ThetaRuleCompare.chart_ge ιK j (show (ιK ▷ G).left (ρ' z) ∈ _ by rw [← Scheme.Hom.comp_apply, hfac]; exact hz)
  rw [← hfac, ← ThetaRuleCompare.gs_pullS ιK τ₁ ρ' z j hz', ← ThetaRuleCompare.gs_pullS ιK τ₂ ρ' z j hz']
  exact congrArg (fun u : SecAt G L (spMap (algebraMap V (FractionRing V)) ≫ x) => gs ρ' z _ (u.f j)) h

open GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace in
theorem mem_nonzeroLocus_of_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) (th : LB.Sec (LPow G L a T)) (z : (T' ⊗ G).left) (hz : z ∈ nonzeroLocus (VVRank.pullS G a h th)) :
    (h ▷ G).left z ∈ nonzeroLocus th := by
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ z).1 hz
  have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => a) th (h ▷ G).left
    (fun _ => whisker_snd_left G h) (𝟙 _) z j hj
  rw [Category.id_comp] at q
  have q' := q.trans (gs_stalkMap (h ▷ G).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left G h) j hj) _)
  refine (mem_nonzeroLocus _ _).2 ⟨j, wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T G).left) _
    (fun _ => whisker_snd_left G h) j hj, ?_⟩
  exact (isUnit_map_iff _ _).1 (q' ▸ u)

theorem spMap_closedPoint {R : Type} [CommRing R] (s : PrimeSpectrum R) {V : Type} [CommRing V] [IsLocalRing V]
    (φ₀ : Localization.AtPrime s.asIdeal →+* V) [IsLocalHom φ₀] :
    (spMap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal)))).base (IsLocalRing.closedPoint V) = s := by
  show PrimeSpectrum.comap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal))) (IsLocalRing.closedPoint V) = s
  rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint]
  ext1
  rw [PrimeSpectrum.comap_asIdeal]
  exact Localization.AtPrime.under_maximalIdeal

theorem om_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R (FractionRing R)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R (FractionRing R) (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ χ θ pt c hodd h3 hm hPol hT hunit
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (φK : FractionRing R →+* FractionRing V)
      (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ),
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ →
      ∃ σ : SecAt t.G t.PP.L (spMap φ ≫ χ), SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) =
        SecM.ofSec t.G (h ▸ SecAt.pull t.G t.PP.L θ φK) ∧ NZ t.G t.PP.L (spMap φ ≫ χ) σ := by
    intro V _ _ _ hV φ φK h hc
    obtain ⟨pt₁, -, hT₁⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N _ _ φK _ θ pt _ hT
    obtain ⟨pt₂, hT₂⟩ := thList_cast t.G t.PP.L t.PP.rig m h _ pt₁ _ hT₁
    have hPF : PolFib t.G t.PP.L g (spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
      (_root_.GlobalTheory.UMin.FibMove.polFib_move S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 _) t.PP.isLB t.PP.isLB (SiegLower.isGrpPullback_id _)
        (SiegLower.lbIso_pull_id t.PP.isLB) g (FractionRing R) _).2 _ φK hPol
    have hPF' : PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) := h ▸ hPF
    have hm' : IsUnit (m : V) := by simpa using hm.map φ
    have hcv : ∀ r, φK (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (φ r) :=
      fun r => congrArg (· r) hc
    have hPrim : Prim (algebraMap V (FractionRing V)) (fun a => φK (algebraMap R (FractionRing R) (c a))) := by
      obtain ⟨a, u, hu⟩ := hunit
      refine ⟨fun b => ?_, a, ?_, ?_⟩
      · dsimp only; rw [hcv]; exact RingHom.isIntegralElem_map _
      · dsimp only; rw [← hu]; exact ((u.isUnit.map (algebraMap R (FractionRing R))).map φK).ne_zero
      · dsimp only
        rw [← hu, hcv, show (algebraMap V (FractionRing V) (φ ↑u))⁻¹ = ((algebraMap V (FractionRing V)).comp φ) ↑u⁻¹ from
          (map_units_inv ((algebraMap V (FractionRing V)).comp φ) u).symm, RingHom.comp_apply]
        exact RingHom.isIntegralElem_map _
    exact _root_.GlobalTheory.UMin.exists_sec_nz_of_prim E H S t g m N V hV (spMap φ ≫ χ) (h ▸ SecAt.pull t.G t.PP.L θ φK) pt₂ _ hodd h3 hm' hPF' hT₂ hPrim
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.UMin.SecExtend.exists_sec_of_extends S t.G t.PP.L t.PP.isLB t.semi R χ θ
    (fun V _ _ _ hV φ φK h hc => (key V hV φ φK h hc).imp fun _ h' => h'.1)
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨p, hps⟩ : ∃ p : PrimeSpectrum R, (p : Sp R) = s := ⟨s, rfl⟩
  have hinjp : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : CharZero (Localization.AtPrime p.asIdeal) := charZero_of_injective_algebraMap hinjp
  obtain ⟨V, _, _, _, φ₀, hV, hinj, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (Localization.AtPrime p.asIdeal)
  obtain ⟨φ, hφdef⟩ : ∃ φ : R →+* V, φ = φ₀.comp (algebraMap R (Localization.AtPrime p.asIdeal)) := ⟨_, rfl⟩
  have hφ : Function.Injective φ := by
    rw [hφdef, RingHom.coe_comp]; exact hinj.comp hinjp
  obtain ⟨φK, hc⟩ := exists_fracMap φ hφ
  have h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hc]
  obtain ⟨σV, hσV, z, hz₁, hz₂⟩ := key V hV φ φK h hc
  have hθ : SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R)) = θ := secAt_ext t.G t.PP.L hσ
  have hFl : Flat t.G.hom := by haveI := t.semi.smooth; infer_instance
  have e₁ := pull_pull_cast t.G t.PP.L χ σ φ (algebraMap R (FractionRing R)) (algebraMap V (FractionRing V)) φK h hc
  rw [hθ] at e₁
  have heq : SecAt.pull t.G t.PP.L σ φ = σV :=
    secAt_eq_of_generic t.G t.PP.L _ _ _ (secAt_ext t.G t.PP.L (e₁.trans hσV.symm))
  subst heq
  refine ⟨((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ t.G).left z, ?_,
    mem_nonzeroLocus_of_pullS t.G _ _ σ z hz₂⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left, Scheme.Hom.comp_apply, hz₁]
  show (spMap φ) (IsLocalRing.closedPoint V) = s
  rw [← hps, hφdef]
  exact spMap_closedPoint p φ₀

end GlobalTheory.UMin.OmExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_sec_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)
    (g : Over.mk s ⟶ G) (x : Over.mk (𝟙 S) ⟶ G) :
    (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left = g.left ≫ (transl x).left := by
  have h2 : g ≫ (Over.homMk G.hom (by simp) : G ⟶ Over.mk (𝟙 S)) = Over.homMk s (by simp) := by
    ext; exact Over.w g
  rw [← Over.comp_left, transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, h2]

theorem irreducibleSpace_fibre_of_semiAbelian {S : Scheme.{0}} (G' : Over S) [GrpObj G'] (hG : IsSemiAbelian G')
    (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) : IrreducibleSpace (pullback G'.hom s : Scheme.{0}) := by
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have hc : ConnectedSpace (pullback G'.hom s : Scheme.{0}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) s _ _ (IsPullback.of_hasPullback G'.hom s)
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace Ω _ (pullback.snd G'.hom s) inferInstance hc

theorem range_one_subset_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (hπ : IsProper π)
    (G' : Over S) [GrpObj G'] (N : Near π G') :
    Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u := by
  have hW : IsOpen ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u) :=
    N.isOpen.isOpen_range.preimage (1 : Over.mk (𝟙 S) ⟶ G').left.continuous
  have hcl : IsClosed (π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ) :=
    π.isClosedMap _ hW.isClosed_compl
  have hover : ∀ z : S, G'.hom ((1 : Over.mk (𝟙 S) ⟶ G').left z) = z := fun z => by
    have := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
    change ((1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom) z = z
    rw [this]; rfl
  rintro _ ⟨z, rfl⟩
  by_contra hz
  have hmem : π z ∈ π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwc⟩ := (IsLocalRing.specializes_closedPoint (π z)).mem_closed hcl hmem
  apply hw
  apply N.all
  rw [hover]; exact hwc

theorem cover_by_translates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π hπ hs hS G' _ _ hG N hL
  obtain ⟨e, he, hPe⟩ := _root_.GlobalTheory.UnitDescent.unit_descends R hR S π hπ hs hS G' hG N hL (range_one_subset_near π hπ G' N)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  let Idx := {ax : (Sp R ⟶ N.U.left) × (Over.mk (𝟙 S) ⟶ G') // ax.1 ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ ax.1) ax.2.left}
  let V : Idx → Set G'.left := fun i => Set.range N.u ∪ (transl i.1.2).left ⁻¹' Set.range N.u
  have hopen : IsOpen (Set.range N.u) := N.isOpen.isOpen_range
  have hV : ∀ i, IsOpen (V i) := fun i => hopen.union (hopen.preimage (transl _).left.continuous)
  have hcov : Set.univ ⊆ ⋃ i, V i := by
    intro p _
    by_cases hp : p ∈ Set.range N.u
    · exact Set.mem_iUnion.2 ⟨⟨(e, 1), he, hPe⟩, Or.inl hp⟩
    · have hfp : (G'.left.fromSpecResidueField p) (closedPoint _) = p := G'.left.fromSpecResidueField_apply p _
      have hnc : closedPoint R ∉ Set.range (G'.left.fromSpecResidueField p ≫ G'.hom ≫ π) := by
        rintro ⟨y, hy⟩
        apply hp
        apply N.all
        rw [← hy, Subsingleton.elim y (closedPoint _)]
        change π (G'.hom p) = π (G'.hom ((G'.left.fromSpecResidueField p) _))
        rw [hfp]
      obtain ⟨a, x, ha, hPa, hr⟩ := _root_.GlobalTheory.MoveNear.exists_section_translate_mem R hR S π G' hG N e he hPe (G'.left.residueField p)
        (G'.left.fromSpecResidueField p ≫ G'.hom) (Over.homMk (G'.left.fromSpecResidueField p) rfl)
        (irreducibleSpace_fibre_of_semiAbelian G' hG _ _) (by simpa [Category.assoc] using hnc)
      rw [mul_sec_left_eq] at hr
      refine Set.mem_iUnion.2 ⟨⟨(a, x), ha, hPa⟩, Or.inr ?_⟩
      have := hr ⟨closedPoint _, rfl⟩
      change (transl x).left ((G'.left.fromSpecResidueField p) (closedPoint _)) ∈ _ at this
      rwa [hfp] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcov
  refine ⟨t.card, fun k => (t.equivFin.symm k).1.1.1, fun k => (t.equivFin.symm k).1.1.2,
    fun k => (t.equivFin.symm k).1.2, ?_⟩
  intro Ω _ s g
  have hpt : ∀ y : Sp Ω, y = closedPoint Ω := fun y => Subsingleton.elim _ _
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (g.left (closedPoint Ω))))
  rcases hi with hi | hi
  · left
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi
  · right
    refine ⟨t.equivFin ⟨i, hit⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [mul_sec_left_eq]
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforward
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finsum_weighted_regroup_along_fibres {A B : Type} (π : A → B) (m : A → ℤ) (n : B → ℤ) (d : A → ℕ) (g : A → ℝ) (h : B → ℝ)
    (P : B → Prop) (hm : (Function.support m).Finite) (hn : (Function.support n).Finite)
    (hP : ∀ z, n z ≠ 0 → P z) (hs : ∀ z, P z → ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = n z)
    (h₁ : ∀ w, m w ≠ 0 → P (π w) → g w = d w * h (π w)) (h₀ : ∀ w, m w ≠ 0 → ¬ P (π w) → g w = 0) :
    ∑ᶠ w, (m w : ℝ) * g w = ∑ᶠ z, (n z : ℝ) * h z := by
  classical
  set S := hm.toFinset with hS
  set T := hn.toFinset ∪ S.image π with hT
  have hmS : ∀ w, m w ≠ 0 ↔ w ∈ S := fun w => by simp [hS]
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun w hw => by
      have : m w ≠ 0 := fun h0 => hw (by simp [h0])
      exact Finset.mem_coe.2 ((hmS w).1 this)),
    finsum_eq_sum_of_support_subset (s := T) _ (fun z hz => by
      have : n z ≠ 0 := fun h0 => hz (by simp [h0])
      simp [hT, this]),
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := π) (fun w hw => by
      simp only [hT, Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hw))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z
  · have e : ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = ∑ w ∈ S.filter (fun w => π w = z), m w * (d w : ℤ) := by
      refine finsum_mem_eq_sum_of_inter_support_eq (s := {w | π w = z}) _ ?_
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hmS w).1 (left_ne_zero_of_mul h2), h1⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.2, h2⟩
    rw [← hs z hz, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₁ w ((hmS w).2 hw') hz, mul_assoc]
  · have e : n z = 0 := by
      by_contra h'
      exact hz (hP z h')
    rw [e, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₀ w ((hmS w).2 hw') hz, mul_zero]

theorem finsum_cycInt_push : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  intro F _ X Y _ _ _ _ p q σ e hp hX hq hY π hπ _ Δ Δ' hΔ L f hf
  have hc : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → CompactSpace Z := by
    rintro Z _ ⟨m, i, hi, rfl⟩
    have := isProper_str F m
    have : IsProper (i ≫ PSpace.str F m) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str F m)
  haveI := hc hp
  haveI := hc hq
  have key := fun (w : Y) (hw : Δ'.mult w ≠ 0) => _root_.GlobalTheory.CycPush.cycInt_pull F X Y p q σ hp hq π hπ e L f hf w
    ((_root_.GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F Y q e hq hY w).1 (CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ') hw))
  exact finsum_weighted_regroup_along_fibres π Δ'.mult Δ.mult (fun w => π.residueDegree w) _ _ (fun z => Order.coheight z = 1)
    Δ'.finite_support_mult Δ.finite_support_mult
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ) hz) hΔ
    (fun w hw h => (key w hw).1 ((_root_.GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hp hX _).1 h))
    (fun w hw h => (key w hw).2 fun h' => h ((_root_.GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hp hX _).2 h'))

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProd
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pt_bsL_fb {n d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) : pt ε (bsL ε w) (fb ε w) = w := by
  ext a
  obtain ⟨x, rfl⟩ := ε.symm.surjective a
  rcases x with b | j <;> simp [pt, bsL_apply, fb]

theorem cellMap_image_eq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε
  have hO := _root_.GlobalTheory.FlagCell2.isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u
  have hP := _root_.GlobalTheory.FlagCell2.cell_points_existsUnique F X Y ι m E E' φ f hR A u hgen
  have hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j,
      ratVal (u j) y = (ratOf Y).val y.1 (u j) :=
    fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))
  refine ⟨?_, ?_, ?_⟩
  · let W : Y.X.Opens := ⟨{y | InCell E E' φ f A u y}, hO.1⟩
    have e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source := by
      ext y
      simp only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]
      rfl
    rw [e]
    exact (isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))
  · intro y hy y' hy' h
    have h1 := congrArg (bsL ε) h
    have h2 := congrArg (fb ε) h
    simp only [cellMap, bsL_pt, fb_pt] at h1 h2
    have hx : ptMap σ f hf y = ptMap σ f hf y' := c.e.injOn hy.2 hy'.2 h1
    have hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ)) := hy.1.1
    apply Subtype.ext
    exact (hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique
      ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩
      ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩
  · intro S hS hA
    ext w
    constructor
    · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
      exact ⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩
    · rintro ⟨x, hxS, hxw⟩
      obtain ⟨p, ⟨hpf, hpc, hpv⟩, -⟩ := hP ℂ x.1 (hA x hxS) (fb ε w)
      have hps : p ≫ Y.str = spMap σ := by rw [← hf, ← Category.assoc, hpf, x.2]
      let y : CxPts Y.str σ := ⟨p, hps⟩
      have hyx : ptMap σ f hf y = x := Subtype.ext hpf
      refine ⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩
      have hv : (fun j => ratVal (u j) y) = fb ε w := funext fun j => (hval y hpc j).trans (hpv j)
      simp only [cellMap, hyx, hxw, hv]
      exact pt_bsL_fb ε w

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAtHeightOneVerticalPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_at_height_one_vertical_point : ∀ (σ : Setup) (p : Sp σ.R) (z : (σ.C p).G.left), p.asIdeal.height = 1 → Vert (σ.C p).G.hom (σ.ρ p σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C p).G.hom) (maximalIdeal (σ.C p).R) (σ.θ p) (σ.W p) (regSet z) := by
  first | exact @GlobalTheory.Desc.gaussAt_chart_of_height_one | exact GlobalTheory.Desc.gaussAt_chart_of_height_one | (intros; apply GlobalTheory.Desc.gaussAt_chart_of_height_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCoefficientsCongruenceScaled
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coefficients_congruence_scaled : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ v : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 g₂ : 𝟙_ (Over S) ⟶ G2 o.A)) v → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom) | (exact GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom <;> assumption)
end

