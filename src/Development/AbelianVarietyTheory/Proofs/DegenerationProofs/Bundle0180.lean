module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcClause

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_lift (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : V →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap V.subtype := by
    rw [Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F, PrimeSpectrum.comap g default = PrimeSpectrum.comap V.subtype q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact Subtype.ext h1
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap V.subtype = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap V.subtype) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap V.subtype)).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap V.subtype)) (default : PrimeSpectrum K) = z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

theorem not_mem_generic {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (f : R →+* R') {r : R} (hr : f r ≠ 0)
    (p : PrimeSpectrum (FractionRing R')) : r ∉ ((jK R' ≫ spMap f) p).asIdeal := by
  intro h
  have h1 : algebraMap R' (FractionRing R') (f r) ∈ PrimeSpectrum.asIdeal p := h
  rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal p)] at h1
  exact hr (IsFractionRing.injective R' (FractionRing R') (h1.trans (map_zero _).symm))

theorem arc_clause : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hX hF E _ _ _ H D l Xo c W₀ Y p hN hA O' _ _ _ b ϖ a hB
  obtain ⟨m, Z, π, t, mt, hodd, hunit, hfin, hsurj, hAF⟩ := hA
  have hm : IsUnit (m : O') := by simpa using hunit.map b
  obtain ⟨R₁, _, _, g, y₁, hg, hgf, hR, hTD, hθ, hf⟩ := hF E H D l Xo c W₀ Y O' b ϖ a hB m hodd hm
  let gam : FractionRing (PowerSeries O') →+* FractionRing R₁ :=
    IsFractionRing.lift (g := (algebraMap R₁ (FractionRing R₁)).comp g) ((IsFractionRing.injective R₁ _).comp hg)
  have hgam : ∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r) := fun r =>
    IsFractionRing.lift_algebraMap _ r
  obtain ⟨y, hy, hTy⟩ := _root_.GlobalTheory.ArcPointDescent.point_descends h1 h2 h3 h4 h5 h6 E H D l Xo c W₀ Y O' b a ϖ hB R₁ g y₁ gam hgam hgf hR hTD
  have hys : y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have := hTy.1
    rwa [show spMap (RingHom.id (PowerSeries O')) = 𝟙 _ from Spec.map_id _, Category.id_comp] at this
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.arc_generic_point_extends_powerSeries h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB m Z π t mt hfin hsurj hAF R₁ g y₁ gam hgam hgf hR
    y hy hys hθ hf
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB y χ hχ hTy
  have c4 := GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData h1 h2 h3 h4 h5 h6 hE hU hP hX E H D l Xo c W₀ Y O' b a ϖ hB hN.2.2.1 y χ hχ hTy
  have hϖ : ϖ ≠ 0 := by
    rcases hB with ⟨-, rfl⟩ | ⟨-, h, -⟩
    exacts [one_ne_zero, h.ne_zero]
  refine ⟨χ, fun χ' => ⟨fun h => h ▸ ⟨c1, c2, c3, c4⟩, fun ⟨d1, _, d3, d4⟩ => ?_⟩, fun hirr y' ev hs hr hd hC hXv => ?_⟩
  · have hpid : IsPrincipalIdealRing O' ∧ IsLocalRing O' := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · letI := h.toField
        exact ⟨inferInstance, inferInstance⟩
      · exact ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hpid
    have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (f := PowerSeries.C (R := O')) PowerSeries.C_injective
    obtain ⟨y', hy'⟩ := exists_lift (c.V W₀) Y (jK (PowerSeries O') ≫ χ') (by
      rintro _ ⟨q, rfl⟩
      refine d3 _ ?_
      have := not_mem_generic (RingHom.id (PowerSeries O')) (r := PowerSeries.C ϖ * PowerSeries.X)
        (mul_ne_zero (fun h => hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero) q
      exact this)
    exact _root_.GlobalTheory.ArcUnique.eq_of_hasArcData h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a (PowerSeries O') (Ideal.span {PowerSeries.X})
      (PowerSeries.C (R := O')) PowerSeries.X ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
      (fun h => PowerSeries.X_prime.not_unit (Ideal.span_singleton_eq_top.1 h)) PowerSeries.C_injective
      χ' χ y' y hy' hχ.symm d1 c1 d4 c4
  · rcases hB with ⟨-, rfl⟩ | ⟨hdvr, -, hc⟩
    · exact absurd isUnit_one hirr.not_isUnit
    have hc' : IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
      rwa [hirr.maximalIdeal_eq]
    have hrg : Set.range (jK O' ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
      rintro _ ⟨q, rfl⟩
      refine c3 _ ?_
      have := not_mem_generic ev (r := PowerSeries.C ϖ * PowerSeries.X)
        (by rw [map_mul, hC, hXv]; exact mul_ne_zero hϖ hϖ) q
      exact this
    have c5 := GlobalTheory.T.arcData_specialise_at_uniformiser h1 h2 hT h4.unifBaseChange h5 E H D l Xo c _ _ Y O' b ϖ a hirr hc' ev hC hXv χ c1 hrg c4
    obtain ⟨z, hz⟩ := exists_lift (c.V W₀) Y _ hrg
    obtain ⟨z', hz'⟩ := exists_lift (c.V W₀) Y _ hr
    have hid : spMap (RingHom.id O') = 𝟙 _ := Spec.map_id _
    have hev : spMap ev ≫ spMap (PowerSeries.C (R := O')) = spMap (RingHom.id O') := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact hC x
    refine _root_.GlobalTheory.ArcUnique.eq_of_hasArcData h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a O' (Ideal.span {ϖ}) (RingHom.id O') ϖ
      ⟨inferInstance, inferInstance, inferInstance, hc⟩
      (fun h => hirr.not_isUnit (Ideal.span_singleton_eq_top.1 h)) Function.injective_id
      _ y' z z' hz hz' ?_ ?_ c5 hd
    · rw [Category.assoc, c1, ← Category.assoc, hev]
    · rw [hid, Category.id_comp, hs]

end GlobalTheory.LN.ArcClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompatibleLineBundlesFormalThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalAlgebraise

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = ⊥ := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)


open GlobalTheory.AbLaw in
theorem algebraisation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) → (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro _ _ R _ _ _ _ I hI hc _ Y β N v hβ hY hN hA
  have isLB_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hfl : ∀ e, Flat (Y e).hom := fun e => by have := hY e; infer_instance
  have hamp : ∀ e, RelAmple (Y e) (N e) := by
    intro e
    induction e with
    | zero => exact hA
    | succ e ih =>
      have := hY (e + 1)
      exact _root_.GlobalTheory.AmpleThickening.relAmple_of_sq_zero _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) (Y (e + 1)) (Y e) (β e)
        (hβ e) inferInstance _ _ (hN _).1 (hN _).1 ⟨v e, (hN e).2⟩ ih
  have hproj : ∀ e, AbLaw.IsProjBy (Y e).hom := fun e => by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ (Y e) (N e) (hN e).1).1 (hamp e)
    exact ⟨_, isLB_pw (hN e).1 _, n, s, hs⟩
  have hle : I ^ (0 + 1) ≤ IsLocalRing.maximalIdeal R := by
    rw [zero_add, pow_one]
    exact IsLocalRing.le_maximalIdeal hI
  let g₀ : R ⧸ I ^ (0 + 1) →+* IsLocalRing.ResidueField R := Ideal.Quotient.factor hle
  have hg₀ : Function.Surjective g₀ := Ideal.Quotient.factor_surjective hle
  have hpb := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := _root_.GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull _ (Y 0) (N 0) (hN 0).1 hA _ g₀ _ _ _ hpb
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [GlobalTheory.Algebraise.pw_pull]
    exact GlobalTheory.Algebraise.lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  have hL := LB.isLB_pull (hN' 0).1 (pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)))
  choose s hs using fun j => _root_.GlobalTheory.SecLifts.exists_compatible_sections_local R I hI Y β hβ hfl hproj
    (fun e => AbLaw.pw (N e) d) v' hN' _ g₀ hg₀ _ _ _ hpb _ _ hL (CubePf.idIsoL_isGen hL) h0 (s₀ j)
  have hva : AbLaw.VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext (fun j => (hs j).1)
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, -, -⟩ := _root_.GlobalTheory.Degen.exists_projective_of_formal_embedding_local R I hI hc Y β hβ hfl
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => (hs j).2 e) hva
  have hP : AbLaw.IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have hS : Smooth B.hom := _root_.GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings R I hI B (AbLaw.isProper_of_isProjBy R B.left B.hom hP) Y b hb hY
  have hF : Flat B.hom := inferInstance
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlgLocal.exists_lineBundle_of_thickenings R I hI hc Y β hβ B b hP hF hb hbβ N v hN
  haveI : Nontrivial (R ⧸ I ^ (0 + 1)) := g₀.domain_nontrivial
  exact ⟨B, M, b, hP, hS, hM, _root_.GlobalTheory.AmpleLocalBase.relAmple_of_closed R B M hF hP hM _ _ Ideal.Quotient.mk_surjective (Y 0) (b 0) (hb 0)
    (N 0) (hN 0).1 (hNM 0) hA, hb, hbβ, hNM⟩

end GlobalTheory.FormalAlgebraise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfMemKL
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CyclicDescent

open ThetaSplit

section Bundles

variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_gen_scale {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (b : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J * gm r z ⊤ b := by
  refine ⟨⟨fun i => t.s i * res le_top b⟩, ?_, ?_⟩
  · unfold LB.Gen.IsGen at ht ⊢
    intro i j
    simp only [map_mul, LB.res_res]
    rw [ht i j]
    exact mul_assoc _ _ _
  · intro Z r z J hJ
    refine (map_mul (gm r z _) _ _).trans ?_
    congr 1
    exact gm_res r z _ (hJ.mem φ r) b

theorem exists_gen_iterate (hL : L.IsLB) (τ : ℕ → (X ⟶ X)) (h0 : τ 0 = 𝟙 X) (hτ : ∀ i, τ (i + 1) = τ i ≫ τ 1)
    (v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ 1] ![1, -1])) (hv : v.IsGen) (j : ℕ) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ j] ![1, -1]), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val w r z J = ∏ i ∈ Finset.range j, val v (r ≫ τ i) z J := by
  induction j with
  | zero =>
    have hF : FormEq (PEmpty.elim : PEmpty → (X ⟶ X)) PEmpty.elim ![𝟙 X, τ 0] ![(1 : ℤ), -1] := by
      intro U _ h
      simp [Fin.prod_univ_two, h0]
    obtain ⟨w, hw, hw'⟩ := exists_gen hL hF (LB.oneGen L (Y := X)) (LB.isGen_oneGen L)
    refine ⟨w, hw, fun Z r z J hJ => ?_⟩
    rw [hw' Z r z J hJ, val_one]
    simp
  | succ j ih =>
    obtain ⟨w, hw, hw'⟩ := ih
    have hp := LB.isGen_pullGen L _ _ v hv (τ j)
    have hm := LB.isGen_mulGen L ![𝟙 X, τ j] ![1, -1] (fun k => τ j ≫ ![𝟙 X, τ 1] k) ![1, -1] w
      (L.pullGen ![𝟙 X, τ 1] ![1, -1] v (τ j)) hw hp
    have hF : FormEq (Sum.elim ![𝟙 X, τ j] (fun k => τ j ≫ ![𝟙 X, τ 1] k)) (Sum.elim ![(1 : ℤ), -1] ![1, -1])
        ![𝟙 X, τ (j + 1)] ![(1 : ℤ), -1] := by
      intro U _ h
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Category.comp_id, ← hτ]
      group
    obtain ⟨w', hw'', hv'⟩ := exists_gen hL hF _ hm
    refine ⟨w', hw'', fun Z r z J hJ => ?_⟩
    rw [hv' Z r z J hJ, val_mul hJ, val_pull hJ, hw' Z r z J hJ, Finset.prod_range_succ]

end Bundles

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem exists_gen_of_memKL {L : LB A.left} (hL : L.IsLB) [Subsingleton S] [Nonempty S]
    {x : 𝟙_ (Over S) ⟶ A} (hx : MemKL A L x) :
    ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl x] ![1, -1]), v.IsGen := by
  obtain ⟨p⟩ := ‹Nonempty S›
  obtain ⟨V, hpV, c, hc⟩ := hx p
  have : Subsingleton ↥(𝟙_ (Over S)).left := ‹Subsingleton ↥S›
  have hW : ∀ y, y ∈ (fst (𝟙_ (Over S)) A).left ⁻¹ᵁ V := fun y => by
    show (fst (𝟙_ (Over S)) A).left y ∈ V
    rwa [Subsingleton.elim ((fst (𝟙_ (Over S)) A).left y) p]
  obtain ⟨t, ht⟩ := GlobalTheory.TwistTranslate.gen_of_pull_top hL _ hW c hc
  have h1 := LB.isGen_invGen L _ _ (LB.pullGen L _ _ t (lift (toUnit A) (𝟙 A)).left)
    (LB.isGen_pullGen L _ _ t ht (lift (toUnit A) (𝟙 A)).left)
  have ea : (lift (toUnit A) (𝟙 A)).left ≫ (lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left =
      ThetaSplit.transl x := by
    rw [← Over.comp_left]
    congr 1
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
    rfl
  have eb : (lift (toUnit A) (𝟙 A)).left ≫ (snd (𝟙_ (Over S)) A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd]
    rfl
  have hF : FormEq (fun k => (lift (toUnit A) (𝟙 A)).left ≫
      ![(lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left, (snd (𝟙_ (Over S)) A).left] k)
      (fun k => -![(1 : ℤ), -1] k) ![𝟙 A.left, ThetaSplit.transl x] ![(1 : ℤ), -1] := by
    intro U _ h
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ea, eb]
    simp [mul_comm]
  obtain ⟨v, hv, -⟩ := exists_gen hL hF _ h1
  exact ⟨v, hv⟩

theorem exists_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB)
    [Subsingleton S] [Nonempty S] (hU : ∀ n : ℕ, 0 < n → ∀ y : Γ(S, ⊤)ˣ, ∃ x : Γ(S, ⊤)ˣ, x ^ n = y)
    {x : 𝟙_ (Over S) ⟶ A} (hx : MemKL A L x)
    {C : Type} [CommGroup C] (i : C →* (𝟙_ (Over S) ⟶ A)) (hi : ∀ c, ∃ j : ℕ, x ^ j = i c) :
    ∃ u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
        (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (ThetaSplit.transl (i c)))) := by
  have : IsCommMonObj A := hA.comm
  have e1 : toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A) = 1 := comp_one (toUnit A)
  have h0 : ThetaSplit.transl (x ^ 0) = 𝟙 A.left := by
    rw [pow_zero]
    show ((toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A)) * 𝟙 A).left = 𝟙 A.left
    rw [e1, _root_.one_mul (𝟙 A : A ⟶ A)]
    rfl
  have hτ : ∀ m : ℕ, ThetaSplit.transl (x ^ (m + 1)) = ThetaSplit.transl (x ^ m) ≫ ThetaSplit.transl (x ^ 1) := by
    intro m
    rw [pow_succ, pow_one, ThetaSplit.transl_mul]
  obtain ⟨v, hv⟩ : ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (x ^ 1)] ![1, -1]),
      v.IsGen := by
    rw [pow_one]
    exact exists_gen_of_memKL hL hx
  choose j hj using hi
  have hw : ∀ c, ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val w r z J = ∏ m ∈ Finset.range (j c), val v (r ≫ ThetaSplit.transl (x ^ m)) z J := by
    intro c
    rw [← hj c]
    exact exists_gen_iterate hL (fun m => ThetaSplit.transl (x ^ m)) h0 hτ v hv (j c)
  choose w hwg hwv using hw
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (a m : ℕ),
      (r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m) = r ≫ ThetaSplit.transl (x ^ (a + m)) := by
    intro Z r a m
    rw [pow_add, ThetaSplit.transl_mul, Category.assoc]
  have hc : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
      val (w c) r z J * val (w c') (r ≫ ThetaSplit.transl (i c)) z J =
        val (w c') r z J * val (w c) (r ≫ ThetaSplit.transl (i c')) z J := by
    intro c c' Z r z J hJ
    have hs : ∀ a b, ∏ m ∈ Finset.range (a + b), val v (r ≫ ThetaSplit.transl (x ^ m)) z J =
        (∏ m ∈ Finset.range a, val v (r ≫ ThetaSplit.transl (x ^ m)) z J) *
          ∏ m ∈ Finset.range b, val v ((r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m)) z J := by
      intro a b
      rw [Finset.prod_range_add]
      simp only [key]
    rw [hwv c Z r z J hJ, hwv c' Z r z J hJ, hwv c' Z _ z J hJ, hwv c Z _ z J hJ, ← hj c, ← hj c', ← hs, ← hs,
      add_comm]
  obtain ⟨b, hb⟩ := ThetaSplit.exists_rescale hL A.hom η[A].left (Over.w η[A]) (hG S A hA).2 hU
    (fun c => ThetaSplit.transl (i c)) (fun c c' => by simp only [map_mul, ThetaSplit.transl_mul])
    (fun c => ThetaSplit.transl_hom (i c)) 1 w hwg hc
  have gmtop_lemma : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (z : Z) (c : Γ(S, ⊤)ˣ),
      gm r z ⊤ (Units.map A.hom.appTop.hom c) = gm (r ≫ A.hom) z ⊤ c := by
    intro Z r z c
    unfold gm
    rw [dite_eq_left (show r z ∈ (⊤ : A.left.Opens) from trivial),
      dite_eq_left (show (r ≫ A.hom) z ∈ (⊤ : S.Opens) from trivial)]
    ext
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, pullU]
    rfl
  have hu : ∀ c, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val u r z J = val (w c) r z J * gm (r ≫ A.hom) z ⊤ (b c) := by
    intro c
    obtain ⟨u, hu, hsc⟩ := exists_gen_scale (w c) (hwg c) (Units.map A.hom.appTop.hom (b c))
    refine ⟨u, hu, fun Z r z J hJ => ?_⟩
    rw [hsc Z r z J hJ, gmtop_lemma]
  choose u hug huv using hu
  refine ⟨u, hug, fun c c' => corr_of_val hL (fun y J hJ => ?_)⟩
  rw [val_mul hJ, val_pull hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, Category.assoc,
    ThetaSplit.transl_hom]
  exact hb c c' _ (𝟙 _) y J hJ

end Group

theorem exists_descent : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (x : (𝟙_ (Over (Sp k)) ⟶ A)) (n : ℕ), 1 ≤ n → orderOf x = n → GlobalTheory.MemKL A L x → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (y : Over.mk t ⟶ A), y ≫ ψ = 1 ↔ ∃ c ∈ Subgroup.zpowers x, y = toUnit _ ≫ c) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) := by
  intro k _ _ A B _ _ hA L hL x n hn hord hx ψ hψ _ _ _ hker
  have : IsCommMonObj A := hA.comm
  have hfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hord]
    omega
  have : Finite (Subgroup.zpowers x) := by
    exact finite_zpowers.mpr hfin
  have hi : ∀ c : Subgroup.zpowers x, ∃ j : ℕ, x ^ j = (Subgroup.zpowers x).subtype c := fun c =>
    (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr c.2)
  obtain ⟨u, hu, hcoc⟩ := exists_cocycle globalFns_holds hA hL (ThetaSplit.units_divisible k) hx
    (Subgroup.zpowers x).subtype hi
  refine GlobalTheory.LinDescent.exists_descent_of_isReduced (Sp k) A B ψ (Subgroup.zpowers x) (Subgroup.zpowers x).subtype
    L hL hψ ‹_› ‹_› ‹_› ?_ u hu hcoc
  intro k' _ _ t
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · rw [hker k' t y]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, rfl⟩
  · have e : (toUnit (Over.mk t)).left = t := by simp
    have : Epi (toUnit (Over.mk t)).left := e ▸ ThetaSplit.epi_of_fields t
    have : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
    have hc' : toUnit (Over.mk t) ≫ (c : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := hc
    apply Subtype.ext
    apply (cancel_epi (toUnit (Over.mk t))).mp
    rw [hc', Subgroup.coe_one, comp_one]

end GlobalTheory.CyclicDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_coords_relabelled_twistedData_series : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  first | exact @GlobalTheory.RelabelCoords.theta_coord | exact GlobalTheory.RelabelCoords.theta_coord | (intros; apply GlobalTheory.RelabelCoords.theta_coord <;> assumption)
end

