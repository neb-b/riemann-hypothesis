module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCovSep.LocalSpread

open GlobalTheory.Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_chart (C : UCompact Xo c) {o₁ Ω : Type} [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [CharZero Ω]
    (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c) (hπ : M.pt ≫ π = uη ≫ C.i) (w : M.Z)
    (hw : π w ∈ Set.range C.i) :
    ∃ (U₀ : M.Z.Opens) (u₀ : Sp (ratHull (M.ringOn U₀)) ⟶ Xo.XF c), w ∈ U₀ ∧
      spMap (ratHull (M.ringOn U₀)).val.toRingHom ≫ u₀ = uη := by
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ π ⁻¹ᵁ ⟨V, hVo⟩ := by
    obtain ⟨x, hx⟩ := hw
    show π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) hwV
  have hne : ((U : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwU⟩
  let R₀ := M.ringOn U
  let φ : Γ(M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := ChartAt.exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : c.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o c.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o c.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hwU, ?_⟩
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap M.pt U hpt := by
    ext a
    show ((M.sectionsEquiv U hne a : M.ringOn U) : Ω) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  haveI := C.isPreimmersion_i
  rw [← cancel_mono C.i, ← hπ, Category.assoc, UCompact.i, ← Category.assoc (IsOpenImmersion.lift _ _ _),
    IsOpenImmersion.lift_fac, pullback.lift_fst]
  show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ π = _
  rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf]

theorem isUnit_intCast (C : UCompact Xo c) {o₁ Ω : Type} [CommRing o₁] [Field Ω] [Algebra o₁ Ω]
    (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (w : M.Z) (hw : π w ∈ Set.range C.i) (n : ℤ) (hn : n ≠ 0) :
    IsUnit (n : M.O w) := by
  obtain ⟨x, hx⟩ := hw
  rw [← map_intCast (M.stalkEquiv w) n, MulEquiv.isUnit_map, LocSpread.isUnit_intCast_stalk_iff π, ← hx,
    ← LocSpread.isUnit_intCast_stalk_iff C.i,
    LocSpread.isUnit_intCast_stalk_iff (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F)]
  have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  have h' := (h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
    ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) x) trivial).hom
  rwa [map_intCast, map_intCast] at h'

theorem exists_uAct {R R' Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R']
    [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] {σ : R →+* R'} (τ : R' →+* Ω) (hτ : Function.Injective τ)
    (e : τ.comp σ = algebraMap R Ω) {P : PolAV (Sp R)} {u : Sp R' ⟶ Xo.XF c} (h : UOver Xo c P σ u) :
    ∃ act : 𝓞 E → (P.A ⟶ P.A), (∀ a, IsMonHom (act a)) ∧ UAct Xo c P act σ u := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have e' : spMap τ ≫ spMap σ = spMap (algebraMap R Ω) := by rw [← Spec.map_comp, ← e]; rfl
  have hG := isGrpPullback_pullback G (spMap τ)
  have hGP := (hG.comp hα).congr e' rfl
  have hs : IsSemiAbelian P.A := by
    have := P.isAb.proper
    refine ⟨P.isAb.comm, P.isAb.smooth, inferInstance, inferInstance, P.isAb.geomConnected, ?_⟩
    intro K _ _ p
    have hab : IsAbelianScheme ((Over.pullback p).obj P.A) := by
      have := P.isAb.comm
      have := P.isAb.smooth
      have := P.isAb.proper
      have := P.isAb.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd P.A.hom p); infer_instance
      · change IsProper (pullback.snd P.A.hom p); infer_instance
      · change GeometricallyConnected (pullback.snd P.A.hom p); infer_instance
    refine ⟨{ X := PUnit
              B := _
              isAbelian := hab
              q := 𝟙 _
              q_hom := inferInstance
              q_flat := ?_
              q_surjective := ?_
              q_quasiCompact := ?_
              i := toUnit _ ≫ η
              i_hom := ?_
              isKernel := ?_ }⟩
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · have := hab.comm; infer_instance
    · have : IsIso (toUnit (splitTorus (Sp K) PUnit)) := by
        have h : 𝟙 (splitTorus (Sp K) PUnit) = 1 := by
          rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
          congr 1
        exact ⟨η, h.symm, toUnit_unique _ _⟩
      exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  haveI := P.isAb.proper
  haveI : Smooth G.hom := MorphismProperty.of_isPullback (P := @Smooth) hα.1 P.isAb.smooth
  haveI : IsSchemeTheoreticallyDominant (spMap τ) := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hτ
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap τ)) := .of_isPullback hG.1.flip
  have key : ∀ a : 𝓞 E, ∃ F : P.A ⟶ P.A, IsMonHom F ∧ ∃ f : G ⟶ G, f.left ≫ α = α ≫ F.left ∧
      f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left := fun a => by
    have w : (β ≫ (Xo.univ.t.act.act (H.bar a)).left) ≫ Xo.univ.t.G.hom = G.hom ≫ u ≫ pullback.fst _ _ := by
      rw [Category.assoc, Over.w, hβ.1.w]
    let f : G ⟶ G := Over.homMk (hβ.1.lift _ _ w) (hβ.1.lift_snd _ _ w)
    have hf : f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left := hβ.1.lift_fst _ _ w
    haveI := Xo.univ.t.act.hom (H.bar a)
    haveI : IsMonHom f := GlobalTheory.SharpPull.isMonHom_lift hβ hβ hf
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField_of_isGrpPullback hs hs hGP hGP
      ((Over.pullback (spMap τ)).map f)
    refine ⟨F, hF, f, ExtUnique.hom_ext_of_dominant P.A.hom ?_ (pullback.fst G.hom (spMap τ)) ?_, hf⟩
    · rw [Category.assoc, Category.assoc, Over.w, hα.1.w, Over.w_assoc]
    · rw [← Category.assoc, ← ExtUnique.pullback_map_left_fst, Category.assoc]
      exact hF'.trans (Category.assoc _ _ _)
  choose act h₁ h₂ using key
  exact ⟨act, h₁, G, _, α, β, hα, hβ, hL, h₂⟩

theorem exists_local_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (o₁ Ω : Type) [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [ArithBase o₁ Ω] (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c), GlobalTheory.IsNormalScheme M.Z → M.pt ≫ π = uη ≫ C.i → ∀ (A₁ : PolAV (Sp Ω)) (m : ℕ) (ze : o₁ˣ), IsUnit (m : o₁) → UOver Xo c A₁ (RingHom.id Ω) uη → Out.Level A₁ m (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) → ∀ (K : Type) [Field K] (yM : Sp K ⟶ M.Z) (y : Sp K ⟶ Xo.XF c), yM ≫ π = y ≫ C.i → ∃ (R : Subalgebra o₁ Ω) (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c) (𝔭 : Ideal R), R.FG ∧ (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ P.g = A₁.g ∧ HypS P.A P.L ∧ Nonempty (Out.Level P m (unitOn (Units.map (algebraMap o₁ R).toMonoidHom ze))) ∧ (∀ a, IsMonHom (act a)) ∧ GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u ∧ spMap (ratHull R).val.toRingHom ≫ u = uη ∧ 𝔭.IsPrime ∧ ∀ a b : R, b ∉ 𝔭 → (a : Ω) / (b : Ω) ∈ M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw _ l Xo c C o₁ Ω _ _ _ hb M π uη hM hπ A₁ m ze hm hU₁ lev K _ yM y hy
  haveI := hb.char
  haveI := hb.ded
  let w : M.Z := yM (closedPoint K)
  have hw : π w ∈ Set.range C.i := ⟨y (closedPoint K), (congrArg (fun χ : Sp K ⟶ C.Z => χ (closedPoint K)) hy).symm⟩
  obtain ⟨U₀, u₀, hw₀, hu₀⟩ := exists_chart C M π uη hπ w hw
  obtain ⟨U, hle, P₁, -, hU, hwU, hP₁⟩ := LocSpread.exists_model (isUnit_intCast C M π w hw) hw₀ u₀
  have hne : ((U : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwU⟩
  let u : Sp (ratHull (M.ringOn U)) ⟶ Xo.XF c := spMap (Subalgebra.inclusion (ratHull_mono hle)).toRingHom ≫ u₀
  have hu : spMap (ratHull (M.ringOn U)).val.toRingHom ≫ u = uη := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  have gen : ∀ P : PolAV (Sp (M.ringOn U)), UOver Xo c P (toRat (M.ringOn U)) u →
      UOver Xo c P (M.ringOn U).val.toRingHom uη := fun P hP => by
    have := hP.comp (ratHull (M.ringOn U)).val.toRingHom
    rw [hu] at this
    exact this
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := GlobalTheory.Poinc.TorsExtend.isIntegrallyClosed_ringOn M ((isNormalScheme_iff_pred _).1 hM) hU hne
  have fg : (M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ M U hU hne
  haveI : IsNoetherianRing (M.ringOn U) := isNoetherianRing_of_fg fg

  obtain ⟨Q, a, a', ha, ha', hL, hL'⟩ :=
    exists_common_baseChange_of_uOver E H Dw l Xo c Ω _ _ A₁ P₁ _ _ uη hU₁ (gen P₁ hP₁)
  have g₁ := GlobalTheory.polAV_g_eq_of_isGrpPullback Ω _ A₁ Q _ a ha
  have g₂ := GlobalTheory.polAV_g_eq_of_isGrpPullback Ω _ P₁ Q _ a' ha'
  obtain ⟨levQ, -⟩ := exists_level_baseChange GlobalTheory.abelianSchemeLaws_all.1 _ _ _ A₁ Q a ha hL g₁ _ _
    (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) (by rw [GSetup.map_unitOn']; rfl) lev.prim lev
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm.ne_zero Nat.cast_zero)
  obtain ⟨P, ψ, hg, hψ, hψL, hlev⟩ := GlobalTheory.SympLevelExt.level_extends P₁ (M.ringOn U) Ω (RingHom.id _) Q a' m
    (Units.map (algebraMap o₁ (M.ringOn U)).toMonoidHom ze) hm0
    (by simpa using hm.map (algebraMap o₁ (M.ringOn U))) g₂ ha' hL' ⟨levQ⟩
  have hP : UOver Xo c P (toRat (M.ringOn U)) u := (uOver_baseChange_iff hψ hψL _).2 hP₁

  obtain ⟨A₀, hS₀, hU₀⟩ := GSetup.exists_fibre Xo c uη
  obtain ⟨Q', b, b', hb₁, hb₂, hb₃, hb₄⟩ :=
    exists_common_baseChange_of_uOver E H Dw l Xo c Ω _ _ A₀ P _ _ uη hU₀ (gen P hP)
  have hS := GlobalTheory.Poinc.hypS_of_generic_ringOn o₁ Ω M U hU hne hM Ω A₀ P Q' _ b b' hb₁ hb₂ hb₃ hb₄ hS₀

  obtain ⟨act, hact, hA⟩ := exists_uAct (ratHull (M.ringOn U)).val.toRingHom Subtype.val_injective rfl hP
  let j : M.ringOn U →+* M.O w := (Subalgebra.inclusion (RatModel.ringOn_le_O hwU)).toRingHom
  refine ⟨M.ringOn U, P, act, u, (maximalIdeal (M.O w)).comap j, fg, fun x => ?_, hg.trans (g₂.symm.trans g₁), hS, hlev,
    hact, hA, hu, inferInstance, fun p q hq => ?_⟩
  · obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hU hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  · have hq' : IsUnit (j q) := by
      by_contra h
      exact hq h
    rw [div_eq_mul_inv]
    exact mul_mem (j p).2 ((RatModel.isUnit_O_iff _).1 hq').2

end GlobalTheory.UCovSep.LocalSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem ker_eq_bot_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K]
    [CharZero K] (φ : o →+* K) : RingHom.ker φ = ⊥ := by
  by_contra h
  haveI : (RingHom.ker φ).IsMaximal := (RingHom.ker_isPrime φ).isMaximal h
  letI := Ideal.Quotient.field (RingHom.ker φ)
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker φ) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : CharZero (o ⧸ RingHom.ker φ) := (RingHom.charZero_iff (RingHom.kerLift_injective φ)).2 inferInstance
  exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := o ⧸ RingHom.ker φ)
    (fun _ _ h => Int.cast_injective (α := o ⧸ RingHom.ker φ) (by simpa using h)) (Field.toIsField _))

theorem UCompact.range_subset_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) {K : Type} [Field K] [CharZero K]
    (x : Sp K ⟶ Sp C.o) : Set.range x ⊆ Set.range (spMap C.b) := by
  haveI := C.ded
  haveI := C.ft
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  rintro _ ⟨w, rfl⟩
  refine ⟨(⊥ : PrimeSpectrum c.F), PrimeSpectrum.ext ?_⟩
  show Ideal.comap C.b ⊥ = Ideal.comap φ.hom w.asIdeal
  rw [Subsingleton.elim w (⊥ : PrimeSpectrum K)]
  exact ((RingHom.injective_iff_ker_eq_bot _).1 C.inj).trans (ker_eq_bot_of_charZero (K := K) φ.hom).symm

theorem exists_open_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  intro E _ _ _ H Dw l Xo c C
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨U, hU, hUe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := hUe ▸ ⟨x, rfl⟩
    exact this
  · intro p _ y hy
    rintro _ ⟨w, rfl⟩
    have h1 : (gPt p ≫ y) w ∈ Set.range (pullback.fst C.z (spMap C.b) :) := by
      rw [Scheme.Pullback.range_fst]
      exact C.range_subset_generic ((gPt p ≫ y) ≫ C.z) ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := h1
    have h2 : t ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := by
      show _ ∈ U
      rw [ht]
      exact hy ⟨w, rfl⟩
    rw [hUe] at h2
    obtain ⟨x, rfl⟩ := h2
    exact ⟨x, ht⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionEvenTranslateSamePolarisedD
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwist

theorem exists_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (a : 𝟙_ (Over (Sp R)) ⟶ G) (P : GlobalTheory.UU.CP G) (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), a ^ 2 = 1 ∧ LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P ∧ IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) ∧ ∀ (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), U₂.LG = P.L → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨a, ha, hcmp⟩ := _root_.GlobalTheory.TwistSec.exists_sec_compare R hR D₀ D A G hG U hS
  obtain ⟨P, hP, hE⟩ := _root_.GlobalTheory.MumTwistCP.exists_cp_transl R hR D A G hG U a ha
  obtain ⟨A₂, gen₂, hm, hl⟩ := _root_.GlobalTheory.TwistAV.exists_translate_pol R hR D A G hG U a ha P hP
  refine ⟨a, P, A₂, gen₂, ha, hP, hE, hm, hl, fun D₂ U₂ hU => ?_⟩
  exact hcmp A₂ D₂ U₂ (by rw [hU]; exact hP)

end GlobalTheory.MumTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_add_add_pull_sub {K : Type} [Field K] {A B : AbVar K} (d : Pic B.X.left)
    (hd : CechPic.pull (Hom.hom (-(𝟙 B))).left d = d) (f g : A ⟶ B) :
    CechPic.pull (f + g).hom.left d + CechPic.pull (f - g).hom.left d
      = (2 : ℤ) • CechPic.pull f.hom.left d + (2 : ℤ) • CechPic.pull g.hom.left d := by
  have hl := (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K B d A.X f.hom g.hom g.hom (-1)).2.2.2.2
  have hq := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd g (-1)).2
  rw [zpow_neg_one] at hl
  rw [neg_one_zsmul] at hq
  norm_num at hq
  have e1 : CechPic.pull (f + g).hom.left d
      = lam d f.hom g.hom + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [lam, add_hom]; abel
  have e2 : CechPic.pull (f - g).hom.left d
      = lam d f.hom (g.hom⁻¹) + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [sub_eq_add_neg, ← hq, lam, add_hom, neg_hom]; abel
  rw [e1, e2, hl]
  simp only [neg_one_smul, two_smul]
  abel

theorem exists_posDef_quadratic_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ,
    (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  intro K _ A B
  obtain ⟨d, hdA, hd⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨c, hc⟩ := GlobalTheory.AV.exists_isAmpleCls K A
  rcases hA : A.dim with _ | n
  · refine ⟨fun _ => 0, fun _ _ => by simp, fun _ => le_rfl, fun f _ => _root_.GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero K A B (Or.inl hA) f⟩
  · obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hA])
    refine ⟨fun f => inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left), ?_, ?_, ?_⟩
    · intro f g
      simp only [← hM]
      rw [← MultilinearMap.cons_add, pull_add_add_pull_sub d hd f g, MultilinearMap.cons_add,
        MultilinearMap.cons_smul, MultilinearMap.cons_smul]
      simp [two_mul]
    · intro f
      by_cases hf : f = 0
      · subst hf
        have h0 := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd (0 : A ⟶ B) 0).2
        rw [zero_smul] at h0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul] at h0
        show 0 ≤ inter A _
        rw [← hM, h0, M.map_coord_zero (0 : Fin (n + 1)) (by simp)]
      · exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).le
    · intro f hf0
      by_contra hf
      exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).ne' hf0

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedLineBundleExtensionOfLocal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PicGlue

namespace GlobalTheory.RigLBDense

theorem exists_extension_of_local_ext : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (σ : S ⟶ Y) (σU : U ⟶ YU), σ ≫ f = 𝟙 S → σU ≫ e = j ≫ σ → ∀ (L : LB YU), L.IsLB → ∀ (r : LB.Gen (L.pull σU)), r.IsGen → (∀ x : S, x ∉ Set.range j → ∃ W : S.Opens, x ∈ W ∧ ∃ N : LB ↑(f ⁻¹ᵁ W), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ M : LB Y, M.IsLB ∧ LBIso (M.pull e) L := by
  intro S Y U YU _ _ f _ _ j _ hj e fU hP σ σU hσ hσU L hL r hr hloc
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback hP.flip ‹IsOpenImmersion j›
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : GeometricallyIntegral f := (GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1
  exact GlobalTheory.DenseGlue.exists_glue j hj f hσ hP hσU hL ⟨r, hr⟩ (by
    intro x hx
    obtain ⟨W, hxW, N, hN, hagr⟩ := hloc x hx
    obtain ⟨M, hM, hMN⟩ := exists_isOn_of_openImmersion Y _ (f ⁻¹ᵁ W).ι N hN
    rw [Scheme.Opens.opensRange_ι] at hM
    refine ⟨W, hxW, M, hM, ?_⟩
    let T : YU.Opens := e ⁻¹ᵁ (f ⁻¹ᵁ W)
    have hrange : Set.range (T.ι ≫ e) ⊆ Set.range (f ⁻¹ᵁ W).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let a : T.toScheme ⟶ (f ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ W).ι (T.ι ≫ e) hrange
    have ha : a ≫ (f ⁻¹ᵁ W).ι = T.ι ≫ e := IsOpenImmersion.lift_fac _ _ _
    have hι : ∀ z, (f ⁻¹ᵁ W).ι z ∈ f ⁻¹ᵁ W := fun z => by
      have : (f ⁻¹ᵁ W).ι z ∈ Set.range (f ⁻¹ᵁ W).ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    have hg : ∀ z, (T.ι ≫ e) z ∈ f ⁻¹ᵁ W := fun z => z.2
    have k₀ : (M.pull (f ⁻¹ᵁ W).ι).IsLB := pull_isLB_of_isOn Y _ _ M _ hM hι
    have k₁ : ((M.pull (f ⁻¹ᵁ W).ι).pull a).IsLB := LB.isLB_pull k₀ a
    have k₂ : (M.pull (T.ι ≫ e)).IsLB := pull_isLB_of_isOn Y _ _ M _ hM hg
    have i₁ : LBIso ((M.pull (f ⁻¹ᵁ W).ι).pull a) (M.pull (T.ι ≫ e)) := by
      have := isOn_pull_comp Y _ _ (f ⁻¹ᵁ W) M (f ⁻¹ᵁ W).ι a hM hι
      rwa [ha] at this
    have i₂ : LBIso ((M.pull (f ⁻¹ᵁ W).ι).pull a) (N.pull a) := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ a a rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ a a rfl) hMN
    have i₃ : LBIso (N.pull a) (L.pull T.ι) := hagr T a T.ι ha
    exact LBIso.trans k₂ k₁ (LB.isLB_pull hL _) i₁.symm (LBIso.trans k₁ (LB.isLB_pull hN a) (LB.isLB_pull hL _) i₂ i₃)
  )

end GlobalTheory.RigLBDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtendDescendedSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescAct

theorem exists_oAct_extend_toSemiAbelian_normBl : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ act : OAct (𝓞 E) G, ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hG he _
  obtain ⟨-, -, -, -, ⟨hBl, hP, -, hd, -⟩, -⟩ := hU
  have : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP
  have : IsDominant j := ⟨hd⟩
  haveI : GlobalTheory.IsNormalScheme S := hBl.1
  obtain ⟨a, ha, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_oAct_of_isGrpPullback
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.IsNormalScheme.pred S) hG he tF.act
  exact ⟨a, ha⟩

end GlobalTheory.DescAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix : ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  first | (exact @GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (exact GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (intros; apply GlobalTheory.ZarhinFam.exists_spanning_family_posDef  <;> assumption)
end

