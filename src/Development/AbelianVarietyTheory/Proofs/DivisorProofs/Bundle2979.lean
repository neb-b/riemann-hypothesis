module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZRam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.LiftOrd

theorem evalZ_ram {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V)
    (hf : Function.Injective f) (hl : IsLocalHom f)
    (hK : ∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a))
    (hy : T'.y = spMap fK ≫ T.y) (m : ℕ) (hm : Associated (f T.ϖ) (T'.ϖ ^ m)) (φ : InvFun (𝓞 E))
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) : φ.evalZ T'.be = m * φ.evalZ T.be := by
  obtain ⟨hdvr, hcpl, hz⟩ := T'.cdvr
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hz⟩
  have hself : Associated (RingHom.id T'.V T'.ϖ) (T'.ϖ ^ 1) := by simp [Associated.refl]
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UPoinc.uTraitUniqSt_holds E H Dw l Xo c T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB hdvr hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    hself
  have hon : IsPolFanOn H.bar φ T.P.D.toPre.X := by
    haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
    exact hφ _ (GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)
  have hc : toReal T.be ∈ psdCone (bar := H.bar) (X := T.P.D.toPre.X) :=
    GlobalTheory.PolFan.StrictData.toReal_mem_psdCone ((balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev)
      fun y => by simpa using T.mono.nonneg 0 y
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.UPoinc.LiftOrd

theorem _root_.GlobalTheory.UPoinc.ideal_orders_of_proper_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range C.i) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (J₁.comap πY) ι → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι J₁ hsupp hval
  haveI := hprop
  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  intro W _ _ _ hW ϖ hϖ χ y hy _ t tK h1 h2 P be hbe hmono
  let T : UTrait Xo c := ⟨W, hW, ϖ, hϖ, y, t, ⟨tK, h1, h2⟩, P, be, hbe, hmono⟩
  obtain ⟨hdvr, hcpl, hz⟩ := hW
  haveI := hdvr
  haveI := hz

  obtain ⟨K', _, σ, yK, hσ, hyK⟩ := GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft πY inferInstance hsurj
    (FractionRing W) (jK W ≫ χ)
  obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ :=
    GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom W hcpl K' σ hσ
  have hfK : ∀ a, (τ.comp σ) (algebraMap W _ a) = algebraMap V' _ (f a) := hτ
  obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.proper_lift_trait πY hprop W V' f (τ.comp σ) hfK χ (spMap τ ≫ yK) (by
    rw [Category.assoc, hyK, spMap_comp, Category.assoc])
  have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
    _root_.GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V' hB' inferInstance (spMap (τ.comp σ) ≫ y)
  haveI := hfl
  haveI := hf₂l
  have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
      (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
      jK S ≫ spMap u = spMap uK ≫ jK R := by
    intro R S _ _ _ _ u uK hu
    change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

  have hcomm : T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π := by
    have e1 := hjK f₂ fK₂ hf₂K
    symm
    calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
          simp only [Category.assoc]
      _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
      _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
      _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK W ≫ χ ≫ X₁.π) := by rw [hyK]; simp only [Category.assoc]
      _ = T₂.y ≫ C.i := by rw [← hy, hT₂y, spMap_comp]; simp only [Category.assoc]
  obtain ⟨tK₂, m₁, m₂⟩ := T₂.gen
  obtain ⟨a', ha', hid⟩ := hval T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ ξ') T₂.y hcomm trivial T₂.t tK₂ m₁ m₂ T₂.P T₂.be
    T₂.lev T₂.mono
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    have eq_map {A : Type} [CommRing A] [IsLocalRing A] (ψ : Sp A ⟶ X)
        (U : X.affineOpens) (hle : ⊤ ≤ ψ ⁻¹ᵁ U.1) :
        idlAlong J ψ = (J.ideal U).map (ψ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of A)).hom).hom := by
      have hx : ψ (closedPoint A) ∈ U.1 := hle trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map χ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
    idlAlong_comp_local] at hid

  set h := f₂.comp f with hh
  have hinj : Function.Injective h := hf₂i.comp hfi
  have hloc : IsLocalHom h := inferInstance
  obtain ⟨hdvr₂, -, -⟩ := T₂.cdvr
  haveI := hdvr₂
  have hne : h ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact absurd ((isUnit_map_iff h ϖ).1 (he.isUnit_iff.2 (by simp))) hϖ.not_isUnit
    · exact hpos
  obtain ⟨b, hb, hI⟩ := GlobalTheory.ideal_map_eq_span_pow_uniformizer W T₂.V h hinj ϖ T₂.ϖ e a' _ hϖ T₂.irr he hid
  have hval2 : φ.evalZ T₂.be = e * φ.evalZ be :=
    GlobalTheory.UPoinc.LiftOrd.evalZ_ram T T₂ h (fK₂.comp (τ.comp σ)) hinj hloc
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (by rw [hT₂y]; simp only [spMap_comp, Category.assoc]; first | rfl | skip) e he φ hφ
  refine ⟨b, ?_, hI⟩
  have h1 : (e : ℝ) * b = e * (ι * φ.evalZ be) := by
    rw [← Nat.cast_mul, hb, ha', hval2]; ring
  have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  exact mul_left_cancel₀ h2 h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatHullLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.UPoinc.ChartAt

theorem isUnit_map_of_ne_zero {o R : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [CommRing R]
    (hR : ∀ n : ℤ, n ≠ 0 → IsUnit (n : R)) (φ : o →+* R) {a : o} (ha : a ≠ 0) : IsUnit (φ a) := by
  by_contra h
  obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
  letI := Ideal.Quotient.field m
  haveI : CharZero (R ⧸ m) := charZero_of_inj_zero fun n hn => by
    by_contra h0
    have hu := (hR n (by exact_mod_cast h0)).map (Ideal.Quotient.mk m)
    exact hu.ne_zero (by simpa using hn)
  have hk := ker_eq_bot_of_charZero ((Ideal.Quotient.mk m).comp φ)
  have : a ∈ RingHom.ker ((Ideal.Quotient.mk m).comp φ) := Ideal.Quotient.eq_zero_iff_mem.2 ham
  rw [hk] at this
  exact ha this

theorem exists_affine_chart_ratHull_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w₀ ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw _ l Xo cf C X w hw
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  haveI := C.isPreimmersion_i
  haveI : CharZero X.Ω₁ := by
    obtain ⟨t, -⟩ := Spec.map_surjective (X.uΩ ≫ pullback.snd _ _)
    exact (RingHom.charZero_iff (R := cf.F) t.hom.injective).1 inferInstance
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨V, hV, hVe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ X.π ⁻¹ᵁ ⟨V, hV⟩ := by
    obtain ⟨x, hx⟩ := hw
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' V := hVe ▸ ⟨x, rfl⟩
    show X.π w ∈ V
    rw [← hx]
    exact this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of (ratHull (X.M.ringOn U)) :=
    CommRingCat.ofHom ((toRat (X.M.ringOn U)).comp (X.M.sectionsEquiv U hne).toRingHom)
  let f : Sp (ratHull (X.M.ringOn U)) ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (f ≫ X.π ≫ C.z)
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (ψ.hom a) := fun a =>
    isUnit_map_of_ne_zero (fun n hn => isUnit_intCast_ratHull _ hn) ψ.hom (nonZeroDivisors.ne_zero a.2)
  let χ : cf.F →+* ratHull (X.M.ringOn U) := IsLocalization.lift (M := nonZeroDivisors C.o) hu
  have hχ : (f ≫ X.π) ≫ C.z = spMap χ ≫ spMap C.b := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun t => spMap t) (IsLocalization.lift_comp (M := nonZeroDivisors C.o) hu).symm
  let g := pullback.lift _ _ hχ
  have hgf : g ≫ pullback.fst _ _ = f ≫ X.π := pullback.lift_fst _ _ _
  have hrange : Set.range g ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hVe]
    show (g ≫ pullback.fst C.z (spMap C.b)) y ∈ V
    rw [hgf]
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact hUV this
  refine ⟨U, IsOpenImmersion.lift C.iF g hrange, hU, hwU, ?_⟩
  rw [← cancel_mono C.i, Category.assoc, Category.assoc, ← X.comp, UCompact.i, IsOpenImmersion.lift_fac_assoc, hgf]
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (ratHull (X.M.ringOn U)).val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [Category.assoc]

end GlobalTheory.UPoinc.ChartAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantTraceGeneratorLocal
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.RealTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_algebraMap (H : Host E) (r : 𝓞 (maximalRealSubfield E)) :
    H.bar (algebraMap _ (𝓞 E) r) = algebraMap _ (𝓞 E) r := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  have h1 : ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E) : E) =
      algebraMap (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) r) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E]
    exact (IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E r).symm
  rw [h1]
  exact (IsCMField.complexConj E).commutes _

theorem sub_bar_mem_pow_succ (H : Host E) (𝔭 : Ideal (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ c, c - H.bar c ∈ 𝔭 ^ n) (c : 𝓞 E) : c - H.bar c ∈ 𝔭 ^ (n + 1) := by
  haveI := H.unram
  let L : 𝓞 E →ₗ[𝓞 (maximalRealSubfield E)] (𝓞 E ⧸ 𝔭 ^ (n + 1)) :=
    { toFun := fun c => Ideal.Quotient.mk _ (c - H.bar c)
      map_add' := fun a b => by rw [← map_add (f := _), map_add H.bar]; congr 1; ring
      map_smul' := fun r a => by
        rw [Algebra.smul_def, map_mul, bar_algebraMap, ← mul_sub, RingHom.id_apply, Algebra.smul_def, map_mul,
          Ideal.Quotient.mk_algebraMap] }
  let D : Derivation (𝓞 (maximalRealSubfield E)) (𝓞 E) (𝓞 E ⧸ 𝔭 ^ (n + 1)) :=
    Derivation.mk' L fun a b => by
      show Ideal.Quotient.mk _ (a * b - H.bar (a * b)) =
        a • Ideal.Quotient.mk _ (b - H.bar b) + b • Ideal.Quotient.mk _ (a - H.bar a)
      rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, ← map_add (f := _),
        Ideal.Quotient.eq]
      have hab : (a - H.bar a) * (b - H.bar b) ∈ 𝔭 ^ (n + 1) :=
        Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) (by rw [pow_add]; exact Ideal.mul_mem_mul (h a) (h b))
      have : a * b - H.bar (a * b) - (a * (b - H.bar b) + b * (a - H.bar a)) = -((a - H.bar a) * (b - H.bar b)) := by
        rw [map_mul]; ring
      rw [this]; exact neg_mem hab
  have hD : D c = 0 := by
    rw [← Derivation.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D _ _ c) 0, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 hD

theorem exists_sub_bar_notMem (H : Host E) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭 ≠ ⊤) : ∃ c, c - H.bar c ∉ 𝔭 := by
  by_contra! h
  have key : ∀ n : ℕ, ∀ c, c - H.bar c ∈ 𝔭 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih => exact sub_bar_mem_pow_succ H 𝔭 (n + 1) (by omega) ih
  have h0 : H.rt - H.bar H.rt = 0 := by
    have hm : H.rt - H.bar H.rt ∈ ⨅ i, 𝔭 ^ i :=
      Ideal.mem_iInf.2 fun i => Ideal.pow_le_pow_right (Nat.le_succ i) (key i _)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭, Ideal.mem_bot] at hm
  rw [GlobalTheory.CharRank.bar_rt_neg, sub_neg_eq_add, ← two_mul] at h0
  have hrt : H.rt = 0 := (mul_eq_zero.1 h0).resolve_left two_ne_zero
  have hd := H.rt_sq
  rw [hrt, zero_pow two_ne_zero, zero_eq_neg, Nat.cast_eq_zero] at hd
  exact H.d_prime.ne_zero hd

end GlobalTheory.RealTheta

namespace GlobalTheory.RealTheta

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_trace_eq (ψ : 𝓞 E →+ ℤ) : ∃ δ : E, ∀ u : 𝓞 E, ((ψ u : ℤ) : ℚ) = Algebra.trace ℚ E (δ * u) := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => (ψ (RingOfIntegers.basis E i) : ℚ))
  obtain ⟨δ, hδ⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective f
  refine ⟨δ, fun u => ?_⟩
  have h1 : Algebra.trace ℚ E (δ * u) = f u := by
    rw [← hδ, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]
  rw [h1]
  have h2 : ((Int.castAddHom ℚ).comp ψ).toIntLinearMap =
      (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom).toIntLinearMap := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    simp [f, ← integralBasis_apply]
  exact (LinearMap.congr_fun h2 u)


open FractionalIdeal in
theorem exists_local_gen {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0) {𝔭 : Ideal (𝓞 E)} {δ : E} (hδ : δ ∈ M)
    (hδ' : δ ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M) :
    ∃ s : 𝓞 E, s ∉ 𝔭 ∧ ∀ x ∈ M, ∃ t : 𝓞 E, (s : E) * x = δ * t := by
  set I := spanSingleton (𝓞 E)⁰ δ * M⁻¹ with hI
  have hIM : I * M = spanSingleton (𝓞 E)⁰ δ := by
    rw [hI, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  have hI1 : I ≤ 1 := by
    rw [← mul_inv_cancel₀ hM, hI]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.2 hδ) _
  have hnot : ¬ I ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro h
    apply hδ'
    have : spanSingleton (𝓞 E)⁰ δ ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := hIM ▸ mul_le_mul_left h M
    exact spanSingleton_le_iff_mem.1 this
  obtain ⟨y, hyI, hy𝔭⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨s, rfl⟩ := (mem_one_iff _).1 (hI1 hyI)
  refine ⟨s, fun hs => hy𝔭 ((mem_coeIdeal _).2 ⟨s, hs, rfl⟩), fun x hx => ?_⟩
  have : algebraMap (𝓞 E) E s * x ∈ spanSingleton (𝓞 E)⁰ δ := hIM ▸ mul_mem_mul hyI hx
  obtain ⟨t, ht⟩ := (mem_spanSingleton _).1 this
  exact ⟨t, by rw [← ht, Algebra.smul_def, mul_comm]⟩


open FractionalIdeal in
theorem exists_mem_notMem_mul {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ x ∈ M, x ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
  by_contra! h
  have hle : M ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := fun x hx => h x hx
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ 𝔭 := by
    have := mul_le_mul_left hle M⁻¹
    rwa [mul_assoc, mul_inv_cancel₀ hM, mul_one] at this
  rw [← coeIdeal_top, coeIdeal_le_coeIdeal E] at h1
  exact h𝔭 (top_le_iff.1 h1)

theorem fi_add_mem (N : FractionalIdeal (𝓞 E)⁰ E) {x y : E} (hx : x ∈ N) (hy : y ∈ N) : x + y ∈ N :=
  FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hy))

theorem fi_sub_mem (N : FractionalIdeal (𝓞 E)⁰ E) {x y : E} (hx : x ∈ N) (hy : y ∈ N) : x - y ∈ N :=
  FractionalIdeal.mem_coe.1 (Submodule.sub_mem _ (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hy))

theorem fi_mul_mem (N : FractionalIdeal (𝓞 E)⁰ E) (a : 𝓞 E) {y : E} (hy : y ∈ N) : (a : E) * y ∈ N := by
  have := Submodule.smul_mem (N : Submodule (𝓞 E) E) a (FractionalIdeal.mem_coe.2 hy)
  rw [Algebra.smul_def] at this
  exact FractionalIdeal.mem_coe.1 this

theorem exists_real_notMem (H : Host E) {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0)
    (hconj : ∀ x ∈ M, IsCMField.complexConj E x ∈ M) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ δ ∈ M, IsCMField.complexConj E δ = δ ∧ δ ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
  obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_mul hM h𝔭.ne_top
  obtain ⟨c, hc⟩ := exists_sub_bar_notMem H h𝔭.ne_top
  have hcc : ∀ y, IsCMField.complexConj E (IsCMField.complexConj E y) = y := IsCMField.complexConj_apply_apply E
  have hbar : IsCMField.complexConj E (c : E) = (H.bar c : E) := (H.bar_eq c).symm
  by_cases h1 : x + IsCMField.complexConj E x ∈ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M
  · refine ⟨(c : E) * x + IsCMField.complexConj E ((c : E) * x), fi_add_mem _ (fi_mul_mem M c hx)
      (hconj _ (fi_mul_mem M c hx)), by rw [map_add (f := _), hcc, add_comm], fun h2 => hx' ?_⟩
    have h3 : ((c - H.bar c : 𝓞 E) : E) * x ∈ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
      have := fi_sub_mem _ h2 (fi_mul_mem _ (H.bar c) h1)
      convert this using 1
      rw [map_mul, hbar]; push_cast; ring
    obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv hc
    have hyi' := congrArg (fun z : 𝓞 E => (z : E)) hyi
    push_cast at hyi'
    have : x = (y : E) * (((c - H.bar c : 𝓞 E) : E) * x) + (i : E) * x := by
      push_cast; linear_combination (-x) * hyi'
    rw [this]
    exact fi_add_mem _ (fi_mul_mem _ y h3)
      (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hi, rfl⟩) hx)
  · exact ⟨x + IsCMField.complexConj E x, fi_add_mem _ hx (hconj x hx), by rw [map_add (f := _), hcc, add_comm], h1⟩

theorem trace_conj (y : E) : Algebra.trace ℚ E (IsCMField.complexConj E y) = Algebra.trace ℚ E y :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y

theorem conj_mem_dual (H : Host E) {x : E} (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    IsCMField.complexConj E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)] at hx ⊢
  intro a ha
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  have := hx _ ((FractionalIdeal.mem_one_iff _).2 ⟨H.bar b, rfl⟩)
  rw [Algebra.traceForm_apply] at this ⊢
  convert this using 1
  rw [← trace_conj, map_mul, IsCMField.complexConj_apply_apply]
  exact congrArg (fun y => Algebra.trace ℚ E (x * y)) (H.bar_eq b).symm

end GlobalTheory.RealTheta

namespace GlobalTheory.RealTheta

open scoped nonZeroDivisors

theorem exists_bar_inv_trace_gen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
  intro E _ _ _ H 𝔭 h𝔭
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set M : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hMdef
  have hM : M ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h10
  obtain ⟨δ, hδM, hδc, hδ⟩ := exists_real_notMem H hM (fun x hx => conj_mem_dual H hx) h𝔭
  have hint : ∀ x ∈ M, ∀ u : 𝓞 E, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E (x * u) := by
    intro x hx u
    rw [hMdef, FractionalIdeal.mem_dual h10] at hx
    obtain ⟨z, hz⟩ := hx _ ((FractionalIdeal.mem_one_iff _).2 ⟨u, rfl⟩)
    exact ⟨z, by rw [← Algebra.traceForm_apply, ← hz]; simp⟩
  choose z hz using hint δ hδM
  let θ : 𝓞 E →+ ℤ := AddMonoidHom.mk' z fun a b => Int.cast_injective (α := ℚ) (by
    push_cast; rw [hz, hz, hz]; push_cast; rw [mul_add, map_add (f := _)])
  have hθ : ∀ u, ((θ u : ℤ) : ℚ) = Algebra.trace ℚ E (δ * u) := hz
  have hmemψ : ∀ ψ : 𝓞 E →+ ℤ, ∃ x ∈ M, ∀ u : 𝓞 E, ((ψ u : ℤ) : ℚ) = Algebra.trace ℚ E (x * u) := by
    intro ψ
    obtain ⟨x, hx⟩ := exists_trace_eq ψ
    refine ⟨x, (FractionalIdeal.mem_dual h10).2 fun a ha => ?_, hx⟩
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    exact ⟨ψ b, by rw [Algebra.traceForm_apply]; simpa using (hx b)⟩
  obtain ⟨s, hs, hsM⟩ := exists_local_gen hM hδM hδ
  have hθbar : ∀ t, θ (H.bar t) = θ t := by
    intro t
    apply Int.cast_injective (α := ℚ)
    rw [hθ, hθ, H.bar_eq, ← hδc, ← map_mul, trace_conj, hδc]
  have hPs : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
    intro ψ
    obtain ⟨x, hx, hψ⟩ := hmemψ ψ
    obtain ⟨t, ht⟩ := hsM x hx
    refine ⟨t, fun u => Int.cast_injective (α := ℚ) ?_⟩
    rw [hψ, hθ]
    push_cast
    rw [← mul_assoc, mul_comm x, ht, mul_assoc]
  have hPbar : ∀ s : 𝓞 E, (∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) →
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (H.bar s * u) = θ (t * u) := by
    intro s hs ψ
    obtain ⟨t, ht⟩ := hs (ψ.comp (H.bar : 𝓞 E →+* 𝓞 E).toAddMonoidHom)
    refine ⟨H.bar t, fun u => ?_⟩
    have := ht (H.bar u)
    simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe,
      map_mul, bar_bar] at this
    rw [this, ← hθbar (t * H.bar u), map_mul, bar_bar]
  refine ⟨θ, hθbar, ?_⟩
  by_cases hb : H.bar s ∈ 𝔭
  · have hsb : s + H.bar s ∉ 𝔭 := fun h => hs (by have := sub_mem h hb; rwa [add_sub_cancel_right] at this)
    refine ⟨s + H.bar s, hsb, by rwa [map_add, bar_bar, add_comm], fun ψ => ?_⟩
    obtain ⟨t, ht⟩ := hPs ψ
    obtain ⟨t', ht'⟩ := hPbar s hPs ψ
    exact ⟨t + t', fun u => by rw [add_mul, map_add (f := _), ht, ht', add_mul, map_add (f := _)]⟩
  · exact ⟨s, hs, hb, hPs⟩

end GlobalTheory.RealTheta
end
end

