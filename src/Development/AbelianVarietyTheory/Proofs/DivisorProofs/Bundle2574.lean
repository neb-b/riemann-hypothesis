module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat.ClosedLift

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem endo_of_closed {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {V : Type} [CommRing V]
    [IsDomain V] {ξ : Sp V ⟶ S} {G₁ : Over (Sp V)} [GrpObj G₁] {φ₁ : G₁.left ⟶ G.left}
    (h : IsGrpPullback G₁ G ξ φ₁) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (j : splitTorus (Sp V) X ⟶ G₁) [IsMonHom j] {GK : Over (Sp (FractionRing V))} [GrpObj GK]
    {ψ : GK.left ⟶ G₁.left} (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ)
    (hK : IsTorPart (pullTorus hψ j)) {κ : Type} [Field κ] {b : V →+* κ} {G₀ : Over (Sp κ)} [GrpObj G₀]
    {ψ₀ : G₀.left ⟶ G₁.left} (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (h0 : IsTorPart (pullTorus hψ₀ j))
    (u : G ⟶ G) [IsMonHom u] (r : X →+ X)
    (hr : (pullTorus hψ₀ j).left ≫ (ψ₀ ≫ φ₁) ≫ u.left = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁) :
    j.left ≫ φ₁ ≫ u.left = (torusMap _ r ≫ j).left ≫ φ₁ := by
  obtain ⟨u₁, hu₁, pa⟩ := GlobalTheory.SymBaseChange.exists_endo h u
  have hw : u₁.left ≫ φ₁ = φ₁ ≫ u.left := by
    have := congrArg CommaMorphism.left (pa (𝟙 G₁))
    simpa [pushPt] using this
  haveI := hu₁
  obtain ⟨s, hs⟩ := hK.factor (pullTorus hψ (j ≫ u₁)) inferInstance
  rw [← pullTorus_torusMap_comp] at hs
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V (FractionRing V))) ∧
      IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSeparated G₁.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have key : j ≫ u₁ = torusMap _ s ≫ j :=
    GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap (algebraMap V (FractionRing V))) X)
      (by rw [← pullTorus_left hψ, ← pullTorus_left hψ, hs])
  have k0 : torusMap _ s ≫ pullTorus hψ₀ j = torusMap _ r ≫ pullTorus hψ₀ j := by
    apply hom_ext_of_pullback (hψ₀.comp h)
    have e1 := pullTorus_left hψ₀ (j ≫ u₁)
    have e2 := pullTorus_left hψ₀ j
    calc (torusMap _ s ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁
        = ((pullTorus hψ₀ (j ≫ u₁)).left ≫ ψ₀) ≫ φ₁ := by
          rw [← pullTorus_torusMap_comp, ← key, Category.assoc]
      _ = bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ u.left := by
          rw [e1]; simp [Category.assoc, hw]
      _ = ((pullTorus hψ₀ j).left ≫ ψ₀) ≫ φ₁ ≫ u.left := by
          rw [e2]; simp only [Category.assoc]
      _ = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := by
          rw [← hr]; simp only [Category.assoc]
  have hsr : s = r := h0.cancel k0
  subst hsr
  rw [← key, Over.comp_left, Category.assoc, hw]

theorem compat_of_closed : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hLu hf hgγ X _ _ _ m c V _ _ _ ξ a G₁ _ φ₁ h j hj hext GK _ ψ hψ hK
    κ _ b hb G₀ _ ψ₀ hψ₀ h0 hC
  haveI := hG.separated
  haveI := hj
  haveI : NeZero L := ⟨hL.ne'⟩
  refine ⟨fun e => ?_, fun t => ?_⟩
  · haveI := hf e
    exact endo_of_closed h j hψ hK hψ₀ h0 (f e) (m e) (hC.1 e)
  obtain ⟨z₀, hz₀, hv₀⟩ := hC.2 t
  have hζV : (Units.map a.toMonoidHom ζ) ^ L = 1 := by rw [← map_pow, hζ, map_one]
  have hpow : ∀ k : ℕ, ((Units.map a.toMonoidHom ζ) ^ k) ^ L = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζV, one_pow]
  let F : Multiplicative X →* Γ(Sp V, ⊤)ˣ :=
    { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
      map_one' := by simp [unitOn]
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add (f := _), ZMod.val_add, ← pow_eq_pow_mod _ hζV, pow_add]
        simp [unitOn] }
  let Z1 : Over (Sp V) := Over.mk (𝟙 (Sp V))
  obtain ⟨z, hz⟩ : ∃ z : Z1 ⟶ splitTorus (Sp V) X, GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z = F :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hzχ : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    show GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z (Multiplicative.ofAdd χ) = _
    rw [hz]; rfl
  have hzL : z ^ L = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1).injective
    rw [map_pow, hz, map_one]
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show unitOn _ ^ L = 1
    rw [unitOn, ← map_pow, hpow, map_one]

  let x : Over.mk (Z1.hom ≫ ξ) ⟶ G := pushPt h.1.w (z ≫ j)
  have hxL : x ^ L = 1 := by
    have e1 : pushPt h.1.w ((z ≫ j) ^ L) = x ^ L := map_pow (pushHom h Z1) (z ≫ j) L
    rw [← e1, ← pow_comp, hzL, one_comp]
    exact map_one (pushHom h Z1)

  obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
  have hvb : spMap b ≫ v = (z₀ ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := ValAt.unique (hv.comp (spMap b)) hv₀
  obtain ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩ := hv
  let H : Over.mk W.ι ⟶ G := Over.homMk hW hW1
  have hne : (W : Set M.Z).Nonempty := ⟨ξ (closedPoint V), by rw [← hs']; exact (s' (closedPoint V)).2⟩
  haveI : Nonempty W.toScheme := ⟨⟨_, hne.some_mem⟩⟩
  haveI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hr : Set.range M.pt ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x₀ := IsOpenImmersion.lift W.ι M.pt hr
  have hx₀ : x₀ ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (x₀ ≫ W.ι) := hx₀ ▸ M.isDominant_pt
  haveI : IsDominant x₀ := IsDominant.of_comp_of_isOpenImmersion x₀ W.ι
  have hHL : H ^ L = 1 := by
    let u : Over.mk M.pt ⟶ Over.mk W.ι := Over.homMk x₀ hx₀
    have hu : u ≫ H = gγ t := Over.OverMorphism.ext (hW2 x₀ hx₀)
    have e : u ≫ H ^ L = u ≫ 1 := by rw [comp_pow, hu, hgγ t, comp_one]
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk W.ι).left := inferInstanceAs (IsReduced W.toScheme)
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x₀ ?_
    · rw [Over.w, Over.w]
    · exact congrArg CommaMorphism.left e
  let σ : Over.mk (Z1.hom ≫ ξ) ⟶ Over.mk W.ι := Over.homMk s' (by
    show s' ≫ W.ι = 𝟙 _ ≫ ξ
    rw [hs', Category.id_comp])
  let y : Over.mk (Z1.hom ≫ ξ) ⟶ G := σ ≫ H
  have hyL : y ^ L = 1 := by
    show (σ ≫ H) ^ L = 1
    rw [← comp_pow, hHL, comp_one]

  have hw' : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
    rw [Category.assoc, Over.w z]; simp [Z1]
  let z' : Over.mk (𝟙 (Sp κ)) ⟶ splitTorus (Sp κ) X :=
    Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw')
      ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
  have hz'l : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
    (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
  have hz'χ : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    ext
    have e := congrArg Units.val (hzχ χ)
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
    rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz'l,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [e]
    simp only [unitOn, Units.coe_map]
    have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.symm.trans ?_
    simp
  have hzz : z₀ = z' := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp κ) X _).injective
    refine MonoidHom.ext fun χ => ?_
    exact (hz₀ (Multiplicative.toAdd χ)).trans (hz'χ (Multiplicative.toAdd χ)).symm
  have hcl : spMap b ≫ x.left = spMap b ≫ y.left := by
    show spMap b ≫ (z ≫ j).left ≫ φ₁ = spMap b ≫ s' ≫ hW
    rw [hsv, hvb, hzz]
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% (pullTorus_left hψ₀ j), reassoc_of% hz'l]
  have hLV : IsUnit (L : V) := by simpa using hLu.map a
  have hxy : x = y := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint M.Z G hG.smooth V (Z1.hom ≫ ξ) L hLV x y
    (by rw [hxL, hyL]) κ b hb hcl
  refine ⟨z, hzχ, ?_⟩
  have e' : (z ≫ j).left ≫ φ₁ = v := (congrArg CommaMorphism.left hxy).trans hsv
  rw [e']
  exact ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩

end GlobalTheory.Poinc.FibLat.ClosedLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem compat_of_compat_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ X _ m c V _ _ _ ξ a G₁ _ φ₁ h₁ j hext K _ b hb GK _ ψ hψ hK
  haveI hsep : IsSeparated G.hom := hG.separated
  haveI : Flat (splitTorusAff ZU X).hom := (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
  haveI : Flat (splitTorus (Sp V) X).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSchemeTheoreticallyDominant (spMap b) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hb
  haveI : QuasiCompact (spMap b) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (bcMap (spMap b) X) :=
    IsSchemeTheoreticallyDominant.of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).flip
  have hw : φ₁ ≫ G.hom = G₁.hom ≫ ξ := h₁.1.w
  refine ⟨fun e => ?_, fun t => ?_⟩
  · have h1 := hK.1 e
    rw [← pullTorus_torusMap_comp] at h1
    simp only [Category.assoc] at h1
    have e1 := pullTorus_left hψ j
    have e2 := pullTorus_left hψ (torusMap (Sp V) (m e) ≫ j)
    refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (bcMap (spMap b) X) ?_
    · simp only [Category.assoc, Over.w, hw, Over.w_assoc, Over.comp_left]
    · calc bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ (f e).left
          = (pullTorus hψ j).left ≫ ψ ≫ φ₁ ≫ (f e).left := by rw [reassoc_of% e1]
        _ = (pullTorus hψ (torusMap (Sp V) (m e) ≫ j)).left ≫ ψ ≫ φ₁ := h1
        _ = bcMap (spMap b) X ≫ (torusMap (Sp V) (m e) ≫ j).left ≫ φ₁ := by rw [reassoc_of% e2]
  · obtain ⟨zK, hzK, hvK⟩ := hK.2 t
    haveI : NeZero L := ⟨hL.ne'⟩
    have huL : Units.map a.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
    let φh : Multiplicative X →* (Γ(Sp V, ⊤))ˣ :=
      { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
        map_one' := by simp [unitOn]
        map_mul' := fun x y => by
          simp only [toAdd_mul, map_add (f := _), unitOn]
          rw [ZMod.val_add, ← pow_eq_pow_mod _ huL, pow_add, map_mul] }
    let z : Over.mk (𝟙 (Sp V)) ⟶ splitTorus (Sp V) X := (GlobalTheory.splitTorusPointsEquiv (Sp V) X _).symm φh
    have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
      rfl
    have hwz : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp K)) ⟶ splitTorus (Sp K) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hwz)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    have hcz' : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    have hzz : zK = z' := GlobalTheory.SplitTorus.hom_ext fun χ => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val,
        ← GlobalTheory.UU.chV_val, hzK, hcz']
    have hvK' : ValAt (gγ t) (spMap b ≫ ξ) (spMap b ≫ (z ≫ j).left ≫ φ₁) := by
      convert hvK using 1
      rw [hzz, Over.comp_left, Over.comp_left]
      simp only [Category.assoc]
      rw [reassoc_of% (pullTorus_left hψ j), reassoc_of% hz']
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
    have hvv : spMap b ≫ v = spMap b ≫ (z ≫ j).left ≫ φ₁ := (hv.comp (spMap b)).unique hvK'
    have hveq : v = (z ≫ j).left ≫ φ₁ := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap b) hvv
      rw [hv.over]
      simp only [Category.assoc, hw, Over.comp_left, Over.w_assoc]
      exact (Category.id_comp _).symm
    exact ⟨z, hz, hveq ▸ hv⟩

end GlobalTheory.Poinc.FibLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommNeg
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem negT_fibre_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2
  have gB : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((GlobalTheory.ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart).congr rfl (by simp only [Category.assoc])
  have gA := C.α_cart
  have nfA : negT C.A.A (TFK (R := R) F) ≫ fst (TFK (R := R) F) C.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsA : negT C.A.A (TFK (R := R) F) ≫ snd (TFK (R := R) F) C.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have nfB : negT T.A.A (TFK (R := W) F) ≫ fst (TFK (R := W) F) T.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsB : negT T.A.A (TFK (R := W) F) ≫ snd (TFK (R := W) F) T.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have hw : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have e := congrArg (· ≫ C.G.hom) hf2
    have wB := gB.1.w
    simp only [Category.assoc] at e wB
    rw [gA.1.w, wB, ← Category.assoc (snd (TFK (R := R) F) C.A.A).left, ← Category.assoc (snd (TFK (R := W) F) T.A.A).left,
      Over.w, Over.w] at e
    exact e
  let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
    Over.homMk f hw
  have key : ρ ≫ pushHom gA _ (snd _ _) = pushHom gB _ (snd _ _) :=
    Over.OverMorphism.ext (by
      show f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ _
      exact hf2)
  have keyi : ρ ≫ pushHom gA _ (snd _ _ ≫ GrpObj.inv) = pushHom gB _ (snd _ _ ≫ GrpObj.inv) := by
    have i1 : (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    have i2 : (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    rw [i1, i2, map_inv, map_inv, GrpObj.comp_inv, key]
  apply pullback.hom_ext
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (fst (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (fst (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nfA, hf1, ← Over.comp_left, nfB]
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (snd (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (snd (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nsA]
    apply gA.1.hom_ext
    · have k : f ≫ (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv).left ≫ C.α =
          (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β :=
        congrArg Over.Hom.left keyi
      rw [Category.assoc, k]
      simp only [Category.assoc]
      rw [hf2, ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nsB]
    · rw [Category.assoc, Over.w, Category.assoc, Category.assoc, Over.w]
      rw [← Over.w (fst (TFK (R := R) F) C.A.A), ← Category.assoc, hf1,
        ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nfB]

end GlobalTheory.ThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommTranslation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.Mum

theorem tensorLeft_hom_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} {a b : Z ⟶ (X ⊗ Y).left}
    (h1 : a ≫ (fst X Y).left = b ≫ (fst X Y).left) (h2 : a ≫ (snd X Y).left = b ≫ (snd X Y).left) : a = b :=
  pullback.hom_ext h1 h2

theorem trait_transl_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2 x' x hx
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) := by
    have := (ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart
    simpa only [Category.assoc] using this
  have gC := C.α_cart
  have hxx : x.left ≫ C.α = x'.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    have e1 : x.left = (ptSecT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    have e2 : x'.left = (ptSecT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [e1, ← hx, Category.assoc, Category.assoc, hf2, ← Category.assoc, ← Category.assoc, ← e2]
    simp only [Category.assoc]
  have hbase : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have a1 : (TFK (R := R) F ⊗ C.A.A).hom = (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom := (Over.w _).symm
    have a2 : (TFK (R := W) F ⊗ T.A.A).hom = (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom := (Over.w _).symm
    have w := gT.1.w
    simp only [Category.assoc] at w
    rw [a1, a2, Category.assoc, Category.assoc, ← gC.1.w, reassoc_of% hf2, w]
  apply tensorLeft_hom_ext
  · simp only [Category.assoc, ← Over.comp_left, translT, lift_fst, hf1]
  · rw [Category.assoc, Category.assoc]
    apply gC.1.hom_ext
    · have eL : (translT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
          ((pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x)) * (pushPt gC.1.w (snd (TFK (R := R) F) C.A.A))).left := by
        rw [gC.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      have eR : (translT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫
          pullback.fst T.G.hom (jK W) ≫ T.β =
          ((pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x')) * (pushPt gT.1.w (snd (TFK (R := W) F) T.A.A))).left := by
        rw [gT.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
        Over.homMk f hbase
      have e0 : ρ ≫ pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x) = pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x') := by
        ext
        show f ≫ (fst (TFK (R := R) F) C.A.A ≫ x).left ≫ C.α = (fst (TFK (R := W) F) T.A.A ≫ x').left ≫ _
        simp only [Over.comp_left, Category.assoc]
        rw [hxx, reassoc_of% hf1]
      have e1 : ρ ≫ pushPt gC.1.w (snd (TFK (R := R) F) C.A.A) = pushPt gT.1.w (snd (TFK (R := W) F) T.A.A) := by
        ext
        exact hf2
      simp only [Category.assoc]
      rw [eL, hf2, eR, ← e0, ← e1, ← MonObj.comp_mul]
      rfl
    · simp only [Category.assoc]
      rw [Over.w (snd (TFK (R := R) F) C.A.A), Over.w (translT C.A.A x), ← Over.w (fst (TFK (R := R) F) C.A.A),
        reassoc_of% hf1, ← Category.assoc, ← Over.comp_left, translT, lift_fst]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioEqOneUnitSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.twistRatio_eq_one_at_unit : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X) (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) ae) (LB.pullGen D.P.L _ _ (gp.s χ) (thick R I e))) → ∀ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (J : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D.P.A.left) → D.P.L.ι) (J' : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val (g.t χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ h) z J * ((∏ k, gv w ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J (((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J' * val (gp.s χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = 1 := by
  intro R _ _ I D D₂ e G _ _ g g₂ β gp w χ₂ χ a h hh hf hcorr z J J' hJ hJ'
  set o := (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G) with ho
  have hom1 : o.left ≫ (thickObj R I e G).hom = 𝟙 _ := Over.w o
  have e1 : o.left ≫ h ≫ (thickObj R I e G).hom = 𝟙 _ := by rw [hh, hom1]
  have f1 : (Over.map (thick R I e)).map o ≫ fstG I e G = 1 := by
    have := GlobalTheory.FormalPoint.map_mul_fstG (R := R) (I := I) (e := e) (G := G) o o
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  let T := (Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))))
  have tu : (toUnit T).left = thick R I e := by
    have := Over.w (toUnit T)
    simpa [T] using this
  have e2 : o.left ≫ h ≫ (fstG I e G).left = thick R I e ≫ a.left := by
    rw [hf]
    show ((Over.map (thick R I e)).map o ≫ fstG I e G ≫ ((toUnit G ≫ a) * 𝟙 G)).left = _
    rw [← Category.assoc, f1, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, _root_.mul_one,
      Over.comp_left, tu]
  have hc := hcorr (o.left ≫ h) (by simpa [Category.assoc] using e1) (by simpa [Category.assoc] using e2)
  have va := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at va
  have vb : val (g₂.t χ₂) o.left z J' = 1 := GlobalTheory.TorusCoord.val_unit g₂ χ₂ hJ'
  let f : (_ ⟶ D₂.P.A.left) → _ := fun ψ => gv w ψ z (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ψ)
  have e0 : ∀ k, o.left ≫ D₂.Oφ g₂.pG χ₂ k = D₂.Oφ (1 : T ⟶ D₂.P.A) χ₂ k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R I e)).map o) g₂.pG χ₂ k).trans
      (congrArg (D₂.Oφ · χ₂ k) (GlobalTheory.TorusCoord.im_one g₂))
  have vc : (∏ k, f (o.left ≫ D₂.Oφ g₂.pG χ₂ k) ^ Oinvε k) = 1 := by
    refine (Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_
    rw [Fin.prod_univ_four]
    show f ((1 : T ⟶ D₂.P.A) * (toUnit T ≫ D₂.c χ₂)).left ^ (-1 : ℤ) * f (toUnit T ≫ D₂.c χ₂).left ^ (1 : ℤ) *
      f (1 : T ⟶ D₂.P.A).left ^ (1 : ℤ) * f (1 : T ⟶ D₂.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have vc' : (∏ k, gv w (o.left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((o.left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (o.left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) = 1 := vc
  rw [vc', vb, ← Category.assoc, hom1, Category.id_comp, va, _root_.one_mul, _root_.one_mul, mul_inv_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowOverAbelianParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem over₀_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a b h e
  let P := Over.pullback (thick R I e)
  have := (U₀.gt e).q_hom
  let fG : (G ⟶ G₀) →* (P.obj G ⟶ P.obj G₀) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  let fB : (D.toPre.P.A ⟶ D₀.toPre.P.A) →* (P.obj D.toPre.P.A ⟶ P.obj D₀.toPre.P.A) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  have hG : P.map (∏ i, a i ^ n i) = ∏ i, P.map (a i) ^ n i :=
    (map_prod fG _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fG _ _)
  have hB : P.map (∏ i, b i ^ n i) = ∏ i, P.map (b i) ^ n i :=
    (map_prod fB _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fB _ _)
  show P.map (∏ i, a i ^ n i) ≫ (U₀.gt e).q = (U.gt e).q ≫ P.map (∏ i, b i ^ n i)
  rw [hG, hB, prod_zpow_comp, comp_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [h i e]

end GlobalTheory.Mum.PowData
end

