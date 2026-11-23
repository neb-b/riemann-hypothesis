module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Lemmata.GeneralBFactFurther.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen

variable {V : Type} [CommRing V] [IsDomain V]

theorem isLocalization_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.general_b_fact_further.goal1 .. | (apply Bl.general_b_fact_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_further.goal1 <;> assumption)

theorem isOpenImmersion_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsOpenImmersion (spMap (algebraMap V (FractionRing V))) := by
  have := isLocalization_frac hϖ
  let e := IsLocalization.algEquiv (Submonoid.powers ϖ) (Localization.Away ϖ) (FractionRing V)
  have he : algebraMap V (FractionRing V) =
      (e : Localization.Away ϖ →+* FractionRing V).comp (algebraMap V (Localization.Away ϖ)) :=
    RingHom.ext fun x => (e.commutes x).symm
  have : IsIso (CommRingCat.ofHom (e : Localization.Away ϖ →+* FractionRing V)) :=
    ⟨⟨CommRingCat.ofHom (e.symm : FractionRing V →+* Localization.Away ϖ), by ext x; simp, by ext x; simp⟩⟩
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem opensRange_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    haveI := isOpenImmersion_frac hϖ
    (spMap (algebraMap V (FractionRing V))).opensRange =
      (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) := by
  have := isLocalization_frac hϖ
  rw [basicOpen_eq_of_affine]
  ext1
  exact PrimeSpectrum.localization_away_comap_range (FractionRing V) ϖ

theorem eq_zero_of_mul {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p] {r : V} (hr : r ≠ 0) (f : Γ(X, ⊤))
    (h : p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv r) * f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x hx => ?_
  show X.presheaf.germ ⊤ x hx f = X.presheaf.germ ⊤ x hx 0
  set r' := (Scheme.ΓSpecIso (CommRingCat.of V)).inv r with hr'def
  have hr' : r' ≠ 0 := by
    intro h0
    apply hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom h0
    rwa [hr'def, Iso.inv_hom_id_apply, map_zero] at this
  set g := (Sp V).presheaf.germ ⊤ (p.base x) trivial r' with hgdef
  have hg : g ≠ 0 := fun h0 =>
    hr' (germ_injective_of_isIntegral (Sp V) (U := ⊤) (p.base x) trivial (h0.trans (map_zero _).symm))
  let := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (X.presheaf.stalk x) := Flat.stalkMap p x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hg)
  have key : (p.stalkMap x).hom g * X.presheaf.germ ⊤ x hx f = 0 := by
    have h1 : (p.stalkMap x).hom g = X.presheaf.germ ⊤ x hx (p.appTop r') :=
      Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial r'
    rw [h1]
    show X.presheaf.germ ⊤ x hx (p.appTop r') * X.presheaf.germ ⊤ x hx f = 0
    rw [← map_mul, h, map_zero]
  have h2 : g • X.presheaf.germ ⊤ x hx f = g • 0 := by
    rw [smul_zero, Algebra.smul_def]
    exact key
  rw [hreg h2, map_zero]

theorem restrict_basicOpen_injective {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (hs : ∀ f : Γ(X, ⊤), s * f = 0 → f = 0) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op) := by
  have := isLocalization_basicOpen_of_qcqs (X := X) (U := ⊤) (by simpa using isCompact_univ)
    (by simpa using isQuasiSeparated_univ) s
  have hM : Submonoid.powers s ≤ nonZeroDivisors Γ(X, ⊤) :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_iff_right.2 fun f hf => hs f (by rwa [mul_comm] at hf))
  exact IsLocalization.injective (Γ(X, X.basicOpen s)) hM

theorem appTop_fst_injective [IsDiscreteValuationRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p]
    [QuasiCompact p] [QuasiSeparated p] :
    haveI := isOpenImmersion_frac (IsDiscreteValuationRing.exists_irreducible V).choose_spec
    Function.Injective (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  haveI := isOpenImmersion_frac hϖ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  set s := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) with hs
  have hrange : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ = X.basicOpen s := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackFst, opensRange_frac hϖ,
      Scheme.preimage_basicOpen_top]
  have hfac : (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop =
      X.presheaf.map (homOfLE le_top : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ ⟶ ⊤).op ≫
        ((pullback.fst p (spMap (algebraMap V (FractionRing V)))).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE _
  have hinj := restrict_basicOpen_injective s (fun f hf => eq_zero_of_mul p hϖ.ne_zero f hf)
  have hW : ∀ (W : X.Opens), W = X.basicOpen s →
      Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
    rintro W rfl
    exact hinj
  rw [hfac]
  intro a b hab
  simp only [CategoryTheory.comp_apply] at hab
  exact hW _ hrange ((ConcreteCategory.bijective_of_isIso _).1 hab)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrPowers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullPowIso {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) :
    ∀ n : ℕ, (Over.pullback f).obj (powObj G n) ≅ powObj ((Over.pullback f).obj G) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback f)).symm
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback f) G (powObj G n)).symm ≪≫
      whiskerLeftIso ((Over.pullback f).obj G) (pullPowIso f G n)

theorem bijective_of_iso {S' : Scheme.{0}} {A B : Over S'} (e : A ≅ B)
    (h : Function.Bijective B.hom.appTop.hom) : Function.Bijective A.hom.appTop.hom := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  rw [hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ h
  refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.left.appTop).hom, fun x => ?_, fun x => ?_⟩
  · show (e.hom.left.appTop ≫ e.inv.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
    simp
  · show (e.inv.left.appTop ≫ e.hom.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.hom_inv_id]
    simp

theorem pull_powObj_globalFns (hGF : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (G : Over S) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    [IsProper ((Over.pullback f).obj G).hom] (n : ℕ) :
    Function.Bijective ((Over.pullback f).obj (powObj G n)).hom.appTop.hom := by
  exact bijective_of_iso (pullPowIso f G n)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.globalFns_powObj hGF ((Over.pullback f).obj G)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f := f) (G := G) hG) n)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

def PullCubCompSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → m'.IsPullCubical c'' c' → n.IsPullCubical c'' c

def PullCubCancelSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → n.IsPullCubical c'' c → m'.IsPullCubical c'' c'

def SABCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (m' : SABMap t'' t' g),
    ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ

def SABCancelSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)),
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ

def AbLocusOneSt : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (K : Type) [Field K] (t : Sp K ⟶ S),
    IsProper (pullback.snd G.hom t) → Set.range t ⊆ abLocus G

def ProjProperSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProjOver f → IsProper f

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

