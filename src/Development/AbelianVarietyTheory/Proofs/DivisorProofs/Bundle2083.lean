module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem tri_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {S : Type} [CommRing S] {φ : c.F →+* S} (z : Sp S ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') (g g' : EigFrame Y φ (z ≫ π)) (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') : ∃ d, g.Tri (RingHom.id S) g' d := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have h1 : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => F.TAt k k' z hh (some ⟨τ, i⟩), by rw [h2, Category.id_comp], rfl, fun τ i =>
    ⟨fun j => (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) j i, rfl, fun j hj => F.B_map_tri k k' τ _ hj, ?_⟩⟩
  simp only [h1, Category.id_comp]
  have e : (fun j => g.v τ j) = fun j => (tv (F.vecAt k z hz rfl τ j)).left := funext (hg τ)
  rw [e, hg' τ i, GlobalTheory.LieMet.isComb_iff]
  exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i

end GlobalTheory.VarFlag

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_congr {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x x' : Sp K ⟶ Y.X} (h : x = x') (g : EigFrame Y φ x) (g' : EigFrame Y φ x')
    (hv : ∀ τ i, g.v τ i = g'.v τ i) (p : Sp K ⟶ C.Y.X) : C.Carries p g ↔ C.Carries p g' := by
  subst h
  obtain ⟨v, a1, a2, a3⟩ := g
  obtain ⟨v', b1, b2, b3⟩ := g'
  have e : v = v' := funext fun τ => funext fun i => hv τ i
  subst e
  rfl

theorem carries_of_tri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {g' : EigFrame Y φ' x'}
    {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h : g.Tri (RingHom.id K) g' d) {p : Sp K ⟶ C.Y.X}
    (hp : C.Carries p g) : C.Carries p g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  exact ⟨y, ψ, φ₁, f, t, _, h1, h2, GlobalTheory.ShFam.FlatSec.tri_trans h3 h⟩

theorem carries_over {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {p : Sp K ⟶ C.Y.X} (hp : C.Carries p g) :
    p ≫ C.π ≫ genι Y = x := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  rw [h1, Category.assoc, ← h3.1]

theorem uniq_rel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hlifts hbar K _ z
  set zz := z ≫ GlobalTheory.CompHS.inc₀ X Z with hzz

  let φ : c.F →+* K := (Spec.preimage (zz ≫ X.π ≫ Y.s)).hom
  have hφ : zz ≫ X.π ≫ Y.s = spMap φ := (Spec.map_preimage _).symm

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover zz
  obtain ⟨g, hg⟩ := hFE K φ zz k hk hφ

  let xg : Sp K ⟶ gen Y := zz ≫ X.π ≫ inv (genι Y)
  have hxg : xg ≫ genι Y = zz ≫ X.π := by simp [xg]
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hstr : xg ≫ genStr Y = spMap φ := by
    have e : genStr Y = genι Y ≫ Y.s := by
      calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
        _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
    rw [e, ← Category.assoc, hxg, Category.assoc, hφ]

  have hr : Set.range xg ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    refine (hbar _).1 ?_
    have e : genι Y (xg a) = X.π (GlobalTheory.CompHS.inc₀ X Z (z a)) := by
      rw [← Scheme.Hom.comp_apply, hxg]; rfl
    rw [e]
    have hm : GlobalTheory.CompHS.inc₀ X Z (z a) ∈ X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z := by
      have := (Scheme.Opens.range_ι (X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z)).le ⟨z a, rfl⟩
      exact this
    exact hm
  let x' := IsOpenImmersion.lift j xg hr
  have hx' : x' ≫ j = xg := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ (xg ≫ genι Y), ∀ τ i, g0.v τ i = g.v τ i := by
    rw [hxg]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨p, ⟨hp1, hp2⟩, hpu⟩ := hlifts K φ xg x' hx' hstr g0
  refine ⟨p, ⟨φ, k, hk, g, hφ, hg, (carries_congr C hxg g0 g hg0 p).1 hp2⟩, ?_⟩
  rintro p' ⟨φ', k', hk', g', hφ', hg', hc'⟩
  have e : φ' = φ := by
    have h0 : spMap φ' = spMap φ := hφ'.symm.trans hφ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst e
  obtain ⟨d, hd⟩ := tri_of_isFrameAt X.F zz k' k hk' hk g' g hg' hg
  have hc : C.Carries p' g := carries_of_tri C hd hc'
  have hc0 : C.Carries p' g0 := (carries_congr C hxg g0 g hg0 p').2 hc
  refine hpu p' ⟨?_, hc0⟩
  have h1 : p' ≫ C.π = xg := by
    rw [← cancel_mono (genι Y), Category.assoc]
    exact carries_over C hc0
  rw [← cancel_mono j, Category.assoc, ← hπ, h1, hx']

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag.LQF

theorem finite_preimage_of_finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (H : {z : Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ X | z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y}.Finite) : (f ⁻¹' {y}).Finite := by
  let k := Y.residueField y
  let K := AlgebraicClosure k
  let pt : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have hcl : closedPoints (f.fiber y) ⊆ f.fiberι y ⁻¹' ((fun z : Spec (CommRingCat.of K) ⟶ X => z pt) '' {z |
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Y.fromSpecResidueField y}) := by
    intro w hw
    have hw' : IsClosed ({w} : Set (f.fiber y)) := hw
    have h1 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w) :=
      isClosed_singleton_iff_locallyOfFiniteType.1 hw'
    have h0 : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹LocallyOfFiniteType f›
    have h2 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) := inferInstance
    have h3 : IsFinite ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 h2
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y)
    have h4 : φ.hom.Finite := by
      rw [← IsFinite.SpecMap_iff, hφ]; exact h3
    letI : Algebra k ((f.fiber y).residueField w) := φ.hom.toAlgebra
    haveI : Module.Finite k ((f.fiber y).residueField w) := h4
    haveI : Algebra.IsAlgebraic k ((f.fiber y).residueField w) := Algebra.IsIntegral.isAlgebraic
    let ι : (f.fiber y).residueField w →ₐ[k] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (f.fiber y).fromSpecResidueField w ≫ f.fiberι y, ?_, ?_⟩
    · show _ = _
      rw [Category.assoc, Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc ((f.fiber y).fromSpecResidueField w),
        ← hφ, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      exact ι.commutes a
    · show (Spec.map _ ≫ _ ≫ _) pt = _
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hfin : (closedPoints (f.fiber y)).Finite :=
    ((H.image _).preimage (f.fiberι y).isEmbedding.injective.injOn).subset hcl
  have huniv : (Set.univ : Set (f.fiber y)) = closedPoints (f.fiber y) := by
    have hc : IsClosed (closedPoints (f.fiber y)) := by
      rw [← Set.biUnion_of_singleton (closedPoints (f.fiber y))]
      exact hfin.isClosed_biUnion fun x hx => hx
    rw [← JacobsonSpace.closure_inter_closedPoints isClosed_univ, Set.univ_inter, hc.closure_eq]
  haveI : Finite (f.fiber y) := Set.finite_univ_iff.1 (huniv ▸ hfin)
  rw [← Scheme.Hom.range_fiberι]
  exact Set.finite_range _

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan initSpan_le_of_tri)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_sum_of_isCombAtG {Y : Model Xo c (RingHom.id c.F)} {K : Type} [Field K] {x x' : Sp K ⟶ Y.X} (e : x' = x)
    {m : ℕ} (u : Fin m → TanM x Y.t.G) (cf : Fin m → K) (w : TanM x Y.t.G)
    (h : IsCombAtG Y.t x' (fun j => (tv (u j)).left) cf (tv w).left) : w = ∑ j, cf j • u j := by
  subst e
  exact (GlobalTheory.LieMet.isComb_iff u cf w).1 h

theorem vecAt_left {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {K : Type}
    [Field K] (k : F.J) (z : Sp K ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (i : Fin (Dw.mult σ)) : (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx; rfl

theorem initSpan_le_of_frameTri {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {K : Type} [Field K] {φ φ' : c.F →+* K} (z z' : Sp K ⟶ Z) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x)
    (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k') (g : EigFrame Y φ (z ≫ π))
    (g' : EigFrame Y φ' (z' ≫ π)) (hg : IsFrameAt F z k hz g) (hg' : IsFrameAt F z' k' hz' g')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (ht : g.Tri (RingHom.id K) g' t) (σ : E →+* ℂ) (i : ℕ) :
    initSpan K (F.vecAt k' z' hz' hx' σ) i ≤ initSpan K (F.vecAt k z hz hx σ) i := by
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have ex : ∀ j : Fin (Dw.mult σ), ∃ cf : Fin (Dw.mult σ) → K, (∀ k, j < k → cf k = 0) ∧
      F.vecAt k' z' hz' hx' σ j = ∑ a, cf a • F.vecAt k z hz hx σ a := fun j => by
    obtain ⟨cf, -, hcf, hc⟩ := ht.2.2 σ j
    refine ⟨cf, hcf, eq_sum_of_isCombAtG hx' _ cf _ ?_⟩
    have e1 : (fun a => spMap (dualMap (RingHom.id K)) ≫ g.v σ a) =
        fun a => (tv (F.vecAt k z hz hx σ a)).left := funext fun a => by
      rw [h1, Category.id_comp, hg σ a, vecAt_left F k z hz hx σ a]
    rw [e1, hg' σ j, ← vecAt_left F k' z' hz' hx' σ j] at hc
    exact hc
  choose cf hcf e using ex
  exact initSpan_le_of_tri (B := Matrix.of fun a j => cf j a) (fun j a h => hcf a j h) e i

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.CompHS (Y₀ inc₀)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_base {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Y φ x} (h : C.Carries p g) :
    x = p ≫ C.π ≫ GlobalTheory.Toroidal.genι Y := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, -, htri⟩ := h
  rw [htri.1, hp, Category.assoc]

theorem tri_of_carries {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) (hC : CarriesTri C)
    {K : Type} [Field K] {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} (e : x = x') {p : Sp K ⟶ C.Y.X}
    (g : EigFrame Y φ x) (g' : EigFrame Y φ' x') (h : C.Carries p g) (h' : C.Carries p g') :
    ∃ t, g.Tri (RingHom.id K) g' t := by
  subst e
  exact hC K φ φ' x p g g' h h'

theorem finite_points {Y : Model Xo c (RingHom.id c.F)} (X : FlagModel Y) (C : FlagCpt Y (RingEquiv.refl c.F))
    (hC : CarriesTri C) (Z : Formalism.L2.Pj.Comp Xo c) (h : Y₀ X.toFlagCover Z ⟶ C.Y.X)
    (hR : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ X.toFlagCover Z), Rel X.F C (z ≫ inc₀ X.toFlagCover Z) (z ≫ h))
    (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ C.Y.X) : {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p} with h0 | ⟨z₁, hz₁⟩
  · rw [h0]; exact Set.finite_empty
  have hfin := X.fin K (z₁ ≫ inc₀ X.toFlagCover Z)
  refine (hfin.preimage (f := fun z => z ≫ inc₀ X.toFlagCover Z)
    (fun a _ b _ e => (cancel_mono (inc₀ X.toFlagCover Z)).1 e)).subset ?_
  intro z hz
  have key : ∀ w : Sp K ⟶ Y₀ X.toFlagCover Z, w ≫ h = p → ∃ (φ : c.F →+* K) (k : X.F.J)
      (hk : ⊤ ≤ (w ≫ inc₀ X.toFlagCover Z) ⁻¹ᵁ X.F.U k)
      (g : EigFrame Y φ ((w ≫ inc₀ X.toFlagCover Z) ≫ X.π)), IsFrameAt X.F _ k hk g ∧ C.Carries p g := by
    intro w hw
    obtain ⟨φ, k, hk, g, -, hg, hc⟩ := hR K w
    exact ⟨φ, k, hk, g, hg, hw ▸ hc⟩
  obtain ⟨φ, k, hk, g, hg, hc⟩ := key z hz
  obtain ⟨φ₁, k₁, hk₁, g₁, hg₁, hc₁⟩ := key z₁ hz₁
  have hx : (z ≫ inc₀ X.toFlagCover Z) ≫ X.π = (z₁ ≫ inc₀ X.toFlagCover Z) ≫ X.π :=
    (carries_base C hc).trans (carries_base C hc₁).symm
  refine ⟨hx, fun σ i => ?_⟩
  obtain ⟨t, ht⟩ := tri_of_carries C hC hx g g₁ hc hc₁
  obtain ⟨t', ht'⟩ := tri_of_carries C hC hx.symm g₁ g hc₁ hc
  rw [X.F.step_eq k _ hk hx, X.F.step_eq k₁ _ hk₁ rfl]
  exact le_antisymm (initSpan_le_of_frameTri X.F _ _ rfl hx k₁ k hk₁ hk g₁ g hg₁ hg t' ht' σ i)
    (initSpan_le_of_frameTri X.F _ _ hx rfl k k₁ hk hk₁ g g₁ hg hg₁ t ht σ i)

end GlobalTheory.VarFlag.LQF

theorem GlobalTheory.VarFlag.locallyQuasiFinite_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagModel Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (h : GlobalTheory.CompHS.Y₀ X.toFlagCover Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X.toFlagCover Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X.toFlagCover Z) (z ≫ h)) → LocallyQuasiFinite h := by
  intro E _ _ _ H Dw l Xo c Y X C hC Z h _ hR
  refine LocallyQuasiFinite.of_finite_preimage_singleton h fun p => ?_
  exact GlobalTheory.VarFlag.LQF.finite_preimage_of_finite_points h p
    (GlobalTheory.VarFlag.LQF.finite_points X C hC Z h hR _ _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLe
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.FlatSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_bounds {PP A M : ℝ} (hH : HostNum D L PP A M) :
    0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hne : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hlog0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := Real.log_nonneg h1
  have hf : (0 : ℝ) < D.R.f := by have := hH.f8; positivity
  have heq : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd, NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 hne), hH.deg]
    push_cast
    ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hH.disc]

theorem abs_flatDegVal_le (p : PtAt ex Csz) (i : Fin D.R.m) {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm| ≤ 9 * D.R.r * L.sc.L := by
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have hpq : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by exact_mod_cast hW.sig.2.2
  have hom := hW.om
  have hL : 10 ≤ L.sc.L := hH.big.2.1
  have hld : Real.log (p.T.Q.H.d : ℝ) ≤ L.sc.L := by rw [hd]; exact hH.logd
  have hld0 : 0 ≤ Real.log (p.T.Q.H.d : ℝ) := Real.log_natCast_nonneg _
  obtain ⟨hr0, hr1⟩ := lrd_bounds hH
  unfold GlobalTheory.FlatLine.flatDegVal
  set a := (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm
  set P : ℝ := ((dat p i).p : ℝ)
  set Q : ℝ := ((dat p i).q : ℝ)
  set u := Real.log (p.T.Q.H.d : ℝ)
  set v := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have h1 : |(P - Q) / 2 * a| ≤ (P + Q) / 2 * (3 * L.sc.L) := by
    rw [abs_mul, abs_div, abs_two]
    refine mul_le_mul ?_ hom (abs_nonneg _) (by positivity)
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |Q * (u - v)| ≤ Q * (2 * L.sc.L) := by
    rw [abs_mul, abs_of_nonneg hQ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hQ
  have h3 := abs_add_le ((P - Q) / 2 * a) (Q * (u - v))
  rw [hpq] at h1
  have hQr : Q ≤ D.R.r := by rw [← hpq]; linarith
  have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hQr (by linarith : (0 : ℝ) ≤ 2 * L.sc.L), mul_nonneg hr (by linarith : (0 : ℝ) ≤ L.sc.L)]

end GlobalTheory.CovTop.FlatSz

namespace GlobalTheory.CovTop.FlatSz

end GlobalTheory.CovTop.FlatSz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem retract_flat_of_finite (R : Type) [CommRing R] (H K : Over (Sp R)) (s : H ⟶ K) (r : K ⟶ H)
    (hsr : s ≫ r = 𝟙 H) (hH : IsFinite H.hom) (hK : IsFinite K.hom) (hKf : Flat K.hom) :
    Flat H.hom := by
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  haveI : IsAffine K.left := isAffine_of_isAffineHom K.hom
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)] at hKf ⊢
  have wr : r.left ≫ H.hom = K.hom := Over.w r
  have ws : s.left ≫ K.hom = H.hom := Over.w s
  have hid : s.left ≫ r.left = 𝟙 H.left := by rw [← Over.comp_left, hsr, Over.id_left]
  letI := H.hom.appTop.hom.toAlgebra
  letI := K.hom.appTop.hom.toAlgebra
  have hKf' : Module.Flat Γ(Sp R, ⊤) Γ(K.left, ⊤) := hKf
  show Module.Flat Γ(Sp R, ⊤) Γ(H.left, ⊤)
  let rs : Γ(H.left, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(K.left, ⊤) :=
    { toFun := r.left.appTop.hom
      map_add' := map_add _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        congr 1
        show (H.hom.appTop ≫ r.left.appTop) a = _
        rw [← Scheme.Hom.comp_appTop, wr]; rfl }
  let ss : Γ(K.left, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(H.left, ⊤) :=
    { toFun := s.left.appTop.hom
      map_add' := map_add _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        congr 1
        show (K.hom.appTop ≫ s.left.appTop) a = _
        rw [← Scheme.Hom.comp_appTop, ws]; rfl }
  refine Module.Flat.of_retract rs ss ?_
  ext x
  show (r.left.appTop ≫ s.left.appTop) x = x
  rw [← Scheme.Hom.comp_appTop, hid]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp_eq_spMap_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (cst p) := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  conv_lhs => rw [h]
  rw [gp]
  erw [Scheme.fromSpecStalk_toSpecΓ_assoc]
  erw [← Spec.map_comp]
  rfl

end GlobalTheory.Desc
end

