module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0020
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralPointsEqOfGeneric
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem coordTie_points_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' :=
  @PositivityTheory.Xgn.same_generic_point_charts

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerAtOneCompEndo
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem isDerAtOne_comp_endo : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (B : L →ₗ[R] L), M.IsDiffOf a B → ∀ (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → ∀ (f : T → R) (w : Module.Dual R L), Γ.IsDerAtOne i M N f w → Γ.IsDerAtOne i M N (fun t => f (α t)) (w ∘ₗ B) :=
  @PositivityTheory.Xgn.isDerAtOne_comp_of_isDiffOf

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDivisible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue

theorem sc_res {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (d : R) :
    (X.presheaf.map (homOfLE h).op).hom (sc π U d) = sc π V d := by
  have e := Scheme.Hom.appLE_map π (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  simp only [sc, RingHom.comp_apply]
  exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) e

theorem sc_ne_zero {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) {V : X.Opens}
    [Nonempty V] {d : R} (hd : sc π ⊤ d ≠ 0) : sc π V d ≠ 0 := by
  intro h
  apply hd
  have hi := map_injective_of_isIntegral X (homOfLE (le_top : V ≤ ⊤))
  apply hi
  have := sc_res π (le_top : V ≤ ⊤) d
  rw [map_zero]
  exact this.trans h

theorem sc_cancel {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) {a b : Γ(X, V)} (h : sc π V d * a = sc π V d * b) : a = b := by
  by_cases hV : Nonempty V
  · exact mul_left_cancel₀ (sc_ne_zero π hd) h
  · have : V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV ⟨⟨x, hx⟩⟩
    subst this
    exact Subsingleton.elim _ _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) (x : Γ(X, V))
    (h : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom x = sc π W d * a) :
    ∃ y : Γ(X, V), x = sc π V d * y := by
  let I := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : I → X.Opens := fun i => (i.1 : X.Opens)
  choose g hg using fun i : I => h (U i) i.2 i.1.2
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    apply sc_cancel π _ hd
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, sc_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (sc π V d * (show Γ(X, V) from s))
  rw [hg i, map_mul, sc_res]
  exact congrArg _ (hs i).symm

theorem exists_sec_of_local {X : Scheme.{0}} [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X)
    (s : LB.Sec M) (δ : R) (hδ : sc π ⊤ δ ≠ 0)
    (h : ∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) :
    ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  choose y hy using fun i => exists_div π (M.U i) hδ (s.f i) (h i)
  refine ⟨⟨y, fun i j => ?_⟩, hy⟩
  apply sc_cancel π _ hδ
  have e := s.compat i j
  rw [hy i, hy j, map_mul, map_mul, sc_res, sc_res] at e
  rw [e]
  ring

theorem sec_eq_smul_of_local : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X) (s : LB.Sec M) (δ : R), sc π ⊤ δ ≠ 0 → (∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W → ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) → ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  intro X _ R _ π M s δ hδ h
  exact exists_sec_of_local R π M s δ hδ h

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ObjMapComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_exists_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' S'' : Scheme.{0}) (s' : S' ⟶ Sp B) (s'' : S'' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (o'' : Obj D l b s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f) (m' : ObjMap o'' o' f'), ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  intro E _ _ _ H D l B _ b S s S' S'' s' s'' o o' o'' f f' m m'
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  refine ⟨{ toSABMap := n, eta := fun x => ?_, etaA := fun x => ?_ }, hn⟩
  · rw [hn', ← Category.assoc, m'.eta, Category.assoc, m.eta, Category.assoc]
  · rw [hn', ← Category.assoc, m'.etaA, Category.assoc, m.etaA, Category.assoc]

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchBoundaryUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_patch_boundary_units : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ) (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ), IsCptGen ξ → (∀ q ∈ B, Char0 ξ q) → h ∈ Mdl.chartQ x c → h ≠ 0 → (∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h → (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω))) → Char0 ξ p → InChart ξ x c p → unitAt ξ p h → p ∉ B → ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpMapEqFromSpecStalk
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.StalkPt

theorem spMap_eq_fromSpecStalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (U : X.Opens), IsAffineOpen U → ∀ (R : Type) [CommRing R] (φ : R →+* Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap φ ≫ x = ξ → (∀ z, x z ∈ U) → ∀ (q : Cpt ξ), q.1 ∈ U → ∀ ψ : R →+* X.presheaf.stalk q.1, (genMap ξ q).comp ψ = φ → spMap ψ ≫ x = X.fromSpecStalk q.1 :=
  @PositivityTheory.Xgn.stalk_point_factorization

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.StalkPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem aeval_const_mul {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℤ R] {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (κ : R) (a : σ → R) :
    aeval (fun j => κ * a j) G = κ ^ n * aeval a G := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = n := by
    have h := hG (mem_support_iff.1 hm)
    have e : Finsupp.weight (1 : σ → ℕ) m = ∑ i, m i := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [← e]
    exact h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_homog {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (c₀ : σ) (h1 : r c₀ = 1)
    (t : Algebra.adjoin ℚ (Set.range r)) :
    ∃ (m : ℤ) (n : ℕ) (G : MvPolynomial σ ℤ), m ≠ 0 ∧ G.IsHomogeneous n ∧
      aeval r G = (m : Ω) * (t : Ω) := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, 1, X j, one_ne_zero, isHomogeneous_X _ _, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [map_intCast, eq_intCast, eq_ratCast, Int.cast_natCast]
    rw [Rat.cast_def]
    field_simp
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add (f := _), map_mul, map_pow, aeval_X, h1, one_pow, mul_one, eq_intCast, map_intCast, e₁, e₂]
      push_cast
      ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, G₁ * G₂, mul_ne_zero hm₁ hm₂, hG₁.mul hG₂, ?_⟩
    simp only [map_mul, e₁, e₂]
    push_cast
    ring

theorem smooth_away_mul {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by
  let S := Localization.Away s
  let T := Localization.Away (algebraMap B S u)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (algebraMap B S u)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans e 0 ℚ S T
  rw [zero_add] at h
  haveI : IsLocalization.Away (s * u) T := IsLocalization.Away.mul' S T s u
  let f : T ≃ₐ[B] Localization.Away (s * u) :=
    IsLocalization.algEquiv (Submonoid.powers (s * u)) T (Localization.Away (s * u))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv e (f.restrictScalars ℚ)

theorem eval_map_int {σ : Type} (w : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))

theorem blockRatio_eq (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (p : Σ k, ι k) [DecidableEq K] :
    y p / y ⟨p.1, E c₀ p.1⟩ =
      (∏ k, y ⟨k, E (E.symm (Function.update (E c₀) p.1 p.2)) k⟩) / ∏ k, y ⟨k, E c₀ k⟩ := by
  obtain ⟨k₀, i⟩ := p
  simp only [Equiv.apply_symm_apply]
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  rw [div_eq_div_iff (hc k₀) h0,
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, E c₀ k⟩) (Finset.mem_univ k₀),
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, Function.update (E c₀) k₀ i k⟩) (Finset.mem_univ k₀)]
  have e : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, Function.update (E c₀) k₀ i k⟩ =
      ∏ k ∈ Finset.univ.erase k₀, y ⟨k, E c₀ k⟩ :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e, Function.update_self]
  ring

theorem aeval_blockRatio_mem [CharZero Ω] (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (β : MRing ι) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ∈
      Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) := by
  classical
  induction β using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem _ n
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    refine mul_mem hp (Algebra.subset_adjoin ⟨E.symm (Function.update (E c₀) i.1 i.2), ?_⟩)
    exact (blockRatio_eq y E c₀ hc i).symm

theorem aeval_eq_prod_mul (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b) :
    aeval y β = (∏ k, y ⟨k, E c₀ k⟩ ^ b k) *
      aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := by
  have h := GlobalTheory.CompanionTheory.Ar.aeval_blockScale hb (fun k => y ⟨k, E c₀ k⟩) (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩)
  have e : (fun p : Σ k, ι k => y ⟨p.1, E c₀ p.1⟩ * (y p / y ⟨p.1, E c₀ p.1⟩)) = y :=
    funext fun p => mul_div_cancel₀ _ (hc p.1)
  rwa [e] at h

theorem mConeMap_segre (j : Fin (N + 1)) :
    mConeMap y (∏ k, (X ⟨k, E j k⟩ : MRing ι)) =
      (∏ k, (X k : MvPolynomial K Ω)) * C (∏ k, y ⟨k, E j k⟩) := by
  simp only [map_prod, mConeMap, aeval_X, Finset.prod_mul_distrib]
  rw [mul_comm]

theorem vanish_of_value (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b)
    {n : ℕ} {m : ℤ} {G : MvPolynomial (Fin (N + 1)) ℤ} (hG : G.IsHomogeneous n)
    (hval : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G =
      (m : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hβ : evC z β = 0) :
    (∏ k, z ⟨k, E c₀ k⟩) = 0 ∨ aeval (fun j => ∏ k, z ⟨k, E j k⟩) G = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hx : aeval (fun j => ∏ k, y ⟨k, E j k⟩) G * ∏ k, y ⟨k, E c₀ k⟩ ^ b k =
      (m : Ω) * aeval y β * (∏ k, y ⟨k, E c₀ k⟩) ^ n := by
    have e : (fun j => ∏ k, y ⟨k, E j k⟩) = fun j => (∏ k, y ⟨k, E c₀ k⟩) *
        ((∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :=
      funext fun j => (mul_div_cancel₀ _ h0).symm
    rw [e, aeval_const_mul hG, hval, aeval_eq_prod_mul y E c₀ hc hb]
    ring
  let P₁ : MRing ι := aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G * ∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k
  let P₂ : MRing ι := C m * β * (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι)) ^ n
  have hmem : P₁ - P₂ ∈ mCoordIdeal y := by
    refine RingHom.mem_ker.2 ?_
    have hG' : mConeMap y (aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G) =
        (∏ k, (X k : MvPolynomial K Ω)) ^ n * C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) := by
      rw [comp_aeval_apply]
      simp only [mConeMap_segre]
      rw [aeval_const_mul hG]
      congr 1
      exact (comp_aeval_apply _ (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) G).symm
    have hX : mConeMap y (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k) =
        (∏ k, (X k : MvPolynomial K Ω) ^ b k) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k) := by
      simp only [map_prod, map_pow, mConeMap, aeval_X, mul_pow, Finset.prod_mul_distrib]
      rw [mul_comm]
    have hC : mConeMap y (C m) = C (m : Ω) := by
      simp [mConeMap]
    have hS := mConeMap_segre y E c₀
    simp only [P₁, P₂, map_sub, map_mul, map_pow, hG', hX, hC, hS,
      GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog y hb]
    rw [sub_eq_zero]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hx
    simp only [map_mul, map_pow] at this
    calc _ = (∏ k, (X k : MvPolynomial K Ω)) ^ n * (∏ k, (X k : MvPolynomial K Ω) ^ b k) *
          (C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k)) := by ring
      _ = _ := by rw [this]; ring
  have hzero := hz.2 _ hmem
  have hev : aeval z (P₁ - P₂) = 0 := by rw [← eval_map_int]; exact hzero
  have hβ' : aeval z β = 0 := by rw [← eval_map_int]; exact hβ
  have hP : aeval (fun j => ∏ k, z ⟨k, E j k⟩) G * ∏ k, z ⟨k, E c₀ k⟩ ^ b k = 0 := by
    simp only [P₁, P₂, map_sub, map_mul, map_pow, map_prod, aeval_X, hβ', comp_aeval_apply] at hev
    simpa using hev
  rcases mul_eq_zero.1 hP with h | h
  · exact Or.inr h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine Or.inl (Finset.prod_eq_zero_iff.2 ⟨k, Finset.mem_univ _, ?_⟩)
    by_contra h'
    exact pow_ne_zero _ h' hk

end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm


open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes in
theorem GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  intro Ω _ _ K _ ι _ y e β b hb hβ N E c₀ hc s hs _
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have h1 : (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) c₀ = 1 := div_self h0
  obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := SegreForm.exists_homog _ c₀ h1 s
  obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := SegreForm.exists_homog _ c₀ h1
    ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩
  have hbt : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ≠ 0 := by
    intro h
    apply hβ
    rw [form_mem_mCoordIdeal_iff y hb, SegreForm.aeval_eq_prod_mul y E c₀ hc hb, h, mul_zero]
  have hm₁' : (m₁ : Ω) ≠ 0 := by exact_mod_cast hm₁
  have hm₂' : (m₂ : Ω) ≠ 0 := by exact_mod_cast hm₂
  have hs' : (s : Ω) ≠ 0 := fun h => hs (Subtype.ext h)
  refine ⟨n₁ + n₂, X c₀ * G₁ * G₂,
    s * (((m₁ * m₂ : ℤ) : Algebra.adjoin ℚ _) * ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩),
    ?_, ?_, ?_, ?_, SegreForm.smooth_away_mul s _ e, ?_⟩
  · have := ((isHomogeneous_X ℤ c₀).mul hG₁).mul hG₂
    convert this using 1
    ring
  · rw [mul_assoc]
    exact dvd_mul_right _ _
  · have e₂' : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G₂ =
        (m₂ : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := e₂
    rw [map_mul, map_mul, aeval_X, e₁, e₂', div_self h0]
    push_cast
    ring
  · intro h
    have h' := congrArg (Subtype.val) h
    have h'' : (s : Ω) * (((m₁ : Ω) * m₂) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β) = 0 := by
      simpa using h'
    exact mul_ne_zero hs' (mul_ne_zero (mul_ne_zero hm₁' hm₂') hbt) h''
  · intro z hz hzβ
    rw [SegreForm.eval_map_int, map_mul, map_mul, aeval_X]
    rcases SegreForm.vanish_of_value y E c₀ hc hb hG₂ e₂ hz hzβ with h | h
    · simp only [h, zero_mul]
    · simp only [h, mul_zero]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_appellHumbert_frame_of_cubical :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  intro A _ _ Lr cs g u₀
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hT := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hT A _ Lr.L g u₀ Lr.isLB cs.t cs.isGen _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u₀.Λ u₀.discrete u₀.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u₀.ex, ex_add := u₀.ex_add, ex_onto := u₀.ex_onto, Λ := u₀.Λ, ker := u₀.ker,
            discrete := u₀.discrete, full := u₀.full, hol := u₀.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSubgroupBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChange

theorem torsion_isBaseChange : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F :=
  @PositivityTheory.Xgn.torsion_group_base_change

end GlobalTheory.CompanionTheory.Ar.BT.BaseChange
end

