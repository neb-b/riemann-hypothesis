module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSections

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl


omit [GrpObj G] in
theorem ringHom_ext_of_mono {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ X) [Mono x] {a b : R →+* A}
    (h : spMap a ≫ x = spMap b ≫ x) : a = b :=
  congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h))

theorem extends_of_tr {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G ξ E) {R : Type} [CommRing R] {x : Sp R ⟶ X} {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1) (hψ : spMap ψ ≫ x = X.fromSpecStalk q.1)
    (j : F → E) (hj : ∀ e, (M.pt (j e)).left = spMap (dualMap ((genMap ξ q).comp ψ)) ≫ (MR.pt e).left) (e : F)
    (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G)
    (hv : v.left = spMap (dualMap ψ) ≫ (MR.pt e).left) : M.Extends q (j e) v := by
  refine ⟨?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom _ _ _).toRingHom) ≫ v.left = _
    rw [hv, ← Category.assoc]
    have h : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q.1) (X.presheaf.stalk q.1) (X.presheaf.stalk q.1)).toRingHom) ≫
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) =
        spMap ψ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      apply RingHom.ext
      intro a
      simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    rw [h, Category.assoc, MR.tan e]
    exact congrArg (·.left) (comp_one (M := G)
      (Over.homMk (spMap ψ) hψ : Over.mk (X.fromSpecStalk q.1) ⟶ Over.mk x))
  · rw [hj, ← spMap_dual_comp, Category.assoc, ← hv]

variable [Smooth G.hom] [IsCommMonObj G]

theorem exists_affine_chart (G : Over X) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (y : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (F : Type) (_ : AddCommGroup F) (_ : Module Γ(X, U) F)
      (_ : LieModel G (R := Γ(X, U)) hU.fromSpec F) (n : ℕ) (_ : Module.Basis (Fin n) Γ(X, U) F), y ∈ U := by
  obtain ⟨R₁, _, x₁, hx₁, F₁, _, _, M₁, n, b₁, hy⟩ := exists_chart G y
  have hU : IsAffineOpen x₁.opensRange := isAffineOpen_opensRange x₁
  let R₀ : Type := Γ(X, x₁.opensRange)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have hr : Set.range x₀ ⊆ Set.range x₁ := by
    change Set.range hU.fromSpec ⊆ _
    rw [hU.range_fromSpec]
    exact subset_of_eq (Scheme.Hom.coe_opensRange x₁)
  let τ : R₁ →+* R₀ := (Spec.preimage (IsOpenImmersion.lift x₁ x₀ hr)).hom
  have hτ : spMap τ ≫ x₁ = x₀ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x₁ x₀ hr)).hom) ≫ x₁ = x₀
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  obtain ⟨F₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R₀ x₀
  obtain ⟨-, B, -, -⟩ := basis_tr τ x₁ x₀ hτ M₁ M₀ b₁
  exact ⟨_, hU, F₀, _, _, M₀, n, B, hy⟩

theorem exists_germs {R : Type} [CommRing R] {x : Sp R ⟶ X} {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) {n : ℕ} (b : Module.Basis (Fin n) R F) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (φ : R →+* Ω) (j : F →ₛₗ[φ] E)
    (hj : ∀ e, (M.pt (j e)).left = spMap (dualMap φ) ≫ (MR.pt e).left) (p : Cpt ξ)
    (ψ : R →+* X.presheaf.stalk p.1) (hψ : spMap ψ ≫ x = X.fromSpecStalk p.1) (hg : (genMap ξ p).comp ψ = φ)
    {c : E} (hc : c ∈ M.lat p) :
    ∃ s : Fin n → X.presheaf.stalk p.1, c = ∑ k, genMap ξ p (s k) • j (b k) := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff p c).1 hc
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨β, Bq, hBq, hβ⟩ := basis_tr (A := X.presheaf.stalk p.1) ψ x (X.fromSpecStalk p.1) hψ MR Mq b
  obtain ⟨jq, hjq⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ξ (genMap ξ p)
    (spec_genMap ξ p) Mq M
  have hcomp : ∀ e, jq (β e) = j e := fun e => LieVB.pt_left_inj M (by
    rw [hjq, hβ, ← Category.assoc, spMap_dual_comp, hg, hj])
  obtain ⟨y, rfl⟩ := Mq.onto v hv.1
  have hy : c = jq y := pt_left_inj M (hv.2.trans (hjq y).symm)
  refine ⟨fun k => Bq.repr y k, ?_⟩
  rw [hy]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← Bq.sum_repr y, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [jq.map_smulₛₗ, hBq, hcomp]

end GlobalTheory.CompanionTheory.Ar.LieSections

namespace GlobalTheory.CompanionTheory.Ar.LieSections

theorem exists_common_denom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) {I : Type} [Finite I]
    (s : I → X.presheaf.stalk y) : ∃ (f : Γ(X, U)) (r : I → Γ(X, U)), y ∈ X.basicOpen f ∧
      ∀ i, (X.presheaf.germ U y hy).hom f * s i = (X.presheaf.germ U y hy).hom (r i) := by
  let u : U := ⟨y, hy⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (u : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf u
  have hloc := hU.isLocalization_stalk u
  obtain ⟨⟨f, hf⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (hU.primeIdealOf u).asIdeal.primeCompl (S := X.presheaf.stalk (u : X)) s
  choose r hr using hint
  refine ⟨f, r, (Scheme.mem_basicOpen _ _ _ hy).2 ?_, fun i => ?_⟩
  · exact IsLocalization.map_units (M := (hU.primeIdealOf u).asIdeal.primeCompl)
      (X.presheaf.stalk (u : X)) ⟨f, hf⟩
  · have := hr i
    rw [Algebra.smul_def] at this
    exact this.symm

end GlobalTheory.CompanionTheory.Ar.LieSections

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieSections in
theorem lieLat_germs_eq_sections : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hN hc
  obtain ⟨U, hU, F₀, _, _, M₀, n, b₀, hpU⟩ := LieSections.exists_affine_chart G p.1
  let R₀ : Type := Γ(X, U)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have hx₀ : IsOpenImmersion x₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : x₀.opensRange = U := hU.opensRange_fromSpec
  have hgen : genPt ξ ∈ x₀.opensRange := p.2.mem_open x₀.opensRange.isOpen (by rw [hrange]; exact hpU)
  obtain ⟨φ₀, hφ₀⟩ := LieVB.exists_lift x₀ ξ hgen
  let ψ₀ : R₀ →+* X.presheaf.stalk p.1 := (X.presheaf.germ U p.1 hpU).hom
  have hψ₀ : spMap ψ₀ ≫ x₀ = X.fromSpecStalk p.1 := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hpU]
    rfl
  have hg : (genMap ξ p).comp ψ₀ = φ₀ := LieSections.ringHom_ext_of_mono x₀ (by
    rw [LieSections.spMap_comp', Category.assoc, hψ₀, hφ₀]
    exact LieTangent.spec_genMap ξ p)
  obtain ⟨j₀, hj₀⟩ := LieVB.exists_tr x₀ ξ φ₀ hφ₀ M₀ M
  choose s hs using fun i => LieSections.exists_germs M₀ b₀ M φ₀ j₀ hj₀ p ψ₀ hψ₀ hg (hc i)
  obtain ⟨f, r, hpf, hr⟩ := LieSections.exists_common_denom hU p.1 hpU (fun ik : J × Fin n => s ik.1 ik.2)
  obtain ⟨g, hgN, hpg⟩ := hU.exists_basicOpen_le (V := N) ⟨p.1, hN⟩ hpU
  let D : X.Opens := X.basicOpen (f * g)
  have hD : IsAffineOpen D := hU.basicOpen (f * g)
  have hDU : D ≤ U := X.basicOpen_le (f * g)
  have hpD : p.1 ∈ D := by
    change p.1 ∈ X.basicOpen (f * g)
    rw [Scheme.basicOpen_mul]
    exact ⟨hpf, hpg⟩
  let R : Type := Γ(X, D)
  let x : Sp R ⟶ X := hD.fromSpec
  have hx : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hD.fromSpec)
  have hxr : x.opensRange = D := hD.opensRange_fromSpec
  let ρ : R₀ →+* R := (X.presheaf.map (homOfLE hDU).op).hom
  have hρ : spMap ρ ≫ x₀ = x := hU.map_fromSpec hD (homOfLE hDU).op
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G R x
  obtain ⟨β, hβ⟩ := LieVB.exists_tr x₀ x ρ hρ M₀ MF
  have hu : IsUnit (ρ (f * g)) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace (f * g)
  obtain ⟨w, hw⟩ : ∃ w : R, ρ f * w = 1 := by
    rw [map_mul] at hu
    exact (isUnit_of_mul_isUnit_left hu).exists_right_inv
  refine ⟨R, inferInstance, x, hx, F, inferInstance, inferInstance, MF,
    fun i => ∑ k, (ρ (r (i, k)) * w) • β (b₀ k), ?_, ?_, fun q ψ hψ i v hv => ?_⟩
  · rw [hxr]; exact hpD
  · rw [hxr]
    have hDg : D = X.basicOpen f ⊓ X.basicOpen g := X.basicOpen_mul f g
    exact (hDg.le.trans inf_le_right).trans hgN
  let φ : R →+* Ω := (genMap ξ q).comp ψ
  have hφ : spMap φ ≫ x = ξ := by
    rw [LieSections.spMap_comp', Category.assoc, hψ]
    exact LieTangent.spec_genMap ξ q
  have hφρ : φ.comp ρ = φ₀ := LieSections.ringHom_ext_of_mono x₀ (by
    rw [LieSections.spMap_comp', Category.assoc, hρ, hφ, hφ₀])
  obtain ⟨j, hj⟩ := LieVB.exists_tr x ξ φ hφ MF M
  have hjβ : ∀ u, j (β u) = j₀ u := fun u => LieVB.pt_left_inj M (by
    rw [hj, hβ, ← Category.assoc, LieVB.spMap_dual_comp, hφρ, hj₀])
  have hjc : j (∑ k, (ρ (r (i, k)) * w) • β (b₀ k)) = c i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [j.map_smulₛₗ, hjβ]
    congr 1
    have h1 : φ (ρ f) * φ w = 1 := by rw [← map_mul, hw, map_one]
    have h2 : φ (ρ (r (i, k))) = φ₀ (r (i, k)) := congrArg (fun t => t (r (i, k))) hφρ
    have h3 : φ (ρ f) = φ₀ f := congrArg (fun t => t f) hφρ
    have h4 : φ₀ f * genMap ξ p (s i k) = φ₀ (r (i, k)) := by
      have := congrArg (genMap ξ p) (hr (i, k))
      rw [map_mul] at this
      have e : ∀ a, genMap ξ p (ψ₀ a) = φ₀ a := fun a => congrArg (fun t => t a) hg
      rw [show (X.presheaf.germ U p.1 hpU).hom f = ψ₀ f from rfl,
        show (X.presheaf.germ U p.1 hpU).hom (r (i, k)) = ψ₀ (r (i, k)) from rfl, e, e] at this
      exact this
    rw [map_mul, h2, ← h4, ← h3, mul_comm (φ (ρ f)), _root_.mul_assoc, h1, _root_.mul_one]
  rw [← hjc]
  exact LieSections.extends_of_tr M MF q ψ hψ j hj _ v hv

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

section Transport

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R']
  {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

theorem exists_lie_transport (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S} (h : spMap c ≫ x = y)
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts S G R R' c x E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  rw [Category.comp_id] at this
  exact this

theorem lie_transport_induction [Smooth G.hom] (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S}
    (h : spMap c ≫ x = y) (M : LieModel G x E) (M' : LieModel G y E') (j : E →ₛₗ[c] E')
    (hj : ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left) {P : E' → Prop} (zero : P 0)
    (base : ∀ e, P (j e)) (smul : ∀ (s : R') n, P n → P (s • n))
    (add : ∀ n n', P n → P n' → P (n + n')) (n : E') : P n := by
  subst h
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    rw [mul_smul]⟩
  let jl : E →ₗ[R] E' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hb : IsBaseChange R' jl := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange S G R R' x E E' M M' jl (fun e => by
    rw [Category.comp_id]
    exact hj e)
  exact hb.inductionOn n base smul add

end Transport

theorem lat_form_regular_generizes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  intro X G _ _ _ Ω _ ξ Li _ _ M f p q _ hqp hf e he
  let c : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hc : spMap c ≫ X.fromSpecStalk p.1 = X.fromSpecStalk q.1 :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hqp
  have hgen : ∀ s, genMap ξ q (c s) = genMap ξ p s :=
    fun s => LieTangent.genMap_specializes p q.2 hqp s
  obtain ⟨E, _, _, ⟨Mp⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨E', _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨j, hj⟩ := exists_lie_transport c hc Mp Mq
  obtain ⟨jp, hjp⟩ := exists_lie_transport (genMap ξ p) (LieTangent.spec_genMap ξ p) Mp M
  obtain ⟨jq, hjq⟩ := exists_lie_transport (genMap ξ q) (LieTangent.spec_genMap ξ q) Mq M

  have hcomp : ∀ e₀, jq (j e₀) = jp e₀ := by
    intro e₀
    refine M.inj (Over.OverMorphism.ext ?_)
    rw [hjq, hj, hjp, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun a => ?_
    ext <;> simp [hgen]

  have hmem : ∀ e₀, jp e₀ ∈ M.lat p := fun e₀ =>
    (M.mem_lat_iff p _).2 ⟨Mp.pt e₀, Mp.tan e₀, hjp e₀⟩

  obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
  obtain ⟨ε, rfl⟩ := Mq.onto v hv.1
  have he' : e = jq ε := M.inj (Over.OverMorphism.ext (hv.2.trans (hjq ε).symm))
  subst he'
  refine lie_transport_induction c hc Mp Mq j hj (P := fun n => f (jq n) ∈ regAt ξ q) ?_ ?_ ?_ ?_ ε
  · simpa using zero_mem (regAt ξ q)
  · intro e₀
    obtain ⟨s, hs⟩ := hf _ (hmem e₀)
    rw [hcomp]
    exact ⟨c s, (hgen s).trans hs⟩
  · intro s n hn
    have : f (jq (s • n)) = genMap ξ q s * f (jq n) := by
      rw [jq.map_smulₛₗ, map_smul, smul_eq_mul]
    change f (jq (s • n)) ∈ regAt ξ q
    rw [this]
    exact mul_mem ⟨s, rfl⟩ hn
  · intro n n' hn hn'
    change f (jq (n + n')) ∈ regAt ξ q
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hn hn'

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelAddedCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncPull
open GlobalTheory.CompanionTheory.Ar.SncRefine

theorem adjoin_insert_eq {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) :
    Algebra.adjoin ℚ (insert t ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω) : Set Ω)) =
      Algebra.adjoin ℚ (insert t (Set.range (bratio y c))) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro b (rfl | hb)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · have h : Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) ≤
          (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).restrictScalars ℤ := Algebra.adjoin_le (by
        rintro _ ⟨d, rfl⟩
        exact seg_ratio_mem y c (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).toSubring
          (fun p => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)) d)
      exact h hb
  · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
    rintro _ ⟨p, rfl⟩
    obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩

theorem map_mem_adjoin {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    {W : Set Ω₀} {W' : Set Ω} (hW : ∀ w ∈ W, algebraMap Ω₀ Ω w ∈ W') {b : Ω₀} (hb : b ∈ Algebra.adjoin ℚ W) :
    algebraMap Ω₀ Ω b ∈ Algebra.adjoin ℚ W' := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hW x hx)
  | algebraMap r =>
    have : algebraMap Ω₀ Ω (algebraMap ℚ Ω₀ r) = algebraMap ℚ Ω r := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_cover {R : Type} [CommRing R] (G : R → Prop) (h : ∀ P : Ideal R, P.IsPrime → ∃ t, t ∉ P ∧ G t) :
    ∃ (m : ℕ) (f a : Fin m → R), ∑ l, a l * f l = 1 ∧ ∀ l, G (f l) := by
  classical
  have hs : Ideal.span {t | G t} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht, hG⟩ := h M hM.isPrime
    exact ht (hle (Ideal.subset_span hG))
  have h1 : (1 : R) ∈ Ideal.span {t | G t} := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : R), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x • (x : R)

theorem isSncModel_pull : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (e : ℕ) (bd : Ideal (MRing J)) (I : Type) [Fintype I] (u : I → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) → Smooth f →
    AlgebraicIndependent Ω₀ u → IntermediateField.adjoin Ω₀ (Set.range u) = ⊤ →
    Cmp.IsSncModel y e bd →
    Cmp.IsSncModel (addY y x') (e + Fintype.card I) (bd.map (MvPolynomial.rename (addV J N))) := by
  classical
  intro X X' Ω₀ Ω _ _ _ _ _ ξ ξ' f K _ J _ y N x' e bd I _ u hq hq' tie tie' hd hsm hu hadj hsnc c₁ hc₁
  let c : (k : K) → J k := fun k => c₁ (Sum.inr k)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc₁ (Sum.inr k) (show algebraMap Ω₀ Ω (y ⟨k, c k⟩) = 0 by rw [h, map_zero])
  have hv : ∀ p, algebraMap Ω₀ Ω (bratio y c p) = bratio (addY y x') c₁ (addV J N p) := fun p => map_div₀ _ _ _
  have hxc : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hxc₁ : seg (addY y x') c₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc₁ k
  have hblk : ∀ p, bratio (addY y x') c₁ p ∈
      Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁) := fun p => by
    obtain ⟨d, hd⟩ := exists_seg_ratio (addY y x') c₁ hc₁ p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩
  obtain ⟨φ, hφ, hφs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing X X' Ω₀ Ω ξ ξ' f (algebraMap Ω₀ Ω) _ _ (seg y) (seg (addY y x'))
    hq hq' tie tie' hd hsm c c₁ hxc hxc₁ (fun d => by
      have e1 : seg y d / seg y c = ∏ k, bratio y c ⟨k, d k⟩ := (Finset.prod_div_distrib _ _).symm
      rw [e1, map_prod]
      refine prod_mem fun k _ => ?_
      rw [hv]
      exact hblk _)
  obtain ⟨m, f₀, a₀, hf, ha, hsum, H⟩ := hsnc c hc
  have hfin := GlobalTheory.T.kaehler_rank_transcendence_degree Ω₀ Ω I u hu hadj
  have hW : ∀ w ∈ Set.range (bratio y c), algebraMap Ω₀ Ω w ∈ Set.range (bratio (addY y x') c₁) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hv p).symm⟩
  let R₁ := Algebra.adjoin ℚ (Set.range (bratio (addY y x') c₁))
  have hfr : ∀ (A : Subalgebra ℤ Ω₀) (S : Subalgebra ℚ Ω₀), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω₀, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω₀ := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hfr₁ : ∀ (A : Subalgebra ℤ Ω) (S : Subalgebra ℚ Ω), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hloc : ∀ P : Ideal R₁, P.IsPrime → ∃ t : R₁, t ∉ P ∧ ((t : Ω) ≠ 0 → ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range (bratio (addY y x') c₁))) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + Fintype.card I) → S') (n' : ℕ), n' ≤ e + Fintype.card I ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename (addV J N)), ∀ s : S',
              (s : Ω) = MvPolynomial.aeval (bratio (addY y x') c₁) g → s ∈ q) ↔
            ∃ i : Fin (e + Fintype.card I), (i : ℕ) < n' ∧ z' i ∈ q)) := by
    intro P hP
    let fl : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (f₀ l), map_mem_adjoin hW (hf l)⟩
    let al : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (a₀ l), map_mem_adjoin hW (ha l)⟩
    have hone : ∑ l, al l * fl l = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      show ∑ l, algebraMap Ω₀ Ω (a₀ l) * algebraMap Ω₀ Ω (f₀ l) = 1
      simp only [← map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hsum, map_one]
    obtain ⟨l, hl⟩ : ∃ l, fl l ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hcon l)))
    have h0 : f₀ l ≠ 0 := fun h => hl (by
      have : fl l = 0 := Subtype.ext (by show algebraMap Ω₀ Ω (f₀ l) = 0; rw [h, map_zero])
      rw [this]
      exact P.zero_mem)
    obtain ⟨hSm, z, n, hn, hli, hspan, hbd⟩ := H l h0 _ rfl
    have hle₀ : Algebra.adjoin ℚ (Set.range (bratio y c)) ≤ Algebra.adjoin ℚ
        ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω₀) : Set Ω₀) :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
        rw [hd]
        exact Algebra.subset_adjoin (Algebra.subset_adjoin ⟨d, rfl⟩))
    obtain ⟨ψ, hψ, hψs⟩ := GlobalTheory.T.smooth_map_localization_compat Ω₀ Ω _ _ φ hφ hφs (f₀ l) (hle₀ (hf l)) h0
      (Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))))
      (Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))))
      (adjoin_insert_eq y c hc _).symm (adjoin_insert_eq (addY y x') c₁ hc₁ _).symm
    have hA₀ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c),
        a ∈ Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))) := fun a ha' => by
      rw [← adjoin_insert_eq y c hc]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    have hA₁ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁),
        a ∈ Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))) := fun a ha' => by
      rw [← adjoin_insert_eq (addY y x') c₁ hc₁]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    obtain ⟨t, ht, hG⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocalStep.local_step Ω₀ Ω _ _ (bratio y c) (bratio (addY y x') c₁) (addV J N) hv e _ bd hfin (f₀ l) h0 _ _ rfl rfl
      ψ hψ hψs (hfr _ _ hA₀ (_root_.GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart X Ω₀ ξ _ (seg y) tie c hxc))
      (hfr₁ _ _ hA₁ (_root_.GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart X' Ω ξ' _ (seg (addY y x')) tie' c₁ hxc₁)) hSm z n hn hli hspan hbd P hP (fl l) rfl hl
    exact ⟨t, ht, fun _ => hG⟩
  obtain ⟨m', f', a', hs', hG⟩ := exists_cover _ hloc
  refine ⟨m', fun l => (f' l : Ω), fun l => (a' l : Ω), fun l => (f' l).2, fun l => (a' l).2, ?_, fun l hl S' hS' => ?_⟩
  · have := congrArg (Subtype.val) hs'
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this
  · obtain ⟨h1, z', n', h2, h3, h4, h5⟩ := hG l hl S' hS'
    exact ⟨h1, z', n', h2, h3, h4, h5⟩

end GlobalTheory.CompanionTheory.Ar.SncPull
end
end

