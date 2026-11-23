module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem eq_of_germ_comp {R : Type} [CommRing R] [IsLocalRing R] {z z' : Spec (CommRingCat.of R) ⟶ X}
    {U : X.Opens} (hU : IsAffineOpen U) (h : z (IsLocalRing.closedPoint R) ∈ U)
    (h' : z' (IsLocalRing.closedPoint R) ∈ U)
    (e : X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo z =
      X.presheaf.germ U _ h' ≫ Scheme.stalkClosedPointTo z') : z = z' := by
  have key : ∀ (t : Spec (CommRingCat.of R) ⟶ X) (ht : t (IsLocalRing.closedPoint R) ∈ U),
      t = Spec.map (X.presheaf.germ U _ ht ≫ Scheme.stalkClosedPointTo t) ≫ hU.fromSpec := by
    intro t ht
    rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk ht]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t).symm
  rw [key z h, key z' h', e]

theorem val_int {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) {A : Type} (s : Finset A) (f : A → Ω) (g : A → R)
    (h : ∀ i ∈ s, ValAt ξ z (f i) (g i)) : ValAt ξ z (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.ArchB.val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact RootHt.ArchB.val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique


open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  intro X Ω _ ξ K _ J y T _ hall z z' w hz hz'
  have hξ := T.gen
  have h := hall (centre z)
  have h' := hall (centre z')
  choose c hc using hz.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have in1 := RootHt.ArchB.in_chart (c := c) h hz hc0
  have in2 := RootHt.ArchB.in_chart (c := c) h' hz' hc0
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T in1 in2
  have hxc : x c ≠ 0 := in1.1
  obtain ⟨U, hU, hUm⟩ := T.affine c hxc
  have hzU : centre z ∈ U := (hUm _).2 ⟨h, in1⟩
  have hzU' : centre z' ∈ U := (hUm _).2 ⟨h', in2⟩

  have hval : ∀ (t : Spec (CommRingCat.of ℂ) ⟶ X), CoordsAt ξ y t w → ∀ (k : K) (i : J k),
      ValAt ξ t (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := by
    intro t ht k i
    obtain ⟨-, h2⟩ := ht.2 k (c k) (hc k)
    obtain ⟨r, hr, e⟩ := h2 i
    rw [e, mul_div_assoc, div_self (hc0 k), _root_.mul_one]
    exact hr
  have hrat : ∀ j : (k : K) → J k, x j / x c = ∏ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ := fun j => by
    rw [hx]
    exact (Finset.prod_div_distrib _ _).symm
  have key : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ r : ℂ, ValAt ξ z a r ∧ ValAt ξ z' a r := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      refine ⟨∏ k, w ⟨k, j k⟩ / w ⟨k, c k⟩, ?_, ?_⟩
      · simp only [hrat]
        exact val_prod h _ _ _ fun k _ => hval z hz k (j k)
      · simp only [hrat]
        exact val_prod h' _ _ _ fun k _ => hval z' hz' k (j k)
    | algebraMap n =>
      refine ⟨(n : ℂ), ?_, ?_⟩
      · simpa using val_int h n
      · simpa using val_int h' n
    | add a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r + s, RootHt.ArchB.val_add h1 h3, RootHt.ArchB.val_add h2 h4⟩
    | mul a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r * s, RootHt.ArchB.val_mul h1 h3, RootHt.ArchB.val_mul h2 h4⟩
  refine eq_of_germ_comp hU hzU hzU' ?_
  ext s
  have hgm : ∀ (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U),
      genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) :=
    fun p q hp hq => GlobalTheory.CompanionTheory.Ar.genMap_germ_eq_genMap_germ ξ U p q hp hq s
  have ha : genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    refine (T.ring c hxc _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hUm _).2 ⟨p.2, hp⟩
    rw [hgm ⟨centre z, h⟩ p hzU hpU]
    exact ⟨_, rfl⟩
  obtain ⟨r, h1, h2⟩ := key _ ha
  have e1 : ValAt ξ z (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hzU s)) := ⟨h, _, rfl, rfl⟩
  have e2 : ValAt ξ z' (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z').hom (X.presheaf.germ U (centre z') hzU' s)) :=
    ⟨h', _, (hgm ⟨centre z', h'⟩ ⟨centre z, h⟩ hzU' hzU), rfl⟩
  exact (RootHt.ArchB.val_unique hξ e1 h1).trans (RootHt.ArchB.val_unique hξ h2 e2)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth

open GroundTheory.Heights₂.Heights LieTangent

section Form

variable {L : Type} [Field L]

theorem one_tmul_smul (σ : L →+* ℂ) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (r : 𝓞 L) (x : V) :
    (1 : ComplexAt σ) ⊗ₜ[𝓞 L] (r • x) = (σ (r : L)) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) := by
  rw [tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  congr 1

variable [NumberField L]

theorem core_span {R V F : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup F] [Module ℂ F]
    (C : InnerProductSpace.Core ℂ F) (f : V →+ F) (φ : R → ℂ) (hs : ∀ r x, f (r • x) = φ r • f x) (A A' : Set V)
    (h : ∀ x ∈ A, ∀ x' ∈ A', C.inner (f x) (f x') = 0) :
    ∀ x ∈ Submodule.span R A, ∀ x' ∈ Submodule.span R A', C.inner (f x) (f x') = 0 := by
  let c : PreInnerProductSpace.Core ℂ F := C.toCore
  intro x hx x' hx'
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hx' using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => rw [map_zero]; exact InnerProductSpace.Core.inner_zero_right _
    | add u v _ _ hu hv =>
      rw [map_add (f := _)]
      exact (InnerProductSpace.Core.inner_add_right _ _ _).trans (by rw [show _ = _ from hu, show _ = _ from hv, add_zero])
    | smul r u _ hu =>
      rw [hs]
      exact (InnerProductSpace.Core.inner_smul_right _ _).trans (by rw [show _ = _ from hu, mul_zero])
  | zero => rw [map_zero]; exact InnerProductSpace.Core.inner_zero_left _
  | add u v _ _ hu hv =>
    rw [map_add (f := _)]
    exact (InnerProductSpace.Core.inner_add_left _ _ _).trans (by rw [show _ = _ from hu, show _ = _ from hv, add_zero])
  | smul r u _ hu =>
    rw [hs]
    exact (InnerProductSpace.Core.inner_smul_left _ _).trans (by rw [show _ = _ from hu, mul_zero])

theorem orth_sat (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (A A' : Set B.carrier)
    (h : ∀ x ∈ A, ∀ x' ∈ A',
      (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x') = 0)
    (x x' : B.carrier) (a a' : 𝓞 L) (ha : a ≠ 0) (ha' : a' ≠ 0) (hx : a • x ∈ Submodule.span (𝓞 L) A)
    (hx' : a' • x' ∈ Submodule.span (𝓞 L) A') :
    (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x') = 0 := by
  let f : B.carrier →+ Fibre σ B.carrier :=
    { toFun := fun x => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := fun x y => TensorProduct.tmul_add _ _ _ }
  have key := core_span (B.metric.form σ) f (fun r : 𝓞 L => σ (r : L)) (fun r x => one_tmul_smul σ r x) A A' h _ hx _ hx'
  let c : PreInnerProductSpace.Core ℂ (Fibre σ B.carrier) := (B.metric.form σ).toCore
  have ne : ∀ b : 𝓞 L, b ≠ 0 → σ (b : L) ≠ 0 := fun b hb =>
    (map_ne_zero σ).2 (by simpa using hb)
  have e : (B.metric.form σ).inner (f (a • x)) (f (a' • x')) =
      (starRingEnd ℂ) (σ (a : L)) * (σ (a' : L) * (B.metric.form σ).inner (f x) (f x')) := by
    rw [show f (a • x) = σ (a : L) • f x from one_tmul_smul σ a x,
      show f (a' • x') = σ (a' : L) • f x' from one_tmul_smul σ a' x']
    exact (InnerProductSpace.Core.inner_smul_left _ _).trans
      (congrArg _ (InnerProductSpace.Core.inner_smul_right _ _))
  rw [e] at key
  have h1 : (starRingEnd ℂ) (σ (a : L)) ≠ 0 := (map_ne_zero _).2 (ne a ha)
  exact (mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left h1)).resolve_left (ne a' ha')

end Form

section Eigen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω}

theorem isLieEigen_of_gen (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X)
    (hp : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z))
    (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
    (hg : (genMap 𝔐.ξ ⟨_, hp⟩).comp g₀ = 𝔐.cst) (s : CMType H ⊕ CMType H) (U : Submodule Ω 𝔐.Li) (hU : U ≤ 𝔐.Vgen s)
    (σ : L →+* ℂ) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel 𝔐.t.G z V) (x : V)
    (hx : x ∈ subGens 𝔐.M U z MB)
    (w : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ 𝔐.t.G)
    (hw : (w.left ≫ (𝟙 𝔐.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left)) :
    IsLieEigen 𝔐.t.act (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
      ((σ.comp ((Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom.comp g₀)).comp (labelEmb c s)) w := by
  obtain ⟨e, he, v, hval, hl⟩ := hx
  have hσ : spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc]
    exact congrArg (· ≫ z) (spec_comp _ _)
  have hd : GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L)) = (GlobalTheory.CompanionTheory.Ar.dualMap σ).comp (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) := by
    refine RingHom.ext fun a => ?_
    ext <;> simp
  have hw' : w = epsBase σ hσ ≫ v := by
    refine (left_eq_iff σ hσ w v).1 ?_
    have h1 : w.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left := by
      simpa [LieModel.Lifts] using hw
    have h2 : v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left := by
      simpa [LieModel.Lifts] using hl
    rw [h1, h2, hd, ← Category.assoc]
    exact congrArg (· ≫ (MB.pt x).left) (spec_comp _ _).symm
  subst hw'
  refine ⟨isTanAt_base σ hσ hval.isTanAt, fun a => ?_⟩
  have ev := GlobalTheory.CompanionTheory.Ar.FlagFib.valAt_eigen E H D l Xo c Y S Ω K J y 𝔐 L _ hp g₀ hg s e v a (hU he) hval
  have e1 : ((epsBase σ hσ ≫ v) ≫ 𝔐.t.act.act a).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap σ)) ≫ (v ≫ 𝔐.t.act.act a).left := rfl
  rw [e1, ev, ← Category.assoc, spec_dual_eps, Category.assoc]
  rfl

end Eigen

theorem orthAt_subFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ (s s' : CMType H ⊕ CMType H), s ≠ s' → ∀ U U' : Submodule Ω 𝔐.Li, U ≤ 𝔐.Vgen s → U' ≤ 𝔐.Vgen s' → OrthAt B (FlagFib.subFib 𝔐.M U z MB) (FlagFib.subFib 𝔐.M U' z MB) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 h hO L _ _ z B MB hF s s' hss U U' hU hU' σ x hx x' hx'
  have hp : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  obtain ⟨g₀, hg⟩ := GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 ⟨_, hp⟩
    (fun n hn => isUnit_natCast_stalk 𝔐.X L _ n hn)
  classical
  let : Fintype (CMType H) := Fintype.ofFinite _
  let ι₀ : c.F →+* ℂ := σ.comp ((Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom.comp g₀)
  have hinj := (GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c ℂ ι₀).1
  have hne : ι₀.comp (labelEmb c s) ≠ ι₀.comp (labelEmb c s') := fun e => hss (hinj e)
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨a', ha', hax'⟩ := hx'
  refine orth_sat B σ _ _ ?_ x x' a a' ha ha' hax hax'
  intro u hu u' hu'
  let w := epsBase (σ.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u
  let w' := epsBase (σ.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u'
  have hl : (w.left ≫ (𝟙 𝔐.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt u).left) := Category.comp_id _
  have hl' : (w'.left ≫ (𝟙 𝔐.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt u').left) := Category.comp_id _
  have e1 := isLieEigen_of_gen 𝔐 z hp g₀ hg s U hU σ MB u hu w hl
  have e2 := isLieEigen_of_gen 𝔐 z hp g₀ hg s' U' hU' σ MB u' hu' w' hl'
  exact (hF σ u u' w w' hl hl').trans (hO _ _ _ w w' hne e1 e2)

end GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionContinuousAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

section Frac

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem stalk_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ f g : Γ(X, U), IsUnit (X.presheaf.germ U p hp g) ∧
      s * X.presheaf.germ U p hp g = X.presheaf.germ U p hp f := by
  let : Algebra Γ(X, U) (X.presheaf.stalk p) := (X.presheaf.germ U p hp).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨f, g⟩, h⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl (S := X.presheaf.stalk p) s
  exact ⟨f, g, IsLocalization.map_units (X.presheaf.stalk p) g, h⟩

theorem genMap_germ_indep {U : X.Opens} {p q : Cpt ξ} (hp : p.1 ∈ U) (hq : q.1 ∈ U) (f : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp f) = genMap ξ q (X.presheaf.germ U q.1 hq f) := by
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  have key : ∀ r : Cpt ξ, ∀ hr : r.1 ∈ U, genMap ξ r (X.presheaf.germ U r.1 hr f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg f) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 f)
  rw [key p hp, key q hq]

theorem exists_frac {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) :
    ∃ (P Q : MvPolynomial κ ℤ) (t : X.presheaf.stalk p.1), IsUnit t ∧
      genMap ξ p t = MvPolynomial.aeval (fun j => x j / x c) Q ∧
      a * MvPolynomial.aeval (fun j => x j / x c) Q = MvPolynomial.aeval (fun j => x j / x c) P := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hp.1
  have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨f, g, hg, e⟩ := stalk_frac hU hpU s
  have hA : ∀ f : Γ(X, U), ∃ P : MvPolynomial κ ℤ, MvPolynomial.aeval (fun j => x j / x c) P =
      genMap ξ p (X.presheaf.germ U p.1 hpU f) := by
    intro f
    have hm : genMap ξ p (X.presheaf.germ U p.1 hpU f) ∈
        Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
      refine (hT.ring c hp.1 _).2 fun q hq => ?_
      have hqU : q.1 ∈ U := (hmem q.1).2 ⟨q.2, hq⟩
      rw [genMap_germ_indep hpU hqU]
      exact ⟨_, rfl⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hm
    obtain ⟨P, hP⟩ := hm
    exact ⟨P, hP⟩
  obtain ⟨P, hP⟩ := hA f
  obtain ⟨Q, hQ⟩ := hA g
  refine ⟨P, Q, X.presheaf.germ U p.1 hpU g, hg, hQ.symm, ?_⟩
  rw [hP, hQ, ← map_mul, e]

end Frac

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X}

theorem val_intCast (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_finsetProd (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (a : I → Ω) (r : I → ℂ)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def ratioAt (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) (c' : (k : K) → J k) : ℂ :=
  ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_ratio {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (ratioAt c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_finsetProd hz _ _ _ fun k _ => ?_
  obtain ⟨-, h2⟩ := hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  obtain ⟨r, hr, e⟩ := h2 (c' k)
  rw [e, mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem val_ratioPoly {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ValAt ξ z (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P)
      (MvPolynomial.aeval (ratioAt c w) P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_intCast hz n
  | add p q hp hq => simpa only [map_add (f := _)] using val_add hp hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (val_ratio hz hw hc i)

theorem continuousAt_ratioAt {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (c' : (k : K) → J k) : ContinuousAt (fun w => ratioAt c w c') w₀ :=
  tendsto_finsetProd _ fun k _ =>
    ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_ratioPoly {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (ratioAt c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_ratioAt hc i)

end Values

theorem val_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (h₀ : genPt ξ ⤳ centre z₀) (a : Ω), CoordsAt ξ y z₀ w₀ →
      a ∈ regAt ξ ⟨centre z₀, h₀⟩ →
      ∃ φ : ((Σ k, J k) → ℂ) → ℂ, ContinuousAt φ w₀ ∧ ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ),
        w ∈ N → CoordsAt ξ y z w → ValAt ξ z a (φ w) := by
  intro X Ω _ ξ K _ J _ y hall hT z₀ w₀ h₀ a hw ha
  choose c hc using hw.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hch := in_chart h₀ hw hc'
  obtain ⟨P, Q, t, ht, hQ, hPQ⟩ := exists_frac hT hch ha
  have hvQ := val_ratioPoly (hall _) hw hc' Q
  have hvt : ValAt ξ z₀ (MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)
      ((Scheme.stalkClosedPointTo z₀).hom t) := ⟨h₀, t, hQ, rfl⟩
  have hne : MvPolynomial.aeval (ratioAt c w₀) Q ≠ 0 := by
    rw [val_unique hT.gen hvQ hvt]
    exact (ht.map (Scheme.stalkClosedPointTo z₀).hom).ne_zero
  have hQa : MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q ≠ (0 : Ω) := by
    rw [← hQ]
    exact (ht.map (genMap ξ _)).ne_zero
  have haeq : a = MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P *
      (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)⁻¹ := by
    rw [← hPQ, mul_inv_cancel_right₀ hQa]
  refine ⟨fun w => MvPolynomial.aeval (ratioAt c w) P / MvPolynomial.aeval (ratioAt c w) Q,
    (continuousAt_ratioPoly hc' P).div (continuousAt_ratioPoly hc' Q) hne,
    {w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (ratioAt c w) Q ≠ 0}, ?_, ?_⟩
  · have e1 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 w₀, ∀ k, w ⟨k, c k⟩ ≠ 0 :=
      eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
    exact e1.and ((continuousAt_ratioPoly hc' Q).eventually_ne hne)
  · rintro z w ⟨h1, h2⟩ hwz
    rw [haeq]
    show ValAt ξ z _ (_ / _)
    rw [div_eq_mul_inv]
    exact val_mul (val_ratioPoly (hall _) hwz h1 P) (val_inv₀ h2 (val_ratioPoly (hall _) hwz h1 Q))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothQ
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieSeq

section Sm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

theorem smooth_q {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} (Q : AbQuot t x) : Smooth Q.q.left := by
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surjective
  have := Q.q_quasiCompact
  have hT := (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Spec (CommRingCat.of k)) Q.Ch).smooth
  have sq := (ReciprocityTheory.ChartRestriction.G.H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) hT

end Sm

end GlobalTheory.CompanionTheory.Ar.LieSeq
end
end

