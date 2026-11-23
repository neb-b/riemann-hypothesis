module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NatAbsDiscrMemDifferent
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.WeilBound.CoreStatements.AmpleLineBundles.TangentVectorExtendsOverIntegers

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionUnramifiedPrime
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem htLattice_eq_dR_of_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (GenTors 𝔐 p) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q :=
  @PositivityTheory.Xgn.lattice_height_unit

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetQuotientFormulaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_jet_quotient_formula : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k) (g : Germ.PS k 2 d), AxOne g → jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow | exact GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        Submodule.span R (Set.range fun k => j (b k)) = ⊤) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_baseChange S G A R x E F M N
  exact ⟨j, h1, h2, fun hs n b => (h3 hs n b).2⟩

end GlobalTheory.CompanionTheory.Ar.LieVal

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_val (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type)
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type)
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER,
      (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧
      (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧
      Submodule.span R (Set.range ev) = ⊤ := by
  intro hξ hs
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, hjs, hjb⟩ := LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := LieVal.exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M

  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  have hmem : ∀ a, i a ∈ M.lat ⟨centre z, h⟩ := fun a => (M.mem_lat_iff _ _).2 ⟨_, hext a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e v, M.Extends ⟨centre z, h⟩ e v → ∃ a, i a = e ∧ MA.pt a = v := by
    intro e v hv
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj (Over.OverMorphism.ext ((hi a).trans hv.2.symm)), rfl⟩
  let i' : EA →+ M.lat ⟨centre z, h⟩ :=
    { toFun := fun a => ⟨i a, hmem a⟩
      map_zero' := Subtype.ext (map_zero i)
      map_add' := fun a b => Subtype.ext (map_add i a b) }
  have hbij : Function.Bijective i' := by
    refine ⟨fun a b hab => hinj a b (congrArg Subtype.val hab), fun e => ?_⟩
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 e.2
    obtain ⟨a, ha, -⟩ := hsurj _ _ hv
    exact ⟨a, Subtype.ext ha⟩
  let q := AddEquiv.ofBijective i' hbij
  have hq : ∀ a, q.symm ⟨i a, hmem a⟩ = a := fun a => q.symm_apply_apply a
  refine ⟨j.comp q.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro e w
    constructor
    · rintro ⟨h', v, hv, hw⟩
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      refine ⟨hmem a, ?_⟩
      change j (q.symm ⟨i a, hmem a⟩) = w
      rw [hq]
      exact MR.inj (Over.OverMorphism.ext ((hj a).trans hw.symm))
    · rintro ⟨he, rfl⟩
      obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      change M.ValAt z (i a) (MR.pt (j (q.symm ⟨i a, hmem a⟩)))
      rw [hq]
      exact ⟨h, _, hext a, hj a⟩
  · rintro a r e ⟨_, s, hsa, rfl⟩
    obtain ⟨b, rfl⟩ := q.surjective e
    have : a • q b = q (s • b) := Subtype.ext (by
      change (a : Ω) • i b = i (s • b)
      rw [his, hsa])
    change j (q.symm (a • q b)) = _ • j (q.symm (q b))
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    exact hjs s b
  · obtain ⟨n, ⟨b⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth X G hs (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
    refine top_le_iff.1 ((hjb hs n b).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨k, rfl⟩
    refine ⟨q (b k), ?_⟩
    change j (q.symm (q (b k))) = _
    rw [q.symm_apply_apply]

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ggeo.LieCoord

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S}

def transport {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E)
    (e : E ≃ₗ[R] E') : LieModel G x E' where
  pt v := M.pt (e.symm v)
  tan v := M.tan _
  inj a b h := e.symm.injective (M.inj h)
  onto v hv := by
    obtain ⟨w, hw⟩ := M.onto v hv
    exact ⟨e w, by simpa using hw⟩
  add a b := by rw [map_add (f := _), M.add]
  smul c a := by rw [map_smul]; exact M.smul c _

theorem transport_pt {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E)
    (e : E ≃ₗ[R] E') (v : E') : (transport M e).pt v = M.pt (e.symm v) := rfl

theorem isTanAt_comp {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G) [IsMonHom f] : IsTanAt G x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem mul_comp' {T : Over S} (u v : T ⟶ G) (f : G ⟶ G) [IsMonHom f] : (u * v) ≫ f = (u ≫ f) * (v ≫ f) := by
  simp [MonObj.mul_comp]

variable {E : Type} [AddCommGroup E] [Module R E]

def endo (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : E :=
  Classical.choose (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

theorem endo_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (endo M f e) = M.pt e ≫ f :=
  Classical.choose_spec (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

def diff (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] : E →ₗ[R] E where
  toFun := endo M f
  map_add' a b := M.inj (by rw [endo_spec, M.add, M.add, endo_spec, endo_spec, mul_comp'])
  map_smul' c a := M.inj (by
    rw [endo_spec, RingHom.id_apply, LieModel.pt_smul, LieModel.pt_smul, endo_spec, Category.assoc])

theorem diff_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (diff M f e) = M.pt e ≫ f :=
  endo_spec M f e

def rho {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : O →+* Module.End R E where
  toFun a := letI := act.hom a; diff M (act.act a)
  map_one' := by
    ext e
    apply M.inj
    letI := act.hom 1
    show M.pt (diff M (act.act 1) e) = M.pt e
    rw [diff_spec, act.one, Category.comp_id]
  map_mul' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a * b)
    show M.pt (diff M (act.act (a * b)) e) = M.pt (diff M (act.act a) (diff M (act.act b) e))
    rw [diff_spec, diff_spec, diff_spec, mul_comm, act.mul, Category.assoc]
  map_zero' := by
    ext e
    apply M.inj
    letI := act.hom 0
    show M.pt (diff M (act.act 0) e) = M.pt 0
    have h0 : act.act 0 = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    rw [diff_spec, LieModel.pt_zero, h0, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (M.pt e ≫ toUnit G)]
  map_add' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a + b)
    show M.pt (diff M (act.act (a + b)) e) = M.pt (diff M (act.act a) e + diff M (act.act b) e)
    rw [diff_spec, M.add, diff_spec, diff_spec, act.add, comp_mul]

theorem rho_isActOf {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : M.IsActOf act.act (rho act M) :=
  fun a e => by letI := act.hom a; exact diff_spec M (act.act a) e

end GlobalTheory.CompanionTheory.Ar.Ggeo.LieCoord

namespace GlobalTheory.CompanionTheory.Ar.Ggeo


open LieCoord in
theorem lieModel_coordinates_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u := by
  intro E _ _ _ H S t R _ _ x
  haveI := t.semi
  haveI : Smooth t.G.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth
  obtain ⟨V, _, _, ⟨M0⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S t.G R x
  obtain ⟨hfin, hproj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective S t.G R x V M0
  haveI : Module.Flat R V := inferInstance
  haveI : Module.Free R V := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R V
  let eV : V ≃ₗ[R] (Fin (Module.finrank R V) → R) := b.equivFun
  refine ⟨Module.finrank R V, transport M0 eV, rho t.act (transport M0 eV), rho_isActOf t.act _, ?_⟩
  intro R' _ f x' hx'
  subst hx'
  letI : Algebra R R' := f.toAlgebra
  obtain ⟨T, _, _, _, _, M', j, hlift, hbc⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange S t.G R R' x V M0
  let eT : T ≃ₗ[R'] (Fin (Module.finrank R V) → R') := (hbc.basis b).equivFun
  have key : ∀ u : Fin (Module.finrank R V) → R, eT.symm (f ∘ u) = j (eV.symm u) := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [eT, eV, Module.Basis.equivFun_symm_apply, map_sum, map_smul, IsBaseChange.basis_apply,
      Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact algebraMap_smul R' (u i) (j (b i))
  have hpt : ∀ u : Fin (Module.finrank R V) → R, ((transport M' eT).pt (f ∘ u)).left =
      spMap (dualMap f) ≫ ((transport M0 eV).pt u).left := by
    intro u
    rw [transport_pt, transport_pt, key]
    have h := hlift (eV.symm u)
    unfold LieModel.Lifts at h
    rw [Category.comp_id] at h
    exact h
  refine ⟨transport M' eT, rho t.act (transport M' eT), rho_isActOf t.act _, hpt, ?_⟩
  intro a u
  apply (transport M' eT).inj
  apply Over.OverMorphism.ext
  letI := t.act.hom a
  have h1 := rho_isActOf t.act (transport M' eT) a (f ∘ u)
  have h2 := rho_isActOf t.act (transport M0 eV) a u
  rw [h1, Over.comp_left, hpt, hpt, h2, Over.comp_left, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Ggeo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.Ar.LieBc

theorem exists_model_of_eq {S : Scheme.{0}} {R : Type} [CommRing R] (G : Over S) [GrpObj G] {x₁ x₂ : Sp R ⟶ S}
    (hx : x₁ = x₂) {T : Type} [AddCommGroup T] [Module R T] (M₁ : LieModel G x₁ T) :
    ∃ M₂ : LieModel G x₂ T, ∀ t, (M₂.pt t).left = (M₁.pt t).left := by
  subst hx
  exact ⟨M₁, fun _ => rfl⟩

theorem injective_of_isBaseChange {K K' : Type} [Field K] [Field K'] [Algebra K K'] {V T : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T] {j : V →ₗ[K] T}
    (hj : IsBaseChange K' j) : Function.Injective j := by
  have e : ⇑j = hj.equiv ∘ TensorProduct.mk K K' V 1 := by
    funext x
    simp [IsBaseChange.equiv_tmul]
  rw [e]
  exact hj.equiv.injective.comp (Module.FaithfullyFlat.tensorProduct_mk_injective V)

theorem span_range_of_isBaseChange {K K' : Type} [CommRing K] [CommRing K'] [Algebra K K'] {V T : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T]
    {j : V →ₗ[K] T} (hj : IsBaseChange K' j) : Submodule.span K' (Set.range j) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  refine hj.inductionOn t (fun m => Submodule.subset_span ⟨m, rfl⟩) (fun s n h => Submodule.smul_mem _ s h)
    (fun a b ha hb => Submodule.add_mem _ ha hb)

end GlobalTheory.CompanionTheory.Ar.LieBc

theorem GlobalTheory.CompanionTheory.Ar.LieBc.main : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  intro L L' _ _ e G G' _ _ _ _ φ h V _ _ MV
  letI : Algebra L L' := e.toAlgebra
  obtain ⟨T, iT, mT, mR, tower, M', j, hl, hbc⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange (Sp L) G L L' (𝟙 _) V MV
  have hx : spMap (algebraMap L L') ≫ 𝟙 (Sp L) = 𝟙 (Sp L') ≫ spMap e := by
    rw [Category.comp_id, Category.id_comp]
    rfl
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.CompanionTheory.Ar.LieBc.exists_model_of_eq G hx M'
  refine ⟨T, iT, mT, GlobalTheory.CompanionTheory.Ar.LieMove.pullModel h M₂, j.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro c x
    change j (c • x) = e c • j x
    rw [map_smul]
    exact (algebraMap_smul L' c (j x)).symm
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.injective_of_isBaseChange hbc
  · intro x
    have e₁ := hl x
    have e₂ : (M'.pt (j x)).left ≫ 𝟙 G.left = spMap (dualMap (algebraMap L L')) ≫ (MV.pt x).left := e₁
    change (GlobalTheory.CompanionTheory.Ar.LieMove.liftEps h (M₂.pt (j x))).left ≫ φ = _
    rw [GlobalTheory.CompanionTheory.Ar.LieMove.liftEps_left, hM₂]
    exact (Category.comp_id _).symm.trans e₂
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.span_range_of_isBaseChange hbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_complex_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre | exact GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieValuePullbackFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem stalk_key {K K' : Type} [Field K] [Field K'] (w : Spec (CommRingCat.of K) ⟶ X)
    (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K') (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') :
    ∃ hc : centre w' = centre w, X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo w' = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := by
  have hl : IsLocalHom (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f).hom := by
    refine ⟨fun b hb => ?_⟩
    have h1 : IsUnit (f ((Scheme.stalkClosedPointTo w).hom b)) := hb
    have h2 : IsUnit ((Scheme.stalkClosedPointTo w).hom b : K) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo w).hom b h2
  have e2 : w' = Spec.map (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f) ≫
      X.fromSpecStalk (w (IsLocalRing.closedPoint (CommRingCat.of K))) := by
    rw [← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hc0 : (Spec.map (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f) ≫
      X.fromSpecStalk (w (IsLocalRing.closedPoint (CommRingCat.of K))))
        (IsLocalRing.closedPoint (CommRingCat.of K')) =
      w (IsLocalRing.closedPoint (CommRingCat.of K)) :=
    closedPoint_specMap_fromSpecStalk (R := CommRingCat.of K') _ _
  have key0 := stalkSpecializes_stalkClosedPointTo _ _ hc0
  clear e
  subst e2
  exact ⟨hc0, key0⟩

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_of_eq (M : LieModel G ξ E) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c) (a : E)
    (v : epsAt (R := X.presheaf.stalk c) (X.fromSpecStalk c) ⟶ G) (hv : M.Extends ⟨c, h⟩ a v)
    {K : Type} [CommRing K] (φ : X.presheaf.stalk c' ⟶ CommRingCat.of K) :
    ∃ (h' : genPt ξ ⤳ c') (v' : epsAt (R := X.presheaf.stalk c') (X.fromSpecStalk c') ⟶ G),
      M.Extends ⟨c', h'⟩ a v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v'.left =
        Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫ φ).hom)) ≫
          v.left := by
  subst hc
  refine ⟨h, v, hv, ?_⟩
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem valAt_field_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (K K' : Type) [Field K] [Field K'] (w : Sp K ⟶ X) (f : K →+* K') (a : Li) (v : epsAt w ⟶ G), M.ValAt w a v → M.ValAt (spMap f ≫ w) a (GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps f w ≫ v) := by
  intro X Ω _ ξ G _ Li _ _ M K K' _ _ w f a v hv
  obtain ⟨h, v₀, hE, hl⟩ := hv
  obtain ⟨hc, key⟩ := stalk_key w (spMap f ≫ w) f rfl
  obtain ⟨h', v', hE', hl'⟩ := extends_of_eq M hc h a v₀ hE (Scheme.stalkClosedPointTo (spMap f ≫ w))
  refine ⟨h', v', hE', ?_⟩
  refine Eq.trans ?_ hl'.symm
  rw [key, Over.comp_left, hl]
  simp only [GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps, Over.homMk_left]
  have e1 : spMap (dualMap f) ≫ Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo w).hom)) =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f).hom)) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← dualMap_comp']
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ v₀.left) e1)

end GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lie_model_extends : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | exact GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_lifts_of_local : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) :=
  @CoverDenseAlt.tangent_vector_extends_over_integers

end GlobalTheory.CompanionTheory.Ar
end

