module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem lieMap_act_pull (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V') : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  intro _ ha ha' hj a e
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  apply M'.inj
  refine hcanc _ _ ?_
  rw [ha' a (j e), hj, ha a e, Over.comp_left, Over.comp_left, Category.assoc, m.act a]
  have h2 := congrArg (· ≫ (t.act.act a).left) (hj e)
  simp only [Category.assoc] at h2 ⊢
  exact h2.symm

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def cast {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F] [Module R F]
    (M : LieModel G x F) : LieModel G y F := h ▸ M

theorem cast_left {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F]
    [Module R F] (M : LieModel G x F) (e : F) : ((cast h M).pt e).left = (M.pt e).left := by
  subst h
  rfl

theorem exists_tr {A B : Type} [CommRing A] [CommRing B] (a : Sp A ⟶ X) (b : Sp B ⟶ X) (c : A →+* B)
    (h : spMap c ≫ a = b) {E E' : Type} [AddCommGroup E] [AddCommGroup E'] [Module A E] [Module B E']
    (M : LieModel G a E) (M' : LieModel G b E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts X G A B c a E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  simpa [LieModel.Lifts] using this

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (dualMap d) ≫ spMap (dualMap c) = spMap (dualMap (d.comp c)) := by
  have : dualMap (d.comp c) = (dualMap d).comp (dualMap c) := by
    ext a <;> simp [dualMap]
  simp only [this, spMap, ← Spec.map_comp]
  rfl

theorem pt_left_inj {A : Type} [CommRing A] {a : Sp A ⟶ X} {E : Type} [AddCommGroup E] [Module A E]
    (M : LieModel G a E) {u v : E} (h : (M.pt u).left = (M.pt v).left) : u = v :=
  M.inj (Over.OverMorphism.ext h)

theorem exists_lift {R A : Type} [CommRing R] [CommRing A] [IsLocalRing A] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (z : Sp A ⟶ X) (h : z (IsLocalRing.closedPoint A) ∈ x.opensRange) : ∃ a : R →+* A, spMap a ≫ x = z := by
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨t, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of A) z h
    exact (this.ge (Set.mem_univ t) : t ∈ z ⁻¹ᵁ x.opensRange)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

variable [Smooth G.hom]

theorem basis_tr {R A : Type} [CommRing R] [CommRing A] (ψ : R →+* A) (x : Sp R ⟶ X) (y : Sp A ⟶ X)
    (hψ : spMap ψ ≫ x = y) {F Fy : Type} [AddCommGroup F] [Module R F] [AddCommGroup Fy] [Module A Fy]
    (MR : LieModel G x F) (My : LieModel G y Fy) {n : ℕ} (b : Module.Basis (Fin n) R F) :
    ∃ (β : F →ₛₗ[ψ] Fy) (B : Module.Basis (Fin n) A Fy), (∀ k, B k = β (b k)) ∧
      ∀ e, (My.pt (β e)).left = spMap (dualMap ψ) ≫ (MR.pt e).left := by
  obtain ⟨j, hj⟩ := exists_tr x y ψ hψ MR My
  letI : Algebra R A := ψ.toAlgebra
  letI : Module R Fy := Module.compHom Fy ψ
  haveI : IsScalarTower R A Fy :=
    ⟨fun s r e => by
      change (ψ s * r) • e = ψ s • r • e
      rw [mul_smul]⟩
  let j' : F →ₗ[R] Fy :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hbc : IsBaseChange A j' :=
    (_root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X G R x F MR).2.2 A Fy (cast hψ.symm My) j' fun e => by
      rw [cast_left]
      exact hj e
  refine ⟨j, (Algebra.TensorProduct.basis A b).map hbc.equiv, fun k => ?_, hj⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul]
  rfl

omit [Smooth G.hom] [GrpObj G] in
theorem mem_span_range {A Ω : Type} [CommRing A] [Field Ω] (g : A →+* Ω) {Fq E : Type} [AddCommGroup Fq]
    [Module A Fq] [AddCommGroup E] [Module Ω E] {n : ℕ} (B : Module.Basis (Fin n) A Fq) (j : Fq →ₛₗ[g] E)
    (y : Fq) : j y ∈ Submodule.span g.range (Set.range fun k => j (B k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr y, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [j.map_smulₛₗ]
  exact Submodule.smul_mem _ (⟨g (B.repr y k), _, rfl⟩ : g.range) (Submodule.subset_span ⟨k, rfl⟩)

variable [IsCommMonObj G]

theorem frame_of_basis {R : Type} [CommRing R] (x : Sp R ⟶ X) {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) {n : ℕ} (b : Module.Basis (Fin n) R F) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (φ : R →+* Ω) (hφ : spMap φ ≫ x = ξ) :
    ∃ c : Fin n → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = ⊤ ∧
      ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 →
        (genMap ξ q).comp ψ = φ → M.lat.IsFrameAt c q := by
  obtain ⟨j, B, hB, hj⟩ := basis_tr φ x ξ hφ MR M b
  have hc : (fun k => j (b k)) = B := funext fun k => (hB k).symm
  refine ⟨fun k => j (b k), ?_, ?_, fun q ψ hψ hg => ?_⟩
  · rw [hc]; exact B.linearIndependent
  · rw [hc]; exact B.span_eq
  refine ⟨by rw [hc]; exact B.linearIndependent, ?_⟩
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨β, Bq, hBq, hβ⟩ := basis_tr (A := X.presheaf.stalk q.1) ψ x (X.fromSpecStalk q.1) hψ MR Mq b
  obtain ⟨jq, hjq⟩ := exists_tr (A := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ξ (genMap ξ q)
    (spec_genMap ξ q) Mq M
  have hcomp : ∀ e, jq (β e) = j e := fun e => pt_left_inj M (by
    rw [hjq, hβ, ← Category.assoc, spMap_dual_comp, hg, hj])
  have hcq : (fun k => j (b k)) = fun k => jq (Bq k) := funext fun k => by rw [hBq, hcomp]
  refine le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
    obtain ⟨y, rfl⟩ := Mq.onto v hv.1
    have hy : e = jq y := pt_left_inj M (hv.2.trans (hjq y).symm)
    rw [hy, hcq]
    exact mem_span_range (genMap ξ q) Bq jq y
  · rintro _ ⟨k, rfl⟩
    exact (M.mem_lat_iff q _).2 ⟨Mq.pt (β (b k)), Mq.tan _, by
      change (M.pt (j (b k))).left = _
      rw [← hcomp]
      exact hjq _⟩

theorem exists_chart (G : Over X) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (y : X) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F)
      (_ : Module R F) (_ : LieModel G x F) (n : ℕ) (_ : Module.Basis (Fin n) R F), y ∈ x.opensRange := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let R₀ : Type := Γ(X, U)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨F₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R₀ x₀
  obtain ⟨hfin, hproj, hbc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X G R₀ x₀ F₀ M₀
  let P : PrimeSpectrum R₀ := hU.primeIdealOf ⟨y, hy⟩
  have hP : x₀ P = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  haveI : Module.FinitePresentation R₀ F₀ := Module.finitePresentation_of_projective R₀ F₀
  haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl F₀) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    P.asIdeal.primeCompl (LocalizedModule.mkLinearMap P.asIdeal.primeCompl F₀) (Localization.AtPrime P.asIdeal)
  let R : Type := Localization.Away f
  let x : Sp R ⟶ X := spMap (algebraMap R₀ R) ≫ x₀
  have hopen : IsOpenImmersion (spMap (algebraMap R₀ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Localization.Away f)))))
  have hx : IsOpenImmersion x := inferInstance
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G R x
  obtain ⟨β, hβ⟩ := exists_tr x₀ x (algebraMap R₀ R) rfl M₀ MF
  letI : Module R₀ F := Module.compHom F (algebraMap R₀ R)
  haveI : IsScalarTower R₀ R F :=
    ⟨fun s r e => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  let β' : F₀ →ₗ[R₀] F :=
    { toFun := β
      map_add' := β.map_add
      map_smul' := fun r e => β.map_smulₛₗ r e }
  have hb : IsBaseChange R β' := hbc R F MF β' hβ
  haveI : IsLocalizedModule (Submonoid.powers f) β' :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) R β').2 hb
  have e : LocalizedModule (Submonoid.powers f) F₀ ≃ₗ[R] F :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) F₀) β').extendScalarsOfIsLocalization
      (Submonoid.powers f) R
  haveI : Module.Free R F := Module.Free.of_equiv e
  haveI : Module.Finite R F := (_root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X G R x F MF).1
  have hmem : P ∈ Set.range (spMap (algebraMap R₀ R)) := by
    have := PrimeSpectrum.localization_away_comap_range R f
    have h2 : P ∈ PrimeSpectrum.basicOpen f := hf
    rw [← SetLike.mem_coe, ← this] at h2
    exact h2
  obtain ⟨t, ht⟩ := hmem
  haveI : Nontrivial R := PrimeSpectrum.nontrivial t
  refine ⟨R, inferInstance, x, hx, F, inferInstance, inferInstance, MF, _, Module.finBasis R F, ?_⟩
  refine ⟨t, ?_⟩
  change (spMap (algebraMap R₀ R) ≫ x₀) t = y
  rw [Scheme.Hom.comp_apply, ht, hP]

end GlobalTheory.CompanionTheory.Ar.LieVB

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB in
theorem lieLat_isVB_of_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), IsCptGen ξ → Smooth G.hom → M.lat.IsVB (Module.finrank Ω Li) ⊤ ∧ M.omLat.IsVB (Module.finrank Ω Li) ⊤ := by
  intro X Ω _ ξ G _ _ Li _ _ M _ hs
  haveI := hs
  have hvb : M.lat.IsVB (Module.finrank Ω Li) ⊤ := by
    intro p _
    obtain ⟨R, _, x, hx, F, _, _, MR, n, b, hp⟩ := exists_chart G p.1
    have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω Li := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge), Fintype.card_fin]
    subst hn
    refine ⟨x.opensRange, hp, c, hsp, fun q _ hq => ?_⟩
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  exact ⟨hvb, (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat Set.univ _ hvb).1⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleFromUnitRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem germ_res_val {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) (q : X) (hq : q ∈ W) :
    X.presheaf.germ W q hq (res h u).val = X.presheaf.germ U q (h hq) u.val :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) q hq u.val

theorem sec_ext {U : X.Opens} {s t : Γ(X, U)}
    (h : ∀ q (hq : q ∈ U), X.presheaf.germ U q hq s = X.presheaf.germ U q hq t) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

theorem exists_unit_of_unitAt [IsLocallyNoetherian X] (hξ : IsCptGen ξ) (U : X.Opens)
    (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω) (ha : ∀ q (hq : q ∈ U), unitAt ξ ⟨q, hU q hq⟩ a) :
    ∃ u : Γ(X, U)ˣ, ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq u.val) = a := by
  by_cases hne : (U : Set X).Nonempty
  · obtain ⟨s, hs, -⟩ := RegSection.existsUnique_section X Ω ξ hξ U hU a hne fun q hq => (ha q hq).2.1
    obtain ⟨t, ht, -⟩ := RegSection.existsUnique_section X Ω ξ hξ U hU a⁻¹ hne fun q hq => (ha q hq).2.2
    have st : s * t = 1 := RegSection.section_eq hξ U hU _ _ fun q hq => by
      rw [map_mul, map_mul, hs q hq, ht q hq, map_one, map_one, mul_inv_cancel₀ (ha q hq).1]
    exact ⟨⟨s, t, st, by rw [mul_comm, st]⟩, hs⟩
  · exact ⟨1, fun q hq => (hne ⟨q, hq⟩).elim⟩

theorem exists_transition : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X] (I : Type) (V : Option I → X.Opens) (T : I → Ω), IsCptGen ξ → (∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q) → (∀ q ∈ V none, ¬ genPt ξ ⤳ q) → (∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) → unitAt ξ ⟨q, hq⟩ (T j / T i)) → (⨆ i, V i = ⊤) → ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (LB.mk (Option I) V g).IsLB ∧ ∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ V (some i) ⊓ V (some j)), genMap ξ ⟨q, hq⟩ (X.presheaf.germ _ q h (g (some i) (some j)).val) = T j / T i := by
  intro X Ω _ ξ _ I V T hξ hsome hnone hunit hcov
  have hU : ∀ (i j : I), ∀ q ∈ V (some i) ⊓ V (some j), genPt ξ ⤳ q := fun i j q hq => hsome i q hq.1
  have A := fun i j => exists_unit_of_unitAt hξ (V (some i) ⊓ V (some j)) (hU i j) (T j / T i)
    fun q hq => hunit i j q _ hq.1 hq.2
  choose u hu using A
  obtain ⟨g, hg₁, hg₂, hg₃⟩ : ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (∀ i j, g (some i) (some j) = u i j) ∧
      (∀ j, g none j = 1) ∧ (∀ i, g (some i) none = 1) :=
    ⟨fun i j => match i, j with
      | some i, some j => u i j
      | none, _ => 1
      | some _, none => 1, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have val : ∀ (i j : I) {W : X.Opens} (h : W ≤ V (some i) ⊓ V (some j)) (q : X) (hq : q ∈ W)
      (hq' : genPt ξ ⤳ q), genMap ξ ⟨q, hq'⟩ (X.presheaf.germ W q hq (res h (u i j)).val) = T j / T i := by
    intro i j W h q hq hq'
    rw [germ_res_val]
    exact hu i j q (h hq)
  refine ⟨g, ⟨hcov, ?_, ?_⟩, fun i j q hq h => ?_⟩
  · intro i
    dsimp only
    apply Units.ext
    rcases i with _ | i
    · simp only [hg₂, map_one]
    · apply sec_ext
      intro q hq
      have hq' := hsome i q hq
      apply hξ.inj ⟨q, hq'⟩
      rw [hg₁, val i i _ q hq hq', Units.val_one, map_one, map_one]
      exact div_self fun e => (hunit i i q hq' hq hq).1 (by simp [e])
  · intro i j k
    dsimp only
    apply Units.ext
    apply sec_ext
    rintro q ⟨⟨hi, hj⟩, hk⟩
    have bad : ∀ a : I, q ∈ V none → q ∈ V (some a) → False := fun a h h' => hnone q h (hsome a q h')
    rcases i with _ | i <;> rcases j with _ | j <;> rcases k with _ | k
    · simp only [hg₂, map_one, _root_.mul_one]
    · exact (bad _ hi hk).elim
    · exact (bad _ hi hj).elim
    · exact (bad _ hi hj).elim
    · exact (bad _ hj hi).elim
    · exact (bad _ hj hi).elim
    · exact (bad _ hk hi).elim
    · have hq' := hsome i q hi
      apply hξ.inj ⟨q, hq'⟩
      have n₁ := (hunit i j q hq' hi hj).1
      have t₁ : T i ≠ 0 := fun e => n₁ (by simp [e])
      have t₂ : T j ≠ 0 := fun e => n₁ (by simp [e])
      simp only [hg₁, Units.val_mul, map_mul]
      have hW : q ∈ V (some i) ⊓ V (some j) ⊓ V (some k) := ⟨⟨hi, hj⟩, hk⟩
      have e₁ := val i j (W := V (some i) ⊓ V (some j) ⊓ V (some k)) inf_le_left q hW hq'
      have e₂ := val j k (W := V (some i) ⊓ V (some j) ⊓ V (some k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) q hW hq'
      have e₃ := val i k (W := V (some i) ⊓ V (some j) ⊓ V (some k))
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) q hW hq'
      refine (congrArg₂ (· * ·) e₁ e₂).trans (Eq.trans ?_ e₃.symm)
      field_simp
  · simpa only [hg₁] using hu i j q h

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPer

open GroundTheory.Heights₂.Heights.Regular

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

theorem add_single_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

theorem expCover_add_single (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have hi : (Fin.castLE h i).val < a := i.2
    simp only [expCover, Pi.add_apply, Pi.single_eq_same, if_pos hi, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
    exact mul_one _
  · simp [expCover, Pi.single_apply, hk]

theorem exists_mem_logCover (h : a ≤ n) : ∃ w : Fin n → ℂ, w ∈ logCover h := by
  refine ⟨fun k => if k.val < a then -1 else 0, fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    simp only [if_pos hi]
    simp
  · simp [not_lt.2 hk]

theorem monodromy_preserves_form (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  obtain ⟨w, hw⟩ := exists_mem_logCover L.a_le
  have h1 := L.im _ (add_single_mem_logCover L.a_le hw i) x y
  rw [L.mono i w hw, L.mono i w hw, expCover_add_single, L.im w hw] at h1
  exact_mod_cast h1

theorem T_bijective (L : Flat.LogPeriods n a g Λ) (i : Fin a) : Function.Bijective (L.T i) := by
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hE : ∀ x y, L.E (S x) y = L.E x (L.T i y) := by
    intro x y
    have h1 : e (S x) = (L.T i).dualMap (e x) := by simp [S]
    exact congrArg (fun f : Module.Dual ℤ Λ => f y) h1
  have hST : ∀ x, S (L.T i x) = x := fun x =>
    L.unimod.1 (LinearMap.ext fun y => by rw [hE, monodromy_preserves_form])
  have hSs : Function.Surjective S := fun x => ⟨_, hST x⟩
  have hSi : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSs
  exact ⟨fun x y h => by rw [← hST x, ← hST y, h], fun y => ⟨S y, hSi (hST (S y))⟩⟩

theorem exists_conj_logPeriods : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ),
    ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧
      ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  intro n a g Λ _ L'
  exact ⟨ConjPeriods.conj L' (T_bijective L'), fun _ _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LogPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_split_pullback_generic : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare <;> assumption)
end

