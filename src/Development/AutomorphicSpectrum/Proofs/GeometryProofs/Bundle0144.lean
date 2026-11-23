module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralModelFacts
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeft
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CoverLie

section Move

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem tan_up {G : Over S} [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (x' : Sp R' ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  let u : Over.mk x' ⟶ Over.mk x := Over.homMk (Spec.map (CommRingCat.ofHom φ)) h
  have e : (LieEx.zsec x' : _ ⟶ LieEx.ob x' R') ≫ LieCarrier.epsHom φ x x' h = u ≫ LieEx.zsec x := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  refine (LieEx.isTanAt_iff x' G _).2 ?_
  rw [← Category.assoc, e, Category.assoc, (LieEx.isTanAt_iff x G _).1 hv, MonObj.comp_one]

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

theorem exists_hom (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hG : IsGrpPullback G' G f φ) (M : LieModel G ξ V)
    (M' : LieModel G' ξ' V') :
    ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  have hx : Spec.map (CommRingCat.ofHom i) ≫ ξ = ξ' ≫ f := hd.symm
  let P := LieMove.pushModel hG M'
  have ex : ∀ e, ∃ e', P.pt e' = LieCarrier.epsHom i ξ (ξ' ≫ f) hx ≫ M.pt e :=
    fun e => P.onto _ (tan_up i ξ (ξ' ≫ f) hx _ (M.tan e))
  choose j hj using ex
  refine ⟨AddMonoidHom.mk' j fun a b => P.inj ?_, fun e => congrArg (fun z => z.left) (hj e)⟩
  rw [P.add, hj, hj, hj, M.add, MonObj.comp_mul]

theorem map_diff {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {a : G ⟶ G} {a' : G' ⟶ G'}
    (hG : IsGrpPullback G' G f φ) (hφ : a'.left ≫ φ = φ ≫ a.left) {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {T : V →ₗ[Ω] V} {T' : V' →ₗ[Ω'] V'} (hT : M.IsDiffOf a T) (hT' : M'.IsDiffOf a' T') (e : V) :
    j (T e) = T' (j e) := by
  refine M'.inj (Over.OverMorphism.ext (hG.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [hj, hT e, hT' (j e), Over.comp_left, Over.comp_left, Category.assoc, hφ, ← Category.assoc, ← Category.assoc, hj]

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {f' : S'' ⟶ S} (hf : f' = g ≫ f) (m : SABMap t' t f) (n : SABMap t'' t f') :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst hf
  exact sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A B i h hd hf
  obtain ⟨m, hm⟩ := cancel hf A.m B.m
  obtain ⟨j, hj⟩ := exists_hom hd m.cart A.M B.M
  obtain ⟨hx, -, hl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePull.main A.X B.X Ω₁ Ω A.ξ B.ξ h i A.t.G B.t.G m.φ A.Li B.Li A.M B.M j A.tie.gen B.tie.gen
    hd m.cart A.t.semi.smooth hj
  refine ⟨j, hx, fun e => ?_, fun a e => ?_, hl⟩
  · rw [hm, ← Category.assoc, hj, Category.assoc]
  · exact map_diff m.cart (m.act a) hj (A.act a) (B.act a) e

end GlobalTheory.CompanionTheory.Ar.CoverLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLatticeMapCompat
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SingVal

open LiePull LieTangent

section Abstract

open MonObj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {Ω : Type} [Field Ω] {L V : Type} [AddCommGroup L] [Module Ω L]
  [AddCommGroup V] [Module ℂ V] {ξ : Sp Ω ⟶ S} {z : Sp ℂ ⟶ S}

def extSub (W : Subring Ω) {x : Sp W ⟶ S} (hx : spMap W.subtype ≫ x = ξ) (N : LieModel G ξ L) : Submodule W L where
  carrier := {e | ∃ v, Ext W.subtype x N e v}
  add_mem' := fun ⟨_, hv⟩ ⟨_, hv'⟩ => ⟨_, hv.mul hx hv'⟩
  zero_mem' := ⟨_, Ext.zero hx⟩
  smul_mem' c _ := fun ⟨_, hv⟩ => ⟨_, hv.smul c⟩

theorem exists_val (W : Subring Ω) (φ : W →+* ℂ) {x : Sp W ⟶ S} (hz : spMap φ ≫ x = z) (N : LieModel G ξ L)
    (Nz : LieModel G z V) :
    ∃ val : L → V, ∀ e v, Ext W.subtype x N e v → Nz.pt (val e) = epsBase φ hz ≫ v := by
  classical
  have key : ∀ e, ∃ w, ∀ v, Ext W.subtype x N e v → Nz.pt w = epsBase φ hz ≫ v := by
    intro e
    by_cases h : ∃ v, Ext W.subtype x N e v
    · obtain ⟨v, hv⟩ := h
      obtain ⟨w, hw⟩ := Nz.onto _ (isTanAt_base φ hz hv.1)
      exact ⟨w, fun v' hv' => by rw [hw, hv.unique Subtype.val_injective hv']⟩
    · exact ⟨0, fun v hv => (h ⟨v, hv⟩).elim⟩
  choose val hval using key
  exact ⟨val, hval⟩

theorem exists_lat_val (W : Subring Ω) (φ : W →+* ℂ) {x : Sp W ⟶ S} (hx : spMap W.subtype ≫ x = ξ)
    (hz : spMap φ ≫ x = z) (N : LieModel G ξ L) (Nz : LieModel G z V) :
    ∃ (Lm : Submodule W L) (val : L → V), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧
      (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧
      ∀ e v, Ext W.subtype x N e v → e ∈ Lm ∧ Nz.pt (val e) = epsBase φ hz ≫ v := by
  obtain ⟨val, hval⟩ := exists_val W φ hz N Nz
  refine ⟨extSub W hx N, val, ?_, ?_, ?_, fun e v h => ⟨⟨v, h⟩, hval e v h⟩⟩
  · apply Nz.inj
    rw [hval 0 1 (Ext.zero hx), LieModel.pt_zero, comp_one]
  · rintro e ⟨v, hv⟩ e' ⟨v', hv'⟩
    apply Nz.inj
    rw [hval _ _ (hv.mul hx hv'), Nz.add, hval _ _ hv, hval _ _ hv', comp_mul]
  · rintro a e ⟨v, hv⟩
    apply Nz.inj
    have h1 := hval _ _ (hv.smul a)
    refine h1.trans ?_
    rw [LieModel.pt_smul, hval _ _ hv]
    have e1 : epsBase φ hz ≫ epsScale x a = epsScale z (φ a) ≫ epsBase φ hz := base_scale φ hz a
    have e2 : LieEx.hom x (a • (LinearMap.id : W →ₗ[W] W)) = epsScale x a := rfl
    rw [e2, ← Category.assoc, e1, Category.assoc]

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C)
    {T : Scheme.{0}} (t : Sp (DualNumber A) ⟶ T) :
    spMap (dualMap (b.comp a)) ≫ t = spMap (dualMap b) ≫ spMap (dualMap a) ≫ t := by
  rw [← dualMap_comp]
  exact (congrArg (· ≫ t) (spec_comp (dualMap a) (dualMap b)).symm).trans (Category.assoc _ _ _)

theorem assoc_three {P Q R T U : Scheme.{0}} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (d : T ⟶ U) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

theorem ext_of_tan {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] {f : X' ⟶ S} {ψ : G'.left ⟶ G.left}
    (hG : IsGrpPullback G' G f ψ) {A B : Type} [CommRing A] [CommRing B] {g : A →+* Ω} {y : Sp B ⟶ X'} (σ : B →+* A)
    {h : B →+* Ω} {x : Sp A ⟶ S} (hxy : x = (spMap σ ≫ y) ≫ f) (hσ : g.comp σ = h) {N : LieModel G ξ L} {e : L}
    {v : epsAt y ⟶ G'} (hv : IsTanAt G' y v)
    (he : (N.pt e).left = spMap (dualMap h) ≫ v.left ≫ ψ) :
    ∃ u : epsAt x ⟶ G, Ext g x N e u ∧ u.left = spMap (dualMap σ) ≫ v.left ≫ ψ := by
  subst hxy
  subst hσ
  refine ⟨LieMove.pushEps hG (epsBase σ rfl ≫ v), ⟨(LieMove.tan_iff hG _).1 (isTanAt_base σ rfl hv), ?_⟩,
    Category.assoc _ _ _⟩
  refine he.trans ?_
  have e1 : spMap (dualMap (g.comp σ)) = spMap (dualMap g) ≫ spMap (dualMap σ) := by
    rw [← dualMap_comp]
    exact (spec_comp _ _).symm
  rw [e1, Category.assoc]
  rfl

end Abstract

theorem value_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (ι : 𝔐₀.Li →+ 𝔐.Li) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X) (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) → (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) → (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) → (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) → (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) → spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f → ∀ (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z₁ Vz), ∃ (Lm : Submodule W 𝔐.Li) (val : 𝔐.Li → Vz), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧ (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧ (∀ (e : 𝔐.Li) (v : epsAt z₁ ⟶ 𝔐.t.G), 𝔐.M.ValAt z₁ e v → e ∈ Lm ∧ v = MR.pt (val e)) ∧ ∀ (e₀ : 𝔐₀.Li) (v₀ : epsAt z₂ ⟶ 𝔐₀.t.G), 𝔐₀.M.ValAt z₂ e₀ v₀ → ι e₀ ∈ Lm ∧ (MR.pt (val (ι e₀))).left ≫ 𝔐.m.φ = v₀.left ≫ 𝔐₀.m.φ := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i ι W φ z₁ z₂ σ₁ σ₂ hgen hι hσ₁ hσ₂ hφ₁ hφ₂ hxx
    Vz _ _ MR
  have hG := 𝔐.m.cart
  have hG₀ := 𝔐₀.m.cart
  have s₁ : W.subtype.comp σ₁ = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ := RingHom.ext hσ₁
  have s₂ : W.subtype.comp σ₂ = i.comp (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩) := RingHom.ext hσ₂
  have t₁ : φ.comp σ₁ = (Scheme.stalkClosedPointTo z₁).hom := RingHom.ext hφ₁
  have t₂ : φ.comp σ₂ = (Scheme.stalkClosedPointTo z₂).hom := RingHom.ext hφ₂
  obtain ⟨x, hx₁⟩ : ∃ x : Sp W ⟶ Y.X, x = (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁)) ≫ 𝔐.f := ⟨_, rfl⟩
  have hx₂ : x = (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂)) ≫ 𝔐₀.f := by
    rw [hx₁, Category.assoc, Category.assoc, hxx]
  have hx : spMap W.subtype ≫ x = 𝔐.ξ ≫ 𝔐.f := by
    rw [hx₁, ← Category.assoc, ← Category.assoc, spec_comp, s₁]
    exact congrArg (· ≫ 𝔐.f) (spec_genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩)
  have hz : spMap φ ≫ x = z₁ ≫ 𝔐.f := by
    rw [hx₁, ← Category.assoc, ← Category.assoc, spec_comp, t₁]
    exact congrArg (· ≫ 𝔐.f) (spec_centre z₁)
  obtain ⟨Lm, val, h0, hadd, hsm, hext⟩ := exists_lat_val W φ hx hz (LieMove.pushModel hG 𝔐.M)
    (LieMove.pushModel hG MR)
  refine ⟨Lm, val, h0, hadd, hsm, ?_, ?_⟩
  · intro e v hv
    obtain ⟨h, v', hv', hl⟩ := hv
    obtain ⟨u, hu, hul⟩ := ext_of_tan (N := LieMove.pushModel hG 𝔐.M) (e := e) hG σ₁ hx₁ s₁ hv'.1
      (by
        show (𝔐.M.pt e).left ≫ _ = _
        rw [hv'.2]
        exact Category.assoc _ _ _)
    obtain ⟨hm, hpt⟩ := hext e u hu
    refine ⟨hm, LieMove.pushEps_inj hG (Eq.trans ?_ hpt.symm)⟩
    have e3 : v.left = spMap (dualMap φ) ≫ spMap (dualMap σ₁) ≫ v'.left := by
      rw [hl, ← t₁]
      exact spMap_dual_comp _ _ _
    apply Over.OverMorphism.ext
    show v.left ≫ _ = spMap (dualMap φ) ≫ u.left
    rw [hul, e3]
    exact assoc_three _ _ _ _
  · intro e₀ v₀ hv
    obtain ⟨h, v', hv', hl⟩ := hv
    have hι' := (hι e₀ (ι e₀)).2 rfl
    obtain ⟨u, hu, hul⟩ := ext_of_tan (N := LieMove.pushModel hG 𝔐.M) (e := ι e₀) hG₀ σ₂ hx₂ s₂ hv'.1
      (by
        show (𝔐.M.pt (ι e₀)).left ≫ _ = _
        rw [hι', hv'.2, spMap_dual_comp]
        exact congrArg (_ ≫ ·) (Category.assoc _ _ _))
    obtain ⟨hm, hpt⟩ := hext _ u hu
    refine ⟨hm, ?_⟩
    have e3 : v₀.left = spMap (dualMap φ) ≫ spMap (dualMap σ₂) ≫ v'.left := by
      rw [hl, ← t₂]
      exact spMap_dual_comp _ _ _
    refine (congrArg (fun q => q.left) hpt).trans ?_
    show spMap (dualMap φ) ≫ u.left = _
    rw [hul, e3]
    exact (assoc_three _ _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.SingVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFrameIndep

theorem linearIndependent_values {Ω C E EC : Type} [Field Ω] [Field C] [AddCommGroup E] [Module Ω E]
    [AddCommGroup EC] [Module C EC] (A : Subring Ω) (ρ : A →+* C) (P : Submodule A E) (ev : P →+ EC)
    (hsm : ∀ (a : A) (e : P), ev (a • e) = ρ a • ev e) (hspan : Submodule.span C (Set.range ev) = ⊤)
    {g n : ℕ} (b : Fin g → E) (hP : P = Submodule.span A (Set.range b))
    (hfin : Module.finrank C EC = g) (S : Finset (Fin g)) (c : Fin n → E) (hc : LinearIndependent Ω c)
    (hL : Submodule.span A (b '' S) = Submodule.span A (Set.range c))
    (w : Fin n → EC) (hw : ∀ i, ∃ he : c i ∈ P, ev ⟨c i, he⟩ = w i) : LinearIndependent C w := by
  subst hP
  have hbm : ∀ k, b k ∈ Submodule.span A (Set.range b) := fun k => Submodule.subset_span ⟨k, rfl⟩
  let v : Fin g → EC := fun k => ev ⟨b k, hbm k⟩
  have hcomb : ∀ {J : Type} [Fintype J] (f : J → Fin g) (t : J → A)
      (he : ∑ i, t i • b (f i) ∈ Submodule.span A (Set.range b)),
      ev ⟨∑ i, t i • b (f i), he⟩ = ∑ i, ρ (t i) • v (f i) := by
    intro J _ f t he
    have : (⟨∑ i, t i • b (f i), he⟩ : Submodule.span A (Set.range b)) =
        ∑ i, t i • (⟨b (f i), hbm _⟩ : Submodule.span A (Set.range b)) := by
      apply Subtype.ext
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm _ _
  have hvspan : ⊤ ≤ Submodule.span C (Set.range v) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨e, he⟩, rfl⟩
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 he
    have := hcomb (fun i => i) t he
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hv : LinearIndependent C v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hvspan (by simp [hfin])
  have hvS : LinearIndependent C (fun k : S => v k) := hv.comp _ Subtype.val_injective
  have himg : b '' S = Set.range (fun k : S => b k) := by
    ext y
    simp
  rw [himg] at hL
  have hcm : ∀ i, c i ∈ Submodule.span A (Set.range fun k : S => b k) := fun i => by
    rw [hL]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbS : ∀ k : S, b k ∈ Submodule.span A (Set.range c) := fun k => by
    rw [← hL]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hcm i)
  choose d hd using fun k => (Submodule.mem_span_range_iff_exists_fun A).1 (hbS k)
  have hdelta : ∀ i j, ∑ k, a i k * d k j = if i = j then 1 else 0 := by
    intro i j
    have hexp : ∑ j, (∑ k, a i k * d k j) • c j = c i := by
      conv_rhs => rw [← ha i]
      simp only [← hd, Finset.smul_sum, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    have hz : ∑ j, (((∑ k, a i k * d k j : A) : Ω) - if i = j then 1 else 0) • c j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [sub_eq_zero]
      exact hexp
    have := Fintype.linearIndependent_iff.1 hc _ hz j
    apply Subtype.ext
    rw [sub_eq_zero] at this
    rw [this]
    split_ifs <;> simp
  have hwexp : ∀ i, w i = ∑ k : S, ρ (a i k) • v k := by
    intro i
    obtain ⟨he, hev⟩ := hw i
    rw [← hev]
    have hmem : ∑ k : S, a i k • b k ∈ Submodule.span A (Set.range b) := by
      rw [ha i]
      exact he
    rw [← hcomb (fun k : S => (k : Fin g)) (a i) hmem]
    congr 2
    exact (ha i).symm
  rw [Fintype.linearIndependent_iff]
  intro l hl j
  have hk : ∀ k : S, ∑ i, l i * ρ (a i k) = 0 := by
    refine Fintype.linearIndependent_iff.1 hvS _ ?_
    rw [← hl]
    simp only [hwexp, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  calc l j = ∑ i, l i * ρ (∑ k, a i k * d k j) := by
        simp only [hdelta]
        simp [apply_ite ρ]
    _ = ∑ k : S, (∑ i, l i * ρ (a i k)) * ρ (d k j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hk]


open GlobalTheory.CompanionTheory.Ar.LieVB in
theorem finrank_eq_of_isFrameAt {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Ω : Type}
    [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {C : Type} [Field C]
    {z : Sp C ⟶ X} (h : genPt ξ ⤳ centre z) {EC : Type} [AddCommGroup EC] [Module C EC] (N : LieModel G z EC)
    {g : ℕ} (b : Fin g → E) (hξ : IsCptGen ξ) (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    Module.finrank C EC = g := by
  obtain ⟨R, _, x, hx, F, _, _, MR, n', b', hp⟩ := exists_chart G (centre z)
  have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨a, ha⟩ := exists_lift x z hp
  obtain ⟨_, B, -, -⟩ := basis_tr φ x ξ hφ MR M b'
  obtain ⟨_, BC, -, -⟩ := basis_tr a x z ha MR N b'
  have hC : Module.finrank C EC = n' := by
    rw [Module.finrank_eq_card_basis BC, Fintype.card_fin]
  have hΩ : Module.finrank Ω E = n' := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  haveI : Module.Finite Ω E := Module.Finite.of_basis B
  obtain ⟨U, hU, b₂, hsp, hfr⟩ := (lieLat_isVB_of_smooth X Ω ξ G E M hξ inferInstance).1 ⟨centre z, h⟩ (Set.mem_univ _)
  have h₂ := (hfr ⟨centre z, h⟩ (Set.mem_univ _) hU).2
  have hspan : ⊤ ≤ Submodule.span Ω (Set.range b) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have hk : b₂ k ∈ Submodule.span (regAt ξ ⟨centre z, h⟩) (Set.range b) := by
      rw [← hb.2, h₂]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (Submodule.span_le_restrictScalars (regAt ξ ⟨centre z, h⟩) Ω (Set.range b)) hk
  have hg : Module.finrank Ω E = g := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hb.1 hspan), Fintype.card_fin]
  rw [hC, ← hΩ, hg]

end GlobalTheory.CompanionTheory.Ar.LieFrameIndep

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.LieFrameIndep in
theorem values_frame_sublattice_linearIndependent : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (C : Type) [Field C] (z : Sp C ⟶ X) (h : genPt ξ ⤳ centre z) (EC : Type) [AddCommGroup EC] [Module C EC] (N : LieModel G z EC) (g n : ℕ) (b : Fin g → E) (S : Finset (Fin g)) (c : Fin n → E) (L : Lat ξ E) (w : Fin n → EC), IsCptGen ξ → M.lat.IsFrameAt b ⟨centre z, h⟩ → L ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (b '' S) → L.IsFrameAt c ⟨centre z, h⟩ → (∀ i, M.ValAt z (c i) (N.pt (w i))) → LinearIndependent C w := by
  intro X G _ _ _ Ω _ ξ E _ _ M C _ z h EC _ _ N g n b S c L w hξ hb hLb hLc hw
  obtain ⟨ev, h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ E M C z h EC N hξ inferInstance
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun s t est => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val est), RingHom.rangeRestrict_surjective _⟩
  let ρ : regAt ξ ⟨centre z, h⟩ →+* C :=
    (Scheme.stalkClosedPointTo z).hom.comp (e.symm : regAt ξ ⟨centre z, h⟩ →+* X.presheaf.stalk (centre z))
  have hρ : ∀ a : regAt ξ ⟨centre z, h⟩, ValAt ξ z (a : Ω) (ρ a) := fun a =>
    ⟨h, e.symm a, congrArg Subtype.val (e.apply_symm_apply a), rfl⟩
  refine linearIndependent_values (regAt ξ ⟨centre z, h⟩) ρ (M.lat ⟨centre z, h⟩) ev
    (fun a x => h2 a _ x (hρ a)) h3 b hb.2 (finrank_eq_of_isFrameAt M h N b hξ hb) S c hLc.1 ?_ w
    fun i => (h1 _ _).1 (hw i)
  rw [← hLb, hLc.2]

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodge
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LiePullSab

theorem exists_bc {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (x : Spec (CommRingCat.of R) ⟶ S) (y : Spec (CommRingCat.of R') ⟶ S)
    (hy : Spec.map (CommRingCat.ofHom f) ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E']
    [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', ∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap f)) ≫ (M.pt e).left := by
  subst hy
  let _ := f.toAlgebra
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_baseChange S G R R' x E E' M M'
  exact ⟨j, hj⟩

theorem lie_pull_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∃ j : V →+ V', (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) ∧ (∀ (a : Ω) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  intro E _ _ _ H X t X' t' f m Ω Ω' _ _ ξ ξ' i V V' _ _ _ _ M M' hξ hξ' hd
  obtain ⟨j, hj⟩ := exists_bc i ξ (ξ' ≫ f) (Eq.symm hd) M (LieMove.pushModel m.cart M')
  have hj' : ∀ e, (M'.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := hj
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePull.main X X' Ω Ω' ξ ξ' f i t.G t'.G m.φ V V' M M' j hξ hξ' hd m.cart
    t.semi.smooth hj'
  exact ⟨j, hj', h₁, h₂, h₃, h₄⟩

end GlobalTheory.CompanionTheory.Ar.LiePullSab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem model_cpt_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q :=
  PositivityTheory.Xgn.integral_model_facts

end GlobalTheory.CompanionTheory.Ar.Flat
end

