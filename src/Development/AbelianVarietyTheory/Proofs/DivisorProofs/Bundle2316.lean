module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mem_map_algebraMap_of_algHom {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) :
    e x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (e : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem K_inf_eq_and_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ →
    ∀ S S' : Sys I π s₀, S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ∧
      (S.Full hI → S'.Full hI) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc
  have key : ∀ S S' : Sys I π s₀,
      S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ≤ S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    intro S S' c hc'
    obtain ⟨hcK, hcI⟩ := hc'
    obtain ⟨Φ⟩ := _root_.GlobalTheory.LiftSys.locIso_nonempty R R₀ I hI π hπ hk X₀ s₀ S S'
    obtain ⟨-, h2, h3⟩ := _root_.GlobalTheory.LiftSys.locIso_transport R R₀ I hI π hπ hk X₀ s₀ S S' Φ
    obtain ⟨z, z', hz, hmk, hmk', hzz⟩ := h3 c hcI
    have h0 : H1.mk _ z = 0 := hmk.trans (LinearMap.mem_ker.1 hcK)
    obtain ⟨g, hg, hdg⟩ := _root_.GlobalTheory.LiftSys.cobound_I R R₀ I hI π hπ hk X₀ s₀ hc S z hz h0
    refine ⟨LinearMap.mem_ker.2 ?_, hcI⟩
    rw [← hmk']
    refine H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
    funext U V a
    rw [h2 g hg U V a, hdg, hzz]
  refine fun S S' ↦ ⟨le_antisymm (key S S') (key S' S), fun hF z₁' hz₁' ↦ ?_⟩
  obtain ⟨Ψ⟩ := _root_.GlobalTheory.LiftSys.locIso_nonempty R R₀ I hI π hπ hk X₀ s₀ S' S
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.LiftSys.locIso_transport R R₀ I hI π hπ hk X₀ s₀ S' S Ψ
  obtain ⟨z₁, hz₁, hz₁e⟩ := h1 z₁' hz₁'
  obtain ⟨c, hcI, hc₁⟩ := hF z₁ hz₁
  obtain ⟨y', y, hy'I, hy', hy, hyy⟩ := h3 c hcI
  have hyI : S.IsIdealValuedLiftSystemCocycle y := fun U V a ↦ by
    rw [hyy]; exact mem_map_algebraMap_of_algHom (Ψ.φ V : S'.F.obj V →ₐ[R] S.F.obj V) (hy'I U V a)
  have hd : H1.mk _ (y - z₁) = 0 := by rw [map_sub, hy, hc₁, sub_self]
  obtain ⟨g, hg, hdg⟩ := _root_.GlobalTheory.LiftSys.cobound_I R R₀ I hI π hπ hk X₀ s₀ hc S (y - z₁)
    (fun U V a ↦ Ideal.sub_mem _ (hyI U V a) (hz₁ U V a)) hd
  let g' : C0 S'.F := fun W ↦ (Ψ.φ W).symm (g W)
  have hg' : S'.IsIdealValuedLiftSystemCochain g' := fun W ↦
    mem_map_algebraMap_of_algHom ((Ψ.φ W).symm : S.F.obj W →ₐ[R] S'.F.obj W) (hg W)
  have hgg : (fun W ↦ Ψ.φ W (g' W)) = g := funext fun W ↦ AlgEquiv.apply_symm_apply _ _
  refine ⟨c, hcI, hy'.symm.trans (H1.mk_eq_mk.2 ⟨g', ?_⟩)⟩
  funext U V a
  apply (Ψ.φ V).injective
  have e := h2 g' hg' U V a
  rw [hgg, hdg] at e
  rw [← e]
  show y.1 U V a - z₁.1 U V a = Ψ.φ V (y'.1 U V a - z₁'.1 U V a)
  rw [map_sub, hyy, hz₁e]
end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfNotNonempty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.SqGlue

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {W : X.Opens} (h : ¬ Nonempty W) : Subsingleton Γ(X, W) := by
  have e : W = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  subst e
  infer_instance

theorem res_cancel {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    {b c : Γ(X, W)} (h : b * (X.presheaf.map (homOfLE hW).op).hom a = c * (X.presheaf.map (homOfLE hW).op).hom a) :
    b = c := by
  by_cases hn : Nonempty W
  · refine mul_right_cancel₀ (fun h0 => ha ?_) h
    apply map_injective_of_isIntegral X (homOfLE hW)
    rw [h0, map_zero]
  · exact (subsingleton_of_not_nonempty hn).elim _ _

theorem exists_unit_of_locally {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) (s : Γ(X, W))
    {t : Γ(X, V)} (ht : t ≠ 0)
    (h : ∀ x ∈ W, ∃ (O : X.Opens) (hO : O ≤ W), x ∈ O ∧ ∃ u : Γ(X, O)ˣ,
      (X.presheaf.map (homOfLE hO).op).hom s = (u : Γ(X, O)) * (X.presheaf.map (homOfLE (hO.trans hW)).op).hom t) :
    ∃ c : Γ(X, W)ˣ, s = (c : Γ(X, W)) * (X.presheaf.map (homOfLE hW).op).hom t := by
  choose O hO hx u hu using fun x : W => h x.1 x.2
  have hcov : W ≤ iSup O := fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O (fun x => (u x : Γ(X, O x))) := by
    intro x y
    refine res_cancel (W := O x ⊓ O y) (inf_le_left.trans ((hO x).trans hW)) ht ?_
    have e₁ := congrArg (X.presheaf.map (homOfLE (inf_le_left : O x ⊓ O y ≤ O x)).op).hom (hu x)
    have e₂ := congrArg (X.presheaf.map (homOfLE (inf_le_right : O x ⊓ O y ≤ O y)).op).hom (hu y)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact e₁.symm.trans e₂
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' O W (fun x => homOfLE (hO x)) hcov
    (fun x => (u x : Γ(X, O x))) hcomp
  have hc' : ∀ x, (X.presheaf.map (homOfLE (hO x)).op).hom c = (u x : Γ(X, O x)) := hc
  have hunit : IsUnit (c : Γ(X, W)) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ W c fun x hxW => ?_
    have e := X.presheaf.germ_res_apply (homOfLE (hO ⟨x, hxW⟩)) x (hx ⟨x, hxW⟩) c
    have e' := (u ⟨x, hxW⟩).isUnit.map (X.presheaf.germ (O ⟨x, hxW⟩) x (hx ⟨x, hxW⟩)).hom
    rw [← hc'] at e'
    exact e ▸ e'
  refine ⟨hunit.unit, ?_⟩
  refine X.sheaf.eq_of_locally_eq' O W (fun x => homOfLE (hO x)) hcov _ _ fun x => ?_
  change (X.presheaf.map (homOfLE (hO x)).op).hom s = (X.presheaf.map (homOfLE (hO x)).op).hom _
  rw [map_mul, res_res, IsUnit.unit_spec, hc', hu x]

theorem app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {O : X.Opens} (hU : U' ≤ U) (hO : O ≤ f ⁻¹ᵁ U')
    (s : Γ(Y, U)) :
    (X.presheaf.map (homOfLE (hO.trans (f.preimage_mono hU))).op).hom ((f.app U).hom s) =
      (X.presheaf.map (homOfLE hO).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom s)) := by
  rw [← res_res (f.preimage_mono hU) hO]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

def resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) : Γ(X, B)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom u

@[simp] theorem coe_resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) :
    (resU h u : Γ(X, B)) = (X.presheaf.map (homOfLE h).op).hom u := rfl

theorem pow_ne_zero' {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  by_cases hn : Nonempty V
  · exact pow_ne_zero n ha
  · exact (ha ((subsingleton_of_not_nonempty hn).elim _ _)).elim

end GlobalTheory.SqGlue


open GlobalTheory.SqGlue in
theorem GlobalTheory.SqGlue.main : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left), L2.IsLB → ∀ (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))) (θ : Lθ.Sec), (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ (Ix : Type) (V : Ix → G₁.left.Opens) (a : ∀ k, Γ(G₁.left, V k)), (∀ k, a k ≠ 0) → (∀ k j, ∃ u : Γ(G₁.left, V k ⊓ L2.U j)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G₁.left, V k ⊓ L2.U j)) * (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2) → (∀ k l, ∃ c : Γ(G₁.left, V k ⊓ V l)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2 = (c : Γ(G₁.left, V k ⊓ V l)) * (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (a l) ^ 2) ∧ (∀ k i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (V k)).hom (a k)) ^ 2) := by
  intro R' _ _ _ _ G₁ _ _ hsemi L2 hL h Lθ θ hθ Ix V a hne hu
  haveI : Smooth G₁.hom := hsemi.smooth
  haveI : GeometricallyConnected G₁.hom := hsemi.geomConnected
  haveI : IsIntegral G₁.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G₁
  haveI : IsIntegral (pullback G₁.hom (jK R')) := GlobalTheory.isIntegral_pullback_of_smooth G₁.hom (jK R')
  have hcov : ∀ x : G₁.left, ∃ j, x ∈ L2.U j := fun x => by
    have : x ∈ (⊤ : G₁.left.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set f := pullback.fst G₁.hom (jK R') with hf
  refine ⟨fun k l => ?_, fun k i => ?_⟩
  · refine (exists_unit_of_locally inf_le_right
      ((G₁.left.presheaf.map (homOfLE (inf_le_left : V k ⊓ V l ≤ V k)).op).hom (a k) ^ 2)
      (pow_ne_zero' (hne l) 2) fun x hx => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨ul, hul⟩ := hu l j
    have hk : V k ⊓ V l ⊓ L2.U j ≤ V k ⊓ L2.U j := inf_le_inf_right _ inf_le_left
    have hl : V k ⊓ V l ⊓ L2.U j ≤ V l ⊓ L2.U j := inf_le_inf_right _ inf_le_right
    have e1 := congrArg (G₁.left.presheaf.map (homOfLE hk).op).hom huk
    have e2 := congrArg (G₁.left.presheaf.map (homOfLE hl).op).hom hul
    rw [map_mul, map_pow, res_res, res_res] at e1 e2
    have e : (resU hk uk : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hk.trans inf_le_left)).op).hom (a k) ^ 2 =
        (resU hl ul : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hl.trans inf_le_left)).op).hom (a l) ^ 2 := by
      rw [coe_resU, coe_resU, ← e1, ← e2]
    refine ⟨V k ⊓ V l ⊓ L2.U j, inf_le_left, ⟨hx, hj⟩, (resU hk uk)⁻¹ * resU hl ul, ?_⟩
    rw [map_pow, res_res, map_pow, Units.val_mul, _root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  · have ht : (f.app (V k)).hom (a k) ≠ 0 := fun h0 =>
      hne k (GlobalTheory.ExpInt.generic_app_injective G₁ (V k) (h0.trans (map_zero _).symm))
    refine (exists_unit_of_locally inf_le_left
      ((((pullback G₁.hom (jK R')).presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V k ⊓ Lθ.U i ≤ Lθ.U i)).op).hom
        (θ.f i)) ^ 2) (pow_ne_zero' ht 2) fun y hy => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov (f.base y)
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨w, hw⟩ := hθ j i
    have hO₁ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ L2.U j ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_right)
    have hO₂ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ (V k ⊓ L2.U j) := inf_le_left
    have hO₃ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ V k ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_left)
    have e1 := congrArg ((pullback G₁.hom (jK R')).presheaf.map (homOfLE hO₁).op).hom hw
    rw [map_mul, map_pow, res_res, res_res] at e1
    rw [app_res f (inf_le_right : V k ⊓ L2.U j ≤ L2.U j) hO₂, huk, map_mul, map_mul, map_pow, map_pow,
      ← app_res f (inf_le_left : V k ⊓ L2.U j ≤ V k) hO₂] at e1
    refine ⟨_, hO₃, ⟨⟨hy.1, hj⟩, hy.2⟩, resU hO₁ w * resU hO₂ (Units.map (f.app (V k ⊓ L2.U j)).hom.toMonoidHom uk), ?_⟩
    rw [map_pow, res_res, map_pow, e1, Units.val_mul, coe_resU, coe_resU, Units.coe_map, _root_.mul_assoc]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem sym_of_lbIso_pull_hom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f →
    ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  intro S H H' _ _ f hf N M hN hM hs hiso s
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, ?_⟩
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨n, hn⟩ : ∃ n : (H.hom ⁻¹ᵁ U).toScheme ⟶ (H'.hom ⁻¹ᵁ U).toScheme,
      n ≫ (H'.hom ⁻¹ᵁ U).ι = (H.hom ⁻¹ᵁ U).ι ≫ f.left :=
    ⟨IsOpenImmersion.lift _ ((H.hom ⁻¹ᵁ U).ι ≫ f.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ U) (Over.w f)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  have hi : (GrpObj.inv : H ⟶ H).left ≫ f.left = f.left ≫ (GrpObj.inv : H' ⟶ H').left :=
    congrArg (fun q => q.left) (GrpObj.inv_hom f)
  let ψ : Fin 2 → ((H.hom ⁻¹ᵁ U).toScheme ⟶ H.left) :=
    ![(H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left, (H.hom ⁻¹ᵁ U).ι]
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame N (fun k => ψ k ≫ f.left) _ ![1, -1] n (fun k => by
    fin_cases k
    · show ((H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left) ≫ f.left =
        n ≫ (H'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H' ⟶ H').left
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc, hi]
    · show (H.hom ⁻¹ᵁ U).ι ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι
      rw [hn])) t ht
  exact exists_down hw' hN hM (φ' := ψ) c₂ h₂

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCobounda
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.SymCob
open TensorProduct

def pt (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) :
    (Spec (CommRingCat.of A)).asOver (Sp K) ⟶ (Spec (CommRingCat.of B)).asOver (Sp K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem pt_sharp (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) (b : B) :
    (pt K φ).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ b) := by
  have hn := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))).hom b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  exact hn.symm

theorem specInv_injective (R : CommRingCat) : Function.Injective (Scheme.ΓSpecIso R).inv.hom := by
  intro x y h
  have := congrArg (Scheme.ΓSpecIso R).hom.hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem secMap_surj (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D] :
    ∃ Ψ : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤) →+*
      B ⊗[K] D, ∀ x, GlobalTheory.CharExists.secMap K B D (Ψ x) = x := by
  let e : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅
      Spec (CommRingCat.of (B ⊗[K] D)) := pullbackSpecIso' K B D
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).hom.hom.comp e.inv.appTop.hom, fun x => ?_⟩
  change e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom x))) = x
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
  change (e.hom ≫ e.inv).appTop.hom x = x
  rw [e.hom_inv_id]; rfl

theorem key (K : Type) [CommRing K] (B A : Type) [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b))
    (z : B ⊗[K] B) :
    (lift f h).left.appTop.hom (GlobalTheory.CharExists.secMap K B B z) =
      j (Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b d => rw [GlobalTheory.CharExists.secMap_lift, hf, hh, Algebra.TensorProduct.lift_tmul, map_mul]

theorem mulpt (K : Type) [CommRing K] (B A : Type) [CommRing B] [HopfAlgebra K B] [CommRing A] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b)) (b : B) :
    (f * h).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      j (((Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom K B)) b) := by
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := K) (Coalgebra.comul (R := K) b)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.CharExists.mulsharp K B Y f h b S (fun i => i.1) (fun i => i.2) hS, hS, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, map_mul, hf, hh]

theorem tensor_assoc_comul_placement_eq (K B : Type) [CommRing K] [CommRing B] [Bialgebra K B] :
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B))
      (((Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B))).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Bialgebra.comulAlgHom_apply, AlgHom.coe_coe]
  have hab : a ⊗ₜ[K] Coalgebra.comul (R := K) b =
      (a ⊗ₜ[K] (1 : B ⊗[K] B)) * ((1 : B) ⊗ₜ[K] Coalgebra.comul (R := K) b) := by simp
  rw [hab, map_mul]
  simp [Algebra.TensorProduct.one_def]

theorem over_comp_appTop {S : Scheme.{0}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (v : Γ(Z.left, ⊤)) :
    (f ≫ g).left.appTop.hom v = f.left.appTop.hom (g.left.appTop.hom v) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]; rfl


set_option maxHeartbeats 1600000 in
theorem exists_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  intro K _ _ N _ _ hf c hcoc hsym
  obtain ⟨B, _, _, hcc, hfin, e, he⟩ := GlobalTheory.CharExists.pres K N hf
  obtain ⟨Ψ, hΨ⟩ := secMap_surj K B B
  obtain ⟨cG, hcG⟩ : ∃ cG : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      cG = pullTop (e.hom ⊗ₘ e.hom).left c := ⟨_, rfl⟩
  have hcB : GlobalTheory.CharExists.secMap K B B (Ψ cG) = cG := hΨ _
  have hcBu : IsUnit (Ψ cG) := cG.isUnit.map Ψ
  have hpull : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      pullTop (lift (x ≫ e.hom) (y ≫ e.hom)).left c = pullTop (lift x y).left cG := by
    intro T x y
    have : lift (x ≫ e.hom) (y ≫ e.hom) = lift x y ≫ (e.hom ⊗ₘ e.hom) := by
      rw [lift_map]
    rw [this, Over.comp_left, GlobalTheory.CharExists.pullTop_comp, hcG]
  have hmul : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      (x ≫ e.hom) * (y ≫ e.hom) = (x * y) ≫ e.hom := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

  let iL : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeRight
  have hsymB : Algebra.TensorProduct.comm K B B (Ψ cG) = Ψ cG := by
    have h := congrArg Units.val (hsym _ (pt K iL ≫ e.hom) (pt K iR ≫ e.hom))
    rw [hpull, hpull] at h
    simp only [pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    rw [← hcB, key K B _ _ _ _ iL iR _ (pt_sharp K iL) (pt_sharp K iR),
      key K B _ _ _ _ iR iL _ (pt_sharp K iR) (pt_sharp K iL)] at h
    have h' := specInv_injective _ h
    have e1 : Algebra.TensorProduct.lift iL iR (fun _ _ => Commute.all _ _) = AlgHom.id K (B ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    have e2 : Algebra.TensorProduct.lift iR iL (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.comm K B B).toAlgHom :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    rw [e1, e2] at h'
    exact h'.symm

  let ι₁ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iL
  let ι₂ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iR
  let ι₃ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeRight
  have hcocB : Ψ cG ⊗ₜ[K] (1 : B) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) (Ψ cG) =
      (Algebra.TensorProduct.assoc K K K B B B).symm ((1 : B) ⊗ₜ[K] Ψ cG *
        Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B) (Ψ cG)) := by
    have h := congrArg Units.val (hcoc _ (pt K ι₁ ≫ e.hom) (pt K ι₂ ≫ e.hom) (pt K ι₃ ≫ e.hom))
    simp only [hmul, hpull] at h
    simp only [Units.val_mul, pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    have k₁ := key K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂) (Ψ cG)
    have k₂ := key K B _ _ (pt K ι₁ * pt K ι₂) (pt K ι₃) _ ι₃ _
      (mulpt K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂)) (pt_sharp K ι₃) (Ψ cG)
    have k₃ := key K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃) (Ψ cG)
    have k₄ := key K B _ _ (pt K ι₁) (pt K ι₂ * pt K ι₃) ι₁ _ _ (pt_sharp K ι₁)
      (mulpt K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃)) (Ψ cG)
    rw [hcB] at k₁ k₂ k₃ k₄
    simp only [k₁, k₂, k₃, k₄] at h
    have h' := specInv_injective _ (((map_mul _ _ _).trans h).trans (map_mul _ _ _).symm)
    have E1 : Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₁, ι₂, iL, iR]
    have E3 : Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B)) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₂, ι₃, iL, iR]
    have E2 : Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) ι₃ (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) := by
      rw [E1]
      exact Algebra.TensorProduct.ext' fun a b => by simp [ι₃]
    have E4 : Algebra.TensorProduct.lift ι₁ ((Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
      rw [E3]
      exact tensor_assoc_comul_placement_eq K B
    rw [E2, E4, E1, E3] at h'
    simpa [map_mul] using h'
  obtain ⟨u₀, hu₀, hcu⟩ := (GlobalTheory.T.exists_twisted_groupLike') K B (Ψ cG) hcBu hcocB hsymB
  have hu := (GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul) K B (Ψ cG) hcBu u₀ hu₀ hcu
  obtain ⟨w, hw⟩ : ∃ w : Γ(((Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      w = Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom hu.unit := ⟨_, rfl⟩
  have hcu' : Ψ cG * Coalgebra.comul (R := K) (hu.unit : B) = (hu.unit : B) ⊗ₜ[K] (hu.unit : B) := by
    rw [IsUnit.unit_spec]; exact hcu
  refine ⟨pullTop e.inv.left w, fun T x y => ?_⟩
  have hc : pullTop (lift x y).left c = pullTop (lift (x ≫ e.inv) (y ≫ e.inv)).left cG := by
    have h := hpull T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    exact h
  have hxy : (x * y) ≫ e.inv = (x ≫ e.inv) * (y ≫ e.inv) := by
    have h := hmul T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    simp only [h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hval : ∀ z : T ⟶ N, ((pullTop z.left (pullTop e.inv.left w) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) =
      (z ≫ e.inv).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (hu.unit : B)) := by
    intro z
    rw [hw]
    exact (over_comp_appTop z e.inv _).symm
  letI : Algebra K Γ(T.left, ⊤) :=
    (T.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let sh : (T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) → (B →ₐ[K] Γ(T.left, ⊤)) := fun f =>
    { toRingHom := f.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      commutes' := fun k => GlobalTheory.CharExists.algsharp K B T f k }
  have kc := key K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (Ψ cG)
  have km := mulpt K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (hu.unit : B)
  rw [hcB] at kc
  have fin : (Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)) (Ψ cG) *
      ((Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (hu.unit : B) = sh (x ≫ e.inv) (hu.unit : B) * sh (y ≫ e.inv) (hu.unit : B) := by
    rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← map_mul, hcu', Algebra.TensorProduct.lift_tmul]
  simp only [hc]
  ext
  simp only [Units.val_mul, hval]
  simp only [hxy]
  simp only [pullTop, Units.coe_map, MonoidHom.coe_coe]
  simp only [kc, km, RingHom.id_apply]
  exact fin
end GlobalTheory.SymCob
end
end

