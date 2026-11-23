module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0148
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0147
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem exists_gen_pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  intro E _ _ _ H X0 t k _ x p y hy κ hκ τ hτ
  have hpow : (fst (Tm x p) t.G ≫ y) ^ p = 1 := by
    have e := map_pow (preHom (fst (Tm x p) t.G)) y p
    rw [hy, map_one] at e
    exact e.symm
  have e₁ : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫ cφG t ![fst t.G t.G ^ p, snd t.G t.G] I =
      (psum t.G ![1, snd (Tm x p) t.G] I.down).left := by
    intro I
    refine congrArg (fun q => q.left) ((psum_hom (preHom (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G))) _ I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      refine (map_pow (preHom _) _ p).trans ?_
      simpa [preHom] using hpow
    · simp [preHom]
  have e₂ : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫ cφG t ![fst t.G t.G, snd t.G t.G] I =
      (psum t.G ![fst (Tm x p) t.G ≫ y, snd (Tm x p) t.G] I.down).left := by
    intro I
    refine congrArg (fun q => q.left) ((psum_hom (preHom (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G))) _ I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
    fin_cases i <;> simp [preHom]
  refine Exists.elim (exists_gen t.PP.isLB (φ' := ![pa t.G x y, pb t.G x p]) (ε' := ![(p : ℤ), -(p : ℤ)]) ?_
    (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ κ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left))
      (genPowG t _ _ (LB.pullGen t.PP.L _ _ τ (fst (Tm x p) t.G).left) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hκ _))
      (GermD.genPowG_isGen t _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) p))) ?_
  · intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    have h₁ : ∏ a₁ : ULift.{0} (Finset (Fin 2)), f ((lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫
          cφG t ![fst t.G t.G ^ p, snd t.G t.G] a₁) ^ (-cε 2 a₁) =
        (∏ I : ULift.{0} (Finset (Fin 2)), f (psum t.G ![1, snd (Tm x p) t.G] I.down).left ^
          ((-1 : ℤ) ^ (2 - I.down.card)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [e₁ I, zpow_neg]
      rfl
    have h₂ : ∏ a₂ : ULift.{0} (Finset (Fin 2)), f ((lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫
          cφG t ![fst t.G t.G, snd t.G t.G] a₂) ^ (- -((p : ℤ) * cε 2 a₂)) =
        (∏ I : ULift.{0} (Finset (Fin 2)), f (psum t.G ![fst (Tm x p) t.G ≫ y, snd (Tm x p) t.G] I.down).left ^
          ((-1 : ℤ) ^ (2 - I.down.card))) ^ (p : ℤ) := by
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [e₂ I, neg_neg, _root_.mul_comm, zpow_mul]
      rfl
    have h₃ : (fst (Tm x p) t.G).left ≫ (1 : Tm x p ⟶ t.G).left = (1 : Tm x p ⊗ t.G ⟶ t.G).left :=
      by
        have e : fst (Tm x p) t.G ≫ (1 : Tm x p ⟶ t.G) = 1 := map_one (preHom (fst (Tm x p) t.G))
        rw [← Over.comp_left, e]
    have h₄ : pa t.G x y = (fst (Tm x p) t.G ≫ y * snd (Tm x p) t.G).left := rfl
    have h₅ : pb t.G x p = (snd (Tm x p) t.G).left := rfl
    rw [h₁, h₂, prod_cube₂, prod_cube₂, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, h₃, h₄, h₅, ← Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rintro C ⟨hC, hv⟩
    refine ⟨C, hC, fun Z' r z J hJ => ?_⟩
    rw [hv Z' r z J hJ, val_mul hJ, val_inv, val_pull hJ, GermD.val_genPowG, val_pull hJ]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePullback
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem isFullLevelAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X'), ξ' ≫ f = spMap i ≫ ξ → ∀ (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ ev' : D.La → (Over.mk ξ' ⟶ t'.G), IsFullLevelAt D t' ξ' N (Units.map i.toMonoidHom z) ev' ∧ ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := by
  intro E _ _ _ H D X X' t t' f m Ω Ω' _ _ i ξ ξ' hξ N z ev hfull
  have hpb : IsPullback m.φ t'.G.hom t.G.hom f := m.cart.1
  have hsq : ∀ a, (spMap i ≫ (ev a).left) ≫ t.G.hom = ξ' ≫ f := by
    intro a
    rw [Category.assoc, Over.w (ev a)]
    exact hξ.symm
  let ev' : D.La → (Over.mk ξ' ⟶ t'.G) := fun a =>
    Over.homMk (hpb.lift (spMap i ≫ (ev a).left) ξ' (hsq a)) (hpb.lift_snd _ _ _)
  have hfst : ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := fun a => hpb.lift_fst _ _ _
  have hsnd : ∀ a, (ev' a).left ≫ t'.G.hom = ξ' := fun a => hpb.lift_snd _ _ _
  refine ⟨ev', ?_, hfst⟩
  unfold IsFullLevelAt
  intro k _ _ j
  obtain ⟨I, hIζ, hIev⟩ := hfull k (j.comp i)
  have hx : spMap (j.comp i) ≫ ξ = (spMap j ≫ ξ') ≫ f := by
    rw [spMap_comp, Category.assoc, Category.assoc, hξ]
  obtain ⟨I', hζ, hev⟩ := (tateIsoAt_move E H D X X' t t' f m k (spMap j ≫ ξ') (spMap (j.comp i) ≫ ξ) hx).1 I
  refine ⟨I', ?_, ?_⟩
  · rw [hζ, hIζ]
    simp
  · intro a
    apply hpb.hom_ext
    · rw [hev N a, hIev a, Category.assoc, hfst a, spMap_comp, Category.assoc]
    · rw [Over.w (I'.ev N a), Category.assoc, hsnd a]
      rfl

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentBaseChangeCompat
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrArch

theorem isLocalRing_of_value {Ω : Type} [Field Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (hW : ∀ a : W, φ a ≠ 0 → IsUnit a) : IsLocalRing W := by
  haveI : Nontrivial W := φ.domain_nontrivial
  refine IsLocalRing.of_nonunits_add fun a b ha hb hu => ?_
  have h0 : ∀ c : W, c ∈ nonunits W → φ c = 0 := fun c hc => by_contra fun h => hc (hW c h)
  have := hu.map φ
  rw [map_add (f := _), h0 a ha, h0 b hb, add_zero] at this
  exact not_isUnit_zero this

theorem exists_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z)
    (hv : ∀ (a : Ω₁) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) :
    ∃ σ : X.presheaf.stalk (centre z) →+* W, (∀ s, (σ s : Ω) = i (genMap ξ ⟨centre z, hz⟩ s)) ∧
      ∀ s, φ (σ s) = (Scheme.stalkClosedPointTo z).hom s := by
  have hm : ∀ s, ValAt ξ z (genMap ξ ⟨centre z, hz⟩ s) ((Scheme.stalkClosedPointTo z).hom s) :=
    fun s => ⟨hz, s, rfl, rfl⟩
  exact ⟨(i.comp (genMap ξ ⟨centre z, hz⟩)).codRestrict W fun s => (hv _ _ (hm s)).1,
    fun _ => rfl, fun s => (hv _ _ (hm s)).2⟩

theorem isLocalHom_of_value {X : Scheme.{0}} {Ω : Type} [Field Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (σ : X.presheaf.stalk (centre z) →+* W)
    (hσ : ∀ s, φ (σ s) = (Scheme.stalkClosedPointTo z).hom s) : IsLocalHom σ :=
  ⟨fun s hs => GlobalTheory.CompanionTheory.Ar.CxVal.isUnit s (by rw [← hσ]; exact (hs.map φ).ne_zero)⟩

theorem domBy_of_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (q : Cpt ξ) (W : Subring Ω) (V : ValuationSubring Ω)
    (hWV : W ≤ V.toSubring) (hloc : IsLocalHom (Subring.inclusion hWV))
    (σ : X.presheaf.stalk q.1 →+* W) (hl : IsLocalHom σ) (hσ : ∀ s, (σ s : Ω) = i (genMap ξ q s)) :
    DomBy V.toSubring i ξ q := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← hσ]
    exact hWV (σ s).2
  · rintro _ ⟨s, rfl⟩ h0 hinv
    have hi : i (genMap ξ q s) ≠ 0 := (map_ne_zero i).2 h0
    have hu : IsUnit (Subring.inclusion hWV (σ s)) := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V.toSubring) (Subtype.ext ?_)
      change ((σ s : W) : Ω) * (i (genMap ξ q s))⁻¹ = 1
      rw [hσ, mul_inv_cancel₀ hi]
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit σ s (isUnit_of_map_unit (Subring.inclusion hWV) _ hu)
    exact ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).val, map_units_inv (genMap ξ q) u⟩

theorem point_closed {X Y : Scheme.{0}} (x : X) (f : X ⟶ Y) {R : Type} [CommRing R] [IsLocalRing R]
    (σ : X.presheaf.stalk x →+* R) (hl : IsLocalHom σ) :
    (spMap σ ≫ X.fromSpecStalk x ≫ f) (IsLocalRing.closedPoint R) = f x := by
  have : IsLocalHom (CommRingCat.ofHom σ).hom := hl
  change f (X.fromSpecStalk x (Spec.map (CommRingCat.ofHom σ) (IsLocalRing.closedPoint R))) = f x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem spec_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (q : Cpt ξ) (W : Subring Ω)
    (σ : X.presheaf.stalk q.1 →+* W) (hσ : ∀ s, (σ s : Ω) = i (genMap ξ q s)) :
    spMap W.subtype ≫ spMap σ ≫ X.fromSpecStalk q.1 = spMap i ≫ ξ := by
  have e : W.subtype.comp σ = i.comp (genMap ξ q) := RingHom.ext hσ
  have e2 : spMap W.subtype ≫ spMap σ = spMap i ≫ spMap (genMap ξ q) :=
    (LieTangent.spec_comp σ W.subtype).trans
      ((congrArg (fun g => Spec.map (CommRingCat.ofHom g)) e).trans (LieTangent.spec_comp _ _).symm)
  rw [← Category.assoc, e2, Category.assoc]
  exact congrArg (spMap i ≫ ·) (LieTangent.spec_genMap ξ q)

theorem exists_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r) → (∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) → ∃ (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) ∧ (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) ∧ (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) ∧ (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) ∧ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i W φ z₁ z₂ hξ hW h₁ h₂
  haveI := isLocalRing_of_value W φ hW
  obtain ⟨σ₁, a₁, b₁⟩ := exists_stalkHom 𝔐.ξ (RingHom.id Ω) W φ z₁ (𝔐.all _) h₁
  obtain ⟨σ₂, a₂, b₂⟩ := exists_stalkHom 𝔐₀.ξ i W φ z₂ (𝔐₀.all _) h₂
  refine ⟨σ₁, σ₂, a₁, a₂, b₁, b₂, ?_⟩
  have e₁ := spec_stalkHom 𝔐.ξ (RingHom.id Ω) ⟨centre z₁, 𝔐.all _⟩ W σ₁ a₁
  have e₂ := spec_stalkHom 𝔐₀.ξ i ⟨centre z₂, 𝔐₀.all _⟩ W σ₂ a₂
  have hid : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
  rw [hid, Category.id_comp] at e₁
  have f₁ := congrArg (· ≫ 𝔐.f) e₁
  have f₂ := congrArg (· ≫ 𝔐₀.f) e₂
  simp only [Category.assoc] at f₁ f₂
  have hgen : spMap W.subtype ≫ (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f) =
      spMap W.subtype ≫ (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f) := by
    simpa only [Category.assoc] using f₁.trans (hξ.trans f₂.symm)
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 Subtype.val_injective]; exact bot_le)⟩
  have hbase : (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f) ≫ Y.s =
      (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have hsep : IsSeparated Y.s := by
    obtain ⟨N, j, hj, he⟩ := Y.proj
    letI : IsClosedImmersion j := hj
    rw [← he]
    have : IsSeparated (PSpace.str (𝓞 c.F) N) := by
      unfold PSpace.str
      infer_instance
    infer_instance
  exact ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen

end GlobalTheory.CompanionTheory.Ar.OrArch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponent
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem exists_isTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 hgen
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq Y.X _ _ 𝔐.ξ₀ (Z.ξ₀ ≫ Y.j) 𝔐.gen₀ Z.gen hgen
  have hdom' : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom (𝔐.fn.comp ψ.toRingHom)) ≫ (Z.ξ₀ ≫ Y.j) := by
    have h1 : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom 𝔐.fn) ≫ 𝔐.ξ₀ := 𝔐.fn_over
    have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (Z.ξ₀ ≫ Y.j) = 𝔐.ξ₀ := hψ
    rw [h1, ← h2, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f (𝔐.fn.comp ψ.toRingHom) := hdom'
  have key : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F)) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    have e1 := 𝔐.cst_over
    have e2 := Z.over_inc
    have e3 := Y.jQ_over
    rw [← e1, ← Category.assoc, hdom', ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, e3, ← Category.assoc Z.ξ₀, e2]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hcst : (𝔐.fn.comp ψ.toRingHom).comp Z.inc = 𝔐.cst := by
    have k0 : Spec.map (CommRingCat.ofHom (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F))) = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) := key
    have k1 := congrArg CommRingCat.Hom.hom (Spec.map_injective k0)
    simp only [CommRingCat.hom_ofHom] at k1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) k1
  letI := CategoryTheory.Over.cartesianMonoidalCategory 𝔐.X
  letI := CategoryTheory.Over.cartesianMonoidalCategory Y.X
  letI : CategoryTheory.GrpObj 𝔐.t.G := 𝔐.t.grp
  letI : CategoryTheory.GrpObj Y.t.G := Y.t.grp
  letI : Group (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  have hpb : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback 𝔐.t.G Y.t.G 𝔐.f 𝔐.m.φ := 𝔐.m.cart
  have hone : (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ = (1 : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G).left := by
    obtain ⟨o, ho⟩ : ∃ o : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, o.left = (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ :=
      ⟨Over.homMk ((1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ) (by
        rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl), rfl⟩
    have hoo : o * o = o := by
      apply Over.OverMorphism.ext
      rw [hpb.2 (Over.mk 𝔐.ξ) 1 1 o o ho ho, mul_one, ho]
    have ho1 : o = 1 := by simpa using hoo
    rw [← ho, ho1]
  have hT : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) = Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) := by
    simp [GlobalTheory.CompanionTheory.Ar.epsAt]
  have hx0 : ∀ e : 𝔐.Li, ((𝔐.M.pt e).left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f)).hom := by
    intro e
    rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : 𝔐.Li → (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := fun e => Over.homMk ((𝔐.M.pt e).left ≫ 𝔐.m.φ) (hx0 e)
  let pt' : 𝔐.Li → (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := fun e => eqToHom hT ≫ x₀ e
  have hleft : ∀ e, (pt' e).left = (𝔐.M.pt e).left ≫ 𝔐.m.φ := by
    intro e
    simp [pt', x₀]
  have hx0mul : ∀ e e', x₀ (e + e') = x₀ e * x₀ e' := by
    intro e e'
    apply Over.OverMorphism.ext
    rw [hpb.2 (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) (𝔐.M.pt e) (𝔐.M.pt e') (x₀ e) (x₀ e') rfl rfl, ← 𝔐.M.add]
    rfl
  have hadd : ∀ e e', pt' (e + e') = pt' e * pt' e' := by
    intro e e'
    simp only [pt']
    rw [hx0mul, MonObj.comp_mul]
  have htan : ∀ e, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) (pt' e) := by
    intro e
    have h := 𝔐.M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h ⊢
    rw [hleft, ← Category.assoc, h, hone]
  have hinj : Function.Injective pt' := by
    intro e e' hee
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [← hleft, ← hleft, hee]
    · rw [Over.w, Over.w]
  have hfa : (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom.comp (algebraMap Ω (DualNumber Ω)) = RingHom.id Ω := by
    ext r
    simp
  have honto : ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) v → ∃ e, pt' e = v := by
    intro v hv
    have hw : v.left ≫ Y.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f := by
      rw [Over.w]
      simp [GlobalTheory.CompanionTheory.Ar.epsAt]
    obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ 𝔐.m.φ = v.left ∧ L ≫ 𝔐.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom :=
      ⟨_, hpb.1.lift_fst _ _ hw, hpb.1.lift_snd _ _ hw⟩
    have htw : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G 𝔐.ξ (Over.homMk (U := GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) L hL2) := by
      unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hv ⊢
      apply hpb.1.hom_ext
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.m.φ = _
        rw [hL1, hv, hone]
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.t.G.hom = _
        rw [hL2, Over.w]
        show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ 𝔐.ξ = 𝔐.ξ
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    obtain ⟨e, he⟩ := 𝔐.M.onto _ htw
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    rw [hleft, he]
    exact hL1
  have hsmul : ∀ (a : Ω) (e : 𝔐.Li), (pt' (a • e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul a)) ≫ (pt' e).left := by
    intro a e
    rw [hleft, hleft, 𝔐.M.smul, Category.assoc]
  let M' : GlobalTheory.CompanionTheory.Ar.LieModel Y.t.G (𝔐.ξ ≫ 𝔐.f) 𝔐.Li := ⟨pt', htan, hinj, honto, hadd, hsmul⟩
  have hsm : AlgebraicGeometry.Smooth Y.t.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ Y.t.semi
  obtain ⟨j, hj1, hj2, -⟩ := GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.exists_ext hsm (𝔐.fn.comp ψ.toRingHom) (Z.ξ₀ ≫ Y.j) (𝔐.ξ ≫ 𝔐.f) hdom'.symm Z.M M'
  refine ⟨𝔐.fn.comp ψ.toRingHom, j, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CptIn.IsTie
  exact ⟨hdom, hcst, hj2, fun e => (hleft (j e)).symm.trans (hj1 e)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeEigenProjectorExists
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem V_eq_HT (s : CMType H ⊕ CMType H) {q : Cpt 𝔐.ξ} {p : ℕ} (hp : p ∈ S) (hq : InFibre 𝔐.ξ p q) :
    𝔐.V s q = 𝔐.HT p s q :=
  Lat.patch_of_unique S _ _ hp hq fun p' hp' h' => by
    by_contra hne
    exact Lat.not_inFibre_of_coprime q ((Nat.coprime_primes (𝔐.S_prime _ hp) (𝔐.S_prime _ hp')).2 (Ne.symm hne)) hq h'

theorem dR_le_V (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) : 𝔐.dR s q ≤ 𝔐.V s q := by
  by_cases h : ∃ p ∈ S, InFibre 𝔐.ξ p q
  · obtain ⟨p, hp, hq⟩ := h
    rw [V_eq_HT 𝔐 s hp hq]
    have hd : 𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q :=
      𝔐.M.eigLat_le_htDual _ _ _ _ q
    rcases s with τ | τ
    · intro e he
      refine Submodule.subset_span ⟨he.2, fun d _ => ?_⟩
      exact Submodule.smul_mem _ (⟨_, Sandwich.emb_mem 𝔐 _ q d⟩ : regAt 𝔐.ξ q) (hd he)
    · exact hd
  · exact (Lat.patch_of_not S _ _ fun p hp hf => h ⟨p, hp, hf⟩).ge

theorem V_le_lat_of_not (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (h : ∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) :
    𝔐.V s q ≤ 𝔐.M.lat q := by
  have e : 𝔐.V s q = 𝔐.dR s q := Lat.patch_of_not S _ _ h
  rw [e]
  exact fun _ he => he.1

theorem smul_V_mem_lat (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) {p : ℕ} (hp : p ∈ S) (hq : InFibre 𝔐.ξ p q) {κ : Ω}
    (hκ : HT.Sandwich 𝔐 p κ) (D₂ : ℕ) (hD : (D₂ : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {e : 𝔐.Li} (he : e ∈ 𝔐.V s q) :
    ((D₂ : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  obtain ⟨hκr, -, -, hS⟩ := hκ q hq
  have hdual : ∀ s' : CMType H ⊕ CMType H, ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s') q,
      κ • e ∈ 𝔐.M.lat q := fun s' e he => ((hS s').2 e he).1
  rw [V_eq_HT 𝔐 s hp hq] at he
  rcases s with τ | τ
  · change e ∈ 𝔐.M.htW 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) (differentIdeal ℤ (𝓞 E)) q at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      have h1 := hdual _ _ (hx.2 _ hD)
      rw [map_natCast, smul_smul, mul_comm] at h1
      exact h1
    | zero => simp
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul t a _ ha =>
      have : ((D₂ : Ω) * κ) • t • a = t • (((D₂ : Ω) * κ) • a) := by
        rw [show t • a = (t : Ω) • a from rfl, show t • (((D₂ : Ω) * κ) • a) = (t : Ω) • (((D₂ : Ω) * κ) • a) from rfl,
          smul_comm]
      rw [this]
      exact Submodule.smul_mem _ t ha
  · have h1 := hdual _ _ he
    rw [mul_smul]
    exact Submodule.smul_mem _ (⟨_, natCast_mem _ D₂⟩ : regAt 𝔐.ξ q) h1

end Loc

theorem hodge_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ Dn : ℕ, 0 < Dn ∧ ∀ (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = (Dn : Ω) • v) ∧ ∀ q : Cpt 𝔐.ξ, (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧ ((∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) → ∀ e ∈ 𝔐.V s q, (Dn : Ω) • e ∈ 𝔐.M.lat q) ∧ ∀ p ∈ S, InFibre 𝔐.ξ p q → ∀ κ : Ω, HT.Sandwich 𝔐 p κ → ∀ e ∈ 𝔐.V s q, ((Dn : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  intro E _ _ _
  obtain ⟨D₁, hD₁, hop⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform E
  have hdiff : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hD₂ : 0 < Ideal.absNorm (differentIdeal ℤ (𝓞 E)) :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hmem : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := Ideal.absNorm_mem _
  generalize Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = D₂ at hD₂ hmem
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, ?_⟩
  intro H D l Xo c Y S Ω _ K _ J _ y 𝔐 s
  haveI := Sandwich.charZero_of_hodgeCpt 𝔐
  obtain ⟨T₁, hT₁, hTe, hTD⟩ := hop Ω 𝔐.Li 𝔐.ρ (𝔐.emb s)
  have hreg : ∀ (q : Cpt 𝔐.ξ) (n : ℕ) {e : 𝔐.Li}, e ∈ 𝔐.M.lat q → (n : Ω) • e ∈ 𝔐.M.lat q := fun q n _ he =>
    Submodule.smul_mem _ (⟨_, natCast_mem _ n⟩ : regAt 𝔐.ξ q) he
  refine ⟨(D₂ : Ω) • T₁, fun v hv => ?_, fun q => ⟨fun e he => ?_, fun h e he => ?_, fun p hp hq κ hκ e he => ?_⟩⟩
  · rw [LinearMap.smul_apply, hTD v hv, smul_smul]
    push_cast
    rw [mul_comm]
  · have hst : T₁ e ∈ 𝔐.M.lat q :=
      Sandwich.opRing_stable (𝔐.M.lat q).toAddSubgroup (fun a e he => Sandwich.lat_act 𝔐 q a e he)
        (fun a e he => (𝔐.M.lat q).smul_mem ⟨_, Sandwich.emb_mem 𝔐 s q a⟩ he) hT₁ e he
    exact dR_le_V 𝔐 s q ⟨hreg q D₂ hst, (eigSp 𝔐.ρ (𝔐.emb s)).smul_mem _ (hTe e)⟩
  · exact hreg q _ (V_le_lat_of_not 𝔐 s q h he)
  · have h1 := hreg q D₁ (smul_V_mem_lat 𝔐 s q hp hq hκ D₂ hmem he)
    rw [smul_smul] at h1
    have e1 : ((D₁ * D₂ : ℕ) : Ω) * κ = (D₁ : Ω) * ((D₂ : Ω) * κ) := by
      push_cast
      ring
    rw [e1]
    exact h1

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PelUniformisedGeometricFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Unif

theorem geomPF_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (IsLocalRing.maximalIdeal R) t), GeomPF t (spMap (IsLocalRing.residue R)) :=
  PositivityTheory.HtPt.Cg.unif_pf

end GlobalTheory.CompanionTheory.Ar.Unif
end

