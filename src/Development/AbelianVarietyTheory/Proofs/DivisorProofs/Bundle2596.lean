module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLifts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
theorem secLift_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (a.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a h)).op).hom ((a.app U).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem secLift_comp_app {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)) :
    ((a ≫ f).app U).hom x = (a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x) := by
  simp [Scheme.Hom.comp_app]
  rfl

theorem secLift_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (k : ℤ))).g i j).val =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) j 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (j 0))).hom (L.g (i 0) (j 0)))) ^ k := by
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl
theorem secLift_rr {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem secLift_res_comp {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Z.Opens}
    (h : V ≤ (a ≫ f) ⁻¹ᵁ U) (h' : V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U)) (x : Γ(X, U)) :
    (Z.presheaf.map (homOfLE h).op).hom (((a ≫ f).app U).hom x) =
      (Z.presheaf.map (homOfLE h').op).hom ((a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x)) := by
  rw [secLift_comp_app]
  rfl
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secLift_compat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (s : SecK L φ k) (i i' : Fin 1 → L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (s.f i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (s.f i') := by
  have h := s.compat i i'
  rw [secLift_g] at h
  exact h

def secLift_ofCompat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (σf : ∀ i : Fin 1 → L.ι, Γ(Y, LB.wchart L (K := Fin 1) (fun _ => φ) i))
    (h : ∀ i i' : Fin 1 → L.ι, (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (σf i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (σf i')) :
    SecK L φ k where
  f := σf
  compat i i' := (h i i').trans (congrArg (· * _) (secLift_g L φ k i i').symm)

set_option maxHeartbeats 1000000 in
theorem secK_lift_of_local_lift : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  intro X X' Y L f a α e k hinj s n j W hWtop hW hloc
  subst e
  have step1 : ∀ j' : Fin 1 → L.ι, ∃ y : Γ(X', LB.wchart L (K := Fin 1) (fun _ => f) j'),
      (a.app _).hom y = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a (a ≫ f) rfl j')).op).hom (s.f j') := by
    intro j'
    refine GlobalTheory.T.exists_preimage_of_local_preimages_injective a hinj _ W (by rw [hWtop]; exact le_top) _ ?_
    intro b
    obtain ⟨y, hy⟩ := hloc b
    have h1 : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ f ⁻¹ᵁ (L.U (j' 0) ⊓ L.U (j b)) :=
      fun x hx => ⟨LB.wchart_le L (K := Fin 1) (fun _ => f) j' 0 hx.1, hW b hx.2⟩
    refine ⟨(X'.presheaf.map (homOfLE h1).op).hom ((f.app _).hom (L.g (j' 0) (j b))) ^ k *
      (X'.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ W b)).op).hom y, ?_⟩
    have hc2 := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b) ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) j' ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) (fun _ => j b) from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl j' hx.1, extLI_le_chart L f a (a ≫ f) rfl (W b) (j b) (hW b) hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s j' (fun _ => j b))
    rw [map_mul, map_pow] at hc2
    erw [secLift_rr, secLift_rr, secLift_rr] at hc2
    rw [map_mul, map_pow, secLift_app_res, secLift_app_res, hy]
    erw [secLift_rr, secLift_rr]
    rw [hc2]
    exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f _ _ _ _).symm
  choose σf hσ using step1
  refine ⟨secLift_ofCompat L f k σf fun i i' => ?_, hσ⟩
  apply hinj (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i')
  have hG : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i 0))
      (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i' 0))
  have e1 := secLift_app_res a (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i) (σf i)
  have e2 := secLift_app_res a hG ((f.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))
  have e3 := secLift_app_res a (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i') (σf i')
  rw [map_mul, map_pow, e1]
  erw [e2, e3]
  rw [hσ, hσ]
  erw [secLift_rr, secLift_rr]
  have hc := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i') ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i' from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl i hx.1, extLI_le_wchart L f a (a ≫ f) rfl i' hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s i i')
  rw [map_mul, map_pow] at hc
  erw [secLift_rr, secLift_rr, secLift_rr] at hc
  rw [hc]
  exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f (L.U (i 0) ⊓ L.U (i' 0)) _ _ _)
end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_localModel_graph_of_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_locModel_graph | exact GlobalTheory.GraphLocal.exists_locModel_graph | (intros; apply GlobalTheory.GraphLocal.exists_locModel_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | exact GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | (intros; apply GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedTranslatedBundleIsoPsiZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Norm

section General

variable {X X' S : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_iso (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (e : S ⟶ X) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
        e' (r z) ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j → e' (r z) ∈ L'.U q →
        gv w (r ≫ e') z j q = gm ((r ≫ e') ≫ Φ) z (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) *
          (gm r z (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹ := by
  have hw := (isGen_iff w₀).1 hw₀
  obtain ⟨u, hu, vu⟩ := exists_up hw hL hL' (K := PUnit) (φ' := fun _ => e') (ε := fun _ => 1) ρ' hρ'
  have l₀ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      (L.pull Φ).U (fun _ => j 0) ⊓ L'.U q := fun j q x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx.1 0), hx.2⟩
  have l₁ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 1
  have l₂ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 2
  let w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε) :=
    ⟨fun c => res (l₀ c.1 c.2) (w₀.s (fun _ => c.1 0, c.2)) *
      (res (l₁ c.1 c.2) (pullU p _ (u.s (fun _ => c.1 1))))⁻¹ * res (l₂ c.1 c.2) (pullU p _ (ρ.s (fun _ => c.1 2)))⟩
  have vw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X') (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
      f z ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q →
      gm f z (LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q) (w.s (j, q)) = gw w₀ f z (j 0) q *
        (gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1)) (u.s (fun _ => j 1)))⁻¹ *
        gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) := fun Z f z j q hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₀ j q) hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ j q) hz _).trans (gm_pull f p z _ (l₁ j q hz) _))))))
      ((gm_res f z (l₂ j q) hz _).trans (gm_pull f p z _ (l₂ j q hz) _)))
  refine ⟨w, ?_, fun Z r z j q hj hq => ?_⟩
  · rintro ⟨j, q⟩ ⟨j', q'⟩
    refine unit_ext fun x hx => ?_
    refine ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j q hx.1)).trans (Eq.symm ((map_mul _ _ _).trans
      ((congrArg₂ (· * ·) ((gm_div L' _ (𝟙 X') x (j, q) (j', q') hx).trans
        (congrArg (· * _) (gm_linComb L _ twε (𝟙 X') x j j' hx.1.1 hx.2.1)))
        ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j' q' hx.2))).trans ?_)))
    rw [hw _ (𝟙 X') x (j 0) (j' 0) q q' (Set.mem_iInter.1 hx.1.1 0) (Set.mem_iInter.1 hx.2.1 0) hx.1.2 hx.2.2,
      gen_trans hu (𝟙 X' ≫ p) x (l₁ j q hx.1) (l₁ j' q' hx.2), gen_trans hρ (𝟙 X' ≫ p) x (l₂ j q hx.1) (l₂ j' q' hx.2),
      Fin.prod_univ_three]
    simp only [trF, Fintype.prod_unique, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_one,
      zpow_neg, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
    have hz : p (e' (r z)) = r z := congrArg (fun g => g z) hp
    have m₀ : Φ (e' (r z)) ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have m₁ : Φ (e' (r z)) ∈ L.U (j 1) := by
      have : Φ (e' (p (e' (r z)))) ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
      rwa [hz] at this
    refine (vw Z (r ≫ e') z j q ⟨hj, hq⟩).trans ?_
    rw [hp, vu Z r z (fun _ => j 1) (fun _ => q) (Set.mem_iInter.2 fun _ => m₁) (Set.mem_iInter.2 fun _ => hq),
      pw, Fintype.prod_unique, zpow_one, hw Z (r ≫ e') z (j 0) (j 1) q q m₀ m₁ hq hq, gm_self hL' (r ≫ e') z hq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, inv_one, ofMul_one]
    abel

theorem exists_iso_maps (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (b e : S ⟶ X) (hb : e' ≫ Φ = b) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) {Y : Scheme.{0}} (r : Y ⟶ S) (x : Y ⟶ X') (hx : x = r ≫ e')
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x) (fun _ => -1)))
    (ha : ∀ (y : Y) (q : L'.ι), e' (r y) ∈ L'.U q →
      gm (𝟙 Y) y (LB.wchart L' (fun _ : PUnit => x) (fun _ => q)) (a.s (fun _ => q)) =
        (gm r y (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ b, p ≫ e] twε), w.IsGen ∧
      ∃ t : LB.Gen (LB.LinComb L (fun i => x ≫ (![Φ, p ≫ b, p ≫ e] : Fin 3 → (X' ⟶ X)) i) (fun i => -1 * twε i)),
        MapsAtExp L L' ![Φ, p ≫ b, p ≫ e] twε w x (-1) a t ∧
        ∀ y J, Good L y J → val t (𝟙 Y) y J = (val ρ r y J)⁻¹ := by
  subst hb hx
  obtain ⟨w, hw, vw⟩ := exists_iso hL hL' p e' he Φ e ρ' hρ' ρ hρ w₀ hw₀
  have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
  have hz : ∀ z, p (e' (r z)) = r z := fun z => congrArg (fun g => g z) hp
  have l₁ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        ((r ≫ e') ≫ Φ) ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, by
    have : Φ (e' (p (e' (r y)))) ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    rw [hz] at this
    exact this⟩
  have l₂ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        r ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j y hy => Set.mem_iInter.2 fun _ => by
    have : e (p (e' (r y))) ∈ L.U (j 2) := Set.mem_iInter.1 hy 2
    rw [hz] at this
    exact this
  let t : LB.Gen (LB.LinComb L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i)
      (fun i => -1 * twε i)) :=
    ⟨fun j => (res (l₁ j) (pullU ((r ≫ e') ≫ Φ) (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1))) * res (l₂ j) (pullU r _ (ρ.s (fun _ => j 2))))⁻¹⟩
  have vt : ∀ (y : Y) (j : Fin 3 → L.ι),
      y ∈ LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j →
      gm (𝟙 Y) y (LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j) (t.s j) =
        (gm ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r y (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)))⁻¹ := fun y j hy =>
    (map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 Y) y (l₁ j) hy _).trans ((gm_pull (𝟙 Y) ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (l₁ j hy) _).trans (by rw [Category.id_comp])))
      ((gm_res (𝟙 Y) y (l₂ j) hy _).trans ((gm_pull (𝟙 Y) r y _ (l₂ j hy) _).trans (by rw [Category.id_comp]))))))
  refine ⟨w, hw, t, fun j q => unit_ext fun y hy => ?_, fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 Y) y _ hy _).trans (vt y j (mapsAtExp_le_b L L' _ twε _ j q hy))).trans
      (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ))
        ((gm_pull (𝟙 Y) (r ≫ e') y _ hy _).trans ((congrArg (fun f => gv w f y j q) (Category.id_comp _)).trans
          (vw Y r y j q hy.1 hy.2))))) ((gm_res (𝟙 Y) y _ hy _).trans (ha y q hy.2))).trans ?_)))
    rw [zpow_neg, zpow_one, ← mul_inv, inv_mul_cancel_right]
  · have e₁ : (r ≫ e') ≫ p ≫ e' ≫ Φ = (r ≫ e') ≫ Φ := by rw [← Category.assoc, hp, Category.assoc]
    have e₂ : (r ≫ e') ≫ p ≫ e = r ≫ e := by rw [← Category.assoc, hp]
    rw [val_of t (𝟙 Y) y J ![J ((r ≫ e') ≫ Φ), J ((r ≫ e') ≫ Φ), J (r ≫ e)] (fun k => by
      rw [Category.id_comp]
      fin_cases k
      exacts [rfl, congrArg J e₁, congrArg J e₂])]
    refine (vt y _ (Set.mem_iInter.2 fun k => ?_)).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ e') ≫ Φ)
      · show ((r ≫ e') ≫ p ≫ e' ≫ Φ) y ∈ L.U (J ((r ≫ e') ≫ Φ))
        rw [e₁]; exact hJ _
      · show ((r ≫ e') ≫ p ≫ e) y ∈ L.U (J (r ≫ e))
        rw [e₂]; exact hJ _
    · exact congrArg (·⁻¹) ((congrArg (· * _) (gm_self hL ((r ≫ e') ≫ Φ) y (hJ _))).trans (_root_.one_mul _))

end General

theorem exists_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A), IsMonHom β → ∀ w₀ : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left), w₀.IsGen → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  intro R _ _ I D D₂ g β hβ w₀ hw₀
  have hb : eSec D₂.toPre.P.A ≫ (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left = g.b.left := by
    rw [eSec, ← Over.comp_left]
    congr 1
    show η[D₂.toPre.P.A] ≫ (β * (toUnit D₂.toPre.P.A ≫ g.b)) = g.b
    have h₁ : η[D₂.toPre.P.A] ≫ β = 1 := by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have h₂ : η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A = 𝟙 _ := toUnit_unique _ _
    rw [MonObj.comp_mul, h₁, ← Category.assoc, h₂, Category.id_comp, _root_.one_mul]
  have he : eSec D₂.toPre.P.A ≫ (toUnit D₂.toPre.P.A).left = 𝟙 _ := by
    rw [eSec, ← Over.comp_left, toUnit_unique (η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A) (𝟙 _)]
    rfl
  obtain ⟨w, hw, t, h₁, h₂⟩ := exists_iso_maps D.toPre.P.isLB D₂.toPre.P.isLB (toUnit D₂.toPre.P.A).left
    (eSec D₂.toPre.P.A) he _ g.b.left (eSec D.toPre.P.A) hb D₂.toPre.rig D₂.toPre.rig_gen D.toPre.rig D.toPre.rig_gen
    w₀ hw₀ (jK R) (D₂.toPre.xK 0) (Uniq.xK_zero D₂.toPre) (D₂.toPre.psi 0)
    (fun y q hq => Uniq.gm_psi_zero D₂.tau_bimult 0 rfl y q hq)
  refine ⟨w, hw, t, h₁, corr_of_val D.toPre.P.isLB fun y J hJ => (h₂ y J hJ).trans ?_⟩
  refine Eq.symm ((val_mul hJ _ _ _).trans ?_)
  rw [PsiZero.val_psi_zero D.tau_bimult hJ, val_pull hJ, val_corr hJ g.s_zero, val_one, _root_.mul_one]

end GlobalTheory.MumCmp.Norm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ g : Fn2 A, IsSecAdd n S g := by
  intro R _ A _ _ n hr b hb S hS
  have difference (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) :=
    (GlobalTheory.sec_mul_diff R A n hr b hb D x y (S D x) (S D y) (S D (x * y))
      (hS D x) (hS D y) (hS D (x * y))).exists
  refine ⟨fun D _ _ x y ↦ (difference D x y).choose, ?_⟩
  intro D _ _ x y E _ _ ψ z w hz hw
  exact ((difference D x y).choose_spec E ψ z w hz hw).symm

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfExtendsOverCompleteDvrs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SecExtend

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left}

theorem pullS_homMk_id {F : Type} [CommRing F] {x : Sp F ⟶ S} (t : SecAt G L x) :
    VVRank.pullS G _ (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) t = t := by
  have e : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := Over.OverMorphism.ext rfl
  refine ThetaRuleCompare.sec_ext fun j => fn_ext fun y hy => ?_
  refine (ThetaRuleCompare.gs_pullS _ t (𝟙 _) y j hy).trans ?_
  rw [e, MonoidalCategory.id_whiskerRight, Over.id_left, Category.id_comp]

theorem eq_pullS_of_cast {F : Type} [CommRing F] {x₁ x₂ : Sp F ⟶ S} (h : x₁ = x₂)
    (t : SecAt G L x₁) (u : SecAt G L x₂) (E : SecM.ofSec G u = SecM.ofSec G (h ▸ t)) :
    u = VVRank.pullS G _ (Over.homMk (𝟙 _) (by simp [h]) : Over.mk x₂ ⟶ Over.mk x₁) t := by
  subst h
  rw [pullS_homMk_id]
  exact ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val E) j

theorem gs_appLE {Z Y : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (O : Z.Opens) (h : O ≤ g ⁻¹ᵁ U) (b : Γ(Y, U))
    (z : Z) (hz : z ∈ O) : gs (𝟙 Z) z O ((g.appLE U O h).hom b) = gs g z U b :=
  (gs_res (𝟙 Z) z h hz ((g.app U).hom b)).trans
    ((gs_pull (𝟙 Z) g z U (h hz) b).trans (by rw [Category.id_comp]))

theorem exists_sec_of_extends : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt G L (spMap (algebraMap R (FractionRing R)) ≫ χ)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ σ : SecAt G L (spMap φ ≫ χ), SecM.ofSec G (SecAt.pull G L σ (algebraMap V (FractionRing V))) = SecM.ofSec G (h ▸ SecAt.pull G L θ φK)) → ∃ σ : SecAt G L χ, SecM.ofSec G (SecAt.pull G L σ (algebraMap R (FractionRing R))) = SecM.ofSec G θ := by
  intro S G _ L hL hG R _ _ _ _ _ χ θ H
  obtain ⟨hLN, hN, hPre, hInj⟩ := _root_.GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic S G hG R χ
  let hK : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ :=
    Over.homMk (spMap (algebraMap R (FractionRing R))) rfl
  let fK : ∀ j, Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left,
      (hK ▷ G).left ⁻¹ᵁ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j) := fun j =>
    ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left.presheaf.map
      (homOfLE (ThetaRuleCompare.chart_ge hK j)).op).hom (θ.f j)
  have ext : ∀ j, ∃ s : Γ((Over.mk χ ⊗ G).left, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j),
      ((hK ▷ G).left.app _).hom s = fK j := fun j =>
    GenericExtend.exists_app_eq (hK ▷ G).left hInj _ (fK j) (_root_.GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one S G hG R χ _ (fK j) (by
      intro V _ _ _ hV φ φK h hφ
      obtain ⟨σV, E⟩ := H V hV φ φK h hφ
      let hφR : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap φ) rfl
      let hVV : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ) :=
        Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
      let B : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
          Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) := Over.homMk (spMap φK) h
      have E' := eq_pullS_of_cast G h _ _ E
      have E'' : VVRank.pullS G _ hVV σV = VVRank.pullS G _ B θ := by
        refine E'.trans ((ThetaRuleCompare.pullS_comp _ _ θ).trans ?_)
        congr 1
      refine ⟨((Over.mk (spMap φ ≫ χ) ⊗ G).left.presheaf.map
        (homOfLE (ThetaRuleCompare.chart_ge hφR j)).op).hom (σV.f j), fun O h₁ h₂ => fn_ext fun x hx => ?_⟩
      have hx₁ := h₁ hx
      have hx₂ := h₂ hx
      have hxc : x ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ))).U j :=
        ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hVV j (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hφR j hx₁)
      rw [gs_appLE _ _ _ _ _ x hx, gs_appLE _ _ _ _ _ x hx, gs_res _ x _ hx₁, gs_res _ x _ hx₂]
      have a₁ := ThetaRuleCompare.gs_pullS hVV σV (𝟙 _) x j hxc
      have a₂ := ThetaRuleCompare.gs_pullS B θ (𝟙 _) x j hxc
      rw [Category.id_comp] at a₁ a₂
      rw [← a₁, ← a₂, E'']))
  choose s hs using ext
  have hv : ∀ j (w : (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left),
      (hK ▷ G).left w ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j →
      gs (𝟙 _ ≫ (hK ▷ G).left) w _ (s j) = gs (𝟙 _) w _ (θ.f j) := fun j w hw =>
    (gs_pull (𝟙 _) _ w _ hw _).symm.trans ((congrArg (gs (𝟙 _) w _) (hs j)).trans
      (gs_res (𝟙 _) w (ThetaRuleCompare.chart_ge hK j) hw _))
  refine ⟨⟨s, fun j j' => hInj _ (fn_ext fun w hw => ?_)⟩,
    congrArg (SecM.ofSec G) (ThetaRuleCompare.sec_ext fun j => fn_ext fun w hw => ?_)⟩
  · have hw' : (𝟙 _ ≫ (hK ▷ G).left) w ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ⊓
        (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j' := hw
    refine (gs_pull (𝟙 _) _ w _ hw' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ w _ hw' _).symm)
    refine ((gs_res _ w _ hw' _).trans ((hv j w hw'.1).trans
      (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) G).left)
        (ε := fun _ => ((1 : ℕ) : ℤ)) θ (𝟙 _) w
        (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hK j hw'.1)
        (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hK j' hw'.2)))).trans (Eq.symm ?_)
    refine (gs_mul _ w _ hw' _ _).trans (congrArg₂ (· * ·) ((gs_unit _ w _ hw' _).trans (congrArg Units.val
      ((gm_linComb L _ _ _ w j j' hw'.1 hw'.2).trans ?_))) ((gs_res _ w _ hw' _).trans (hv j' w hw'.2)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, VVRank.whisker_snd_left]
  · exact (ThetaRuleCompare.gs_pullS hK _ _ w j hw).trans
      (hv j w (chart_le_res G L (hK ▷ G) (whiskerRight_snd _ _) _ j hw))
end GlobalTheory.UMin.SecExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionLabels_genericFibre_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  first | exact @GlobalTheory.Mum.Trait.exists_lab_pull | exact GlobalTheory.Mum.Trait.exists_lab_pull | (intros; apply GlobalTheory.Mum.Trait.exists_lab_pull <;> assumption)
end

