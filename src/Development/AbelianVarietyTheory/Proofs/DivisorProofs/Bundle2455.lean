module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mum

theorem intAt_of_integral_mul_basicOpen : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  intro X Y L α k s j W hW hWa x d hx hint
  have hle : X.basicOpen d ≤ W := X.basicOpen_le d
  have hW' : X.basicOpen d ≤ L.U j := hle.trans hW
  refine ⟨j, X.basicOpen d, hW', hx, hWa.basicOpen d, ?_⟩
  set ρX := (X.presheaf.map (homOfLE hle).op).hom with hρX
  set ρY := (Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom with hρY
  have hnat : ∀ r, ρY ((α.app W).hom r) = (α.app (X.basicOpen d)).hom (ρX r) := by
    intro r
    have := congrArg (fun g => g.hom r) (Scheme.Hom.naturality α (homOfLE hle).op)
    simpa [ρX, ρY] using this.symm
  have hcv : chartVal L α s j (X.basicOpen d) hW' = ρY (chartVal L α s j W hW) := by
    simp only [chartVal, ρY]
    change _ = (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op ≫
      Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom _
    rw [← Functor.map_comp]
    rfl

  have hint' : (α.app (X.basicOpen d)).hom.IsIntegralElem (ρY ((α.app W).hom d * chartVal L α s j W hW)) := by
    obtain ⟨p, hp, hp0⟩ := hint
    refine ⟨p.map ρX, hp.map ρX, ?_⟩
    rw [Polynomial.eval₂_map]
    have : ((α.app (X.basicOpen d)).hom.comp ρX) = ρY.comp (α.app W).hom := by
      ext r; exact (hnat r).symm
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨u, hu⟩ : IsUnit (ρX d) := X.toRingedSpace.isUnit_res_basicOpen d
  have hmul : ρY ((α.app W).hom d * chartVal L α s j W hW) =
      (α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW' := by
    rw [map_mul, hnat, hcv]
    congr 2
    exact hu.symm
  rw [hmul] at hint'
  have key : chartVal L α s j (X.basicOpen d) hW' =
      (α.app (X.basicOpen d)).hom ((u⁻¹ : (Γ(X, X.basicOpen d))ˣ) : Γ(X, X.basicOpen d)) *
        ((α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW') := by
    rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
  rw [key]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hint'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem sumForm_add {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x = ∑ m, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ y = ∑ m, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x + y = ∑ m, gc (c m) * gk (b m) := by
  first
  | exact @_root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | (apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral ..)

theorem isAffineOpen_Sp_field (K : Type) [Field K] (V : (Sp K).Opens) : IsAffineOpen V := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases h : (V : Set (Sp K)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    rw [this]; exact isAffineOpen_top _
  · have : V = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [this]; exact isAffineOpen_bot _

theorem eq_sum_of_isIntegral_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU f hf
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have hf' : IsIntegral Γ(G.left, W) f := hf
  have hx : IsIntegral Γ(G.left, W) (e.symm f) := hf'.map e.symm.toAlgHom
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := Γ(M.S, U)) (S := Γ(G.left, W))
    (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))).2 ⟨e.symm f, hx⟩
  have hfy : f = e ((TensorProduct.toIntegralClosure Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) y : _)) := by
    rw [congrArg Subtype.val hy]; exact (e.apply_symm_apply f).symm
  rw [hfy]
  clear hfy hy
  induction y with
  | tmul c b =>
    refine ⟨1, fun _ => c, fun _ => (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), fun _ => b.2, ?_⟩
    rw [Fin.sum_univ_one]
    exact Algebra.IsPushout.equiv_tmul _ _ _ _ c (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))
  | add u v hu hv =>
    rw [map_add (f := _), Subalgebra.coe_add, map_add (f := _)]
    exact sumForm_add _ _ _ hu hv

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobAdjoint

section Dual

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {P : LB (A ⊗ A).left}


end Dual

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

end Down

section Frob

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {A A₁ : Over (Sp R)} [GrpObj A] [GrpObj A₁]
  {π : A₁.left ⟶ A.left}

variable {G : PDivGroup p R} (t : G.TorsionTower A)

theorem absFrob_y (n : ℕ) : spMap ((absFrob hR G).app n).toRingHom ≫ (t.y n).left =
    (t.y n).left ≫ VB.frob A.left p (cast_left p R hR A) := by
  have h := natCast_eq_zero_of_algebra hR (G.A n)
  exact (congrArg (· ≫ (t.y n).left) (frob_sp p _ h (SS.FrobField.cast_zero_sp _ h)).symm).trans
    (VB.frob_naturality p _ (t.y n).left _)

theorem exists_tower (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) :
    ∃ t₁ : (frobTwist hR G).TorsionTower A₁, ∀ n,
      spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π :=
  letI := (frobRing hR).toAlgebra
  ⟨t.baseChange (O' := R) hπ, t.toBase_y (O' := R) hπ⟩

theorem map_eq_verschiebung (t₁ : (frobTwist hR G).TorsionTower A₁)
    (ht : ∀ n, spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π)
    (F : A ⟶ A₁) (V : A₁ ⟶ A) [IsMonHom F] [IsMonHom V]
    (hF : F.left ≫ π = VB.frob A.left p (cast_left p R hR A)) (hV : F ≫ V = 𝟙 A ^ p) :
    t₁.map t V = verschiebung hR G := by
  have e : t.map t₁ F = relFrob hR G := frobTwist_hom_ext hR fun n a ↦
    (t₁.semiOf_semiOf t t (s' := SemiHom.ofHom (t.map t₁ F)) (s'' := absFrob hR G) (ψ := F.left) ht
      (fun n ↦ congrArg Over.Hom.left (t.map_y t₁ F n)) (fun n ↦ by rw [hF]; exact absFrob_y hR t n) n a).symm.trans
      ((absFrob_app hR G n a).trans (relFrob_app_frobProj hR n a).symm)
  have : IsMonHom (𝟙 A ^ p) := hV ▸ inferInstance
  refine eq_verschiebung_of_relFrob_comp hR ?_
  rw [← e, ← t.map_comp, t.map_congr t hV, t.map_pow_id]

end Frob

section Pairing

open GlobalTheory.CatCoh GlobalTheory.AbLaw

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

end Pairing

end GlobalTheory.FrobAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.LabIndex

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (n : ℕ) :
    (x ^ n).left = (x' ^ n).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem eq_of_comp_fst {P X Y Z T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Mono g] {a b : T ⟶ P} (e : a ≫ fst = b ≫ fst) : a = b :=
  h.hom_ext e ((cancel_mono g).1 (by rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc, e, Category.assoc]))

theorem isDominant_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens) {K : Type} [Field K]
    (eg : Sp K ⟶ W.toScheme) (heg : ∀ w, W.ι (eg w) = genericPoint (Sp R)) : IsDominant eg := by
  refine ⟨fun w => ?_⟩
  let w0 : Sp K := genericPoint (Sp K)
  have h1 : eg w0 ⤳ w := by
    rw [← W.ι.isOpenEmbedding.isInducing.specializes_iff, heg w0]
    exact genericPoint_specializes _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w0)) (specializes_iff_mem_closure.1 h1)

theorem spMap_generic (R : Type) [CommRing R] [IsDomain R] (w : Sp (AlgebraicClosure (FractionRing R))) :
    spMap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap R (FractionRing R))) w =
      genericPoint (Sp R) := by
  have hw : w = genericPoint (Sp (AlgebraicClosure (FractionRing R))) := Subsingleton.elim _ _
  subst hw
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
    (algebraMap R (FractionRing R))) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    ((algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R (FractionRing R)))

end GlobalTheory.Poinc.LabIndex

namespace GlobalTheory.Poinc.LabIndex

theorem one_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem torsion_section_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ (S.r * S.N) = 1 → ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ t : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ FinalForm.φ = spMap ((OO p).subtype.comp ev) ≫ s.left ≫ gm → t ≫ pullback.fst _ _ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi s hs
  set ξ : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξdef
  let W : (Sp R).Opens := ξ ⁻¹ᵁ U₀
  have hrW : Set.range (W.ι ≫ ξ) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact w.2
  let w₀ : W.toScheme ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (W.ι ≫ ξ) hrW
  have hw₀ : w₀ ≫ U₀.ι = W.ι ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  have hsG : s.left ≫ G.hom = 𝟙 _ := Over.w s
  have hσw : (W.ι ≫ s.left ≫ gm) ≫ FinalForm.G.hom = w₀ ≫ U₀.ι := by
    rw [hw₀, Category.assoc, Category.assoc, hgm.1.w, ← Category.assoc s.left, hsG, Category.id_comp]
  let σ : W.toScheme ⟶ pullback ρ.P.A.hom FinalForm.u₀ := FinalForm.cart.1.lift _ _ hσw
  have hσ1 : σ ≫ FinalForm.φ = W.ι ≫ s.left ≫ gm := FinalForm.cart.1.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = w₀ := FinalForm.cart.1.lift_snd _ _ _
  have key : (W : Set (Sp R)).Nonempty →
      ∃ b : S.Gam, σ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (w₀ ≫ FinalForm.u₀) ≫ (ρ.pt b).left := by
    intro hWne
    let K := AlgebraicClosure (FractionRing R)
    let e0 : Sp K ⟶ Sp R := spMap ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)))
    have he0 : ∀ w, e0 w = genericPoint (Sp R) := spMap_generic R
    have hgW : genericPoint (Sp R) ∈ W := by
      obtain ⟨w, hw⟩ := hWne
      exact (genericPoint_specializes w).mem_open W.isOpen hw
    have hr : Set.range e0 ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      rw [he0]
      exact hgW
    let eg : Sp K ⟶ W.toScheme := IsOpenImmersion.lift W.ι e0 hr
    have heg : eg ≫ W.ι = e0 := IsOpenImmersion.lift_fac _ _ _
    haveI : IsDominant eg := isDominant_of_generic W eg (fun w => by rw [← Scheme.Hom.comp_apply, heg, he0])
    haveI : IsSeparated ρ.P.A.hom := by haveI := ρ.P.isAb.proper; infer_instance
    let T : Over (Sp R) := Over.mk e0
    have htu : (toUnit T).left = e0 := (Category.comp_id _).symm.trans (Over.w (toUnit T))
    let x1 : T ⟶ G := toUnit T ≫ s
    have hx1 : x1 ^ (S.r * S.N) = 1 := by
      show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (toUnit T) s ^ (S.r * S.N) = 1
      rw [← map_pow, hs, map_one]
    let x2 := pushHom hgm T x1
    have hx2 : x2 ^ (S.r * S.N) = 1 := by
      show pushHom hgm T x1 ^ (S.r * S.N) = 1
      rw [← map_pow, hx1, map_one]
    let T' : Over U₀.toScheme := Over.mk (eg ≫ w₀)
    let x3 : T' ⟶ (Over.pullback FinalForm.u₀).obj ρ.P.A := Over.homMk (eg ≫ σ) (by
      show (eg ≫ σ) ≫ pullback.snd _ _ = eg ≫ w₀
      rw [Category.assoc, hσ2])
    have hbase : T'.hom ≫ U₀.ι = T.hom ≫ ξ := by
      show (eg ≫ w₀) ≫ U₀.ι = e0 ≫ ξ
      rw [Category.assoc, hw₀, ← Category.assoc, heg]
    have hx3 : x3 ^ (S.r * S.N) = 1 := by
      apply Over.OverMorphism.ext
      apply eq_of_comp_fst FinalForm.cart.1
      have a1 : ((pushHom FinalForm.cart T') (x3 ^ (S.r * S.N))).left = ((pushHom FinalForm.cart T' x3) ^ (S.r * S.N)).left := by
        rw [map_pow]
      have a2 : ((pushHom FinalForm.cart T') 1).left = (1 : Over.mk (T'.hom ≫ U₀.ι) ⟶ FinalForm.G).left := by
        rw [map_one]
      have a3 := pow_left_congr hbase (pushHom FinalForm.cart T' x3) x2 (by
        show (eg ≫ σ) ≫ FinalForm.φ = (toUnit T ≫ s).left ≫ gm
        rw [Over.comp_left, htu, Category.assoc, hσ1, ← Category.assoc eg, heg]
        simp only [Category.assoc]) (S.r * S.N)
      have a4 := one_left_congr (G := FinalForm.G) hbase
      refine a1.trans (a3.trans ?_)
      rw [hx2, ← a4, ← a2]
      rfl
    let x4 := pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3
    have hx4 : x4 ^ (S.r * S.N) = 1 := by
      show pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3 ^ (S.r * S.N) = 1
      rw [← map_pow, hx3, map_one]
    obtain ⟨b, hb, -⟩ := ρ.pt_bij K (T'.hom ≫ FinalForm.u₀) x4 hx4
    refine ⟨b, ext_of_isDominant_of_isSeparated ρ.P.A.hom ?_ eg ?_⟩
    · have e1 : (ρ.pt b).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt b)
      rw [Category.assoc, pullback.condition, ← Category.assoc, hσ2, Category.assoc, e1]
      exact (Category.comp_id _).symm
    · have e2 := congrArg (fun z => z.left) hb
      simp only [Over.comp_left, Over.homMk_left] at e2
      rw [← Category.assoc, ← Category.assoc]
      exact (e2.trans rfl).symm
  by_cases hWne : (W : Set (Sp R)).Nonempty
  · obtain ⟨b, hb⟩ := key hWne
    refine ⟨b, fun p _ y ev hCen hev y₀ hAt t ht => ?_⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcW : Set.range c ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show ξ (c w) ∈ U₀
      rw [← Scheme.Hom.comp_apply, hc]
      exact hCen.2 ⟨w, rfl⟩
    let c' : Sp (PadicAlgCl p) ⟶ W.toScheme := IsOpenImmersion.lift W.ι c hcW
    have hc' : c' ≫ W.ι = c := IsOpenImmersion.lift_fac _ _ _
    have htc : t = c' ≫ σ := eq_of_comp_fst FinalForm.cart.1 (by
      rw [ht, Category.assoc, hσ1, ← Category.assoc c', hc'])
    have hq : (c' ≫ w₀) ≫ U₀.ι = gPt p ≫ y := by
      rw [Category.assoc, hw₀, ← Category.assoc, hc', hc]
    have hu : (c' ≫ w₀) ≫ FinalForm.u₀ = spMap y₀ := by
      rw [← Spec.map_preimage ((c' ≫ w₀) ≫ FinalForm.u₀)]
      congr 1
      ext a
      rw [GlobalTheory.ZH.preimage_comp_eq_val M U₀ hAdm.1.ne S.R FinalForm.u₀ FinalForm.u₀_gen, hq, ← hAt a]
      rfl
    rw [htc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hu]
  · refine ⟨0, fun p _ y ev hCen hev y₀ hAt t ht => absurd ?_ hWne⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine ⟨c (genericPoint _), ?_⟩
    show ξ (c (genericPoint _)) ∈ U₀
    rw [← Scheme.Hom.comp_apply, hc]
    exact hCen.2 ⟨_, rfl⟩

end GlobalTheory.Poinc.LabIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteNormalNormalisationProjectiveSpaceArith
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFin

theorem isFinite_fromNormalization_and_normal : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → IsFinite f.fromNormalization ∧ Geo.Tor.IsNormalScheme f.normalization := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hinj hfrac hX _ _ _ hw _
  letI : Algebra o F := b.toAlgebra
  haveI : IsFractionRing o F := by
    refine ⟨fun d => ?_, fun x => ?_, fun {x y} h => ?_⟩
    · refine IsUnit.mk0 _ ?_
      change b d ≠ 0
      exact (map_ne_zero_iff b hinj).mpr (nonZeroDivisors.ne_zero d.2)
    · obtain ⟨a, d, hd, e⟩ := hfrac x
      refine ⟨⟨a, ⟨d, mem_nonZeroDivisors_of_ne_zero fun h0 => hd (by rw [h0, map_zero])⟩⟩, e⟩
    · exact ⟨1, by simpa using hinj h⟩
  haveI : CharZero o := ⟨fun m k h => by
    have := congrArg b h
    simp only [map_natCast] at this
    exact Nat.cast_injective this⟩
  haveI : IsDedekindDomain (CommRingCat.of o) := ‹IsDedekindDomain o›
  haveI : CharZero (CommRingCat.of o) := ‹CharZero o›
  haveI hN : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hX
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IsProper (PSpace.str o n) := isProper_str o n
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine ⟨GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := CommRingCat.of o) f
    (PSpace.str o n) F s hw, ?_⟩
  exact GlobalTheory.IsNormalScheme.pred _

end GlobalTheory.ThetaFin
end
end

