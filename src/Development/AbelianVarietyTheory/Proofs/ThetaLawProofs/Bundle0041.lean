module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.GeomComp

theorem exists_idempotent {A : Type} [CommRing A] [IsNoetherianRing A]
    (h : ∀ (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q)) (P : Ideal A) [P.IsPrime] :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ P ∧ ∀ x y : A, e * (x * y) = 0 → e * x = 0 ∨ e * y = 0 := by
  classical
  let z : ∀ (q : Ideal A) [q.IsPrime], Ideal A := fun q _ =>
    RingHom.ker (algebraMap A (Localization.AtPrime q))
  have zp : ∀ (q : Ideal A) [q.IsPrime], (z q).IsPrime := fun q _ =>
    haveI := h q
    RingHom.ker_isPrime _
  have zm : ∀ (q : Ideal A) [q.IsPrime] (a : A), a ∈ z q ↔ ∃ s ∉ q, s * a = 0 := fun q _ a => by
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff q.primeCompl]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, s.2, hs⟩, fun ⟨s, hs, hs'⟩ => ⟨⟨s, hs⟩, hs'⟩⟩
  have zle : ∀ (q r : Ideal A) [q.IsPrime] [r.IsPrime], r ≤ q → z q ≤ r := fun q r _ hr hrq a ha => by
    obtain ⟨s, hs, hs'⟩ := (zm q a).1 ha
    exact (hr.mem_or_mem (hs' ▸ r.zero_mem)).resolve_left fun h => hs (hrq h)
  have htop : z P ⊔ (z P).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hm.isPrime
    haveI := zp P
    haveI := zp m
    have h1 : z m ≤ z P := zle m (z P) (le_sup_left.trans hle)
    have h2 : z P ≤ z m := zle P (z m) (h1.trans (zle P P le_rfl))
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian (z P)
    have h3 : ∀ a : s, ∃ t ∉ m, t * (a : A) = 0 := fun a =>
      (zm m a).1 (h2 (by rw [← hs]; exact Submodule.subset_span a.2))
    choose t ht ht' using h3
    have h4 : ∏ a, t a ∈ (z P).annihilator := by
      rw [← hs, Submodule.mem_annihilator_span]
      intro a
      obtain ⟨r, hr⟩ : t a ∣ ∏ a, t a := Finset.dvd_prod_of_mem t (Finset.mem_univ _)
      rw [hr, smul_eq_mul, mul_right_comm, ht', zero_mul]
    obtain ⟨a, -, ha⟩ := Ideal.IsPrime.prod_mem_iff.1 (le_sup_right.trans hle h4)
    exact ht a ha
  obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : A) ∈ _)
  have hk : ∀ a ∈ z P, e * a = 0 := fun a ha => Submodule.mem_annihilator.1 he a ha
  have hfP : f ∈ P := zle P P le_rfl hf
  have heP : e ∉ P := fun h' =>
    Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 (hfe ▸ P.add_mem hfP h'))
  refine ⟨e, ?_, heP, fun x y hxy => ?_⟩
  · have := hk f hf
    unfold IsIdempotentElem
    linear_combination e * hfe - this
  · exact ((zp P).mem_or_mem ((zm P _).2 ⟨e, heP, hxy⟩)).imp (hk x) (hk y)

theorem isDomain_away {A : Type} [CommRing A] {e : A} (he : IsIdempotentElem e) (h0 : e ≠ 0)
    (h : ∀ x y : A, e * (x * y) = 0 → e * x = 0 ∨ e * y = 0)
    (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away e S] : IsDomain S := by
  have hz : ∀ a : A, algebraMap A S a = 0 ↔ e * a = 0 := fun a => by
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers e)]
    refine ⟨fun ⟨⟨_, n, rfl⟩, hn⟩ => ?_, fun h => ⟨⟨e, Submonoid.mem_powers e⟩, h⟩⟩
    have h1 : e ^ (n + 1) * a = 0 := by
      rw [pow_succ', _root_.mul_assoc]
      exact (congrArg (e * ·) hn).trans (mul_zero _)
    rwa [he.pow_succ_eq] at h1
  have hs := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he (S := S)
  haveI : Nontrivial S := ⟨1, 0, fun h1 => h0 (by simpa using (hz 1).1 (by rw [map_one, h1]))⟩
  haveI : NoZeroDivisors S := ⟨fun {a b} hab => by
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    rw [← map_mul, hz] at hab
    rw [hz, hz]
    exact h x y hab⟩
  exact NoZeroDivisors.to_isDomain S

theorem isDomain_tensor_of_isAlgClosed (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (F : Type) [Field F] [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let f : Spec (.of A) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hf : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hi : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral (Spec (.of A)))
  have hg : GeometricallyIntegral f :=
    GlobalTheory.geometricallyIntegral_of_isIntegral_of_isAlgClosed K (Over.mk f) hf
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := IsIntegral.of_isIso (pullbackSpecIso K F A).hom
  exact (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this

theorem isDomain_tensor_of_closure (k Ω S : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsDomain (Ω ⊗[k] S)]
    (F : Type) [Field F] [Algebra k F] : IsDomain (F ⊗[k] S) := by
  let L := AlgebraicClosure F
  let j : Ω →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω L := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Ω L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI := isDomain_tensor_of_isAlgClosed Ω (Ω ⊗[k] S) L
  haveI : IsDomain (L ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω L L S).symm.toMulEquiv.isDomain _
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F L) (AlgHom.id k S)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S)
      (IsScalarTower.toAlgHom k F L).toLinearMap (algebraMap F L).injective
  exact Function.Injective.isDomain φ.toRingHom hφ

theorem geomInt_away (k Ω B : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing B] [Algebra k B] [Algebra.Smooth k B] (e : B)
    (he : IsIdempotentElem e) (h0 : ((1 : Ω) ⊗ₜ[k] e) ≠ 0)
    (h : ∀ x y : Ω ⊗[k] B, ((1 : Ω) ⊗ₜ[k] e) * (x * y) = 0 →
      ((1 : Ω) ⊗ₜ[k] e) * x = 0 ∨ ((1 : Ω) ⊗ₜ[k] e) * y = 0) :
    GeomInt k (Localization.Away e) := by
  haveI : Algebra.Smooth B (Localization.Away e) := Algebra.Smooth.of_isLocalization_Away e
  haveI : Algebra.Smooth k (Localization.Away e) := Algebra.Smooth.comp k B _
  refine ⟨this, fun F _ _ => ?_⟩
  letI : Algebra (Ω ⊗[k] B) (Ω ⊗[k] Localization.Away e) :=
    (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      (IsScalarTower.toAlgHom k B (Localization.Away e))).toAlgebra
  haveI : IsScalarTower Ω (Ω ⊗[k] B) (Ω ⊗[k] Localization.Away e) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k Ω (Submonoid.powers e)
    (Localization.Away e) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hloc
  have he' : IsIdempotentElem ((1 : Ω) ⊗ₜ[k] e) :=
    he.map (Algebra.TensorProduct.includeRight (R := k) (A := Ω) (B := B))
  haveI : IsLocalization.Away ((1 : Ω) ⊗ₜ[k] e) (Ω ⊗[k] Localization.Away e) := hloc
  haveI := isDomain_away he' h0 h (Ω ⊗[k] Localization.Away e)
  exact isDomain_tensor_of_closure k Ω _ F

theorem geomInt_away_baseChange (K k Ω R : Type) [Field K] [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra K k]
    [Algebra k Ω] [Algebra K Ω] [IsScalarTower K k Ω] [Algebra.IsAlgebraic k Ω] [CommRing R] [Algebra K R]
    [Algebra.Smooth K R] (e : k ⊗[K] R) (he : IsIdempotentElem e)
    (h0 : Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e ≠ 0)
    (h : ∀ x y : Ω ⊗[K] R,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * (x * y) = 0 →
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * x = 0 ∨
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * y = 0) :
    GeomInt k (Localization.Away e) := by
  let φ := Algebra.TensorProduct.cancelBaseChange K k Ω Ω R
  have hφ : ∀ x : k ⊗[K] R, φ ((1 : Ω) ⊗ₜ[k] x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [φ, Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add (f := _), hx, hy]
  refine geomInt_away k Ω (k ⊗[K] R) e he (fun h => h0 ?_) (fun x y hxy => ?_)
  · rw [← hφ, h, map_zero]
  · have h1 := congrArg φ hxy
    rw [map_mul, map_mul, map_zero, hφ] at h1
    refine (h _ _ h1).imp (fun h => φ.injective ?_) (fun h => φ.injective ?_) <;>
      rw [map_mul, map_zero, hφ, h]

theorem exists_finite_level (K C R : Type) [Field K] [Field C] [Algebra K C] [CommRing R] [Algebra K R]
    (Ω : IntermediateField K C) [Algebra.IsAlgebraic K Ω] (x : Ω ⊗[K] R) :
    ∃ (k : IntermediateField K C) (hk : k ≤ Ω) (e : k ⊗[K] R), FiniteDimensional K k ∧
      Algebra.TensorProduct.map (IntermediateField.inclusion hk) (AlgHom.id K R) e = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, bot_le, 0, inferInstance, map_zero _⟩
  | tmul a r =>
    have ha : _root_.IsIntegral K (a : C) :=
      (Algebra.IsAlgebraic.isAlgebraic a).isIntegral.map Ω.val
    refine ⟨IntermediateField.adjoin K {(a : C)}, by simp,
      ⟨a, IntermediateField.mem_adjoin_simple_self K _⟩ ⊗ₜ r,
      IntermediateField.adjoin.finiteDimensional ha, ?_⟩
    rfl
  | add x y hx hy =>
    obtain ⟨k₁, h₁, e₁, f₁, rfl⟩ := hx
    obtain ⟨k₂, h₂, e₂, f₂, rfl⟩ := hy
    have key : ∀ (a b : IntermediateField K C) (hab : a ≤ b) (hb : b ≤ Ω) (e : a ⊗[K] R),
        Algebra.TensorProduct.map (IntermediateField.inclusion hb) (AlgHom.id K R)
          (Algebra.TensorProduct.map (IntermediateField.inclusion hab) (AlgHom.id K R) e) =
        Algebra.TensorProduct.map (IntermediateField.inclusion (hab.trans hb)) (AlgHom.id K R) e := by
      intro a b hab hb e
      induction e using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    refine ⟨k₁ ⊔ k₂, sup_le h₁ h₂,
      (Algebra.TensorProduct.map (IntermediateField.inclusion (le_sup_left : k₁ ≤ k₁ ⊔ k₂))
        (AlgHom.id K R) : k₁ ⊗[K] R →ₐ[K] _) e₁ +
      (Algebra.TensorProduct.map (IntermediateField.inclusion (le_sup_right : k₂ ≤ k₁ ⊔ k₂))
        (AlgHom.id K R) : k₂ ⊗[K] R →ₐ[K] _) e₂,
      inferInstance, ?_⟩
    rw [map_add (f := _), key, key]

theorem exists_geomInt_component : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  intro K _ _ _ R _ _ _ p
  let Ω : IntermediateField K ℂ := algebraicClosure K ℂ
  haveI : IsAlgClosed Ω := (algebraicClosure.isAlgClosure K ℂ).isAlgClosed
  haveI : Algebra.IsAlgebraic K Ω := algebraicClosure.isAlgebraic K ℂ
  haveI hreg : IsRegularRing (Ω ⊗[K] R) := GlobalTheory.isRegularRing_of_smooth Ω _
  have : IsNoetherianRing (Ω ⊗[K] R) := hreg.toIsNoetherian
  let π : Ω ⊗[K] R →ₐ[K] ℂ := Algebra.TensorProduct.lift Ω.val p (fun _ _ => Commute.all _ _)
  haveI : (RingHom.ker π).IsPrime := RingHom.ker_isPrime _
  obtain ⟨e', he', hP, hpr⟩ := exists_idempotent (A := Ω ⊗[K] R)
    (fun q _ =>
      haveI := IsRegularRing.isRegularLocalRing_localization q
      GlobalTheory.isDomain_of_isRegularLocalRing _) (RingHom.ker π)
  obtain ⟨k, hk, e, hfin, rfl⟩ := exists_finite_level K ℂ R Ω e'
  let inc := Algebra.TensorProduct.map (IntermediateField.inclusion hk) (AlgHom.id K R)
  have hinc : Function.Injective inc :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R)
      (IntermediateField.inclusion hk).toLinearMap (IntermediateField.inclusion_injective hk)
  have he : IsIdempotentElem e := hinc (by rw [map_mul]; exact he')
  have hπ : ∀ x, π (inc x) = Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨k, e, hfin, he, ?_, ?_⟩
  · rw [← hπ]
    exact (IsIdempotentElem.iff_eq_zero_or_one.1 (he'.map π)).resolve_left hP
  · letI : Algebra k Ω := (IntermediateField.inclusion hk).toRingHom.toAlgebra
    haveI : IsScalarTower K k Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.tower_top (K := K) k
    exact geomInt_away_baseChange K k Ω R e he (fun h => hP (by
      rw [RingHom.mem_ker]
      exact (congrArg π h).trans (map_zero π))) hpr

end GlobalTheory.GeomComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsL2ValFieldOrDvrSplitKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilLocal

open GlobalTheory.RelBasis GlobalTheory.SimilDet

theorem det_ne_zero : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (ξ : (Fin 4 → Fin N) → Fin 4 → Pt x) (w : ∀ I, LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (Q : Matrix (Fin 4 → Fin N) (Fin 4 → Fin N) K), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → Function.Injective ξ → (∀ I, (w I).IsGen) → (∀ I, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ I r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ I r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ I r)).left))) = (val (w I) ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → Q.det ≠ 0 := by
  intro laws K _ _ x m N al b ξ w Q hm hal hξ hw hE
  classical
  have hL := x.P.isLB
  intro h0
  obtain ⟨c, hc, hcQ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  obtain ⟨I₀, -⟩ := Function.ne_iff.1 hc
  refine hc ?_
  let S : Over (Sp K) := 𝟙_ _
  let T := Out.powObj x.P.A 4
  haveI : IsIntegral S.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of K)))
  haveI : Subsingleton S.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : S.left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : S.left ⟶ x.P.A.left => exists_chart hL (χ p)
  replace hJ : Good x.P.L p J := hJ
  let ev : Γ(S.left, ⊤) →+* S.left.presheaf.stalk p := (S.left.presheaf.germ ⊤ p trivial).hom
  have hev : ∀ (y : S ⟶ T) a, gs (y.left ≫ T.hom) p ⊤ a = ev a := fun y a => by
    rw [Over.w y]
    exact gs_eq (𝟙 S.left) p ⊤ trivial a
  let κ : K →+* S.left.presheaf.stalk p := ev.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  choose a ha using fun I v => exists_transl_ratio laws x m al (ξ I₀) (ξ I) (w I₀) (w I) (hw I₀) (hw I) v
  let u : (Fin 4 → Fin N) → (S ⟶ T) → (S.left.presheaf.stalk p)ˣ := fun I y =>
    val (w I₀) y.left p J * (val (w I) y.left p J)⁻¹
  have hu : ∀ I (v : ker x al) (y : S ⟶ T), (u I (v.1 * y)).val = ev (a I v) * (u I y).val := fun I v y => by
    have := ha I v _ y.left p J hJ
    rw [hev, ← Over.comp_left, pt_tr] at this
    rw [← this, ← Units.val_mul, inv_mul_cancel_right]
  let χ : (Fin 4 → Fin N) → ker x al →* S.left.presheaf.stalk p := fun I =>
    { toFun := fun v => ev (a I v)
      map_one' := by
        have := hu I 1 1
        rw [Submonoid.coe_one, _root_.one_mul] at this
        exact (Units.mul_left_inj (u I 1)).1 (this.symm.trans (_root_.one_mul _).symm)
      map_mul' := fun v v' => by
        have := hu I (v * v') 1
        rw [Submonoid.coe_mul, _root_.mul_assoc, hu, hu, ← _root_.mul_assoc] at this
        exact ((Units.mul_left_inj (u I 1)).1 this).symm }
  have hχ : Function.Injective χ := fun I I' h => by
    have e := GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant laws K x m al (ξ I) (ξ I') (w I) (w I') hm hal (hw I) (hw I') (fun v hv Z r z J hJ => by
      have e₁ : a I ⟨v, hv⟩ = a I' ⟨v, hv⟩ := fn_ext (X := S.left) fun y _ => by
        obtain rfl : y = p := Subsingleton.elim _ _
        exact (gs_eq (𝟙 S.left) p ⊤ trivial _).trans ((DFunLike.congr_fun h ⟨v, hv⟩).trans
          (gs_eq (𝟙 S.left) p ⊤ trivial _).symm)
      have e₂ := Units.ext ((ha I ⟨v, hv⟩ Z r z J hJ).trans (e₁ ▸ (ha I' ⟨v, hv⟩ Z r z J hJ).symm))
      have alg : ∀ {U : Type} [CommGroup U] (A B B' C D D' : U),
          A * B⁻¹ * (C * D⁻¹)⁻¹ = A * B'⁻¹ * (C * D'⁻¹)⁻¹ → B * D' = B' * D := fun A B B' C D D' h => by
        rw [mul_inv, mul_inv, inv_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj, mul_left_comm,
          mul_left_comm B'⁻¹, mul_right_inj, inv_mul_eq_iff_eq_mul] at h
        rw [h, mul_left_comm B', mul_inv_cancel_left]
      exact alg _ _ _ _ _ _ e₂)
    exact hξ e
  let θ : (Fin 4 → Fin N) → (S ⟶ T) → S.left.presheaf.stalk p := fun I y =>
    ∏ r, gs (y.left ≫ (alMap x al r (ξ I r)).left) p _ (x.th.f (J (y.left ≫ (alMap x al r (ξ I r)).left)))
  refine eq_zero_of_eigen κ χ hχ (fun v y => v.1 * y) (fun I y => θ I y * (u I y).val) (fun I v y => ?_)
    (fun I => ?_) c (fun y => ?_)
  · have e : θ I (v.1 * y) = θ I y := Finset.prod_congr rfl fun r _ =>
      congrArg (fun ψ : S.left ⟶ x.P.A.left => gs ψ p _ (x.th.f (J ψ))) (by
        rw [← Over.comp_left, ← Over.comp_left, ← pt_tr, Category.assoc, tr_alMap])
    simp only [hu, e]
    exact mul_left_comm _ _ _
  · obtain ⟨y, hy⟩ := GlobalTheory.SimilNonvan.exists_pt_isUnit laws K x m al (ξ I) hm hal
    exact ⟨y, mul_ne_zero (Finset.prod_ne_zero_iff.2 fun r _ => (hy p J hJ r).ne_zero) (Units.ne_zero _)⟩
  · have e : ∀ I, θ I y * (u I y).val = (val (w I₀) y.left p J).val * ∑ I', κ (Q I I') *
        ∏ c, gs (y.left ≫ (Out.powPr x.P.A c).left) p _ ((b (I' c)).f (J (y.left ≫ (Out.powPr x.P.A c).left))) :=
      fun I => by
      have e₁ : θ I y = _ := hE I _ y.left p J hJ
      rw [e₁, mul_right_comm, ← Units.val_mul, mul_comm (val (w I) y.left p J),
        inv_mul_cancel_right]
      refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
      rw [gs_cst, hev]
      rfl
    simp only [e, mul_left_comm _ (val (w I₀) y.left p J).val, ← Finset.mul_sum]
    refine mul_eq_zero_of_right _ ?_
    simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun I' _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum, show ∑ I, c I * Q I I' = 0 from congrFun hcQ I', map_zero, zero_mul]

theorem exists_coords_pow (laws : Out.Laws) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R)
    (m : ℕ) (hm : 1 ≤ m) (b : Fin (m ^ x.P.g) → RR x m) (hb : IsBasis x b) (n : ℕ)
    (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))) :
    ∃ q : (Fin n → Fin (m ^ x.P.g)) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J,
      Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) *
        ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
          ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  refine GlobalTheory.T.boxProducts_span_external_powers_of_boxSpan R x.P.A x.P.L m _ b x.P.isLB (fun T => ?_) n s
  refine GlobalTheory.T.pullbackSectionsSpanTwisted_of_indep_span _ _ _ _ _ _ b _ _ x.P.isLB (GlobalTheory.T.pullbackSections_basis_of_affine_opens _ _ _ _ _ _ b _ _ ?_)
  refine _root_.GlobalTheory.RelBasis.indepOn_spanOn_of_affine R _ x.P.A.hom x.P.L _ _ b (fun R' _ f => ?_) _ _ T.hom _ _
    (IsPullback.of_hasPullback x.P.A.hom T.hom)
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange laws.polBaseChange R R' x f
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyVia.main R R' x x' f
  obtain ⟨φ, w, hv⟩ := h₁.1 hx'
  choose b' hb' using fun k => ((h₂ φ w hv).1 m (b k)).exists
  have hP : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := by
    obtain ⟨he, hg, F, ⟨hP, -⟩, -⟩ := hv
    exact hP
  exact ⟨_, x'.P.A.hom, φ, hP, _root_.GlobalTheory.RelBasisFibre.main R R' x x' f φ w m _ b b' hv hb'
    ((GlobalTheory.KeyBasis.main laws R x m hm).2 b hb R' f x' φ w b' hv hb')⟩

theorem exists_l2Val : Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m) (ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x), IsUnit (m : R) → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) → (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  intro laws R _ _ _ _ x m al b ξ hm hal hb hξ hk
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hm)
  obtain ⟨mu, hmu, hmu'⟩ := GlobalTheory.KeyKa.exists_normalised_mulPull laws R x m
  choose w hw using fun I => GlobalTheory.SimilPull.exists_gen_similitude_pull laws R x m al (ξ I) hal (hk I)
  choose rho hrho using fun I => GlobalTheory.SimilUnit.exists_normalising_unit R x m al (ξ I) mu (w I) hm0 hal (hk I) hmu (hw I)
  choose s hs using fun I => GlobalTheory.KeyQuot.exists_sec_quot _ _ x.P.L x.P.isLB _ _ _ _ (m : ℤ) x.th (w I) (hw I)
  choose Q hQ using fun I => exists_coords_pow laws R x m (Nat.one_le_iff_ne_zero.2 hm0) b hb 4 (s I)
  have hZ : ∀ I, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ I r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ I r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ I r)).left))) = (val (w I) ρ z J).val * ∑ I' : Fin 4 → Fin (m ^ x.P.g), gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left))) := by
    intro I Z ρ z J hJ
    rw [← hQ I Z ρ z J hJ]
    exact hs I Z ρ z J hJ
  have hE : ∀ I, ∀ (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J → ∏ r, gs (alMap x al r (ξ I r)).left y _ (x.th.f (J (alMap x al r (ξ I r)).left)) = (val (w I) (𝟙 _) y J).val * ∑ I' : Fin 4 → Fin (m ^ x.P.g), gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left)) ((b (I' c)).f (J (Out.powPr x.P.A c).left)) := by
    intro I y J hJ
    have e₁ := hZ I _ (𝟙 _) y J hJ
    have c₁ : ∀ ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left,
        gs (𝟙 _ ≫ ψ) y (x.P.L.U (J (𝟙 _ ≫ ψ))) (x.th.f (J (𝟙 _ ≫ ψ))) = gs ψ y (x.P.L.U (J ψ)) (x.th.f (J ψ)) :=
      fun ψ => by rw [Category.id_comp]
    have c₂ : ∀ (ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left) k,
        gs (𝟙 _ ≫ ψ) y (x.P.L.U (J (𝟙 _ ≫ ψ))) ((b k).f (J (𝟙 _ ≫ ψ))) = gs ψ y (x.P.L.U (J ψ)) ((b k).f (J ψ)) :=
      fun ψ k => by rw [Category.id_comp]
    simpa only [c₁, c₂] using e₁
  have hdet : IsUnit (Matrix.det (Matrix.of Q)) := by
    let k := AlgebraicClosure (IsLocalRing.ResidueField R)
    let f : R →+* k := (algebraMap (IsLocalRing.ResidueField R) k).comp (IsLocalRing.residue R)
    obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange laws.polBaseChange R k x f
    obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyVia.main R k x x' f
    obtain ⟨φ, u, hv⟩ := h₁.1 hx'
    choose b' hb' using fun j => ((h₂ φ u hv).1 m (b j)).exists
    choose ξ' hξ' using fun I r => ((h₂ φ u hv).2.1 (ξ I r)).exists
    choose w' hw' hE' using fun I =>
      GlobalTheory.T.similitudeIso_thetaProduct_baseChange R k x x' f φ u m _ al b b' (ξ I) (ξ' I) (w I) (Q I) hv hb' (hξ' I) (hw I) (hZ I)
    have hinj : Function.Injective ξ' := fun I I' e => by
      by_contra hne
      obtain ⟨r, hr⟩ := hξ I I' hne (spMap f (IsLocalRing.closedPoint k))
      have e' : spMap f ≫ (ξ I r).left = spMap f ≫ (ξ I' r).left := by rw [← hξ' I r, ← hξ' I' r, e]
      exact hr (congrArg (fun q => q (IsLocalRing.closedPoint k)) e')
    have hne := det_ne_zero laws k x' m _ al b' ξ' w' ((Matrix.of Q).map f)
      (by simpa only [map_natCast] using (hm.map f).ne_zero) hal hinj hw' hE'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hne
    by_contra hu
    refine hne ?_
    have : IsLocalRing.residue R (Matrix.det (Matrix.of Q)) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu
    show algebraMap (IsLocalRing.ResidueField R) k (IsLocalRing.residue R _) = 0
    rw [this, map_zero]
  refine ⟨hdet.unit ^ (2 * m ^ 2) * ∏ I, rho I ^ 2, ξ, mu, w, Matrix.of Q, rho, hξ, hk, hmu, hw,
    fun p J hJ => ⟨hmu' p J hJ, fun I => hrho I p J hJ⟩, hE, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_prod]

end GlobalTheory.SimilLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNhdsSubsetImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelOpen

theorem image_mem_nhds_of_injOn {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {a : Fin n → ℂ}
    (ha : a ∈ U) : f '' U ∈ nhds (f a) := by
  have han : AnalyticAt ℂ f a := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn n U f hU hf hinj a ha
  have hm : Filter.map f (nhds a) = nhds (f a) :=
    han.hasStrictFDerivAt.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hb.2)
  rw [← hm]
  exact Filter.image_mem_map (hU.mem_nhds ha)

theorem eq_of_out {J R : Type} {s t : Matrix J J R} (hs : s.IsSymm) (ht : t.IsSymm)
    (h : ∀ z : Sym2 J, s z.out.1 z.out.2 = t z.out.1 z.out.2) : s = t := by
  ext i j
  have h1 := h s(i, j)
  have h2 : s((s(i, j) : Sym2 J).out.1, (s(i, j) : Sym2 J).out.2) = s(i, j) :=
    Quot.out_eq (s(i, j) : Sym2 J)
  rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rwa [h3, h4] at h1
  · rw [h3, h4] at h1
    rw [← hs.apply i j, ← ht.apply i j]
    exact h1

theorem exists_nhds_subset_image :
    ∀ (h : ℕ) (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ) (b₀ : Fin (h * (h + 1) / 2) → ℂ), IsOpen B → b₀ ∈ B → (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → Set.InjOn τ B → ∃ N ∈ nhds (τ b₀), ∀ t ∈ N, t.IsSymm → (t.map Complex.im).PosDef → ∃ b ∈ B, τ b = t := by
  intro h B τ b₀ hB hb₀ hd hs hinj
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (GlobalTheory.card_sym2_fin h)
  let p : Matrix (Fin h) (Fin h) ℂ → (Fin (h * (h + 1) / 2) → ℂ) :=
    fun t k => t (e.symm k).out.1 (e.symm k).out.2
  have hpc : Continuous p := continuous_pi fun k => continuous_id.matrix_elem _ _
  have hp : ∀ s t : Matrix (Fin h) (Fin h) ℂ, s.IsSymm → t.IsSymm → p s = p t → s = t := by
    intro s t hs' ht' hst
    refine eq_of_out hs' ht' fun z => ?_
    have := congrFun hst (e z)
    simpa only [p, Equiv.symm_apply_apply] using this
  have key := image_mem_nhds_of_injOn (f := fun b => p (τ b)) hB
    (differentiableOn_pi.mpr fun k => hd _ _)
    (fun x hx y hy hxy => hinj hx hy (hp _ _ (hs x hx).1 (hs y hy).1 hxy)) hb₀
  refine ⟨_, hpc.continuousAt.preimage_mem_nhds key, ?_⟩
  rintro t ⟨b, hb, hbt⟩ ht -
  exact ⟨b, hb, hp _ _ (hs b hb).1 ht hbt⟩

end GlobalTheory.SiegelOpen
end

