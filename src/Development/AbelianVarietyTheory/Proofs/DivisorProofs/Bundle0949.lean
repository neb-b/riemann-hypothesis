module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowSpec

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

def lastSubst {A : Type} [CommRing A] {N : ℕ} (D : ℕ) (t : Fin N → A) :
    Fin (D + 1) × Fin N → MvPolynomial (Fin D × Fin N) A :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin D × Fin N) A)
    (C (t v.2)) (fun i => X (i, v.2)) v.1

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_last {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (j : Fin N) : _root_.GlobalTheory.ChowSpec.lastSubst D t (Fin.last D, j) = C (t j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_castSucc {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (i : Fin D) (j : Fin N) :
    _root_.GlobalTheory.ChowSpec.lastSubst D t (i.castSucc, j) = X (i, j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

def lastEquiv (K : Type) [CommRing K] (N D : ℕ) :
    MvPolynomial (Fin (D + 1) × Fin N) K ≃+* MvPolynomial (Fin D × Fin N) (MvPolynomial (Fin N) K) :=
  RingEquiv.ofRingHom
    (aeval (R := K) (lastSubst D (X : Fin N → MvPolynomial (Fin N) K))).toRingHom
    (eval₂Hom (aeval (R := K) (fun j => X (Fin.last D, j))).toRingHom
      (fun v => X (v.1.castSucc, v.2)))
    (by
      refine MvPolynomial.ringHom_ext' (MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_))
        (fun v => ?_) <;> simp)
    (by
      refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
      rintro ⟨i, j⟩
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp)

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
private theorem isWeightedHomogeneous_aeval_of_forall {R S σ τ Γ Δ : Type} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid Γ] [AddCommMonoid Δ] {w : σ → Γ}
    {w' : τ → Δ} (g : Γ →+ Δ) {p : MvPolynomial σ R} {m : Γ}
    (hp : IsWeightedHomogeneous w p m) (φ : σ → MvPolynomial τ S)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ v) (g (w v))) :
    IsWeightedHomogeneous w' (aeval φ p) (g m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [mem_weightedHomogeneousSubmodule, aeval_monomial, Finsupp.prod]
  have hw : Finsupp.weight w s = m := hp (mem_support_iff.mp hs)
  have hm : g m = 0 + ∑ v ∈ s.support, s v • g (w v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp [map_nsmul]
  rw [hm, MvPolynomial.algebraMap_apply]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _)


set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
theorem _root_.GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → _root_.GlobalTheory.ChowHt.IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, _root_.GlobalTheory.ChowHt.IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  intro K L _ _ N _ _ _ _ P D δ f hP hf
  set t : Fin N → L := fun j => algebraMap (MvPolynomial (Fin N) K) L (X j) with ht
  set φ := _root_.GlobalTheory.ChowSpec.lastSubst (D + 1) t with hφ
  set f' : MvPolynomial (Fin (D + 1) × Fin N) L := aeval (R := K) φ f with hf'
  have hfhom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f (fun _ => δ) :=
    _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.1 hf.homog
  have hf'hom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f' (fun _ => δ) := by
    unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hfhom ⊢
    let g : (Fin (D + 1 + 1) → ℕ) →+ (Fin (D + 1) → ℕ) :=
      { toFun := fun a i => a i.castSucc, map_zero' := rfl, map_add' := fun _ _ => rfl }
    refine isWeightedHomogeneous_aeval_of_forall (S := L) g hfhom φ ?_
    rintro ⟨i, j⟩
    induction i using Fin.lastCases with
    | last =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (Fin.last (D + 1), j)) = 0 := by
        funext i
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Fin.castSucc_ne_last]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_last, hg]
      exact isWeightedHomogeneous_C _ _
    | cast i =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (i.castSucc, j)) = _root_.GlobalTheory.Chow.blockWeight (i, j) := by
        funext i'
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Pi.single_apply]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_castSucc, hg]
      exact isWeightedHomogeneous_X _ _ _
  refine ⟨f', _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.2 hf'hom, ?_, ?_⟩
  · have hkey : MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f) = f' := by
      rw [hf']
      change ((MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).comp
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1)).toRingHom) f = (aeval φ).toRingHom f
      congr 1
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp [_root_.GlobalTheory.ChowSpec.lastEquiv, MvPolynomial.algebraMap_apply,
          IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · rcases v with ⟨i, j⟩
        induction i using Fin.lastCases <;> simp [_root_.GlobalTheory.ChowSpec.lastEquiv, hφ, ht]
    set F := _root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f with hF
    have hFirr : Irreducible F :=
      (MulEquiv.irreducible_iff (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1))).2
        hf.irred
    have hF0 : F ≠ 0 := hFirr.ne_zero
    have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.1 hFirr
    have hδ : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · exfalso
        subst h
        have hh := hfhom.isHomogeneous
        simp only [Finset.sum_const_zero] at hh
        have hf0 := hf.ne_zero
        have hC : f = C (AddMonoidAlgebra.coeff f 0) :=
          (totalDegree_eq_zero_iff_eq_C).1 (by simpa using hh.totalDegree hf0)
        have hc : AddMonoidAlgebra.coeff f 0 ≠ 0 := fun h0 => hf0 (by rw [hC, h0, C_0])
        apply hf.irred.not_isUnit
        rw [hC]
        exact hc.isUnit.map C
      · exact h
    have hf'0 : f' ≠ 0 := by
      rw [← hkey]
      exact fun h => hF0 ((map_eq_zero_iff _
        (MvPolynomial.map_injective _ (IsFractionRing.injective (MvPolynomial (Fin N) K) L))).1 h)
    have hnotunit : ¬ IsUnit f' := by
      intro hu
      obtain ⟨r, hr, hfr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hu
      have hh := hf'hom.isHomogeneous
      rw [hfr] at hh
      have h0 := hh (show AddMonoidAlgebra.coeff (C r) 0 ≠ 0 by simpa using hr.ne_zero)
      simp at h0
      omega
    have hdisj : Disjoint ((Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K))) :
            Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K)))
        (↑(Ideal.span {F}) : Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmem
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 hmem
      apply hnotunit
      have hs0 : algebraMap (MvPolynomial (Fin N) K) L s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      have hmapped := congrArg (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)) hg
      rw [map_mul, hkey, map_C] at hmapped
      exact isUnit_of_mul_isUnit_right (hmapped ▸ hs0.isUnit.map C)
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K)))
      (MvPolynomial (Fin (D + 1) × Fin N) L) (Ideal.span {F})
      ((Ideal.span_singleton_prime hF0).2 hFprime) hdisj
    rw [Ideal.map_span, Set.image_singleton] at hprime
    have hF' : algebraMap (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
        (MvPolynomial (Fin (D + 1) × Fin N) L) F = f' := hkey
    rw [hF'] at hprime
    exact ((Ideal.span_singleton_prime hf'0).1 hprime).irreducible
  · intro u
    set ũ : Fin (D + 1 + 1) × Fin N → AlgebraicClosure L := fun v =>
      Fin.lastCases (motive := fun _ => AlgebraicClosure L) (algebraMap L (AlgebraicClosure L) (t v.2))
        (fun i => u (i, v.2)) v.1 with hũ
    have hev : aeval u f' = aeval ũ f := by
      rw [hf']
      change ((aeval u).restrictScalars K) (aeval φ f) = aeval ũ f
      rw [← AlgHom.comp_apply, comp_aeval]
      refine congrArg (fun x => (aeval x) f) (funext fun v => ?_)
      rcases v with ⟨i, j⟩
      induction i using Fin.lastCases <;> simp [hφ, hũ]
    have hPhom : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
      intro i r hr
      convert hP r hr i using 1
      conv_lhs => rw [← sum_homogeneousComponent r]
      rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
        Finset.sum_eq_single i]
      · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem i r)
      · intro b _ hb
        exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem b r) hb
      · intro hi
        have h0 : homogeneousComponent i r = 0 :=
          homogeneousComponent_eq_zero i r (by simp at hi; omega)
        rw [h0, DirectSum.decompose_zero]
        rfl
    have hideal : ∀ y : Fin N → AlgebraicClosure L,
        (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
          Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)}, aeval y g = 0) ↔
        (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, ũ (Fin.last (D + 1), j) * y j = 0 := by
      intro y
      have hmap : ∀ g : MvPolynomial (Fin N) K,
          aeval y (MvPolynomial.map (algebraMap K L) g) = aeval y g := fun g => aeval_map_algebraMap L y g
      have hlin : aeval y (∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L) =
          ∑ j, ũ (Fin.last (D + 1), j) * y j := by
        simp [hũ]
      constructor
      · intro H
        refine ⟨fun g hg => ?_, ?_⟩
        · rw [← hmap]
          exact H _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
        · rw [← hlin]
          exact H _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      · rintro ⟨H1, H2⟩ g hg
        have hle : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
            Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)} ≤
            RingHom.ker (aeval y : MvPolynomial (Fin N) L →ₐ[L] AlgebraicClosure L) := by
          refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
          · simpa [RingHom.mem_ker, hmap] using H1 g hg
          · simpa [RingHom.mem_ker, hlin] using H2
        exact RingHom.mem_ker.1 (hle hg)
    rw [hev, hf.zero_iff_of_isAlgClosed hPhom ũ]
    constructor
    · rintro ⟨y, hy0, hyP, hyu⟩
      rw [Fin.forall_fin_succ'] at hyu
      exact ⟨y, hy0, (hideal y).2 ⟨hyP, hyu.2⟩, fun i => by simpa [hũ] using hyu.1 i⟩
    · rintro ⟨y, hy0, hyI, hyu⟩
      obtain ⟨hyP, hyh⟩ := (hideal y).1 hyI
      exact ⟨y, hy0, hyP, Fin.forall_fin_succ'.2 ⟨fun i => by simpa [hũ] using hyu i, hyh⟩⟩

end GlobalTheory.ChowSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulUnitAtCodimOneOfFactorialBase
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem UnitAt.zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {s : X.functionField} (hs : UnitAt x s) (n : ℤ) :
    UnitAt x (s ^ n) := by
  obtain ⟨u, rfl⟩ := hs
  refine ⟨u ^ n, ?_⟩
  have := congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map] at this
  exact this

theorem UnitAt.prod {X : Scheme.{0}} [IsIntegral X] {x : X} {ι : Type} (s : Finset ι) (f : ι → X.functionField)
    (h : ∀ b ∈ s, UnitAt x (f b)) : UnitAt x (∏ b ∈ s, f b) :=
  Finset.prod_induction f (UnitAt x) (fun _ _ => UnitAt.mul) ⟨1, by simp⟩ h

theorem eq_of_specializes_of_coheight {X : Scheme.{0}} {x y : X} (h : y ⤳ x) (hx : Order.coheight x = 1)
    (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm (show x ⤳ y from h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [hx, hy] at this
  exact absurd this (by decide)

theorem unitAt_constFn {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Sp R) (x : X) (b : R)
    (hb : b ∉ (q x).asIdeal) : IsUnit (X.presheaf.germ ⊤ x trivial (constFn q ⊤ b)) := by
  rw [← Scheme.mem_basicOpen_top, constFn_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hb

theorem exists_const_mul_unitAt_coheight_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  intro R K _ _ _ _ _ _ _ X _ _ q _ _ κ hκ I U t hcov ht0 htr hgen
  classical
  have hgz : GeneralizingMap q := Flat.generalizingMap q
  have hinj := IsFractionRing.injective R K
  have hunit : ∀ (x : X) (b : R), b ∉ (q x).asIdeal → UnitAt x (κ (algebraMap R K b)) := fun x b hb =>
    ⟨(unitAt_constFn q x b hb).unit, by
      rw [IsUnit.unit_spec, hκ]
      exact X.presheaf.germ_stalkSpecializes_apply _ _ _⟩
  let S : Set X := {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
  have hS : IsOpen S := by
    change IsOpen {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => (U i).isOpen.inter (isOpen_unitAt _)
  have hg : genericPoint X ∈ S := by
    let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, -, hy⟩ := hgz ((PrimeSpectrum.le_iff_specializes p₀ (q (genericPoint X))).1 bot_le)
    exact (genericPoint_specializes y).mem_open hS (hgen y (by rw [hy]))
  have hB := GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint X S hS hg
  set B : Set X := {x : X | Order.coheight x = 1 ∧ x ∉ S} with hBdef
  have key : ∀ b ∈ B, ∃ π : R, Prime π ∧ (q b).asIdeal = Ideal.span {π} ∧
      (∀ x : X, (q x).asIdeal = Ideal.span {π} → b ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk b) ∧
      Irreducible (X.presheaf.germ ⊤ b trivial (constFn q ⊤ π)) := by
    rintro b ⟨h1, hbS⟩
    have hb0 : (q b).asIdeal ≠ ⊥ := fun h => hbS (hgen b h)
    obtain ⟨π, hπ, hqb⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz b h1.le hb0
    obtain ⟨ξ, -, hξ, hd, hirr⟩ := _root_.GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime R X q π hπ
    have hξ1 : Order.coheight ξ = 1 := by
      have e := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk ξ)
      rw [ringKrullDim_stalk_eq_coheight] at e
      exact_mod_cast e
    obtain rfl : b = ξ := eq_of_specializes_of_coheight (hξ b hqb) h1 hξ1
    exact ⟨π, hπ, hqb, hξ, hd, hirr⟩
  choose! π hπ hqπ hsp hdvr hirr using key
  have hstar : ∀ b ∈ B, ∀ x : X, Order.coheight x = 1 → π b ∈ (q x).asIdeal → x = b := by
    intro b hb x hx hmem
    have hx0 : (q x).asIdeal ≠ ⊥ := fun h => (hπ b hb).ne_zero (by rw [h, Ideal.mem_bot] at hmem; exact hmem)
    obtain ⟨π', hπ', hqx⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz x hx.le hx0
    have hdvd : π' ∣ π b := Ideal.mem_span_singleton.1 (hqx ▸ hmem)
    have hq : (q x).asIdeal = Ideal.span {π b} :=
      hqx.trans (Ideal.span_singleton_eq_span_singleton.2 (hπ'.associated_of_dvd (hπ b hb) hdvd))
    exact eq_of_specializes_of_coheight (hsp b hb x hq) hx hb.1
  have hne : ∀ b ∈ B, algebraMap R K (π b) ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).2 (hπ b hb).ne_zero
  have key2 : ∀ b ∈ B, ∃ (i : I) (n : ℤ), b ∈ U i ∧ UnitAt b (κ (algebraMap R K (π b)) ^ (-n) * t i) := by
    intro b hb
    obtain ⟨i, hi⟩ := hcov b
    have := hdvr b hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (hirr b hb) (ht0 i b hi)
    have e : algebraMap _ X.functionField (X.presheaf.germ ⊤ b trivial (constFn q ⊤ (π b))) =
        κ (algebraMap R K (π b)) := by
      rw [hκ]; exact X.presheaf.germ_stalkSpecializes_apply _ _ _
    have hπ' : κ (algebraMap R K (π b)) ≠ 0 := (map_ne_zero κ).2 (hne b hb)
    refine ⟨i, n, hi, u, ?_⟩
    rw [hu, e, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hπ', neg_add_cancel, zpow_zero,
      _root_.mul_one]
  have : Nonempty I := ⟨(hcov (genericPoint X)).choose⟩
  choose! ib n hUi hunitb using key2
  let F := hB.toFinset
  let a : Kˣ := ∏ b ∈ F.attach, (Units.mk0 _ (hne b.1 (hB.mem_toFinset.1 b.2))) ^ (-n b.1)
  have hκa : κ (a : K) = ∏ b ∈ F, κ (algebraMap R K (π b)) ^ (-n b) := by
    simp only [a, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
    exact Finset.prod_attach F (fun b => κ (algebraMap R K (π b)) ^ (-n b))
  refine ⟨a, fun i x hx h1 => ?_⟩
  rw [hκa]
  have hother : ∀ b ∈ F, b ≠ x → UnitAt x (κ (algebraMap R K (π b)) ^ (-n b)) := fun b hb hbx =>
    (hunit x (π b) fun hm => hbx (hstar b (hB.mem_toFinset.1 hb) x h1 hm).symm).zpow _
  by_cases hxS : x ∈ S
  · obtain ⟨j, hj, hu⟩ := hxS
    refine htr i j x _ hx hj ((UnitAt.prod F _ fun b hb => hother b hb ?_).mul hu)
    rintro rfl
    exact (hB.mem_toFinset.1 hb).2 ⟨j, hj, hu⟩
  · have hxB : x ∈ B := ⟨h1, hxS⟩
    have hxF : x ∈ F := hB.mem_toFinset.2 hxB
    rw [← Finset.mul_prod_erase F (fun b => κ (algebraMap R K (π b)) ^ (-n b)) hxF]
    refine htr i (ib x) x _ hx (hUi x hxB) ?_
    rw [mul_comm (κ (algebraMap R K (π x)) ^ (-n x)), mul_assoc]
    exact (UnitAt.prod _ _ fun b hb => hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).mul
      (hunitb x hxB)

end GlobalTheory.VerticalUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.ColAction

theorem sympl_eq_neg_dotProduct {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]
  ring

theorem mem_symplecticGroup_of_sympl {l : Type} [Fintype l] [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (M *ᵥ u) (M *ᵥ v) = sympl u v) : M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext a b
  have key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]
  have := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem signed_sum_eq_trace {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) = Matrix.trace (Jm P Q * X * Jm R S * Yᴴ) := by
  have e : Jm P Q * X * Jm R S =
      Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b := by
    ext a b
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Fintype.sum_sum_type, lineSign]

theorem signed_sum_mul_transpose {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) (k : Mat R S)
    (hk : kᴴ * Jm R S * k = Jm R S) :
    ∑ a, ∑ b, lineSign a b * (X * kᵀ) a b * star ((Y * kᵀ) a b) = ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) := by
  have hJ : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal]
  have e : (kᵀ)ᴴ = k.map star := by ext i j; simp
  have hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S := by
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose] at this
    rw [e, Matrix.mul_assoc, this]
  rw [signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Jm P Q * (X * kᵀ) * Jm R S * ((kᵀ)ᴴ * Yᴴ) = Jm P Q * X * (kᵀ * Jm R S * (kᵀ)ᴴ) * Yᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hk']

theorem exists_symplectic_hom_of_unitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    mem_symplecticGroup_of_sympl _ (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColAction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentCutoffTendstoAdelicUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧ Tendsto q atTop (𝓝 g) := by
  first | exact @GlobalTheory.UnitaryCutoff.exists_approx | exact GlobalTheory.UnitaryCutoff.exists_approx | (intros; apply GlobalTheory.UnitaryCutoff.exists_approx <;> assumption)
end

