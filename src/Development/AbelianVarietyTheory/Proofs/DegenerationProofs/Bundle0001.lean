module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
section
open KaehlerDifferential TensorProduct

namespace GlobalTheory.EtaleCoordJacobian

section tower
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis (i : I) :
    mapBaseChange R (MvPolynomial I R) B (((mvPolynomialBasis R I).baseChange B) i) =
      D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i)) := by
  rw [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, one_smul,
    map_D]

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale [Finite I] [Algebra.Etale (MvPolynomial I R) B] :
    (∃ b : Module.Basis I B Ω[B⁄R],
      ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) ∧
      Algebra.Smooth R B := by
  haveI : Algebra.Smooth R (MvPolynomial I R) := Algebra.Smooth.mk
  refine ⟨⟨((mvPolynomialBasis R I).baseChange B).map
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial I R) B), fun i => ?_⟩,
    Algebra.Smooth.comp R (MvPolynomial I R) B⟩
  rw [Module.Basis.map_apply, ← _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis]
  rfl

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis [Finite I] [Algebra.Smooth R B]
    (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial I R) B := by
  set bc := (mvPolynomialBasis R I).baseChange B
  have hmap : mapBaseChange R (MvPolynomial I R) B = (bc.equiv b (Equiv.refl I)).toLinearMap :=
    bc.ext fun i => by
      rw [_root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
        Equiv.refl_apply, hb]
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).injective
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).surjective
  have hΩ : Subsingleton Ω[B⁄MvPolynomial I R] := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Ω[B⁄MvPolynomial I R], z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial I R) B z
      obtain ⟨v, rfl⟩ := hsurj w
      exact (exact_mapBaseChange_map R (MvPolynomial I R) B).apply_apply_eq_zero v
    rw [hx x, hx y]
  have hH : Subsingleton (Algebra.H1Cotangent (MvPolynomial I R) B) := by
    haveI : Subsingleton (Algebra.H1Cotangent R B) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Algebra.H1Cotangent (MvPolynomial I R) B, z = 0 := fun z => by
      have h1 : Algebra.H1Cotangent.δ R (MvPolynomial I R) B z = 0 :=
        hinj (((Algebra.H1Cotangent.exact_δ_mapBaseChange R _ B).apply_apply_eq_zero z).trans
          (map_zero _).symm)
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial I R) B z).mp h1
      rw [Subsingleton.elim w 0, map_zero]
    rw [hx x, hx y]
  haveI : Algebra.FormallyEtale (MvPolynomial I R) B := Algebra.FormallyEtale.mk hΩ hH
  haveI : Algebra.FinitePresentation (MvPolynomial I R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ B
  exact Algebra.Etale.mk

end tower

open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_and_smooth_of_etale_eval2Hom (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] (t : I → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale) :
    (∃ b : Module.Basis I B Ω[B⁄R], ∀ i, b i = D R B (t i)) ∧ Algebra.Smooth R B := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  haveI : Algebra.Etale (MvPolynomial I R) B := h
  obtain ⟨⟨b, hb⟩, hs⟩ := _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B I
  exact ⟨⟨b, fun i => by rw [hb]; simp [RingHom.algebraMap_toAlgebra]⟩, hs⟩

open KaehlerDifferential TensorProduct in
private theorem det_derivation_eq_mul_det_repr {R B I : Type} [CommRing R] [CommRing B] [Fintype I]
    [DecidableEq I] [Algebra R B] (t t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C)
    (hd : ∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x)
    (hc : ∀ i r, d i (algebraMap R B r) = 0) :
    (Matrix.of fun i j => d i (t' j)).det =
      φ (Matrix.of fun k j => b.repr (D R B (t' j)) k).det *
        (Matrix.of fun i j => d i (t j)).det := by
  letI : Algebra B C := φ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ∀ i j, d i (t' j) = ∑ k, d i (t k) * φ (b.repr (D R B (t' j)) k) := by
    intro i j
    let δ : Derivation R B C := Derivation.mk'
      { toFun := d i
        map_add' := map_add (d i)
        map_smul' := fun r x => by
          rw [RingHom.id_apply, Algebra.smul_def r (d i x), Algebra.smul_def, hd, hc, mul_zero,
            add_zero]
          rfl }
      (fun x y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
        exact hd i x y)
    have h1 : ∀ x, d i x = δ.liftKaehlerDifferential (D R B x) := fun x => by
      rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
    rw [h1]
    conv_lhs => rw [← b.sum_repr (D R B (t' j))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hb, ← h1, Algebra.smul_def, mul_comm]
    rfl
  have hmat : (Matrix.of fun i j => d i (t' j)) = (Matrix.of fun i j => d i (t j)) *
      (Matrix.of fun k j => b.repr (D R B (t' j)) k).map φ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, key]
  rw [hmat, Matrix.det_mul, mul_comm]
  congr 1
  exact (RingHom.map_det φ _).symm

open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_of_isUnit_det_repr {R B I : Type} [CommRing R] [CommRing B]
    [Fintype I] [DecidableEq I] [Algebra R B] (t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (ha : IsUnit (Matrix.of fun k j => b.repr (D R B (t' j)) k).det) :
    ∃ b' : Module.Basis I B Ω[B⁄R], ∀ j, b' j = D R B (t' j) := by
  refine ⟨b.map (Matrix.toLinearEquiv b _ ha), fun j => ?_⟩
  rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (D R B (t' j))]
  simp only [Matrix.of_apply]

open KaehlerDifferential TensorProduct in
private theorem etale_eval2Hom_of_basis_D (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] [Algebra.Smooth R B] (t : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  exact _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis R B I b fun i => by
    rw [hb]; simp [RingHom.algebraMap_toAlgebra]


open KaehlerDifferential TensorProduct in
theorem _root_.GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (I : Type) [Fintype I] [DecidableEq I] (t t' : I → B), (MvPolynomial.eval₂Hom c t).Etale → ∃ a : B, (∀ (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C), (∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x) → (∀ i r, d i (c r) = 0) → (Matrix.of fun i j => d i (t' j)).det = φ a * (Matrix.of fun i j => d i (t j)).det) ∧ (IsUnit a → (MvPolynomial.eval₂Hom c t').Etale) := by
  intro R B _ _ c I _ _ t t' het
  letI : Algebra R B := c.toAlgebra
  obtain ⟨⟨b, hb⟩, hs⟩ := exists_basis_D_and_smooth_of_etale_eval2Hom R B I t het
  refine ⟨(Matrix.of fun k j => b.repr (D R B (t' j)) k).det,
    fun C _ φ d hd hc => det_derivation_eq_mul_det_repr t t' b hb C φ d hd hc, fun ha => ?_⟩
  obtain ⟨b', hb'⟩ := exists_basis_D_of_isUnit_det_repr t' b ha
  exact etale_eval2Hom_of_basis_D R B I t' b' hb'

end GlobalTheory.EtaleCoordJacobian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CharSumInv
section
namespace GlobalTheory.CharacterSumInverse

open scoped BigOperators

theorem charSum_inv {o : Type} [CommRing o] [IsDomain o] {T : Type} [CommGroup T] [Fintype T]
    [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)] [DecidableEq T] (t : T) :
    (∑ c : T →* oˣ, ((c t)⁻¹ : oˣ).val) = if t = 1 then (Fintype.card T : o) else 0 := by
  classical
  have hinv : ∀ c : T →* oˣ, ((c t)⁻¹ : oˣ).val = (c t⁻¹).val := fun c => by rw [map_inv]
  simp_rw [hinv]
  split_ifs with ht
  · subst ht
    simp only [inv_one, map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    have h := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T o
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [h]
  · have hs : t⁻¹ ≠ 1 := by simpa using ht
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity T o hs
    set S := ∑ c : T →* oˣ, (c t⁻¹).val with hS
    have hshift : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = S :=
      Fintype.sum_equiv (Equiv.mulLeft φ) _ _ (fun _ => rfl)
    have hmul : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = (φ t⁻¹).val * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp [MonoidHom.mul_apply, Units.val_mul]
    have h0 : ((φ t⁻¹).val - 1) * S = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    have hne : (φ t⁻¹).val - 1 ≠ 0 := by
      intro h
      apply hφ
      exact Units.val_eq_one.mp (sub_eq_zero.mp h)
    exact (mul_eq_zero.mp h0).resolve_left hne

theorem main : (let d1 : {o : Type} → [inst : CommRing o] → {T : Type} → [inst_1 : CommGroup T] → {M : Type} → [inst_2 : AddCommGroup M] → [inst_3 : Module o M] → [Fintype T] → Representation o T M → o → (T →* oˣ) → M →ₗ[o] M := @(fun {o : Type} [CommRing o] {T : Type} [CommGroup T] {M : Type} [AddCommGroup M] [Module o M] [Fintype T] (ρ : Representation o T M) (u : o) (c : T →* oˣ) ↦ u • ∑ t : T, (↑((c : T → oˣ) t)⁻¹ : o) • (ρ : T → M →ₗ[o] M) t); ∀ {o : Type} [inst : CommRing o] {T : Type} [inst_1 : CommGroup T] {M : Type} [inst_2 : AddCommGroup M] [inst_3 : Module o M] [inst_4 : Fintype T] (ρ : Representation o T M) (u : o) [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [inst_7 : Fintype (T →* oˣ)], u * (↑(Fintype.card T) : o) = (1 : o) → ∀ (x : M), ∑ c : T →* oˣ, (d1 ρ u c : M → M) x = x) := by
  intro d1 o _ T _ M _ _ _ ρ u _ _ _ hu x
  classical
  simp only [d1, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, charSum_inv]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one,
    Module.End.one_apply]
  rw [smul_smul, hu, one_smul]

end GlobalTheory.CharacterSumInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosets
section
namespace GlobalTheory.ThetaReal

theorem zmod_pow_exists_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : 1 ≤ n) (hJ : 2 ≤ J)
    (y : ZMod (n ^ J)) (hy : n • y = 0) : ∃ w : ZMod (n ^ J), y = n • w := by
  haveI : NeZero (n ^ J) := ⟨pow_ne_zero _ (by omega)⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 2 := ⟨J - 2, by omega⟩
  have h1 : n * (n * n ^ j) ∣ n * k := by
    have : n * (n * n ^ j) = n ^ (j + 2) := by ring
    rw [this]; exact hy
  have h2 : n * n ^ j ∣ k := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  obtain ⟨c, rfl⟩ := (Dvd.intro _ rfl : n ∣ n * n ^ j).trans h2
  exact ⟨(c : ZMod (n ^ (j + 2))), by rw [nsmul_eq_mul, Nat.cast_mul]⟩

theorem closure_eq_top_of_meets_torsion_cosets :
    ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M),
      (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) →
      AddSubgroup.closure X = ⊤ := by
  intro κ n J M hn hJ hM X hX
  subst hM
  have step : ∀ a : κ → ZMod (n ^ J), ∃ w : κ → ZMod (n ^ J),
      a + n • w ∈ AddSubgroup.closure X := by
    intro a
    obtain ⟨y, hy, hay⟩ := hX a
    have : ∀ i, ∃ w : ZMod (n ^ J), y i = n • w := fun i =>
      zmod_pow_exists_nsmul_of_nsmul_eq_zero n J hn hJ (y i) (congrFun hy i)
    choose w hw using this
    refine ⟨w, ?_⟩
    have : n • w = y := funext fun i => (hw i).symm
    rw [this]
    exact AddSubgroup.subset_closure hay
  have ind : ∀ (i : ℕ) (a : κ → ZMod (n ^ J)), ∃ w : κ → ZMod (n ^ J),
      a + n ^ i • w ∈ AddSubgroup.closure X := by
    intro i
    induction i with
    | zero => intro a; exact ⟨-a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨w, hw⟩ := ih a
      obtain ⟨v, hv⟩ := step (-w)
      refine ⟨v, ?_⟩
      have h := (AddSubgroup.closure X).add_mem hw ((AddSubgroup.closure X).nsmul_mem hv (n ^ i))
      have e : a + n ^ i • w + n ^ i • (-w + n • v) = a + n ^ (i + 1) • v := by
        rw [smul_add, smul_neg, smul_smul, pow_succ]; abel
      rwa [e] at h
  rw [eq_top_iff]
  intro a _
  obtain ⟨w, hw⟩ := ind J a
  have : n ^ J • w = 0 := by
    funext i
    show n ^ J • w i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rwa [this, add_zero] at hw

end GlobalTheory.ThetaReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffEqZeroOfHasSumMFourierOrthonormalImage
section
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem coeff_eq_zero_of_hasSum_mFourier_orthonormal_image {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by
  classical
  have h1 := ((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h
  have h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ) := by
    rw [map_zero] at h1
    refine HasSum.congr_fun h1 fun s => ?_
    have := orthonormal_iff_ite.mp hL t s
    simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]
    by_cases hs : s = t
    · simp [hs]
    · simp [hs, Ne.symm hs]
  exact (hasSum_ite_eq t (b t)).unique h2

theorem mFourier_coe_eq_exp {J : Type} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    UnitAddTorus.mFourier s (fun j => (x j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

theorem coeff_eq_zero_of_fourier_series_eq_zero :
    ∀ (J : Type) [Fintype J] (b : (J → ℤ) → ℂ), (Summable fun s => ‖b s‖) →
      (∀ x : J → ℝ, ∑' s, b s *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) = 0) →
      ∀ s, b s = 0 := by
  intro J _ b hb h0 t
  have hs : Summable (fun s => b s • UnitAddTorus.mFourier s : (J → ℤ) → C(UnitAddTorus J, ℂ)) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using hb
  have hz : (∑' s, b s • UnitAddTorus.mFourier s : C(UnitAddTorus J, ℂ)) = 0 := by
    ext y
    choose x hx using fun j => QuotientAddGroup.mk_surjective (y j)
    have hy : y = fun j => (x j : UnitAddCircle) := funext fun j => (hx j).symm
    have h1 := ((ContinuousMap.evalCLM ℂ y).hasSum hs.hasSum).tsum_eq
    simp only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] at h1
    rw [← h1, hy]
    simp only [mFourier_coe_eq_exp]
    simpa using h0 x
  have hsum := hs.hasSum
  rw [hz] at hsum
  exact coeff_eq_zero_of_hasSum_mFourier_orthonormal_image _ UnitAddTorus.orthonormal_mFourier b hsum t

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompCMulMap
section
open PowerSeries

namespace GlobalTheory.PowerSeriesCompositionMap

variable {O O₁ K : Type} [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁]

noncomputable def comp {ι : Type} (b : Module.Basis ι O O₁) (j : ι) : PowerSeries O₁ →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => b.repr (coeff n f) j
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

lemma coeff_comp {ι : Type} (b : Module.Basis ι O O₁) (j : ι) (f : PowerSeries O₁) (n : ℕ) :
    coeff n (comp b j f) = b.repr (coeff n f) j := by
  simp [comp]

lemma decomp {ι : Type} [Fintype ι] (b : Module.Basis ι O O₁) (f : PowerSeries O₁) :
    f = ∑ j, C (b j) * map (algebraMap O O₁) (comp b j f) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_C_mul, coeff_map, coeff_comp]
  conv_lhs => rw [← b.sum_repr (coeff n f)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, mul_comm]

lemma comp_C_mul_map {ι : Type} (b : Module.Basis ι O O₁) (j : ι) (a : O₁) (g : PowerSeries O) :
    comp b j (C a * map (algebraMap O O₁) g) = C (b.repr a j) * g := by
  ext n
  rw [coeff_comp, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul]
  simp [mul_comm]

variable {ι : Type} [Fintype ι] (b : Module.Basis ι O O₁) (i : PowerSeries O →+* K) (io : O₁ →+* K)

noncomputable def ext : PowerSeries O₁ →+ K :=
  ∑ j, (AddMonoidHom.mulLeft (io (b j))).comp ((i : PowerSeries O →+ K).comp (comp b j))

lemma ext_apply (f : PowerSeries O₁) : ext b i io f = ∑ j, io (b j) * i (comp b j f) := by
  simp [ext, AddMonoidHom.finsetSum_apply]

variable {b i io}

lemma ext_C_mul_map (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) (a : O₁) (g : PowerSeries O) :
    ext b i io (C a * map (algebraMap O O₁) g) = io a * i g := by
  rw [ext_apply]
  simp only [comp_C_mul_map, map_mul, ← h, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← b.sum_repr a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, mul_comm]

lemma ext_mul (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) (f g : PowerSeries O₁) :
    ext b i io (f * g) = ext b i io f * ext b i io g := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [decomp b f, decomp b g, Finset.sum_mul_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [decomp b f, decomp b g, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : C (b j) * map (algebraMap O O₁) (comp b j f) * (C (b k) * map (algebraMap O O₁) (comp b k g))
      = C (b j * b k) * map (algebraMap O O₁) (comp b j f * comp b k g) := by
    rw [map_mul, map_mul]; ring
  rw [e, ext_C_mul_map h, ext_C_mul_map h, ext_C_mul_map h, map_mul, map_mul]
  ring

theorem main (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁]
    [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K)
    (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a : O₁, Φ (C a) = io a) ∧ Φ X = i X ∧
      ∀ f : PowerSeries O₁, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  let b := Module.Free.chooseBasis O O₁
  have hC : ∀ a : O₁, ext b i io (C a) = io a := fun a => by
    simpa using ext_C_mul_map (b := b) h a 1
  let Φ : PowerSeries O₁ →+* K :=
    { ext b i io with
      map_one' := by simpa using hC 1
      map_mul' := ext_mul h }
  refine ⟨Φ, hC, ?_, fun f => ?_⟩
  · show ext b i io X = i X
    simpa using ext_C_mul_map (b := b) h 1 X
  · show ext b i io f ∈ _
    rw [ext_apply]
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

end GlobalTheory.PowerSeriesCompositionMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
section
open Module

namespace GlobalTheory.ZH

theorem div_mem_of_forall_pow_succ_div_pow_mem :
    ∀ (Ω : Type) [Field Ω] (O : Subring Ω) [ValuationRing O] [IsNoetherianRing O],
      (∀ x : Ω, x ∈ O ∨ x⁻¹ ∈ O) → ∀ f f' : Ω, f ≠ 0 → f' ≠ 0 →
        (∀ j : ℕ, 1 ≤ j → f' ^ (j + 1) / f ^ j ∈ O) → f' / f ∈ O := by
  intro Ω _ O _ _ hO f f' hf hf' h
  by_contra hn
  have hg : f / f' ∈ O := by
    rcases hO (f' / f) with h1 | h1
    · exact absurd h1 hn
    · simpa using h1
  set g : O := ⟨f / f', hg⟩ with hgdef
  have hI : Ideal.span {g} ≠ ⊤ := by
    intro htop
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_top.mp htop).exists_right_inv
    have hu' : f / f' * (u : Ω) = 1 := congrArg Subtype.val hu
    have : (u : Ω) = f' / f := by
      field_simp at hu' ⊢
      linear_combination hu'
    exact hn (this ▸ u.2)
  have hK := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hmem : (⟨f' ^ (1 + 1) / f ^ 1, h 1 le_rfl⟩ : O) ∈ ⨅ n : ℕ, Ideal.span {g} ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨f' ^ (n + 1 + 1) / f ^ (n + 1), h (n + 1) (by omega)⟩, Subtype.ext ?_⟩
    simp only [hgdef, Subring.coe_mul, SubmonoidClass.coe_pow, div_pow]
    field_simp
    ring
  rw [hK, Ideal.mem_bot] at hmem
  have h0 : f' ^ (1 + 1) / f ^ 1 = 0 := congrArg Subtype.val hmem
  exact div_ne_zero (pow_ne_zero _ hf') (pow_ne_zero _ hf) h0

end GlobalTheory.ZH
end

