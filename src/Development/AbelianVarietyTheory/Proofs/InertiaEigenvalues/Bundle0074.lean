module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystem
section
open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem winPt_card (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F)
    (lam π : Fin h → F) (hπ : ∀ j, π j ≠ 0) (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F)
    (hM : ∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) :
    Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} =
      Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  set φ := iterateFrobeniusEquiv F p (h * (L - 1)) with hφ
  have hpow : ∀ y : F, φ y = y ^ (p ^ h) ^ (L - 1) := fun y => by
    rw [hφ, iterateFrobeniusEquiv_def, pow_mul]
  have hN : (p ^ h) ^ (L - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hwin : ∀ z : Fin h → F, ∀ j, winPt p π L z j = π j * φ (z j) := fun z j => by
    simp only [winPt, hpow]
  symm
  refine Nat.card_congr
    { toFun := fun z => ⟨winPt p π L z.1, fun j => ?_, (hM z.1).1 z.2.2⟩
      invFun := fun x => ⟨fun j => φ.symm (x.1 j / π j), fun j => ?_, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun x => ?_ }
  · rw [hwin, norm_mul, hpow, norm_pow]
    have h0 : 0 ≤ ‖z.1 j‖ := norm_nonneg _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ h0 (z.2.1 j))
  · have hx : ‖φ (φ.symm (x.1 j / π j))‖ ≤ 1 := by
      rw [RingEquiv.apply_symm_apply, norm_div, div_le_one (norm_pos_iff.2 (hπ j))]
      exact x.2.1 j
    rw [hpow, norm_pow] at hx
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN).1 hx
  · rw [hM]
    have : winPt p π L (fun j => φ.symm (x.1 j / π j)) = x.1 := by
      funext j
      rw [hwin, RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]
    rw [this]; exact x.2.2
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [mul_div_cancel_left₀ _ (hπ j), RingEquiv.symm_apply_apply]
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuter
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section WinInner

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def frobPerm : Equiv.Perm F := (frobeniusEquiv F p).toEquiv

theorem frobPerm_pow_apply (n : ℕ) (x : F) : (frobPerm (F := F) p ^ n) x = x ^ p ^ n := by
  rw [Equiv.Perm.coe_pow]
  have : (⇑(frobPerm (F := F) p)) = frobenius F p := by
    funext y; simp [frobPerm]
  rw [this, iterate_frobenius]

theorem pw_eq_zpow (k : ℤ) (x : F) : pw p k x = (frobPerm (F := F) p ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frobPerm_pow_apply]
    simp
  · push_neg at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]
    simp only [neg_neg, Int.toNat_natCast]
    rfl

theorem pw_pow (k : ℤ) (h : ℕ) (y : F) : pw p k (y ^ p ^ h) = pw p (k + h) y := by
  rw [pw_eq_zpow, pw_eq_zpow, ← frobPerm_pow_apply, ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]

theorem term_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (r j : Fin h) (n : ℤ) :
    term p ϖ lam (fun i => x' i ^ p ^ h) r j n = ϖ * term p ϖ lam x' r j (n + 1) := by
  unfold term
  rw [pw_pow]
  have h1 : ((r : ℤ) + n * h + h) = (r : ℤ) + (n + 1) * h := by ring
  have h2 : ϖ ^ (-n) = ϖ * ϖ ^ (-(n + 1)) := by
    rw [show -n = -(n + 1) + 1 by ring, zpow_add_one₀ hϖ]; ring
  rw [h1, h2]; ring

theorem rowT_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (K : ℕ) (hK : 1 ≤ K) (r : Fin h) :
    rowT p ϖ lam K (fun i => x' i ^ p ^ h) r = ϖ * rowS p ϖ lam (K - 1) (K + 1) x' r := by
  unfold rowT rowS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [term_pow p ϖ hϖ]
  rw [← Finset.mul_sum]
  congr 1
  have hI : Finset.Icc (-((K - 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)
      = (Finset.Icc (-(K : ℤ)) (K : ℤ)).map (addRightEmbedding 1) := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> push_cast [hK] <;> ring
  rw [hI, Finset.sum_map]
  rfl

end WinInner

theorem win_inner : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F),
    ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F,
      Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} =
        Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  intro F _ p _ _ _ h K ϖ hϖ hK lam π
  let e : (Fin h → F) ≃ (Fin h → F) := Equiv.piCongrRight fun _ => frobPerm (F := F) p ^ h
  have he : ∀ x' : Fin h → F, e x' = fun i => x' i ^ p ^ h := by
    intro x'; funext i; simp [e, frobPerm_pow_apply]
  symm
  refine Nat.card_congr (e.subtypeEquiv fun x' => ?_)
  rw [he]
  have hq : p ^ h ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h1 j) _
    · rw [rowT_pow p ϖ hϖ lam x' K hK, h2 r, mul_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · have := h1 j
      rw [norm_pow] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hq).1 this
    · have := h2 r
      rw [rowT_pow p ϖ hϖ lam x' K hK] at this
      exact (mul_eq_zero.1 this).resolve_left hϖ

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundaryStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary : ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G] (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), Topology.IsEmbedding (fun m : M => ϖ • m) → ∀ (s : Finset (Z1 ρ)), (∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ)) → ∀ c : Z1 ρ, ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M), (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  first | exact @GlobalTheory.cocycle_lift_mod_uniformizer | exact GlobalTheory.cocycle_lift_mod_uniformizer | (intros; apply GlobalTheory.cocycle_lift_mod_uniformizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsCharpolyCoeffEq
section
open GlobalTheory.JR Matrix

namespace GlobalTheory.JR.CompanionCharpoly

theorem companion_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {r : ℕ} (p : Fin r → k) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [Matrix.map_apply, companion, Matrix.of_apply]
  split_ifs <;> simp

theorem coeff_universal (r : ℕ) (i : Fin r) :
    (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).charpoly.coeff (i : ℕ) =
      MvPolynomial.X i := by
  set R := MvPolynomial (Fin r) ℤ
  set K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  apply hinj
  have h := GlobalTheory.JR.NormalFormL.charpoly_companion_coeff
    (fun j : Fin r => algebraMap R K (MvPolynomial.X j)) i
  rw [← companion_map, Matrix.charpoly_map, Polynomial.coeff_map] at h
  exact h

theorem charpoly_companion_coeff_ring :
    ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  intro k _ r p i
  let f : MvPolynomial (Fin r) ℤ →+* k := MvPolynomial.eval₂Hom (Int.castRingHom k) p
  have hp : companion p = (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).map f := by
    rw [companion_map]
    congr 1
    funext j
    simp [f]
  rw [hp, Matrix.charpoly_map, Polynomial.coeff_map, coeff_universal]
  simp [f]

end GlobalTheory.JR.CompanionCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
section
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem norm_val_monoidHom_units_eq_one {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    ‖((ξ g : ℂˣ) : ℂ)‖ = 1 := by
  have h : (ξ g) ^ (Nat.card G) = 1 := by rw [← map_pow, pow_card_eq_one']; exact map_one ξ
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isIntegral_int_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [h]⟩

theorem isIntegral_val_monoidHom_units {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((ξ g : ℂˣ) : ℂ) := by
  refine isIntegral_int_of_pow_eq_one (n := Nat.card G) Nat.card_pos ?_
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem isIntegral_addChar_apply {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (x : k) :
    IsIntegral ℤ (ψ x) := by
  refine isIntegral_int_of_pow_eq_one (n := Fintype.card k) Fintype.card_pos ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]

theorem complexMatrixGaussSum_norm_integral_galois :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∀ S : ℂ, S = (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))) → ‖S‖ ^ 2 = (Fintype.card k : ℝ) ^ (r ^ 2) ∧ IsIntegral ℤ S ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ (r ^ 2) * S⁻¹) ∧ ∀ (τ : ℂ ≃+* ℂ) (ξ' : kˣ →* ℂˣ), (∀ x, ((ξ' x : ℂˣ) : ℂ) = τ ((ξ x : ℂˣ) : ℂ)) → ∃ a : kˣ, (∀ x, τ (ψ x) = ψ ((a : k) * x)) ∧ τ S = ((ξ' a : ℂˣ) : ℂ) ^ r * ∑ x : GL (Fin r) k, (((ξ' (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) := by
  intro k _ _ _ ψ ξ r hψ hξ S hS
  have hN := _root_.GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow k ℂ ψ ξ r hψ hξ
  simp only [Matrix.one_mul] at hN
  rw [← hS] at hN
  set D := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hD
  have hconj : D = starRingEnd ℂ S := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj, MonoidHom.inv_apply, inv_inv,
      Units.val_inv_eq_inv_val, map_inv₀,
      ← Complex.inv_eq_conj (norm_val_monoidHom_units_eq_one ξ _), inv_inv]
  have hDint : IsIntegral ℤ D := by
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    exact isIntegral_val_monoidHom_units _ _
  have hSint : IsIntegral ℤ S := by
    rw [hS]
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    rw [← map_inv]
    exact isIntegral_val_monoidHom_units _ _
  have hq0 : (Fintype.card k : ℂ) ^ (r ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hS0 : S ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hN
    exact hq0 hN.symm
  refine ⟨?_, hSint, ?_, ?_⟩
  · rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hN
    exact_mod_cast hN
  · rw [← hN, mul_comm S D, mul_assoc, mul_inv_cancel₀ hS0, mul_one]
    exact hDint
  · intro τ ξ' hξ'

    let φ : AddChar k ℂ := (τ : ℂ →+* ℂ).toMonoidHom.compAddChar ψ
    have hbij : Function.Bijective (fun b : k => ψ.mulShift b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ, AddChar.card_eq.symm⟩
    obtain ⟨b, hb⟩ := hbij.2 φ
    have hbφ : ∀ x, τ (ψ x) = ψ (b * x) := fun x => by
      have := DFunLike.congr_fun hb x
      simpa [φ, AddChar.mulShift_apply] using this.symm
    have hb0 : b ≠ 0 := by
      rintro rfl
      have h1 : ψ.mulShift 1 ≠ 1 := hψ one_ne_zero
      apply h1
      ext x
      have := hbφ x
      rw [zero_mul, AddChar.map_zero_eq_one, ← map_one τ] at this
      rw [AddChar.mulShift_apply, one_mul, AddChar.one_apply]
      exact τ.injective this
    have hξ'1 : ξ' ≠ 1 := by
      intro h1
      apply hξ
      ext x
      have := hξ' x
      rw [h1, MonoidHom.one_apply, Units.val_one, ← map_one τ] at this
      exact (τ.injective this).symm
    refine ⟨Units.mk0 b hb0, fun x => hbφ x, ?_⟩
    let g : GL (Fin r) k :=
      Units.map (Matrix.scalar (Fin r) : k →+* Matrix (Fin r) (Fin r) k).toMonoidHom (Units.mk0 b hb0)
    have hg : (g : Matrix (Fin r) (Fin r) k) = Matrix.scalar (Fin r) b := rfl
    have hdet : Matrix.GeneralLinearGroup.det g = (Units.mk0 b hb0) ^ r := by
      ext
      simp [hg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]
    have key := (GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ' r hψ hξ'1).2 g
    rw [hdet, map_pow, Units.val_pow_eq_pow_val] at key
    simp only [Matrix.one_mul] at key
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← key, hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, hbφ, Units.val_inv_eq_inv_val, map_inv₀, ← hξ', ← Units.val_inv_eq_inv_val, hg,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousDistribHaarCharUnitsOfCompactOpen
section
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory

theorem continuous_distribHaarChar_units_of_compact_open (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSn : S.Nonempty) : Continuous (fun u : Rˣ => distribHaarChar R u) := by
  obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hSc hSo subset_rfl
  have h0 : μ S ≠ 0 := hSo.measure_ne_zero μ hSn
  have ht : μ S ≠ ⊤ := hSc.measure_lt_top.ne
  have hle : ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u ≤ 1 := by
    intro u hu
    have h1 : μ (u • S) ≤ μ S := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u S] at h1
    have h2 : ((distribHaarChar R u : NNReal) : ENNReal) * μ S ≤ 1 * μ S := by simpa using h1
    have h3 := (ENNReal.mul_le_mul_iff_left h0 ht).1 h2
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
    Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
  have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
    Units.continuous_coe_inv.continuousAt.eventually
      (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
  have e3 : (fun _ : Rˣ => (1 : NNReal)) =ᶠ[𝓝 1] (distribHaarChar R : Rˣ →* NNReal) := by
    filter_upwards [e1, e2] with u h1 h2
    have a1 := hle u h1
    have a2 := hle u⁻¹ h2
    have a3 : distribHaarChar R u * distribHaarChar R u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    refine le_antisymm ?_ a1
    calc (1 : NNReal) = distribHaarChar R u * distribHaarChar R u⁻¹ := a3.symm
      _ ≤ distribHaarChar R u * 1 := by gcongr
      _ = _ := mul_one _
  exact continuousAt_const.congr e3

theorem exists_isHaarMeasure_units_div_module : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [IsOpenUnits R] [MeasurableSpace R] [BorelSpace R] [BorelSpace Rˣ] (μ : Measure R), μ.IsAddHaarMeasure → (∃ S : Set R, IsOpen S ∧ IsCompact S ∧ S.Nonempty) → ∃ μ' : Measure Rˣ, μ'.IsHaarMeasure ∧ ∀ (g δ : R → ℂ), (∀ u : Rˣ, δ u = ((distribHaarChar R u : ℝ) : ℂ)) → ∀ T : Set Rˣ, MeasurableSet T → ∫ u in T, g u ∂μ' = ∫ t in Units.val '' T, g t * (δ t)⁻¹ ∂μ := by
  intro R _ _ _ _ _ _ _ _ _ _ μ hμ ⟨S, hSo, hSc, hSn⟩
  have hc := continuous_distribHaarChar_units_of_compact_open R μ S hSo hSc hSn
  have hoe : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : Rˣ → R) := hoe.measurableEmbedding
  set ν : Measure Rˣ := μ.comap Units.val with hν
  set f : Rˣ → NNReal := fun u => distribHaarChar R u⁻¹ with hf
  have hfc : Continuous f := hc.comp continuous_inv
  have hνa : ∀ s : Set Rˣ, ν s = μ (Units.val '' s) := fun s => hme.comap_apply μ s
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := μ.finiteAt_nhds (x : R)
    refine ⟨Units.val ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero μ (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ENNReal)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => by
      simpa [hf] using (distribHaarChar_pos (A := R) (g := x)).ne'
  have hinv : (ν.withDensity fun x => (f x : ENNReal)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : Rˣ => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : Rˣ => a * x) ν = (f a : ENNReal) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul, hf,
        distribHaarChar_mul μ a⁻¹]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨a * x, hx, rfl⟩, by simp [Units.smul_def]⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨a⁻¹ * x, by simpa using hx, by simp [Units.smul_def]⟩
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x : Rˣ, (f x : ENNReal) = (f a⁻¹ : ENNReal) * (f (a * x) : ENNReal) := by
      intro x
      rw [← ENNReal.coe_mul, hf]
      simp only
      rw [← map_mul]
      congr 2
      simp [mul_comm a x, mul_left_comm]
    have h2 : (f a⁻¹ : ENNReal) * (f a : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, hf]
      simp only
      rw [← map_mul]
      simp
    calc ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f x : ENNReal) ∂ν
        = ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f a⁻¹ : ENNReal) * (f (a * x) : ENNReal) ∂ν := by
          exact lintegral_congr h1
      _ = (f a⁻¹ : ENNReal) * ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f (a * x) : ENNReal) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ENNReal) * ∫⁻ x in s, (f x : ENNReal) ∂(Measure.map (fun x : Rˣ => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2,
            one_mul]
  refine ⟨ν.withDensity fun x => (f x : ENNReal), ⟨⟩, fun g δ hδ T hT => ?_⟩
  rw [setIntegral_withDensity_eq_setIntegral_smul hfc.measurable _ hT]
  have h3 := hme.setIntegral_map (μ := ν) (fun t => g t * (δ t)⁻¹) (Units.val '' T)
  rw [hν, hme.map_comap, Measure.restrict_restrict (hme.measurableSet_image.2 hT),
    Set.inter_eq_left.2 (Set.image_subset_range _ _),
    Set.preimage_image_eq _ hme.injective] at h3
  rw [h3]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [hδ, hf, map_inv, NNReal.smul_def, NNReal.coe_inv, Complex.real_smul]
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZero
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem etale_norm_continuous_and_zero (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := by
  classical
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  let b0 := Module.finBasisOfFinrankEq F E h2
  let b : Module.Basis (Fin 2) A.K A.L := hb.basis b0
  have hN : ∀ y, A.NL y = (Algebra.leftMulMatrix b y).det := fun y => Algebra.norm_eq_matrix_det b y
  refine ⟨?_, ?_⟩
  · have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := funext hN
    rw [this]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    let f : A.L →ₗ[F] A.K := ((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine hf.congr fun y => ?_
    simp [f, Algebra.leftMulMatrix_eq_repr_mul]
  · rw [hN, map_zero]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussPointStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussPoint' : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧ IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧ ∀ x, vV T'.V (i x) = vV T.V x := by
  exact @GlobalTheory.GaussPoint.exists_gaussPoint
end

