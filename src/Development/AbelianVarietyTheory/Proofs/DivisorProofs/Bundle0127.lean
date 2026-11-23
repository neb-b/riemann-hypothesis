module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKilledByIdealModIntEqAbsNormPow
section
open scoped NumberField

namespace GlobalTheory.TorsQuotCount

variable {K : Type} [Field K] [NumberField K] {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

theorem flat_of_free [Module.Free ℤ M] : Module.Flat (𝓞 K) M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : a • x = 0 := hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hI : Ideal.span {a} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using ha0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  have h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← ht, mul_smul, hx', smul_zero]
  exact (Submodule.mem_bot _).2 ((smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN))

theorem finrank_eq [Module.Free ℤ M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.finrank ℤ M = r * Module.finrank ℚ K) : Module.finrank (𝓞 K) M = r := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have h20 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  have hI : Ideal.span {(2 : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using h20
  haveI : Finite (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have e1 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(2 : 𝓞 K)})
  haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) :=
    Nat.finite_of_card_ne_zero (by rw [Int.card_ideal_quot]; norm_num)
  have e2 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := ℤ) (N := M) (Ideal.span {((2 : ℕ) : ℤ)})
  rw [Int.card_ideal_quot] at e2
  have hq : Nat.card (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) = 2 ^ Module.finrank ℚ K := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
    have h2 : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
    rw [h2, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hPQ : (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M).restrictScalars ℤ =
      (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [two_smul]⟩
  have hsame : Nat.card (M ⧸ (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)) =
      Nat.card (M ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M)) := by
    rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)).toEquiv, hPQ]
  rw [hsame, e2, hq, hr, ← pow_mul] at e1
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h3 := Nat.pow_right_injective (le_refl 2) e1
  have h4 : Module.finrank ℚ K * r = Module.finrank ℚ K * Module.finrank (𝓞 K) M := by
    rw [mul_comm] at h3; exact h3
  exact (Nat.eq_of_mul_eq_mul_left hn h4).symm

theorem card_killed_eq : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M],
    Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K →
    ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 →
    Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} =
      Ideal.absNorm 𝔟 ^ r := by
  intro K _ _ M _ _ hfree hfin r hr 𝔟 c hc hcb
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have hd := finrank_eq (K := K) (M := M) r hr
  have hc0 : (c : 𝓞 K) ≠ 0 := by exact_mod_cast hc.ne'
  have hspan : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc0
  have hb : 𝔟 ≠ ⊥ := fun h => hc0 (by rw [h] at hcb; exact (Submodule.mem_bot _).1 hcb)
  haveI : Finite (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hspan
  haveI : Finite (𝓞 K ⧸ 𝔟) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have hX := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(c : 𝓞 K)})
  have hNc : Nat.card (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) ≠ 0 := Nat.card_pos.ne'
  set P : Submodule (𝓞 K) M := Ideal.span {(c : 𝓞 K)} • ⊤ with hP
  haveI : Finite (M ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hX]; exact pow_ne_zero _ hNc)
  obtain ⟨b, hbsup⟩ := IsDedekindDomain.exists_sup_span_eq ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb) hspan
  have hcX : ∀ x : M ⧸ P, (c : 𝓞 K) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  let f : (M ⧸ P) →ₗ[𝓞 K] (M ⧸ P) := b • LinearMap.id
  have hf : ∀ x, f x = b • x := fun x => rfl
  have hmem : ∀ a ∈ 𝔟, ∃ u v : 𝓞 K, a = u * c + v * b := by
    intro a ha
    rw [← hbsup, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨u, v, rfl⟩
  have hbmem : b ∈ 𝔟 := hbsup ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  have e1 : {x : M ⧸ P // ∀ a ∈ 𝔟, a • x = 0} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1, by rw [LinearMap.mem_ker, hf]; exact x.2 b hbmem⟩
      invFun := fun x => ⟨x.1, fun a ha => by
        obtain ⟨u, v, rfl⟩ := hmem a ha
        have hx : b • (x.1 : M ⧸ P) = 0 := by rw [← hf]; exact x.2
        rw [add_smul, mul_smul, mul_smul, hcX, hx, smul_zero, smul_zero, add_zero]⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card ((M ⧸ P) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hker : Nat.card (LinearMap.ker f) = Nat.card ((M ⧸ P) ⧸ LinearMap.range f) := by
    rw [h3] at h1
    have h4 := h1.symm.trans h2
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact h4)
  have hPle : P ≤ 𝔟 • ⊤ := Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb)
  have hrange : LinearMap.range f = Submodule.map P.mkQ (𝔟 • ⊤) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H m => exact ⟨b • m, Submodule.smul_mem_smul hbmem trivial, by simp [hf]⟩
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.smul_induction_on (p := fun m => P.mkQ m ∈ LinearMap.range f) hm ?_ ?_
      · intro a ha n _
        obtain ⟨u, v, rfl⟩ := hmem a ha
        refine ⟨v • P.mkQ n, ?_⟩
        rw [hf, map_smul, add_smul, mul_smul, mul_smul, hcX, smul_zero, zero_add]
        exact smul_comm _ _ _
      · intro x y hx hy
        rw [map_add (f := _)]
        exact add_mem hx hy
  have hQ : Nat.card ((M ⧸ P) ⧸ LinearMap.range f) = Nat.card (M ⧸ (𝔟 • ⊤ : Submodule (𝓞 K) M)) := by
    rw [hrange]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotient P (𝔟 • ⊤) hPle).toEquiv
  have hM := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) 𝔟
  rw [Nat.card_congr e1, hker, hQ, hM, hd, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]

end GlobalTheory.TorsQuotCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSubtypeEqOfMultiset
section
open Matrix GlobalTheory.LKTrip Finset

namespace GlobalTheory.SigDiag

theorem eigenvalues_multiset_eq {n : ℕ} (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian) :
    Multiset.map hA.eigenvalues univ.val = Multiset.map r univ.val := by
  have h3 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at h3
  · have h4 := congrArg (Multiset.map Complex.re) h3
    simp only [Polynomial.roots_X_sub_C, Multiset.map_map] at h4
    simpa [Function.comp_def, Multiset.bind_singleton] using h4.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem card_subtype_eq_of_multiset {n : ℕ} {f g : Fin n → ℝ}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {i // P (f i)} = Fintype.card {i // P (g i)} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have e : ∀ k : Fin n → ℝ, (univ.filter fun i => P (k i)).card =
      Multiset.countP P (Multiset.map k univ.val) := by
    intro k
    rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]
  rw [e f, e g, h]

end GlobalTheory.SigDiag

namespace GlobalTheory.LKTrip

theorem sigPosH_sigNegH_diagonal : ∀ (n : ℕ) (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian),
    sigPosH hA = Fintype.card {i // 0 < r i} ∧ sigNegH hA = Fintype.card {i // r i < 0} := by
  intro n r hA
  have h := GlobalTheory.SigDiag.eigenvalues_multiset_eq r hA
  exact ⟨GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => 0 < x),
    GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => x < 0)⟩

end GlobalTheory.LKTrip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder MatrixOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem cartanInvolution_conj_of_posDef (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformSkewMemUnitaryGroup
section
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.CayleyUnitary

open Formalism.UG

theorem cT_add' {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A + B) = cT σ A + cT σ B := by
  unfold cT; rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]

theorem cT_sub' {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A - B) = cT σ A - cT σ B := by
  unfold cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.transpose_sub]

theorem cayley_mem_UJ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E) :
    J.det ≠ 0 → cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  intro hJ hS hd
  have hneg : cT σ S * J = -(J * S) := eq_neg_of_add_eq_zero_left hS
  have hBu : IsUnit (1 - S).det := isUnit_iff_ne_zero.mpr hd
  have hBBi : (1 - S) * (1 - S)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have h1 : cT σ (1 + S) * J = J * (1 - S) := by
    rw [cT_add', cT_one, Matrix.add_mul, Matrix.one_mul, hneg, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
  have h2 : J * (1 + S) = cT σ (1 - S) * J := by
    rw [cT_sub', cT_one, Matrix.sub_mul, Matrix.one_mul, hneg, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  have hc : (1 - S) * (1 + S) = (1 + S) * (1 - S) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]; abel
  have key : cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J := by
    rw [cT_mul]
    calc cT σ (1 - S)⁻¹ * cT σ (1 + S) * J * ((1 + S) * (1 - S)⁻¹)
        = cT σ (1 - S)⁻¹ * (cT σ (1 + S) * J) * (1 + S) * (1 - S)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * J * ((1 - S) * (1 + S)) * (1 - S)⁻¹ := by
          rw [h1]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * (J * (1 + S)) * ((1 - S) * (1 - S)⁻¹) := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = J := by
          rw [h2, hBBi, Matrix.mul_one, ← Matrix.mul_assoc, ← cT_mul, hBBi, cT_one, Matrix.one_mul]
  have hdet : ((1 + S) * (1 - S)⁻¹).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ this.symm
  refine ⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), ?_, rfl⟩
  show cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J
  exact key

end GlobalTheory.CayleyUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CcSubst
section
open Polynomial

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (GlobalTheory.taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  obtain ⟨r, hr⟩ := hT
  have hS' : S' = S + PowerSeries.X ^ m * PowerSeries.C c + PowerSeries.X ^ (m + 1) * r := by
    linear_combination hr
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have heq : (y + PowerSeries.X ^ (n + 1) * g) * S' - y * S
      - PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c)
      = PowerSeries.X ^ (n + 1) * (y * PowerSeries.C c - PowerSeries.C (y0 * c)
          + (g * S - PowerSeries.C (PowerSeries.constantCoeff g * A)))
        + PowerSeries.X ^ (n + 1 + 1) * (y * r + PowerSeries.X ^ n *
          (g * PowerSeries.C c + PowerSeries.X * g * r)) := by
    rw [hS', map_add (f := _)]; ring
  rw [heq]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [PowerSeries.X_dvd_iff]
  simp [hy, hS]

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

theorem deform : ∀ (k J I : Type) [Field k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N → (N : k) ≠ 0 →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * ((GlobalTheory.PicDiv.hasse l (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ N ξ s y₀ hN hNk h0 hlow hN' hsurj
  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l f)
      = PowerSeries.coeff l f := fun f l => GlobalTheory.PicDiv.constantCoeff_hasse l f
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l f)
      = ((l + 1 : ℕ) : k) * PowerSeries.coeff (l + 1) f := fun f l => GlobalTheory.PicDiv.coeff_one_hasse l f
  have hsur : Function.Surjective (lin N ξ s y₀) := by
    intro w
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : N - 1 + 1 = N := by omega
      rw [e1]
      calc ∑ j, y₀ j * (((N : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((N : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hNk (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse (N - 1) (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dite_eq_left l.2] at this
          exact this
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((l.1 + 1 : ℕ) : k) * PowerSeries.coeff (l.1 + 1) (s i j))
              = ((l.1 + 1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (l.1 + 1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (l.1 + 1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by
    intro e
    rcases e with _ | ⟨i, l⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [sys, map_sum, h0]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
        have h' : ∀ j, PowerSeries.constantCoeff ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst
            (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = PowerSeries.coeff l.1 (s i j) := by
          intro j; rw [cc_subst _ _ (by simp), hA]
        simp only [h']
        exact hlow i l.1 l.2
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))) := by
        intro j
        have T := GlobalTheory.taylor_subst_first_order k (GlobalTheory.PicDiv.hasse l.1 (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
          Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.newton_powerSeries_target k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.PicDiv.DeformZerosHasse
end

