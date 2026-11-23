module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivativeCyclotomicMul
section
open GlobalTheory.K5 Polynomial TrivSqZeroExt

noncomputable section
namespace GlobalTheory.K5.DlogUniq

section generic
variable {R : Type*} [CommRing R]

theorem aeval_dual {S : Type*} [CommRing S] [Algebra R S] (a m : S) (f : R[X]) :
    (aeval (inl a + inr m : DualNumber S) f).fst = aeval a f ∧
    (aeval (inl a + inr m : DualNumber S) f).snd = aeval a (derivative f) * m := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add (f := _), fst_add, snd_add, hf.1, hf.2, hg.1, hg.2, map_add (f := _), map_add (f := _), map_add (f := _), add_mul]
    exact ⟨rfl, rfl⟩
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, derivative_monomial, aeval_monomial]
    constructor
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_pow]
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_pow]
      ring

theorem exists_derivation (Φ : R[X]) (N : ℕ) (q : R) (I : Ideal R[X][X])
    (hI : I = Ideal.span {C Φ, X ^ N - C (C q)}) (S : Type*) [CommRing S] [Algebra R S]
    [Algebra (R[X][X] ⧸ I) S] [IsScalarTower R (R[X][X] ⧸ I) S] (mx my : S)
    (hx : algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) (derivative Φ)) * mx = 0)
    (hy : (N : S) * my = 0) :
    ∃ D : Derivation R (R[X][X] ⧸ I) S,
      D (Ideal.Quotient.mk I (C X)) = mx ∧ D (Ideal.Quotient.mk I X) = my := by
  let π : R[X][X] →+* S := (algebraMap (R[X][X] ⧸ I) S).comp (Ideal.Quotient.mk I)
  let ψ0 : R[X][X] →+* DualNumber S :=
    eval₂RingHom (aeval (inl (π (C X)) + inr mx : DualNumber S) : R[X] →ₐ[R] DualNumber S).toRingHom
      (inl (π X) + inr my)
  have hC : ∀ f : R[X], ψ0 (C f) = aeval (inl (π (C X)) + inr mx : DualNumber S) f := by
    intro f; simp [ψ0]
  have hX : ψ0 X = inl (π X) + inr my := by simp [ψ0]
  have hπC : ∀ f : R[X], aeval (π (C X)) f = π (C f) := by
    intro f
    have : (aeval (π (C X)) : R[X] →ₐ[R] S).toRingHom = π.comp C := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
        exact IsScalarTower.algebraMap_apply R (R[X][X] ⧸ I) S a
      · simp
    exact congrArg (fun g => g f) this
  have hπC' : ∀ f : R[X], aeval (π (C X)) f =
      algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) f) := by
    intro f
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R (R[X][X] ⧸ I) S) (Ideal.Quotient.mk I (C X)) f)
  have hfst : ∀ f, (ψ0 f).fst = π f := by
    intro f
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp ψ0 = π := by
      apply Polynomial.ringHom_ext
      · intro a
        show (ψ0 (C a)).fst = _
        rw [hC, (aeval_dual _ _ _).1, hπC]
      · show (ψ0 X).fst = _
        rw [hX]; simp
    exact congrArg (fun g => g f) this
  have hπI : ∀ f ∈ I, π f = 0 := by
    intro f hf
    show algebraMap (R[X][X] ⧸ I) S (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hker : ∀ f ∈ I, ψ0 f = 0 := by
    have : I ≤ RingHom.ker ψ0 := by
      have h1 : C Φ ∈ I := hI ▸ Ideal.subset_span (by simp)
      have h2 : X ^ N - C (C q) ∈ I := hI ▸ Ideal.subset_span (by simp)
      refine hI.le.trans (Ideal.span_le.2 ?_)
      rintro f (rfl | rfl)
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h1]; rfl
        · rw [hC, (aeval_dual _ _ _).2, hπC']; exact hx
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h2]; rfl
        · rw [map_sub, map_pow, hX, hC, aeval_C, snd_sub, snd_pow, TrivSqZeroExt.algebraMap_eq_inl']
          simp only [snd_add, snd_inl, snd_inr, zero_add, sub_zero, snd_zero, smul_eq_mul, nsmul_eq_mul]
          rw [mul_left_comm, hy, mul_zero]
    exact fun f hf => this hf
  let ψ : (R[X][X] ⧸ I) →+* DualNumber S := Ideal.Quotient.lift I ψ0 hker
  have hψ : ∀ z, (ψ z).fst = algebraMap (R[X][X] ⧸ I) S z := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hfst f
  have hleib : ∀ a b, (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd := by
    intro a b
    rw [map_mul, DualNumber.snd_mul, hψ, hψ, Algebra.smul_def, Algebra.smul_def, mul_comm (ψ a).snd]
  have halg : ∀ c : R, (ψ (algebraMap R _ c)).snd = 0 := by
    intro c
    show (ψ0 (C (C c))).snd = 0
    rw [hC, (aeval_dual _ _ _).2]; simp
  let L : (R[X][X] ⧸ I) →ₗ[R] S :=
    { toFun := fun z => (ψ z).snd
      map_add' := fun a b => by rw [RingHom.map_add ψ, snd_add]
      map_smul' := fun c z => by
        rw [Algebra.smul_def, hleib, halg, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' L hleib, ?_, ?_⟩
  · show (ψ0 (C X)).snd = mx
    rw [hC]; simp
  · show (ψ0 X).snd = my
    rw [hX]; simp

end generic

variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_quot {A : Type*} [CommRing A] (k l : ℕ) :
    ((k ^ l : ℕ) : A ⧸ Ideal.span {(k : A) ^ l}) * 1 = 0 := by
  rw [mul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(k : A) ^ l})),
    Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

theorem aeval_xn (n : ℕ) (f : (O0 p)[X]) :
    aeval (xn p n) f = Ideal.Quotient.mk (towerIdeal p n) (C f) := by
  have : (aeval (xn p n) : (O0 p)[X] →ₐ[O0 p] On p n).toRingHom =
      (Ideal.Quotient.mk (towerIdeal p n)).comp C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
      rfl
    · simp [xn]
  exact congrArg (fun g => g f) this

theorem aeval_xn_cyclotomic (n : ℕ) : aeval (xn p n) (cyclotomic (p ^ n) (O0 p)) = 0 := by
  rw [aeval_xn, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem isUnit_xn (m : ℕ) : IsUnit (xn p (m + 1)) := by
  have h := congrArg (aeval (xn p (m + 1))) (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  rw [map_mul, aeval_xn_cyclotomic, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact IsUnit.of_pow_eq_one (sub_eq_zero.1 h.symm) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

theorem isUnit_yn (n : ℕ) : IsUnit (yn p n) := by
  have hq : IsUnit (qO p) := by
    refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
    rw [HahnSeries.single_mul_single]; simp
  have h : yn p n ^ (p ^ n) = Ideal.Quotient.mk (towerIdeal p n) (C (C (qO p))) := by
    rw [yn, ← map_pow, Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)
  have h2 : IsUnit (yn p n ^ (p ^ n)) := h ▸ ((hq.map _).map _).map _
  exact (isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).1 h2

theorem derivative_cyclotomic_mul (m : ℕ) :
    aeval (xn p (m + 1)) (derivative (cyclotomic (p ^ (m + 1)) (O0 p))) * (xn p (m + 1) ^ p ^ m - 1) =
      (p : On p (m + 1)) ^ (m + 1) * xn p (m + 1) ^ (p ^ (m + 1) - 1) := by
  have h := congrArg (fun f => aeval (xn p (m + 1)) (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, map_add (f := _), map_mul, aeval_xn_cyclotomic, zero_mul, add_zero] at h
  simpa [derivative_X_pow] using h

end GlobalTheory.K5.DlogUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondDiagMulEqMulOfDvdLowerLeftGamma1InterGamm
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem dia_diag_mul_of_dvd_lowerLeft : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, mat σ * dg q 1 * mat γ = mat γ' * (mat σ * dg q 1) := by
  intro N l q σ γ hq hnd hσ hγ hc
  obtain ⟨u, hu⟩ := hc
  have hcop : Nat.Coprime q (N * l) := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  have hcN : IsCoprime (N : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_right_right hcop).symm
  have hcl : IsCoprime (l : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_left_right hcop).symm
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨ha, hd, hcN'⟩ := (Gamma1_mem N γ).1 h1
  have hcl' := Gamma0_mem.1 h0
  have hu' : (γ 1 0 : ℤ) = q * u := hu
  have huN : (u : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcN' ⊢
    rw [hu'] at hcN'
    exact hcN.dvd_of_dvd_mul_left hcN'
  have hul : (u : ZMod l) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcl' ⊢
    rw [hu'] at hcl'
    exact hcl.dvd_of_dvd_mul_left hcl'
  have hs : ((N * l : ℕ) : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hsN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hs)
  have hsl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hs)
  have dσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.det_coe; rwa [Matrix.det_fin_two] at this
  have dγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have dσN : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) dσ
    push_cast at this
    rw [hsN] at this
    simpa using this
  refine ⟨⟨!![(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 1 1 - (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 1 0,
      -(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 0 1 + (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 0 0;
      (σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 1 1 - (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 1 0,
      -(σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 0 1 + (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 0 0], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    rw [hu'] at dγ
    linear_combination (σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 + 1) * (γ 0 0 * γ 1 1 - γ 0 1 * (q * u)) * dσ + dγ
  · refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩
    · simp [hsN, huN, ha, hd, dσN]
    · simp [hsN, huN, ha, hd, mul_comm, dσN]
    · simp [hsN, huN]
    · simp [hsl, hul]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two, hu']
    · linear_combination (-(q : ℤ) * (σ 0 0 * γ 0 0 + σ 0 1 * u)) * dσ
    · linear_combination (-(σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1)) * dσ
    · linear_combination (-(q : ℤ) * (σ 1 0 * γ 0 0 + σ 1 1 * u)) * dσ
    · linear_combination (-(σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1)) * dσ

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondDiagMulEqMulUpperTriangularOfNotDvdLowerL
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HkInvFin

theorem sigma_dg_mul_eq : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ →
    γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      mat σ * dg q 1 * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  intro N l q σ γ hq _ hσ hγ hc
  haveI := Fact.mk hq
  have hdetγ : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * mat γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hdetσ : mat σ 0 0 * mat σ 1 1 - mat σ 0 1 * mat σ 1 0 = 1 := by
    have := σ.2; rwa [Matrix.det_fin_two] at this
  have hcq : ((mat γ 1 0 : ℤ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hdiv : (q : ℤ) ∣ mat γ 1 1 - mat γ 1 0 *
      (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_comm ((mat γ 1 1 : ℤ) : ZMod q), ← mul_assoc,
      mul_inv_cancel₀ hcq, one_mul, sub_self]
  obtain ⟨x, hx⟩ := hdiv
  set j' : ℕ := (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val with hj'
  have hjlt : j' < q := ZMod.val_lt _
  let δ : Matrix (Fin 2) (Fin 2) ℤ := !![q * mat γ 0 0, mat γ 0 1 - mat γ 0 0 * j'; mat γ 1 0, x]
  have hdetδ : δ.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdetγ - mat γ 0 0 * hx
  let γ' : SL(2, ℤ) := ⟨mat σ * δ, by rw [Matrix.det_mul, hdetδ, σ.2, one_mul]⟩
  have hlev := hγ
  rw [GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem] at hlev
  obtain ⟨⟨ha, hd, hcN⟩, hcl⟩ := hlev
  obtain ⟨hs10, hs11⟩ := hσ
  have hs10' : ((N * l : ℕ) : ℤ) ∣ mat σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hs10
  have hsN : ((mat σ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_right _ _) hs10'
  have hsl : ((mat σ 1 0 : ℤ) : ZMod l) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_left _ _) hs10'
  refine ⟨j', hjlt, γ', ?_, ?_⟩
  · have e00 : γ'.1 0 0 = mat σ 0 0 * (q * mat γ 0 0) + mat σ 0 1 * mat γ 1 0 := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have e10 : γ'.1 1 0 = mat σ 1 0 * (q * mat γ 0 0) + mat σ 1 1 * mat γ 1 0 := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have e11 : γ'.1 1 1 = mat σ 1 0 * (mat γ 0 1 - mat γ 0 0 * j') + mat σ 1 1 * x := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have hxN := congrArg (Int.cast : ℤ → ZMod N) hx
    have hdN := congrArg (Int.cast : ℤ → ZMod N) hdetσ
    have ha' : ((mat γ 0 0 : ℤ) : ZMod N) = 1 := ha
    have hd' : ((mat γ 1 1 : ℤ) : ZMod N) = 1 := hd
    have hcN' : ((mat γ 1 0 : ℤ) : ZMod N) = 0 := hcN
    have hcl' : ((mat γ 1 0 : ℤ) : ZMod l) = 0 := hcl
    have h11 : ((mat σ 1 1 : ℤ) : ZMod N) = (q : ZMod N) := by
      have : ((mat σ 1 1 : ℤ) : ZMod N) = ((q : ℤ) : ZMod N) := hs11
      simpa using this
    push_cast at hxN hdN
    rw [hd', hcN'] at hxN
    rw [hsN, h11] at hdN
    rw [GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show ((γ'.1 0 0 : ℤ) : ZMod N) = 1
      rw [e00]; push_cast; rw [ha', hcN']; linear_combination hdN
    · show ((γ'.1 1 1 : ℤ) : ZMod N) = 1
      rw [e11]; push_cast; rw [hsN, h11]; linear_combination -hxN
    · show ((γ'.1 1 0 : ℤ) : ZMod N) = 0
      rw [e10]; push_cast; rw [hsN, hcN']; ring
    · show ((γ'.1 1 0 : ℤ) : ZMod l) = 0
      rw [e10]; push_cast; rw [hsl, hcl']; ring
  · show mat σ * dg q 1 * mat γ = (mat σ * δ) * _
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, δ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hx | ring

end GlobalTheory.HkInvFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondGenEigenEigen
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SsD

theorem toGL_mat (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  unfold toGL
  rw [dite_eq_right h]
  ext i j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, mat]

theorem DdF_eq (k : ℤ) (σ : SL(2, ℤ)) (F : ℍ → ℂ) : DdF k σ F = F ∣[k] σ := by
  simp [DdF, hkF, toGL_mat, ModularForm.SL_slash]

theorem exists_pow_mem {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] (a : G) :
    ∃ m, 0 < m ∧ a ^ m ∈ H := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (QuotientGroup.mk (a ^ n) : G ⧸ H))
  have h' : (a ^ i)⁻¹ * a ^ j ∈ H := QuotientGroup.eq.mp h
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : a ^ (j - i) = (a ^ i)⁻¹ * a ^ j := by
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rwa [e]
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : a ^ (i - j) = (a ^ j)⁻¹ * a ^ i := by
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e]
    simpa [mul_inv_rev] using H.inv_mem h'

theorem eigen_of_pow_fix {V : Type*} [AddCommGroup V] [Module ℂ V] (D : Module.End ℂ V) {m : ℕ}
    (hm : 0 < m) (v : V) (c : ℂ) (n : ℕ) (h1 : (D ^ m) v = v)
    (h2 : ((D - c • LinearMap.id : Module.End ℂ V) ^ n) v = 0) : D v = c • v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h2
    simp [h2]
  set p : ℂ[X] := X ^ m - C 1
  set q : ℂ[X] := (X - C c) ^ n
  have hp : aeval D p v = 0 := by simp [p, h1]
  have hq : aeval D q v = 0 := by
    simpa [q, Module.algebraMap_end_eq_smul_id] using h2
  have hsq : Squarefree p :=
    (separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).squarefree
  have hg : aeval D (EuclideanDomain.gcd p q) v = 0 := by
    rw [EuclideanDomain.gcd_eq_gcd_ab p q, mul_comm p, mul_comm q, map_add (f := _), map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp, hq, map_zero, map_zero,
      add_zero]
  have hgd : EuclideanDomain.gcd p q ∣ X - C c := by
    exact (hsq.squarefree_of_dvd (EuclideanDomain.gcd_dvd_left p q)).dvd_pow_iff_dvd hn.ne' |>.mp
      (EuclideanDomain.gcd_dvd_right p q)
  obtain ⟨r, hr⟩ := hgd
  have : aeval D (X - C c) v = 0 := by
    rw [hr, mul_comm, map_mul, Module.End.mul_apply, hg, map_zero]
  simpa [sub_eq_zero, Module.algebraMap_end_eq_smul_id] using this

noncomputable def slashEnd (k : ℤ) (σ : SL(2, ℤ)) : Module.End ℂ (ℍ → ℂ) where
  toFun F := F ∣[k] σ
  map_add' F G := SlashAction.add_slash _ _ _ _
  map_smul' c F := by simp [ModularForm.SL_smul_slash]

theorem slashEnd_pow (k : ℤ) (σ : SL(2, ℤ)) (j : ℕ) (F : ℍ → ℂ) :
    (slashEnd k σ ^ j) F = F ∣[k] (σ ^ j) := by
  induction j generalizing F with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', SlashAction.slash_mul]
    rfl

end GlobalTheory.HeckeFamilyMatrices.SsD

namespace GlobalTheory.HeckeFamilyMatrices


open GlobalTheory.HeckeFamilyMatrices.SsD in
theorem diamond_genEigen_eigen : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
  ∀ (f : ModularForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => DdF (k : ℤ) σ F - c • F)^[n] ⇑f = 0 → DdF (k : ℤ) σ ⇑f = c • ⇑f := by
  intro N l k hN hl _ _ d σ _ f c n hn
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  obtain ⟨m, hm, hmem⟩ := exists_pow_mem (Lev N l) σ
  have hfix : (slashEnd (k : ℤ) σ ^ m) ⇑f = ⇑f := by
    rw [slashEnd_pow]
    exact SlashInvariantForm.slash_action_eqn f _ ⟨_, hmem, rfl⟩
  have hE : ⇑(slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) = fun F => DdF (k : ℤ) σ F - c • F := by
    funext F
    simp [slashEnd, DdF_eq]
  have h2 : ((slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) ^ n) ⇑f = 0 := by
    rw [Module.End.pow_apply, hE]
    exact hn
  have := eigen_of_pow_fix _ hm _ c n hfix h2
  simpa [slashEnd, DdF_eq] using this

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixNormalizesGammaOneGammaZeroLevel
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem diam_conj_mem (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) (hσ : IsDiam N l d σ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Lev N l) : σ * γ * σ⁻¹ ∈ Lev N l := by
  obtain ⟨hσ0, -⟩ := hσ
  rw [Lev, Subgroup.mem_inf] at hγ ⊢
  obtain ⟨hγ1, hγ0⟩ := hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hσ0
  have hσl : σ ∈ CongruenceSubgroup.Gamma0 l := by
    rw [CongruenceSubgroup.Gamma0_mem]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ0 ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro_left N rfl) hσ0
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ0 ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro l rfl) hσ0
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, h10⟩ := hγ1
    have hdet := σ.2
    rw [Matrix.det_fin_two] at hdet
    have hdet' : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) - ((σ 0 1 : ℤ) : ZMod N) * ((σ 1 0 : ℤ) : ZMod N) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul, Int.cast_neg]
    set a : ZMod N := ((σ 0 0 : ℤ) : ZMod N)
    set b : ZMod N := ((σ 0 1 : ℤ) : ZMod N)
    set c : ZMod N := ((σ 1 0 : ℤ) : ZMod N)
    set e : ZMod N := ((σ 1 1 : ℤ) : ZMod N)
    set p : ZMod N := ((γ 0 0 : ℤ) : ZMod N)
    set q : ZMod N := ((γ 0 1 : ℤ) : ZMod N)
    set r : ZMod N := ((γ 1 0 : ℤ) : ZMod N)
    set s : ZMod N := ((γ 1 1 : ℤ) : ZMod N)
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hdet' + a * e * h00 + b * e * h10 - a * q * hσN - b * c * h11
    · linear_combination hdet' + a * e * h11 - b * c * h00 - b * e * h10 + a * q * hσN
    · linear_combination e * p * hσN + e * e * h10 - c * q * hσN - e * s * hσN
  · exact (CongruenceSubgroup.Gamma0 l).mul_mem ((CongruenceSubgroup.Gamma0 l).mul_mem hσl hγ0)
      ((CongruenceSubgroup.Gamma0 l).inv_mem hσl)

theorem diam_normalises_lev : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  intro N l d σ hσ γ
  refine ⟨⟨σ * (γ : SL(2, ℤ)) * σ⁻¹, diam_conj_mem N l d σ hσ γ γ.2⟩, ?_⟩
  simp only [mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentFiniteOfTriangularSignedIndicatorsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_finite_of_triangular_signed_indicators : ∀ (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ))), (∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧ ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) → Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  first | exact @GlobalTheory.LaurentFinite.finite_of_triangular | exact GlobalTheory.LaurentFinite.finite_of_triangular | (intros; apply GlobalTheory.LaurentFinite.finite_of_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow : ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω), 0 < N → ℓ ≠ 0 → A.valuation ℓ < 1 → A.valuation π ^ N = A.valuation ℓ → (∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k) → (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A → ∀ i < N, c i ∈ A := by
  first | exact @GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | exact GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | (intros; apply GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow <;> assumption)
end

