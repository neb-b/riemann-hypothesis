module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOfRedEqZero
section
open GlobalTheory.Col PowerSeries

noncomputable section
namespace GlobalTheory.Col.NormFrob

theorem ringHom_ext_of_poly {R S : Type} [CommRing R] [CommRing S] (f g : PowerSeries R →+* PowerSeries S)
    (hfg : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom)
    (hf : X ∣ f X) (hg : X ∣ g X) : f = g := by
  ext1 h
  ext n
  set P : Polynomial R := trunc (n + 1) h
  have hd : X ^ (n + 1) ∣ h - (P : PowerSeries R) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [P, Polynomial.coeff_coe, coeff_trunc, hm]
  obtain ⟨q, hq⟩ := hd
  have hh : h = (P : PowerSeries R) + X ^ (n + 1) * q := by rw [← hq]; ring
  have hP : f (P : PowerSeries R) = g (P : PowerSeries R) := by
    have := congrArg (fun F => F P) hfg
    simpa using this
  have key : ∀ F : PowerSeries R →+* PowerSeries S, X ∣ F X → coeff n (F (X ^ (n + 1) * q)) = 0 := by
    intro F hF
    have : X ^ (n + 1) ∣ F (X ^ (n + 1) * q) := by
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hF _) _
    exact (X_pow_dvd_iff.1 this) n (Nat.lt_succ_self n)
  rw [hh, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hP, key f hf, key g hg]

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev red : PowerSeries R →+* PowerSeries (R ⧸ Ideal.span {(p : R)}) :=
  PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))

theorem exists_of_red_eq_zero (D : PowerSeries R) (hD : red p D = 0) :
    ∃ g : PowerSeries R, D = (p : PowerSeries R) * g := by
  have hc : ∀ n, ∃ c : R, coeff n D = (p : R) * c := by
    intro n
    have h1 : coeff n (red p D) = 0 := by rw [hD, map_zero]
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [hc n, show (p : PowerSeries R) = C (p : R) from (map_natCast C p).symm, coeff_C_mul, coeff_mk]

theorem red_pow_eq (σ : R ≃+* R) (hfl : FrobLift R p σ) (h : PowerSeries R) :
    red p h ^ p = red p (phi (R := R) p hp.out.pos (smap σ h)) := by
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  have hX1 : ((frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p)) X = X ^ p := by
    simp [frobenius_def]
  have hX2 : ((red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ))) X = X ^ p := by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smap, map_X, phi_X, map_sub, map_pow,
      map_add, map_one]
    rw [add_pow_char, one_pow, add_sub_cancel_left]
  suffices H : (frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p) =
      (red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ)) by
    have := congrArg (fun F => F h) H
    simpa [frobenius_def] using this
  apply ringHom_ext_of_poly
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, smap, map_C, frobenius_def, ← map_pow]
      have h1 : (phi (R := R) p hp.out.pos) (C (σ a)) = C (σ a) := (phi (R := R) p hp.out.pos).commutes (σ a)
      have h2 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ a) = (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) ^ p := by
        rw [← map_pow]; exact Ideal.Quotient.eq.2 (hfl.frob a)
      rw [h1, map_C, h2, map_pow]
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      rw [RingHom.comp_apply] at hX1 hX2
      rw [hX1, RingHom.comp_apply] at *
      rw [hX2]
  · rw [hX1]; exact dvd_pow_self _ hp.out.ne_zero
  · rw [hX2]; exact dvd_pow_self _ hp.out.ne_zero

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

theorem normOp_eq_smap_add (σ : R ≃+* R) (hfl : FrobLift R p σ)
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule)) (h : PowerSeries R) :
    ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  haveI := hfl.dom
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hfl.prime.ne_zero).2 hfl.prime
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule
  haveI : Module.Free (PowerSeries R) (PowerSeries R) := Module.Free.of_basis b
  have hrank : Module.finrank (PowerSeries R) (PowerSeries R) = p := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hred0 : red p (p : PowerSeries R) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p

  have hcong : ∀ x g : PowerSeries R,
      red p (Algebra.norm (PowerSeries R) (x + (p : PowerSeries R) * g)) = red p (Algebra.norm (PowerSeries R) x) := by
    intro x g
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det, RingHom.map_det, map_add (f := _),
      map_mul, map_natCast, map_add, map_mul, map_natCast]
    have hz : ((p : ℕ) : Matrix (Fin p) (Fin p) (PowerSeries (R ⧸ Ideal.span {(p : R)}))) = 0 := by
      ext i j
      rw [Matrix.natCast_apply]
      split_ifs <;> simp [CharP.cast_eq_zero]
    rw [hz, zero_mul, add_zero]
  obtain ⟨g, hg⟩ := exists_of_red_eq_zero p (h ^ p - phi (R := R) p hp.out.pos (smap σ h)) (by
    rw [map_sub, map_pow, red_pow_eq p σ hfl h, sub_self])
  have hpow : red p (normOp p h) ^ p = red p (smap σ h) ^ p := by
    have e1 : h ^ p = phi (R := R) p hp.out.pos (smap σ h) + (p : PowerSeries R) * g := by rw [← hg]; ring
    have e2 : Algebra.norm (PowerSeries R) (phi (R := R) p hp.out.pos (smap σ h)) = (smap σ h) ^ p := by
      have := Algebra.norm_algebraMap (S := PowerSeries R) (smap σ h)
      rw [hrank] at this; exact this
    unfold normOp
    rw [← map_pow, ← map_pow (Algebra.norm _), e1, hcong, e2, map_pow]
  have hinj := frobenius_inj (PowerSeries (R ⧸ Ideal.span {(p : R)})) p
  have heq : red p (normOp p h) = red p (smap σ h) := hinj (by simpa [frobenius_def] using hpow)
  obtain ⟨r, hr⟩ := exists_of_red_eq_zero p (normOp p h - smap σ h) (by rw [map_sub, heq, sub_self])
  exact ⟨r, by rw [← hr]; ring⟩

end GlobalTheory.Col.NormFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMul
section
noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_inv_qParam_pow_mul {M a : ℕ} (ha : a < M) {g : ℍ → ℂ}
    (hg : g =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    Tendsto (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹ * g τ) atImInfty (𝓝 0) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_le a).trans_lt ha
  have haM : (a : ℝ) < M := by exact_mod_cast ha
  have h1 : (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (2 * Real.pi * τ.im * a / M) := by
    refine Asymptotics.IsBigO.of_norm_le fun τ => le_of_eq ?_
    rw [norm_inv, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, ← Real.exp_neg, coe_im]
    congr 1; ring
  refine (h1.mul hg).trans_tendsto ?_
  have hr : -2 * Real.pi * (1 - a / M) < 0 := by
    have : (a : ℝ) / M < 1 := (div_lt_one hM).2 haM
    have := Real.pi_pos
    nlinarith
  have h2 : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  refine (Real.tendsto_exp_atBot.comp (h2.const_mul_atTop_of_neg hr)).congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_add]; congr 1; ring

theorem sum_mul_co_eq {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} {w : Fin r → ℤ}
    {F : Fin r → ℍ → ℂ} (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (l : Fin r) {a : ℕ} (ha : a < M) (c : Fin r → ℂ)
    (hc : ∀ i, (leadM M s w F).mulVec c i = co M (w l) (F l) (s i) a) (x : SL(2, ℤ)) {n : ℕ} (hn : n < M) :
    ∑ j, c j * co M (w j) (F j) x n = if n = a then co M (w l) (F l) x a else 0 := by
  have H := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  rw [← sub_eq_zero]
  refine _root_.GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero M Γ r s
    (fun x n => ∑ j, c j * co M (w j) (F j) x n - if n = a then co M (w l) (F l) x a else 0)
    hM hs ?_ ?_ ?_ ?_ x n hn
  · intro x n
    simp only [fun j => (H j).1, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · split_ifs with h
      · rw [h]
      · simp
  · intro γ hγ x n
    simp only [fun j => (H j).2.1 γ hγ]
  · intro x n
    simp only [fun j => (H j).2.2 (hF j).1, mul_neg, Finset.sum_neg_distrib]
    split_ifs <;> ring
  · intro i
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range M) a, if_pos (Finset.mem_range.2 ha),
      ← hc i, Finset.sum_comm, sub_eq_zero]
    simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, mul_comm]

theorem exists_tendsto_evM_mul (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (leadM M s w F).det ≠ 0) :
    ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ,
      Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧
        Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  set c : Fin r → ℕ → Fin r → ℂ := fun l a =>
    (leadM M s w F)⁻¹.mulVec fun i => co M (w l) (F l) (s i) a with hcdef
  have hc : ∀ l a i, (leadM M s w F).mulVec (c l a) i = co M (w l) (F l) (s i) a := by
    intro l a i
    simp only [hcdef]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  set t : ℍ → ℂ := fun τ => Function.Periodic.qParam (M : ℝ) (τ : ℂ) with ht
  have ht0 : ∀ τ, t τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  refine ⟨fun τ => Matrix.of fun j l => ∑ a ∈ Finset.range M, c l a j * (t τ ^ a)⁻¹, ?_, ?_⟩
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun l => ?_
    have hlim : Tendsto (fun τ : ℍ => leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j *
        ((t τ ^ a)⁻¹ * ((F j ∣[w j] s i) τ -
          ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n))) atImInfty
        (𝓝 (leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j * 0)) := by
      refine tendsto_const_nhds.add (tendsto_finsetSum _ fun a ha => tendsto_finsetSum _ fun j _ => ?_)
      exact (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha)
        (_root_.GlobalTheory.OddFrame.slash_sub_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 (s i))).const_mul _
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.mul_apply, evM, leadM, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    have key : ∑ j, c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n =
        co M (w l) (F l) (s i) a * t τ ^ a := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ n ∈ Finset.range M, ∑ j, c l a j * (co M (w j) (F j) (s i) n * t τ ^ n) =
          if n = a then co M (w l) (F l) (s i) a * t τ ^ a else 0 := by
        intro n hn
        simp only [← mul_assoc, ← Finset.sum_mul]
        rw [sum_mul_co_eq hM hΓ hs hF l ha' (c l a) (hc l a) (s i) (Finset.mem_range.1 hn)]
        split_ifs with h
        · rw [h]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range M) a, if_pos ha]
    have hta : t τ ^ a ≠ 0 := pow_ne_zero _ (ht0 τ)
    have e : co M (w l) (F l) (s i) a =
        ∑ j, (t τ ^ a)⁻¹ * (c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n) := by
      rw [← Finset.mul_sum, key]; field_simp
    rw [e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun l => ?_
    have hΔ : ModularForm.discriminant =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      simpa [CuspForm.coe_discriminant] using
        CuspFormClass.exp_decay_atImInfty CuspForm.discriminant one_pos one_mem_strictPeriods_SL
    have hlim : Tendsto (fun τ : ℍ => ∑ a ∈ Finset.range M, c l a j *
        ((t τ ^ a)⁻¹ * ModularForm.discriminant τ)) atImInfty (𝓝 (∑ a ∈ Finset.range M, c l a j * 0)) :=
      tendsto_finsetSum _ fun a ha =>
        (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha) hΔ).const_mul _
    simp only [mul_zero, Finset.sum_const_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.OddFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem finiteDimensional_of_Gamma_le :
    ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro M Γ k hM hle
  exact GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm Γ k (finiteIndex_of_Gamma_le hM hle)

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAddStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 2 = t ^ 3 → Subgroup.closure ({s, t} : Set G) = ⊤ → FiniteDimensional ℂ E → FiniteDimensional ℂ (relThree Γ ρ t) → FiniteDimensional ℂ (extn Γ ρ s) ∧ Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtensionStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 4 = 1 → FiniteDimensional ℂ (extn Γ ρ s) → FiniteDimensional ℂ (cocyc Γ ρ) ∧ Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s)) ≤ Module.finrank ℂ (extn Γ ρ s) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeActionStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ), Γ.FiniteIndex → FiniteDimensional ℂ E → 0 < m → g ^ m = 1 → A ^ m = 1 → (∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) → FiniteDimensional ℂ (twInv Γ g A) ∧ Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisDenseTauPowMulFixingQRootsStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricGalois_dense_tau_pow_mul_fixing_qRoots : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ g ∈ Ggeo (p := p) Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo (p := p) Ω ⊓ ⨅ n, Gn T n,
    ∀ x ∈ S, (τ ^ s * h) x = g x := by
  exact @GlobalTheory.K5.Dense.dense_tau_pow_mul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangular
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

theorem qD_sub (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ) (hk : 0 < a / d)
    (φ : HahnSeries ℚ Ω) :
    qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  have hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r :=
    fun _ _ _ => rfl
  have hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r := by
    intro ψ r
    rw [scale, dite_eq_left hk]
    exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)
  rw [HahnSeries.C_mul_eq_smul]
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = a / d * r := ⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩
  rw [HahnSeries.coeff_smul]
  simp only [qD, sub]
  rw [hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CyclotomicQExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.HeckeInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_pre_exp [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ∃ ω : Ω, ε ω = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hn : x.den ≠ 0 := x.den_nz
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩
  haveI : NeZero x.den := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * hx
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eps_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_pre_exp ε x)

theorem sub_coeff (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (j : ℚ) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε 1 j (q : ℚ) φ).coeff s = eOm ε (s * j) * φ.coeff ((q : ℚ) * s) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h : (0 : ℚ) < 1 / (q : ℚ) := by positivity
  unfold sub scale
  rw [dite_eq_left h]
  have e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s := by
    simp only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  have key := HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding)
    (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)
  rw [e] at key
  rw [key]
  simp only [cm]
  congr 2
  field_simp

theorem sum_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (s : ℚ) (hs : ((q : ℚ) * s).den = 1) :
    ∑ j ∈ Finset.range q, eOm ε (s * (j : ℚ)) = if s.den = 1 then (q : Ω) else 0 := by
  apply ε.injective
  have hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j := by
    intro j
    rw [eps_eOm, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hz]
  split_ifs with hd
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1 := by
      have : (s : ℂ) = ((s.num : ℤ) : ℂ) := by
        have := Rat.coe_int_num_of_den_eq_one hd
        rw [← this]; push_cast; rfl
      rw [this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [h1]
  · have hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hsn : (s : ℂ) = (n : ℂ) := by
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination hn
      have : s = (n : ℚ) := by exact_mod_cast hsn
      exact hd (by rw [this]; rfl)
    have hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ) := (Rat.coe_int_num_of_den_eq_one hs).symm
      have hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ) := by exact_mod_cast hx
      rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        rw [← hx']; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]

theorem hq_coeff_of_int : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
    (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ,
      (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  intro Ω _ _ _ ε q hq0 φ hφ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  unfold hq
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]
  simp only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]
  rw [← Finset.sum_mul]
  by_cases hc : φ.coeff ((q : ℚ) * s) = 0
  · simp [hc]
  · rw [GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]
    have hqne : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
    split_ifs
    · field_simp
    · simp

end GlobalTheory.HeckeInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) → IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  first | exact @GlobalTheory.K5.PDiv.pdiv | exact GlobalTheory.K5.PDiv.pdiv | (intros; apply GlobalTheory.K5.PDiv.pdiv <;> assumption)
end

