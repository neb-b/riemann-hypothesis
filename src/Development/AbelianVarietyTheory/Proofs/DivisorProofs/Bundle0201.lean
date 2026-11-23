module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0148

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfLocalRetractionsModMaximalIdealPow
section
open IsLocalRing

namespace GlobalTheory

section

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

theorem isLocalHom_mk_maximalIdeal_pow_succ (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hu
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))),
    Ideal.Quotient.eq] at hc
  have h1 : a * c - 1 ∈ maximalIdeal A := Ideal.pow_le_self n.succ_ne_zero hc
  have h2 : a * c ∈ maximalIdeal A := Ideal.mul_mem_right _ _ hu
  have h3 : (1 : A) ∈ maximalIdeal A := by simpa using sub_mem h2 h1
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h3)

theorem quotientMap_pow_bijective_of_retraction (φ : A →+* B) [IsLocalHom φ] (n : ℕ)
    (hle : maximalIdeal A ^ (n + 1) ≤ (maximalIdeal B ^ (n + 1)).comap φ)
    (ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1)) (hψ : ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ →
      g₁.comp φ = g₂.comp φ → g₁ = g₂) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle) := by
  haveI hA := isLocalHom_mk_maximalIdeal_pow_succ (A := A) n
  haveI hB := isLocalHom_mk_maximalIdeal_pow_succ (A := B) n
  have hψφ : ∀ a, ψ (φ a) = Ideal.Quotient.mk _ a := fun a => RingHom.congr_fun hψ a
  have hsurj : Function.Surjective ψ := fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨φ a, hψφ a⟩
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self n.succ_ne_zero))
  haveI hψl : IsLocalHom ψ := IsLocalHom.of_surjective ψ hsurj
  haveI hφl : IsLocalHom (Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk] at hx
    exact (IsUnit.of_map φ _ (IsUnit.of_map (Ideal.Quotient.mk _) _ hx)).map _
  have key := huniq (Ideal.Quotient.mk _)
    ((Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle).comp ψ) hB inferInstance (by
      ext a
      simp [hψφ])
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have h1 : maximalIdeal B ≤ ((maximalIdeal A).map
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))).comap ψ := by
      intro b hb
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (ψ b)
      rw [Ideal.mem_comap, ← hc]
      refine Ideal.mem_map_of_mem _ fun hu => hb ?_
      exact IsUnit.of_map ψ _ (hc ▸ hu.map _)
    have h2 := pow_le_comap_pow_of_le h1 (n + 1) hx
    rwa [Ideal.mem_comap, ← Ideal.map_pow, Ideal.map_quotient_self, hψφ, Ideal.mem_bot] at h2
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨ψ b, (RingHom.congr_fun key b).symm⟩

end

theorem flat_of_retractions_mod_pow {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hex : ∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ →
      IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal B).comap φ := fun a ha => map_nonunit φ a ha
  have hbij : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap (maximalIdeal B ^ n) φ (pow_le_comap_pow_of_le hle n)) := by
    intro n
    cases n with
    | zero =>
      haveI : Subsingleton (A ⧸ maximalIdeal A ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      haveI : Subsingleton (B ⧸ maximalIdeal B ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    | succ n =>
      obtain ⟨ψ, hψ⟩ := hex n
      exact quotientMap_pow_bijective_of_retraction φ n _ ψ hψ (huniq n)
  refine ringHom_flat_of_flat_quotientMap_pow φ ?_ (maximalIdeal_le_jacobson _)
    (pow_le_comap_pow_of_le hle) fun n => RingHom.Flat.of_bijective (hbij n)
  refine le_antisymm (Ideal.map_le_of_le_comap hle)
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) fun y hy => ?_)
  obtain ⟨x, hx⟩ := (hbij 2).2 (Ideal.Quotient.mk _ y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
  have hxm : x ∈ maximalIdeal A := by
    have : φ x ∈ maximalIdeal B := by
      simpa using add_mem (Ideal.pow_le_self two_ne_zero hx) hy
    exact fun hu => this (hu.map φ)
  rw [show y = φ x - (φ x - y) by ring]
  refine sub_mem (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hxm)) (Submodule.mem_sup_right ?_)
  rwa [smul_eq_mul, ← pow_two]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleAwayOfEtaleOffMaximalIdeal
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleAway

theorem isEtaleAt_of_formallyEtale_baseChange (S B : Type) [CommRing S] [CommRing B] [Algebra S B]
    (Q : Ideal B) [Q.IsPrime]
    (h : Algebra.FormallyEtale (Localization.AtPrime (Q.under S))
      (TensorProduct S (Localization.AtPrime (Q.under S)) B)) :
    Algebra.FormallyEtale S (Localization.AtPrime Q) := by
  set P : Ideal S := Q.under S with hP
  let M : Submonoid B := Algebra.algebraMapSubmonoid B P.primeCompl
  let Bp := Localization M
  have hpush : Algebra.IsPushout S (Localization.AtPrime P) B Bp :=
    (Algebra.isPushout_of_isLocalization P.primeCompl (Localization.AtPrime P) B Bp).symm
  let e : Localization.AtPrime P ⊗[S] B ≃ₐ[Localization.AtPrime P] Bp := hpush.equiv
  have h1 : Algebra.FormallyEtale (Localization.AtPrime P) Bp := Algebra.FormallyEtale.of_equiv e
  have h0 : Algebra.FormallyEtale S (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have h2 : Algebra.FormallyEtale S Bp := Algebra.FormallyEtale.comp S (Localization.AtPrime P) Bp
  have hle : M ≤ Q.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [P, Ideal.under] using hx
  letI : Algebra Bp (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Bp (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsScalarTower B Bp (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Bp (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Bp Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le Bp (Localization.AtPrime Q) M Q.primeCompl hle
  have h3 : Algebra.FormallyEtale Bp (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid Bp Q.primeCompl)
  haveI : IsScalarTower S Bp (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun s => by
    rw [IsScalarTower.algebraMap_apply S B Bp, ← IsScalarTower.algebraMap_apply B Bp,
      ← IsScalarTower.algebraMap_apply S B])
  exact Algebra.FormallyEtale.comp S Bp (Localization.AtPrime Q)

end GlobalTheory.EtaleAway

namespace GlobalTheory.EtaleAway

theorem formallyEtale_away : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A],
    (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
    ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g)
      (TensorProduct R (Localization.Away g) A) := by
  intro R _ _ _ A _ _ _ he g hg
  set S := Localization.Away g
  set B := S ⊗[R] A
  refine Algebra.etaleLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun Q => ?_)
  show Algebra.FormallyEtale S (Localization.AtPrime Q.asIdeal)
  apply isEtaleAt_of_formallyEtale_baseChange
  set P : Ideal S := Q.asIdeal.under S
  set q : Ideal R := P.under R with hq
  have hqm : q ≠ maximalIdeal R := by
    intro h
    have hgq : g ∈ q := h ▸ hg
    have : algebraMap R S g ∈ P := hgq
    exact (Ideal.IsPrime.ne_top inferInstance)
      (P.eq_top_of_isUnit_mem this (IsLocalization.Away.algebraMap_isUnit g))
  haveI := he q hqm
  haveI : P.LiesOver q := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime q] (Localization.AtPrime q ⊗[R] A)
      ≃ₐ[Localization.AtPrime P] Localization.AtPrime P ⊗[S] (S ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime q) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R S (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  haveI : Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[S] (S ⊗[R] A)) :=
    Algebra.Etale.of_equiv e
  infer_instance

end GlobalTheory.EtaleAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

open Set Filter Topology

theorem norm_pow_mul_cexp_neg (n : ℕ) (r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ n * Complex.exp (-(r * t))‖ = t ^ (n : ℝ) * Real.exp (-r.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp

theorem integrableOn_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]

theorem tendsto_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]

theorem integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp [hr0]
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2 <;> simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem fourier_phi1_eq_factorial_mul_zpow : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ),
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  intro k hk hke w hw x
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hwx : w - (x : ℂ) ≠ 0 := by
    intro h
    apply hw
    have := congrArg Complex.im h
    simpa using this
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [Nat.add_sub_cancel]
  rw [Real.fourier_real_eq_integral_exp_smul]
  rcases hw.lt_or_gt with hneg | hpos
  · set r : ℂ := 2 * Real.pi * Complex.I * (w - x) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (-v) * x) * Complex.I) • phi1 (m + 1) w (-v)) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_neg hneg, SignType.coe_neg,
        SignType.coe_one, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos (by linarith), if_pos hv, abs_neg, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg (by linarith), if_neg hv, mul_zero]
    rw [← integral_neg_eq_self, e, integral_indicator measurableSet_Ioi,
      integral_pow_mul_cexp_neg m hr, hrdef, mul_pow, zpow_neg, zpow_natCast]
    field_simp
  · set r : ℂ := -(2 * Real.pi * Complex.I * (w - x)) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • phi1 (m + 1) w v) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_pos hpos,
        SignType.coe_one, one_mul, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos hv, if_pos hv, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [e, integral_indicator measurableSet_Ioi, integral_pow_mul_cexp_neg m hr, hrdef,
      hke.neg_pow, mul_pow, zpow_neg, zpow_natCast]
    field_simp

end GlobalTheory.LipschitzTR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetFourier

theorem star_eq_inv_of_pow_eq_one {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n = 1) :
    star w = w⁻¹ := by
  have h1 : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hn
  have h2 : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.inv_def, h2]; simp [Complex.star_def]

theorem geom_sum_root_of_unity {w : ℂ} {n : ℕ} (hw : w ^ n = 1) :
    ∑ a ∈ Finset.range n, w ^ a = if w = 1 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, hw]; simp

theorem fourier_coset_sums : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  intro G Γ _ _ _ _ φ s hs ζ hζ
  have hn0 : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  let u : ℂˣ := Units.mk0 ζ (hζ.ne_zero hn0)
  have hu : orderOf u ∣ orderOf s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hord]; ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]
    exact hζ.pow_eq_one
  let η₀ : Γ →* ℂˣ := monoidHomOfForallMemZpowers hs hu
  have hη₀s : η₀ s = u := monoidHomOfForallMemZpowers_apply_gen hs hu
  have hinj : Function.Injective η₀ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs t)
    rw [map_zpow, hη₀s] at ht
    have hk : ζ ^ k = 1 := by
      have := congrArg Units.val ht
      simpa [u, Units.val_zpow_eq_zpow_val] using this
    rw [hζ.zpow_eq_one_iff_dvd] at hk
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact hk
  let η : G ⋊[φ] Γ →* ℂˣ := η₀.comp rightHom
  have hηx : ∀ x, η x = η₀ x.right := fun x => rfl
  have hpow : ∀ x, (η x : ℂ) ^ Nat.card Γ = 1 := by
    intro x
    rw [hηx, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']; simp
  have hstar : ∀ x, star (η x : ℂ) = (η x : ℂ)⁻¹ := fun x => star_eq_inv_of_pow_eq_one hn0 (hpow x)
  have hone : ∀ x : G ⋊[φ] Γ, (η x : ℂ)⁻¹ = 1 ↔ x.right = 1 := by
    intro x
    rw [inv_eq_one, Units.val_eq_one, hηx, ← map_one η₀, hinj.eq_iff]
  have hzeta : ∀ x : G ⋊[φ] Γ, ζ * (η x : ℂ)⁻¹ = 1 ↔ x.right = s := by
    intro x
    have hne : (η x : ℂ) ≠ 0 := (η x).ne_zero
    rw [mul_inv_eq_one₀ hne, eq_comm, hηx]
    have : ζ = ((η₀ s : ℂˣ) : ℂ) := by rw [hη₀s]; rfl
    rw [this, Units.val_inj, hinj.eq_iff]
  refine ⟨η, fun g => by simp [η], by rw [show η (inr s) = η₀ s from by simp [η], hη₀s]; rfl, ?_⟩
  intro X Y
  haveI : Fintype G := Fintype.ofFinite G
  let e : G ⋊[φ] Γ ≃ G × Γ :=
    ⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  haveI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv (G × Γ) e.symm

  have key : ∀ (c : ℂ) (t : Γ), (∀ x : G ⋊[φ] Γ, c * (η x : ℂ)⁻¹ = 1 ↔ x.right = t) →
      c ^ Nat.card Γ = 1 →
      ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) =
        (Nat.card Γ : ℂ) * ∑ g : G, X ⟨g, t⟩ * star (Y ⟨g, t⟩) := by
    intro c t hct hc
    simp_rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ x : G ⋊[φ] Γ, ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * (X x * star (Y x * (η x : ℂ) ^ a))
        = X x * star (Y x) * (if x.right = t then (Nat.card Γ : ℂ) else 0) := by
      intro x
      have : ∀ a, c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (c * (η x : ℂ)⁻¹) ^ a := by
        intro a
        rw [star_mul', star_pow, hstar, mul_pow]; ring
      simp_rw [this]
      rw [← Finset.mul_sum, geom_sum_root_of_unity (by rw [mul_pow, inv_pow, hc, hpow, inv_one, one_mul])]
      simp only [hct]
    simp_rw [hterm]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [e, mul_comm]
  refine ⟨?_, ?_⟩
  · have := key 1 1 (fun x => by rw [one_mul]; exact hone x) (one_pow _)
    simp only [one_pow, one_mul] at this
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  · rw [key ζ s hzeta hζ.pow_eq_one, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    have : (inl g * inr s : G ⋊[φ] Γ) = ⟨g, s⟩ := by ext <;> simp
    rw [this]

end GlobalTheory.Shin.CosetFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobLiftLocalization
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem frobLift_localization :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add (f := _), map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add (f := _), map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponentialStatement
section
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first | exact @GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | exact GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | (intros; apply GlobalTheory.hasDerivAt_of_continuous_additive_to_mul <;> assumption)
end

