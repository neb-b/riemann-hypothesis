module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DApprox
section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S
open Classical ValuativeRel
open scoped TensorProduct

theorem resChar_memK {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) :
    ((Loc.resChar p : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem int_memK {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
    {Fp : Type} [Field Fp] [ValuativeRel Fp] (ι : K →+* Fp)
    (hval : ∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) (a : 𝓞 K) :
    ι (a : K) ∈ 𝒪[Fp] := by
  rw [Valuation.mem_integer_iff]
  have h := (hval (a : K) 1).mpr (by rw [map_one]; exact p.valuation_le_one a)
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation Fp)] at h
  simpa only [map_one] using h

theorem val_ell_lt {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
    {Fp : Type} [Field Fp] [ValuativeRel Fp] (ι : K →+* Fp)
    (hval : ∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) :
    valuation Fp ((Loc.resChar p : ℕ) : Fp) < 1 := by
  have hmem := resChar_memK p
  have h1 : p.valuation K ((Loc.resChar p : ℕ) : K) < 1 := by
    have h := (p.valuation_lt_one_iff_mem (K := K) ((Loc.resChar p : ℕ) : 𝓞 K)).mpr hmem
    simpa using h
  have h2 : ¬ (ι 1 ≤ᵥ ι ((Loc.resChar p : ℕ) : K)) := by
    rw [hval, map_one]
    exact not_le.mpr h1
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation Fp)] at h2
  simp only [map_one, map_natCast] at h2
  exact not_le.mp h2

theorem zp_memK {ℓ : ℕ} [Fact ℓ.Prime] {Fp : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp] (hc : Continuous (algebraMap ℚ_[ℓ] Fp))
    (x : ℤ_[ℓ]) : algebraMap ℚ_[ℓ] Fp (x : ℚ_[ℓ]) ∈ 𝒪[Fp] := by
  have hg : Continuous fun y : ℤ_[ℓ] => algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) :=
    hc.comp continuous_subtype_val
  have hcl : IsClosed {y : ℤ_[ℓ] | algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) ∈ 𝒪[Fp]} :=
    Valuation.isClosed_integer.preimage hg
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[ℓ]) ⊆ {y : ℤ_[ℓ] | algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) ∈ 𝒪[Fp]} := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq]
    push_cast
    exact natCast_mem _ k
  exact hcl.closure_subset_iff.mpr hsub (PadicInt.denseRange_natCast x)

theorem approx_core {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] {Fp : Type} [Field Fp]
    [CharZero Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp]
    (hS : PowSmall) (hc : Continuous (algebraMap ℚ_[ℓ] Fp)) (hfin : FiniteDimensional ℚ_[ℓ] Fp) (ι : K →+* Fp)
    (hsurj : Function.Surjective (piMap K ℓ Fp ι)) (hint : ∀ a : 𝓞 K, ι (a : K) ∈ 𝒪[Fp])
    (hℓ : valuation Fp (ℓ : Fp) < 1) (z : Fp) (hz : ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[ℓ] Fp (c * z)‖ ≤ 1)
    (k : ℕ) : ∃ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) ∧
      ∃ μ ∈ 𝒪[Fp], ι t = z + (ℓ : Fp) ^ k * μ := by
  have hπ1 : ∀ y : K, piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y := piMap_one_tmul K ℓ Fp ι
  let b := NumberField.integralBasis K
  let bd := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b
  have hdb : ∀ i j, Algebra.trace ℚ K (bd i * b j) = if j = i then 1 else 0 := by
    intro i j
    have := (Algebra.traceForm ℚ K).apply_dualBasis_left (traceForm_nondegenerate ℚ K) b i j
    rwa [Algebra.traceForm_apply] at this
  let BA := Algebra.TensorProduct.basis ℚ_[ℓ] bd
  have hBA : ∀ i, BA i = 1 ⊗ₜ bd i := fun i => Algebra.TensorProduct.basis_apply bd i
  let Bb := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hBb : ∀ i, Bb i = 1 ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  have : FiniteDimensional ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) := Module.Finite.of_basis BA
  have htb : ∀ i j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) ((1 ⊗ₜ bd i) * (1 ⊗ₜ b j)) =
      if j = i then 1 else 0 := by
    intro i j
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, hdb]
    split_ifs <;> simp
  have hnd : ∀ γ : ℚ_[ℓ] ⊗[ℚ] K,
      (∀ j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (γ * (1 ⊗ₜ b j)) = 0) → γ = 0 := by
    intro γ hγ
    have hexp := BA.sum_repr γ
    have hc0 : ∀ j, BA.repr γ j = 0 := by
      intro j
      have h := hγ j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hexp, Finset.sum_mul, map_sum] at h
      simpa only [smul_mul_assoc, map_smul, hBA, htb, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] using h
    rw [← hexp]
    simp [hc0]
  let φ : ℚ_[ℓ] ⊗[ℚ] K →ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
    (Algebra.trace ℚ_[ℓ] Fp).comp ((LinearMap.mulLeft ℚ_[ℓ] z).comp (piMap K ℓ Fp ι).toLinearMap)
  have hφ : ∀ x, φ x = Algebra.trace ℚ_[ℓ] Fp (z * piMap K ℓ Fp ι x) := fun x => rfl
  let β : ℚ_[ℓ] ⊗[ℚ] K := ∑ i, φ (1 ⊗ₜ b i) • (1 ⊗ₜ bd i)
  have hβ : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) = φ x := by
    have hL : (Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K)).comp (LinearMap.mulLeft ℚ_[ℓ] β) = φ := by
      apply Bb.ext
      intro j
      rw [hBb, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [β, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, htb, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro x
    exact congrArg (fun L => L x) hL
  have hker : ∀ x, piMap K ℓ Fp ι x = 0 → β * x = 0 := by
    intro x hx
    apply hnd
    intro j
    rw [mul_assoc, hβ, hφ, map_mul (piMap K ℓ Fp ι), hx, zero_mul, mul_zero, map_zero]
  have htr : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) =
      Algebra.trace ℚ_[ℓ] Fp (piMap K ℓ Fp ι β * piMap K ℓ Fp ι x) := by
    intro x
    rw [trace_of_ker (piMap K ℓ Fp ι) hsurj (β * x), map_mul]
    intro y hy
    rw [mul_comm β x, mul_assoc, hker y hy, mul_zero]
  have hπβ : piMap K ℓ Fp ι β = z := by
    by_contra hne
    have hd0 : piMap K ℓ Fp ι β - z ≠ 0 := sub_ne_zero.2 hne
    obtain ⟨x, hx⟩ := hsurj (piMap K ℓ Fp ι β - z)⁻¹
    have e1 : Algebra.trace ℚ_[ℓ] Fp ((piMap K ℓ Fp ι β - z) * piMap K ℓ Fp ι x) = 0 := by
      rw [sub_mul, map_sub, ← htr, hβ, hφ, sub_self]
    rw [hx, mul_inv_cancel₀ hd0, ← map_one (algebraMap ℚ_[ℓ] Fp), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one] at e1
    exact (Nat.cast_ne_zero.2 Module.finrank_pos.ne') e1
  have hzi : ∀ i, ‖φ (1 ⊗ₜ b i)‖ ≤ 1 := by
    intro i
    rw [hφ, hπ1, mul_comm]
    apply hz
    have hb : b i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) := NumberField.integralBasis_apply K i
    rw [hb]
    exact hint _
  choose N hN using fun i => hS Fp (ι (bd i)) (ℓ : Fp) hℓ
  let w : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ_[ℓ] := fun i => ⟨φ (1 ⊗ₜ b i), hzi i⟩
  let n : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℕ := fun i => PadicInt.appr (w i) (k + N i)
  have hsp : ∀ i, ∃ e : ℤ_[ℓ], e * (ℓ : ℤ_[ℓ]) ^ (k + N i) = w i - n i :=
    fun i => Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (k + N i) (w i))
  choose e he using hsp
  let t : K := ∑ i, (n i : ℚ) • bd i
  refine ⟨t, ?_, -(∑ i, algebraMap ℚ_[ℓ] Fp (e i : ℚ_[ℓ]) * ((ℓ : Fp) ^ N i * ι (bd i))), ?_, ?_⟩
  · have htj : ∀ j, Algebra.trace ℚ K (t * b j) = (n j : ℚ) := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [t, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hdb, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro a
    have ha : (a : K) = ∑ j, ((RingOfIntegers.basis K).repr a j) • b j := by
      have h := congrArg (algebraMap (𝓞 K) K) ((RingOfIntegers.basis K).sum_repr a)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      simp only [map_zsmul, ← NumberField.integralBasis_apply] at h
      exact h.symm
    refine ⟨∑ j, (RingOfIntegers.basis K).repr a j * (n j : ℤ), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul_comm, map_zsmul, htj, zsmul_eq_mul]
  · exact Subring.neg_mem _ (Subring.sum_mem _ fun i _ =>
      Subring.mul_mem _ (zp_memK hc (e i)) ((Valuation.mem_integer_iff _ _).2 (hN i).le))
  · have hz' : z = ∑ i, algebraMap ℚ_[ℓ] Fp (w i : ℚ_[ℓ]) * ι (bd i) := by
      rw [← hπβ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [β, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, hπ1, Algebra.smul_def]
    have hw : ∀ i, algebraMap ℚ_[ℓ] Fp (w i : ℚ_[ℓ]) =
        (n i : Fp) + (ℓ : Fp) ^ (k + N i) * algebraMap ℚ_[ℓ] Fp (e i : ℚ_[ℓ]) := by
      intro i
      have h := congrArg (fun x : ℤ_[ℓ] => algebraMap ℚ_[ℓ] Fp (x : ℚ_[ℓ])) (he i)
      simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub, map_mul, map_pow,
        map_natCast, map_sub] at h
      linear_combination -h
    have hιt : ι t = ∑ i, (n i : Fp) * ι (bd i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [t, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast, Rat.cast_natCast]
    rw [hιt, hz']
    simp only [hw]
    rw [mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

theorem dualApprox_of (hS : PowSmall) (hP : PiSurj) : DualApprox := by
  intro K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd hval z hz k
  haveI : CharZero Fp :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[Loc.resChar p] Fp).injective
  exact approx_core hS hc hfin ι (hP K (Loc.resChar p) Fp hc hfin ι hd) (int_memK ι hval)
    (val_ell_lt ι hval) z hz k

end PI.CntNotIntW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGSmall
section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

theorem oneFI_ne_zero (D : Formalism.BasicNotions.D7) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := by
  first
  | exact one_ne_zero
  | exact FractionalIdeal.one_ne_zero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem small_powers_bound : PowSmall := by
  intro Fp _ _ _ _ x y hy
  by_cases hx : valuation Fp x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨n, hn⟩ := exists_pow_lt₀ hy (Units.mk0 (valuation Fp x)⁻¹ (inv_ne_zero hx))
    have hn' : valuation Fp y ^ n < (valuation Fp x)⁻¹ := by rwa [Units.val_mk0] at hn
    refine ⟨n, ?_⟩
    rw [map_mul, map_pow]
    have hpos : 0 < valuation Fp x := zero_lt_iff.2 hx
    calc valuation Fp y ^ n * valuation Fp x < (valuation Fp x)⁻¹ * valuation Fp x :=
          mul_lt_mul_of_pos_right hn' hpos
      _ = 1 := inv_mul_cancel₀ hx

theorem dual_mul_different_integral (D : Formalism.BasicNotions.D7) (t : D.host.F)
    (ht : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) :
    ∀ d ∈ differentIdeal ℤ (𝓞 D.host.F), IsIntegral ℤ (t * algebraMap (𝓞 D.host.F) D.host.F d) := by
  intro d hd
  have h1 := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (B := 𝓞 D.host.F) (L := D.host.F)
  have hdmem : algebraMap (𝓞 D.host.F) D.host.F d ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F))⁻¹ := by
    rw [← h1]
    exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩
  have htmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [FractionalIdeal.mem_dual (oneFI_ne_zero D)]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := ht a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hn.symm
  have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ (oneFI_ne_zero D)
  have hprod := FractionalIdeal.mul_mem_mul htmem hdmem
  rw [mul_inv_cancel₀ hne] at hprod
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [← hy]
  first
  | exact RingOfIntegers.isIntegral_coe y
  | exact y.2

theorem differentF_ne_bot (D : Formalism.BasicNotions.D7) : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
  first
  | exact differentIdeal_ne_bot
  | exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)

theorem dual_lattice_powers : DualPow := by
  intro D t ht m
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)).injective
  have hne : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective hinj]
    exact differentF_ne_bot D
  have key : ∀ z ∈ Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)),
      (t : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E z ∈
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      have hint := (dual_mul_different_integral D t ht d hd).map
        (algebraMap D.host.F D.host.E).toIntAlgHom
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨⟨_, hint⟩, ?_⟩
      first
      | rfl
      | (simp [map_mul]; done)
      | (simp only [RingHom.toIntAlgHom_apply, map_mul]; rfl)
    | zero =>
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w₁, hw₁⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨w₂, hw₂⟩ := (FractionalIdeal.mem_one_iff _).mp hy
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨w₁ + w₂, by rw [map_add (f := _), hw₁, hw₂, map_add (f := _), mul_add]⟩
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul, mul_left_comm]
      obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨a * w, by rw [map_mul, hw]⟩
  have h1 : (t : D.host.E) ∈ (ddS D)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hne]
    intro y hy
    unfold ddS at hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact key z hz
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    first
    | exact FractionalIdeal.one_mem_one _
    | exact FractionalIdeal.one_mem_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact FractionalIdeal.mul_mem_mul ih h1

end PI.CntNotIntW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NGDefs
section
noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrIntG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → ∀ a,
      (g.e (frFac δ p a)).1 ∈ 𝒪[(D.s.atP p).Fp]

theorem frFac_last (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) :
    frFac δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac
  simp only [Fin.val_last, Nat.sub_self, pow_zero, Ring.inverse_one]

theorem frFac_coord (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (p : PlF D)
    (g : Loc.SplitG (M p).L) (a : Fin (D.R.rS + 1)) :
    (g.e (frFac δ p a)).2 = (g.e (frFac δ p a)).1 := by
  have hc : (M p).L.cj (frFac δ p a) = frFac δ p a := by
    rw [(hA p).2.2.1, cj_frFac]
  have h := g.e_cj (frFac δ p a)
  rw [hc] at h
  have h2 := congrArg Prod.snd h
  rw [Prod.snd_swap] at h2
  exact h2

theorem zhatLoc_eq (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (p : PlF D) (Z : MatZ D)
    (a b : Fin (D.R.rS + 1)) :
    ZhatLoc M δ p Z a b = frFac δ p b * frFac δ p a * (D.s.atP p).ιE (Z a b) := by
  have h : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  simp only [ZhatLoc, Matrix.of_apply]
  rw [h, cj_frFac]

end PI.CntNotIntW
end
end

