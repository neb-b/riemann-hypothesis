module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcBase

@[expose] public section

-- bundled from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiffSmulMem
section
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem kc_comm_of (σ : H.E ≃ₐ[ℚ] H.E) (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ (τ x) = τ (σ x) := by
  have h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ :=
    H.gal.injective (by rw [map_mul, map_mul, mul_comm])
  have := congrArg (fun f : H.E ≃ₐ[ℚ] H.E => f x) h
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using this

theorem kc_comm_symm (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x))
    (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ.symm (τ x) = τ (σ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]

theorem kc_sum_comm (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (w : H.E) :
    σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun τ _ => hc τ w

theorem kc_one_ne : (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := one_ne_zero

private theorem mem_one_fractionalIdeal_iff_isIntegral (t : H.E) : t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

private theorem isIntegral_algEquiv_apply_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) : IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

theorem kc_mem_dual_iff (y : H.E) :
    y ∈ FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x)) := by
  haveI := H.galois
  rw [FractionalIdeal.mem_dual (kc_one_ne H)]
  have key : ∀ w : H.E, Algebra.trace H.K H.E w ∈ (algebraMap (𝓞 H.K) H.K).range ↔
      IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) := by
    intro w
    rw [← trace_eq_sum_automorphisms, isIntegral_algebraMap_iff ]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact NumberField.RingOfIntegers.isIntegral_coe a
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  constructor
  · intro h x
    rw [← key]
    have := h _ ((mem_one_fractionalIdeal_iff_isIntegral H _).mpr (NumberField.RingOfIntegers.isIntegral_coe x))
    rwa [Algebra.traceForm_apply] at this
  · intro h a ha
    rw [mem_one_fractionalIdeal_iff_isIntegral] at ha
    rw [Algebra.traceForm_apply, key]
    exact h ⟨a, ha⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem kc_mem_diff_iff (z : 𝓞 H.E) :
    z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      ∀ y : H.E, (∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) →
        IsIntegral ℤ ((z : H.E) * y) := by
  have hd : FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
    simpa [FractionalIdeal.dual_eq_zero_iff] using kc_one_ne H
  have e1 : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      (z : H.E) ∈ ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro h
      exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, e⟩
      have : w = z := NumberField.RingOfIntegers.ext e
      rwa [← this]
  rw [e1, coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E), FractionalIdeal.mem_inv_iff hd]
  simp only [kc_mem_dual_iff, mem_one_fractionalIdeal_iff_isIntegral]

theorem kc_dual_smul (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (y : H.E)
    (hy : ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) :
    ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x)) := by
  intro x
  have hx := hy (σ⁻¹ • x)
  have hx' : σ ((σ⁻¹ • x : 𝓞 H.E) : H.E) = (x : H.E) := by
    show σ (σ⁻¹ (x : H.E)) = x
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have e : ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x) =
      σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * ((σ⁻¹ • x : 𝓞 H.E) : H.E))) := by
    rw [kc_sum_comm H σ hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul σ, hx']
  rw [e, isIntegral_algEquiv_apply_iff]
  exact hx

theorem kc_diff_smul_mem (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (z : 𝓞 H.E)
    (hz : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E)) : σ • z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  rw [kc_mem_diff_iff] at hz ⊢
  intro y hy
  have hy' := kc_dual_smul H σ.symm (kc_comm_symm H σ hc) y hy
  have h1 := hz (σ.symm y) hy'
  rw [← isIntegral_algEquiv_apply_iff H σ, map_mul, AlgEquiv.apply_symm_apply] at h1
  have e : ((σ • z : 𝓞 H.E) : H.E) = σ (z : H.E) := rfl
  rw [e]
  exact h1

theorem kc_diff_smul_le (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) ≤ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have := kc_diff_smul_mem H σ hc _ hx
  rwa [smul_inv_smul] at this

theorem kc_diff_smul_eq (σ : H.E ≃ₐ[ℚ] H.E) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  apply le_antisymm (kc_diff_smul_le H σ (kc_comm_of H σ))
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  exact kc_diff_smul_mem H σ⁻¹ (kc_comm_of H σ⁻¹) x hx

theorem kc_mem_one_iff (t : H.E) :
    t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

theorem kc_integ_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

theorem kc_smul_ne_bot (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  rw [← inv_smul_smul σ B, h]
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

theorem kc_mem_inv_smul (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) (y : H.E) :
    σ y ∈ ((σ • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
  have hB' : (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hσB : ((σ • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H σ B hB)
  rw [FractionalIdeal.mem_inv_iff hσB, FractionalIdeal.mem_inv_iff hB']
  constructor
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    have hb' : σ • b ∈ σ • B := by
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hb
    have := h (algebraMap (𝓞 H.E) H.E (σ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ • b, hb', rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    rw [show algebraMap (𝓞 H.E) H.E (σ • b) = σ (algebraMap (𝓞 H.E) H.E b) from rfl, ← map_mul,
      kc_integ_iff] at this
    exact this
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have := h (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ⁻¹ • b, hb, rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    have e : σ (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) = algebraMap (𝓞 H.E) H.E b := by
      show σ (σ⁻¹ (b : H.E)) = b
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rw [← kc_integ_iff H σ, map_mul, e] at this
    exact this

theorem unimodular : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  intro B hdiff x
  have hD0 := differentIdeal_ne_bot (A := 𝓞 H.K) (B := 𝓞 H.E)
  have hB : B ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_mul] at hdiff
    exact hD0 hdiff
  have hJ : ((H.conj • B : Ideal (𝓞 H.E)) :
      FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H H.conj B hB)
  have hdual : FractionalIdeal.dual (𝓞 H.K) H.K
      (((H.conj • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) =
      ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, inv_inv,
      ← inv_inv (FractionalIdeal.dual (𝓞 H.K) H.K
        (1 : FractionalIdeal (𝓞 H.E)⁰ H.E)),
      ← coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E),
      hdiff, FractionalIdeal.coeIdeal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hJ, mul_one]
  have hx : x ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ ↔
      x ∈ FractionalIdeal.dual (𝓞 H.K) H.K
        (((H.conj • B : Ideal (𝓞 H.E)) :
          FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) := by
    rw [hdual]
  rw [hx, FractionalIdeal.mem_dual (inv_ne_zero hJ)]
  constructor
  · intro hh y hy
    have := hh (H.conj y) ((kc_mem_inv_smul H H.conj B hB y).mpr hy)
    rwa [Algebra.traceForm_apply] at this
  · intro hh z hz
    rw [Algebra.traceForm_apply]
    have hz' : H.conj (H.conj.symm z) = z := H.conj.apply_symm_apply z
    rw [← hz'] at hz ⊢
    exact hh _ ((kc_mem_inv_smul H H.conj B hB _).mp hz)

end Formalism.HC.Der

end
end

-- bundled from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne
section
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem kc_eq_of_pow_eq_one {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

variable (C : HostCore H)
include C

theorem kc_no_root_d (η : H.E) (hη : IsPrimitiveRoot η H.d) : False := by
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have := H.galois
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hge := Mu.mu_le_ram H.d Q (H.d - 1) (Mu.mu_mem_pow H.d Q η hη)
  have hd := H.hyp.2.2.2.1
  have hle := Mu.mu_card_le_two (L := H.E) H.gal H.gal.injective φ.iod (Q.inertia Gal(H.E/ℚ))
    (fun ρ hρ => (C.inertia_d Q ρ).mp (AddSubgroup.mem_inertia.mp hρ))
  rw [odd_card H.E H.d Q] at hle
  omega

theorem kc_iod_fix (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ = φ.iod) (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : σ x = x := by
  obtain ⟨n, hn, hxn⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hxn⟩
  have hmpos : 0 < orderOf x := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hd : ¬ H.d ∣ orderOf x := by
    rintro ⟨k, hk⟩
    exact kc_no_root_d H C _ (hprim.pow hmpos (by rw [hk, mul_comm]))
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hin := (C.inertia_d P σ).mpr (Or.inr hσ)
  have hint : IsIntegral ℤ x := hprim.isIntegral hmpos
  let X : 𝓞 H.E := ⟨x, hint⟩
  have hX : X ^ orderOf x = 1 := by
    apply RingOfIntegers.ext
    have : ((X ^ orderOf x : 𝓞 H.E) : H.E) = (X : H.E) ^ orderOf x := by push_cast; rfl
    rw [this]
    exact hprim.pow_eq_one
  have hX' : (σ • X) ^ orderOf x = 1 := by rw [← smul_pow', hX, smul_one]
  have hm : ((orderOf x : ℕ) : 𝓞 H.E) ∉ P := by
    intro h0
    have h1 := (odd_intCast_mem_iff H.d P ((orderOf x : ℕ) : ℤ)).mp (by exact_mod_cast h0)
    exact hd (by exact_mod_cast h1)
  have := kc_eq_of_pow_eq_one P hm hX' hX (hin X)
  exact congrArg (fun y : 𝓞 H.E => (y : H.E)) this

theorem kc_conj_mul_self (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : x * H.conj x = 1 := by
  obtain ⟨n, hn, hxn⟩ := hx
  let ψ : H.E →+* ℂ := Classical.choice inferInstance
  apply ψ.injective
  have h1 : ‖ψ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hxn, map_one]) hn.ne'
  rw [map_mul, (C.conj_iff ψ H.conj).mpr (kc_gal_conj H), Complex.mul_conj', h1, map_one]
  simp

theorem norm_mu : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1 := by
  classical
  intro x hx
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  obtain ⟨ι, hι⟩ := H.gal.surjective φ.iod
  set s₀ := H.conj * ι with hs₀
  have hg : H.gal s₀ = φ.sg := by
    rw [hs₀, map_mul, kc_gal_conj, hι]
    exact Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)
  have hΨ : H.gal s₀ ∈ φ.Psi := by rw [hg]; rfl
  let s : H.E ≃ₐ[H.K] H.E := AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv) (fun y => kc_fixK H s₀ hΨ y)
  have hs : ∀ y, s y = s₀ y := fun _ => rfl
  have hsx : x * s x = 1 := by
    rw [hs, hs₀, AlgEquiv.mul_apply, kc_iod_fix H C ι hι x hx]
    exact kc_conj_mul_self H C x hx
  have hss0 : s₀ * s₀ = 1 := by
    apply H.gal.injective
    rw [map_mul, hg, map_one]
    exact Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)
  have hss : s * s = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : s₀ = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun h1 y
    rw [h2, map_one] at hg
    exact absurd (congrArg (fun g : φ.GG => g.1) hg) (show ¬ (1 : G0) = (-1, 1) by decide)
  apply (algebraMap H.K H.E).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_one]
  refine Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_) (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun σ _ => ?_)
  · rw [AlgEquiv.mul_apply, ← map_mul, hsx, map_one]
  · exact fun h1 => hs1 (mul_eq_left.mp h1)
  · rw [mul_assoc, hss, mul_one]

end Formalism.HC.Der

end
end

