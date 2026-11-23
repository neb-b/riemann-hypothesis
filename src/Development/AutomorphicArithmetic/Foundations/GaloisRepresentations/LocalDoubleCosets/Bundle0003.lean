module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
public import GroundTheory.AutomorphicForms.Bundle0007
public import GroundTheory.AutomorphicForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrSurj
section
noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

theorem prSurj : PrSurj := by
  classical
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ K hKo hKc hBK φ hφ
  obtain ⟨hφB, K0, hK0o, hφK0⟩ := mem_indF.1 hφ
  set S : Set B := {b | (b : G) ∈ K} with hS
  have hSo : IsOpen S := hKo.preimage continuous_subtype_val
  have hSc : IsCompact S := (hB.isClosedEmbedding_subtypeVal).isCompact_preimage hKc
  have hSpos : 0 < μ S := hSo.measure_pos μ ⟨1, K.one_mem⟩
  have hSfin : μ S < ⊤ := hSc.measure_lt_top
  have hr : (μ S).toReal ≠ 0 := (ENNReal.toReal_pos hSpos.ne' hSfin.ne).ne'
  have hr' : ((μ S).toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  set c : ℂ := ((μ S).toReal : ℂ)⁻¹ with hc
  refine ⟨fun g => if g ∈ K then c * φ g else 0, ?_, ?_⟩
  · let K' : OpenSubgroup G := ⟨K ⊓ K0, hKo.inter hK0o⟩
    apply GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right (R := ℂ) K'
    · exact HasCompactSupport.intro hKc (fun g hg => if_neg hg)
    · intro g k hk
      have hk' : k ∈ K ∧ k ∈ K0 := Subgroup.mem_inf.1 hk
      simp only [K.mul_mem_cancel_right hk'.1, hφK0 k hk'.2 g]
  · funext g
    obtain ⟨b0, hb0, k0, hk0, rfl⟩ := hBK g
    set b0' : B := ⟨b0, hb0⟩
    have key : ∀ b : B, ((b : G)⁻¹ * (b0 * k0) ∈ K) ↔ b ∈ (fun x => b0'⁻¹ * x) ⁻¹' S := by
      intro b
      simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, b0']
      rw [← mul_assoc, K.mul_mem_cancel_right hk0, ← K.inv_mem_iff]
      simp [mul_inv_rev]
    have hTm : MeasurableSet ((fun x : B => b0'⁻¹ * x) ⁻¹' S) :=
      (hSo.preimage (continuous_const.mul continuous_id)).measurableSet
    have hint : (fun b : B => (χ b : ℂ) * (if ((b:G)⁻¹ * (b0 * k0)) ∈ K then c * φ ((b:G)⁻¹ * (b0*k0)) else 0))
        = ((fun x : B => b0'⁻¹ * x) ⁻¹' S).indicator (fun _ => c * φ (b0 * k0)) := by
      funext b
      by_cases h : ((b:G)⁻¹ * (b0 * k0)) ∈ K
      · rw [if_pos h, Set.indicator_of_mem ((key b).1 h)]
        have h1 := hφB b⁻¹ (b0 * k0)
        rw [Subgroup.coe_inv] at h1
        rw [h1]
        have hu : (χ b : ℂ) * (χ b⁻¹ : ℂ) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        linear_combination (c * φ (b0 * k0)) * hu
      · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((key b).2 h')), mul_zero]
    simp only [pr]
    rw [hint, integral_indicator_const _ hTm, measureReal_def, measure_preimage_mul]
    rw [hc, Complex.real_smul]
    field_simp

end UpperTheory.Gal.LocD

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.StabSub
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.stabSub :
    StabSub := by
  intro H _ _ _ _ _ _ τ p hp hτ hper L hL
  obtain ⟨K, hKc, hKL⟩ := GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset
    (hL.mem_nhds L.one_mem)
  let L₀ : Subgroup H :=
    { carrier := {l | ∀ i < p, τ^[i] l ∈ K}
      one_mem' := fun i _ => by rw [iterate_map_one]; exact K.one_mem
      mul_mem' := fun ha hb i hi => by
        rw [iterate_map_mul]; exact K.mul_mem (ha i hi) (hb i hi)
      inv_mem' := fun ha i hi => by
        rw [iterate_map_inv]; exact K.inv_mem (ha i hi) }
  have hset : (L₀ : Set H) = ⋂ i ∈ {i : ℕ | i < p}, τ^[i] ⁻¹' (K : Set H) := by
    ext l; simp [L₀]
  have hopen : IsOpen (L₀ : Set H) := by
    rw [hset]
    exact (Set.finite_lt_nat p).isOpen_biInter
      (fun i _ => K.isOpen.preimage (hτ.iterate i))
  have hsub : (L₀ : Set H) ⊆ K := fun l hl => by
    have := hl 0 hp
    simpa using this
  refine ⟨L₀, hKc.of_isClosed_subset (L₀.isClosed_of_isOpen hopen) hsub, hopen,
    fun l hl => hKL (hsub hl), fun l => ?_⟩
  show (∀ i < p, τ^[i] (τ l) ∈ K) ↔ ∀ i < p, τ^[i] l ∈ K
  constructor
  · intro h i hi
    rcases i with _ | j
    · have h1 := h (p - 1) (by omega)
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper] at h1
      simpa using h1
    · rw [Function.iterate_succ_apply]
      exact h j (by omega)
  · intro h i hi
    rw [← Function.iterate_succ_apply]
    by_cases hlt : i + 1 < p
    · exact h (i + 1) hlt
    · have hip : i + 1 = p := by omega
      rw [Nat.succ_eq_add_one, hip, hper]
      simpa using h 0 hp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.ToBorel
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private def dg (E : Type) [Field E] (n : ℕ) : borel E (Fin n) →* (Fin n → Eˣ) :=
  (leviTorus E (Fin n)).symm.toMonoidHom.comp (leviProj E (points (Fin n)))

private theorem dg_val (b : borel E (Fin n)) (i : Fin n) :
    ((dg E n b i : Eˣ) : E) = ((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i := by
  show (GeneralLinearGroup.det (leviProj E (points (Fin n)) b i) : E) = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  exact leviProj_apply E (points (Fin n)) b i _ _

private theorem absPow_map (σ : E ≃+* E) (hσ : Isom σ) (s : ℂ) (x : Eˣ) :
    absPow E s (Units.map (σ : E →* E) x) = absPow E s x := by
  have hv : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1 := by
    have hx : valuation E (x : E) ≠ 0 := by simp
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    rw [hσ]
    exact mul_inv_cancel₀ hx
  have h1 := isUnram_absPow E s _ hv
  have h2 : Units.map (σ : E →* E) x = (Units.map (σ : E →* E) x * x⁻¹) * x := by group
  rw [h2, map_mul, h1, one_mul]

private def dl (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    borel E (Fin n) →* ℂˣ :=
  (deltaHalf E (fun _ : Fin n => Unit)).comp (leviProj E (points (Fin n)))

private theorem dl_eq (b : borel E (Fin n)) :
    dl E n b = ∏ i, absPow E ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (dg E n b i) :=
  deltaHalf_apply E _

end

theorem toBorel : ToBorel := by
  intro E _ _ _ _ n σ hσ V _ _ π μ hμ l hl
  refine ⟨dl E n * μ.comp (dg E n), ?_, ?_⟩
  · intro b b' hbb'
    have hd : dg E n b' = fun i => Units.map (σ : E →* E) (dg E n b i) := by
      funext i
      ext
      rw [dg_val, hbb', Units.coe_map, dg_val]
      simp only [sg, Matrix.GeneralLinearGroup.map_apply]
      rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, dl_eq, hd, hμ, absPow_map σ hσ]
  · intro b v
    obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip E (points (Fin n)) b
    have hq : (Submodule.Quotient.mk (π u v) : Jacquet π (unipB E (Fin n))) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      apply Submodule.subset_span
      exact ⟨⟨u, hu⟩, v, by simp⟩
    have hL : leviTorus E (Fin n) (dg E n b) = leviProj E (points (Fin n)) b :=
      MulEquiv.apply_symm_apply _ _
    have ht : jacB π (dg E n b) (Submodule.Quotient.mk (π u v))
        = jac (points (Fin n)) π (leviProj E (points (Fin n)) b) (Submodule.Quotient.mk (π u v)) := by
      show jac (points (Fin n)) π (leviTorus E (Fin n) (dg E n b)) _ = _
      exact congrArg (fun g => jac (points (Fin n)) π g (Submodule.Quotient.mk (π u v))) hL
    have h2 : l (jacB π (dg E n b) (Submodule.Quotient.mk (π u v)))
        = (((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b))⁻¹ : ℂˣ) : ℂ)
          * l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v))) := by
      rw [ht, jac_mk]
      exact map_smul l _ _
    have hX : l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v)) : Jacquet π (unipB E (Fin n)))
        = ((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b) : ℂˣ) : ℂ)
          * ((μ (dg E n b) : ℂ) * l (Submodule.Quotient.mk v)) := by
      rw [← hq, ← hl, h2, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [hbu, map_mul, Module.End.mul_apply, hX, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_assoc]
    rfl

end UpperTheory.Gal.LocD

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePowAlt
section
namespace UpperTheory.Gal.LocD

theorem tracePow : TracePow := by
  intro J _ _ _ _ φ hφ k₀
  by_contra hne
  push_neg at hne
  set p := φ.charpoly with hp
  have hc : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff φ).1
      (by rw [Polynomial.constantCoeff_apply]; exact h0)
    exact hm (hφ (by rw [hm0, map_zero]))
  set t : Polynomial ℂ := -Polynomial.C (p.coeff 0)⁻¹ * Polynomial.divX p with ht
  have hinv : φ * Polynomial.aeval φ t = 1 := by
    have h := congrArg (Polynomial.aeval φ) (Polynomial.X_mul_divX_add p)
    rw [hp, LinearMap.aeval_self_charpoly, ← hp] at h
    simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    have h' : φ * Polynomial.aeval φ (Polynomial.divX p) = -(algebraMap ℂ _ (p.coeff 0)) :=
      eq_neg_of_add_eq_zero_left h
    rw [ht, map_mul, map_neg, Polynomial.aeval_C, neg_mul, mul_neg, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, h', mul_neg, neg_neg, ← map_mul, inv_mul_cancel₀ hc,
      map_one]
  set Q : Polynomial ℂ := (Polynomial.X * t) ^ k₀ with hQ
  have hQ1 : Polynomial.aeval φ Q = 1 := by
    rw [hQ, map_pow, map_mul, Polynomial.aeval_X, hinv, one_pow]
  have htr : LinearMap.trace ℂ J (Polynomial.aeval φ Q) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.aeval_eq_sum_range, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
    by_cases hi : k₀ ≤ i
    · rw [hne i hi, mul_zero]
    · rw [hQ, mul_pow, Polynomial.coeff_X_pow_mul', if_neg hi, zero_mul]
  rw [hQ1, LinearMap.trace_one] at htr
  exact (Nat.cast_ne_zero.2 (Module.finrank_pos (R := ℂ) (M := J)).ne') htr

end UpperTheory.Gal.LocD
end

