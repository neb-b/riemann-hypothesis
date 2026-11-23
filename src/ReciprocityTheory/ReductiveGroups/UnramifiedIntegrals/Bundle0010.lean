module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0005
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsExtendEndomorphismFractions
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem norm_prime_lt_one_padicField : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_l_Cl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_prime_pos_padicField : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_l_Cl]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)

theorem frobeniusLift_near_pow (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨r, hr, h⟩ := rmu_sigma_congr l s hs x
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

theorem frobeniusLift_norm_one (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l)
    (hx : ‖(x : ℂ_[l])‖ = 1) : ‖((s x : Rmu l) : ℂ_[l])‖ = 1 := by
  have h1 : ‖(x : ℂ_[l]) ^ l‖ = 1 := by rw [norm_pow, hx, one_pow]
  have h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖ := by
    rw [h1]; exact lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) (norm_prime_lt_one_padicField l)
  have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h2)
  rw [sub_add_cancel, max_eq_right h2.le, h1] at h3
  exact h3

theorem unitBall_eq_frac_normOne {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖b‖ = 1 ∧ x * b = a := by
  by_cases hx0 : x = 0
  · exact ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, norm_one, by simp [hx0]⟩
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l hx hx0
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖x‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd h1 (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  refine ⟨(l : ℂ_[l]) ^ k * a, (Rmu l).mul_mem ((Rmu l).pow_mem (natCast_mem _ l) k) ha,
    b, hb, hnb, ?_⟩
  rw [h, zpow_natCast]
  field_simp

theorem rmu_sigma_norm (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : (x : ℂ_[l]) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l (rmu_le_kmu l x.2) hx0'
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd (rmu_norm_le l x.2) (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l) := by
    apply Subtype.ext
    push_cast
    rw [h, zpow_natCast]
    field_simp
  have hs' := congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) (congrArg s he)
  simp only [map_mul, map_pow, map_natCast] at hs'
  push_cast at hs'
  rw [norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb,
    frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one] at hs'
  rw [hs', hn, zpow_natCast]

section Generic

variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)

def subringInclusionSubfield : R →+* F := Subring.inclusion h

theorem subringInclusionSubfield_coe (x : R) : ((subringInclusionSubfield R F h x : F) : K) = (x : K) := rfl

theorem subringInclusionSubfield_injective : Function.Injective (subringInclusionSubfield R F h) := fun x y e =>
  Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])

theorem isFractionRing_subringInclusion (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (subringInclusionSubfield_injective R F h)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, ha, b, hb, -, e⟩ := hf z z.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div, e]
  rfl

theorem exists_extend_endomorphism_fractions (h : R ≤ F.toSubring) (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b)
    (s : R →+* R) (hsinj : Function.Injective s) :
    ∃ σ : F →+* F, ∀ (x : F) (a b : R), (x : K) * b = a →
      ((σ x : F) : K) * (s b : R) = (s a : R) := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : IsFractionRing R F := isFractionRing_subringInclusion R F h hf
  have hg : Function.Injective ((subringInclusionSubfield R F h).comp s) := (subringInclusionSubfield_injective R F h).comp hsinj
  have hσ : ∀ x : R, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x) :=
    fun x => IsFractionRing.lift_algebraMap hg x
  refine ⟨IsFractionRing.lift hg, fun x a b e => ?_⟩
  have h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a :=
    Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])
  have h2 := congrArg (IsFractionRing.lift hg) h'
  rw [map_mul, hσ, hσ] at h2
  rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]

end Generic

theorem frobeniusLift_injective (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) : Function.Injective s := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have := rmu_sigma_norm l s hs x
  rw [hx, Subring.coe_zero, norm_zero] at this
  exact Subtype.ext (norm_eq_zero.mp this.symm)

theorem norm_unramifiedField_coe (x : Kmu l) : ‖x‖ = ‖(x : ℂ_[l])‖ := rfl

theorem kmu_sigma : ∃ s : Kmu l →+* Kmu l, (∀ x : Kmu l, ‖s x‖ = ‖x‖) ∧
    ∀ x : Kmu l, ‖x‖ ≤ 1 → ‖s x - x ^ l‖ ≤ ‖(l : Kmu l)‖ := by
  obtain ⟨s, hs⟩ := rmu_sigma l
  obtain ⟨σ, key⟩ := exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx)
    (fun _ hx => kmu_frac l hx) s (frobeniusLift_injective l s hs)
  refine ⟨σ, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, b, hb, hb0, h⟩ := kmu_frac l x.2
    have h1 : (x : ℂ_[l]) * b = a := by rw [h]; field_simp
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have h3 := congrArg norm h2
    have h4 := congrArg norm h1
    rw [norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs] at h3
    rw [norm_mul] at h4
    have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe]
    exact mul_right_cancel₀ hb' (h3.trans h4.symm)
  · intro x hx
    rw [norm_unramifiedField_coe] at hx
    obtain ⟨a, ha, b, hb, hnb, h1⟩ := unitBall_eq_frac_normOne l x.2 hx
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have hsb := frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb
    have hna := frobeniusLift_near_pow l s hs ⟨a, ha⟩
    have hnb' := frobeniusLift_near_pow l s hs ⟨b, hb⟩
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    generalize ((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna
    generalize ((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb
    generalize ((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢
    simp only at hna hnb'
    have e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l)) := by
      rw [← h1, ← h2]; ring
    have hxl : ‖(x : ℂ_[l]) ^ l‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have e2 : ‖(y - (x : ℂ_[l]) ^ l)‖ = ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖ := by
      rw [← e, norm_mul, hsb, mul_one]
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hna ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hxl).trans hnb'

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem qm_eq_qParam (m : ℕ) (τ : ℍ) : qm m τ = Function.Periodic.qParam (m : ℝ) τ := by
  simp [qm, Function.Periodic.qParam]

theorem qm_norm_lt_one {m : ℕ} (hm : 0 < m) (τ : ℍ) : ‖qm m τ‖ < 1 := by
  rw [qm_eq_qParam]
  exact Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos

theorem qm_surj {m : ℕ} (hm : 0 < m) {x : ℂ} (h0 : 0 < ‖x‖) (h1 : ‖x‖ < 1) : ∃ τ : ℍ, qm m τ = x := by
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg h0 h1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im := by
    rw [Function.Periodic.im_invQParam]
    refine mul_pos_of_neg_of_neg ?_ hlog
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨⟨_, him⟩, ?_⟩
  rw [qm_eq_qParam]
  exact Function.Periodic.qParam_right_inv hmR.ne' (norm_pos_iff.mp h0)

theorem qm_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) : qm m τ ^ m = qm 1 τ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [qm, qm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem qm_one_eq (τ : ℍ) : qm 1 τ = Function.Periodic.qParam 1 τ := by
  simpa using qm_eq_qParam 1 τ

theorem qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  rw [qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem IsMF.hasSum {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) := by
  obtain ⟨g, hg⟩ := hf
  have hgf : (⇑g : ℍ → ℂ) = f := funext hg
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rw [hgf, ← qm_one_eq] at h
  exact h

theorem IsMF.conv {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv (qExpansion 1 f) := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  · obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
    rw [← hτ]
    exact (hf.hasSum τ).summable

theorem IsMF.ev_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmSlash
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by
  classical
  have hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧
      Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t' := by
    intro t ht
    apply hnf_exists hm
    rw [Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]
  choose! g σ hσ hg using hex
  have hinvR : ∀ A : SL(2, ℤ),
      (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvL : ∀ A : SL(2, ℤ),
      ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Set.InjOn σ (Tm m) := by
    intro t1 h1 t2 h2 he
    have e1 := hg t1 h1
    have e2 := hg t2 h2
    rw [← he] at e2
    have key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rw [e1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ),
        hinvL, mul_one]
    apply hnf_unique hm h1 h2 (g t1 * (g t2)⁻¹)
    calc Tmat t1 = Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [mul_assoc, hinvR, mul_one]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 *
            (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [key]; simp only [mul_assoc]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by
          rw [mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]
  have himg : (Tm m).image σ = Tm m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hσ t ht
    · rw [Finset.card_image_of_injOn hinj]
  have hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t := by
    intro F
    conv_rhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hfac : ∏ t ∈ Tm m, fac (σ t) τ = ∏ t ∈ Tm m, fac t τ := hprod (fun t => fac t τ)
  have hden : ∏ t ∈ Tm m, ((σ t).2.2 : ℂ) = ∏ t ∈ Tm m, (t.2.2 : ℂ) := hprod (fun t => (t.2.2 : ℂ))
  have hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    exact_mod_cast (Tm_pos hm ht).2.ne'
  have hstep : ∏ t ∈ Tm m, fac t (γ • τ) =
      ∏ t ∈ Tm m, (denom γ τ ^ 24 * ((t.2.2 : ℂ) / (σ t).2.2) ^ 12 * fac (σ t) τ) :=
    Finset.prod_congr rfl (fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm (hσ t ht)) γ (g t) (hg t ht) τ)
  unfold Gm
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hfac,
    Finset.prod_pow, Finset.prod_div_distrib, hden, div_self hne, one_pow, mul_one]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1.KE

open Formalism.L2.Th1.CM

theorem norm_le_one_of_integral {K R : Type*} [NormedField K] [IsUltrametricDist K] [CommRing R]
    [Algebra R K] (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (δ : K) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨p, hp, hpe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpe
  have h1 : δ ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hpe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ p.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R K (p.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ p.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ p.natDegree / ‖δ‖ < ‖δ‖ ^ p.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ p.natDegree‖ = ‖δ‖ ^ p.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

theorem norm_int_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (n : ℤ) :
    ‖algebraMap ℤ K n‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_intCast_le_one K n

theorem norm_le_one_of_integral_int {K : Type*} [NormedField K] [IsUltrametricDist K] (δ : K)
    (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral norm_int_le_one δ h

theorem norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖x ^ i - y ^ i‖ ≤ ‖x - y‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : x ^ (i + 1) - y ^ (i + 1) = x * (x ^ i - y ^ i) + (x - y) * y ^ i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by gcongr
        _ = _ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖x - y‖ * ‖y‖ ^ i ≤ ‖x - y‖ * 1 := by
            gcongr; exact pow_le_one₀ (norm_nonneg _) hy
        _ = _ := mul_one _

theorem norm_eval_sub_eval_le {K : Type*} [NormedField K] [IsUltrametricDist K] (P : Polynomial K)
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖P.coeff i‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by
        gcongr
        · exact hP i
        · exact norm_pow_sub_pow_le hx hy i
    _ = _ := one_mul _

theorem finite_domain_frob (R : Type*) [CommRing R] [IsDomain R] [Finite R] (l : ℕ) (hl : l.Prime)
    (h0 : (l : R) = 0) : ∃ f : ℕ, 0 < f ∧ ∀ x : R, x ^ (l ^ f) = x := by
  classical
  have hch : CharP R l := (CharP.charP_iff_prime_eq_zero hl).mpr h0
  let _ := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R
  obtain ⟨n, -, hq⟩ := FiniteField.card R l
  exact ⟨n, n.pos, fun x => hq ▸ FiniteField.pow_card x⟩

theorem frob_fix_of_integral {K : Type*} [NormedField K] [IsUltrametricDist K] (l : ℕ)
    (hlp : l.Prime) (hl : ‖(l : K)‖ < 1) (δ : K) (hδ : IsIntegral ℤ δ) :
    ∃ f : ℕ, 0 < f ∧ ‖δ ^ (l ^ f) - δ‖ < 1 := by
  let A : Subalgebra ℤ K := Algebra.adjoin ℤ {δ}
  have hA : ∀ x : A, ‖(x : K)‖ ≤ 1 := fun x =>
    norm_le_one_of_integral norm_int_le_one _ (adjoin_le_integralClosure hδ x.2)
  let I : Ideal A :=
    { carrier := {x | ‖(x : K)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖((c * x : A) : K)‖ < 1
        rw [MulMemClass.coe_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hA c) (norm_nonneg _) hx }
  have hImem : ∀ x : A, x ∈ I ↔ ‖(x : K)‖ < 1 := fun x => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
      rw [hImem] at h1
      simp at h1
    · intro x y hxy
      by_contra hcon
      rw [not_or, hImem, hImem, not_lt, not_lt] at hcon
      rw [hImem, MulMemClass.coe_mul, norm_mul] at hxy
      have := one_le_mul_of_one_le_of_one_le hcon.1 hcon.2
      linarith
  have : Module.Finite ℤ A := Algebra.finite_adjoin_simple_of_isIntegral hδ
  have hl0 : ((l : ℕ) : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) l, Ideal.Quotient.eq_zero_iff_mem, hImem]
    have h2 : (((l : ℕ) : A) : K) = (l : K) := map_natCast A.val l
    rw [h2]
    exact hl
  have htors : Module.IsTorsion ℤ (A ⧸ I) := fun {x} =>
    ⟨⟨(l : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hlp.ne_zero)⟩, by
      change (l : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hl0, zero_mul]⟩
  have : Finite (A ⧸ I) := Module.finite_of_fg_torsion _ htors
  obtain ⟨f, hf, h⟩ := finite_domain_frob (A ⧸ I) l hlp hl0
  refine ⟨f, hf, ?_⟩
  let d : A := ⟨δ, Algebra.self_mem_adjoin_singleton ℤ δ⟩
  have h3 := h (Ideal.Quotient.mk I d)
  rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hImem] at h3
  exact h3

variable (l : ℕ) [Fact l.Prime]

theorem rmu_isIntegral_int {x : ℂ_[l]} (hx : x ∈ Rmu l) : IsIntegral ℤ x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨n, hn, -, h⟩ := hx
    exact IsIntegral.of_pow hn (h ▸ isIntegral_one)
  | zero => exact isIntegral_zero
  | one => exact isIntegral_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem isIntegral_int_of_rmu (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) :
    (Int.castRingHom ℂ_[l]).IsIntegralElem δ := by
  have : Algebra.IsIntegral ℤ (Rmu l) := ⟨fun x => by
    have := rmu_isIntegral_int l x.2
    exact (isIntegral_algebraMap_iff (A := Rmu l) (B := ℂ_[l]) ).mp this⟩
  have h : IsIntegral ℤ δ := isIntegral_trans δ hδ
  exact (Subsingleton.elim (algebraMap ℤ ℂ_[l]) (Int.castRingHom ℂ_[l])) ▸ h

theorem tch_mem_rmu {x : ℂ_[l]} (hx : x ∈ Tch l) : x ∈ Rmu l := by
  rcases hx with rfl | hx
  · exact (Rmu l).zero_mem
  · exact Subring.subset_closure hx

end ReciprocityTheory.ChartRestriction.L1.KE
end
end

