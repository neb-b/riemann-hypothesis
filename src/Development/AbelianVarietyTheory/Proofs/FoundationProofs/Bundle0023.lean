module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMulInvMemGamma1InterGamma0Level
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_mul_inv_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N →
    GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  intro N l d σ τ _ hσ hτ
  obtain ⟨hσc, hσd⟩ := hσ
  obtain ⟨hτc, hτd⟩ := hτ
  have detσ := Matrix.SpecialLinearGroup.det_coe σ
  have detτ := Matrix.SpecialLinearGroup.det_coe τ
  rw [Matrix.det_fin_two] at detσ detτ
  have e00 : ((τ * σ⁻¹) 0 0 : ℤ) = τ 0 0 * σ 1 1 - τ 0 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e10 : ((τ * σ⁻¹) 1 0 : ℤ) = τ 1 0 * σ 1 1 - τ 1 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e11 : ((τ * σ⁻¹) 1 1 : ℤ) = τ 1 1 * σ 0 0 - τ 1 0 * σ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσc hτc
  push_cast at hσc hτc
  have hNl : (N : ℤ) * l ∣ (τ * σ⁻¹) 1 0 := by
    rw [e10]
    exact dvd_sub (dvd_mul_of_dvd_left hτc _) (dvd_mul_of_dvd_right hσc _)
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hσc)
  have hτN : ((τ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hτc)
  have dσ : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - (σ 0 1 : ℤ) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detσ
  have dτ : ((τ 0 0 : ℤ) : ZMod N) * (τ 1 1 : ℤ) - (τ 0 1 : ℤ) * (τ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detτ
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; push_cast
      linear_combination (τ 0 0 : ZMod N) * hσd - (τ 0 0 : ZMod N) * hτd + dτ
        + (τ 0 1 : ZMod N) * hτN - (τ 0 1 : ZMod N) * hσN
    · rw [e11]; push_cast
      linear_combination (σ 0 0 : ZMod N) * hτd - (σ 0 0 : ZMod N) * hσd + dσ
        + (σ 0 1 : ZMod N) * hσN - (σ 0 1 : ZMod N) * hτN
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hNl)
  · rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) hNl)

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem conj_mem_lev {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ lev N l) : σ * γ * σ⁻¹ ∈ lev N l := by
  obtain ⟨h1, -⟩ := hσ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  have hN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) h1)
  have hl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) h1)
  obtain ⟨hg1, hg0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at hg1
  obtain ⟨hx, hw, hz⟩ := hg1
  rw [Gamma0_mem] at hg0
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdN := congrArg (Int.cast : ℤ → ZMod N) hdet
  push_cast at hdN
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hN, hx, hw, hz] at *
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hdN
    · linear_combination hdN
    · ring
  · rw [Gamma0_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hl, hg0]
    ring

end GlobalTheory.Hk

namespace GlobalTheory.Hk


open scoped Pointwise in
theorem dia_cuspForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  have hle : ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ) •
      (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤ (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv] at hy
    obtain ⟨γ, hγ, hγe⟩ := hy
    refine ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, ?_⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ (σ * γ * σ⁻¹) = y
    rw [map_mul, map_mul, map_inv, hγe]
    group
  refine ⟨{ toFun := dia k σ f
            slash_action_eq' := fun A hA => ?_
            holo' := ?_
            zero_at_cusps' := fun {x} hx => ?_ }, rfl⟩
  · obtain ⟨γ, hγ, rfl⟩ := hA
    have h : (f : ℍ → ℂ) ∣[k] (σ * γ * σ⁻¹) = f :=
      f.slash_action_eq' _ ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, rfl⟩
    show ((f : ℍ → ℂ) ∣[k] σ) ∣[k] γ = (f : ℍ → ℂ) ∣[k] σ
    rw [← SlashAction.slash_mul]
    have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
    rw [e, SlashAction.slash_mul, h]
  · exact MDifferentiable.slash f.holo' _ _
  · have h3 : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • x) (lev N l : Subgroup (GL (Fin 2) ℝ)) :=
      (hx.smul _).mono hle
    show x.IsZeroAt ((f : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ) k
    exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3)

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGam
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

open ConjAct Pointwise

namespace GlobalTheory.Hk

theorem conj_entries (σ y : SL(2, ℤ)) :
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 0 0 = (σ 0 0 * y 0 0 + σ 0 1 * y 1 0) * σ 1 1 - (σ 0 0 * y 0 1 + σ 0 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 0 = (σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 1 1 - (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 1 = -(σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 0 1 + (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 0 0) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  refine ⟨by ring, by ring, by ring⟩

theorem dia_conj_mem {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {y : SL(2, ℤ)}
    (hy : y ∈ lev N l) : σ * y * σ⁻¹ ∈ lev N l := by
  obtain ⟨hy1, hy0⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hc, -⟩ := hσ
  rw [Gamma1_mem] at hy1
  rw [Gamma0_mem] at hy0
  obtain ⟨hp, hs, hr⟩ := hy1
  obtain ⟨e00, e10, e11⟩ := conj_entries σ y
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (σ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
  have hcN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdvd)
  have hcl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd)
  have hdet : (σ 0 0 : ℤ) * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdetN : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - ((σ 0 1 : ℤ) : ZMod N) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem, e00, e10, e11]
    push_cast
    rw [hp, hs, hr, hcN]
    rw [hcN] at hdetN
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetN
  · rw [Gamma0_mem, e10]
    push_cast
    rw [hy0, hcl]
    ring

theorem lev_le_conj {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) :
    (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ • (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]
  exact Subgroup.mem_map.2 ⟨σ * y * σ⁻¹, dia_conj_mem hσ hy, by simp [map_mul, map_inv]⟩

theorem dia_modularForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → IsDia N l d σ →
    ∀ f : ModularForm (lev N l) k, ∃ g : ModularForm (lev N l) k, ⇑g = dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  let F := ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  have hle := lev_le_conj hσ
  refine ⟨{ toFun := ⇑F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, ?_⟩
  show ⇑F = _
  rw [ModularForm.coe_translate, dia, ModularForm.SL_slash]
  rfl

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeCupProps
section
open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KEdge

theorem edge_cup_props : ∀ (Γ : Type) [Group Γ] (N : ℕ) (Δ : Subgroup Γ) [Δ.Normal] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  CobOn Δ x y η →
  (∀ σ, ∀ h ∈ Δ, ∀ h' ∈ Δ, edge x y η σ (h * h') = edge x y η σ h + edge x y η σ h') ∧
  (∀ σ τ, ∀ h ∈ Δ, edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h) ∧
  (∀ σ ∈ Δ, ∀ h ∈ Δ, edge x y η σ h = 0) := by
  intro Γ _ N Δ hN x y η hC
  have hmul : ∀ (z : Γ →* Multiplicative (ZMod N)) (a b : Γ), (z (a * b)).toAdd = (z a).toAdd + (z b).toAdd := by
    intro z a b; rw [z.map_mul]; rfl
  have hconj : ∀ (z : Γ →* Multiplicative (ZMod N)) (s a : Γ), (z (s * a * s⁻¹)).toAdd = (z a).toAdd := by
    intro z s a
    rw [hmul, hmul, z.map_inv, toAdd_inv]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro σ h hh h' hh'
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have m2 : σ * h' * σ⁻¹ ∈ Δ := hN.conj_mem h' hh' σ
    have e1 := hC _ m1 _ m2
    have e2 := hC h hh h' hh'
    have g : σ * (h * h') * σ⁻¹ = (σ * h * σ⁻¹) * (σ * h' * σ⁻¹) := by group
    simp only [edge]
    rw [g, hmul x h h', hmul y h h']
    rw [hconj x, hconj y] at e1
    linear_combination e1 - e2
  · intro σ τ h _
    have g : σ * τ * h * (σ * τ)⁻¹ = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
    simp only [edge]
    rw [g, hmul x σ τ, hmul y σ τ, hconj x τ h, hconj y τ h]
    ring
  · intro σ hσ h hh
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have e1 := hC _ m1 σ hσ
    have e2 := hC σ hσ h hh
    have g : σ * h * σ⁻¹ * σ = σ * h := by group
    rw [g, hconj x] at e1
    simp only [edge]
    linear_combination e2 - e1

end GlobalTheory.KEdge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EePosFalseDvd
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UpSplit

open GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

theorem cmul_vp_vp (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    cmul (vp p f) (vp p g) (p * r) = cmul f g r := by
  unfold cmul
  symm
  have h1 : ∀ j ∈ range (r + 1), f j * g (r - j) = vp p f (p * j) * vp p g (p * r - p * j) := by
    intro j _
    simp only [vp, dvd_mul_right, if_true, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hp]
  rw [sum_congr rfl h1, ← sum_image (f := fun i => vp p f i * vp p g (p * r - i)) (g := fun j => p * j)
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  apply sum_subset
  · intro i hi
    simp only [mem_image, mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    have : j ≤ r := by omega
    have := Nat.mul_le_mul_left p this
    omega
  · intro i hi hni
    simp only [mem_image, mem_range, not_exists, not_and] at hi hni
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      exact absurd rfl (hni j (by
        have : p * j ≤ p * r := by omega
        have := Nat.le_of_mul_le_mul_left this hp
        omega))
    · simp [vp, hpi]

end GlobalTheory.KummerEisensteinGalois.UpSplit

namespace GlobalTheory.KummerEisensteinGalois


end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromIFinsetSum
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerSum

theorem eichler_integrand_intervalIntegrable {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : ℍ) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ k * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := (UpperHalfPlane.mdifferentiable_iff.mp hf).continuousOn
  apply ContinuousOn.intervalIntegrable
  have hmap : Set.MapsTo (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) {z : ℂ | 0 < z.im} := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.I_re, zero_mul, add_zero]
    rw [UpperHalfPlane.coe_im]
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; nlinarith
    · nlinarith [mul_nonneg h0 hτ.le]
  have hc : ContinuousOn (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) := by fun_prop
  refine ContinuousOn.mul (ContinuousOn.mul (hd.comp hc hmap) ?_) continuousOn_const
  fun_prop

theorem eichler_finset_sum (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ)
    (hg : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) (τ : ℍ) :
    eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  unfold eichler
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum,
    ← intervalIntegral.integral_finsetSum fun i _ => eichler_integrand_intervalIntegrable (hg i) τ (w - j)]
  congr 4
  funext t
  simp only [Function.comp_apply, Finset.sum_apply, Finset.sum_mul]

end GlobalTheory.EichlerSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromITailExponentialDecay
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open MeasureTheory Filter Topology Set

namespace GlobalTheory.HeckeFamilyMatrices

theorem eichler_tail_cauchy (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (hc : 0 < c)
    (hb : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) (hτ : 1 ≤ τ.im) :
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) := by
  have hI : (1:ℝ) ≤ Complex.I.im := by simp
  have i1 := (_root_.GlobalTheory.vertRay_integral_expPow_bound g K c m Complex.I hg.continuousOn hc hb hI).1
  have i2 := (_root_.GlobalTheory.vertRay_integral_expPow_bound g K c m τ hg.continuousOn hc hb hτ).1
  have t1 := intervalIntegral_tendsto_integral_Ioi 0 i1 tendsto_id
  have t2 := intervalIntegral_tendsto_integral_Ioi 0 i2 tendsto_id
  have t3 := _root_.GlobalTheory.top_side_integral_tendsto_zero g K c m τ hg.continuousOn hc hb hτ
  have hlim : Tendsto (fun S : ℝ => Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop
      (𝓝 (Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) + (τ - Complex.I) * 0)) :=
    ((t1.const_mul _).sub (t2.const_mul _)).add (t3.const_mul _)
  rw [mul_zero, add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 0] with S hS
  exact _root_.GlobalTheory.cauchy_parallelogram_upper_half_plane g τ S hg (by linarith) hS

theorem eichler_tail : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c →
    (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) →
    ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w,
      ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  intro w F C c hF hc hbd
  set G : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex with hGdef
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := UpperHalfPlane.mdifferentiable_iff.mp hF
  let g : ℕ → ℂ → ℂ := fun j z => G z * (-z) ^ (w - j)
  have hg : ∀ j, DifferentiableOn ℂ (g j) {z : ℂ | 0 < z.im} := fun j =>
    hG.mul ((differentiable_id.neg.pow _).differentiableOn)
  have hgb : ∀ j, ∀ z : ℂ, 1 ≤ z.im → ‖g j z‖ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w := by
    intro j z hz
    have hz0 : 0 < z.im := by linarith
    have h1 : ‖G z‖ ≤ C * Real.exp (-c * z.im) := by
      have := hbd ⟨z, hz0⟩ hz
      simpa [hGdef, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz0] using this
    have h2 : ‖(-z) ^ (w - j)‖ ≤ (1 + ‖z‖) ^ w := by
      rw [norm_pow, norm_neg]
      calc ‖z‖ ^ (w - j) ≤ (1 + ‖z‖) ^ (w - j) := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + ‖z‖) ^ w := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.sub_le _ _)
    calc ‖g j z‖ = ‖G z‖ * ‖(-z) ^ (w - j)‖ := norm_mul _ _
      _ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  set M : ℝ := ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ w
  set Lp : ℂ[X] := ∑ j ∈ Finset.range (w + 1),
      Polynomial.C ((w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I))) * X ^ j
    with hLp
  refine ⟨Lp, 2 ^ w * C * M, ?_⟩
  intro τ hτ j hj
  have hj' : j ∈ Finset.range (w + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hc1 : (eichler w F τ).coeff j = (w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) := by
    rw [eichler, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hc2 : Lp.coeff j = (w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I)) := by
    rw [hLp, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hint : (∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
      ((τ : ℂ) - Complex.I) * ∫ t in (0:ℝ)..1, g j (Complex.I + t * ((τ : ℂ) - Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; simp only [g, hGdef]; ring
  have hL5 := eichler_tail_cauchy (g j) C c w (τ : ℂ) (hg j) hc (hgb j) hτ
  have hkey : (eichler w F τ - Lp).coeff j = -((w.choose j : ℂ) * Complex.I * ∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)) := by
    rw [Polynomial.coeff_sub, hc1, hc2, hint, hL5]; ring
  rw [hkey, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have hb3 := (_root_.GlobalTheory.vertRay_integral_expPow_bound (g j) C c w (τ : ℂ) (hg j).continuousOn hc (hgb j) hτ).2
  have hch : ‖(w.choose j : ℂ)‖ ≤ 2 ^ w := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.choose_le_two_pow w j
  have hnn : 0 ≤ C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M := (norm_nonneg _).trans hb3
  calc ‖(w.choose j : ℂ)‖ * ‖∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)‖
      ≤ 2 ^ w * (C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M) :=
        mul_le_mul hch hb3 (norm_nonneg _) (by positivity)
    _ = 2 ^ w * C * M * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
        ring

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleSubgroupOf
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem almostSep_subgroupOf (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (U H : Subgroup G) (hU : AlmostSep v U) :
    AlmostSep v (U.subgroupOf H) := by
  intro r hr
  obtain ⟨n, a, b, c, hs, hc⟩ := hU r hr
  have hfix : ∀ x : L, x ∈ Fix L U → x ∈ Fix L (U.subgroupOf H) := by
    intro x hx σ
    exact hx ⟨(σ.1 : G), Subgroup.mem_subgroupOf.mp σ.2⟩
  refine ⟨n, a, b, c, ⟨fun i => hfix _ (hs.a_mem i), fun i => hfix _ (hs.b_mem i),
    hfix _ hs.c_mem, hs.a_le, hs.b_le, hs.c_le, ?_, ?_⟩, hc⟩
  · intro σ hσ
    exact hs.sum_in (σ : G) (Subgroup.mem_subgroupOf.mp hσ)
  · intro σ hσ
    exact hs.sum_out (σ : G) (fun h => hσ (Subgroup.mem_subgroupOf.mpr h))

end GlobalTheory.AlmostEt
end

