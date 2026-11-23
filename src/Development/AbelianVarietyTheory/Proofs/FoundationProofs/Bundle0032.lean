module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatrix
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section
namespace GlobalTheory.Hk.UDia

def gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a*d - b*q*c - a*j*c, a*b + b*j'*c + a*Y; c*d - c^2*j - c*d*q, a*d + c*d*j' + c*Y]

theorem det_gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) : (gam a b c d j j' q Y).det = 1 := by
  rw [gam, Matrix.det_fin_two_of]
  subst hY
  linear_combination (a*d - (a*j + j*j'*c - j'*d - q*Y)*c + 1) * hdet

theorem alg (a b c d Y t w z j j' q : ℂ) (hq : q ≠ 0) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) (hwq : w*q = t + j)
    (hzq : z*q*(c*t+d) = a*t + b + j'*(c*t+d)) :
    a*w + b = (c*t+d) * ((a*d - b*q*c - a*j*c) * z + (a*b + b*j'*c + a*Y)) ∧
    c*w + d = (c*t+d) * ((c*d - c^2*j - c*d*q) * z + (a*d + c*d*j' + c*Y)) := by
  subst hY
  constructor
  · apply mul_left_cancel₀ hq
    linear_combination a*hwq - (a*d - (a*j + j*j'*c - j'*d - q*Y)*q*c - a*j*c)*hzq
      - (a*(t+j) + (a*j + j*j'*c - j'*d - q*Y)*q)*hdet
  · apply mul_left_cancel₀ hq
    linear_combination c*hwq - (c*d - c^2*j - c*d*q)*hzq - (c*(t+j) + d*q)*hdet

theorem key {N l q : ℕ} {k : ℤ} (f : ModularForm (GlobalTheory.Hk.lev N l) k) (ρ : SL(2, ℤ))
    (hcN : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0) (hq : 0 < q) (j j' : ℕ) (Y : ℤ)
    (hY : ρ 0 1 = ρ 0 0 * j + j * j' * ρ 1 0 - j' * ρ 1 1 - q * Y) (τ : ℍ) :
    (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + j) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q)) * denom ρ τ ^ (-k) := by
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set γ : SL(2, ℤ) := ⟨gam (ρ 0 0) (ρ 0 1) (ρ 1 0) (ρ 1 1) j j' q Y,
    det_gam _ _ _ _ _ _ _ _ hdetZ hY⟩ with hγdef
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hN : ((ρ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdiv)
  have hl : ((ρ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdiv)
  have hγ : γ ∈ GlobalTheory.Hk.lev N l := by
    refine Subgroup.mem_inf.mpr ⟨(Gamma1_mem _ _).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩
    · have e : γ 0 0 = 1 + ρ 1 0 * (ρ 0 1 - ρ 0 1 * q - ρ 0 0 * j) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 1 = 1 + ρ 1 0 * (ρ 0 1 + ρ 1 1 * j' + Y) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hl]; ring
  have hpos : ∀ x : ℍ, ∀ n : ℕ, 0 < (((x : ℂ) + n) / q).im := by
    intro x n
    have := x.im_pos
    rw [Complex.div_natCast_im]; simp; positivity
  set w : ℍ := ofComplex (((τ : ℂ) + j) / q) with hwdef
  set z : ℍ := ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q) with hzdef
  have hwc : (w : ℂ) = ((τ : ℂ) + j) / q := by rw [hwdef, ofComplex_apply_of_im_pos (hpos τ j)]
  have hzc : (z : ℂ) = (((ρ • τ : ℍ) : ℂ) + j') / q := by
    rw [hzdef, ofComplex_apply_of_im_pos (hpos (ρ • τ) j')]
  have hu : ((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero ρ τ; rwa [ModularGroup.denom_apply] at this
  have hρτ : ((ρ • τ : ℍ) : ℂ) = (((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ)) /
      (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [coe_specialLinearGroup_apply]; simp
  have hwq : (w : ℂ) * q = τ + j := by rw [hwc]; field_simp
  have hzq : (z : ℂ) * q * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) =
      ((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ) + (j' : ℂ) * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [hzc, div_mul_cancel₀ _ hqC, hρτ, add_mul, div_mul_cancel₀ _ hu]
  have hdetC : ((ρ 0 0 : ℤ) : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - ((ρ 0 1 : ℤ) : ℂ) * ((ρ 1 0 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hdetZ
  have hYC : ((ρ 0 1 : ℤ) : ℂ) = ((ρ 0 0 : ℤ) : ℂ) * (j : ℂ) + (j : ℂ) * (j' : ℂ) * ((ρ 1 0 : ℤ) : ℂ)
      - (j' : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - (q : ℂ) * (Y : ℂ) := by exact_mod_cast hY
  obtain ⟨hA, hB⟩ := alg _ _ _ _ (Y : ℂ) (τ : ℂ) (w : ℂ) (z : ℂ) (j : ℂ) (j' : ℂ) (q : ℂ) hqC hdetC hYC hwq hzq
  have hγ10 : ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero γ z; rwa [ModularGroup.denom_apply] at this
  have hsm : ρ • w = γ • z := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [hγdef, gam, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hA, hB, mul_div_mul_left _ _ hu]
  have hden : denom ρ w = denom ρ τ * denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, ModularGroup.denom_apply, hB]
    simp only [hγdef, gam]
    simp
  rw [ModularForm.SL_slash_apply, hsm, SlashInvariantForm.slash_action_eqn_SL'' f hγ z, hden, mul_zpow]
  have h1 := denom_ne_zero ρ τ
  have h2 := denom_ne_zero γ z
  rw [zpow_neg, zpow_neg]
  field_simp

theorem cast_toNat_emod {q : ℕ} (hq : 0 < q) (x : ℤ) :
    (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (x : ZMod q) := by
  have h0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  rw [show (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (((x % (q : ℤ)).toNat : ℤ) : ZMod q) by
    push_cast; rfl, Int.toNat_of_nonneg h0, ZMod.intCast_mod]

theorem toNat_emod_lt {q : ℕ} (hq : 0 < q) (x : ℤ) : (x % (q : ℤ)).toNat < q := by
  have h1 : x % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  omega

theorem eq_of_cast_eq {q : ℕ} {i i' : ℕ} (hi : i < q) (hi' : i' < q)
    (h : (i : ZMod q) = (i' : ZMod q)) : i = i' := by
  haveI : NeZero q := ⟨by omega⟩
  rw [← ZMod.val_cast_of_lt hi, ← ZMod.val_cast_of_lt hi', h]

end GlobalTheory.Hk.UDia


open GlobalTheory.Hk.UDia in
theorem GlobalTheory.Hk.uOp_dia_comm : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime →
    q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q k d ρ _ _ hqp hqNl hρ f
  have hq : 0 < q := hqp.pos
  have hcN := hρ.1
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hcq : ((ρ 1 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by exact_mod_cast hqNl) hdiv)
  have had : ((ρ 0 0 : ℤ) : ZMod q) * ((ρ 1 1 : ℤ) : ZMod q) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod q)) hdetZ
    push_cast at h; rw [hcq] at h; linear_combination h
  set a : ℤ := ρ 0 0
  set b : ℤ := ρ 0 1
  set dd : ℤ := ρ 1 1
  let φ : ℕ → ℕ := fun i => ((a * (a * i - b)) % (q : ℤ)).toNat
  let ψ : ℕ → ℕ := fun i => ((dd * (dd * i + b)) % (q : ℤ)).toNat
  funext τ
  simp only [GlobalTheory.Hk.dia]
  rw [ModularForm.SL_slash_apply]
  simp only [GlobalTheory.Hk.uOp]
  rw [mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range q, (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + i) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + (φ i : ℕ)) / q)) * denom ρ τ ^ (-k) := by
    intro i _
    have hX : ((q : ℕ) : ℤ) ∣ a * i + i * (φ i) * ρ 1 0 - (φ i) * dd - b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [cast_toNat_emod hq, hcq]
      push_cast
      linear_combination (-(((a : ℤ) : ZMod q) * i - b)) * had
    obtain ⟨Y, hY⟩ := hX
    exact key f ρ hcN hq i (φ i) Y (by linear_combination -hY) τ
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' φ ψ ?_ ?_ ?_ ?_ ?_
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i - dd * b) * had
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i + a * b) * had
  · intro i _; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitSlashInvariantGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_transform {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (A B C D : ℤ) (hdet : A * D - B * C = 1)
    (hA : (A : ZMod N) = 1) (hD : (D : ZMod N) = 1) (hCN : (C : ZMod N) = 0)
    (hCl : (C : ZMod l) = 0) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex ((A * z + B) / (C * z + D))) = (C * z + D) ^ k * f (ofComplex z) := by
  let g : SL(2, ℤ) := ⟨!![A, B; C, D], by simp [Matrix.det_fin_two_of]; linarith⟩
  have hg : g ∈ lev N l := by
    refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N g).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩ <;> simpa [g]
  let w : ℍ := ⟨z, hz⟩
  have h1 := congrFun (hf g hg) w
  rw [SL_slash_apply] at h1
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = C * z + D := by
    have e1 : g 1 0 = C := rfl
    have e2 : g 1 1 = D := rfl
    have := (show denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = ((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℤ) by
      simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, w])
    rw [this, e1, e2]
  have hsm : ((g • w : ℍ) : ℂ) = (A * z + B) / (C * z + D) := by
    rw [specialLinearGroup_apply]; simp [g, w]
  have hne : (C * z + D : ℂ) ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  rw [hden] at h1
  have hw : ofComplex z = w := ofComplex_apply_of_im_pos hz
  rw [← hsm, ofComplex_apply, hw, ← h1, zpow_neg]
  field_simp

theorem lev_periodic {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex (z + 1)) = f (ofComplex z) := by
  have h := lev_transform hf 1 1 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp) z hz
  simpa using h

theorem sum_range_affine {q : ℕ} (hq : 0 < q) (F : ℤ → ℂ) (hF : Function.Periodic F q)
    (u v : ℤ) (hu : ∃ w : ZMod q, w * u = 1) :
    ∑ j ∈ Finset.range q, F (v + u * j) = ∑ j ∈ Finset.range q, F j := by
  haveI : NeZero q := ⟨hq.ne'⟩
  let G : ZMod q → ℂ := fun x => F (x.val : ℤ)
  have hFG : ∀ m : ℤ, F m = G m := by
    intro m
    simp only [G, ZMod.val_intCast]
    have := (hF.int_mul (m / q)) (m % q)
    rw [← this]; congr 1
    rw [Int.cast_id]; linear_combination (Int.mul_ediv_add_emod m q).symm
  have hsum : ∀ H : ZMod q → ℂ, ∑ j ∈ Finset.range q, H (j : ZMod q) = ∑ x, H x := by
    intro H
    symm
    refine Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro j _; exact Finset.mem_univ _
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro x _; rw [ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := hu
  have hbij : Function.Bijective (fun x : ZMod q => (v : ZMod q) + u * x) := by
    refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    have : (u : ZMod q) * x = u * y := add_left_cancel hxy
    calc x = w * (u * x) := by rw [← mul_assoc, hw, one_mul]
      _ = y := by rw [this, ← mul_assoc, hw, one_mul]
  calc ∑ j ∈ Finset.range q, F (v + u * j)
      = ∑ j ∈ Finset.range q, G ((v : ZMod q) + u * (j : ZMod q)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl
    _ = ∑ x, G ((v : ZMod q) + u * x) := hsum (fun x => G ((v : ZMod q) + u * x))
    _ = ∑ x, G x := hbij.sum_comp G
    _ = ∑ j ∈ Finset.range q, G (j : ZMod q) := (hsum G).symm
    _ = ∑ j ∈ Finset.range q, F j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl

theorem uOp_slash_lev : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    (∀ γ ∈ lev N l, f ∣[k] γ = f) → ∀ γ ∈ lev N l, uOp q f ∣[k] γ = uOp q f := by
  intro N l q k f _ _ hq hqNl hf γ hγ
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha, hd, hcN⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hqc : (q : ℤ) ∣ γ 1 0 := by
    rcases hq.dvd_mul.1 hqNl with h | h
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcN)
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h0)
  obtain ⟨t, ht⟩ := hqc
  funext τ
  rw [SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hsm : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    rw [specialLinearGroup_apply]; simp
  have hcd : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  set a := γ 0 0 with ha_def
  set b := γ 0 1 with hb_def
  set c := γ 1 0 with hc_def
  set d := γ 1 1 with hd_def
  let F : ℤ → ℂ := fun m => f (ofComplex (((τ : ℂ) + m) / q))
  have hzim : ∀ m : ℤ, 0 < (((τ : ℂ) + m) / q).im := by
    intro m
    have : (((τ : ℂ) + m) / q).im = τ.im / q := by simp [Complex.div_natCast_im]
    rw [this]; exact div_pos τ.im_pos hqpos
  have hper : Function.Periodic F (q : ℤ) := by
    intro m
    have e : ((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q = ((τ : ℂ) + m) / q + 1 := by
      push_cast; field_simp; ring
    show f (ofComplex (((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q)) = f (ofComplex (((τ : ℂ) + m) / q))
    rw [e]; exact lev_periodic hf _ (hzim m)
  have hterm : ∀ j : ℕ, f (ofComplex (((a * τ + b) / (c * τ + d) + j) / q)) =
      (c * τ + d) ^ k * F (d * b + d * d * j) := by
    intro j
    set j' : ℤ := d * b + d * d * j with hj'
    set e : ℤ := t * (-(b * b) - 2 * j * b * d - j * j * d * d) with he_def
    have he : e * q = b + j * d - (a + j * c) * j' := by
      rw [he_def, hj']
      linear_combination (b + j * d) * hdet + (b * b + 2 * j * b * d + j * j * d * d) * ht
    have heC : (e : ℂ) * q = b + j * d - (a + j * c) * j' := by exact_mod_cast he
    have h := lev_transform hf (a + j * c) e (q * c) (d - c * j')
      (by linear_combination hdet - c * he)
      (by push_cast; simp [ha, hcN]) (by push_cast; simp [hd, hcN]) (by push_cast; simp [hcN])
      (by push_cast; simp [h0]) _ (hzim j')
    have hCD : ((q * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + ((d - c * j' : ℤ) : ℂ) = c * τ + d := by
      push_cast; field_simp; ring
    rw [hCD] at h
    have harg : (((a + j * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + (e : ℂ)) / (c * τ + d) =
        ((a * τ + b) / (c * τ + d) + j) / q := by
      push_cast
      field_simp
      linear_combination heC
    rw [harg] at h
    exact h
  have hunit : ∃ w : ZMod q, w * ((d * d : ℤ) : ZMod q) = 1 := by
    refine ⟨(a : ZMod q) * a, ?_⟩
    have h := congrArg (Int.cast : ℤ → ZMod q) hdet
    rw [ht] at h
    push_cast at h
    rw [ZMod.natCast_self] at h
    push_cast
    linear_combination ((a : ZMod q) * d + 1) * h
  unfold uOp
  rw [hsm, hden]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_range_affine hq.pos F hper _ _ hunit]
  have hF : ∑ j ∈ Finset.range q, F j =
      ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q)) := by simp [F]
  rw [hF, zpow_neg]
  field_simp

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlRepresentativesRightMulPerm
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulFam_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l),
    ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  intro N l _ hl _ γ
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp γ.2
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  rw [CongruenceSubgroup.Gamma0_mem] at hγ0
  obtain ⟨ha1, hd1, hcN⟩ := hγ1
  set a : ℤ := mat γ 0 0 with ha
  set b : ℤ := mat γ 0 1 with hb
  set c : ℤ := mat γ 1 0 with hc
  set d : ℤ := mat γ 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := (γ : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at h
    exact h
  have hmat : mat γ = !![a, b; c, d] := Matrix.eta_fin_two _
  have hcl : (c : ZMod l) = 0 := hγ0
  have hcN' : (c : ZMod N) = 0 := hcN
  have ha1' : (a : ZMod N) = 1 := ha1
  have hd1' : (d : ZMod N) = 1 := hd1
  have had : (d : ZMod l) * a = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  let f : Fin l → Fin l := fun i => ⟨(((b + (i : ℕ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩
  have hf : ∀ i, (((f i : ℕ) : ℤ) : ZMod l) = (((b + (i : ℕ) * d) * d : ℤ) : ZMod l) := by
    intro i
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  have hinj : Function.Injective f := by
    intro i i' h
    have h2 := congrArg (fun x : Fin l => (((x : ℕ) : ℤ) : ZMod l)) h
    simp only [hf] at h2
    push_cast at h2
    have h3 : ((i : ℕ) : ZMod l) = ((i' : ℕ) : ZMod l) := by
      linear_combination (a * a) * h2 - ((i : ℕ) - (i' : ℕ) : ZMod l) * (d * a + 1) * had
    have h4 := congrArg ZMod.val h3
    rw [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt i'.2] at h4
    exact Fin.ext h4
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  set j : ℤ := ((f i : ℕ) : ℤ) with hj
  set x : ℤ := ((i : ℕ) : ℤ) with hx
  have hdvd : (l : ℤ) ∣ b + x * d - j * (a + x * c) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp
    have hj' := hf i
    rw [← hj] at hj'
    have hxc : (x : ZMod l) = ((i : ℕ) : ZMod l) := by rw [hx, Int.cast_natCast]
    push_cast
    rw [hj', hcl, hxc]
    push_cast
    linear_combination (-(b : ZMod l) - x * d) * had + (d : ZMod l) * (d * a - 1) * hxc
  obtain ⟨e, he⟩ := hdvd
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a + x * c, e; l * c, d - j * c]
  have hMdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨M, hMdet⟩
  have hg : g ∈ Lev N l := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · show ((a + x * c : ℤ) : ZMod N) = 1
        push_cast; rw [ha1', hcN']; ring
      · show ((d - j * c : ℤ) : ZMod N) = 1
        push_cast; rw [hd1', hcN']; ring
      · show (((l : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast; rw [hcN']; ring
    · rw [CongruenceSubgroup.Gamma0_mem]
      show (((l : ℤ) * c : ℤ) : ZMod l) = 0
      push_cast; simp
  refine ⟨⟨g, hg⟩, ?_⟩
  show ulFam l i * mat γ = M * ulFam l (f i)
  rw [hmat]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [ulFam, M, Matrix.mul_apply, Fin.sum_univ_two, ← hj, ← hx] <;>
    first | ring1 | linear_combination he

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_conj_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), IsDia N l d σ → γ ∈ lev N l →
    σ * γ * σ⁻¹ ∈ lev N l := by
  intro N l d σ γ hσ hγ
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hσN : σ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_right N l)) hc)
  have hσl : σ ∈ Gamma0 l := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_left l N)) hc)
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  refine Subgroup.mem_inf.2
    ⟨?_, (Gamma0 l).mul_mem ((Gamma0 l).mul_mem hσl hγ0) ((Gamma0 l).inv_mem hσl)⟩
  have hγN : γ ∈ Gamma0 N := ((Gamma1_mem N γ).1 hγ1).2.2
  set S : Gamma0 N := ⟨σ, hσN⟩
  set G : Gamma0 N := ⟨γ, hγN⟩
  have hG : G ∈ Gamma1' N := (Gamma1_to_Gamma0_mem G).2 ((Gamma1_mem N γ).1 hγ1)
  have hX : S * G * S⁻¹ ∈ Gamma1' N := by
    rw [Gamma1_mem'] at hG ⊢
    rw [map_mul, map_mul, hG, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have h := (Gamma1_to_Gamma0_mem _).1 hX
  exact (Gamma1_mem N _).2 h

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMaximalPowOfJetsVanishStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximal_pow_of_jets_vanish : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k), 2 ≤ N → Δ 0 1 = 1 → (∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) → (∃ π : A, Δ 1 π = 1) →
 ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  first | exact @GlobalTheory.mem_pow_of_jets_vanish | exact GlobalTheory.mem_pow_of_jets_vanish | (intros; apply GlobalTheory.mem_pow_of_jets_vanish <;> assumption)
end

