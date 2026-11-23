module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffine
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isExp_comp_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l →
    (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) →
    (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) →
    IsExp ε f h → IsExp ε f' h' := by
  intro Ω _ ε f f' l m h h' hl hf hc hexp
  obtain ⟨⟨N, hN, hden⟩, C, hC⟩ := hexp
  have hl0 : l ≠ 0 := hl.ne'
  refine ⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩
  · intro s hs
    have hr : h.coeff (s / l) ≠ 0 := by
      intro h0
      apply hs
      have := hc (s / l)
      rw [div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero] at this
      exact (map_eq_zero ε).1 this
    obtain ⟨n, hn⟩ := hden _ hr
    refine ⟨n * l.num, ?_⟩
    have hs' : s = s / l * l := by field_simp
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hd0 : (l.den : ℚ) ≠ 0 := by exact_mod_cast l.den_pos.ne'
    rw [hs', hn]
    push_cast
    rw [← Rat.mul_den_eq_num l]
    field_simp
  · intro z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hlz : C < ((l : ℂ) * z + (m : ℂ)).im := by
      have h1 : C / l < z.im := lt_of_le_of_lt (le_max_left _ _) hz
      have h2 : C < z.im * l := (div_lt_iff₀ (by exact_mod_cast hl)).1 h1
      simpa [mul_comm] using h2
    rw [hf z hz0]
    have key := hC _ hlz
    rw [← (Equiv.mulRight₀ l hl0).hasSum_iff]
    convert key using 1
    funext r
    have he : (Equiv.mulRight₀ l hl0) r = r * l := rfl
    simp only [Function.comp, he, hc r]
    rw [mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_gal (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.exp (X.gal s f) = HahnSeries.map (X.exp f) (s : Ω →+* Ω) := by
  ext r; simp [X.gal_exp]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  rw [exp_gal, AlgHom.commutes, AlgHom.commutes]
  ext r
  have hC : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.single 0 c := fun c => by
    rw [HahnSeries.algebraMap_apply']
    simp [PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  simp only [HahnSeries.map_coeff, hC, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem map_mul_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) :=
  HahnSeries.map_mul (s : Ω →+* Ω).toNonUnitalRingHom

theorem map_sub_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r; simp

theorem theta_map (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (φ : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map φ (s : Ω →+* Ω)) = HahnSeries.map (theta q φ) (s : Ω →+* Ω) := by
  ext r; simp [theta]

theorem cgA_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (l n : ℕ) (x y : Ω)
    (h : CgA A l n x y) : CgA A l n (s x) (s y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨s z, (hA z).1 hz, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

theorem prim_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (φ : HahnSeries ℚ Ω)
    (h : Prim A φ) : Prim A (HahnSeries.map φ (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr, hu⟩ := h
  refine ⟨fun r => by simpa using (hA _).1 (h1 r), r, by simpa using hr, ?_⟩
  simpa [← map_inv₀] using (hA _).1 hu

theorem exists_root [IsAlgClosed Ω] (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) :
    ∃ (ζ : Ω) (d e : ℤ), IsPrimitiveRoot ζ M ∧ s ζ = ζ ^ d ∧ (d : ZMod M) * e = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hs : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hs.pow_eq_one
  have hc : i.Coprime M := (hζ.pow_iff_coprime hM i).1 (hi ▸ hs)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine ⟨ζ, i, u, hζ, by rw [zpow_natCast, hi], ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod M)) huv
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact_mod_cast this

theorem recip_zmod (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) (ζ : Ω) (hζ : IsPrimitiveRoot ζ M)
    (d e : ℤ) (hd : s ζ = ζ ^ d) (hde : (d : ZMod M) * e = 1) (δ δ' : SL(2, ℤ))
    (h00 : (en δ' 0 0 : ZMod M) = en δ 0 0) (h01 : (en δ' 0 1 : ZMod M) = e * en δ 0 1)
    (h10 : (en δ' 1 0 : ZMod M) = d * en δ 1 0) (h11 : (en δ' 1 1 : ZMod M) = en δ 1 1) :
    X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  apply X.recip M f hM hf ζ hζ s d hd δ' δ
  refine ⟨h00.symm, ?_, h10.symm, h11.symm⟩
  rw [h01, ← mul_assoc, hde, one_mul]

theorem inv_gal [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 M) f) : Inv X (CongruenceSubgroup.Gamma1 M) (X.gal s f) := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨M1, hM1, hlev, h00, h11, h10⟩ : ∃ M1 : ℕ, 0 < M1 ∧
      (∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f) ∧
      ((en γ 0 0 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 1 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 0 : ℤ) : ZMod M1) = 0 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      obtain ⟨M0, h0, hl⟩ := X.level f
      obtain ⟨a, b, c⟩ := hγ
      have a' : en γ 0 0 = 1 := by simpa [en] using a
      have b' : en γ 1 1 = 1 := by simpa [en] using b
      have c' : en γ 1 0 = 0 := by simpa [en] using c
      exact ⟨M0, h0, hl, by simp [a'], by simp [b'], by simp [c']⟩
    · refine ⟨M, h, fun g hg => hf g ?_, hγ⟩
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
  obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
  have hT : ModularGroup.T ^ (e * en γ 0 1) ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
  have key := recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde γ (ModularGroup.T ^ (e * en γ 0 1))
    (by simp [en, ModularGroup.coe_T_zpow]; exact h00.symm) (by simp [en, ModularGroup.coe_T_zpow])
    (by simp [en, ModularGroup.coe_T_zpow]; rw [show (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M1) = 0 from h10, mul_zero])
    (by simp [en, ModularGroup.coe_T_zpow]; exact h11.symm)
  rw [hf _ hT] at key
  exact key.symm

end GlobalTheory.ThGal

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {a b : ℕ} (h : a ∣ b) (x y : ℤ) (hxy : (x : ZMod b) = y) : (x : ZMod a) = y :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y a).2
    (dvd_trans (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff_dvd_sub x y b).1 hxy))

theorem exists_twist [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (N l n : ℕ) (hl : 0 < l) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f) (δ : SL(2, ℤ))
    (h1 : δ ∈ CongruenceSubgroup.Gamma1 N) (h2 : -δ ∈ CongruenceSubgroup.Gamma (l ^ n)) :
    ∃ δ' : SL(2, ℤ), δ' ∈ CongruenceSubgroup.Gamma1 N ∧ -δ' ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma_mem] at h2
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at h2
  obtain ⟨g00, g01, g10, g11⟩ := h2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain ⟨M0, h0, hlev⟩ := X.level f
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M0 h0
    obtain ⟨a, b, c⟩ := h1
    have a' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simpa using a
    have b' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simpa using b
    have c' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simpa using c
    refine ⟨ModularGroup.T ^ (e * en δ 0 1), ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
    · rw [CongruenceSubgroup.Gamma_mem]
      rw [a'] at g00
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ModularGroup.coe_T_zpow, en]
      refine ⟨by simpa using g00, ?_, by simp, by simpa using g00⟩
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_neg, Int.cast_mul]
      rw [mul_comm, ← neg_mul, g01, zero_mul]
    · apply recip_zmod X s M0 h0 f hlev ζ hζ d e hd hde δ
      · simp [en, ModularGroup.coe_T_zpow, a']
      · simp [en, ModularGroup.coe_T_zpow]
      · simp [en, ModularGroup.coe_T_zpow, c']
      · simp [en, ModularGroup.coe_T_zpow, b']
  · set M1 := N * l ^ n with hM1def
    have hM1 : 0 < M1 := Nat.mul_pos hN (pow_pos hl n)
    have hlev : ∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f := by
      intro g hg
      apply hf g
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
    let m : Matrix (Fin 2) (Fin 2) (ZMod M1) :=
      !![(en δ 0 0 : ZMod M1), e * en δ 0 1; d * en δ 1 0, en δ 1 1]
    have hm : m.det = 1 := by
      rw [Matrix.det_fin_two_of]
      have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
        have := δ.det_coe; rw [Matrix.det_fin_two] at this; exact this
      have := congrArg (fun z : ℤ => (z : ZMod M1)) hdet
      push_cast at this
      linear_combination this - ((en δ 0 1 : ZMod M1) * en δ 1 0) * hde
    obtain ⟨δ', hδ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M1 ⟨m, hm⟩
    have he : ∀ i j, (((δ' : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M1) = m i j := fun i j => by
      have := congrArg (fun g : SL(2, ZMod M1) => (g : Matrix (Fin 2) (Fin 2) (ZMod M1)) i j) hδ'
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    have e00 : (en δ' 0 0 : ZMod M1) = en δ 0 0 := he 0 0
    have e01 : (en δ' 0 1 : ZMod M1) = ((e * en δ 0 1 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 0 1
    have e10 : (en δ' 1 0 : ZMod M1) = ((d * en δ 1 0 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 1 0
    have e11 : (en δ' 1 1 : ZMod M1) = en δ 1 1 := he 1 1
    have dN : N ∣ M1 := Dvd.intro _ rfl
    have dl : l ^ n ∣ M1 := Dvd.intro_left _ rfl
    refine ⟨δ', ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      obtain ⟨a, b, c⟩ := h1
      refine ⟨?_, ?_, ?_⟩
      · exact (cast_of_dvd dN _ _ e00).trans a
      · exact (cast_of_dvd dN _ _ e11).trans b
      · refine (cast_of_dvd dN _ _ e10).trans ?_
        rw [Int.cast_mul, show ((en δ 1 0 : ℤ) : ZMod N) = 0 from c, mul_zero]
    · rw [CongruenceSubgroup.Gamma_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod (l ^ n)) = en δ 0 0 from cast_of_dvd dl _ _ e00]
        exact g00
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod (l ^ n)) = ((e * en δ 0 1 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e01]
        push_cast; rw [← mul_neg]; rw [show -((en δ 0 1 : ℤ) : ZMod (l ^ n)) = 0 from g01, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (l ^ n)) = ((d * en δ 1 0 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e10]
        push_cast; rw [← mul_neg]; rw [show -((en δ 1 0 : ℤ) : ZMod (l ^ n)) = 0 from g10, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (l ^ n)) = en δ 1 1 from cast_of_dvd dl _ _ e11]
        exact g11
    · exact recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde δ δ' e00 (by rw [e01]; push_cast; rfl)
        (by rw [e10]; push_cast; rfl) e11

end GlobalTheory.ThGal

namespace GlobalTheory

open GlobalTheory.KZ GlobalTheory.Glue

theorem isThB_galB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ ε X A N l _ n w s _ hA b _ φ hb
  obtain ⟨f, hfI, hcls, hδ, hdl⟩ := hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
  refine ⟨Units.map (X.gal s).toMonoidHom f, ?_, ?_, ?_, ?_⟩
  · rw [hf]; exact ThGal.inv_gal X s _ _ hfI
  · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
      funext i; fin_cases i <;> simp
    have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
    rw [hu] at hg
    rw [AdicCompletion.eval_apply] at hcls
    rw [hg, AdicCompletion.eval_apply, Tower.kmap]
    erw [AdicCompletion.map_val_apply]
    rw [hcls]
    simp [Tower.cls, LinearMap.reduceModIdeal_apply]
  · intro δ hδ1 hδ2
    obtain ⟨δ', h1, h2, hrec⟩ := ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
    obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
    refine ⟨X.gal s g, ThGal.inv_gal X s _ _ hg, ?_⟩
    rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · obtain ⟨hφ, a, c, κ, hκ, hfa, ha, hc, hcg⟩ := hdl
    refine ⟨fun r => by simpa using (hA _).1 (hφ r), X.gal s a, X.gal s c, s κ, by simpa using hκ, ?_, ?_, ?_, ?_⟩
    · rw [hf, ← ThGal.gal_algebraMap, ← map_mul, ← map_mul, hfa]
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ ha
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ hc
    · intro r
      rw [ThGal.exp_gal, ThGal.exp_gal, ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ThGal.theta_map, ThGal.theta_map,
        ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ← ThGal.map_sub_gal, HahnSeries.map_coeff, HahnSeries.map_coeff]
      exact ThGal.cgA_map A s hA l n _ _ (hcg r)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescale
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.DlRescale

def mulN (N : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (N : ℚ)

theorem mulN_le (N : ℕ) (hN : 0 < N) (g g' : ℚ) : mulN N g ≤ mulN N g' ↔ g ≤ g' := by
  have : (0:ℚ) < N := by exact_mod_cast hN
  simp [mulN, mul_le_mul_iff_of_pos_left this]

theorem mulN_inj (N : ℕ) (hN : 0 < N) : Function.Injective (mulN N) := fun g g' h =>
  le_antisymm ((mulN_le N hN g g').1 h.le) ((mulN_le N hN g' g).1 h.ge)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def resc (N : ℕ) (hN : 0 < N) : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω :=
  HahnSeries.embDomainRingHom (mulN N) (mulN_inj N hN) (mulN_le N hN)

theorem resc_coeff (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) (r : ℚ) :
    (resc N hN ψ).coeff r = ψ.coeff (r / N) := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : r = mulN N (r / N) := by simp [mulN]; field_simp
  conv_lhs => rw [e]
  simp only [resc, HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (f := ⟨⟨mulN N, mulN_inj N hN⟩, mulN_le N hN _ _⟩)

theorem forall_div (N : ℕ) (hN : 0 < N) (Q : ℚ → Prop) : (∀ r : ℚ, Q (r / N)) ↔ ∀ r, Q r := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun h r => ?_, fun h r => h _⟩
  have := h (N * r)
  rwa [mul_div_cancel_left₀ r hN'] at this

theorem theta_resc (N : ℕ) (hN : 0 < N) (s : ℚ) (ψ : HahnSeries ℚ Ω) :
    theta (s / N) (resc N hN ψ) = resc N hN (theta s ψ) := by
  ext r
  simp only [theta, resc_coeff]
  congr 2
  ring

theorem prim_resc (A : ValuationSubring Ω) (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) :
    Prim A (resc N hN ψ) ↔ Prim A ψ := by
  unfold Prim
  simp only [resc_coeff]
  rw [forall_div N hN (fun r => ψ.coeff r ∈ A)]
  constructor
  · rintro ⟨h1, r, h2, h3⟩; exact ⟨h1, r / N, h2, h3⟩
  · rintro ⟨h1, r, h2, h3⟩
    have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨h1, N * r, ?_⟩
    rw [mul_div_cancel_left₀ r hN']; exact ⟨h2, h3⟩

theorem eOm_zero (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

theorem exp_sl_diag (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) (hN : 0 < N) (u : X.K) :
    X.exp (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) u) = resc N hN (X.exp u) := by
  have hdet : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hN
  have e00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext r
  rw [resc_coeff]
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) e10 u (r / N)
  rw [e00, e01, e11, mul_zero, zero_div, eOm_zero, one_mul, div_one, div_mul_cancel₀ r hN'] at h
  exact h

end GlobalTheory.DlRescale

end

open GlobalTheory.DlRescale in
theorem GlobalTheory.Glue.isDl_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  intro Ω _ _ _ ε X _ l _ A _ n N s f φ φ' hN hφ
  have hφ' : φ' = resc N hN φ := by ext r; rw [hφ, resc_coeff]
  subst hφ'
  have hexp := exp_sl_diag ε X N hN
  set g := toGQ !![(N : ℤ), 0; 0, 1]
  have key : ∀ a b : X.K, (∀ r, CgA A l n ((resc N hN φ * X.exp (X.sl g a) * X.exp (X.sl g b)).coeff r)
      ((theta (s / N) (X.exp (X.sl g a)) * X.exp (X.sl g b) - X.exp (X.sl g a) * theta (s / N) (X.exp (X.sl g b))).coeff r)) ↔
      ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r) := by
    intro a b
    simp only [hexp, theta_resc, ← map_mul, ← map_sub, resc_coeff]
    exact forall_div N hN (fun r => CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r))
  have hA : (∀ r, (resc N hN φ).coeff r ∈ A) ↔ ∀ r, φ.coeff r ∈ A := by
    simp only [resc_coeff]; exact forall_div N hN (fun r => φ.coeff r ∈ A)
  constructor
  · rintro ⟨h0, a, b, κ, hκ, hfb, pa, pb, hc⟩
    refine ⟨hA.2 h0, X.sl g a, X.sl g b, κ, hκ, ?_, ?_, ?_, (key a b).2 hc⟩
    · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
    · rw [hexp]; exact (prim_resc A N hN _).2 pa
    · rw [hexp]; exact (prim_resc A N hN _).2 pb
  · rintro ⟨h0, a', b', κ, hκ, hfb, pa, pb, hc⟩
    obtain ⟨a, rfl⟩ := (X.sl g).surjective a'
    obtain ⟨b, rfl⟩ := (X.sl g).surjective b'
    refine ⟨hA.1 h0, a, b, κ, hκ, ?_, ?_, ?_, (key a b).1 hc⟩
    · apply (X.sl g).injective
      rw [map_mul, map_mul, AlgEquiv.commutes]; exact hfb
    · rw [hexp] at pa; exact (prim_resc A N hN _).1 pa
    · rw [hexp] at pb; exact (prim_resc A N hN _).1 pb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPrimitiveRootEOmLevel
section
noncomputable section

namespace GlobalTheory.Glue.Roots

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem eOm_pow (ε : Ω →+* ℂ) (x : ℚ) (n : ℕ) : eOm ε x ^ n = eOm ε (n * x) := by
  apply ε.injective
  rw [map_pow, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem isPrimitiveRoot_eOm_inv (ε : Ω →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (eOm ε (1 / (n : ℚ))) n := by
  apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ ε.injective
  rw [eOm_spec ε ε.injective]
  convert Complex.isPrimitiveRoot_exp n hn using 2
  push_cast; ring

theorem isPrimitiveRoot_zt (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (zt ε l m) (l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (pow_ne_zero m hl)
  rwa [Nat.cast_pow] at h

theorem zt_add_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m k : ℕ) :
    zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  rw [zt, zt, eOm_pow]
  congr 1; push_cast; field_simp; ring

theorem zt_succ_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    zt ε l (m + 1) ^ l = zt ε l m := by
  simpa using zt_add_pow ε hl m 1

theorem eOm_level_pow (ε : Ω →+* ℂ) {N : ℕ} (hN : N ≠ 0) (l m : ℕ) :
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = zt ε l m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  rw [zt, eOm_pow]
  congr 1
  rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]

theorem isPrimitiveRoot_eOm_level (ε : Ω →+* ℂ) {N l : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (mul_ne_zero hN (pow_ne_zero m hl))
  rwa [Nat.cast_mul, Nat.cast_pow] at h

theorem eOm_isPrimitiveRoot_compatible : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε →
    ∀ (l : ℕ), l.Prime → ∀ (N : ℕ), 0 < N → ∀ m : ℕ,
    IsPrimitiveRoot (eOm ε (1 / (l : ℚ) ^ m)) (l ^ m) ∧ eOm ε (1 / (l : ℚ) ^ (m + 1)) ^ l = eOm ε (1 / (l : ℚ) ^ m) ∧
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) ∧
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = eOm ε (1 / (l : ℚ) ^ m) := by
  intro Ω _ _ _ ε _ l hl N hN m
  have hl0 : l ≠ 0 := hl.ne_zero
  have hN0 : N ≠ 0 := hN.ne'
  exact ⟨isPrimitiveRoot_zt ε hl0 m, zt_succ_pow ε hl0 m, isPrimitiveRoot_eOm_level ε hN0 hl0 m, eOm_level_pow ε hN0 l m⟩

end GlobalTheory.Glue.Roots
end
end

