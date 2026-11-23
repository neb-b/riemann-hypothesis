module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.CharAbs
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isUnifAt_unif {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Formalism.L2.Host.IsUnifAt v (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (v.adicCompletion K)) := by
  have hiff : ∀ x y : v.adicCompletion K,
      ValuativeRel.valuation (v.adicCompletion K) x ≤ ValuativeRel.valuation (v.adicCompletion K) y ↔
        Valued.v x ≤ Valued.v y := by
    intro x y
    letI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ValuativeRel.isEquiv _ _ x y
  have hlt1 : ∀ x : v.adicCompletion K,
      ValuativeRel.valuation (v.adicCompletion K) x < 1 ↔ Valued.v x < 1 := by
    intro x
    have h := hiff 1 x
    rw [map_one, map_one] at h
    rw [lt_iff_not_ge, lt_iff_not_ge, h]
  have hdisc : ∀ a : WithZero (Multiplicative ℤ), a < 1 → a ≤ WithZero.exp (-1) := by
    intro a h
    rcases eq_or_ne a 0 with rfl | ha
    · exact zero_le'
    · rw [← WithZero.exp_log ha] at h ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
      rw [WithZero.exp_le_exp]
      omega
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = WithZero.exp (-1) := Formalism.L2.Host.unif_spec v
  have hex : ∃ p : (v.adicCompletion K)ˣ,
      ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) < 1 ∧
        ∀ x : v.adicCompletion K, ValuativeRel.valuation (v.adicCompletion K) x < 1 →
          ValuativeRel.valuation (v.adicCompletion K) x ≤
            ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) := by
    refine ⟨Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v), ?_, ?_⟩
    · rw [hlt1, hπ]
      exact hexp
    · intro x hx
      rw [hiff, hπ]
      exact hdisc _ ((hlt1 x).1 hx)
  obtain ⟨hu1, hu2⟩ := Classical.epsilon_spec hex
  unfold Formalism.L2.Host.IsUnifAt UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif
  apply le_antisymm
  · exact hdisc _ ((hlt1 _).1 hu1)
  · rw [← hπ, ← hiff]
    apply hu2
    rw [hlt1, hπ]
    exact hexp

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.charAbs :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.CharAbs := by
  intro K _ _ χ
  obtain ⟨s, hs⟩ := (GlobalTheory.HeckeNormPow.toQC χ).exists_norm_eq_rpow
  refine ⟨-s, fun v => ⟨GlobalTheory.HeckeComp.smooth_loc χ v, ?_⟩⟩
  have h1 := hs
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding v
      (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (v.adicCompletion K))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (isUnifAt_unif v),
    Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
section
noncomputable section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GroundTheory.Global.SemiLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private theorem equivV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (ValuativeRel.valuation (v.adicCompletion K)).IsEquiv
      (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact ValuativeRel.isEquiv _ _

private theorem le_of_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

private theorem v_unif {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((unif (v.adicCompletion K) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hs := Classical.epsilon_spec (p := fun p : (v.adicCompletion K)ˣ =>
      ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) < 1 ∧
      ∀ x : v.adicCompletion K, ValuativeRel.valuation (v.adicCompletion K) x < 1 →
        ValuativeRel.valuation (v.adicCompletion K) x ≤ ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K))
    ⟨Units.mk0 p hp0, (equivV v).lt_one_iff_lt_one.2 (by rw [Units.val_mk0, hp]; exact hlt), fun x hx =>
      ((equivV v) _ _).2 (by rw [Units.val_mk0, hp]; exact le_of_lt_one ((equivV v).lt_one_iff_lt_one.1 hx))⟩
  refine le_antisymm (le_of_lt_one ((equivV v).lt_one_iff_lt_one.1 hs.1)) ?_
  rw [← hp]
  exact ((equivV v) _ _).1 (hs.2 p ((equivV v).lt_one_iff_lt_one.2 (by rw [hp]; exact hlt)))

private theorem absNorm_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w := by
  obtain ⟨w, hw⟩ := w
  exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot

private theorem v_nm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) (x : (w.1.adicCompletion L)ˣ) :
    Valued.v ((nm w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = Valued.v (x : w.1.adicCompletion L) ^ fdeg w := by
  have hN := absNorm_eq v w
  obtain ⟨w, hw⟩ := w
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hw.over
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  apply GlobalTheory.NormValGen.valuation_eq_pow_of_norm_eq _ w _ x hm' _
  simpa [GroundTheory.Global.AdeleBaseChange.below, HeightOneSpectrum.under,
    Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hN

theorem normVal :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal := by
  intro K L _ _ _ _ _ v w μ
  have hu : ValuativeRel.valuation (v.adicCompletion K)
      ((nm w (unif (w.1.adicCompletion L)) * (unif (v.adicCompletion K) ^ fdeg w)⁻¹ : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := by
    rw [(equivV v).eq_one_iff_eq_one, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      map_inv₀, map_pow, v_nm, v_unif, v_unif]
    exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
  have hN := absNorm_eq v w
  refine ⟨fun hμ => ⟨fun x hx => hμ _ ?_, ?_⟩, fun hμ => ?_, ?_, hN⟩
  · rw [(equivV v).eq_one_iff_eq_one, v_nm, (equivV w.1).eq_one_iff_eq_one.1 hx, one_pow]
  · have h := hμ _ hu
    rwa [map_mul, map_inv, mul_inv_eq_one, map_pow] at h
  · have h := GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one μ hμ _ hu
    rw [map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_mul, norm_inv,
      norm_pow, mul_inv_eq_one₀ (pow_ne_zero _ (norm_ne_zero_iff.2 (Units.ne_zero _)))] at h
    exact h
  · refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at hN
    exact w.1.isPrime.ne_top hN

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped Classical

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unif_spec : valuation k (unif k : k) < 1 ∧
    ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (unif k : k) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact uniformizer_ne_zero (R := k) hx.symm
  have hex : ∃ p : kˣ, valuation k (p : k) < 1 ∧
      ∀ y : k, valuation k y < 1 → valuation k y ≤ valuation k (p : k) :=
    ⟨Units.mk0 x hx0, by
      simp only [Units.val_mk0, hx]
      exact ⟨uniformizer_lt_one, fun y hy => le_uniformizer_iff.2 hy⟩⟩
  exact Classical.epsilon_spec hex

private theorem val_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 unif_spec.1) (hp ▸ unif_spec.2 p (hp ▸ uniformizer_lt_one))

private theorem eq_of_unram (ξ ξ' : kˣ →* ℂˣ) (h : IsUnram (ξ * ξ'⁻¹)) (e : ξ (unif k) = ξ' (unif k)) : ξ = ξ' := by
  let ord (x : kˣ) : ℤ :=
    -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (x : k)))
  have ord_mul (x y : kˣ) : ord (x * y) = ord x + ord y := by
    simp only [ord, Units.val_mul, map_mul]
    rw [WithZero.log_mul (by simp) (by simp)]
    ring
  have ord_one : ord (unif k) = 1 := by
    set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
    have h0 : φ (uniformizer k) ≠ 0 := by simp
    have key : φ (uniformizer k) = WithZero.exp (-1) := by
      apply le_antisymm
      · have ht : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
        rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
        rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
        omega
      · have ht : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
          rw [le_uniformizer_iff, ← map_one φ.symm]
          exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
        simpa using φ.strictMono.monotone ht
    simp [ord, val_unif, φ, key]
  have val_of_ord_zero (x : kˣ) (hx : ord x = 0) : valuation k (x : k) = 1 := by
    set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
    have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
    have h1 : WithZero.log (φ (valuation k (x : k))) = 0 := neg_eq_zero.1 hx
    apply φ.strictMono.injective
    rw [map_one, ← WithZero.exp_log h0, h1, WithZero.exp_zero]
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  apply mul_inv_eq_one.mp
  refine MonoidHom.ext fun x => ?_
  have h0 : o (x / unif k ^ ord x) = 1 := by
    rw [_root_.map_div, map_zpow, show o (unif k) = .ofAdd 1 from congrArg Multiplicative.ofAdd ord_one,
      ← ofAdd_zsmul, smul_eq_mul, mul_one]
    exact div_self' _
  have hx := h _ (val_of_ord_zero _ (ofAdd_eq_one.mp h0))
  have he : (ξ * ξ'⁻¹) (unif k) = 1 := by
    simp [e]
  rw [_root_.map_div, map_zpow, he, one_zpow, div_one] at hx
  exact hx

private noncomputable def pfac (χ : kˣ →* ℂˣ) (y : IrrGL (k := k)) : ℂ[X] :=
  if h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * χ) then
    1 - C (((h.choose * χ) (unif k) : ℂˣ) : ℂ) * X else 1

private theorem pol_cons (y : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) :
    pol (y ::ₘ s) χ = pfac χ y * pol s χ := by
  simp only [pol, Multiset.map_cons, Multiset.prod_cons]
  rfl

private theorem pol_zero (χ : kˣ →* ℂˣ) : pol (0 : Multiset (IrrGL (k := k))) χ = 1 := by
  simp [pol]

private theorem fac_pos (χ ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) (hu : IsUnram (ξ * χ)) :
    pfac χ (IrrGL.ofChar ξ hξ) = 1 - C (((ξ * χ) (unif k) : ℂˣ) : ℂ) * X := by
  have h : ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * χ) :=
    ⟨ξ, ⟨hξ, rfl⟩, hu⟩
  unfold pfac
  rw [dite_eq_left h]
  obtain ⟨h', e⟩ := h.choose_spec.1
  rw [← IrrGL.ofChar_inj.1 e]

private theorem fac_neg (χ : kˣ →* ℂˣ) (y : IrrGL (k := k)) (h : ¬ ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)) :
    pfac χ y = 1 := by
  unfold pfac
  rw [dite_eq_right]
  rintro ⟨ξ, ⟨hξ, e⟩, hu⟩
  exact h ⟨ξ, hξ, e, hu⟩

private theorem fac_eval (χ : kˣ →* ℂˣ) (y : IrrGL (k := k)) : (pfac χ y).eval 0 = 1 := by
  unfold pfac
  split_ifs <;> simp

private theorem pol_eval (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) : (pol s χ).eval 0 = 1 := by
  induction s using Multiset.induction_on with
  | empty => rw [pol_zero, eval_one]
  | cons y s ih => rw [pol_cons, eval_mul, ih, fac_eval, mul_one]

private theorem natDegree_lin (a : ℂ) (ha : a ≠ 0) : (1 - C a * X : ℂ[X]).natDegree = 1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp [natDegree_C_mul_X _ ha]

private theorem pol_deg (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) : (pol s χ).natDegree = cnt s χ := by
  induction s using Multiset.induction_on with
  | empty => simp [pol_zero, cnt]
  | cons y s ih =>
    have hne : ∀ p : ℂ[X], p.eval 0 = 1 → p ≠ 0 := fun p hp h0 => by simp [h0] at hp
    rw [pol_cons, natDegree_mul (hne _ (fac_eval χ y)) (hne _ (pol_eval s χ)), ih]
    simp only [cnt, Multiset.filter_cons]
    by_cases hy : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)
    · obtain ⟨ξ, hξ, rfl, hu⟩ := hy
      rw [fac_pos χ ξ hξ hu, natDegree_lin _ (Units.ne_zero _), if_pos ⟨ξ, hξ, rfl, hu⟩,
        Multiset.card_add, Multiset.card_singleton]
    · rw [fac_neg χ y hy, if_neg hy, natDegree_one, zero_add, zero_add]

private theorem fac_root (χ : kˣ →* ℂˣ) (y : IrrGL (k := k)) (x : ℂ) : (pfac χ y).eval x = 0 ↔
    ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ) ∧ (((ξ * χ) (unif k) : ℂˣ) : ℂ) * x = 1 := by
  by_cases hy : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)
  · obtain ⟨ξ, hξ, rfl, hu⟩ := hy
    rw [fac_pos χ ξ hξ hu]
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_zero]
    constructor
    · intro h
      exact ⟨ξ, hξ, rfl, hu, h.symm⟩
    · rintro ⟨ξ', hξ', e, _, h⟩
      have hq := IrrGL.ofChar_inj.1 e
      subst hq
      exact h.symm
  · rw [fac_neg χ y hy]
    simp only [eval_one, one_ne_zero, false_iff]
    rintro ⟨ξ, hξ, e, hu, _⟩
    exact hy ⟨ξ, hξ, e, hu⟩

private theorem pol_root (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) (x : ℂ) : (pol s χ).eval x = 0 ↔
    ∃ ξ ∈ chars s, IsUnram (ξ * χ) ∧ (((ξ * χ) (unif k) : ℂˣ) : ℂ) * x = 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [pol_zero, eval_one, one_ne_zero, false_iff]
    rintro ⟨ξ, ⟨hξ, hm⟩, _⟩
    simp at hm
  | cons y s ih =>
    rw [pol_cons, eval_mul, mul_eq_zero, fac_root, ih]
    constructor
    · rintro (⟨ξ, hξ, rfl, hu, h⟩ | ⟨ξ, ⟨hξ, hm⟩, hu, h⟩)
      · exact ⟨ξ, ⟨hξ, Multiset.mem_cons.2 (Or.inl rfl)⟩, hu, h⟩
      · exact ⟨ξ, ⟨hξ, Multiset.mem_cons.2 (Or.inr hm)⟩, hu, h⟩
    · rintro ⟨ξ, ⟨hξ, hm⟩, hu, h⟩
      rcases Multiset.mem_cons.1 hm with e | hm
      · exact Or.inl ⟨ξ, hξ, e.symm, hu, h⟩
      · exact Or.inr ⟨ξ, ⟨hξ, hm⟩, hu, h⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unram_mul_iff (a μ : kˣ →* ℂˣ) (hμ : IsUnram μ) : IsUnram (a * μ) ↔ IsUnram a := by
  constructor
  · intro h x hx
    have h2 := h x hx
    rwa [MonoidHom.mul_apply, hμ x hx, mul_one] at h2
  · intro h x hx
    rw [MonoidHom.mul_apply, h x hx, hμ x hx, mul_one]

private theorem fac_comp (χ μ : kˣ →* ℂˣ) (hμ : IsUnram μ) (y : IrrGL (k := k)) :
    pfac (χ * μ) y = (pfac χ y).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  by_cases hy : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)
  · obtain ⟨ξ, hξ, rfl, hu⟩ := hy
    have hu' : IsUnram (ξ * (χ * μ)) := by
      rw [← mul_assoc ξ χ μ, unram_mul_iff _ _ hμ]
      exact hu
    rw [fac_pos _ ξ hξ hu', fac_pos _ ξ hξ hu, ← mul_assoc ξ χ μ, MonoidHom.mul_apply (ξ * χ) μ,
      Units.val_mul, C_mul, sub_comp, one_comp, mul_comp, C_comp, X_comp, mul_assoc]
  · have hy' : ¬ ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (χ * μ)) := by
      rintro ⟨ξ, hξ, e, hu⟩
      rw [← mul_assoc ξ χ μ, unram_mul_iff _ _ hμ] at hu
      exact hy ⟨ξ, hξ, e, hu⟩
    rw [fac_neg _ _ hy', fac_neg _ _ hy, one_comp]

private theorem pol_comp (s : Multiset (IrrGL (k := k))) (χ μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    pol s (χ * μ) = (pol s χ).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  induction s using Multiset.induction_on with
  | empty => rw [pol_zero, pol_zero, one_comp]
  | cons y s ih => rw [pol_cons, pol_cons, mul_comp, ih, fac_comp χ μ hμ]

end Loc

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.polFacts :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PolFacts := fun _ _ _ _ _ =>
  ⟨unif_spec, eq_of_unram, fun _ _ _ _ => IrrGL.ofChar_inj.1, fun s χ =>
    ⟨pol_eval s χ, pol_deg s χ, pol_root s χ, pol_comp s χ⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppSmo := by
  intro K _ _ _ n _ π π' h t v hw
  have e : π = π' := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC K n π π'
    (h.mono fun w ⟨B, h₁, h₂⟩ =>
      ⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π w B).1 h₁, (GlobalTheory.CuspRep.CG.hasSat_mk π' w B).1 h₂⟩))
  exact e ▸ hw
end

