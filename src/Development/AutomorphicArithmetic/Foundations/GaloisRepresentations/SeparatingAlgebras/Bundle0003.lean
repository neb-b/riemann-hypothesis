module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
public import GroundTheory.AutomorphicForms.Bundle0026
public import GroundTheory.AutomorphicForms.Cartan

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DensCont
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_val {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

private lemma pt_cont {n : ℕ} (i : Fin n) :
    Continuous fun θ : Fin n → UnitAddCircle => ((pt θ i : ℂˣ) : ℂ) := by
  simp only [pt_val]
  fun_prop

private lemma pt_norm {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ‖((pt θ i : ℂˣ) : ℂ)‖ = 1 := by
  rw [pt_val]
  exact Circle.norm_coe _

private lemma half_cont {X : Type*} [TopologicalSpace X] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ}
    (u : X → Fin n → ℂˣ) (hc : ∀ i, Continuous fun x => ((u x i : ℂˣ) : ℂ))
    (hn : ∀ x i, ‖((u x i : ℂˣ) : ℂ)‖ = 1) :
    Continuous fun x => half (t : ℂ) (u x) := by
  unfold half
  refine continuous_finsetProd _ (fun p _ => ?_)
  have h1 := hc p.1
  have h2 := hc p.2
  have hne : ∀ x, ((u x p.2 : ℂˣ) : ℂ) ≠ 0 := fun x => Units.ne_zero _
  have hq : Continuous fun x => ((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ) := h1.div h2 hne
  refine (continuous_const.sub hq).div (continuous_const.sub (continuous_const.mul hq)) (fun x => ?_)
  intro h
  have hnq : ‖((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ)‖ = 1 := by
    rw [norm_div, hn, hn, div_one]
  have h' := congrArg norm (sub_eq_zero.mp h).symm
  rw [norm_one, norm_mul, hnq, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at h'
  linarith

theorem UpperTheory.Gal.Gen.densCont_pf :
    UpperTheory.Gal.Gen.DensCont := by
  intro n t ht0 ht1
  have hinvc : ∀ i, Continuous fun θ : Fin n → UnitAddCircle => (((pt θ)⁻¹ i : ℂˣ) : ℂ) := by
    intro i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact (pt_cont i).inv₀ (fun θ => Units.ne_zero _)
  have hinvn : ∀ (θ : Fin n → UnitAddCircle) i, ‖(((pt θ)⁻¹ i : ℂˣ) : ℂ)‖ = 1 := by
    intro θ i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, pt_norm, inv_one]
  refine ⟨half_cont ht0 ht1 _ pt_cont pt_norm, ?_, ?_, pt_norm⟩
  · exact (half_cont ht0 ht1 _ pt_cont pt_norm).mul (half_cont ht0 ht1 _ hinvc hinvn)
  · intro p
    simp only [evalAt_apply, monomialChar_apply, Units.val_zpow_eq_zpow_val]
    unfold Finsupp.sum
    refine continuous_finsetSum _ (fun l _ => ?_)
    refine continuous_const.mul (continuous_finsetProd _ (fun i _ => ?_))
    exact (pt_cont i).zpow₀ _ (fun θ => Or.inl (Units.ne_zero _))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DensSymm
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private noncomputable def densPhi {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) (p : Fin n × Fin n) : ℂ :=
  (1 - (z p.1 : ℂ) / (z p.2 : ℂ)) / (1 - t * ((z p.1 : ℂ) / (z p.2 : ℂ)))

private lemma half_inv_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    half t z⁻¹ = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), densPhi t z p := by
  unfold half
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    have h : (((z⁻¹) p.1 : ℂˣ) : ℂ) / (((z⁻¹) p.2 : ℂˣ) : ℂ) = (z p.2 : ℂ) / (z p.1 : ℂ) := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
      rw [inv_div_inv]
    simp only [densPhi, Prod.fst_swap, Prod.snd_swap, h]

private lemma dens_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    dens t z = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2), densPhi t z p := by
  have h3 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      prs n ∪ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, prs]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim (fun h => h.ne) (fun h => h.ne')⟩
  have hd : Disjoint (prs n) ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prs] at hp hq
    exact lt_asymm hp hq
  rw [h3, Finset.prod_union hd, ← half_inv_eq]
  rfl

theorem UpperTheory.Gal.Gen.densSymm :
    UpperTheory.Gal.Gen.DensSymm := by
  intro n t z σ
  rw [dens_eq, dens_eq]
  refine Finset.prod_nbij' (Prod.map σ σ) (Prod.map σ.symm σ.symm) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp
  · intro p _
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConj
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem rhoPair_dual {n : ℕ} (l : Fin n → ℤ) :
    rhoPair (fun i => -l (Fin.rev i)) = rhoPair l := by
  unfold rhoPair
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  rw [Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast
  ring

private theorem conj_vPoly (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (vPoly n (t : ℂ)) = vPoly n (t : ℂ) := by
  unfold vPoly
  simp [map_prod, map_div₀]

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.Gen.gammaConj_pf :
    UpperTheory.Gal.Gen.RConj → UpperTheory.Gal.Gen.GammaConj := by
  intro hR F _ _ _ _ n _ _ μ _
  show ∀ z, _
  intro z hinj hz g
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have htp : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hl' : Antitone (fun i : Fin n => -l (Fin.rev i)) := by
    intro i j hij
    show -l (Fin.rev j) ≤ -l (Fin.rev i)
    exact neg_le_neg (hl (Fin.rev_le_rev.mpr hij))
  have hinv : (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      k₂⁻¹ * Iwasawa.torusPow F n (-l) * k₁⁻¹ := by
    rw [Iwasawa.torusPow_neg, ← htp]
    group
  have hcomp : Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)) =
      Iwasawa.torusPow F n ((-l) ∘ Fin.revPerm) := rfl
  have hZinv : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      zonalSpherical μ z (Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i))) := by
    rw [hinv, zonalSpherical_mul_right z _ (inv_mem hk₁), zonalSpherical_mul_left z (inv_mem hk₂),
      hcomp, zonalSpherical_torusPow_comp]
  have hZ : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      zonalSpherical μ z (Iwasawa.torusPow F n l) := by
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, htp]
  rw [hZinv, hZ]
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hcast : (((qF F : ℝ)⁻¹ : ℝ) : ℂ) = ((qF F : ℂ))⁻¹ := by simp
  have m1 := macdonald_formula_hlR (μ := μ) z hl'
  have m2 := macdonald_formula_hlR (μ := μ) z hl
  have hc := hR n ((qF F : ℝ))⁻¹ l z hinj hz
  rw [hcast] at hc
  have hhm : halfModulus F (fun i : Fin n => -l (Fin.rev i)) = halfModulus F l := by
    rw [halfModulus_eq, halfModulus_eq, rhoPair_dual]
  have hhmr : (starRingEnd ℂ) (halfModulus F l) = halfModulus F l := by
    rw [halfModulus_eq, map_zpow₀]
    simp [sqrtQ]
  have hvr : (starRingEnd ℂ) (vPoly n ((qF F : ℂ))⁻¹) = vPoly n ((qF F : ℂ))⁻¹ := by
    rw [← hcast]
    exact conj_vPoly n _
  apply mul_left_cancel₀ hv
  rw [m1, hhm, hc]
  have m2c := congrArg (starRingEnd ℂ) m2
  rw [map_mul, map_mul, hvr, hhmr] at m2c
  rw [m2c]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaInt
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem qInv_props (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 0 ≤ ((qF F : ℝ))⁻¹ ∧ ((qF F : ℝ))⁻¹ < 1 := by
  have h : 1 < qF F := by
    haveI := fintypeResidue' (F := F)
    exact Finite.one_lt_card
  have h' : (1 : ℝ) < (qF F : ℝ) := by exact_mod_cast h
  exact ⟨by positivity, inv_lt_one_of_one_lt₀ h'⟩

theorem UpperTheory.Gal.Gen.gammaInt_pf :
    UpperTheory.Gal.Gen.RInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.GammaInt := by
  intro hR hD F _ _ _ _ n _ _ μ _ g
  obtain ⟨ht0, ht1⟩ := qInv_props F
  have htc : (((((qF F : ℝ))⁻¹ : ℝ)) : ℂ) = ((qF F : ℂ))⁻¹ := by push_cast; rfl
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hint := hR n _ ht0 ht1
  have hcont := (hD n _ ht0 ht1).2.2.1
  rw [htc] at hint
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have hdt : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hΓ : ∀ z : Fin n → ℂˣ, zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * (halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l)) := by
    intro z
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, hdt,
      eq_inv_mul_iff_mul_eq₀ hv]
    exact macdonald_formula_hlR z hl
  refine ⟨?_, ?_⟩
  · simp only [hΓ]
    exact continuous_const.mul (continuous_const.mul (hcont _))
  · have hI : ∫ θ : Fin n → UnitAddCircle,
        zonalSpherical μ (pt θ) (k₁ * Cartan.diagPow F n l * k₂) * dens ((qF F : ℂ))⁻¹ (pt θ) =
        (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * halfModulus F l *
          ∫ θ : Fin n → UnitAddCircle, evalAt (pt θ) (hlR ((qF F : ℂ))⁻¹ l) * dens ((qF F : ℂ))⁻¹ (pt θ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hΓ]
      ring
    rw [hI, hint l hl, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    have hdom0 : Cartan.IsDominant (0 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have hd0 : Cartan.diagPow F n 0 = 1 := by
      apply Units.ext
      rw [Cartan.coe_diagPow]
      simp
    by_cases h0 : l = 0
    · subst h0
      rw [if_pos rfl, halfModulus_zero, one_mul, if_pos]
      rw [hd0, mul_one]
      exact mul_mem hk₁ hk₂
    · rw [if_neg h0, mul_zero, if_neg]
      intro hg
      have hk : k₁⁻¹ * (k₁ * Cartan.diagPow F n l * k₂) * k₂⁻¹ ∈ GLnLocal.integralGL F n :=
        mul_mem (mul_mem (inv_mem hk₁) hg) (inv_mem hk₂)
      refine h0 (Cartan.eq_of_mul_diagPow_eq F n hdom0 hl hk (one_mem _) ?_).symm
      rw [hd0]
      group
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HalfCancel
section
noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

private lemma factor_eq {a b t : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (hat : a - t * b ≠ 0) :
    (a - t * b) / (a - b) * ((1 - a⁻¹ / b⁻¹) / (1 - t * (a⁻¹ / b⁻¹))) = 1 := by
  have e : a⁻¹ / b⁻¹ = b / a := by field_simp
  rw [e]
  have h1 : 1 - b / a = (a - b) / a := by field_simp
  have h2 : 1 - t * (b / a) = (a - t * b) / a := by field_simp
  rw [h1, h2]
  field_simp

private lemma half_cancel (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (w : Fin n → ℂˣ)
    (hw : Function.Injective w) (hn : ∀ i, ‖(w i : ℂ)‖ = 1) :
    (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) / ((w p.1 : ℂ) - (w p.2 : ℂ))) *
      half (t : ℂ) w⁻¹ = 1 := by
  unfold half
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun p hp => ?_)
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hne : p.1 ≠ p.2 := hp.ne
  refine factor_eq (w p.1).ne_zero (w p.2).ne_zero ?_ ?_
  · intro h
    exact hne (hw (Units.ext (sub_eq_zero.mp h)))
  · intro h
    have h' : (w p.1 : ℂ) = (t : ℂ) * (w p.2 : ℂ) := sub_eq_zero.mp h
    have hn' := congrArg norm h'
    rw [norm_mul, hn, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at hn'
    linarith

theorem rDens_pf : RFormula → DensSymm → RDens := by
  intro hR hS n t h0 h1 l z hz hn
  rw [hR n (t : ℂ) l z hz, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw : Function.Injective (z ∘ σ) := hz.comp σ.injective
  have hwn : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hn (σ i)
  have hc := half_cancel n t h0 h1 (z ∘ σ) hw hwn
  rw [← hS n (t : ℂ) z σ]
  unfold dens
  simp only [Function.comp_apply] at hc
  calc _ = monomialChar l (z ∘ σ) * half (t : ℂ) (z ∘ σ) * ((∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (t : ℂ) * (z (σ p.2) : ℂ)) / ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ))) * half (t : ℂ) (z ∘ σ)⁻¹) := by ring
    _ = _ := by rw [hc, mul_one]

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HalfInt
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_shift {n : ℕ} (c : ℤ) (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) :
    pt ((fun i : Fin n => (c - ((i : ℕ) : ℤ)) • s) + θ) =
      fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i := by
  funext i
  simp only [pt, Pi.add_apply, AddCircle.toCircle_add, AddCircle.toCircle_zsmul, map_mul, map_zpow]

private lemma prod_zpow_sum {ι : Type*} (S : Finset ι) (u : ℂˣ) (f : ι → ℤ) :
    ∏ i ∈ S, u ^ f i = u ^ ∑ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private lemma monoChar_shift {n : ℕ} (l : Fin n → ℤ) (c : ℤ) (m : ℕ)
    (hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) (u : ℂˣ) :
    monomialChar l (fun i : Fin n => u ^ (c - ((i : ℕ) : ℤ))) = (u : ℂ) ^ m := by
  rw [monomialChar_apply, ← Units.coe_prod]
  have h : ∏ i : Fin n, (u ^ (c - ((i : ℕ) : ℤ))) ^ l i = u ^ (m : ℤ) := by
    rw [← hm, ← prod_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, mul_comm]
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val]

private lemma key {n : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hM : MeanVal) (hD : DensCont)
    (l : Fin n → ℤ) (c : ℤ) (m : ℕ) (hcm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) :
    ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * half (t : ℂ) (pt θ) =
      ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * (if m = 0 then 1 else 0) := by
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨hhalf, -, hev, hnorm⟩ := hD n t ht0 ht1
  have hmono : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have h := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using h
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hFc : Continuous F := hmono.mul hhalf
  let a : UnitAddCircle → Fin n → UnitAddCircle := fun s i => (c - ((i : ℕ) : ℤ)) • s
  have ha : Continuous a := continuous_pi fun i => continuous_zsmul _
  have hshift : ∀ s, ∫ θ, F (a s + θ) = ∫ θ, F θ := fun s => integral_add_left_eq_self F (a s)
  have hG : Continuous (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ)) :=
    hFc.comp ((ha.comp continuous_fst).add continuous_snd)
  have hint : Integrable (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ))
      ((volume : Measure UnitAddCircle).prod (volume : Measure (Fin n → UnitAddCircle))) :=
    hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ θ, F θ = ∫ s : UnitAddCircle, ∫ θ, F (a s + θ) := by
    simp only [hshift, integral_const, probReal_univ, one_smul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp only
  have hpt : ∀ s, pt (a s + θ) = (fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ))) * pt θ := by
    intro s
    rw [pt_shift]
    rfl
  simp only [hF, hpt, map_mul, monoChar_shift l c m hcm]
  have hz := hM n t ht0 ht1 (pt θ) (hnorm θ) c m
  have hcoe : ∀ s : UnitAddCircle, ((Circle.toUnits (AddCircle.toCircle s) : ℂˣ) : ℂ) = (AddCircle.toCircle s : ℂ) :=
    fun s => rfl
  calc _ = ∫ s : UnitAddCircle, monomialChar l (pt θ) * ((AddCircle.toCircle s : ℂ) ^ m *
        half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i)) := by
        congr 1
        funext s
        rw [hcoe, mul_comm (_ ^ m), mul_assoc]
        rfl
    _ = _ := by rw [integral_const_mul, hz]

theorem UpperTheory.Gal.Gen.halfInt_pf :
    UpperTheory.Gal.Gen.WtPos → UpperTheory.Gal.Gen.MeanVal → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.HalfInt := by
  intro hW hM hD n t ht0 ht1 l hl
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  by_cases h0 : l = 0
  · subst h0
    rw [key t ht0 ht1 hM hD (0 : Fin n → ℤ) 0 0 (by simp)]
    simp [monomialChar_zero]
  · obtain ⟨c, hc⟩ := hW n l hl h0
    have hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = ((∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat : ℤ) :=
      (Int.toNat_of_nonneg hc.le).symm
    rw [key t ht0 ht1 hM hD l c _ hm]
    have hne : (∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat ≠ 0 := by omega
    simp [hne, h0]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.InjAEPf
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.injAE_pf :
    UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.InjAE := by
  intro hN n
  have h : ∀ i j : Fin n, ∀ᵐ θ : Fin n → UnitAddCircle, i ≠ j → pt θ i ≠ pt θ j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun θ h => absurd hij h)
    · have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun e => hij (MvPolynomial.X_injective e))
      filter_upwards [hN n _ hp] with θ hθ _ e
      apply hθ
      simp [e]
  have h2 : ∀ᵐ θ : Fin n → UnitAddCircle, ∀ i j : Fin n, i ≠ j → pt θ i ≠ pt θ j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j
  filter_upwards [h2] with θ hθ i j e
  by_contra hne
  exact hθ i j hne e
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PairTerm
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem mono_term {n : ℕ} (l : Fin n → ℤ) (w : Fin n → ℂˣ) (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    monomialChar (fun i => -l (Fin.rev i)) (w ∘ Fin.revPerm) =
      (starRingEnd ℂ) (monomialChar l w) := by
  show ∏ i, (((w (Fin.revPerm i)) ^ (-l (Fin.rev i)) : ℂˣ) : ℂ) =
    (starRingEnd ℂ) (∏ i, ((w i ^ l i : ℂˣ) : ℂ))
  rw [map_prod, ← Equiv.prod_comp Fin.revPerm (fun k => (starRingEnd ℂ) ((w k ^ l k : ℂˣ) : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
  rw [← Complex.inv_eq_conj (hw _), zpow_neg, inv_zpow]

private theorem pair_term {n : ℕ} (t : ℝ) (w : Fin n → ℂˣ) (hinj : Function.Injective w)
    (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    ∏ p ∈ prs n, ((w (Fin.rev p.1) : ℂ) - (t : ℂ) * (w (Fin.rev p.2) : ℂ)) /
        ((w (Fin.rev p.1) : ℂ) - (w (Fin.rev p.2) : ℂ)) =
      (starRingEnd ℂ) (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) /
        ((w p.1 : ℂ) - (w p.2 : ℂ))) := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : Fin.rev p.2 ≠ Fin.rev p.1 := fun h => (ne_of_lt hp) (Fin.rev_injective h).symm
    have hab : (w (Fin.rev p.2) : ℂ) ≠ (w (Fin.rev p.1) : ℂ) :=
      fun h => hne (hinj (Units.val_injective h))
    have ha : (w (Fin.rev p.2) : ℂ) ≠ 0 := Units.ne_zero _
    have hb : (w (Fin.rev p.1) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal]
    rw [← Complex.inv_eq_conj (hw _), ← Complex.inv_eq_conj (hw _)]
    generalize (w (Fin.rev p.2) : ℂ) = a at *
    generalize (w (Fin.rev p.1) : ℂ) = b at *
    have h1 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have h2 : a⁻¹ - b⁻¹ ≠ 0 := by
      rw [inv_sub_inv ha hb]
      exact div_ne_zero h1 (mul_ne_zero ha hb)
    rw [div_eq_div_iff h1 h2]
    field_simp

theorem UpperTheory.Gal.Gen.rConj_pf :
    UpperTheory.Gal.Gen.RFormula → UpperTheory.Gal.Gen.RConj := by
  intro hR n t l z hinj hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hR n t _ z hinj, hR n t l z hinj, map_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ ?_).symm
  intro σ
  have hw : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hz _
  have hi : Function.Injective (z ∘ σ) := hinj.comp σ.injective
  have h1 := mono_term l (z ∘ σ) hw
  have h2 := pair_term t (z ∘ σ) hi hw
  rw [map_mul]
  simp only [Function.comp_apply] at h2
  rw [← h1, ← h2]
  rfl
end

