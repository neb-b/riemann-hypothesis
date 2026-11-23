module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvChar
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.ConjForm

def refl (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

@[simp] lemma coe_refl (τ : ℍ) : ((refl τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

@[simp] lemma im_refl (τ : ℍ) : (refl τ).im = τ.im := by
  change (-conj (τ : ℂ)).im = τ.im
  simp [UpperHalfPlane.coe_im]

lemma qs_conj (g : ℕ → ℂ) (τ : ℍ) : qs (fun n => conj (g n)) τ = conj (qs g (refl τ)) := by
  unfold qs
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [coe_refl, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]

def twist (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linarith⟩

lemma refl_smul (γ : SL(2, ℤ)) (τ : ℍ) : refl (γ • τ) = twist γ • refl τ := by
  apply UpperHalfPlane.ext
  have e := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply (twist γ) (refl τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e e2
  have hd := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hd
  simp at hd
  rw [coe_refl, e, e2, coe_refl, map_div₀]
  have hd' : conj (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 := (map_ne_zero _).2 hd
  have hd'' : ((twist γ 1 0 : ℤ) : ℂ) * (-conj (τ : ℂ)) + ((twist γ 1 1 : ℤ) : ℂ) =
      conj (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    simp [twist, map_add (f := _), map_mul, map_intCast]
  rw [hd'', neg_div', div_left_inj' hd']
  simp [twist, map_add (f := _), map_mul, map_intCast]
  ring

lemma conj_ch {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℤ) : conj (ch χ d) = ch χ⁻¹ d := by
  unfold ch
  exact MulChar.star_apply' χ _

end GlobalTheory.EisM.ConjForm

namespace GlobalTheory.EisM.ConjForm

lemma polyB_conj {g : ℕ → ℂ} (h : PolyB g) : PolyB (fun n => conj (g n)) := by
  obtain ⟨C, A, hC⟩ := h
  exact ⟨C, A, fun n => by simpa using hC n⟩

lemma inv_conj {k L : ℕ} {χ : DirichletCharacter ℂ L} {g : ℕ → ℂ} (h : Inv k L (ch χ) (qs g)) :
    Inv k L (ch χ⁻¹) (qs (fun n => conj (g n))) := by
  intro γ hc τ
  have h1 := h (twist γ) (by simpa [twist] using hc) (refl τ)
  rw [qs_conj, qs_conj, refl_smul, h1, map_mul, map_mul, map_pow, conj_ch]
  congr 2
  simp [twist, map_add (f := _), map_mul, map_intCast]

lemma cf_conj {k N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℕ → ℂ} (h : CF k N (ch χ) g) :
    CF k N (ch χ⁻¹) (fun n => conj (g n)) := by
  obtain ⟨⟨hp, hi⟩, C, hC⟩ := h
  refine ⟨⟨polyB_conj hp, inv_conj hi⟩, C, fun τ => ?_⟩
  have := hC (refl τ)
  rw [im_refl] at this
  rwa [qs_conj, Complex.norm_conj]

theorem conj_form : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ),
    (CF k N (ch χ) g → CF k N (ch χ⁻¹) (fun n => conj (g n))) ∧
    (Prim k N χ g → Prim k N χ⁻¹ (fun n => conj (g n))) := by
  intro k N χ g
  refine ⟨cf_conj, fun h => ⟨cf_conj h.cf, by simp [h.one], fun n hn => by simp [h.zero n hn], ?_⟩⟩
  intro q hq hqN
  funext n
  have e := congrFun (h.eig q hq hqN) n
  have e' := congrArg conj e
  simp only [To, Vo, map_add (f := _), map_mul, map_pow, map_natCast, conj_ch] at e'
  simp only [To, Vo]
  rw [← e']
  congr 2
  split_ifs <;> simp

end GlobalTheory.EisM.ConjForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DehomogeniseBinaryPolyHomogeneousEquivSlash
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem dehH_mon (w : ℕ) (i : Fin (w + 1)) : deh (mon ℂ w i) = Polynomial.X ^ (i : ℕ) := by
  simp [deh, mon]

theorem dehH_slP_mon (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i : ℕ) :
    deh (slP m (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (w - i))) =
      (Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
        (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [deh, slP, Polynomial.smul_eq_C_mul]

theorem dehH_expand (w : ℕ) (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous w) :
    deh p = ∑ i ∈ Finset.range (w + 1),
      Polynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) * Polynomial.X ^ i := by
  have h := (_root_.GlobalTheory.KZ.H3.mon_expand ℂ w).2.1 p hp
  conv_lhs => rw [h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (AddMonoidAlgebra.coeff
    p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) * Polynomial.X ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, dehH_mon]
  simp [deh]

theorem dehH_coeff (w : ℕ) (c : ℕ → ℂ) (j : ℕ) (hj : j < w + 1) :
    (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i).coeff j = c j := by
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hj]

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

theorem dehH_slP_sum (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (c : ℕ → ℂ) :
    GlobalTheory.HeckeFamilyMatrices.slP w m (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i) =
      ∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  rw [GlobalTheory.HeckeFamilyMatrices.slP, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, Polynomial.lcoeff_apply,
    LinearMap.toSpanSingleton_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dehH_coeff w c i (Finset.mem_range.mp hi), Polynomial.smul_eq_C_mul]

theorem dehH_sum_eq (w : ℕ) (q : Polynomial ℂ) (hq : q ∈ Polynomial.degreeLT ℂ (w + 1)) :
    ∑ i ∈ Finset.range (w + 1), Polynomial.C (q.coeff i) * Polynomial.X ^ i = q := by
  ext j
  by_cases hj : j < w + 1
  · exact dehH_coeff w _ j hj
  · rw [Polynomial.finsetSum_coeff]
    rw [Polynomial.mem_degreeLT] at hq
    have h0 : q.coeff j = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hq (by exact_mod_cast not_lt.mp hj))
    rw [h0]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    have : j ≠ i := fun h => hj (h ▸ Finset.mem_range.mp hi)
    simp [this]

theorem deh_homog_iso : ∀ w : ℕ, (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous w → deh (slP m p) = GlobalTheory.HeckeFamilyMatrices.slP w m (deh p)) ∧ (∀ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → deh p ∈ Polynomial.degreeLT ℂ (w + 1)) ∧ (∀ q ∈ Polynomial.degreeLT ℂ (w + 1), ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w ∧ deh p = q) ∧ (∀ p p' : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → p'.IsHomogeneous w → deh p = deh p' → p = p') := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m p hp
    have h := (_root_.GlobalTheory.KZ.H3.mon_expand ℂ w).2.1 p hp
    rw [dehH_expand w p hp, dehH_slP_sum]
    conv_lhs => rw [h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (AddMonoidAlgebra.coeff
      p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, MvPolynomial.algHom_C, mon, dehH_slP_mon]
    simp [deh]
  · intro p hp
    rw [dehH_expand w p hp]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Polynomial.mem_degreeLT]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    have := Finset.mem_range.mp hi
    exact_mod_cast this
  · intro q hq
    refine ⟨∑ i : Fin (w + 1), MvPolynomial.C (q.coeff i) * mon ℂ w i, ?_, ?_⟩
    · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
        ((_root_.GlobalTheory.KZ.H3.mon_expand ℂ w).2.2.1 i).C_mul _
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      simp only [map_mul, dehH_mon]
      simp only [deh, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i)]
      exact dehH_sum_eq w q hq
  · intro p p' hp hp' he
    rw [(_root_.GlobalTheory.KZ.H3.mon_expand ℂ w).2.1 p hp, (_root_.GlobalTheory.KZ.H3.mon_expand ℂ w).2.1 p' hp']
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := dehH_coeff w (fun i => AddMonoidAlgebra.coeff p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) i i.2
    have h2 := dehH_coeff w (fun i => AddMonoidAlgebra.coeff p' (Finsupp.single 0 i + Finsupp.single 1 (w - i))) i i.2
    rw [← dehH_expand w p hp, he, dehH_expand w p' hp', h2] at h1
    rw [h1]

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetAdjointOfInvariantWeight
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem hasSum_integral_smul_of_partition {X Γ E : Type} [MeasurableSpace X] [Countable Γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) (w : Γ → X → ℝ)
    (hw : ∀ γ, Measurable (w γ)) (hw0 : ∀ γ x, 0 ≤ w γ x)
    (hw1 : ∀ x, HasSum (fun γ => w γ x) 1) (F : X → E) (hF : Integrable F μ) :
    (∀ γ, Integrable (fun x => w γ x • F x) μ) ∧
      HasSum (fun γ => ∫ x, w γ x • F x ∂μ) (∫ x, F x ∂μ) := by
  have hle : ∀ γ x, w γ x ≤ 1 := fun γ x =>
    le_hasSum (hw1 x) γ (fun j _ => hw0 j x)
  have hnorm : ∀ γ x, ‖w γ x • F x‖ = w γ x * ‖F x‖ := fun γ x => by
    rw [norm_smul, Real.norm_of_nonneg (hw0 γ x)]
  have hmeas : ∀ γ, AEStronglyMeasurable (fun x => w γ x • F x) μ := fun γ =>
    (hw γ).aestronglyMeasurable.smul hF.aestronglyMeasurable
  refine ⟨fun γ => hF.mono (hmeas γ) (Eventually.of_forall fun x => ?_), ?_⟩
  · rw [hnorm]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle γ x)
  refine hasSum_integral_of_dominated_convergence (fun γ x => w γ x * ‖F x‖) hmeas
    (fun γ => Eventually.of_forall fun x => (hnorm γ x).le)
    (Eventually.of_forall fun x => ((hw1 x).mul_right ‖F x‖).summable) ?_ ?_
  · have : (fun x => ∑' γ, w γ x * ‖F x‖) = fun x => ‖F x‖ := by
      funext x
      rw [((hw1 x).mul_right ‖F x‖).tsum_eq, one_mul]
    rw [this]
    exact hF.norm
  · exact Eventually.of_forall fun x => by simpa using (hw1 x).smul_const (F x)

theorem integrable_tsum_of_summable_norm_integral {ι Y : Type} [Countable ι]
    [MeasurableSpace Y] (μ : Measure Y) (F : ι → Y → ℂ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ := by
  have hm : AEStronglyMeasurable (fun y => ∑' i, F i y) μ :=
    (AEMeasurable.tsum fun i => (hF i).aemeasurable).aestronglyMeasurable
  have hle : ∫⁻ y, ‖∑' i, F i y‖ₑ ∂μ ≤ ENNReal.ofReal (∑' i, ∫ y, ‖F i y‖ ∂μ) := by
    calc ∫⁻ y, ‖∑' i, F i y‖ₑ ∂μ ≤ ∫⁻ y, ∑' i, ‖F i y‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ y, ‖F i y‖ₑ ∂μ := lintegral_tsum fun i => (hF i).aemeasurable.enorm
      _ = ∑' i, ENNReal.ofReal (∫ y, ‖F i y‖ ∂μ) :=
          tsum_congr fun i => (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg
          (fun i => integral_nonneg fun y => norm_nonneg _) hs).symm
  exact ⟨hm, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩

theorem abstract_double_coset_adjoint : ∀ (G X Γ ι κ : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ] [Group Γ] [Countable Γ] [Fintype ι] [Fintype κ] (φ : Γ →* G) (ρ : X → ℝ) (β : ι → G) (α : κ → G) (e : Γ × ι ≃ κ × Γ) (P : ι → X → ℂ) (Q : κ → X → ℂ), Measurable ρ → (∀ x, 0 ≤ ρ x) → (∀ x, HasSum (fun γ : Γ => ρ (φ γ • x)) 1) → (∀ p, φ p.1 * β p.2 = α (e p).1 * φ (e p).2) → (∀ p x, P p.2 x = Q (e p).1 (φ (e p).2 • x)) → (∀ i, Integrable (fun x => (ρ x : ℂ) * P i x) μ) → (∀ j, AEStronglyMeasurable (Q j) μ) → (∀ j, Integrable (fun x => (ρ x : ℂ) * Q j ((α j)⁻¹ • x)) μ) ∧ ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ := by
  intro G X Γ ι κ _ _ _ _ μ _ _ _ _ _ φ ρ β α e P Q hρm hρ0 hρ1 he hPQ hPi _

  set wP : ι → Γ → X → ℝ := fun i γ x => ρ (φ γ • β i • x) with hwP
  set wQ : κ → Γ → X → ℝ := fun j γ y => ρ ((φ γ)⁻¹ • (α j)⁻¹ • y) with hwQ
  set FP : ι → X → ℂ := fun i x => (ρ x : ℂ) * P i x with hFP
  set FQ : κ → X → ℂ := fun j y => (ρ y : ℂ) * Q j ((α j)⁻¹ • y) with hFQ
  have hwPm : ∀ i γ, Measurable (wP i γ) := fun i γ =>
    hρm.comp ((measurable_id.const_smul (β i)).const_smul (φ γ))
  have hwQm : ∀ j γ, Measurable (wQ j γ) := fun j γ =>
    hρm.comp ((measurable_id.const_smul (α j)⁻¹).const_smul (φ γ)⁻¹)
  have hwP0 : ∀ i γ x, 0 ≤ wP i γ x := fun _ _ _ => hρ0 _
  have hwQ0 : ∀ j γ x, 0 ≤ wQ j γ x := fun _ _ _ => hρ0 _
  have hwP1 : ∀ i x, HasSum (fun γ => wP i γ x) 1 := fun i x => hρ1 (β i • x)
  have hwQ1 : ∀ j y, HasSum (fun γ => wQ j γ y) 1 := fun j y => by
    have h := (Equiv.inv Γ).hasSum_iff.2 (hρ1 ((α j)⁻¹ • y))
    simpa [Function.comp_def, map_inv] using h

  have hpt : ∀ (q : κ × Γ) (x : X),
      wQ q.1 q.2 ((α q.1 * φ q.2) • x) • FQ q.1 ((α q.1 * φ q.2) • x) =
        wP (e.symm q).2 (e.symm q).1 x • FP (e.symm q).2 x := by
    intro q x
    have h1 := he (e.symm q)
    have h2 := hPQ (e.symm q) x
    simp only [Equiv.apply_symm_apply] at h1 h2
    have hx1 : (φ q.2)⁻¹ • (α q.1)⁻¹ • (α q.1 * φ q.2) • x = x := by
      rw [smul_smul, smul_smul, ← mul_assoc, mul_assoc _ (α q.1)⁻¹, inv_mul_cancel, mul_one,
        inv_mul_cancel, one_smul]
    have hx2 : (α q.1)⁻¹ • (α q.1 * φ q.2) • x = φ q.2 • x := by
      rw [smul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hx3 : (α q.1 * φ q.2) • x = φ (e.symm q).1 • β (e.symm q).2 • x := by
      rw [← h1, mul_smul]
    simp only [hwQ, hwP, hFQ, hFP, hx1, hx2, h2, inv_smul_smul]
    rw [hx3, Complex.real_smul, Complex.real_smul]
    ring

  have hPpart := fun i => hasSum_integral_smul_of_partition μ (wP i) (hwPm i) (hwP0 i) (hwP1 i)
    (FP i) (hPi i)
  have hPnorm := fun i => hasSum_integral_smul_of_partition μ (wP i) (hwPm i) (hwP0 i) (hwP1 i)
    (fun x => ‖FP i x‖) (hPi i).norm
  have hnP : ∀ i γ x, ‖wP i γ x • FP i x‖ = wP i γ x • ‖FP i x‖ := fun i γ x => by
    rw [norm_smul, Real.norm_of_nonneg (hwP0 i γ x), smul_eq_mul]
  let a : Γ × ι → ℝ := fun p => ∫ x, ‖wP p.2 p.1 x • FP p.2 x‖ ∂μ
  let t : Γ × ι → ℂ := fun p => ∫ x, wP p.2 p.1 x • FP p.2 x ∂μ
  have ha0 : 0 ≤ a := fun p => integral_nonneg fun x => norm_nonneg _
  have haP : ∀ i, HasSum (fun γ => a (γ, i)) (∫ x, ‖FP i x‖ ∂μ) := fun i => by
    simpa only [a, hnP] using (hPnorm i).2
  have hsa : Summable a := by
    rw [summable_prod_of_nonneg ha0]
    refine ⟨fun γ => Summable.of_finite, ?_⟩
    simp only [tsum_fintype]
    exact summable_sum fun i _ => (haP i).summable
  have hst : Summable t :=
    Summable.of_norm_bounded hsa fun p => norm_integral_le_integral_norm _

  have hcv : ∀ q : κ × Γ, (fun x => wQ q.1 q.2 ((α q.1 * φ q.2) • x) •
      FQ q.1 ((α q.1 * φ q.2) • x)) = fun x => wP (e.symm q).2 (e.symm q).1 x • FP (e.symm q).2 x :=
    fun q => funext (hpt q)
  have hta : ∀ q : κ × Γ, t (e.symm q) = ∫ y, wQ q.1 q.2 y • FQ q.1 y ∂μ := fun q => by
    rw [← integral_smul_eq_self (fun y => wQ q.1 q.2 y • FQ q.1 y) (g := α q.1 * φ q.2)]
    exact congrArg (fun f => ∫ x, f x ∂μ) (hcv q).symm
  have haa : ∀ q : κ × Γ, a (e.symm q) = ∫ y, ‖wQ q.1 q.2 y • FQ q.1 y‖ ∂μ := fun q => by
    rw [← integral_smul_eq_self (fun y => ‖wQ q.1 q.2 y • FQ q.1 y‖) (g := α q.1 * φ q.2)]
    exact congrArg (fun f => ∫ x, ‖f x‖ ∂μ) (hcv q).symm
  have hintQ : ∀ q : κ × Γ, Integrable (fun y => wQ q.1 q.2 y • FQ q.1 y) μ := fun q => by
    have hemb := (MeasurableEquiv.smul (α q.1 * φ q.2) : X ≃ᵐ X).measurableEmbedding
    rw [← (measurePreserving_smul (α q.1 * φ q.2) μ).integrable_comp_emb hemb]
    have := (hPpart (e.symm q).2).1 (e.symm q).1
    rw [← hcv q] at this
    exact this
  have hsb : Summable fun q => a (e.symm q) := e.symm.summable_iff.2 hsa
  obtain ⟨hfib, -⟩ := (summable_prod_of_nonneg fun q => ha0 (e.symm q)).1 hsb
  have hsQ : ∀ j, Summable fun γ => ∫ y, ‖wQ j γ y • FQ j y‖ ∂μ := fun j => by
    simpa only [haa] using hfib j
  have hFQsum : ∀ j, (fun y => ∑' γ, wQ j γ y • FQ j y) = FQ j := fun j => by
    funext y
    simpa using ((hwQ1 j y).smul_const (FQ j y)).tsum_eq
  have hQint : ∀ j, Integrable (FQ j) μ := fun j => by
    have h := integrable_tsum_of_summable_norm_integral μ (fun γ y => wQ j γ y • FQ j y)
      (fun γ => hintQ (j, γ)) (hsQ j)
    rwa [hFQsum j] at h
  refine ⟨hQint, ?_⟩
  have hQpart := fun j => hasSum_integral_smul_of_partition μ (wQ j) (hwQm j) (hwQ0 j)
    (hwQ1 j) (FQ j) (hQint j)
  have hstb : Summable fun q => t (e.symm q) := e.symm.summable_iff.2 hst
  calc ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ i, ∑' γ, t (γ, i) :=
        Finset.sum_congr rfl fun i _ => ((hPpart i).2.tsum_eq).symm
    _ = ∑' γ, ∑ i, t (γ, i) := (Summable.tsum_finsetSum fun i _ => (hPpart i).2.summable).symm
    _ = ∑' γ, ∑' i, t (γ, i) := by simp only [tsum_fintype]
    _ = ∑' p, t p := hst.tsum_prod.symm
    _ = ∑' q, t (e.symm q) := (e.symm.tsum_eq t).symm
    _ = ∑' j, ∑' γ, t (e.symm (j, γ)) := hstb.tsum_prod
    _ = ∑ j, ∑' γ, ∫ y, wQ j γ y • FQ j y ∂μ := by
        rw [tsum_fintype]; simp only [hta]
    _ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ :=
        Finset.sum_congr rfl fun j _ => (hQpart j).2.tsum_eq

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraCocyclesGammaOneGammaZeroFiniteDim
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem polySlash_one_of_mem (w : ℕ) (p : Polynomial ℂ) (hp : p ∈ Polynomial.degreeLT ℂ (w + 1)) :
    GlobalTheory.HeckeFamilyMatrices.slP w (1 : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  simp [GlobalTheory.HeckeFamilyMatrices.slP]
  rw [Polynomial.mem_degreeLT] at hp
  have hn : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hp
  conv_rhs => rw [p.as_sum_range' (w + 1) hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.smul_X_eq_monomial]

theorem eichlerShimuraCocycle_eq_zero_of_closure (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (hz : ∀ s ∈ S, (z : Γ → Polynomial ℂ) s = 0) :
    (z : Γ → Polynomial ℂ) = 0 := by
  obtain ⟨hdeg, hco⟩ := z.2
  have hone : (z : Γ → Polynomial ℂ) 1 = 0 := by
    have h := hco 1 1
    rw [mul_one] at h
    have hid : GlobalTheory.HeckeFamilyMatrices.slP w (GlobalTheory.HeckeFamilyMatrices.mat (1 : Γ)) ((z : Γ → Polynomial ℂ) 1) = (z : Γ → Polynomial ℂ) 1 := by
      have : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := by simp [GlobalTheory.HeckeFamilyMatrices.mat]
      rw [this]
      exact polySlash_one_of_mem w _ (hdeg 1)
    rw [hid] at h
    have : (z : Γ → Polynomial ℂ) 1 + (z : Γ → Polynomial ℂ) 1 - (z : Γ → Polynomial ℂ) 1 = 0 := by
      rw [← h]; ring
    simpa using this
  let K : Subgroup Γ :=
    { carrier := {γ | (z : Γ → Polynomial ℂ) γ = 0}
      mul_mem' := by
        intro a b ha hb
        show (z : Γ → Polynomial ℂ) (a * b) = 0
        rw [hco, ha.out, hb.out, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := by
        intro a ha
        show (z : Γ → Polynomial ℂ) a⁻¹ = 0
        have h := hco a a⁻¹
        rw [mul_inv_cancel, hone, ha.out, map_zero, zero_add] at h
        exact h.symm }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).2 hz
  rw [hS] at hle
  funext γ
  exact hle (Subgroup.mem_top γ)

theorem eichlerShimuraCocycles_finiteDimensional_of_fg (Γ : Subgroup SL(2, ℤ)) [Group.FG Γ] (w : ℕ) :
    FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) := by
  obtain ⟨S, hS, hSfinite⟩ := (Group.fg_iff).1 (inferInstance : Group.FG Γ)
  letI := hSfinite.fintype
  haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ (w + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ (w + 1)).symm
  let g : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w →ₗ[ℂ] (S → Polynomial.degreeLT ℂ (w + 1)) :=
    LinearMap.pi fun s => LinearMap.codRestrict (Polynomial.degreeLT ℂ (w + 1))
      ((LinearMap.proj (s : Γ)).comp (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w).subtype) (fun z => z.2.1 s)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 := eichlerShimuraCocycle_eq_zero_of_closure Γ w z (S : Set Γ) hS (fun s hs => by
      have := congrArg Subtype.val (congrFun hz ⟨s, hs⟩)
      exact this)
    exact Subtype.ext h0
  exact Module.Finite.of_injective g hg

theorem lev_fd : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  intro N l w hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (GlobalTheory.HeckeFamilyMatrices.Lev N l).FiniteIndex := by unfold GlobalTheory.HeckeFamilyMatrices.Lev; infer_instance
  haveI : Group.FG (GlobalTheory.HeckeFamilyMatrices.Lev N l) := Subgroup.fg_of_index_ne_zero _
  exact eichlerShimuraCocycles_finiteDimensional_of_fg _ w

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelationStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_betti_cocycle_kummer_relation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  first | exact @GlobalTheory.KZ.BettiEx.exists_betti_cocycle | exact GlobalTheory.KZ.BettiEx.exists_betti_cocycle | (intros; apply GlobalTheory.KZ.BettiEx.exists_betti_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummer
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.KZ.exists_pot_rel_of_mem_bSet : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  intro Ω _ _ _ ε X _ hj N l w hl h2 hN hc hw b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨φ, hφ, hφ'⟩ := hj
  exact _root_.GlobalTheory.KZ.H3.exists_pot_rel Ω ε X l ⟨φ, hφ', hφ⟩ N w (by omega) h2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hc.symm) hw b (Submodule.subset_span hb)
end

