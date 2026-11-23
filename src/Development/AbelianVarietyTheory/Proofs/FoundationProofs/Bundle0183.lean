module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg GlobalTheory.QFam Cardinal

namespace GlobalTheory.KZ.GalUnits

theorem exists_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  let : Algebra R K := f.toAlgebra
  let : Algebra R L := g.toAlgebra
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' R L
  have h1 : #K = #ι := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hv hR hK
  have h2 : #L = #κ :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' w hw hR (hKL ▸ hK)
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let e' : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  have hf : f r = algebraMap R K r := rfl
  have hg : g r = algebraMap R L r := rfl
  rw [hf, hg, IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  have : e'.toRingEquiv (algebraMap R _ r) = algebraMap R _ r := e'.commutes r
  rw [this, ← IsScalarTower.algebraMap_apply]

theorem exists_ext {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : Ω, σ (ε x) = ε (s x) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hR : #Ω ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Ω).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  exact exists_equiv_comp ε (ε.comp (s : Ω →+* Ω)) hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl

theorem mem_range_of_pow_eq_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ε : Ω →+* ℂ) {n : ℕ}
    (hn : 0 < n) {w : ℂ} (hw : w ^ n = 1) : ∃ y, ε y = w := by
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos n Ω hn))
  have hz' : IsPrimitiveRoot z n := Polynomial.isRoot_cyclotomic_iff.1 hz
  have he : IsPrimitiveRoot (ε z) n := hz'.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := he.eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

theorem eps_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = ee (x : ℂ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = x.num * (2 * Real.pi * Complex.I) := by
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have : (x : ℂ) = (x.num : ℂ) / x.den := by exact_mod_cast (Rat.num_div_den x).symm
      rw [this]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hex := mem_range_of_pow_eq_one ε x.den_pos hw
  unfold eOm ee
  exact Function.invFun_eq hex


open Classical in
def lc {R : Type} [Zero R] (M : ℕ) (k : ℤ) (A : ℕ → R) (r : ℚ) : R :=
  if h : ∃ n : ℕ, r = ((k : ℚ) + n) / M then A h.choose else 0

theorem lc_eq {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) (k : ℤ) (A : ℕ → R) (n : ℕ) :
    lc M k A (((k : ℚ) + n) / M) = A n := by
  have h : ∃ m : ℕ, ((k : ℚ) + n) / M = ((k : ℚ) + m) / M := ⟨n, rfl⟩
  unfold lc
  rw [dite_eq_left h]
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have := h.choose_spec
  rw [div_left_inj' hM', add_right_inj] at this
  have : h.choose = n := by exact_mod_cast this.symm
  rw [this]

theorem lc_zero {R : Type} [Zero R] {M : ℕ} {k : ℤ} (A : ℕ → R) {r : ℚ} (h : ∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) :
    lc M k A r = 0 := by
  unfold lc
  rw [dite_eq_right]
  push_neg
  exact h

theorem lc_map {R S : Type} [Zero R] [Zero S] (M : ℕ) (k : ℤ) (A : ℕ → R) (g : R → S) (hg : g 0 = 0) (r : ℚ) :
    lc M k (fun n => g (A n)) r = g (lc M k A r) := by
  unfold lc
  split_ifs <;> simp [hg]

theorem eq_lc {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) {k : ℤ} {A : ℕ → R} {F : ℚ → R}
    (h1 : ∀ n : ℕ, F (((k : ℚ) + n) / M) = A n) (h2 : ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → F r = 0) :
    ∀ r, F r = lc M k A r := by
  intro r
  by_cases h : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := h
    rw [h1, lc_eq hM]
  · push_neg at h
    rw [h2 r h, lc_zero A h]

theorem lc_unique {M : ℕ} (hM : 0 < M) {f : ℍ → ℂ} {k k' : ℤ} {A A' : ℕ → ℂ}
    (h : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A)
    (h' : HasQ M (fun τ => f τ * ee (-((k' : ℂ) / M) * (τ : ℂ))) A') : lc M k A = lc M k' A' := by
  wlog hk : k ≤ k' generalizing k k' A A'
  · exact (this h' h (le_of_not_ge hk)).symm
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k' = k + m := ⟨(k' - k).toNat, by omega⟩
  have hs : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => if m ≤ n then A' (n - m) else 0) := by
    rw [hasQ_iff] at h' ⊢
    intro τ
    set Q := Complex.exp (2 * Real.pi * Complex.I * τ / M) with hQ
    have h2 := (h' τ).mul_right (Q ^ m)
    have e : f τ * ee (-(((k + m : ℤ) : ℂ) / M) * (τ : ℂ)) * Q ^ m = f τ * ee (-((k : ℂ) / M) * (τ : ℂ)) := by
      rw [mul_assoc]; congr 1
      unfold ee
      rw [hQ, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [e] at h2
    refine (Function.Injective.hasSum_iff (f := fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n)
      (add_left_injective m) ?_).mp ?_
    · intro x hx
      have : ¬ m ≤ x := by
        intro hmx; exact hx ⟨x - m, by simp only; omega⟩
      simp [this]
    · rw [← hQ] at h2
      have e2 : (fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n) ∘ (· + m) = fun i => A' i * Q ^ i * Q ^ m := by
        funext n
        simp only [Function.comp, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, pow_add]
        ring
      rw [e2]; exact h2
  have hA := HasQ.coeff_unique hM h hs
  subst hA
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  funext r
  by_cases hr : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := hr
    rw [lc_eq hM]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      have : ((k : ℚ) + n) / M = (((k + m : ℤ) : ℚ) + ((n - m : ℕ) : ℚ)) / M := by
        push_cast [Nat.cast_sub hmn]; ring
      rw [this, lc_eq hM]
    · rw [if_neg hmn, lc_zero]
      intro n' hn'
      rw [div_left_inj' hM'] at hn'
      push_cast at hn'
      have : (n : ℚ) = m + n' := by linarith
      have : n = m + n' := by exact_mod_cast this
      omega
  · push_neg at hr
    rw [lc_zero _ hr, lc_zero]
    intro n' hn'
    apply hr (m + n')
    rw [hn']; push_cast; ring

end GlobalTheory.KZ.GalUnits

namespace GlobalTheory.KZ

open GalUnits

theorem gal_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  intro Ω _ _ _ ε T c M a b d s hM ha hs h1 h2
  obtain ⟨σ, hσ⟩ := exists_ext ε s
  have hσM : σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) := by
    have e1 := eps_eOm ε (1 / M)
    have e2 := eps_eOm ε (d / M)
    push_cast at e1 e2
    rw [← e1, hσ, hs, e2]
  obtain ⟨k0, B, hB, hB'⟩ := _root_.GlobalTheory.Sieg.sg_coeff_galois_int c M a b d σ hM ha hσM h1 h2
  obtain ⟨k1, A1, hA1, c1, z1⟩ := _root_.GlobalTheory.KExp.siegel_exp Ω ε T c M a b hM ha h1
  obtain ⟨k2, A2, hA2, c2, z2⟩ := _root_.GlobalTheory.KExp.siegel_exp Ω ε T c M a (d * b) hM ha h2
  have L1 := eq_lc hM c1 z1
  have L2 := eq_lc hM c2 z2
  have U1 := lc_unique hM hA1 hB
  have U2 := lc_unique hM hB' hA2
  apply T.exp.toRingHom.injective
  ext r
  apply ε.injective
  show ε ((T.exp (T.gal s _)).coeff r) = ε ((T.exp _).coeff r)
  rw [T.gal_exp, ← hσ, L1, L2, ← lc_map M k1 A1 ε (map_zero ε), U1, ← lc_map M k0 B σ (map_zero σ), U2,
    lc_map M k2 A2 ε (map_zero ε)]

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjoint
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma adjT_adj_adj (M : M2) : M.adjugate.adjugate = M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]

lemma intMatrixTwo_adjugate_zero_zero (M : M2) : M.adjugate 0 0 = M 1 1 := by
  simp [Matrix.adjugate_fin_two]

lemma pet_const_mul_left (k : ℕ) (ρ : ℍ → ℝ) (c : ℂ) (F G : ℍ → ℂ) :
    pet k ρ (fun τ => c * F τ) G = conj c * pet k ρ F G := by
  unfold pet
  rw [← integral_const_mul]
  congr 1; funext τ
  simp only [map_mul]; ring

end GlobalTheory.EisM

theorem GlobalTheory.EisM.pet_To_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → q.Prime → ¬ q ∣ L → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (To k (ch ε q) q a)) = ch ε q * pet k ρ (qs (To k (ch ε q) q h)) (qs a) := by
  intro k L N q ε ρ h a hk hL hNL hq hqL hρ hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hqN : ¬ q ∣ N := fun h' => hqL (h'.trans hNL)
  have hcop : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
  have hq0 : 0 < q := hq.pos
  have hε1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨-, hTaeq⟩ := _root_.GlobalTheory.EisM.qs_To_hsum k q (ch ε) a hk hq0 hε1 ha.1
  obtain ⟨-, hTheq⟩ := _root_.GlobalTheory.EisM.qs_To_hsum k q (ch ε) h hk hq0 hε1 hh.1.1
  have hcont_h := (_root_.GlobalTheory.EisM.qs_summable_continuous h hh.1.1).2
  have hcont_a := (_root_.GlobalTheory.EisM.qs_summable_continuous a ha.1).2
  have hslz := _root_.GlobalTheory.EisM.slz_props k (qs a) hk
  have hdetpos : ∀ i, 0 < (repT q i).det := by
    intro i; cases i <;> simp [repT, repU, Matrix.det_fin_two_of, hq0]
  have hlow : ∀ i, (repT q i) 1 0 = 0 := by
    intro i; cases i <;> simp [repT, repU]
  have hint : ∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repT q i) (qs a) τ * (τ.im : ℂ) ^ k)) :=
    fun i => _root_.GlobalTheory.EisM.integrable_pet_integrand k L L N ε h ρ (slz k (repT q i) (qs a)) hk hL hNL hρ hh
      ((hslz.2.2.2.1 _ (hdetpos i) hcont_a).aestronglyMeasurable)
      (_root_.GlobalTheory.EisM.mod_algebra.2.2 _ k _ (hdetpos i) (hlow i) (_root_.GlobalTheory.EisM.mod_qs_of_polyB a ha.1))
  have hadj := _root_.GlobalTheory.EisM.pet_hsum_adjoint k L N q ε ρ (DT L q) (Option (Fin q)) (Option (Fin q)) (repT q)
    (fun i => (repT q i).adjugate) (qs h) (qs a) hk hN hNL hq0 hcop hρ
    (fun δ hδ => ⟨hδ.1, (Int.natCast_dvd_natCast.2 hNL).trans hδ.2⟩)
    (_root_.GlobalTheory.EisM.lRep_DT_repT L q hq hqL) (_root_.GlobalTheory.EisM.rrep_DT_adj_repT L q hq hqL) hh.1.2 ha.2 hcont_h hcont_a hint
  rw [← hTaeq] at hadj
  rw [hadj]

  have hu : ((q : ℤ) : ZMod N) = ((ZMod.unitOfCoprime q hcop : (ZMod N)ˣ) : ZMod N) := by
    simp [ZMod.coe_unitOfCoprime]
  have hnorm : ‖ch ε q‖ = 1 := by
    simp only [ch]; rw [hu]; exact DirichletCharacter.unit_norm_eq_one ε _
  have hne : ch ε q ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hinvq : ch ε⁻¹ q = (ch ε q)⁻¹ := by
    simp only [ch]; rw [MulChar.inv_apply_eq_inv']
  have hinv1 : ch ε⁻¹ 1 = 1 := by simp [ch]
  have hsumeq : (fun τ => ∑ j, ch ε⁻¹ ((repT q j).adjugate 0 0) * slz k (repT q j).adjugate.adjugate (qs h) τ)
      = fun τ => (ch ε q)⁻¹ * qs (To k (ch ε q) q h) τ := by
    funext τ
    rw [hTheq]
    simp only [hsum, Fintype.sum_option, adjT_adj_adj, intMatrixTwo_adjugate_zero_zero, Finset.mul_sum, mul_add]
    simp [repT, repU, hinvq, hinv1, hε1, hne]
  rw [hsumeq, pet_const_mul_left]
  have hc : conj ((ch ε q)⁻¹) = ch ε q := by
    rw [map_inv₀]
    have : conj (ch ε q) * ch ε q = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]; simp
    exact inv_eq_of_mul_eq_one_right this
  rw [hc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralSelfNeZeroCuspForm
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.PetPos

theorem volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  have h0 : (volume.comap UpperHalfPlane.coe : Measure ℍ).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  have hm : Continuous fun z : ℍ => (NNReal.mk z.im z.im_pos.le : NNReal) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have hc : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) :=
    (continuous_const.div₀ hm (fun x => NNReal.ne_iff.mp x.im_ne_zero)).pow 2
  refine ⟨fun U hU hne => ?_⟩
  rw [UpperHalfPlane.volume_def, withDensity_apply _ hU.measurableSet]
  refine ne_of_gt ?_
  have hmeas : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal) :=
    (ENNReal.continuous_coe.comp hc).measurable
  rw [setLIntegral_pos_iff hmeas]
  have hsupp : Function.support (fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal)) = Set.univ := by
    ext z
    simp [z.im_ne_zero]
    intro h
    have h' := congrArg Subtype.val h
    simp [z.im_ne_zero] at h'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos _ hne

theorem norm_ch_eq_one {L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) (γ : SL(2, ℤ))
    (hγ : (L : ℤ) ∣ γ 1 0) : ‖ch ε (γ 1 1)‖ = 1 := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : ((γ 1 1 : ℤ) : ZMod N) * ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    rw [hc, mul_zero, sub_zero] at h
    rw [mul_comm]
    exact h
  obtain ⟨u, hu⟩ := IsUnit.of_mul_eq_one _ h1
  show ‖ε ((γ 1 1 : ℤ) : ZMod N)‖ = 1
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one ε u

theorem norm_sq_mul_im_pow_smul {k L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← ModularGroup.denom_apply]
    exact UpperHalfPlane.denom_ne_zero _ _
  have hpos : 0 < ‖((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ := norm_pos_iff.mpr hD
  rw [hf γ hγ τ, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, norm_mul, norm_mul,
    norm_ch_eq_one ε hNL γ hγ, one_mul, norm_pow, div_pow, Complex.normSq_eq_norm_sq]
  field_simp
  ring

theorem pet_self_ne_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  intro k L N ε ρ h hk hL hN hW hCF hh
  haveI : (volume : Measure ℍ).IsOpenPosMeasure := volume_isOpenPosMeasure
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hP : PolyB h := hCF.1.1
  have hInv : Inv k L (ch ε) (qs h) := hCF.1.2
  have hqc : Continuous (qs h) := (_root_.GlobalTheory.EisM.qs_summable_continuous h hP).2
  set Φ : ℍ → ℝ := fun τ => ‖qs h τ‖ ^ 2 * τ.im ^ k with hΦ
  set G : ℍ → ℝ := fun τ => ρ τ * Φ τ with hG
  have hΦc : Continuous Φ := (hqc.norm.pow 2).mul (UpperHalfPlane.continuous_im.pow k)
  have hGnn : 0 ≤ G := fun τ => mul_nonneg (hW.nonneg τ) (by positivity)
  have heq : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs h τ * (τ.im : ℂ) ^ k)) =
      fun τ => ((G τ : ℝ) : ℂ) := by
    funext τ
    rw [Complex.conj_mul']
    simp only [hG, hΦ]
    push_cast
    ring
  have hint := _root_.GlobalTheory.EisM.integrable_pet_integrand k L L N ε h ρ (qs h) hk hL hN hW hCF hqc.aestronglyMeasurable
    (_root_.GlobalTheory.EisM.mod_qs_of_polyB h hP)
  rw [heq] at hint
  have hGi : Integrable G := by
    have := hint.re
    simpa using this
  intro hzero
  have hpet : pet k ρ (qs h) (qs h) = ((∫ τ, G τ : ℝ) : ℂ) := by
    unfold pet
    rw [heq, integral_complex_ofReal]
  rw [hpet, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg hGnn hGi] at hzero
  have hmp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
    intro γ
    have hm := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
    convert hm using 1
    ext z
    simp
  have hall : ∀ᵐ τ ∂(volume : Measure ℍ), ∀ γ : Gamma0 L, G ((γ : SL(2, ℤ)) • τ) = 0 := by
    rw [ae_all_iff]
    intro γ
    have h1 := (hmp (γ : SL(2, ℤ))).quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [h1] with τ hτ
    simpa using hτ
  have hΦ0 : Φ =ᵐ[volume] 0 := by
    filter_upwards [hall] with τ hτ
    have hterm : ∀ γ : Gamma0 L, Φ τ * ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ
      have hγL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
      have hinv := norm_sq_mul_im_pow_smul ε hN hInv (γ : SL(2, ℤ)) hγL τ
      have h2 := hτ γ
      simp only [hG, hΦ] at h2 ⊢
      rw [hinv] at h2
      rw [mul_comm]
      exact h2
    have hs := (hW.sum τ).mul_left (Φ τ)
    simp only [hterm, mul_one] at hs
    exact hs.unique hasSum_zero
  have hΦz : Φ = 0 := (Continuous.ae_eq_iff_eq volume hΦc continuous_const).mp hΦ0
  apply hh
  have hq0 : qs h = qs 0 := by
    funext τ
    have h3 := congrFun hΦz τ
    simp only [hΦ, Pi.zero_apply] at h3
    have him : τ.im ^ k ≠ 0 := pow_ne_zero _ τ.im_ne_zero
    have h4 : ‖qs h τ‖ ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_right him
    have h5 : qs h τ = 0 := by simpa using h4
    rw [h5]
    simp [qs]
  exact _root_.GlobalTheory.EisM.qs_injective h 0 hP ⟨0, 0, fun n => by simp⟩ hq0

end GlobalTheory.EisM.PetPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearForms
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qs_lin (a b : ℕ → ℂ) (x y : ℂ) (ha : PolyB a) (hb : PolyB b) (τ : ℍ) :
    qs (x • a + y • b) τ = x * qs a τ + y * qs b τ := by
  have sa : Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
    ((_root_.GlobalTheory.EisM.qs_summable_continuous a ha).1 τ).of_norm
  have sb : Summable fun n : ℕ => b n * cexp (2 * π * Complex.I * n * τ) :=
    ((_root_.GlobalTheory.EisM.qs_summable_continuous b hb).1 τ).of_norm
  unfold qs
  rw [← tsum_mul_left, ← tsum_mul_left, ← (sa.mul_left x).tsum_add (sb.mul_left y)]
  congr 1; funext n; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem pet_linear : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  intro k L L' N ε ρ hk hL' hN hW
  have intg : ∀ h a : ℕ → ℂ, CF k L' (ch ε) h → PolyB a →
      Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
    intro h a hh ha
    exact _root_.GlobalTheory.EisM.integrable_pet_integrand k L L' N ε h ρ (qs a) hk hL' hN hW hh
      (_root_.GlobalTheory.EisM.qs_summable_continuous a ha).2.aestronglyMeasurable (_root_.GlobalTheory.EisM.mod_qs_of_polyB a ha)
  refine ⟨?_, ?_⟩
  · intro h a b x y hh ha hb
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs (x • a + y • b) τ * (τ.im : ℂ) ^ k)) =
        fun τ => x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          y * ((ρ τ : ℂ) * (conj (qs h τ) * qs b τ * (τ.im : ℂ) ^ k)) := by
      funext τ; rw [qs_lin a b x y ha hb τ]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul x) ((intg h b hh hb).const_mul y),
      integral_const_mul, integral_const_mul]
  · intro h h' a x y hh hh' ha
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (x * qs h τ + y * qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) =
        fun τ => conj x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          conj y * ((ρ τ : ℂ) * (conj (qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
      funext τ; simp only [map_add (f := _), map_mul]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul _) ((intg h' a hh' ha).const_mul _),
      integral_const_mul, integral_const_mul]

end GlobalTheory.EisM
end

