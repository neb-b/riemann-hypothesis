module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankFourLtTop
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin4
noncomputable section

def pw (t : ℂ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-(4 / 3 : ℝ))

theorem lintegral_pw_lt_top : ∫⁻ t : ℂ, ENNReal.ofReal (pw t) < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 8 / 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  convert h.lintegral_lt_top using 4
  simp only [pw]; norm_num

theorem gB_eq (w : Low 4 → ℂ) (p0 : ℕ) : gB p0 w =
    (colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 ^ 2 * colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 ^ 2)⁻¹ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := blkW p0 w
  show ∏ k : Fin 3, colGram M k.castSucc ^ (-2:ℤ) = (colGram M 1 ^ 2 * colGram M 2 ^ 2)⁻¹
  rw [Fin.prod_univ_three]
  have h0 : colGram M (Fin.castSucc 0) = 1 := by simp [colGram, lminor]
  rw [h0]
  simp only [one_zpow, one_mul, zpow_neg, mul_inv, inv_one]
  rfl

theorem pw_nonneg (t : ℂ) : 0 ≤ pw t := by unfold pw; positivity

theorem measurable_pw : Measurable fun t : ℂ => ENNReal.ofReal (pw t) := by
  unfold pw; fun_prop

theorem blkW_diag (w : Low 4 → ℂ) (p0 : ℕ) : ∀ i, (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i i = 1 := by
  intro i; fin_cases i <;> simp [blkW, lowMat]

theorem blkW_upper (w : Low 4 → ℂ) (p0 : ℕ) :
    ∀ i j : Fin 3, i < j → (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [blkW, lowMat]

theorem gB_eq_entries (p0 : ℕ) (pa pb pc : Low 4) (w : Low 4 → ℂ)
    (ha : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 0 = w pa)
    (hb : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 0 = w pb)
    (hc : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 1 = w pc) :
    gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.IntBall.colGram_three_unitLower (blkW (r := 4) p0 w) (blkW_diag w p0) (blkW_upper w p0)
  rw [gB_eq, h1, h2, ha, hb, hc]

theorem lintegral_hB_lt_top_of_pos (p0 : ℕ) (pa pb pc : Low 4) (hab : pa ≠ pb) (hcb : pc ≠ pb)
    (hac : pa ≠ pc)
    (hg : ∀ w : Low 4 → ℂ, gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹)
    (hmix : ∀ p : Low 4, p ≠ pa → p ≠ pb → p ≠ pc → (p.1.2 : ℕ) < p0 ∧ p0 ≤ (p.1.1 : ℕ)) :
    ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  set S : Finset (Low 4) := {pa, pb, pc} with hS
  let f : Low 4 → ℂ → ℝ≥0∞ := fun p x =>
    if p ∈ S then ENNReal.ofReal (pw x) else (Metric.closedBall (0 : ℂ) 1).indicator 1 x
  have hf : ∀ p, Measurable (f p) := by
    intro p; by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact measurable_pw
    · simp only [f, hp, if_false]; exact measurable_one.indicator measurableSet_closedBall
  let U : (Low 4 → ℂ) → ℝ≥0∞ := fun w => ∏ p, f p (w p)
  have hU : Measurable U := Finset.measurable_prod _ fun p _ => (hf p).comp (measurable_pi_apply p)
  have hUfin : ∫⁻ w, U w < ⊤ := by
    have := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun _ : Low 4 => (volume : Measure ℂ))
      (fun p => (hf p).aemeasurable)
    rw [volume_pi, this]
    refine ENNReal.prod_lt_top fun p _ => ?_
    by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact lintegral_pw_lt_top
    · simp only [f, hp, if_false]
      rw [lintegral_indicator measurableSet_closedBall]
      simpa using (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1))
  have hUeq : ∀ w : Low 4 → ℂ, (∀ p, p ∉ S → ‖w p‖ ≤ 1) →
      U w = ENNReal.ofReal (pw (w pa)) * ENNReal.ofReal (pw (w pb)) * ENNReal.ofReal (pw (w pc)) := by
    intro w hw
    simp only [U, f]
    rw [Finset.prod_ite, Finset.prod_eq_one (s := Finset.univ.filter (fun p => p ∉ S)) ?_, mul_one]
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hS, Finset.prod_insert, Finset.prod_insert,
        Finset.prod_singleton, mul_assoc]
      · simpa using hcb.symm
      · simp [hab, hac]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Set.indicator, hw p hp]
  have hpt : ∀ w, hB p0 w ≤ U w + U (Function.update w pb (w pb - w pa * w pc)) := by
    intro w
    by_cases hw : w ∈ {w : Low 4 → ℂ | ∀ p : Low 4, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    · have hw' : ∀ p, p ∉ S → ‖w p‖ ≤ 1 := fun p hp => by
        have h1 : p ≠ pa := fun h => hp (by simp [hS, h])
        have h2 : p ≠ pb := fun h => hp (by simp [hS, h])
        have h3 : p ≠ pc := fun h => hp (by simp [hS, h])
        obtain ⟨k1, k2⟩ := hmix p h1 h2 h3
        exact hw p k1 k2
      have hw'' : ∀ p, p ∉ S → ‖Function.update w pb (w pb - w pa * w pc) p‖ ≤ 1 := fun p hp => by
        have : p ≠ pb := fun h => hp (by simp [hS, h])
        rw [Function.update_of_ne this]; exact hw' p hp
      rw [hUeq w hw', hUeq _ hw'']
      simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb]
      have n1 := pw_nonneg (w pa)
      have n2 := pw_nonneg (w pb)
      have n3 := pw_nonneg (w pc)
      have n4 := pw_nonneg (w pb - w pa * w pc)
      unfold hB
      rw [Set.indicator_of_mem hw, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [hg w]
      have key := _root_.GlobalTheory.flagGram_density_ineq (w pa) (w pb) (w pc)
      have e : pw (w pb - w pa * w pc) = (1 + ‖w pa * w pc - w pb‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
        simp only [pw, norm_sub_rev (w pb)]
      rw [e]
      simp only [pw]
      calc _ ≤ _ := key
        _ = _ := by ring
    · unfold hB; rw [Set.indicator_of_notMem hw]; exact zero_le'
  have hgm : Measurable fun w : Low 4 → ℂ => w pa * w pc :=
    (measurable_pi_apply pa).mul (measurable_pi_apply pc)
  have hgi : ∀ w v : Low 4 → ℂ, (∀ j, j ≠ pb → w j = v j) → w pa * w pc = v pa * v pc := by
    intro w v h; rw [h pa hab, h pc hcb]
  calc ∫⁻ w, hB p0 w ≤ ∫⁻ w, (U w + U (Function.update w pb (w pb - w pa * w pc))) :=
        lintegral_mono hpt
    _ = (∫⁻ w, U w) + ∫⁻ w, U (Function.update w pb (w pb - w pa * w pc)) :=
        lintegral_add_left hU _
    _ = (∫⁻ w, U w) + ∫⁻ w, U w := by
        rw [GlobalTheory.T.lintegral_update_sub_shear' pb (fun w => w pa * w pc) hgm hgi U hU]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hUfin, hUfin⟩

theorem lintegral_hB_four_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  rintro p0 (rfl | rfl)
  · exact lintegral_hB_lt_top_of_pos 1 ⟨(2, 1), by decide⟩ ⟨(3, 1), by decide⟩ ⟨(3, 2), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 1 _ _ _ w rfl rfl rfl) (by decide)
  · exact lintegral_hB_lt_top_of_pos 3 ⟨(1, 0), by decide⟩ ⟨(2, 0), by decide⟩ ⟨(2, 1), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 3 _ _ _ w rfl rfl rfl) (by decide)
end
end GlobalTheory.IntBall.Fin4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
section
open Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosedClass

section Alg

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

noncomputable abbrev cen : S ⊗[ℚ] F →ₐ[S] S ⊗[ℚ] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B)

theorem eq_zero_of_isNilpotent (n : ℕ) (x₀ : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (c : Fin n → S ⊗[ℚ] F)
    (h : IsNilpotent (∑ j, cen S F B (c j) * ((1 : S) ⊗ₜ[ℚ] x₀) ^ (j : ℕ))) : c = 0 := by
  classical
  haveI hcz : CharZero S := charZero_of_injective_algebraMap (algebraMap ℚ S).injective
  obtain rfl : ‹Algebra ℚ S› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨ι, _, L, _, _, _, Φ, ψ, hΦ1, hΦ2⟩ := GlobalTheory.tensor_decomp_factorwise S F B
  have key : ∀ i (j : Fin n), ψ (c j) i = 0 := by
    intro i
    let K := L i
    let e : K ⊗[F] B := (1 : K) ⊗ₜ[F] x₀
    let hp : K[X] := ∑ j : Fin n, C (ψ (c j) i) * X ^ (j : ℕ)
    have hΦw : Φ (∑ j, cen S F B (c j) * ((1 : S) ⊗ₜ[ℚ] x₀) ^ (j : ℕ)) i = aeval e hp := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hp, map_sum, map_mul, map_pow, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hΦ2, hΦ1,
        aeval_C, aeval_X, e]
      rfl
    obtain ⟨m, hm⟩ := h
    have hnil : aeval e (hp ^ (m + 1)) = 0 := by
      rw [map_pow, ← hΦw, pow_succ]
      have := congrArg (fun w => w i) (congrArg Φ hm)
      simp only [map_pow, map_zero, Pi.pow_apply, Pi.zero_apply] at this
      rw [this, zero_mul]
    have hmin : minpoly K e = (minpoly F x₀).map (algebraMap F K) := GlobalTheory.SkNoFactor.minpoly_one_tmul K x₀
    have hd1 : minpoly K e ∣ hp ^ (m + 1) := minpoly.dvd K e hnil
    rw [hmin] at hd1
    have hd2 : (minpoly F x₀).map (algebraMap F K) ∣ hp :=
      (hsep.map.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 hd1
    have hdeglt : hp.degree < ((minpoly F x₀).map (algebraMap F K)).degree := by
      have h1 : hp.degree < n := Polynomial.degree_sum_fin_lt _
      rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite F x₀)), hdeg]
      exact h1
    have hz : hp = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hd2 hdeglt
    intro j
    have := congrArg (fun q : K[X] => q.coeff (j : ℕ)) hz
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      rw [if_neg]
      exact fun h' => hb (Fin.ext h'.symm)
    · simp
  funext j
  apply ψ.injective
  funext i
  simp [key i j]

end Alg

end GlobalTheory.ClosedClass

namespace GlobalTheory.ClosedClass

section Conj

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

noncomputable abbrev trL : S ⊗[ℚ] B →ₗ[S] S :=
  (LinearMap.trace S (S ⊗[ℚ] B)).comp (Algebra.lmul S (S ⊗[ℚ] B)).toLinearMap

theorem trL_conj (g : (S ⊗[ℚ] B)ˣ) (u : S ⊗[ℚ] B) :
    trL S B ((g : S ⊗[ℚ] B) * u * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) = trL S B u := by
  simp only [trL, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem cen_comm (z : S ⊗[ℚ] F) (y : S ⊗[ℚ] B) : Commute (cen S F B z) y := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s' b =>
      simp only [cen, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (s ⊗ₜ[ℚ] algebraMap F B f) * (s' ⊗ₜ[ℚ] b) = (s' ⊗ₜ[ℚ] b) * (s ⊗ₜ[ℚ] algebraMap F B f)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s s',
        Algebra.commutes]
    | add a b ha hb => exact Commute.add_right ha hb
  | add a b ha hb => rw [map_add (f := _)]; exact Commute.add_left ha hb

theorem exists_conj_of_traces [Algebra.IsCentral F B] [IsSimpleRing B] (n : ℕ) (hn : Module.finrank F B = n ^ 2)
    (x₀ : B) (hsep : (minpoly F x₀).Separable) (hdeg : (minpoly F x₀).natDegree = n) (y : S ⊗[ℚ] B)
    (hP : ∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * y ^ i = 0)
    (hT : ∀ (z : S ⊗[ℚ] F) (k : ℕ), trL S B (cen S F B z * y ^ k) =
      trL S B (cen S F B z * ((1 : S) ⊗ₜ[ℚ] x₀) ^ k)) :
    ∃ g : (S ⊗[ℚ] B)ˣ, (g : S ⊗[ℚ] B) * ((1 : S) ⊗ₜ[ℚ] x₀) = y * g := by
  classical
  haveI hcz : CharZero S := charZero_of_injective_algebraMap (algebraMap ℚ S).injective
  obtain rfl : ‹Algebra ℚ S› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : Module.Finite ℚ B := Module.Finite.trans F B
  refine GlobalTheory.SkNoFactor.exists_unit_conj_baseChange S F B n hn x₀ y hsep hdeg hP ?_
  intro c hc
  set e₀ : S ⊗[ℚ] B := (1 : S) ⊗ₜ[ℚ] x₀ with he₀
  let ev : S ⊗[ℚ] B → (S ⊗[ℚ] F)[X] →+* S ⊗[ℚ] B := fun u =>
    Polynomial.eval₂RingHom' (cen S F B).toRingHom u (fun a => cen_comm S F B a u)
  have hev : ∀ u (H : (S ⊗[ℚ] F)[X]), ev u H = ∑ k ∈ Finset.range (H.natDegree + 1), cen S F B (H.coeff k) * u ^ k := by
    intro u H
    show Polynomial.eval₂ _ u H = _
    rw [Polynomial.eval₂_eq_sum_range]
    rfl
  have htr : ∀ H : (S ⊗[ℚ] F)[X], trL S B (ev y H) = trL S B (ev e₀ H) := by
    intro H
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hev, hev, map_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => hT _ k
  let R : (S ⊗[ℚ] F)[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hevR : ∀ u, ev u R = ∑ j : Fin n, cen S F B (c j) * u ^ (j : ℕ) := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [R, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Polynomial.eval₂ _ u (C (c j)) * Polynomial.eval₂ _ u X ^ (j : ℕ) = _
    rw [Polynomial.eval₂_C, Polynomial.eval₂_X]
    rfl
  have hyR : ev y R = 0 := by rw [hevR]; exact hc
  set w := ev e₀ R with hw
  have hpow : ∀ k, 1 ≤ k → LinearMap.trace S (S ⊗[ℚ] B) ((Algebra.lmul S (S ⊗[ℚ] B) w) ^ k) = 0 := by
    intro k hk
    rw [← map_pow, hw, ← map_pow]
    have := htr (R ^ k)
    rw [map_pow, hyR, zero_pow (by omega), map_zero] at this
    exact this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.UnipNormalTrace.isNilpotent_of_trace_pow_eq_zero _ hpow
  have hwn : IsNilpotent w := by
    refine ⟨m, ?_⟩
    have := congrArg (fun f : Module.End S (S ⊗[ℚ] B) => f 1) hm
    rw [← map_pow] at this
    simpa using this
  rw [hw, hevR] at hwn
  exact eq_zero_of_isNilpotent S F B n x₀ hsep hdeg c hwn

end Conj

end GlobalTheory.ClosedClass

namespace GlobalTheory.ClosedClass

section Top

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

theorem conj_val_pow (g e : (S ⊗[ℚ] B)ˣ) (i : ℕ) :
    (((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) ^ i =
      (g : S ⊗[ℚ] B) * (e : S ⊗[ℚ] B) ^ i * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
  rw [← Units.val_pow_eq_pow_val, conj_pow]
  simp [Units.val_pow_eq_pow_val]

theorem cen_mul_conj (z : S ⊗[ℚ] F) (g : (S ⊗[ℚ] B)ˣ) (u : S ⊗[ℚ] B) :
    cen S F B z * ((g : S ⊗[ℚ] B) * u * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) =
      (g : S ⊗[ℚ] B) * (cen S F B z * u) * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
  rw [← mul_assoc, ← mul_assoc, (cen_comm S F B z g).eq, mul_assoc (g : S ⊗[ℚ] B)]

theorem one_tmul_eq_cen (f : F) : (1 : S) ⊗ₜ[ℚ] algebraMap F B f = cen S F B ((1 : S) ⊗ₜ[ℚ] f) := by
  simp [cen]

theorem isClosed_conjClass [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [Algebra.IsCentral F B]
    [IsSimpleRing B] (n : ℕ) (hn : Module.finrank F B = n ^ 2) (x₀ : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (e : (S ⊗[ℚ] B)ˣ) (he : (e : S ⊗[ℚ] B) = (1 : S) ⊗ₜ[ℚ] x₀) :
    letI : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S (S ⊗[ℚ] B)
    IsClosed {y : (S ⊗[ℚ] B)ˣ | ∃ g : (S ⊗[ℚ] B)ˣ, y = g * e * g⁻¹} := by
  classical
  letI : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S (S ⊗[ℚ] B)
  haveI : IsModuleTopology S (S ⊗[ℚ] B) := ⟨rfl⟩
  haveI : Module.Finite ℚ B := Module.Finite.trans F B
  haveI : IsTopologicalRing (S ⊗[ℚ] B) := IsModuleTopology.isTopologicalRing S (S ⊗[ℚ] B)
  let Pv : S ⊗[ℚ] B → S ⊗[ℚ] B := fun y =>
    ∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * y ^ i
  have hPe : Pv (e : S ⊗[ℚ] B) = 0 := by
    have h0 : Polynomial.aeval x₀ (minpoly F x₀) = 0 := minpoly.aeval F x₀
    rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
    have h1 := congrArg (fun b : B => (1 : S) ⊗ₜ[ℚ] b) h0
    simp only [TensorProduct.tmul_zero, TensorProduct.tmul_sum] at h1
    rw [← h1]
    simp only [Pv, he]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  let b := Module.finBasis S (S ⊗[ℚ] B)
  have hset : {y : (S ⊗[ℚ] B)ˣ | ∃ g : (S ⊗[ℚ] B)ˣ, y = g * e * g⁻¹} =
      (⋂ i, {y : (S ⊗[ℚ] B)ˣ | b.coord i (Pv (y : S ⊗[ℚ] B)) = 0}) ∩
      ⋂ (z : S ⊗[ℚ] F) (k : ℕ), {y : (S ⊗[ℚ] B)ˣ | trL S B (cen S F B z * (y : S ⊗[ℚ] B) ^ k) =
        trL S B (cen S F B z * (e : S ⊗[ℚ] B) ^ k)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨g, rfl⟩
      have hPy : Pv ((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) = 0 := by
        have : Pv ((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) =
            (g : S ⊗[ℚ] B) * Pv (e : S ⊗[ℚ] B) * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
          simp only [Pv, conj_val_pow, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [one_tmul_eq_cen, cen_mul_conj]
        rw [this, hPe, mul_zero, zero_mul]
      refine ⟨fun i => by rw [hPy, map_zero], fun z k => ?_⟩
      rw [conj_val_pow, cen_mul_conj, trL_conj]
    · rintro ⟨hP, hT⟩
      have hP' : Pv (y : S ⊗[ℚ] B) = 0 := by
        apply b.forall_coord_eq_zero_iff.1
        exact hP
      rw [he] at hT
      obtain ⟨g, hg⟩ := exists_conj_of_traces S F B n hn x₀ hsep hdeg (y : S ⊗[ℚ] B) hP' hT
      refine ⟨g, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_mul, he, hg, mul_assoc, Units.mul_inv, mul_one]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun z => isClosed_iInter fun k => ?_)
  · have hc : Continuous fun y : (S ⊗[ℚ] B)ˣ => b.coord i (Pv (y : S ⊗[ℚ] B)) := by
      refine (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp ?_
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (Units.continuous_val.pow j)
    exact isClosed_eq hc continuous_const
  · have hc : Continuous fun y : (S ⊗[ℚ] B)ˣ => trL S B (cen S F B z * (y : S ⊗[ℚ] B) ^ k) :=
      (IsModuleTopology.continuous_of_linearMap (trL S B)).comp
        (continuous_const.mul (Units.continuous_val.pow k))
    exact isClosed_eq hc continuous_const

end Top

end GlobalTheory.ClosedClass

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittakerStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompact
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

theorem locCpt_Qv {p : ℕ} [Fact p.Prime] (v : AwayP p) : LocallyCompactSpace (Qv v) := by
  have ho : IsOpen (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) :=
    (Valued.isClopen_integer (v.1.adicCompletion ℚ)).isOpen
  exact (GlobalTheory.LKTrip.LevelExists.isCompact_intCompl v.1).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem secCount_Qv {p : ℕ} [Fact p.Prime] (v : AwayP p) : SecondCountableTopology (Qv v) := by
  haveI := locCpt_Qv v
  letI : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  haveI : ProperSpace (Qv v) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  exact secondCountable_of_proper

theorem units_topA (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [LocallyCompactSpace K] [SecondCountableTopology K]
    (A : Type) [Ring A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] :
    T2Space Aˣ ∧ LocallyCompactSpace Aˣ ∧ SigmaCompactSpace Aˣ := by
  let b := Module.finBasis K A
  let e : A ≃ₗ[K] (Fin (Module.finrank K A) → K) := b.equivFun
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A ≃ₜ (Fin (Module.finrank K A) → K) := ⟨e.toEquiv, hc1, hc2⟩
  haveI : T2Space A := h.isEmbedding.t2Space
  haveI : LocallyCompactSpace A := h.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology A := h.isEmbedding.secondCountableTopology
  haveI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing K A
  haveI : LocallyCompactSpace Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace Aˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology Aˣ := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  haveI : T2Space Aˣ := Units.isEmbedding_embedProduct.t2Space
  exact ⟨inferInstance, inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

theorem topA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := by
  intro p _ G v
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI := locCpt_Qv v
  haveI := secCount_Qv v
  exact units_topA (Qv v) (Qv v ⊗[ℚ] G.C)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_acts_on_realVacua_by_detPowers : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ x₁ x₂ y₁ y₂ : D.what₂.Tau → ℤ, (∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * ((1 / 2 : ℂ) • (1 + sS τ) * compAt θ τ (mt S g) + (1 / 2 : ℂ) • (1 - sS τ)).det ^ y₁ τ * ((1 / 2 : ℂ) • (1 - sS τ) * compAt θ τ (mt S g) + (1 / 2 : ℂ) • (1 + sS τ)).det ^ y₂ τ) • f) := by
  first | exact @GlobalTheory.VacuumChar.vacuum_char | exact GlobalTheory.VacuumChar.vacuum_char | (intros; apply GlobalTheory.VacuumChar.vacuum_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZeroStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negDef_of_hermitianMatrixPositiveIndex_eq_zero : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | (exact @GlobalTheory.herm_negDef_of_sigPosH_eq_zero) | (exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero) | (intros; apply GlobalTheory.herm_negDef_of_sigPosH_eq_zero  <;> assumption)
end

