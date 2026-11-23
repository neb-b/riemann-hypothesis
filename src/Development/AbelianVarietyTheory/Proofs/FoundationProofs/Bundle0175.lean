module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliMain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBound
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem series_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  intro g hg N L τ hτ f hf
  obtain ⟨V, hV, hchar, hgen, hdim⟩ := hτ.2 f hf
  obtain ⟨h1, hmul, hc1, hcmul, -⟩ := _root_.GlobalTheory.BadShare.LevGroup.lev_group g N L
  obtain ⟨hproj, he1, -, -⟩ := _root_.GlobalTheory.BadShare.EpsProj.eps_spec (GG g N) V V.ρ L.Mem L.chi h1 hmul hc1 hcmul
  have hz := (_root_.GlobalTheory.BadShare.ZCalc.zc_calc (GG g N) V).2.2.2 L.e hproj.1
  have hT : 0 < torusCard g f := ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 N f hf).1
  have hr := _root_.GlobalTheory.BadShare.rk_lev_lower g N V V.ρ hgen L
  have hJ := _root_.GlobalTheory.BadShare.lev_card g N L
  have hG := _root_.GlobalTheory.BadShare.card_GG_eq g N
  have hGpos : 0 < Fintype.card (GG g N) := Fintype.card_pos
  have hgpos : 0 < g := hg.out.pos
  set k : ℕ := (if L.sharp = true then L.k else 0) with hk
  rw [← hJ, ← hdim] at hG
  have he : L.e 1 = ((Nat.card {u // L.Mem u} : ℂ))⁻¹ := he1
  set J : ℕ := Nat.card {u // L.Mem u}
  set d : ℕ := Module.finrank ℂ V
  set T : ℕ := torusCard g f
  set r : ℕ := rk V.ρ L.e
  have hJ0 : J ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  have hd0 : d ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  refine ⟨(r : ℝ) / ((g : ℝ) ^ k * (T : ℝ)), ?_, ?_⟩
  · rw [← hchar, hz, he, hG]
    have a1 : (J : ℂ) ≠ 0 := by exact_mod_cast hJ0
    have a2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have a3 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have a4 : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  · have a3 : (0 : ℝ) < T := by exact_mod_cast hT
    have a4 : (0 : ℝ) < (g : ℝ) ^ k := by positivity
    rw [le_div_iff₀ (mul_pos a4 a3)]
    calc (1 - 1 / (g : ℝ)) * (T : ℝ)⁻¹ * ((g : ℝ) ^ k * T) = (1 - 1 / (g : ℝ)) * (g : ℝ) ^ k := by
          field_simp
      _ ≤ r := hr

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelMem


open Polynomial in
theorem mem_range_of_isIntegral {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {α : ℂ}
    (hα : IsIntegral ℚ α) : α ∈ Set.range ε := by
  have h0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots := by
    rw [e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot,
      ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α
  rw [Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

theorem isIntegral_ee {M : ℕ} (hM : 0 < M) : IsIntegral ℚ (ee (1 / (M : ℂ))) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h : ee (1 / (M : ℂ)) ^ M = 1 := by
    rw [ee, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)

theorem isIntegral_of_mem_adjoin {M : ℕ} (hM : 0 < M) {z : ℂ}
    (hz : z ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) : IsIntegral ℚ z := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)
  have h := Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})
  exact IntermediateField.isIntegral_iff.1 h

theorem act_zero (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 0 = x 0 * (γ 0 0 : ℚ) + x 1 * (γ 1 0 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem act_one' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 1 = x 0 * (γ 0 1 : ℚ) + x 1 * (γ 1 1 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩
  all_goals
    have hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    rw [act_zero] at hm0
    rw [act_one'] at hm1
    push_cast
  · linear_combination (γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet
  · linear_combination (γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem exp_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {c M : ℕ} (hM : 0 < M)
    {y : Fin 2 → ℚ} (P : Fin 2 → ℤ) (hP : ∀ i, (M : ℚ) * y i = P i) (hy : GlobalTheory.Sieg.admitted c y) :
    ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c y τ) := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ) := fun i => by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]
  have hlt : (P 0 % (M : ℤ)).toNat < M := by
    have := Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0
  set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1
  set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'
  have hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M := fun i => by
    fin_cases i
    · simp [x', ha0, hr]
    · simp [x', ha1, hr]
  set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn
  have hyx : y = fun i => x' i + n i := by
    funext i
    have h1 : y i = (P i : ℚ) / M := by rw [← hP i]; field_simp
    have h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ) := by
      have h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ) := by rw [Int.emod_def]; ring
      exact_mod_cast h3
    rw [h1, hx'i, h2]
    simp only [n]
    field_simp
    ring
  have hadm : GlobalTheory.Sieg.admitted c x' := by
    refine ⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩
    · rw [hyx]; push_cast; rw [hm0]; ring
    · rw [hyx]; push_cast; rw [hm1]; ring
  have hper : ∀ τ : ℍ, sg c y τ = sg c x' τ := fun τ => by
    rw [hyx]; exact _root_.GlobalTheory.Sieg.Per.sg_add_int c x' n τ hadm
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A, hQ, -, hA, -, -⟩ := hk a1 hadm
  have hε : ∀ j, ε (Function.invFun ε (A j)) = A j := fun j =>
    Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))
  classical
  refine ⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k,
    fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k) := fun i j h => by simpa using h
  rw [← Function.Injective.hasSum_iff hinj (fun m hm => by
    have : ¬ k ≤ m := fun h => hm ⟨(m - k).toNat, by simp; omega⟩
    simp [this])]
  have h1 := (hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))
  have key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ := by
    rw [hper, mul_left_comm, ee, ee, ← Complex.exp_add]
    have : 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0 := by
      ring
    rw [this, Complex.exp_zero, mul_one]
  rw [key] at h1
  have e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) =
      fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M)) := by
    funext j
    simp only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right,
      Int.toNat_natCast, hε]
    rw [mul_left_comm, ee, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact e ▸ h1

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem an_siegel_eq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  intro Ω _ _ _ ε T c x hx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set M : ℕ := (x 0).den * (x 1).den with hMdef
  have hM : 0 < M := Nat.mul_pos (x 0).den_pos (x 1).den_pos
  set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx
  have hMx : ∀ i, (M : ℚ) * x i = Px i := fun i => by
    fin_cases i
    · simp only [hMdef, hPx, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 0)]; ring
    · simp only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 1)]; ring
  have hd : DifferentiableOn ℂ (sgC c x) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)
  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ := by
    intro γ hγ τ
    haveI : NeZero M := ⟨hM.ne'⟩
    obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have d00 : (M : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])
    have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01
    have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10
    have d11 : (M : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])
    obtain ⟨t00, h00⟩ := d00
    obtain ⟨t01, h01⟩ := d01
    obtain ⟨t10, h10⟩ := d10
    obtain ⟨t11, h11⟩ := d11
    have e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i := by
      have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00 := by
        have : γ 0 0 = 1 + M * t00 := by rw [← h00]; ring
        rw [this]; push_cast; ring
      have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11 := by
        have : γ 1 1 = 1 + M * t11 := by rw [← h11]; ring
        rw [this]; push_cast; ring
      have q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01 := by rw [h01]; push_cast; ring
      have q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10 := by rw [h10]; push_cast; ring
      have r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ) := by
        rw [act_zero, q00, q10]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      have r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ) := by
        rw [act_one', q01, q11]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      funext i
      fin_cases i
      · simpa using r0
      · simpa using r1
    rw [e]
    exact _root_.GlobalTheory.Sieg.Per.sg_add_int c x _ τ hx
  refine SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)
  refine exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [← hMx 0, ← hMx 1]
  ring

end GlobalTheory.KZ.SiegelMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SturmSumOverCharactersEqZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sturm_sum_coef_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ,
    (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  classical
  intro k L N hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  choose f hf using fun ε => modularForm_gammaOne_of_MF k L N ε (a ε) hL hN (ha ε)
  have hc : ∀ ε n, (qExpansion 1 (f ε)).coeff n = a ε n := by
    intro ε n
    have := coef_qs (a ε) (ha ε).1 n
    unfold coef at this
    rw [← this, hf]
  have hsum : ∀ (s : Finset (DirichletCharacter ℂ N)) (n : ℕ),
      (qExpansion 1 ⇑(∑ ε ∈ s, f ε)).coeff n = ∑ ε ∈ s, a ε n := by
    intro s n
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero, map_zero]
    | insert e s he ih =>
      rw [Finset.sum_insert he, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ, map_add (f := _), ih, hc, Finset.sum_insert he]
  have h0 : ∑ ε, f ε = 0 := hm _ fun n hn => by
    rw [hsum]
    simpa [Finset.sum_apply] using hz n hn
  funext n
  have := hsum Finset.univ n
  rw [h0] at this
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero] at this
  rw [Finset.sum_apply, ← this]
  rfl

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPermOfNotInjective
section
open Polynomial MeasureTheory

namespace GlobalTheory.CapelliWeyl

theorem sum_perm_of_not_injective {M : Type} [AddCommMonoid M] {n : ℕ}
    (F : (Fin n → Fin n) → M) (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ p : Equiv.Perm (Fin n), F p := by
  symm
  have e : ∑ p : Equiv.Perm (Fin n), F p = ∑ s ∈ Finset.univ.map
      (⟨fun p : Equiv.Perm (Fin n) => (p : Fin n → Fin n), DFunLike.coe_injective⟩ :
        Equiv.Perm (Fin n) ↪ (Fin n → Fin n)), F s := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_
  rw [Finset.mem_map]
  exact ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩

theorem map_det_eq {C W : Type} [CommRing C] [Ring W] {n : ℕ} (f : C →+* W)
    (M : Matrix (Fin n) (Fin n) C) :
    f M.det = ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (p j) j)).prod := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.det_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

theorem normal_sum_of_map {C W : Type} [CommRing C] [Ring W] {n : ℕ} (f : C →+* W)
    (M : Matrix (Fin n) (Fin n) C) (d : Fin n → Fin n → W) :
    ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      ∑ s : Fin n → Fin n, (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod *
        (List.ofFn fun j : Fin n => d (s j) j).prod =
    (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (p j) j)).prod) *
    (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => d (p j) j).prod) := by
  have hdet : ∀ s : Fin n → Fin n, ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod = f (M.submatrix s id).det := by
    intro s
    rw [← Matrix.det_transpose, map_det_eq]
    rfl
  rw [← map_det_eq]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, hdet]
  rw [sum_perm_of_not_injective
    (fun s => f (M.submatrix s id).det * (List.ofFn fun j : Fin n => d (s j) j).prod)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.det_permute, map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]
  · intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij]), map_zero, zero_mul]

theorem exists_comm_lift {W : Type} [Ring W] {n : ℕ} (x : Fin n → Fin n → W)
    (hx : ∀ a b c e, Commute (x a b) (x c e)) :
    ∃ f : MvPolynomial (Fin n × Fin n) ℤ →+* W, ∀ a b, f (MvPolynomial.X (a, b)) = x a b := by
  let S : Set W := Set.range fun p : Fin n × Fin n => x p.1 p.2
  have hS : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hx _ _ _ _).eq
  letI : IsMulCommutative (Subring.closure S) :=
    Subring.isMulCommutative_closure (fun a ha b hb _ => hS a ha b hb)
  open scoped IsMulCommutative in
  refine ⟨(Subring.closure S).subtype.comp
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun p => (⟨x p.1 p.2, Subring.subset_closure ⟨p, rfl⟩⟩ : Subring.closure S))), ?_⟩
  intro a b
  rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
  rfl

theorem capelli_identity : ∀ {W : Type} [Ring W] {n : ℕ} (x d : Fin n → Fin n → W), (∀ a b c e, Commute (x a b) (x c e)) → (∀ a b c e, Commute (d a b) (d c e)) → (∀ a b c e, d a b * x c e - x c e * d a b = if a = c ∧ b = e then 1 else 0) → ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => (∑ k, x k (p j) * d k j) + if p j = j then ((n - 1 - j.val : ℕ) : W) else 0).prod = (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => x (p j) j).prod) * (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => d (p j) j).prod) := by
  intro W _ n x d hx _ hdx
  have hA := PI.HookSteps.Cap.capelli_absolute_value W (Fin n) (Fin n) (fun a t => x t a)
    (fun b t => d t b) (fun a s b t => (hx _ _ _ _).eq)
    (fun a s b t => by
      have h := hdx t b s a
      rw [sub_eq_iff_eq_add'] at h
      rw [h]
      congr 1
      refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2.symm, h1.symm⟩)
    n id id
  simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hA
  obtain ⟨f, hf⟩ := exists_comm_lift x hx
  have hB := normal_sum_of_map f (Matrix.of fun a b => MvPolynomial.X (a, b)) d
  simp only [Matrix.of_apply, hf] at hB
  rw [← hB]
  refine Eq.trans ?_ (hA.trans rfl)
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold PI.HookSteps.Cap.Lw PI.HookSteps.Cap.Eop
  congr 3
  funext j
  have hj : 1 + j.val ≤ n := by have := j.isLt; omega
  rw [Nat.sub_sub, Nat.cast_sub hj, Nat.cast_add, Nat.cast_one, ← sub_sub]
  rfl

end GlobalTheory.CapelliWeyl
end

