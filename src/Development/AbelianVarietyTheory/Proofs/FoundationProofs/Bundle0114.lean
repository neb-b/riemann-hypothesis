module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorIterateSuccCongrFrobenius
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.Col.normOp_frob R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := _root_.GlobalTheory.Col.normOp_congr R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', _root_.GlobalTheory.Col.NormCoeff.normOp_smap R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwine
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem translate_mem_aug_of_not_intertwine {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (J : Set G) (θ : G → ℂ) (u : V) (hu : IsEig π J θ u) (y j : G) (hj : j ∈ J) (hc : y * j * y⁻¹ ∈ J)
    (hne : θ j ≠ θ (y * j * y⁻¹)) : π y u ∈ aug π J θ := by
  have h1 : π (y * j * y⁻¹) (π y u) = θ j • π y u := by
    have : π (y * j * y⁻¹) (π y u) = π y (π j u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [this, hu j hj, map_smul]
  have h2 : (θ j - θ (y * j * y⁻¹)) • π y u ∈ aug π J θ := by
    apply Submodule.subset_span
    exact ⟨_, hc, π y u, by rw [h1, sub_smul]⟩
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne)).mp h2

theorem eig_eq_zero_of_mem_aug_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ →
    Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) →
    ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ hJ hN hy u hu he
  classical
  obtain ⟨R, h1, hR, hs⟩ := _root_.GlobalTheory.PsType.aug_avg_zero G V π hπ N _ hN u hu
  simp only [inv_one, one_smul] at hs
  refine (_root_.GlobalTheory.PsType.eig_compl_aug G V π hπ J θ hJ).1 u ?_ he
  rw [← Finset.sum_filter_add_sum_filter_not R (fun y => y ∈ J ∧ θ y = 1)] at hs
  have hA : ∑ y ∈ R.filter (fun y => y ∈ J ∧ θ y = 1), π y u
      = ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) • u := by
    rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro y hy'
    obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hy'
    rw [he y a, b, one_smul]
  have hB : ∑ y ∈ R.filter (fun y => ¬ (y ∈ J ∧ θ y = 1)), π y u ∈ aug π J θ := by
    refine Submodule.sum_mem _ fun y hy' => ?_
    obtain ⟨a, b⟩ := Finset.mem_filter.mp hy'
    obtain ⟨j, hj, hc, hne⟩ := (hy y (hR y a)).resolve_left b
    exact translate_mem_aug_of_not_intertwine π J θ u he y j hj hc hne
  have hc : ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, Finset.mem_filter.mpr ⟨h1, hJ.one, hJ.val_one⟩⟩
  rw [← Submodule.smul_mem_iff _ hc, ← hA, eq_neg_of_add_eq_zero_left hs]
  exact Submodule.neg_mem _ hB

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOrEqNegOfWeierstrassPTorsionEq
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.WpSep

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → x = y ∨ x = -y := by
  intro N _ τ x y hx hy h1
  obtain ⟨hsub, hadd, hmem, -, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact Or.inl ((hsub x y).1 h)
  · right
    have h2 := (tauPair τ).lattice.add_mem (hadd x y) h
    rw [sub_add_cancel] at h2
    have h3 := (hmem (x + y)).1 h2
    exact eq_neg_of_add_eq_zero_left h3

end GlobalTheory.FN.WpSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureAutomorphismRestrictingLocalStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosure_automorphism_restricting_local : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.CuspDown.exists_restrict | exact GlobalTheory.CuspDown.exists_restrict | (intros; apply GlobalTheory.CuspDown.exists_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePow
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial

namespace GlobalTheory.K5.DenseAlg

theorem exists_mem_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
    (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ (k : ℕ) (e : Ωl),
    IsInt (p := p) e → IsAlgZp (p := p) e → ∃ a ∈ A, Cong (p := p) k e (j a) := by
  intro Ω _ _ _ p hp A Ωl _ _ hclo j hA k e he halg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcong : ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
    obtain ⟨P, hP0, hP⟩ := halg
    have : CharZero Ωl := Basic.charZero_of_isClo hclo
    have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hvaluation : ∃ v : Valuation Ωl ℝ≥0, (∀ x, v x ≤ 1 ↔ IsInt (p := p) x) ∧
        v (p : Ωl) < 1 := by
      obtain ⟨_, hdvr, hirr⟩ := _root_.GlobalTheory.K5.completed_laurent_isDVR p
      have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
        rw [hirr.maximalIdeal_eq]
        exact _root_.GlobalTheory.K5.o0_isAdicComplete_span_p p
      have := hclo.alg
      obtain ⟨v, hv⟩ := _root_.GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr
        (O0 p) Ωl hclo.inj
      refine ⟨v, hv, lt_of_le_of_ne ((hv _).2 ?_) ?_⟩
      · simpa [IsInt] using Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
      · intro h_eq
        have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, h_eq, inv_one]
        exact Basic.not_cong_one_zero hclo 1 one_ne_zero
          ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hpne]⟩
    obtain ⟨v, hv, hp1⟩ := hvaluation
    set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
    have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
    have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
    have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
    have hc : φ P.leadingCoeff ≠ 0 := by
      rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
      exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
    have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
    have hp0 : 0 < v (p : Ωl) := (Valuation.pos_iff v).2 hpne
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
      (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
    have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
    have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
      hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
    obtain ⟨Q, R, hdeg, hQR⟩ := Dense.exists_approx P N
    have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
      intro y hy
      rw [map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hy
    have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
      have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
      simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
      rw [map_pow, map_natCast] at this
      exact this
    have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
      rw [eq_sub_of_add_eq hco.symm]
      exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
    have hQ0 : Q.coeff P.natDegree ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, map_zero] at hvQ
      exact hvc.ne hvQ
    have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
    have hRe : v (R.eval₂ φ e) ≤ 1 := by
      rw [eval₂_eq_sum_range]
      refine Valuation.map_sum_le v fun i _ => ?_
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
    have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
      rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
        RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
      exact eq_neg_of_add_eq_zero_left hPe
    obtain ⟨a, ha⟩ := Dense.exists_near_root v j e (v (p : Ωl) ^ k) Q (by
      rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
      exact (hsmall _ hRe).trans_lt hN)
    refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
    · rw [show j a = e - (e - j a) by ring]
      exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
    · rw [map_div₀, map_pow]
      exact div_le_one_of_le₀ ha.le zero_le
    · field_simp
  obtain ⟨a, ha, hc⟩ := hcong
  exact ⟨a, (hA a).2 ha, hc⟩

end GlobalTheory.K5.DenseAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrime
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.ValConjClosure

theorem valuation_intCast_eq_one {Ω : Type} [Field Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : A.valuation (n : Ω) = 1 := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  refine le_antisymm (hle n) (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hn
  have hab' : (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have h1 : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) :=
          mul_le_mul' (hle a) le_rfl
      _ < 1 := by rwa [one_mul]
  have h2 : A.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) :=
          mul_le_mul' (hle b) le_rfl
      _ < 1 := by rwa [one_mul]
  have hadd := A.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
  rw [hab', map_one] at hadd
  exact absurd hadd (not_le.mpr (max_lt h1 h2))

theorem ratCast_mem_iff {Ω : Type} [Field Ω] [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (a : ℚ) : (a : Ω) ∈ A ↔ ¬ p ∣ a.den := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hden0 : (a.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  rw [Rat.cast_def, ← A.valuation_le_one_iff]
  constructor
  · intro ha hd
    have hnum : ¬ (p : ℤ) ∣ a.num := by
      intro h
      have h1 : p ∣ a.num.natAbs := Int.natCast_dvd.mp h
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 a.reduced) hd)
    have hv1 := valuation_intCast_eq_one hp A hA a.num hnum
    obtain ⟨k, hk⟩ := hd
    have hdlt : A.valuation (a.den : Ω) < 1 := by
      rw [hk, Nat.cast_mul, map_mul]
      calc A.valuation (p : Ω) * A.valuation (k : Ω) ≤ A.valuation (p : Ω) * 1 :=
            mul_le_mul' le_rfl (by exact_mod_cast hle k)
        _ < 1 := by rwa [mul_one]
    have hnd : A.valuation (a.num : Ω) ≤ A.valuation (a.den : Ω) := by
      rw [← div_mul_cancel₀ (a.num : Ω) hden0, map_mul]
      calc A.valuation ((a.num : Ω) / (a.den : Ω)) * A.valuation (a.den : Ω) ≤
            1 * A.valuation (a.den : Ω) := mul_le_mul' ha le_rfl
        _ = A.valuation (a.den : Ω) := one_mul _
    rw [hv1] at hnd
    exact absurd (lt_of_le_of_lt hnd hdlt) (lt_irrefl 1)
  · intro hd
    have hv1 : A.valuation (a.den : Ω) = 1 := by
      have h := valuation_intCast_eq_one hp A hA (a.den : ℤ) (by exact_mod_cast hd)
      exact_mod_cast h
    rw [map_div₀, hv1, div_one]
    exact hle a.num

theorem isClosed_apply_mem {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (x : Ω) (T : Set Ω) : IsClosed {σ : Ω ≃ₐ[F] Ω | σ x ∈ T} := by
  let E := IntermediateField.adjoin F ({x} : Set Ω)
  haveI : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (E.fixingSubgroup : Set (Ω ≃ₐ[F] Ω)), ?_,
    E.fixingSubgroup_isOpen.preimage (continuous_const_mul σ⁻¹), ?_⟩
  · intro τ hτ hT
    apply hσ
    have hfix : (σ⁻¹ * τ) x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x
      (IntermediateField.mem_adjoin_simple_self F x)
    have hinv : ∀ y, σ (σ⁻¹ y) = y := fun y => by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply] at hfix
    have he : τ x = σ x :=
      calc τ x = σ (σ⁻¹ (τ x)) := (hinv _).symm
        _ = σ x := by rw [hfix]
    change σ x ∈ T
    rw [← he]
    exact hT
  · show σ⁻¹ * σ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact E.fixingSubgroup.one_mem

theorem exists_conj_of_isGalois {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (A B : ValuationSubring Ω) (h : ∀ a : F, algebraMap F Ω a ∈ A ↔ algebraMap F Ω a ∈ B) :
    ∃ σ : Ω ≃ₐ[F] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  let C : Finset Ω → Set (Ω ≃ₐ[F] Ω) := fun s => {σ | ∀ x ∈ s, σ x ∈ B ↔ x ∈ A}
  have hclosed : ∀ s, IsClosed (C s) := by
    intro s
    have hC : C s = ⋂ x ∈ s, {σ : Ω ≃ₐ[F] Ω | σ x ∈ {y : Ω | y ∈ B ↔ x ∈ A}} := by
      ext σ
      simp [C]
    rw [hC]
    exact isClosed_biInter fun x _ => isClosed_apply_mem x _
  have hne : ∀ s, (C s).Nonempty := by
    intro s
    let L := (FiniteGaloisIntermediateField.adjoin F (s : Set Ω)).toIntermediateField
    have hsL : (s : Set Ω) ⊆ L := FiniteGaloisIntermediateField.subset_adjoin F (s : Set Ω)
    obtain ⟨τ, hτ⟩ := GlobalTheory.KZ.ES.exists_conj_of_same_trace F L (A.comap (algebraMap L Ω))
      (B.comap (algebraMap L Ω)) (by
        intro a
        rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
          ← IsScalarTower.algebraMap_apply]
        exact h a)
    refine ⟨τ.liftNormal Ω, fun x hx => ?_⟩
    have hxL : x ∈ L := hsL hx
    have key := hτ ⟨x, hxL⟩
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at key
    have he : (τ.liftNormal Ω) x = algebraMap L Ω (τ ⟨x, hxL⟩) :=
      AlgEquiv.liftNormal_commutes τ Ω ⟨x, hxL⟩
    rw [he]
    exact key
  have hdir : Directed (fun s t => s ⊇ t) C := by
    intro s t
    exact ⟨s ∪ t, fun σ hσ x hx => hσ x (Finset.mem_union_left _ hx),
      fun σ hσ x hx => hσ x (Finset.mem_union_right _ hx)⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun s => (hclosed s).isCompact) hclosed
  refine ⟨σ, fun x => ?_⟩
  exact Set.mem_iInter.mp hσ {x} x (Finset.mem_singleton_self x)

theorem exists_conj_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  intro Ω _ _ _ p _ A B hA hB
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hA' := (A.mem_nonunits_iff).mp hA
  have hB' := (B.mem_nonunits_iff).mp hB
  apply exists_conj_of_isGalois A B
  intro a
  rw [eq_ratCast, ratCast_mem_iff hp A hA', ratCast_mem_iff hp B hB']

end GlobalTheory.ValConjClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCo
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.PotCoc

def orbSetoid (Γ : Subgroup SL(2, ℤ)) : Setoid Hs where
  r a b := ∃ γ ∈ Γ, mob (ofSL γ) a.1 = b.1
  iseqv := by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    refine ⟨fun a => ⟨1, Γ.one_mem, by simp [hone]⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, h⟩
      refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
      rw [← h, ← hmul _ _ _ a.2, ← map_mul, inv_mul_cancel, map_one, hone]
    · rintro a b c ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, ?_⟩
      rw [map_mul, hmul _ _ _ a.2, h, h']

def rep (Γ : Subgroup SL(2, ℤ)) (a : Hs) : Hs := (Quotient.mk (orbSetoid Γ) a).out

theorem rep_rel (Γ : Subgroup SL(2, ℤ)) (a : Hs) : ∃ γ ∈ Γ, mob (ofSL γ) (rep Γ a).1 = a.1 :=
  Quotient.mk_out (s := orbSetoid Γ) a


open Classical in
def gel (Γ : Subgroup SL(2, ℤ)) (τ : ℂ) : SL(2, ℤ) :=
  if h : τ ∈ Hs then (rep_rel Γ ⟨τ, h⟩).choose else 1

theorem gel_spec (Γ : Subgroup SL(2, ℤ)) {τ : ℂ} (h : τ ∈ Hs) :
    gel Γ τ ∈ Γ ∧ mob (ofSL (gel Γ τ)) (rep Γ ⟨τ, h⟩).1 = τ := by
  simp only [gel, dif_pos h]
  exact (rep_rel Γ ⟨τ, h⟩).choose_spec

theorem rep_eq (Γ : Subgroup SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) {τ : ℂ} (h : τ ∈ Hs)
    (h' : mob (ofSL δ) τ ∈ Hs) : rep Γ ⟨mob (ofSL δ) τ, h'⟩ = rep Γ ⟨τ, h⟩ := by
  unfold rep
  congr 1
  exact Quotient.sound (s := orbSetoid Γ) ⟨δ⁻¹, Γ.inv_mem hδ, by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    show mob (ofSL δ⁻¹) (mob (ofSL δ) τ) = τ
    rw [← hmul _ _ _ h, ← map_mul, inv_mul_cancel, map_one, hone]⟩

theorem slPS {R : Type} [CommRing R] (a c : SL(2, ℤ)) (p : MvPolynomial (Fin 2) R) :
    slP (c : Matrix (Fin 2) (Fin 2) ℤ) (slP (a : Matrix (Fin 2) (Fin 2) ℤ) p) =
      slP ((a * c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) p := by
  rw [GlobalTheory.KZ.Betti.polySlash_polySlash, Matrix.SpecialLinearGroup.coe_mul]

def potOf {R : Type} [CommRing R] (Γ : Subgroup SL(2, ℤ)) (z : SL(2, ℤ) → MvPolynomial (Fin 2) R) (τ : ℂ) :
    MvPolynomial (Fin 2) R :=
  slP (((gel Γ τ)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z (gel Γ τ))

end GlobalTheory.KZ.H3.PotCoc


open GlobalTheory.KZ.H3.PotCoc GlobalTheory.KZ.Betti in
theorem GlobalTheory.KZ.H3.exists_pot_of_isCoc : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N →
    ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l),
      ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  intro R _ w N l hN z hz
  obtain ⟨hmem, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
  set Γ := Gam N l
  have key : ∀ γ ∈ Γ, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (potOf Γ z (mob (ofSL γ) τ)) - potOf Γ z τ = z γ := by
    intro δ hδ τ hτ
    have hτ' : mob (ofSL δ) τ ∈ Hs := hmem _ _ hτ
    obtain ⟨hg1, hg2⟩ := gel_spec Γ hτ
    obtain ⟨hg1', hg2'⟩ := gel_spec Γ hτ'
    rw [rep_eq Γ hδ hτ hτ'] at hg2'
    set g := gel Γ τ
    set g' := gel Γ (mob (ofSL δ) τ)
    have hg : g' = δ * g := by
      have hfree := _root_.GlobalTheory.KZ.gam_free N l hN (g'⁻¹ * (δ * g)) (Γ.mul_mem (Γ.inv_mem hg1') (Γ.mul_mem hδ hg1))
        _ (rep Γ ⟨τ, hτ⟩).2 (by
          rw [map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, hg2, ← hg2',
            ← hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, ← map_mul, inv_mul_cancel, map_one, hone])
      exact (inv_mul_eq_one.mp hfree)
    show slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (slP ((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g')) -
      slP ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g) = z δ
    rw [hg, (hz.2 δ hδ g hg1)]
    have e1 : (δ * g)⁻¹ * δ = g⁻¹ := by group
    have e2 : g * (δ * g)⁻¹ * δ = 1 := by rw [mul_assoc, e1]; group
    simp only [map_add (f := _), slPS, e1, e2, Matrix.SpecialLinearGroup.coe_one, polySlash_one]
    abel
  refine ⟨potOf Γ z, ⟨fun τ => ?_, fun γ hγ => ⟨z γ, key γ hγ⟩⟩, key⟩
  by_cases hτ : τ ∈ Hs
  · exact polySlash_isHomogeneous _ (hz.1 _ (gel_spec Γ hτ).1)
  · have : gel Γ τ = 1 := by simp [gel, dif_neg hτ]
    unfold potOf
    rw [this]
    exact polySlash_isHomogeneous _ (hz.1 _ Γ.one_mem)
end
end

