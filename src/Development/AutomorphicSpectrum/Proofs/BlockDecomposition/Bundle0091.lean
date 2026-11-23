module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardNonzero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0063
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0083
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCard
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.Sphere

theorem card_fibre {E : Type} [CommRing E] {τ : E →+* E} [Fintype E] {V : Type} [AddCommGroup V]
    [Module E V] [Finite V] (B : HermSp E τ V) {w : V} (hw : IsUnit (B.h w w)) (c : E) :
    Nat.card {v : V // B.h v v = c} =
      ∑ a : E, Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} := by
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  have e1 : {x : E × B.perp w // (B.perpForm hw).h x.2 x.2 = c - x.1 * τ x.1 * B.h w w} ≃
      {v : V // B.h v v = c} :=
    Equiv.subtypeEquiv (B.perpEquiv hw) (by
      rintro ⟨a, v⟩
      have hv : B.h (v : V) w = 0 := v.2
      simp only [HermSp.perpEquiv_apply, HermSp.perpForm_h]
      rw [B.norm_perp hv a]
      constructor
      · intro h; rw [h]; ring
      · intro h; rw [← h]; ring)
  exact e1.symm.trans
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun s => ⟨(s.1, s.2.1), s.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem sum_ite_card {E : Type} [Fintype E] (p : E → Prop) (A B₀ : ℝ) [DecidablePred p] :
    ∑ a, (if p a then B₀ else A) =
      (Nat.card {a // p a} : ℝ) * B₀ + ((Nat.card E : ℝ) - Nat.card {a // p a}) * A := by
  have h : ∀ a, (if p a then B₀ else A) = A + (B₀ - A) * (if p a then 1 else 0) := by
    intro a; split_ifs <;> ring
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_univ, nsmul_eq_mul]
  ring

theorem arith_unit (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q - ε) * (Q / q * (1 + (q - 1) * x)) + (q ^ 2 - (q - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 - x * (ε / q)) := by
  field_simp
  ring

theorem arith_zero (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q * (1 + ε) - ε) * (Q / q * (1 + (q - 1) * x)) +
        (q ^ 2 - (q * (1 + ε) - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 + (q - 1) * (x * (ε / q))) := by
  field_simp
  ring

theorem count : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  intro E _ τ q ε hR m
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast this.ne'
  induction m with
  | zero =>
    intro V _ _ B hc
    have hc1 : Nat.card V = 1 := by simpa using hc
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 hc1
    refine ⟨?_, ?_⟩
    · intro c _ hc0
      have : IsEmpty {v : V // B.h v v = c} :=
        ⟨fun x => hc0 (by
          have h := x.2
          rw [Subsingleton.elim x.1 0, B.zero_left] at h
          exact h.symm)⟩
      rw [Nat.card_of_isEmpty]
      simp
    · have : Subsingleton {v : V // B.h v v = 0} := inferInstance
      rw [Nat.card_of_subsingleton (⟨0, B.zero_left 0⟩ : {v : V // B.h v v = 0})]
      field_simp
      ring
  | succ m ih =>
    intro V _ _ B hc
    have hpow : 1 < q ^ (2 * (m + 1)) := Nat.one_lt_pow (by omega) hq1
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have hfinE : Finite E := Nat.finite_of_card_ne_zero (by
      rw [hR.card]; exact pow_ne_zero _ (by omega))
    have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hw⟩ := GlobalTheory.T.hermitian_space_anisotropic_unit E τ q ε hR V B hnt
    have hP : Nat.card (B.perp w) = q ^ (2 * m) := by
      have h1 : Nat.card E * Nat.card (B.perp w) = Nat.card V := by
        rw [← Nat.card_prod]; exact Nat.card_congr (B.perpEquiv hw)
      rw [hR.card, hc] at h1
      have hq2 : 0 < q ^ 2 := pow_pos (by omega) _
      apply Nat.eq_of_mul_eq_mul_left hq2
      rw [h1]; ring
    obtain ⟨ihc, ihz⟩ := ih (B.perp w) (B.perpForm hw) hP
    classical
    haveI := Fintype.ofFinite E
    have hdfix : τ (B.h w w) = B.h w w := (B.symm w w).symm
    obtain ⟨di, hdi⟩ : ∃ di, B.h w w * di = 1 := hw.exists_right_inv
    have hdifix : τ di = di := by
      have h1 : B.h w w * τ di = 1 := by
        have := congrArg τ hdi
        rwa [map_mul, hdfix, map_one] at this
      calc τ di = (B.h w w * di) * τ di := by rw [hdi, one_mul]
        _ = di * (B.h w w * τ di) := by ring
        _ = di := by rw [h1, mul_one]
    set A : ℝ := (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m) with hA
    set B₀ : ℝ := (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) with hB₀
    have key : ∀ c : E, τ c = c → (Nat.card {v : V // B.h v v = c} : ℝ) =
        (Nat.card {a : E // a * τ a = c * di} : ℝ) * B₀ +
          ((q : ℝ) ^ 2 - Nat.card {a : E // a * τ a = c * di}) * A := by
      intro c hcf
      have hiff : ∀ a : E, a * τ a * B.h w w = c ↔ a * τ a = c * di := by
        intro a
        constructor
        · intro h
          rw [← h, mul_assoc, hdi, mul_one]
        · intro h
          rw [h, mul_assoc, mul_comm di, hdi, mul_one]
      have hterm : ∀ a : E,
          (Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} : ℝ) =
            if a * τ a = c * di then B₀ else A := by
        intro a
        split_ifs with h
        · have h0 : c - a * τ a * B.h w w = 0 := by rw [(hiff a).2 h, sub_self]
          rw [h0]; exact ihz
        · refine ihc _ ?_ ?_
          · rw [map_sub, map_mul, map_mul, hcf, hdfix, hR.inv a]
            ring
          · intro h0
            exact h ((hiff a).1 (sub_eq_zero.1 h0).symm)
      rw [card_fibre B hw c]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_ite_card, hR.card]
      push_cast
      rfl
    have hpw : (q : ℝ) ^ (2 * (m + 1)) = (q : ℝ) ^ (2 * m) * (q : ℝ) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · intro c hcf hc0
      have hn : (Nat.card {a : E // a * τ a = c * di} : ℝ) = (q : ℝ) - ε := by
        have := _root_.GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre E τ q ε hR (c * di)
          (by rw [map_mul, hcf, hdifix])
          (by
            intro h0
            apply hc0
            calc c = c * (di * B.h w w) := by rw [mul_comm di, hdi, mul_one]
              _ = (c * di) * B.h w w := by ring
              _ = 0 := by rw [h0, zero_mul])
        exact_mod_cast this
      rw [key c hcf, hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_unit _ _ _ _ hq0
    · have hn : (Nat.card {a : E // a * τ a = (0 : E) * di} : ℝ) = (q : ℝ) * (1 + ε) - ε := by
        have := _root_.GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero E τ q ε hR
        rw [zero_mul]
        exact_mod_cast this
      rw [key 0 (map_zero τ), hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_zero _ _ _ _ hq0

end GlobalTheory.CompanionTheory.UnrDens.Sphere
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt
section
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem continuous_detW (n : ℕ) : Continuous (fun b : Matrix (Fin n) (Fin n) ℂ => detW b) := by
  unfold detW
  exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop))

theorem measurable_term (n : ℕ) (s : ℝ) :
    Measurable (fun b : hermC n => ENNReal.ofReal (detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s))) := by
  have h : Continuous (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ)) :=
    (continuous_detW n).comp continuous_subtype_val
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨C, hC, hD⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg s (by linarith)
  have hL := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top n (2 * s - 1) (by linarith)
  set L := ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1))) with hLdef
  refine ⟨C * L, ENNReal.mul_ne_top hC hL, fun b' => ?_⟩
  have hB : (b' : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b'.2
  have hw1 := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW n _ hB
  have hwA := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul n _ hB
  have hdet : Matrix.det (1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) ≠ 0 := by
    intro h0
    rw [h0] at hwA
    simp at hwA
    linarith
  have hgm : Measurable (fun u : Fin n → ℂ => ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))) := by
    apply Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → ℂ) × ℝ => ENNReal.ofReal (detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)))
    have hc : Continuous (fun p : (Fin n → ℂ) × ℝ => detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      (continuous_detW _).comp (continuous_blkM.comp
        (by fun_prop : Continuous fun p : (Fin n → ℂ) × ℝ => ((b' : Matrix (Fin n) (Fin n) ℂ), p.1, p.2)))
    exact (hc.measurable.pow_const _).ennreal_ofReal
  rw [GlobalTheory.T.lintegral_linear_change_variables_complex n _ hdet _ hgm, ← hwA]
  have hv : ∀ v : Fin n → ℂ, ∫⁻ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
        (C * ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1)))) := by
    intro v
    have hr : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hterm : ∀ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
        = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
          ENNReal.ofReal (((1 + ∑ i, Complex.normSq (v i)) ^ 2 +
            (d - (star v ⬝ᵥ ((b' : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re) ^ 2) ^ (-s)) := by
      intro d
      have hh := mem_hermC.1 (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d).2
      rw [_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul _ _ hh]
      have e : ((blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : hermC (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          = blkM (b' : Matrix (Fin n) (Fin n) ℂ) ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d := rfl
      rw [e, GlobalTheory.T.detW_block_matrix_formula n _ hB hdet v d, ← hwA, Real.mul_rpow (by linarith) (by positivity),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    simp only [hterm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD (1 + ∑ i, Complex.normSq (v i)) (by linarith)]
    congr 3
    ring_nf
  simp only [hv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
  have e2 : ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ)) *
        ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add (by linarith), Real.rpow_one]
  rw [e2]
  ring

theorem hua_integrable : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDomMonoid
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem isDom_monoid : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), D.IsDom 1 ∧ ∀ t t' : D.T, D.IsDom t → D.IsDom t' → D.IsDom (t * t') := by
  intro G _ _ _ D
  refine ⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn,
    fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩
  rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · have h := h1 _ (h1' n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := h2' _ (h2 n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3 _ (h3' x hx).1).1
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3' _ (h3 x hx).2).2
    rw [Subgroup.coe_mul]
    convert h using 1
    group

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction
section
open ValuativeRel Matrix Topology MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.IwContract

open PositivityTheory.Rg.Tf.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ↔ g ∈ GlobalTheory.SmGL.iwahori F (Fin n) := by
  rw [GlobalTheory.SmGL.mem_iwahori]; rfl


end GlobalTheory.CompanionTheory.IwContract
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JhMultMulLeOfSteps
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CsStages

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

theorem jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr

end GlobalTheory.CompanionTheory.CsStages
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevel
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.Tower

theorem rho_lim {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W} (L : LSeq l S S') (x : S.lim)
    (b c : ℕ) (h : b ≤ c) : L.ρ c b (x.1 c) = x.1 b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact L.ρ_self b _
  | succ d ih =>
    have h' := L.ρ_succ (b + d) b (Nat.le_add_right _ _) (x.1 (b + d + 1))
    rw [x.2 (b + d), ih (Nat.le_add_right _ _)] at h'
    exact h'

theorem lim_eq_pow_smul : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  intro W _ l S S' L hA n x hx
  have hex : ∀ a, ∃ y, L.ν a (n + a) y = x.1 (n + a) := fun a =>
    L.ex₁ a n (n + a) (Nat.add_comm _ _) _ (by rw [rho_lim L x n (n + a) (Nat.le_add_right _ _), hx])
  choose y hy using hex
  have hN : ∀ a w, w ∈ LinearMap.ker (L.ν (a + 1) (n + (a + 1))) →
      S.r a w ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a w hw
    have hw' : L.ν (a + 1) (n + a + 1) w = 0 := hw
    rw [LinearMap.mem_ker, ← L.ν_r a (n + a) (Nat.le_add_left _ _), hw', map_zero]
  have hc : ∀ a, S.r a (y (a + 1)) - y a ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a
    have h1 : L.ν (a + 1) (n + a + 1) (y (a + 1)) = x.1 (n + a + 1) := hy (a + 1)
    rw [LinearMap.mem_ker, map_sub, ← L.ν_r a (n + a) (Nat.le_add_left _ _), h1, x.2 (n + a), hy a,
      sub_self]
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.CompanionTheory.ArtinTower.exists_compatible W S hA (fun a => LinearMap.ker (L.ν a (n + a))) y hN hc
  have key : ∀ a, ((l : W) ^ n) • z.1 (n + a) = x.1 (n + a) := by
    intro a
    have h1 := L.ν_ρ a (n + a) (Nat.le_add_left _ _) (z.1 (n + a))
    have h2 : L.ν a (n + a) (z.1 a) = x.1 (n + a) := by
      have h3 : L.ν a (n + a) (z.1 a - y a) = 0 := hz a
      rw [map_sub, hy a, sub_eq_zero] at h3
      exact h3
    rw [rho_lim L z a (n + a) (Nat.le_add_left _ _), h2, Nat.add_sub_cancel] at h1
    exact h1.symm
  refine ⟨z, Subtype.ext (funext fun c => ?_)⟩
  calc x.1 c = L.ρ (n + c) c (x.1 (n + c)) := (rho_lim L x c (n + c) (Nat.le_add_left _ _)).symm
    _ = L.ρ (n + c) c (((l : W) ^ n) • z.1 (n + c)) := by rw [key]
    _ = ((l : W) ^ n) • L.ρ (n + c) c (z.1 (n + c)) := map_smul _ _ _
    _ = ((l : W) ^ n) • z.1 c := by rw [rho_lim L z c (n + c) (Nat.le_add_left _ _)]

end GlobalTheory.CompanionTheory.Tower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvarianceStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_gauss_sum_congr_invariance : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ), (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R), g * g' = 1 → g' * g = 1 → p * p' = 1 → p' * p = 1 → cT σ g * h * g = D → cT σ p * S * p = E → (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) = ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegCov.gauss_cov | exact GlobalTheory.CompanionTheory.SiegCov.gauss_cov | (intros; apply GlobalTheory.CompanionTheory.SiegCov.gauss_cov <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformVerticalInvarianceStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tube_transform_vertical_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (c, s) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (c, a) t = phi G (c, b) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd <;> assumption)
end

