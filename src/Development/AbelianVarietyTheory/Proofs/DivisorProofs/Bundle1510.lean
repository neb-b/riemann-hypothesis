module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Formalism.PairingDivisors.StatementH
public import Formalism.PairingDivisors.PairingDivisorProofs.Height
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLattice
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine.RightUnfold

theorem isMulRightInvariant_of_lattice {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Λ : Subgroup G)
    [Countable Λ] (𝓑 : Set G) (h𝓑 : IsFundamentalDomain Λ 𝓑 ν) (hfin : ν 𝓑 ≠ ⊤) :
    ν.IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  haveI : (ν.map (· * x)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν x
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map (· * x)) ν
  set c := Measure.haarScalarFactor (ν.map (· * x)) ν
  have h𝓑' : IsFundamentalDomain Λ ((· * x) ⁻¹' 𝓑) ν := by
    refine h𝓑.preimage_of_equiv (quasiMeasurePreserving_mul_right ν x) (e := id)
      Function.bijective_id ?_
    intro g y
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ν ((· * x) ⁻¹' 𝓑) = ν 𝓑 := h𝓑'.measure_eq h𝓑
  have h0 : ν 𝓑 ≠ 0 := h𝓑.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map (· * x)) 𝓑 = ν ((· * x) ⁻¹' 𝓑) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x) 𝓑
  have h1 : (c : ENNReal) * ν 𝓑 = 1 * ν 𝓑 := by
    calc (c : ENNReal) * ν 𝓑 = (c • ν) 𝓑 := by simp [Measure.smul_apply]
      _ = (ν.map (· * x)) 𝓑 := by rw [hc]
      _ = 1 * ν 𝓑 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem unimodular_and_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  intro G _ _ _ _ _ _ _ _ ν Λ _ 𝓑 hν h𝓑 hfin
  haveI hR := isMulRightInvariant_of_lattice ν Λ 𝓑 h𝓑 hfin
  haveI := isInvInvariant_of_right ν
  refine ⟨hR, fun f hf => ?_⟩
  rw [← lintegral_inv_eq_self f, h𝓑.lintegral_eq_tsum' (fun x => f x⁻¹), lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    refine lintegral_congr fun b => ?_
    simp [Subgroup.smul_def]
  · intro γ
    exact (hf.comp (measurable_inv.mul_const _)).aemeasurable

end GlobalTheory.ResLine.RightUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEtaCharacterKillsFiniteIdeleNorm
section
noncomputable section

namespace GlobalTheory.EtaTildeNorm

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

theorem map_finPartI_locF {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra F L] (χ : Formalism.L2.Host.HChar L)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (GlobalTheory.Mem.Chr.locF F v k)) = χ.resFin v k := by
  unfold Formalism.L2.Host.HChar.resFin
  rw [MonoidHom.finsetProd_apply]
  unfold GlobalTheory.Mem.Chr.locF
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (GlobalTheory.Mem.KerDet.finPartI_localIdele Q _)

theorem eq_one (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : Formalism.L2.Host.IsEtaT D.host χ) (x : (AE D)ˣ) :
    χ.1 (finIdl D (x * sgU D x)) = 1 := by
  classical
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have ec : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
  set a : Neutral.B1.Ideles D.host.E := finIdl D (x * sgU D x) with ha_def
  have ha : a ∈ balanced (L := D.host.E) D.host.F := norm_balanced x
  let T : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 D.host.F)
  let m : HeightOneSpectrum (𝓞 D.host.F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Neutral.B1.Ideles D.host.E := ∏ v ∈ T, GlobalTheory.Mem.Chr.locF (L := D.host.E) D.host.F v (Formalism.L2.Host.unif v) ^ m v
  have hm : ∀ w : HeightOneSpectrum (𝓞 D.host.E), m (w.under (𝓞 D.host.F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := ⟨w, rfl⟩
    simp only [m]
    rw [dite_eq_left hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 D.host.F) → valAt w (GlobalTheory.Mem.Chr.locF (L := D.host.E) D.host.F v (Formalism.L2.Host.unif v) ^ m v) = 1 :=
      fun v hv => by rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 D.host.F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl D.host.E := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)

  have h1 : χ.1 (finPartI D.host.E (b⁻¹ * a)) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hu') (fun _ => rfl) fun v y hy =>
      hχ.unr v y (by
        unfold Formalism.L2.Host.IsUnitAt
        rw [hy]
        exact hu' v)

  have h2 : χ.1 (finPartI D.host.E b) = 1 := by
    simp only [b]
    rw [map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_finPartI_locF, hχ.res.1 v, Formalism.L2.Host.etaFin]
    split_ifs with hcard
    · rw [ordF_unif_self, zpow_one]
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hm]
      obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
      have hund : w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) :=
        (under_eq_iff_conjPl c hcm.rank hcm.ne w w').2 (Or.inr (by rw [ec]; exact hw'))
      have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) →
          Q ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (w.under (𝓞 D.host.F)) := fun Q hQ => by
        simp [Formalism.L2.Host.aboveF, hQ]
      have hww : w' = w := Finset.card_le_one.1 hcard.le _ (hmem w' hund) _ (hmem w rfl)
      subst hww
      have e1 : valAt w' a = vl D w' (x : AE D) * vl D w' (x : AE D) := by
        change vl D w' ((x : AE D) * sgA D x) = _
        rw [map_mul, vl_sgA hw' x]
      have h0 : vl D w' (x : AE D) ≠ 0 := by
        intro h
        have := valAt_ne_zero w' a
        rw [e1, h, zero_mul] at this
        exact this rfl
      rw [e1, WithZero.log_mul h0 h0]
      exact Even.neg_one_zpow (Even.add_self _).neg
    · exact one_zpow _
  have e : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
  have e2 : finPartI D.host.E a = a := by rw [ha_def]; exact finPartI_finIdl D _
  rw [← e2, e, map_mul, map_mul, h1, h2, one_mul]

end SlopeTestRemainingChoices

end GlobalTheory.EtaTildeNorm

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem GlobalTheory.EtaTildeNorm.map_finIdl_norm : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ →
    ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 :=
  fun D χ hχ x => GlobalTheory.EtaTildeNorm.eq_one D χ hχ x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMinpolyCoeffZeroGeOfPowMulIntegral
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum.LowVal

theorem coeff_zero_mul_pow_mem {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {β : ℂ} {p : K[X]}
    (h : IsMinPol σ β p) {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral ℤ ((c : ℂ) * β)) :
    ∃ a : 𝓞 K, p.coeff 0 * (c : K) ^ p.natDegree = (a : K) := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hβ : IsIntegral K β := ⟨p, h.1, h.2.2⟩
  have es : (c : K) • β = (c : ℂ) * β := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
  have hγ : IsIntegral (𝓞 K) ((c : K) • β) := by
    rw [es]; exact hc.tower_top
  have e1 := IsIntegrallyClosed.minpoly_smul (R := K) hc0 hβ
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' K hγ
  rw [← h.eq_minpoly] at e1
  refine ⟨(minpoly (𝓞 K) ((c : K) • β)).coeff 0, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, ← coeff_map, ← e2, e1, coeff_scaleRoots, Nat.sub_zero]

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] {w : Formalism.PairingDivisionLocalBalance.Pl K} {l n : ℕ} (hn : n.Coprime l)
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro h
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using hw))

theorem vw_coeff_zero_ge : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ),
    GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) →
    ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  intro K _ _ _ σ β p l N h hl ⟨n, hn, hi⟩ w hw
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.1 hn)
  have hc : IsIntegral ℤ (((n * l ^ N : ℕ) : ℂ) * β) := by
    convert hi using 1
    push_cast
    rw [zpow_natCast]
    ring
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hn0' : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hc0 : ((n * l ^ N : ℕ) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hn0' (pow_ne_zero _ hl0)
  obtain ⟨a, ha⟩ := coeff_zero_mul_pow_mem h hc0 hc
  have h1 : 0 ≤ vw w (p.coeff 0 * ((n * l ^ N : ℕ) : K) ^ p.natDegree) := by
    rw [ha]; exact Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w a
  have hvn : vw w (n : K) = 0 := by
    have := Formalism.DivisionValues.ReductionFirst.vw_unit w (n : 𝓞 K) (natCast_not_mem hn hw)
    simpa using this
  have hvl := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
  by_cases hp0 : p.coeff 0 = 0
  · rw [hp0, Formalism.DivisionValues.ValuationRepresentative.vw_zero]
    have : (0 : ℤ) ≤ ((N * p.natDegree : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  · rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hp0 (pow_ne_zero _ hc0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hc0] at h1
    push_cast at h1
    rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hn0' (pow_ne_zero _ hl0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hl0, hvn] at h1
    push_cast
    nlinarith

end GlobalTheory.FunObj.SqNum.LowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

theorem GlobalTheory.ArchDecay.word_action_square_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (μ : @Measure (Fin n × Fin d → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ p : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (w : List (Op F (Fin n × Fin d))), w.length ≤ p → (∀ o ∈ w, size F o ≤ 1) → ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ((ht g : ℝ) * ht h) ^ k) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ p
  have S := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.ArchDecay.HeisArch.heisD_liftI F E σ n d X W M B.ψ hP.base.std
  obtain ⟨C3, k3, hsz⟩ := _root_.GlobalTheory.ArchDecay.movI_size F E σ B n d X W M χX χW om r s r' s' hP
  set c : ℂ := -(2 * Real.pi * Complex.I) with hc
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_one]
    norm_num
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hcn
    linarith [Real.pi_pos]
  obtain ⟨C4, hwb⟩ := _root_.GlobalTheory.ArchDecay.wordR_L2_le F (Fin n × Fin d)
    (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
    c Φ hΦ μ hμ p
  have hcl : ∀ ζ, ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ (liftI M ζ) f ∈ schA F (Fin n × Fin d) := by
    intro ζ f hf
    rw [hT ζ f hf, dR]
    exact Submodule.add_mem _ (_root_.GlobalTheory.ArchDecay.SchAStab.app_mem_schA F _ (Sum.inl ζ.1) f hf)
      (Submodule.smul_mem _ c (_root_.GlobalTheory.ArchDecay.SchAStab.app_mem_schA F _ (Sum.inr _) f hf))
  have hHcl : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f ∈ schA F (Fin n × Fin d) := by
    intro zs f hf
    induction zs with
    | nil => exact hf
    | cons ζ zs ih => exact hcl ζ _ ih
  have hHR : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f =
      wordR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
        c zs f := by
    intro zs f hf
    induction zs with
    | nil => rfl
    | cons ζ zs ih =>
      show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs f) = dR F _ c ζ (wordR F _ c zs f)
      rw [hT ζ _ (hHcl zs f hf), ih]
  let dirOf : Op F (Fin n × Fin d) →
      (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
    fun o => Sum.elim (fun v => (v, 0)) (fun l => (0, T.symm l)) o
  let cOf : Op F (Fin n × Fin d) → ℂ := fun o => Sum.elim (fun _ => 1) (fun _ => c⁻¹) o
  have hlet : ∀ o, ∀ f ∈ schA F (Fin n × Fin d), app F o f = cOf o • heisD M B.ψ (liftI M (dirOf o)) f := by
    intro o f hf
    rw [hT _ f hf]
    cases o with
    | inl v =>
      show dD F v f = (1 : ℂ) • (dD F v f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] _) 0) f)
      rw [map_zero, mM_zero, smul_zero, add_zero, one_smul]
    | inr l =>
      show mM F l f = c⁻¹ • (dD F 0 f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] _) (T.symm l)) f)
      rw [dD_zero, zero_add, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
  set C0 : ℝ := max 1 ‖(T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ]
    (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ with hC0
  have hC01 : 1 ≤ C0 := le_max_left _ _
  have hdir : ∀ o, ‖dirOf o‖ ≤ C0 * size F o := by
    intro o
    cases o with
    | inl v =>
      show ‖((v, 0) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤
        C0 * ‖v‖
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)]
      exact le_mul_of_one_le_left (norm_nonneg v) hC01
    | inr l =>
      show ‖((0, T.symm l) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤
        C0 * ‖l‖
      rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
      exact (ContinuousLinearMap.le_opNorm (T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ]
        (Fin n × Fin d → mixedEmbedding.mixedSpace F)) l).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg l))
  have hcOf : ∀ o, ‖cOf o‖ ≤ 1 := by
    intro o
    cases o with
    | inl v => show ‖(1 : ℂ)‖ ≤ 1; rw [norm_one]
    | inr l =>
      show ‖c⁻¹‖ ≤ 1
      rw [norm_inv, hcn]
      exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  refine ⟨max C4 0 * (max 1 (max C3 0 * C0)) ^ (2 * p), k3 * (2 * p), fun g h w hw hw1 => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hΨs : om (g, h) Φ ∈ schA F (Fin n × Fin d) := S.pres _ _ hΦ
  have c1 : ∀ w : List (Op F (Fin n × Fin d)), ∃ a : ℂ, ‖a‖ ≤ 1 ∧
      word F w (om (g, h) Φ) = a • wordH M B.ψ (w.map dirOf) (om (g, h) Φ) := by
    intro w
    induction w with
    | nil => exact ⟨1, by rw [norm_one], by rw [one_smul]; rfl⟩
    | cons o w ih =>
      obtain ⟨a, ha, e⟩ := ih
      refine ⟨a * cOf o, ?_, ?_⟩
      · rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) (hcOf o)
      · rw [word_cons, e, app_smul, hlet o _ (hHcl _ _ hΨs), smul_smul]
        rfl
  have c2 : ∀ zs, wordH M B.ψ zs (om (g, h) Φ) = om (g, h) (wordH M B.ψ (zs.map (movI M (g, h))) Φ) := by
    intro zs
    induction zs with
    | nil => rfl
    | cons ζ zs ih =>
      obtain ⟨hA, hL⟩ := _root_.GlobalTheory.ArchDecay.liftI_at_movI F E σ n d X W M (g, h) ζ
      show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs (om (g, h) Φ)) =
        om (g, h) (heisD M B.ψ (liftI M (movI M (g, h) ζ)) (wordH M B.ψ (zs.map (movI M (g, h))) Φ))
      rw [ih, GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine F E σ B n d X W M χX χW om r s r' s' hP (g, h) _ hA _ (hHcl _ _ hΦ), hL]
  obtain ⟨a, ha, e⟩ := c1 w
  have ha' : ‖a‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_one.2 ha
  set zs := (w.map dirOf).map (movI M (g, h)) with hzs
  have hG : wordH M B.ψ zs Φ ∈ schA F (Fin n × Fin d) := hHcl _ _ hΦ
  set ρ : ℝ := max 1 (max C3 0 * C0 * H ^ k3) with hρdef
  have hρ : ∀ ζ ∈ zs, ‖ζ‖ ≤ ρ := by
    intro ζ hζ
    obtain ⟨ζ', hζ', rfl⟩ := List.mem_map.1 hζ
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hζ'
    refine le_max_of_le_right ((hsz g h _).trans ?_)
    have hk : 0 ≤ H ^ k3 := pow_nonneg hH0 _
    calc C3 * H ^ k3 * ‖dirOf o‖ ≤ max C3 0 * H ^ k3 * (C0 * size F o) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hk) (hdir o) (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) hk)
      _ ≤ max C3 0 * H ^ k3 * (C0 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw1 o ho) (zero_le_one.trans hC01))
            (mul_nonneg (le_max_right _ _) hk)
      _ = max C3 0 * C0 * H ^ k3 := by ring
  have hlen : zs.length ≤ p := by rw [hzs, List.length_map, List.length_map]; exact hw
  have hb := hwb ρ (le_max_left _ _) zs hlen hρ
  rw [← hHR zs Φ hΦ] at hb
  have hk1 : 1 ≤ H ^ k3 := one_le_pow₀ hH1
  have hρle : ρ ≤ max 1 (max C3 0 * C0) * H ^ k3 :=
    max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hk1)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hk1))
  have hρ0 : 0 ≤ ρ := zero_le_one.trans (le_max_left _ _)
  calc ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, ‖a‖ₑ ^ 2 * ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ := by
        congr 1
        funext x
        rw [e, c2, Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    _ ≤ ∫⁻ x, ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x => mul_le_of_le_one_left bot_le (pow_le_one₀ bot_le ha')
    _ = ∫⁻ x, ‖wordH M B.ψ zs Φ x‖ₑ ^ 2 ∂μ := S.unit μ hμ _ _ hG
    _ ≤ ENNReal.ofReal (C4 * ρ ^ (2 * p)) := hb
    _ ≤ ENNReal.ofReal (max C4 0 * max 1 (max C3 0 * C0) ^ (2 * p) * H ^ (k3 * (2 * p))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C4 * ρ ^ (2 * p) ≤ max C4 0 * ρ ^ (2 * p) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0 _)
          _ ≤ max C4 0 * (max 1 (max C3 0 * C0) * H ^ k3) ^ (2 * p) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρle _) (le_max_right _ _)
          _ = _ := by rw [mul_pow, ← pow_mul]; ring
end
end

