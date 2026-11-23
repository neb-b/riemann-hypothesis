module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0305
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormLeOfMeanZero
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.MeanZero

theorem continuous_mean {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C) (hν : ν Cᶜ = 0)
    {f : G → ℂ} (hf : Continuous f) : Continuous fun y => ∫ m, f (m * y) ∂ν := by

  have hae : ∀ᵐ m ∂ν, m ∈ C := by
    rw [ae_iff]
    exact hν
  have hres : ν.restrict C = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hcont : Continuous (Function.uncurry fun (y m : G) => f (m * y)) :=
    hf.comp (continuous_snd.mul continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := ν) hcont hC
  rw [hres] at h
  exact h

theorem norm_le_of_mean_zero {X : Type} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] {D : ℕ}
    (f : Fin D → X → ℂ) (c : Fin D → ℂ) (r : ℝ) (hi : ∀ i, Integrable (f i) ν)
    (h0 : ∀ i, ∫ m, f i m ∂ν = 0) (hb : ∀ᵐ m ∂ν, Real.sqrt (∑ i, ‖f i m - c i‖ ^ 2) ≤ r) :
    Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ r := by
  set S : ℝ := ∑ i, ‖c i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hr0 : 0 ≤ r := by
    obtain ⟨m, hm⟩ := hb.exists
    exact (Real.sqrt_nonneg _).trans hm

  have hint : ∀ i ∈ (Finset.univ : Finset (Fin D)),
      Integrable (fun m => star (c i) * (c i - f i m)) ν :=
    fun i _ => ((integrable_const (c i)).sub (hi i)).const_mul (star (c i))
  have hval : ∫ m, (∑ i, star (c i) * (c i - f i m)) ∂ν = (S : ℂ) := by
    rw [integral_finsetSum _ hint, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (integrable_const _) (hi i), h0 i, integral_const]
    simp [Complex.conj_mul']

  have hbound : ∀ᵐ m ∂ν, ‖∑ i, star (c i) * (c i - f i m)‖ ≤ Real.sqrt S * r := by
    filter_upwards [hb] with m hm
    calc ‖∑ i, star (c i) * (c i - f i m)‖ ≤ ∑ i, ‖star (c i) * (c i - f i m)‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖f i m - c i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star, norm_sub_rev]
      _ ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) * Real.sqrt (∑ i, ‖f i m - c i‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt S * r := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)
  have key : S ≤ Real.sqrt S * r := by
    have h := norm_integral_le_of_norm_le (integrable_const (Real.sqrt S * r)) hbound
    rw [hval, integral_const] at h
    simpa [Complex.norm_real, abs_of_nonneg hS0] using h
  have hsq := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  nlinarith

theorem norm_le_of_cusp (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (g : ℕ)
    (W : Submodule I.E (Fin I.n → I.E)) (D : ℕ) (Fn : Fin D → I.GA → ℂ) (x : I.GA) (c : Fin D → ℂ) (r : ℝ)
    (hg : 1 ≤ g) (hW : I.IsIsot W)
    (hF : ∀ i, Continuous (Fn i) ∧ (∀ γ ∈ I.GFset, ∀ y, Fn i (γ * y) = Fn i y) ∧
      (∀ k ∈ I.Kg g, ∀ y, Fn i (y * (1, k)) = Fn i y) ∧ I.IsCuspFn (I.muA μf) (Fn i))
    (hr : ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W →
      Real.sqrt (∑ i, ‖Fn i ((ν, 1) * x) - c i‖ ^ 2) ≤ r) :
    Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ r := by
  classical
  obtain ⟨ν, hνP, hνQ, Cp, hCp, -, hνCp⟩ := GlobalTheory.T.exists_unipotentQuotient_invariant_probability I W hW
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := _root_.GlobalTheory.UnipApprox.strong_approximation I W hW
  obtain ⟨-, -, -, -, hpos⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  obtain ⟨hT2, hLC, hSC, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hKo, ⟨K, hK⟩, -⟩ := hKg g hg
  haveI := hT2
  haveI := hLC
  haveI := hSC

  have hU : {u : I.Gf | x.2⁻¹ * u * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    refine hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const) |>.mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel, ← hK]
    exact K.one_mem

  have horb : ∀ m ∈ I.NA W, Real.sqrt (∑ i, ‖Fn i (m * x) - c i‖ ^ 2) ≤ r := by
    intro m hm
    obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
    have hm' : γ⁻¹ * m ∈ I.NA W := by
      rw [← hN] at hγN hm ⊢
      exact N.mul_mem (N.inv_mem hγN) hm
    have hk : x.2⁻¹ * (γ⁻¹ * m).2 * x.2 ∈ I.Kg g := hγU
    have heq : ∀ i, Fn i (m * x) = Fn i (((γ⁻¹ * m).1, 1) * x) := by
      intro i
      have h1 := (hF i).2.1 γ hγF (γ⁻¹ * m * x)
      rw [← mul_assoc, mul_inv_cancel_left] at h1
      have h2 : γ⁻¹ * m * x = (((γ⁻¹ * m).1, 1) * x) * (1, x.2⁻¹ * (γ⁻¹ * m).2 * x.2) := by
        ext <;> simp [mul_assoc]
      rw [h1, h2, (hF i).2.2.1 _ hk]
    simp_rw [heq]
    exact hr _ (hsplit _ hm').1

  have hzero : ∀ i, ∫ m, Fn i (m * x) ∂ν = 0 := by
    intro i
    by_contra hne
    have hc := continuous_mean ν hCp hνCp (hF i).1
    have hopen : IsOpen {y | ∫ m, Fn i (m * y) ∂ν ≠ 0} := isOpen_ne_fun hc continuous_const
    have hae := (hF i).2.2.2 W hW ν hνQ
    rw [ae_iff] at hae
    exact (hpos _ hopen ⟨x, hne⟩).ne' hae

  have hint : ∀ i, Integrable (fun m => Fn i (m * x)) ν := by
    intro i
    have hci : Continuous fun m => Fn i (m * x) := (hF i).1.comp (continuous_id.mul continuous_const)
    obtain ⟨B, hB⟩ := hCp.exists_bound_of_continuousOn hci.continuousOn
    have hae : ∀ᵐ m ∂ν, m ∈ Cp := by
      rw [ae_iff]
      exact hνCp
    refine Integrable.of_bound hci.aestronglyMeasurable B ?_
    filter_upwards [hae] with m hm
    exact hB m hm
  have hb : ∀ᵐ m ∂ν, Real.sqrt (∑ i, ‖Fn i (m * x) - c i‖ ^ 2) ≤ r := by
    have hae : ∀ᵐ m ∂ν, m ∈ I.NA W := by
      rw [ae_iff]
      exact hνQ.2.2.1
    filter_upwards [hae] with m hm
    exact horb m hm
  exact norm_le_of_mean_zero ν (fun i m => Fn i (m * x)) c r hint hzero hb

end GlobalTheory.MeanZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneTypeArith
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearMod

theorem fDeg_eq (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by

  have hE : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hdeg : Module.finrank ℚ I.E = Module.finrank ℚ I.F * 2 := by
    rw [← I.cm.deg2, Module.finrank_mul_finrank]
  have hc := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.E
  have hr : NumberField.InfinitePlace.nrRealPlaces I.E = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr hE
  unfold Formalism.HermitianLatticesTheory.fDeg AutInst.f
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem two_vInv_eq (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_eq]
  ring

theorem one_type_arith (L κ Y : ℝ) (a J : ℕ) (hL : 0 ≤ L) (hJ : 1 ≤ J) (haJ : a ≤ J)
    (hκ : κ ≤ Real.exp (-(1 / 2 * J * L))) (hY0 : 0 ≤ Y) (hY : Y ≤ Real.exp (1 / 8 * L)) :
    2 * κ * Y ^ a ≤ 2 * Real.exp (-(3 / 8) * L) := by

  have hYa : Y ^ a ≤ Real.exp (a * (1 / 8 * L)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hY0 hY a
  have hYa0 : 0 ≤ Y ^ a := pow_nonneg hY0 a
  rcases lt_or_ge κ 0 with hκ0 | hκ0
  · have : κ * Y ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ0.le hYa0
    nlinarith [Real.exp_pos (-(3 / 8) * L)]
  · have h1 : κ * Y ^ a ≤ Real.exp (-(1 / 2 * J * L)) * Real.exp (a * (1 / 8 * L)) :=
      mul_le_mul hκ hYa hYa0 (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have ha' : (a : ℝ) ≤ J := by exact_mod_cast haJ
    have h2 : -(1 / 2 * J * L) + a * (1 / 8 * L) ≤ -(3 / 8) * L := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha') hL, mul_nonneg (sub_nonneg.2 hJ') hL]
    have h3 := Real.exp_le_exp.2 h2
    nlinarith

theorem nearModerate : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.FlagMeas.ConstantBound → GlobalTheory.Dec.NearUnip →
    GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate := by
  intro hFM hCB hNU hPB
  unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate
  intro Cg hCg
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.moderate_log_factor_absorbed Cg
  refine ⟨max n₁ (3 ^ 15), ?_⟩
  intro B d p q b hq hC
  have h8 : 8 ≤ max n₁ (3 ^ 15) := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨-, hrd, hf, -, hpq, -, -, hmin, hd, hX, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b h8 hC
  obtain ⟨hDS, hSig, hn₀, hq2, hlrd, hlf, hb, hlb, -, hg1, hgb, -⟩ := id hC

  have hPt := hPB B d p q h hDS hSig hgap (by rw [hmin]; exact h120)
  have hm : 0 ≤ mainTerm B d := by
    show 0 ≤ (∏ v, d v) * B.I.vol B.μf B.fund * (B.e 1).re
    exact mul_nonneg (mul_nonneg hd.le ENNReal.toReal_nonneg) hPt.2.2.2.2.1

  have hn3 : 3 ^ 15 ≤ B.I.n := (le_max_right _ _).trans hn₀
  have hn1 : 1 ≤ B.I.n := le_trans (by norm_num) hn3
  have hlogn : 15 ≤ Real.log B.I.n := by
    have h3 : Real.exp 15 ≤ (B.I.n : ℝ) := by
      have e1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le e1 15
        _ ≤ (B.I.n : ℝ) := by exact_mod_cast hn3
    have := Real.log_le_log (Real.exp_pos 15) h3
    rwa [Real.log_exp] at this
  have hL : 0 ≤ (B.I.n : ℝ) * B.I.f * Real.log B.I.n := by
    have : (0 : ℝ) ≤ Real.log B.I.n := by linarith
    positivity

  have hY := hn₁ B.I.n B.I.f q B.I.rd (B.g : ℝ) b ((le_max_left _ _).trans hn₀) hf hq hq2 hrd hlrd hlf
    hb hlb (by exact_mod_cast hg1) hgb
  have hlX : 0 ≤ Real.log (bigX B b) := Real.log_nonneg (by linarith)
  have hY0 : 0 ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlX)
  have hY1 : 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) ≤
      Real.exp (1 / 8 * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
    hY.1.trans_eq (by congr 1; ring)

  have hA := _root_.GlobalTheory.NearType.near_terms_one_type hFM hNU hPB B Cg _ d p q b h8 hq hC
  have hper : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (mainTerm B d *
          (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)))) := by
    intro J hJmem c
    have hJ := Finset.mem_Icc.1 hJmem
    have hsum : ∑ i, c.blocksFun i = J := c.sum_blocksFun
    have ha : 1 ≤ c.length := c.length_pos_of_pos (by omega)
    have hj1 : ∀ i, 1 ≤ c.blocksFun i := fun i => c.one_le_blocksFun i
    refine (hA.2 c.length c.blocksFun ha hj1 (by rw [hsum]; exact hJ.2)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hm
    have hκ := hCB B.I.E B.I.cm.cmUnram p q c.length c.blocksFun hj1 (by rw [hsum]; exact hJ.2)
      (by rw [hpq]; exact hlogn) (by rw [hpq]; exact hq2) (by rw [two_vInv_eq, hpq]; exact hlrd)
      (by rw [fDeg_eq, hpq]; exact hlf)
    rw [hsum, hpq, fDeg_eq] at hκ
    exact one_type_arith _ _ _ c.length J hL hJ.1 c.length_le (hκ.trans_eq (by congr 1; ring)) hY0 hY1

  have hSm : MeasurableSet {x : B.I.GA | tauStar B q b ≤ least B.I x} :=
    measurableSet_le measurable_const (GlobalTheory.LeastVar.continuous_least B.I hn1).measurable
  have hΦ0 : ∀ x, 1 / 2 ≤ least B.I x →
      {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x = 0 :=
    fun x hx => Set.indicator_apply_eq_zero.2 (fun _ => hA.1 x hx)
  set M : ℝ := mainTerm B d * (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))) with hM
  have h2q : (2 : ENNReal) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x ∂(B.I.muA B.μf)
      = ∫⁻ x in B.fund, {x | tauStar B q b ≤ least B.I x}.indicator
          (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]; rfl
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
          ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
            {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_le_sum_types B p q hSig hn1 _ hΦ0
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal M :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hper J hJ c
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ENNReal) * ENNReal.ofReal M := by
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 : ENNReal) ^ q * ENNReal.ofReal M := by
        gcongr
        exact_mod_cast (GlobalTheory.sum_card_composition_lt q).le
    _ = ENNReal.ofReal (2 ^ q * M) := by
        rw [h2q]; exact (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d) := by
        apply ENNReal.ofReal_le_ofReal
        have e2 : Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) =
            Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        have e1 : Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) =
            Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
        rw [e2, hM, e1]
        calc (2 : ℝ) ^ q * (mainTerm B d * (2 * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)))
            = mainTerm B d * (2 * 2 ^ q * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)) := by ring
          _ ≤ mainTerm B d * Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) :=
            mul_le_mul_of_nonneg_left hY.2 hm
          _ = _ := mul_comm _ _

end GlobalTheory.NearMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeBetweenFrameAndComplementParts
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProj
variable {D : D7}

private theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hc : Submodule.IsFullLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) := by
    refine { toIsLattice := GlobalTheory.Unfold.LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((GlobalTheory.Unfold.LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (GlobalTheory.Unfold.LatLoc.cE D).surjective
  have := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (GlobalTheory.Unfold.LatLoc.cL Λ) hc).2.1 p
  rw [GlobalTheory.Unfold.LatLoc.localLattice_eq]
  exact this

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)


set_option maxHeartbeats 1600000 in
open GlobalTheory.ThetaMove.CommonRef in
theorem lattice_between_parts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  intro D X Y u u' F F' w hZ hG Z FP hB hRel Λ₀ hΛ₀
  letI := hΛ₀
  have hU : ∀ y ∈ Xplus F ⊔ Xplus F', y ∈ orth (VS D) (Xplus F ⊔ Xplus F') → y = 0 := by
    intro y hyU hyW
    by_contra hy
    have hpos := _root_.GlobalTheory.ComplPos.complement_totPos D X Y u u' F F' w hZ hG y hyW hy
    have h0 : (VS D).hT y y = 0 := (mem_orth_iff _ y).1 hyW y hyU
    rw [h0, map_zero] at hpos
    exact lt_irrefl _ hpos
  have hdet := gram_det_isUnit _ hU
  have hcomm : ∀ p : PlF D, ∀ h ∈ (FP p).UW0, ∀ y,
      projP Z p (Xplus F ⊔ Xplus F') (h y) = h (projP Z p (Xplus F ⊔ Xplus F') y) :=
    fun p h hh y => localOrthogonalProj_comm_complementUnitary Z p F F' (FP p) (hB p).1 (hB p).2.1 h hh y
  generalize Xplus F ⊔ Xplus F' = U at hU hdet hcomm ⊢
  obtain ⟨N, hN, hNmem⟩ := exists_nat_smul_le (full_of_span (Submodule.IsFullLattice.span_eq_top (A := D.host.E) (M := Λ₀)))
    (hΛ₀.fg.map ((proj U).restrictScalars (𝓞 D.host.E)))
  have hcast : ∀ v : (VS D).V, (N : D.host.E) • v = (N : 𝓞 D.host.E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨Q, hQ⟩ : ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, Q = (N : D.host.E) • proj U := ⟨_, rfl⟩
  have hQx : ∀ x, Q x = (N : D.host.E) • proj U x := fun x => by rw [hQ]; rfl
  have hQ₀ : Λ₀.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Λ₀ := by
    rintro _ ⟨x, hx, rfl⟩
    show Q x ∈ Λ₀
    rw [hQx, hcast]
    exact hNmem _ ⟨x, hx, rfl⟩
  refine ⟨N, hN, ?_⟩
  intro Λ hΛ hloc
  have hQp : ∀ p : PlF D, ∀ x, baseChange₂ D p (Q x) = ((N : (D.s.atP p).Ep) • projP Z p U) (baseChange₂ D p x) := by
    intro p x
    rw [hQx, LinearMap.smul_apply, baseChange_smul₂, baseChangeAt_proj Z p, map_natCast]
  obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
  obtain ⟨g, hg, hgp⟩ := hloc p
  have hspan₀ := (localLattice_fg_span Z Λ₀ hΛ₀ p).2
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← hgp]
    have e : (LocNG.img g (lattice₂ D Z.M p Λ₀) : Set (Vp D p)) =
        (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) '' (lattice₂ D Z.M p Λ₀ : Set (Vp D p)) := rfl
    rw [e, Submodule.span_image, hspan₀, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  have hΛfull := isFullLattice_of_local_span Z p Λ hΛ hspan
  have hlat' : Submodule.IsLattice D.host.E (Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E))) :=
    Submodule.IsLattice.of_fg D.host.E (hΛ.fg.sup (hΛ.fg.map _))
  have hlatFull : Submodule.IsFullLattice D.host.E (Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E))) := by
    refine { toIsLattice := hlat', span_eq_top := ?_ }
    apply top_unique
    rw [← hΛfull.span_eq_top]
    exact Submodule.span_mono (by intro x hx; exact Submodule.mem_sup_left hx)
  have heq : Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E)) = Λ := by
    refine ((GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 _ Λ hlatFull hΛfull).2 fun p => ?_
    rw [localLattice_sup, sup_eq_left, localLattice_map Z p Q _ (hQp p)]
    obtain ⟨h, hh, himg⟩ := hloc p
    obtain ⟨Qp, hQpdef⟩ : ∃ Qp : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p, Qp = (N : (D.s.atP p).Ep) • projP Z p U :=
      ⟨_, rfl⟩
    rw [← hQpdef]
    have hc : ∀ y, Qp (h y) = h (Qp y) := by
      intro y
      rw [hQpdef, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hcomm p h hh y]
    have hL : (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O) ≤ lattice₂ D Z.M p Λ₀ :=
      calc (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O)
          = lattice₂ D Z.M p (Λ₀.map (Q.restrictScalars (𝓞 D.host.E))) :=
            (localLattice_map Z p Q Qp (fun x => hQpdef ▸ hQp p x) Λ₀).symm
        _ ≤ lattice₂ D Z.M p Λ₀ := localLattice_mono Z p hQ₀
    have := img_map_le Z p Qp h hc _ hL
    rwa [himg] at this
  have key : ∀ y ∈ Λ, Q y ∈ Λ := fun y hy => by
    rw [← heq]
    exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
  intro x hx
  refine Submodule.mem_sup.2 ⟨Q x, ⟨key x hx, ?_⟩, (N : D.host.E) • x - Q x, ⟨?_, ?_⟩, add_sub_cancel _ _⟩
  · show Q x ∈ U
    rw [hQx]
    exact U.smul_mem _ (proj_mem U x)
  · refine Λ.sub_mem ?_ (key x hx)
    rw [hcast]
    exact Λ.smul_mem _ hx
  · show (N : D.host.E) • x - Q x ∈ orth (VS D) U
    rw [hQx, ← smul_sub]
    exact Submodule.smul_mem _ _ (sub_proj_mem_orth U hdet x)

end GlobalTheory.FrameProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalStabiliserPointFromUnitaryFixingFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GamRat

theorem gam_rat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  intro D X u γ
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 γ.2
  obtain ⟨γ₀, hU, h1, h2⟩ := (Formalism.MainNotions.LeviCoordinates.rr_mem_GF _ _).1 hGF
  refine ⟨γ₀, hU, h1, h2, ?_⟩
  intro x hx
  have hf := (Subgroup.mem_prod.1 hH).2 x hx
  rw [h2] at hf
  have : Nontrivial (Af X.B.I.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 X.B.I.F)
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h0 : (0 : w.adicCompletion X.B.I.F) = 1 := congrArg (fun a : Af X.B.I.F => a w) h
    exact zero_ne_one h0
  funext i
  apply Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)
  calc Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x) i)
      = ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ∘ x)) i := RingHom.map_mulVec _ _ _ _
    _ = _ := congrFun hf i

end GlobalTheory.GamRat
end

