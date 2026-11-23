module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0670
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0709
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLe
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.OneZero

theorem one_vector_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → SWFree σ J (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM h₀ hne d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  classical
  obtain ⟨t0, t1, t2⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero F E σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  set I := thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) with hI
  set m0 : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
    fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hm0
  set mi0 := mi (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hmi0
  obtain ⟨sfi, sfv, hnz⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm
  obtain ⟨nzi, nzv⟩ := hnz hne
  obtain ⟨hfin, hsum⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable F E σ hcm M J hJ hM h₀ d b lam hlam m hm
  choose cS hcS using _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeFact.fact_free F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm I t0 t1 t2
  obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ mi0 sfi nzi
  choose B hBm hB0 hBt using fun v => @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m0 v) (sfv v) (nzv v)
  have hLv : ∀ v, IsLocR (Fv F v) := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
      (cS S : ℝ) = cS (insert v S) * (m0 v (latV b v)).toReal := by
    intro S _ v hv
    have hlatm : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) := by
      haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hcm (Fv F v) (hLv v) 1 M
      exact ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 M).2.2.2.1 v).2.measurableSet
    let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
      fun w => (B w).indicator 1
    let φ1 := Function.update φ0 v ((latV b v).indicator 1)
    have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
    have hφ1 : ∀ w, Measurable (φ1 w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [φ1] using measurable_one.indicator hlatm
      · simpa [φ1, Function.update_of_ne hw] using hφ0 w
    have hAφ : Measurable (A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
    have e1 : ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I = (cS S : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w)) :=
      hcS S _ φ0 hAφ hφ0
    have e2 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I = (cS (insert v S) : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ insert v S, ∫⁻ X, φ1 w X ∂(m0 w)) :=
      hcS (insert v S) _ φ1 hAφ hφ1
    have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
        ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
      lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
    rw [e3, e1, Finset.prod_insert hv] at e2
    have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m0 w) = ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w) :=
      Finset.prod_congr rfl fun w hw => by
        have hne : w ≠ v := fun h => hv (h ▸ hw)
        simp only [φ1, Function.update_of_ne hne]
    have hL : ∫⁻ X, φ1 v X ∂(m0 v) = m0 v (latV b v) := by
      simp only [φ1, Function.update_self]
      exact lintegral_indicator_one hlatm
    have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m0 w) = m0 w (B w) := fun w => lintegral_indicator_one (hBm w)
    have hA : ∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0 = mi0 A :=
      lintegral_indicator_one hAm
    rw [hp, hL, hA] at e2
    simp only [hB] at e2
    set Q := ∏ w ∈ S, m0 w (B w) with hQ
    set a := mi0 A with ha
    set L := m0 v (latV b v) with hLdef
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
    have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
    have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
    have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
    have e4 : (cS S : ℝ≥0∞) * (a * Q) = ((cS (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
      rw [e2]; ring
    have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
    have e6 := congrArg ENNReal.toReal e5
    simpa [ENNReal.toReal_mul] using e6
  obtain ⟨c, S₀, -, hS₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail _ (fun v => (m0 v (latV b v)).toReal) cS ∅
    (fun _ => ENNReal.toReal_nonneg) hsum hstep
  have hc : IsEulerProd b I c mi0 m0 := by
    refine ⟨hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    refine (hcS S φinf φ hφi hφ).trans ?_
    have hcS' : (cS S : ℝ≥0∞) = (c : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m0 v.1 (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := cS S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS']
    ring
  suffices h : c = 1 from h ▸ hc
  obtain ⟨φ, C, φc, φp, φf, hb⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero.estimate_zero F E σ hcm M J hJ hM h₀ d b li lam hli hlam μ 𝓕 hμ h𝓕 mi hmi m hm
  obtain ⟨hdf, κ, hκ, hg⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero F E σ hcm M J hJ hM h₀ d b lam hlam m hm nzv
  have : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := by
    have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
    exact (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 M
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := φc.measurable.ennreal_ofReal
  set w := ∫⁻ X, ENNReal.ofReal (φ X) ∂mi0 with hw
  have hw0 : 0 < w.toReal := ENNReal.toReal_pos (fun h => nzi (by
    rw [hw, lintegral_eq_zero_iff hφm] at h
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (h.mono fun X hX =>
      (ENNReal.ofReal_pos.2 (φp X)).ne' hX)))) φf.ne
  have key : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ |(c : ℝ) - 1| * (w.toReal * κ) * (a : ℝ) ≤ |C| := fun k => by
    obtain ⟨a, ha, h1⟩ := hg k
    have ha0 : 0 < a := lt_of_le_of_lt k.zero_le ha
    have haE : (a : E) ≠ 0 := by exact_mod_cast ha0.ne'
    obtain ⟨I', e1, e2⟩ := hb a ha0
    have hA : ∀ v, MeasurableSet {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} := fun v => by
      have hR := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
      obtain ⟨_, _, _, _, -⟩ := hR
      have : BorelSpace (Fv F v) := ⟨rfl⟩
      obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Fv F v)
      have := hB 1 M
      have hu : IsUnit (a : Fv F v ⊗[F] E) := by simpa using (Ne.isUnit haE).map (inclR (F := F) (Fv F v))
      have hK : IsCompact {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} :=
        (Homeomorph.smul hu.unit).isCompact_preimage.2 ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 M).2.2.2.1 v).1
      exact hK.measurableSet
    obtain ⟨-, e3⟩ := _root_.GlobalTheory.CompanionTheory.SW.EulerBox.euler_box F E σ hcm d b 1 M _ c _ _ hc _ _ hφm (fun v => hA v) (fun v => hdf a ha0 v)
      (((_root_.GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 M).1 (Matrix.of fun _ _ => (a : E)) ((Matrix.det_unique _).trans_ne haE)).mono fun v hv => Set.ext fun X => by
        refine Iff.trans (Iff.of_eq (congrArg (· ∈ latV b v) (funext fun p => funext fun i => ?_))) (hv X)
        rw [Subsingleton.elim p 0]
        simp [rmul, mul_comm])
    generalize (∏' v, (m0 v {X : Fin 1 → Fin M → Fv F v ⊗[F] E |
      (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) = P at h1 e2 e3
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hP : 0 ≤ P := le_trans (by positivity) h1
    have e4 := congrArg ENNReal.toReal (e1.symm.trans e3)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hP, ENNReal.coe_toReal, ENNReal.coe_toReal] at e4
    rw [e4, show (c : ℝ) * w.toReal * P - w.toReal * P = (c - 1) * (w.toReal * P) by ring, abs_mul,
      abs_of_nonneg (mul_nonneg hw0.le hP)] at e2
    have hD : 0 < Module.finrank ℚ F := Module.finrank_pos
    have h2 : (a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M) ≤ (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) := by
      rw [← pow_succ']
      refine pow_le_pow_right₀ haR ?_
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      rw [show 2 * (M' + 3) - 2 = M' + 3 + (M' + 1) by omega, mul_add _ (M' + 3)]
      exact Nat.add_le_add_left (Nat.mul_pos hD (Nat.succ_pos _)) _
    refine ⟨a, ha, le_of_mul_le_mul_right ?_ (show (0 : ℝ) < (a : ℝ) ^ (Module.finrank ℚ F * M) by positivity)⟩
    calc _ = |(c : ℝ) - 1| * (w.toReal * (κ * ((a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M)))) := by ring
      _ ≤ |(c : ℝ) - 1| * (w.toReal * P) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left h2 hκ.le).trans h1
      _ ≤ _ := e2.trans (by gcongr; exact le_abs_self C)
  by_contra hne'
  have hp : 0 < |(c : ℝ) - 1| * (w.toReal * κ) :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne'))) (mul_pos hw0 hκ)
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| / (|(c : ℝ) - 1| * (w.toReal * κ)))
  obtain ⟨a, ha, h⟩ := key k
  rw [div_lt_iff₀' hp] at hk
  have : (k : ℝ) < a := by exact_mod_cast ha
  nlinarith

end GlobalTheory.CompanionTheory.SW.OneZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.JtUnif

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel GlobalTheory.Eis GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.SiegelFormula

variable {D : D7}

abbrev ht (D : D7) (n : ℕ) (g : G D n) : ℝ≥0 := iwAbs (modP (D := D) (n := n)) (K D n) g

theorem continuous_ht (n : ℕ) : Continuous (ht D n) := by
  exact (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).continuous_iwAbs
    GlobalTheory.StdUnn.HeightExists.isClosed_P GlobalTheory.StdUnn.PolesModel.continuous_modP
    GlobalTheory.StdUnn.HeightExists.isCompact_K

theorem norm_le_of_law {n : ℕ} {χ : (AE D)ˣ →* Circle} {t : ℂ} {f : G D n → ℂ} (hc : Continuous f)
    (hl : ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      f (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) t * f g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖f g‖ ≤ C * (ht D n g : ℝ) ^ t.re := by
  obtain ⟨C, hC⟩ := (GlobalTheory.StdUnn.HeightExists.isCompact_K (D := D) (n := n)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
  have hlaw : GlobalTheory.Doubling.IndLaw GlobalTheory.StdUnn.PolesModel.modP (χ.comp GlobalTheory.StdUnn.PolesModel.detP) t f := by
    intro p g
    exact hl p.1 p.2 ((GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n)) p) rfl g
  exact (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).norm_le hlaw
    (fun k hk => (hC k hk).trans (le_max_left _ _)) g

theorem ht_mul_le {n : ℕ} {S : Set (G D n)} (hS : IsCompact S) :
    ∃ C : ℝ≥0, ∀ x, ∀ u ∈ S, ht D n (x * u) ≤ C * ht D n x := by
  obtain ⟨C, hC⟩ := ((GlobalTheory.StdUnn.HeightExists.isCompact_K (D := D) (n := n)).prod hS).image
    ((continuous_ht (D := D) n).comp continuous_mul) |>.bddAbove
  refine ⟨C, fun x u hu => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).1 x
  have h1 : ht D n (↑p * k * u) = GlobalTheory.StdUnn.PolesModel.modP p * ht D n (k * u) := by
    rw [mul_assoc]
    exact (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).iwAbs_left p (k * u)
  have h2 : ht D n (↑p * k) = GlobalTheory.StdUnn.PolesModel.modP p :=
    (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).iwAbs_mul p hk
  have h3 : ht D n (k * u) ≤ C := hC ⟨(k, u), Set.mk_mem_prod hk hu, rfl⟩
  calc ht D n (↑p * k * u) = GlobalTheory.StdUnn.PolesModel.modP p * ht D n (k * u) := h1
    _ ≤ GlobalTheory.StdUnn.PolesModel.modP p * C := by gcongr
    _ = C * ht D n (↑p * k) := by rw [h2, mul_comm]

theorem continuous_block_matrix {n : ℕ} {X : Type} [TopologicalSpace X] {f : X → Mx D n n} (hf : Continuous f) :
    Continuous fun x => (blk4 1 (f x) 0 1 : Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.blk4
  exact (Continuous.matrix_fromBlocks continuous_const hf continuous_const continuous_const).matrix_submatrix _ _

theorem exists_continuous_unip (n : ℕ) :
    ∃ N : hermA D n → G D n, Continuous N ∧ ∀ b, mat (N b) = blk4 1 b.1 0 1 := by
  have hex : ∀ b : hermA D n, ∃ g : G D n, mat g = blk4 1 b.1 0 1 :=
    fun b => (GlobalTheory.StdUnn.Model.exists_unip (D := D) b.1).2 b.2
  choose N hN using hex
  refine ⟨N, ?_, hN⟩
  have hinv : ∀ b, mat (N b)⁻¹ = blk4 1 (-b.1) 0 1 := by
    intro b
    have h1 : mat (N b) * blk4 1 (-b.1) 0 1 = 1 := by
      rw [hN, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      simp [GlobalTheory.StdUnn.Model.block_matrix_one]
    calc mat (N b)⁻¹ = mat (N b)⁻¹ * (mat (N b) * blk4 1 (-b.1) 0 1) := by rw [h1, mul_one]
      _ = blk4 1 (-b.1) 0 1 := by
        rw [← mul_assoc, ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one,
          one_mul]
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_block_matrix continuous_subtype_val).congr (fun b => (hN b).symm)
  · exact (continuous_block_matrix continuous_subtype_val.neg).congr (fun b => (hinv b).symm)

theorem exists_hermQ {n : ℕ} (c : ratHerm D n) : ∃ b : HermQ D n, b.1.map (incA D) = c.1.1 := by
  obtain ⟨M, hM⟩ := c.2
  refine ⟨⟨M, fun i j => ?_⟩, hM⟩
  have hM' : M.map (incA D) = c.1.1 := hM
  have hh : GlobalTheory.MixModel.adj (c.1.1 : Mx D n n) = c.1.1 := c.1.2
  have hij := congrFun (congrFun hh i) j
  rw [← hM'] at hij
  have hij' : Formalism.L2.Theta.cA D (incA D (M j i)) = incA D (M i j) := by
    simpa [GlobalTheory.MixModel.adj] using hij
  apply GlobalTheory.RatAut.incA_inj
  rw [← hij']
  simp [Formalism.L2.Theta.cA, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

private theorem leftInv_ht {n : ℕ} : GlobalTheory.AutomorphicL2Unitary.LeftInv (P D n ⊓ GF D n) (ht D n) := by
  intro γ hγ g
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 ((GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n)) ⟨γ, hγ.1⟩) rfl
  have h1 : GlobalTheory.StdUnn.PolesModel.modP (⟨γ, hγ.1⟩ : P D n) = 1 := by
    show GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det ((GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n)) ⟨γ, hγ.1⟩)) = 1
    rw [hu]
    exact GlobalTheory.Doubling.absE_inclR u
  have h := (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).iwAbs_left ⟨γ, hγ.1⟩ g
  rw [h1, one_mul] at h
  exact h

theorem summable_ht {n : ℕ} {s₁ : ℂ} (hs : (n : ℝ) / 2 < s₁.re) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0)
    {N : hermA D n → G D n} (hN : ∀ b, mat (N b) = blk4 1 b.1 0 1) :
    Summable fun c : ratHerm D n => (ht D n (w * N c.1) : ℝ) ^ (s₁ + (n : ℂ) / 2).re := by
  have hmem : ∀ c : ratHerm D n, w * N c.1 ∈ GF D n := fun c => by
    obtain ⟨b, hb⟩ := exists_hermQ c
    exact GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.cell_mem_GF hw b (by rw [hN, hb])
  let i : ratHerm D n → GlobalTheory.Eis.Cosets (P D n) (GF D n) :=
    fun c => GlobalTheory.AutomorphicL2Unitary.mk ((P D n).subgroupOf (GF D n)) ⟨w * N c.1, hmem c⟩
  have hi : Function.Injective i := by
    intro c c' h
    have h' : (⟨w * N c'.1, hmem c'⟩ : GF D n) * (⟨w * N c.1, hmem c⟩)⁻¹ ∈ (P D n).subgroupOf (GF D n) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    rw [Subgroup.mem_subgroupOf] at h'
    have e := GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.cell_inj hw (hN c.1) (hN c'.1) (by simpa using h')
    exact Subtype.ext (Subtype.ext e)
  have hs' := (GlobalTheory.StdUnn.PolesModel.summable_spherical (D := D) (n := n) s₁.re hs).comp_injective hi
  refine hs'.congr (fun c => ?_)
  simp only [Function.comp_apply, i]
  rw [GlobalTheory.Eis.term_mk leftInv_ht, mul_one]
  congr 1
  simp

theorem jt_bound {r : ℕ} {V : HSp D} (hV : 2 * r < V.rank) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank r)} {ω : G D r →* Module.End ℂ (schwartzA θ V.rank r)}
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank r) (hc : Continuous fun g : G D r => (ω g Φ).1 0)
    (Kc : Set (hermA D r)) (hK : IsCompact Kc) :
    ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ Kc, ‖Jt ψ V μ Φ.1 (b + c.1)‖ ≤ u c := by
  obtain ⟨w, hw⟩ := GlobalTheory.StdUnn.Model.exists_weyl (D := D) (n := r)
  obtain ⟨N, hNc, hN⟩ := exists_continuous_unip (D := D) r
  obtain ⟨C, hC0, hC⟩ := norm_le_of_law (t := GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2) hc
    (fun p hp a ha g => GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law D r ψ χ θ V μ ω hω Φ p hp a ha g)
  obtain ⟨C', hC'⟩ := ht_mul_le (D := D) (n := r) (hK.image hNc)
  have hV' : (2 * r : ℝ) < V.rank := by exact_mod_cast hV
  have hs : (r : ℝ) / 2 < (GlobalTheory.StdUnn.s0 V r).re := by
    simp [GlobalTheory.StdUnn.s0]
    linarith
  have hsum := summable_ht hs hw hN
  have ht0 : 0 ≤ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re := by
    simp [GlobalTheory.StdUnn.s0]
    positivity
  refine ⟨fun c => C * (C' : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re *
    (ht D r (w * N c.1) : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re, hsum.mul_left _, fun c b hb => ?_⟩
  have e1 : Jt ψ V μ Φ.1 (b + c.1) = (ω (w * N (b + c.1)) Φ).1 0 :=
    (GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.cell_value hω hw (hN (b + c.1)) Φ).symm
  have e2 : N (b + c.1) = N c.1 * N b := by
    apply GlobalTheory.StdUnn.LeftInvSect.mat_inj
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hN, hN, hN, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp
  have h2 : ht D r (w * N c.1 * N b) ≤ C' * ht D r (w * N c.1) := hC' _ _ ⟨b, hb, rfl⟩
  have h2' : (ht D r (w * N c.1 * N b) : ℝ) ≤ (C' : ℝ) * ht D r (w * N c.1) := by exact_mod_cast h2
  rw [e1, e2, ← mul_assoc]
  calc ‖(ω (w * N c.1 * N b) Φ).1 0‖
      ≤ C * (ht D r (w * N c.1 * N b) : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re := hC _
    _ ≤ C * ((C' : ℝ) * ht D r (w * N c.1)) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h2' ht0) hC0
    _ = C * (C' : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re *
          (ht D r (w * N c.1) : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        ring

theorem exists_weil_value (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (lam : D.host.F) (hlam0 : lam ≠ 0) (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (Mx D B.rank A.rank))
    (𝓖 : Set (Mx D B.rank A.rank)) (hcov : IsCovolOne (ratMx D B.rank A.rank) ν 𝓖) (Φ : schwartzA θ B.rank A.rank) :
    ∃ (χ : (AE D)ˣ →* Circle) (ω : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)),
      IsWeilSch (shift ψ lam) χ θ B ν ω ∧ Continuous fun γ : G D A.rank => (ω γ Φ).1 0 := by
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam0
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hμ : IsSkew μ := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨χ, hχ₁, hχ₂⟩ := GlobalTheory.RawLift.exists_hecke_resEta D B.rank
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨ω, hW⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (dblSp A) B 1 χ hψ
    ⟨continuous_const, fun _ => rfl⟩ hχ₁ hr1 hχ₂
  obtain ⟨omS, hT⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A B χ ω hW ν 𝓖 hcov θ hθ κ
  have hWS : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν omS :=
    ⟨GlobalTheory.StdUnn.transport_levi D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.Unip.transport_unip D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.WeylStd.main D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam⟩
  obtain ⟨f, hf, hfΦ⟩ := ((GlobalTheory.SchSchwartzAll.schSchwartz D) ψ hψ θ hθ A B ν 𝓖 hcov).2.1 Φ.1 Φ.2
  have hΦ : Φ.1 = sch ψ A B ν 𝓖 (ω (((1 : siegel A) : GA D (dblSp A))⁻¹, 1) f) := by
    simp only [OneMemClass.coe_one, inv_one, Prod.mk_one_one, map_one, Module.End.one_apply]
    exact hfΦ.symm
  obtain ⟨-, -, hact⟩ := GlobalTheory.StdUnn.flat_swSec_eq_sect D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam 1 1 f hf Φ hΦ
  have hact' : ∀ g, (omS (κ g) Φ).1 = sch ψ A B ν 𝓖 (ω (g, 1) f) := fun g => by
    have := hact g; rwa [OneMemClass.coe_one, mul_one] at this
  have hval : ∀ g, swSection A B ν 𝓖 ω f g = 1 * (fun γ => (omS γ Φ).1 0) (κ (g * 1)) := fun g => by
    simp only [one_mul, mul_one]
    rw [hact' g, GlobalTheory.Core.Rk.IP.swSection_eq_swSec]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, sch, mixS_dblDec_zero]
  refine ⟨χ⁻¹, omS, hWS, ?_⟩
  have e : (fun γ : G D A.rank => (omS γ Φ).1 0) = swSection A B ν 𝓖 ω f ∘ κ.symm := by
    funext γ
    have := hval (κ.symm γ)
    simp only [one_mul, mul_one, MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e]
  exact (GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous D ψ A B χ ω hW f hf ν 𝓖 hcov).comp
    (GlobalTheory.CompanionTheory.ChartSymm.continuous_symm D A μ hμ κ hκ)

theorem jt_unif : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r))
    (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r →
    ∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧
      ∀ c : ratHerm D r, ∀ b ∈ K, ‖Jt ψ V μ φ (b + c.1)‖ ≤ u c := by
  intro D r V ψ θ μ φ hV hψ hθ h𝓕 hφ Kc hK
  obtain ⟨𝓕, h𝓕⟩ := h𝓕
  obtain ⟨A, hA⟩ : ∃ A : HSp D, A.rank = r :=
    ⟨Formalism.BasicNotions.Examples₂.stdSpace (fun x hx => hx.map (starRingEnd D.host.E).toIntAlgHom) r (fun _ => false) 0 0, rfl⟩
  subst hA
  obtain ⟨ψ₀, hstd, a, ha, hψa⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = GlobalTheory.StdUnn.shift ψ₀ a := AddChar.ext _ _ (fun x => by rw [hψa]; rfl)
  obtain ⟨χ, ω, hω, hc⟩ := exists_weil_value A V ψ₀ hstd a ha θ hθ μ 𝓕 h𝓕 ⟨φ, hφ⟩
  subst hsh
  exact jt_bound hV hω ⟨φ, hφ⟩ hc Kc hK

end GlobalTheory.CompanionTheory.JtUnif

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP
section Generic
variable {R : Type} [CommRing R] {r t n : ℕ}

theorem upperUnipotent_mul (hn : r + t = n) (y y' : Matrix (Fin r) (Fin t) R) :
    bl hn 1 y 0 1 * bl hn 1 y' 0 1 = bl hn 1 (y + y') 0 1 := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotent_zero (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem det_bl_one (hn : r + t = n) (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

end Generic

variable {D : D7} {n t : ℕ} {B W : HSp D}

def shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [upperUnipotent_mul, add_neg_cancel, upperUnipotent_zero]
  inv_val := by rw [upperUnipotent_mul, neg_add_cancel, upperUnipotent_zero]

theorem det_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (shear (D := D) hn y : GL (Fin n) (AE D)) = 1 :=
  Units.ext (det_bl_one hn y)

theorem integral_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) {m : ℕ} (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure)
    (f : Mx D m n → ℂ) : ∫ U, f (mm U (bl hn 1 y 0 1)) ∂μ = ∫ U, f U ∂μ := by
  have h := GlobalTheory.CompanionTheory.IwaAd.integral_mul_right m μ hμ (shear hn y) f
  rw [det_shear, map_one, one_npow, one_mul] at h
  exact h

end GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem shift : Shift := by
  intro D n t B W d hn I Φ y a
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have e := ShiftP.integral_shear hn y I.μ₁ hf.1
    (fun U => projS I.νK Φ (d.jX ⬝ U + d.j0 ⬝ (mm a (bl hn 1 y 0 1))))
  simp only [ikp, ikS]
  rw [← e]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [projS]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [mm, Matrix.mul_assoc, Matrix.add_mul]

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

