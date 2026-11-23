module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0095
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0091
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0052
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ImportsAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0066
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0094
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0092
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0086
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FundamentalDomainHaarPlancherel
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.fundamental_domain_haar_plancherel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  first | exact @_root_.PositivityTheory.ThKW.fundamental_domain_plancherel_global | exact _root_.PositivityTheory.ThKW.fundamental_domain_plancherel_global | (intros; apply _root_.PositivityTheory.ThKW.fundamental_domain_plancherel_global <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ModelExistsOfSiegelSmall
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelExists_of_siegelSmall (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.modelExists_of_smallness hG (_root_.PositivityTheory.SiegelWeilFormula.Ald.smallS_of'_k _root_.PositivityTheory.SiegelWeilFormula.Ald.chartFacts_k sliceFacts)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnfK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
theorem unf_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (habs : ∀ x, (∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
      Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    {w₁ : d.G} {cM : (Fin L.n → AE F E) × AF F → d.G} {κ : Measure ((Fin L.n → AE F E) × AF F)} {δ : E}
    (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (hcM : Continuous cM) (hκ : κ.IsAddHaarMeasure) :
    ∃ K : ℂ, ∀ x, _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∫ β in 𝓖',
      (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β ∂lam' := by
  classical
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : Countable (rat2 σ L.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ L.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := Quotient.countable
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_crat_k
  have : ν.IsAddHaarMeasure := hU.2.1
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have hψc : Continuous d.B.ψ := d.ok.good.std.1
  obtain ⟨P, hP, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  obtain ⟨cP, hcP0, hcPt, hPc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lam_map_k (lam := lam) (ν := ν) (lam' := lam') P
  obtain ⟨cK, hcK0, hcKt, hκeq⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.kap_eq_k (ν := ν) (κ := κ)
  obtain ⟨𝓐, h𝓐, h𝓐0, h𝓐t⟩ := exists_fd_fA (F := F)
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hU.2.2.2])
  have : IsFiniteMeasure (lam'.restrict 𝓖') := isFiniteMeasure_restrict.2 (by simp [hc'.2.2.2])
  have : IsFiniteMeasure ((lamA F).restrict 𝓐) := isFiniteMeasure_restrict.2 h𝓐t
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_bijection h
  refine ⟨(cP.toReal : ℂ) * ((cK.toReal : ℂ))⁻¹, fun x => ?_⟩
  have hΦc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  obtain ⟨hi, hs⟩ := habs x
  obtain ⟨e1, fin1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_section_integral (L := L) (nb := nb) (uM := uM) hU.2.2.2 hc.2.2.2 x hi hs
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsC_k (R := R) h hc hU hc' hT h𝓐 hP hPc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z)) (fun r hr hx g => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_term_left_invariant hf z hr hx g) x
  set μO := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμO
  set μI := (ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)) with hμI
  set μN := (lam'.restrict 𝓖').prod μI with hμN
  have hnb' : Continuous nb' := kunf.continuous_nb hc'.1
  have hnew : Continuous fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)) := by
    refine ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_sM'_k (R := R) (L := L)).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul
      ((hcM.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))).mul
        (((L.cont.comp (hnb'.comp continuous_fst))).mul continuous_const))
  have hth' : Continuous fun β : nA σ L.Y L.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_th'_k T'
  let G : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) → nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) → ℂ :=
    fun y p => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM y.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k y.1) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)))))) *
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1
  have hGc : ∀ y, Continuous (G y) := fun y =>
    (hΦc.comp (continuous_const.mul (continuous_const.mul (continuous_const.mul hnew)))).mul (hth'.comp continuous_fst)
  have fin2 : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂μN < ⊤ := by
    have hE := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsE_k (R := R) h hc hU hc' hT h𝓐 hP hPc
      (fun g => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ)
      (Measurable.tsum fun q => (hΦc.comp (continuous_const.mul continuous_id)).enorm.measurable)
      (fun r hr hx g => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_norm_sum_invariant hf z hr hx g) x
    have l1 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x)))‖ₑ) *
        ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂μO < ⊤ := by
      refine lt_of_eq_of_lt ?_ fin1
      refine lintegral_congr fun p => ?_
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun q => (enorm_mul _ _).symm
    rw [hE] at l1
    have l2 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
        ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))))‖ₑ) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1‖ₑ
        ∂μN < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, ENNReal.mul_top hcP0] at l1
      exact lt_irrefl _ l1
    refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) l2
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).2, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => enorm_mul _ _
  have hGm : ∀ y, AEMeasurable (fun p => ‖G y p‖ₑ) μN := fun y => (hGc y).enorm.measurable.aemeasurable
  have hGlt : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂μN < ⊤ := fun y =>
    lt_of_le_of_lt (lintegral_mono fun p => ENNReal.le_tsum (f := fun y => ‖G y p‖ₑ) y) fin2
  have hGi : ∀ y, Integrable (G y) μN := fun y => ⟨(hGc y).aestronglyMeasurable, hGlt y⟩
  have hGs : Summable fun y => ∫ p, ‖G y p‖ ∂μN := by
    have h1 : ∀ y, ∫ p, ‖G y p‖ ∂μN = (∫⁻ p, ‖G y p‖ₑ ∂μN).toReal := fun y =>
      integral_norm_eq_lintegral_enorm (hGi y).aestronglyMeasurable
    simp_rw [h1]
    refine ENNReal.summable_toReal ?_
    rw [← lintegral_tsum hGm]
    exact fin2.ne
  have e3 : ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1 ∂μN =
      ∑' y, ∫ p, G y p ∂μN := by
    rw [(hasSum_integral_of_summable_integral_norm hGi hGs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [G]
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).1, tsum_mul_right]
  have hsI : Summable fun y => ∫ p, G y p ∂μN := hGs.of_norm_bounded (fun y => norm_integral_le_integral_norm _)
  rw [hsI.tsum_sigma] at e3
  have hκ' : ∀ g : (Fin L.n → AE F E) × AF F → ℂ, ∫ c, g c ∂(ν.prod (lamA F)) = ((cK.toReal : ℂ))⁻¹ * ∫ c, g c ∂κ := by
    intro g
    rw [hκeq, integral_smul_measure, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hcK0, hcKt⟩)
  have e4 : ∀ q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ((cK.toReal : ℂ))⁻¹ *
      ∫ β in 𝓖', (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β ∂lam' := by
    intro q'
    have hi' : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, Integrable (G ⟨q', c₀⟩) μN := fun c₀ => hGi _
    have hs' : Summable fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => ∫ p, ‖G ⟨q', c₀⟩ p‖ ∂μN := hGs.sigma_factor q'
    obtain ⟨-, hex⟩ := PositivityTheory.SiegelWeilFormula.Act.exch (μ := lam'.restrict 𝓖') (m := μI) (fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => G ⟨q', c₀⟩) hi' hs'
    have hpr : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ∫ β, ∫ v, G ⟨q', c₀⟩ (β, v) ∂μI ∂(lam'.restrict 𝓖') :=
      fun c₀ => integral_prod _ (hi' c₀)
    simp_rw [hpr]
    rw [← hex, ← integral_const_mul]
    refine integral_congr_ae ?_
    have hmq : Measurable fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
        ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ := Measurable.tsum fun c₀ => (hGc _).enorm.measurable
    have hfinq : ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ ∂μN < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun p => ?_) fin2
      exact (ENNReal.le_tsum (f := fun q'' => ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q'', c₀⟩ p‖ₑ) q').trans
        (ENNReal.tsum_sigma' (fun y => ‖G y p‖ₑ)).symm.le
    rw [hμN, lintegral_prod _ hmq.aemeasurable] at hfinq
    have hae := ae_lt_top (hmq.lintegral_prod_right') hfinq.ne
    filter_upwards [hae] with β hβ
    have hG' : ∀ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, G ⟨q', c₀⟩ (β, v) = (∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
        _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))) *
          _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β := fun v => by simp only [G]; rw [tsum_mul_right]
    simp_rw [hG']
    rw [integral_mul_const]
    have hjj : L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (L.j (nb' β) * x) = L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x := by rw [map_mul, mul_assoc]
    by_cases hθ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β = 0
    · rw [hθ, mul_zero, mul_zero, mul_zero]
    · have hθe : ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β‖ₑ ≠ 0 := enorm_ne_zero.2 hθ
      have hl : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
          ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI < ⊤ := by
        have e5 : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ (β, v)‖ₑ ∂μI = (∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
            ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI) *
              ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β‖ₑ := by
          rw [← lintegral_mul_const' _ _ enorm_ne_top]
          refine lintegral_congr fun v => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun c₀ => enorm_mul _ _
        rw [e5] at hβ
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, ENNReal.top_mul hθe] at hβ
        exact lt_irrefl _ hβ
      have hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' ∈ rat2 σ L.Y := (Quot.out q').2
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqE_k h hf z hU h𝓐 hγ (L.j (nb' β) * x)] at hl
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqC_k h hf z hU h𝓐 hγ (L.j (nb' β) * x) hl, hκ']
      simp_rw [hjj]
      ring
  rw [e1, e2, e3]
  simp_rw [e4]
  rw [tsum_mul_left, Complex.real_smul]
  ring
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

