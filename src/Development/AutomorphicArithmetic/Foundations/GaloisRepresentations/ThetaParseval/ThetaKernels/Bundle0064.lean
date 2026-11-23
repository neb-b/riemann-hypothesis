module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AbsConvK
section
set_option synthInstance.maxHeartbeats 200000

section
set_option linter.style.haveILetI false
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
open ComplexParameterFamilyContinuity
theorem cptDom_k : _root_.PositivityTheory.SiegelWeilFormula.Act.CptDom_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩
  · have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
    obtain ⟨hlc, hsc, ht2, hbo⟩ := kfour.nA_top hσ d.ok.frame
    obtain ⟨K, hK, hc⟩ := kfour.nF_cocompact hσ d.ok.frame
    obtain ⟨hnb, hlam, hfd, h1⟩ := h
    obtain ⟨𝓖₀, hfd₀, hcpt⟩ := addFD_of_cover' (nF σ d.Y d.b) hK hc lam
    exact ⟨𝓖₀, ⟨hnb, hlam, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
  · obtain ⟨hfr, hν, hfd, h1⟩ := h
    haveI : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n
    haveI : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n
    obtain ⟨K, hK, hc⟩ : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ v, ∃ γ ∈ L.ratV, γ + v ∈ K :=
      ratVec_cocompact (F := F) (E := E) L.n
    obtain ⟨𝓤₀, hfd₀, hcpt⟩ := addFD_of_cover' L.ratV hK hc ν
    exact ⟨𝓤₀, ⟨hfr, hν, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
theorem absConv_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨hTG, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨hnb, hlam, hfd, h1⟩ := h𝓖
  obtain ⟨hfr, hν, hfdU, hU1⟩ := h𝓤
  have cu : Continuous uM := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_uM_k L ⟨hfr, hν, hfdU, hU1⟩
  have cn : Continuous nb := kunf.continuous_nb hnb
  have cφ : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  set m : (Fin L.n → AE F E) × nA σ d.Y d.b → d.G := fun p => nb p.2 * (uM p.1 * x) with hm
  have cm : Continuous m := (cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)
  have hKc : IsCompact (closure 𝓤 ×ˢ closure 𝓖) := hc𝓤.prod hc𝓖
  obtain ⟨u, hu, hub⟩ := (hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) (hKc.image cm)
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have cψ := kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b) hψ.1 T.1.1
  obtain ⟨Mψ, hMψ⟩ := hc𝓖.exists_bound_of_continuousOn cψ.continuousOn
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [hU1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖 := by
    rw [ae_iff]
    refine measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ) ?_ ?_
    · intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    · have eU : (closure 𝓤)ᶜ ∩ 𝓤 = ∅ := (show Disjoint (closure 𝓤)ᶜ 𝓤 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓤)ᶜ) (h' : y ∈ 𝓤) => hy (subset_closure h')).inter_eq
      have eG : (closure 𝓖)ᶜ ∩ 𝓖 = ∅ := (show Disjoint (closure 𝓖)ᶜ 𝓖 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓖)ᶜ) (h' : y ∈ 𝓖) => hy (subset_closure h')).inter_eq
      refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eU, measure_empty, zero_mul]
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eG, measure_empty, mul_zero]
  have hbd : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, ∀ᵐ p ∂μ, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ≤ |u q| * |Mψ| := by
    intro q
    filter_upwards [hS] with p hp
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, norm_mul]
    refine mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hcq : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) := fun q =>
    (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)
  have hint : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) μ := fun q =>
    Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))
  calc ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂μ ≤ ∫ _p, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AldAscBigT
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald.Asc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.SiegelWeilFormula.Ald.Asc
namespace PositivityTheory.SiegelWeilFormula.Ald
open Asc in
theorem bigT_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k := by
  intro hT _hA F E _ _ _ _ _ σ d dd0 had hrat
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ
    (Fin d.m × Fin d.n × Fin 2) _ d.dd dd0 (by exact d.ok.dbl.rat) (by exact hrat)
  have hop := hS.1
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = dd0.rho d.B.ψ w (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ]
    simp
  have rhoS' : ∀ w, ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), S0' (dd0.rho d.B.ψ w φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm (Fin d.m × Fin d.n × Fin 2) := hop.adm' d.l d.ok.dbl.adm
  have hsurj : ∀ y : Fin d.m × Fin d.n × Fin 2 → AF F, ∃ Z : Mx F E d.m d.n,
      dd0.e (Z * (incM F d.b.1.toCols₁)ᵀ) = (0, y) := by
    intro y
    obtain ⟨Z, X, hw⟩ := eq_split d.b (dd0.e.symm (0, y))
    have h1 := had Z X
    rw [← hw, LinearEquiv.apply_symm_apply] at h1
    have h2 := had Z 0
    rw [Matrix.zero_mul, add_zero, crdB_zero] at h2
    refine ⟨Z, h2.trans ?_⟩
    have h3 := congrArg Prod.snd h1
    simp only at h3
    rw [← h3]
  obtain ⟨t, ht0⟩ := d.ok.frame.2
  have ht : (d.b.1.toCols₁ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * (t.1 : Matrix (Fin d.n) (Fin d.n) E) := ht0
  have hinv : ∀ (y : Fin d.m × Fin d.n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2),
      l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨Z, hZ⟩ := hsurj y
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = dd0.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) φ := by
      funext x
      simp [Darboux.rho, hZ, schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    have e2 : Z * (incM F d.b.1.toCols₁)ᵀ = ((Z * (incM F t.1)ᵀ : Mx F E d.m d.n)) *
        ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)))ᵀ := by
      rw [ht, incM_mul', incM_diagCols, Matrix.transpose_mul]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [e2]
    exact d.ok.dbl.kill _ _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CharInvForm.main F d.B.ψ hψ (Fin d.m × Fin d.n × Fin 2) l' hadm hinv
  have hform : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = c * S0 Φ (crdB d.bs X) := by
    intro Φ hΦ X
    have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ hΦ
    have h0 := had 0 X
    rw [Matrix.zero_mul, zero_add] at h0
    simp only [Bf_zero_left] at h0
    have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
      rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
      rfl
    rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ]
    simp [Darboux.rho, h0, schr]
  refine ⟨S0, S0', c, ?_, hS, hform⟩
  rintro rfl
  obtain ⟨φ, hφ, hφ0⟩ := _root_.GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F d.κ
  have hz : d.T φ = 0 := by
    funext X
    rw [hform φ hφ X, zero_mul]
    rfl
  exact hφ0 (by rw [(hT.1 F E σ d).2.2 φ hφ hz]; rfl)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
section
set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem nilpotentMap_add (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a : E) : σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good a
theorem cc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (z : AE F E) : cA σ (cA σ z) = z := kfour.cA_cA' σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d) z
theorem idx_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (i : Fin d.n) : i = L.i₀ ∨ ∃ k, i = L.em k := by
  by_cases h : i = L.i₀
  · exact Or.inl h
  · obtain ⟨k, hk⟩ := (L.rng i).1 h
    exact Or.inr ⟨k, hk.symm⟩
theorem sum_split_k {M : Type} [AddCommMonoid M] (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : Fin d.n → M) :
    ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  have himg : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [L.rng i]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀), ← himg, Finset.sum_image (fun a _ b _ h => L.inj h)]
theorem uA_mul_neg_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) = 1 := by
  have e : ∀ v, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L v = 1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L v := fun v => rfl
  have hs : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u) = 0 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, ← Finset.sum_add_distrib, Pi.neg_apply, ← Matrix.single_add, add_neg_cancel, neg_add_cancel,
      Matrix.single_zero, Finset.sum_const_zero]
  rw [e, e]
  calc (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) * (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u)) = 1 + (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u)) + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u) := by
        noncomm_ring
    _ = 1 := by rw [hs, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero]; simp
theorem blockDiagonal_preserves_form_iff (x : d.G) (h21 : (inFrame d.b x).toBlocks₂₁ = 0) :
    ((inFrame d.b x).toBlocks₁₁)ᵀ * ((inFrame d.b x).toBlocks₂₂).map (cA σ) = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hf := kunf.frame_eq hε x
  set M := inFrame d.b x with hMdef
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21]; exact (Matrix.fromBlocks_toBlocks M).symm
  rw [hM] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  exact h12
theorem lr_of_k {x : d.G} {a β D ainv : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks a β 0 D) (ha : a * ainv = 1) : D = ainvᵀ.map (cA σ) := by
  have hx := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.blockDiagonal_preserves_form_iff x (by rw [h]; rfl)
  rw [h] at hx
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂] at hx
  have e2 : D.map (cA σ) = ainvᵀ := by
    calc D.map (cA σ) = (ainvᵀ * aᵀ) * D.map (cA σ) := by
          rw [← Matrix.transpose_mul, ha, Matrix.transpose_one, Matrix.one_mul]
      _ = ainvᵀ := by rw [Matrix.mul_assoc, hx, Matrix.mul_one]
  rw [← e2]
  ext i j
  simp [Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d]
theorem eq_of_upper_k {x y : d.G} (hx : (inFrame d.b x).toBlocks₂₁ = 0) (hy : (inFrame d.b y).toBlocks₂₁ = 0)
    (h11 : (inFrame d.b x).toBlocks₁₁ = (inFrame d.b y).toBlocks₁₁)
    (h12 : (inFrame d.b x).toBlocks₁₂ = (inFrame d.b y).toBlocks₁₂) : x = y := by
  have ex := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.blockDiagonal_preserves_form_iff x hx
  have ey := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.blockDiagonal_preserves_form_iff y hy
  rw [h11] at ex
  have ey' : ((inFrame d.b y).toBlocks₂₂).map (cA σ) * ((inFrame d.b y).toBlocks₁₁)ᵀ = 1 := mul_eq_one_comm.1 ey
  have hD : ((inFrame d.b x).toBlocks₂₂).map (cA σ) = ((inFrame d.b y).toBlocks₂₂).map (cA σ) := by
    calc _ = (((inFrame d.b y).toBlocks₂₂).map (cA σ) * ((inFrame d.b y).toBlocks₁₁)ᵀ) *
          ((inFrame d.b x).toBlocks₂₂).map (cA σ) := by rw [ey', Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ex, Matrix.mul_one]
  have hD' : (inFrame d.b x).toBlocks₂₂ = (inFrame d.b y).toBlocks₂₂ := by
    ext i j
    have := congrArg (cA σ) (congrFun (congrFun hD i) j)
    simpa only [Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d] using this
  exact _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d (Matrix.ext_iff_blocks.2 ⟨h11, h12, hx.trans hy.symm, hD'⟩)
variable {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inFrame_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA⟩ := h.cf c
  rw [hA, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k hA (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L c.1)]
theorem eps_mul_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ((R.ε : ℤ) : AE F E) * ((R.ε : ℤ) : AE F E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem eps_mulE_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ((R.ε : ℤ) : E) * ((R.ε : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem eA_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R = ((R.ε : ℤ) : AE F E) := map_intCast _ _
theorem sB_i0i0_k (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b L.i₀ L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm]
theorem sB_i0em_k (b : Fin L.n → AE F E) (l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b L.i₀ (L.em l) = b l := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm,
    L.inj.eq_iff]
theorem section_entry_embedded_row (b : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b (L.em k) L.i₀ = -(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b k)) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm,
    L.inj.eq_iff]
theorem sB_emem_k (b : Fin L.n → AE F E) (k l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b (L.em k) (L.em l) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm]
theorem sB_cond_k (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b ∈ kfour.nCond σ d.n R.ε := by
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b)ᵀ = -((((R.ε : ℤ) : AE F E)) • (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b).map (cA σ))
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R
  ext i j
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L j with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_entry_embedded_row,
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_emem_k, map_zero, smul_zero, neg_zero, smul_eq_mul, map_neg, map_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_eq_k]
  all_goals (try simp only [map_intCast])
  all_goals first | (simp; done) | (simp only [mul_neg, neg_neg, neg_mul]; rw [← mul_assoc, e2, one_mul])
theorem continuous_sB_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k
  refine continuous_finsetSum _ fun j _ => Continuous.add ?_ ?_
  · have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
        fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
      funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]; exact (continuous_apply j).smul continuous_const
  · have e : (fun b : Fin L.n → AE F E => Matrix.single (L.em j) L.i₀ (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j)))) =
        fun b => (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j))) • Matrix.single (L.em j) L.i₀ (1 : AE F E) := by
      funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact ((continuous_const.mul ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp (continuous_apply j))).neg).smul continuous_const
theorem inFrame_sM'_k (b : Fin L.n → AE F E) : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b) := by
  have hex : ∃ x : d.G, inFrame d.b x = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b) :=
    ⟨⟨kfour.nU d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b), kfour.nU_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d) R.hε (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_cond_k b)⟩, kfour.inFrame_nU _ _⟩
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.elt_k
  rw [dite_eq_left hex]
  exact hex.choose_spec
theorem sig_delta_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : σ δ = -(((R.ε : ℤ) : E)) * δ := by
  have hx : inFrame d.b (cM (0, 1)) = kfour.nM (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ 1) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, kfour.nM, Matrix.transpose_one]
  have hc := kfour.cond_of_inFrame R.hε (cM (0, 1)) _ hx
  have e := congrFun (congrFun hc L.i₀) L.i₀
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply_same,
    one_smul, smul_eq_mul] at e
  have hcA : cA σ (inclR (F := F) (AF F) δ) = inclR (F := F) (AF F) (σ δ) := by
    show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] σ δ
    simp
  have e' : inclR (F := F) (AF F) δ = inclR (F := F) (AF F) (-(((R.ε : ℤ) : E) * σ δ)) := by
    rw [e, map_neg, map_mul, map_intCast, hcA]
  have hδ := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) e'
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mulE_k R
  linear_combination (((R.ε : ℤ) : E)) * hδ - σ δ * e2
theorem eig_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (y : AE F E) (hy : cA σ y = -(((R.ε : ℤ) : AE F E)) * y) :
    ellA δ y • inclR (F := F) (AF F) δ = y := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hδ0 := h.δ0
  have hδ : σ δ = -(((R.ε : ℤ) : E)) * δ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sig_delta_k h
  have hℓ := ellSpec (F := F) hδ0
  set ℓ := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hline : ∀ e : E, σ e = -(((R.ε : ℤ) : E)) * e → ℓ e • δ = e := by
    intro e he
    obtain ⟨c, rfl⟩ := eigLine hcm R.ε hδ0 hδ he
    rw [map_smul, hℓ, smul_eq_mul, mul_one]
  have hε2 : ((R.ε : ℤ) : E) * ((R.ε : ℤ) : E) = 1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mulE_k R
  have hψ : ∀ z : AE F E, ellA δ (z - ((R.ε : ℤ) : AE F E) * cA σ z) • inclR (F := F) (AF F) δ =
      z - ((R.ε : ℤ) : AE F E) * cA σ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by
        simp [cA, Algebra.TensorProduct.map_tmul]
      have hm : ((R.ε : ℤ) : AE F E) * (a ⊗ₜ[F] σ e) = a ⊗ₜ[F] (((R.ε : ℤ) : E) * σ e) := by
        rw [← zsmul_eq_mul, ← zsmul_eq_mul, TensorProduct.tmul_smul]
      rw [hc, hm, ← TensorProduct.tmul_sub]
      have he' : σ (e - ((R.ε : ℤ) : E) * σ e) = -(((R.ε : ℤ) : E)) * (e - ((R.ε : ℤ) : E) * σ e) := by
        rw [map_sub, map_mul, map_intCast, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d]
        linear_combination (-(σ e)) * hε2
      have hl := hline _ he'
      simp only [ellA, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply,
        Algebra.TensorProduct.rid_tmul, inclR, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [show (Algebra.TensorProduct.includeRight.toRingHom δ : AE F E) = (1 : AF F) ⊗ₜ[F] δ from rfl,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
      exact congrArg (a ⊗ₜ[F] ·) hl
    | add x z hx hz =>
      rw [map_add (f := _), mul_add, add_sub_add_comm, map_add (f := _), add_smul, hx, hz]
  have key := hψ y
  rw [hy, neg_mul, mul_neg, ← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R, one_mul, sub_neg_eq_add, map_add (f := _), add_smul] at key
  have h2 : (2 : F) • (ellA δ y • inclR (F := F) (AF F) δ) = (2 : F) • y := by
    rw [two_smul, two_smul]; exact key
  exact smul_right_injective (AE F E) (two_ne_zero) h2
theorem ellA_inclR_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (e : E) : ellA δ (inclR (F := F) (AF F) e) ∈ (algebraMap F (AF F)).range := by
  refine ⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩
  simp [ellA, inclR, LinearMap.baseChange_tmul, Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one]
theorem continuous_sM'_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d
  have hb := d.ok.frame
  have hnb := kfour.isNMap_nbE hσ hb
  have hmem : ∀ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b ∈ nA σ d.Y d.b := fun b => (kfour.mem_nA_iff hσ R.hε _).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_cond_k b)
  have e : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L = fun b => kfour.nbE σ d.Y d.b ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b, hmem b⟩ := by
    funext b
    apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, hnb]
    rfl
  rw [e]
  exact (kfour.nb_continuous hσ hb hnb).comp (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_sB_k.subtype_mk _)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.CompanionTheory.SiegelEisHalf
theorem eisHalf_k : _root_.SiegelEisensteinSeries.EisHalf_k := by
  intro F E _ _ _ _ _ σ B n Y r' s' hB hn hY χ _ c _ b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t, hsum, hhol⟩ := _root_.GlobalTheory.T.eisenstein_series_absolute_convergence F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, hmod⟩ := _root_.GlobalTheory.T.eisenstein_series_left_invariance F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t' := ⟨max t t₀, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x) :=
    fun s hs => hsum s (lt_of_le_of_lt ht hs)
  obtain ⟨hmem, hcont, hbd⟩ := hmod t' Ê ht₀ hsum'
  classical
  let v : ℂ → modFun σ Y := fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0
  have hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x := by
    intro s h x
    simp only [v, dif_pos h]
  refine ⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩
  have hS : IsOpen {s : ℂ | t' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_
  · intro x
    exact ((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x
  · refine hcont.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hv s hs x
  · intro Q hQ hQc
    rcases Q.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    obtain ⟨z₁, hz₁, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨C, N, h⟩ := hbd z₁.re z₂.re (hQ hz₁)
    refine ⟨C, N, fun s hs x => ?_⟩
    rw [hv s (hQ hs) x]
    exact h s (hmin hs) (hmax hs) x
end GlobalTheory.CompanionTheory.SiegelEisHalf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFiniteUnramifiedOutsideOfIsHecke
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
theorem UpperTheory.exists_finite_unramified_outside_of_isHecke :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}, _root_.UpperTheory.TP.W.GoodK σ B → ∀ {χ : Chr F E}, IsHecke F E χ → ∃ S : Finset (Pl F), UnrOff χ (S : Set (Pl F)) := by
  intro F E _ _ _ _ _ σ B hB χ hχ
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ UnrAt χ w}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.PairVac.eventually_unrAt_of_isHecke σ hB.cm χ hχ)
  refine ⟨(hfin.image fun w => w.under (𝓞 F)).toFinset, fun w hw => ?_⟩
  by_contra hu
  exact hw (by
    show w.under (𝓞 F) ∈ (((hfin.image fun w => w.under (𝓞 F)).toFinset : Finset (Pl F)) : Set (Pl F))
    rw [Set.Finite.coe_toFinset]
    exact ⟨w, hu, rfl⟩)
end
end

