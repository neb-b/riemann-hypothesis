module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} {L : LD d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}

def Ap (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose

theorem inFrame_uM (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (Au L u) 0 0 (Ap hU u) := (hU.1 u).choose_spec

theorem uM_add (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine blk_unique d (A₂ := Ap hU u * Ap hU v) (inFrame_uM hU (u + v)) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_uM hU, inFrame_uM hU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Au_mul]

theorem uM_zero (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine blk_unique d (A₂ := 1) (inFrame_uM hU 0) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Au_zero, Matrix.fromBlocks_one]

theorem uM_neg (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← uM_add hU, neg_add_cancel, uM_zero hU])

theorem Ap_neg_mul (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Ap hU (-u) * Ap hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← uM_add hU, neg_add_cancel, uM_zero hU])
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_uM hU, inFrame_uM hU, Matrix.fromBlocks_multiply,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2

theorem frame_conj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = Matrix.fromBlocks 1 (Au L (-u) * β.1 * Ap hU u) 0 1 := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← uM_neg hU, inFrame_uM hU, inFrame_uM hU, hN β,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Au_mul, neg_add_cancel, Au_zero,
    Ap_neg_mul hU]

theorem cj_mem (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Au L (-u) * β.1 * Ap hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, frame_conj hU hN u β⟩

def cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, cj_mem hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])

theorem cj_val (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (cj hU hN u β).1 = Au L (-u) * β.1 * Ap hU u := rfl

theorem nb_cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (cj hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [frame_conj hU hN, hN]
  rfl

theorem cj_inv (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    cj hU hN (-u) (cj hU hN u β) = β := by
  apply Subtype.ext
  have h1 : Au L u * Au L (-u) = 1 := by rw [Au_mul, add_neg_cancel, Au_zero]
  have h2 : Ap hU u * Ap hU (-u) = 1 := by simpa using Ap_neg_mul hU (-u)
  rw [cj_val, cj_val, neg_neg]
  calc Au L u * (Au L (-u) * β.1 * Ap hU u) * Ap hU (-u)
      = (Au L u * Au L (-u)) * β.1 * (Ap hU u * Ap hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem continuous_cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (cj hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

def cjE (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := cj hU hN u
  invFun := cj hU hN (-u)
  left_inv β := cj_inv hU hN u β
  right_inv β := by simpa using cj_inv hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := continuous_cj hU hN u
  continuous_invFun := continuous_cj hU hN (-u)

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ParabolicUnipotents
section
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

open ComplexParameterFamilyContinuity

theorem cptDom : CptDom := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩
  · have hσ := kfour.sigma_sigma_of_good d.ok.good
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

theorem absConv : AbsConv := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨hTG, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨hnb, hlam, hfd, h1⟩ := h𝓖
  obtain ⟨hfr, hν, hfdU, hU1⟩ := h𝓤
  have cu : Continuous uM := continuous_uM L ⟨hfr, hν, hfdU, hU1⟩
  have cn : Continuous nb := kunf.continuous_nb hnb
  have cφ : Continuous (phz d f s₁ z) := continuous_phz d hf.cont s₁ z
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
  have hbd : ∀ q : Cs d, ∀ᵐ p ∂μ, ‖kq L f s₁ z nb T uM (rep q) x p‖ ≤ |u q| * |Mψ| := by
    intro q
    filter_upwards [hS] with p hp
    simp only [kq, norm_mul]
    refine mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hcq : ∀ q : Cs d, Continuous (kq L f s₁ z nb T uM (rep q) x) := fun q =>
    (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)
  have hint : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) μ := fun q =>
    Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))
  calc ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂μ ≤ ∫ _p, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]

end PositivityTheory.SiegelWeilFormula.Act

end
end

