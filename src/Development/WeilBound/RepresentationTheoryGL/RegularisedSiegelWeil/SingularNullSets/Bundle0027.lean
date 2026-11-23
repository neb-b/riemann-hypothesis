module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0026
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0718
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixTh
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LFixTh

open Classical in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem fixTh : IdemEx → GenG → GenK → FixTh := by
  intro _ hG hK D ρ p m ψ hψ χ hχ θ _ b₀ hb₀
  obtain ⟨S₁, hS₁⟩ := hK D p
  obtain ⟨S₃, hS₃⟩ := LFixW.psi_kernel hψ
  obtain ⟨S₄, hS₄⟩ := LFixW.ft_supp b₀.1 hb₀ hψ
  have hgood := eventually_goodPl hχ b₀
  refine ⟨S₁ ∪ S₃ ∪ S₄ ∪ (Filter.eventually_cofinite.1 hgood).toFinset, fun S hS e he Ω hΩ hgoodΩ => ?_⟩
  have hSg : ∀ v ∉ S, GoodPl χ b₀ v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)))
  have hSI := hS₃ S (fun v hv => hS (by simp [hv]))
  have hS4 := hS₄ S (fun v hv => hS (by simp [hv])) e he p m.μ
  have : m.μ.IsAddHaarMeasure := m.hμ.1
  let A' : Set (G D p) := {x | Ω x = Ω 1}
  have hA'c : IsClosed A' := by
    have e : A' = ⋂ y, {x | Ω x y = Ω 1 y} := by
      ext x; simp only [A', Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq (hΩ.cont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have hgen : ∀ g ∈ KOff D p S, (IsN g ∨ IsM g ∨ ∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D p S ∧ g = w * u * w⁻¹) →
      ∀ x ∈ A', g * x ∈ A' := by
    intro g hg hgt x hx
    simp only [A', Set.mem_ofPred_eq] at hx ⊢
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | ⟨w, u, hw, ⟨b, hb⟩, hu, rfl⟩
    · funext y
      rw [hΩ.unip g b hb x y, hx]
      by_cases hy : IntOff S y
      · rw [unip_one hSg hSI hg hb hy, one_mul]
      · rw [hgoodΩ y, if_neg hy, mul_zero]
    · have hbl := levi_blocks hg ha
      obtain ⟨h1, h2⟩ := levi_chr hχ hSg a (fun i j w => ((hbl i j).1 w).1) (fun i j v hv => ((hbl i j).2.1 v hv).1)
        (fun i j v hv => (hbl i j).2.2 v hv)
      funext y
      rw [hΩ.levi g a ha x y, hx, h1, h2, levi_good he hg ha _ hgoodΩ y]
      simp [npow]
    · let c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D)))) ((ρ : ℂ) / 2)
      have hΦ : ∀ y, Ω (w⁻¹ * x) y = ∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ := by
        intro y
        have e1 : w⁻¹ * x = w * ((w * w)⁻¹ * x) := by group
        rw [e1, hΩ.weyl w hw]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hΩ.levi _ (-1) (mat_ww hw) x z, hx, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
      have hzero : ∀ y, ψ (halfTr (b * pr b₀ y y).trace) * Ω (w⁻¹ * x) y = Ω (w⁻¹ * x) y := by
        intro y
        by_cases hy : IntOff S y
        · rw [unip_one hSg hSI hu hb hy, one_mul]
        · rw [hΦ y, show (∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ) = 0 from
            hS4 this _ (good_neg hgoodΩ c) y hy, mul_zero]
      funext y
      have e2 : w * u * w⁻¹ * x = w * (u * (w⁻¹ * x)) := by group
      have e3 : Ω 1 y = Ω (w * (w⁻¹ * x)) y := by rw [mul_inv_cancel_left, hx]
      rw [e2, e3, hΩ.weyl w hw, hΩ.weyl w hw]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      rw [hΩ.unip u b hb, hzero z]
  have hK' : (KOff D p S : Set (G D p)) ⊆ A' :=
    hS₁ S (fun v hv => hS (by simp [hv])) A' hA'c rfl hgen
  intro u hu h
  let A : Set (G D p) := {h | Ω (h * u) = Ω h}
  have hAc : IsClosed A := by
    have e : A = ⋂ y, {h | Ω (h * u) y = Ω h y} := by
      ext x; simp only [A, Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq
      (hΩ.cont.comp ((continuous_mul_const u).prodMk continuous_const))
      (hΩ.cont.comp (continuous_id.prodMk continuous_const))
  have h1 : (1 : G D p) ∈ A := by
    show Ω (1 * u) = Ω 1
    rw [one_mul]; exact hK' hu
  have hA := hG D p A hAc h1 fun g hgt x hx => by
    show Ω (g * x * u) = Ω (g * x)
    have hx' : Ω (x * u) = Ω x := hx
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | hw
    · funext y; rw [mul_assoc, hΩ.unip g b hb, hΩ.unip g b hb, hx']
    · funext y; rw [mul_assoc, hΩ.levi g a ha, hΩ.levi g a ha, hx']
    · funext y; rw [mul_assoc, hΩ.weyl g hw, hΩ.weyl g hw, hx']
  have hh : h ∈ A := hA ▸ Set.mem_univ h
  exact hh

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

open PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.ThTot

namespace PositivityTheory.Rg.Rsw.L.LThProd

variable {D : D7}

theorem rowB_eq {m p : ℕ} (y : Mx D (m + 1) p) : rowB (r := m) (s := 1) y = y.submatrix (fun _ => Fin.last m) id := by
  funext a j
  show y (Fin.natAdd m a) j = y (Fin.last m) j
  rw [natAdd_one]

theorem succ (hW : L.WMaj) {p : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    (hθ : IsInfFam θ) : ∀ (k : ℕ) (b₀ : HermE D (k + 1)), IsDiagInv b₀ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ (k + 1) → ∀ (μ : Measure (Mx D (k + 1) p)) (𝓕 : Set (Mx D (k + 1) p)), IsCovolOne (ratMx D (k + 1) p) μ 𝓕 →
    ∀ η : Fin (k + 1) → Mx D 1 p → ℂ, (∀ i, η i ∈ schwartzA θ 1 p) →
    ∃ Ω, IsTh ψ χ θ b₀ μ Ω ∧ ∀ y, Ω 1 y = ∏ i, η i (y.submatrix (fun _ => i) id) := by
  intro k
  induction k with
  | zero =>
    intro b₀ hb χ hχ hr μ 𝓕 hμ η hη
    obtain ⟨Ω, hT, h1⟩ := oneTh hW μ 𝓕 hμ hψ b₀ hb.2 hχ hr hθ (η 0) (hη 0)
    refine ⟨Ω, hT, fun y => ?_⟩
    rw [Fin.prod_univ_one, h1]
    congr 1
    funext a j
    rw [Fin.fin_one_eq_zero a]
    rfl
  | succ k ih =>
    intro b₀ hb χ hχ hr μ 𝓕 hμ η hη
    obtain ⟨ε, hε, hεr⟩ := GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta D 1
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.MixModel.exists_isCovolOne D (k + 1) p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 p
    obtain ⟨Ωr, hTr, hr1⟩ := ih (topH b₀) (topH_diag hb) (χ * ε⁻¹) (hecke_mul_inv hχ hε)
      (resEta_mul_inv hr (by simpa using hεr)) μr 𝓕r hμr (fun i => η (Fin.castSucc i)) fun i => hη _
    obtain ⟨Ωs, hTs, hs1⟩ := oneTh hW μs 𝓕s hμs hψ (botH b₀) (botH_det hb) hε (by simpa using hεr) hθ
      (η (Fin.last (k + 1))) (hη _)
    have hP := GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor D (k + 1) 1 p μr 𝓕r μs 𝓕s
      hμr hμs ψ hψ (χ * ε⁻¹) ε θ hθ (topH b₀) (botH b₀) b₀ (diagonal_hermitian_is_block hb) Ωr Ωs hTr hTs
    rw [inv_mul_cancel_right,
      ← GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas D (k + 1) 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ] at hP
    refine ⟨_, hP, fun y => ?_⟩
    show Ωr 1 (rowT y) * Ωs 1 (rowB y) = _
    rw [hr1, hs1, rowB_eq]
    conv_rhs => rw [Fin.prod_univ_castSucc]
    rfl

end PositivityTheory.Rg.Rsw.L.LThProd

namespace PositivityTheory.Rg.Rsw.L

theorem thProd (hW : WMaj) : ThProd := by
  intro D ρ p m ψ hψ b₀ hb χ hχ hr hρ θ hθ η hη
  obtain ⟨k, rfl⟩ : ∃ k, ρ = k + 1 := ⟨ρ - 1, by omega⟩
  exact LThProd.succ hW hψ hθ k b₀ hb χ hχ hr m.μ m.𝓕 m.hμ η hη

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WMaj
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open GlobalTheory.Core.Rk.SW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L

theorem wMaj : WMaj := by
  intro D n V ψ hψ χ hχ hr θ hθ μ hμ' ω hω Φ
  obtain ⟨𝓕, hμ⟩ := hμ'
  refine ⟨_root_.GlobalTheory.CompanionTheory.ThTot.weilCont D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ, fun C hC => ?_⟩
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    _root_.GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    rwa [κ.apply_symm_apply g] at h
  have hC' : IsCompact (κ.symm '' C) := hC.image (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  obtain ⟨U, hU, hlev⟩ := LWMaj.unifLevel hW hf _ hC'
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.Unf.mixS_support_inBox D ψ₀ hstd (dblSp A) _ V A.rank (GlobalTheory.Core.Rk.SWLaw.dblDec A)
    (GlobalTheory.SchwartzSch.volOf μ 𝓕 hμ) U hU
  have hsupp : ∀ u ∈ {u | ∃ g ∈ C, u = (ω g Φ).1}, ∀ x, u x ≠ 0 → GlobalTheory.Unf.InBox K x := by
    rintro u ⟨g, hg, rfl⟩ x hx
    rw [key] at hx
    exact hbox _ (hlev _ ⟨g, hg, rfl⟩) x 0 hx
  have hdec : ∀ N : ℕ, ∃ B : ℝ, ∀ u ∈ {u | ∃ g ∈ C, u = (ω g Φ).1}, ∀ x,
      ‖u x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ B := by
    intro N
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.Unf.mixS_decay D ψ₀ hstd θ hθ (dblSp A) _ V A.rank (GlobalTheory.Core.Rk.SWLaw.dblDec A)
      (GlobalTheory.SchwartzSch.volOf μ 𝓕 hμ) N
    obtain ⟨B, hB⟩ := LWMaj.unifSob hstd hθ hW hf _ hC' N
    have hne : (C₂ : ℝ≥0∞) * (B : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
    refine ⟨((C₂ : ℝ≥0∞) * (B : ℝ≥0∞)).toReal, ?_⟩
    rintro u ⟨g, hg, rfl⟩ x
    have h := hC₂ (omh (κ.symm g, 1) f) (hW.om_pres _ _ hf) x 0
    change ‖sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) x‖ₑ * _ ≤ _ at h
    have h2 : (C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ₀ θ N (omh (κ.symm g, 1) f) ≤ C₂ * B :=
      mul_le_mul' le_rfl (hB _ ⟨g, hg, rfl⟩)
    rw [key]
    have h3 : ENNReal.ofReal (‖sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N) ≤
        (C₂ : ℝ≥0∞) * B := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      exact h.trans h2
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h3
  obtain ⟨M, hM, hle⟩ := LWMaj.adMaj θ hθ K hK _ hsupp hdec
  exact ⟨M, hM, fun g hg x => hle _ ⟨g, hg, rfl⟩ x⟩

end PositivityTheory.Rg.Rsw.L

end
end

