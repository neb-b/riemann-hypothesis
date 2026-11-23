module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebr
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AdelicModels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (HA HR HFinIn AF Ainf IsCMExt IsHermND)
open Formalism.MainNotions.StandardLattice (finMat infMat IsInfEmb)
open GlobalTheory.Mem.Vol.Scale
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_real_equiv (I : AutInst) (hcm : IsCMExt I.F I.E I.cm.sig)
    (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)) (hθ : ∀ v, IsInfEmb (I.φ v) (θ v)) :
    ∃ e : HA (Ainf I.F) I.cm.sig I.J ≃ₜ* I.Ginf, ∀ h v, uMat (e h v) =
      (I.P v)⁻¹ * ((HA.mat (Ainf I.F) I.cm.sig I.J h : GL (Fin I.n) (Ainf I.F ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Ainf I.F ⊗[I.F] I.E)).map (θ v) * I.P v := by
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv I.F I.E I.cm.sig _ I.φ θ hcm
    (GlobalTheory.GaussDecay.isCMFam_of_over _ hcm I.φ I.φ_over) hθ
  choose p q s hsort using fun v => exists_sorts (I.ε v)
  have hd : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : ∀ v, (I.P v)⁻¹ * I.P v = 1 := fun v => Matrix.nonsing_inv_mul _ (hd v)
  have h2 : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hd v)
  have hJ : ∀ v, Formalism.UG.Jpq (p v) (q v) = (Formalism.REAL.Jm (I.ε v)).submatrix (s v) (s v) := fun v => by
    rw [← (hsort v).reindex_Jpq]
    ext a b
    simp
  obtain ⟨f, hf⟩ := GlobalTheory.Mem.InfGroup.exists_equiv he hc hc' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf I.F) I.cm.sig)
    (fun x i => by rw [← he, ← he, hs]) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J) p q
    (fun v => (I.P v)⁻¹.submatrix (s v) (Equiv.refl _)) (fun v => (I.P v).submatrix (Equiv.refl _) (s v))
    (fun v => by rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv])
    (fun v => by rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_one_equiv])
    (fun v => by
      have h3 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J).map (θ v) = I.J.map (I.φ v) := by
        ext a b
        exact (hθ v).1 (I.J a b)
      rw [h3, hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        ← I.P_spec v]
      change (I.P v)⁻¹ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ = _
      calc _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp)
  let g : (∀ v, Formalism.BasicNotions.UpqT (p v) (q v)) ≃ₜ* I.Ginf :=
    { toFun := fun x v => (hsort v).equiv (x v)
      invFun := fun y v => (hsort v).equiv.symm (y v)
      left_inv := fun x => funext fun v => (hsort v).equiv.symm_apply_apply _
      right_inv := fun x => funext fun v => (hsort v).equiv.apply_symm_apply _
      map_mul' := fun x y => funext fun v => map_mul (hsort v).equiv _ _
      continuous_toFun := continuous_pi fun v => (hsort v).equiv.continuous.comp (continuous_apply v)
      continuous_invFun := continuous_pi fun v => (hsort v).equiv.symm.continuous.comp (continuous_apply v) }
  refine ⟨f.trans g, fun h v => ?_⟩
  have h4 := hf h v
  change Matrix.reindex (s v) (s v) (Formalism.BasicNotions.UpqT.mat (f h v)) = (I.P v)⁻¹ * (h.1.1).map (θ v) * I.P v
  generalize Formalism.BasicNotions.UpqT.mat (f h v) = X at h4 ⊢
  generalize (h.1.1).map (θ v) = Y at h4 ⊢
  have h5 : Matrix.reindex (s v) (s v) X * (I.P v)⁻¹ = (I.P v)⁻¹ * Y := by
    ext a b
    have := congrFun (congrFun h4 ((s v).symm a)) b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.coe_refl, id] at this
    rw [Matrix.mul_apply, Matrix.mul_apply, ← this, ← (s v).sum_comp]
    simp
  rw [← h5, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bc_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {γ : GL (Fin M) E}
    (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  have h2 := congrArg (fun X => Matrix.map X (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) h
  simp only [Matrix.map_mul] at h2
  change Formalism.UG.cT _ (γ.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) * J.map _ * γ.1.map _ = J.map _
  rw [← h2]
  congr 2

theorem exists_adelic_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  intro I
  have hcm : IsCMExt I.F I.E I.cm.sig := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨hcm, ⟨fun i j => congrFun (congrFun I.J_herm i) j, I.J_det⟩, ?_⟩
  have hex := GlobalTheory.Mem.VolEmb.existsUnique_infEmb I.F I.E I.cm.sig hcm
  choose θ hθ hθu using fun v => hex (I.φ v)
  obtain ⟨er, her⟩ := exists_real_equiv I hcm θ hθ
  obtain ⟨ef, hef, -⟩ := _root_.GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic I
  obtain ⟨sp, hsp⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split I.F I.E I.cm.sig I.n I.J
  let g : HA (Ainf I.F) I.cm.sig I.J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.cm.sig I.J ≃ₜ* I.GA :=
    { toFun := fun x => (er x.1, ef.symm x.2)
      invFun := fun y => (er.symm y.1, ef y.2)
      left_inv := fun x => Prod.ext (er.symm_apply_apply _) (ef.apply_symm_apply _)
      right_inv := fun x => Prod.ext (er.apply_symm_apply _) (ef.symm_apply_apply _)
      map_mul' := fun x y => Prod.ext (map_mul er _ _) (map_mul ef.symm _ _)
      continuous_toFun := (er.continuous.comp continuous_fst).prodMk (ef.symm.continuous.comp continuous_snd)
      continuous_invFun := (er.symm.continuous.comp continuous_fst).prodMk (ef.continuous.comp continuous_snd) }
  have hfin : ∀ h, I.fmat ((sp.trans g) h).2 =
      (finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
    intro h
    have h1 := hef (ef.symm (sp h).2)
    rw [ef.apply_symm_apply, (hsp h).1] at h1
    rw [h1]
    change I.fmat (ef.symm (sp h).2) = _
    ext a b
    exact ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply _).symm
  have hinf : ∀ v h, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * infMat I.cm.sig I.J (θ v) h * I.P v := by
    intro v h
    have h1 := her (sp h).1 v
    rw [(hsp h).2] at h1
    exact h1
  have hrat : ∀ (γ : GL (Fin I.n) I.E) (h : HA (AF I.F) I.cm.sig I.J),
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (AF I.F)) γ = HA.mat _ _ _ h →
      (∀ v, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat ((sp.trans g) h).2 =
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    intro γ h hh
    refine ⟨fun v => ?_, ?_⟩
    · rw [hinf]
      congr 2
      unfold infMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, ← (hθ v).1]
      change θ v (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    · rw [hfin]
      unfold finMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      change Algebra.TensorProduct.comm I.F _ _
        (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
  refine ⟨sp.trans g, fun h => ⟨?_, ?_⟩, hfin, fun v θ' hθ' h => ?_⟩
  · rintro ⟨γ, hγ, hh⟩
    exact ⟨γ, hγ, hrat γ h hh⟩
  · rintro ⟨γ, hγ, h1, h2⟩
    let h' : HA (AF I.F) I.cm.sig I.J :=
      (⟨_, bc_mem (AF I.F) I.cm.sig I.J hγ⟩ : HR (AF I.F) I.cm.sig I.J)
    obtain ⟨h3, h4⟩ := hrat γ h' rfl
    have : h = h' := (sp.trans g).injective (Prod.ext
      (funext fun v => Subtype.ext (Units.ext ((h1 v).trans (h3 v).symm)))
      (Subtype.ext (Units.ext (h2.trans h4.symm))))
    rw [this]
    exact ⟨γ, hγ, rfl⟩
  · rw [hθu v θ' hθ']
    exact hinf v h

end GlobalTheory.AdelicModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRowRepresentativesLowestKType
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothRepsType

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

theorem exists_level_bump (B : RowsAut) (hg : 1 ≤ B.g) :
    ∃ χ : B.I.Gf → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) ∧
      ∫ k, χ k ∂B.μf = 1 := by
  obtain ⟨hT, -, -, hKc, -, -, hK⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨ho, ⟨K, hKe⟩, -⟩ := hK B.g hg
  have hcl : IsClosed (B.I.Kg B.g) := by
    rw [← hKe] at ho ⊢
    exact K.isClosed_of_isOpen ho
  have hc : IsCompact (B.I.Kg B.g) := hKc.of_isClosed_subset hcl fun x hx => hx.1
  have hne : (B.I.Kg B.g).Nonempty := by
    rw [← hKe]; exact ⟨1, K.one_mem⟩
  have hpos : 0 < B.μf.real (B.I.Kg B.g) :=
    ENNReal.toReal_pos (ho.measure_pos B.μf hne).ne' hc.measure_lt_top.ne
  refine ⟨(B.I.Kg B.g).indicator fun _ => (((B.μf.real (B.I.Kg B.g))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
  · intro k hk
    exact Set.mem_of_indicator_ne_zero hk
  · rw [integral_indicator_const _ ho.measurableSet, Complex.real_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]

theorem integrable_of_prod (B : RowsAut) (hσ : IsURep B.σs) (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ)
    (h1 : ∫ k, χ k ∂B.μf = 1) (hc : Continuous fun y : B.I.GA => a y.1 * χ y.2)
    (hs : HasCompactSupport fun y : B.I.GA => a y.1 * χ y.2) (w : B.Hs) :
    Integrable (fun g => a g • B.σs g w) (muInf B.I) := by
  obtain ⟨k, hk⟩ : ∃ k, χ k ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at h1
  have hac : Continuous a := by
    have h2 : Continuous fun g : B.I.Ginf => a g * χ k :=
      hc.comp (f := fun g : B.I.Ginf => ((g, k) : B.I.GA)) (Continuous.prodMk_left k)
    have h3 := h2.mul_const (χ k)⁻¹
    simpa [mul_assoc, mul_inv_cancel₀ hk] using h3
  have has : HasCompactSupport a := by
    refine HasCompactSupport.intro (hs.isCompact.image continuous_fst) fun g hg => ?_
    by_contra h0
    exact hg ⟨(g, k), subset_tsupport _ (mul_ne_zero h0 hk), rfl⟩
  have : IsFiniteMeasureOnCompacts (muInf B.I) := by unfold muInf; infer_instance
  exact (hac.smul (hσ.2.2.2 w)).integrable_of_hasCompactSupport has.smul_right

theorem conv_avg (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund)
    (hT : T ∈ B.I.HomS B.σs B.μf B.fund B.R) (hk : ∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u)
    (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ) (hχ : ∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) (h1 : ∫ k, χ k ∂B.μf = 1)
    (w : B.Hs) (hint : Integrable (fun g => a g • B.σs g w) (muInf B.I)) :
    ∫ y, (a y.1 * χ y.2) • B.R y (T w) ∂(B.I.muA B.μf) = T (∫ g, a g • B.σs g w ∂(muInf B.I)) := by
  have : SigmaFinite (muInf B.I) := by unfold muInf; infer_instance
  obtain ⟨-, hmul, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have hpt : ∀ y : B.I.GA, (a y.1 * χ y.2) • B.R y (T w) = χ y.2 • T (a y.1 • B.σs y.1 w) := by
    rintro ⟨g, k⟩
    by_cases h0 : χ k = 0
    · simp [h0]
    · have e1 : B.R (g, k) (T w) = T (B.σs g w) := by
        have : ((g, k) : B.I.GA) = (g, 1) * (1, k) := by simp
        rw [this, hmul, ContinuousLinearMap.mul_apply, hk w k (hχ k h0)]
        exact (congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S w) (hT g)).symm
      simp only [e1, map_smul, smul_smul, mul_comm]
  simp_rw [hpt]
  change ∫ y : B.I.Ginf × B.I.Gf, χ y.2 • T (a y.1 • B.σs y.1 w) ∂((muInf B.I).prod B.μf) = _
  rw [← integral_prod_swap]
  have := integral_prod_smul (μ := B.μf) (ν := muInf B.I) χ (fun g => T (a g • B.σs g w))
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [this, h1, one_smul, T.integral_comp_comm hint]

theorem repsExist : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v))
      (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g →
    ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) →
      ∃ Fr, IsReps B T Fr := by
  intro B d hd h1 hg T hT hk
  classical
  obtain ⟨χ, hχc, hχs, hχK, hχ1⟩ := exists_level_bump B hg
  obtain ⟨huniq, -, htr, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hd).1
  let Fr : B.Hs → B.I.GA → ℂ := fun u => if h : ∃ f, IsContRep B (T u) f then h.choose else 0
  have hFr : ∀ u f, IsContRep B (T u) f → Fr u = f := by
    intro u f hf
    have h : ∃ f, IsContRep B (T u) f := ⟨f, hf⟩
    have : Fr u = h.choose := dif_pos h
    rw [this]
    exact huniq _ _ _ h.choose_spec hf
  refine ⟨Fr, fun P u hu => ?_⟩
  obtain ⟨A, hA, hAs, hfix⟩ := _root_.GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf B d hd h1 P u hu
  let ψ : B.I.GA → ℂ := fun y => A (fun v i j => uMat (y.1 v) i j) * χ y.2
  have hder := fun E => _root_.GlobalTheory.ConvDeriv.convolution_hasDerivAt B A χ ψ E hA hAs hχc hχs (fun _ => rfl)
  have hψ : ∫ y, ψ y • B.R y (T (B.tens B.w)) ∂(B.I.muA B.μf) = T u := by
    rw [hfix]
    exact conv_avg B T hT hk (fun g => A (fun v i j => uMat (g v) i j)) χ hχK hχ1 _
      (integrable_of_prod B hσ (fun g => A (fun v i j => uMat (g v) i j)) χ hχ1 (hder 0).1 (hder 0).2.1 _)
  have hrep := GlobalTheory.ConvContRep.conv_isContRep B ψ (T (B.tens B.w)) (hder 0).1 (hder 0).2.1
  rw [hψ] at hrep
  have hFu := hFr u _ hrep
  have hrep' : IsContRep B (T u) (Fr u) := by rw [hFu]; exact hrep
  refine ⟨hrep', fun k hkK y => ?_, fun E y => ?_⟩
  · have := htr _ _ (1, k) hrep'
    rw [hk u k hkK] at this
    exact congrFun (huniq _ _ _ this hrep') y
  · obtain ⟨-, -, ψ', hc', hs', hd'⟩ := hder E
    obtain ⟨hd1, hd2⟩ := hd' (T (B.tens B.w))
    rw [hψ] at hd1
    obtain ⟨A', -, -, hA'⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B A E (B.tens B.w) hσ hA hAs
    rw [← hfix] at hA'
    have hdiff : HasDerivAt (orbit B E u) (dAct B E u) 0 := hA'.differentiableAt.hasDerivAt
    have hd3 : HasDerivAt (fun t : ℝ => T (orbit B E u t)) (T (dAct B E u)) 0 :=
      (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hdiff
    have hfun : (fun t : ℝ => T (orbit B E u t)) =
        fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (T u) := by
      funext t
      exact congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S u) (hT _)
    rw [hfun] at hd3
    have heq := hd3.unique hd1
    have hrep2 := GlobalTheory.ConvContRep.conv_isContRep B ψ' (T (B.tens B.w)) hc' hs'
    rw [← heq] at hrep2
    rw [hFr _ _ hrep2, hFu]
    exact hd2 y

end GlobalTheory.SmoothRepsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGardingKMap
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.SmoothKType


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem exists_garding_kMap (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKTypeOf ε σ μ S) :
    ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : S →ₗ[ℂ] H), SmoothOnG ε α ∧
      HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
      (∀ (s : S) (u : H), ⟪u, T s⟫_ℂ = ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε)) ∧
      (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ k (T x)) ∧ T ≠ 0 := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha, ha0, ha1, hac, haU, haK⟩ := exists_conjInvariant_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add (f := _), smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨fun y => (a y : ℂ), T, ?_, hsuppC, hT, ?_, ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun y => (a y : ℂ), isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    exact (Complex.ofRealCLM.contDiff.comp ha).contDiffOn
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [h0, LinearMap.zero_apply, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4

theorem exists_isDer_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ μ S → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (S' : Submodule ℂ H), IsDer ε σ V E ∧ IsKTypeOf ε σ μ S' ∧ S' ≤ V := by
  intro n ε μ H _ _ _ σ S hσ hK
  let G : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ G, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ G,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add (f := _)]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := GlobalTheory.DerEx.smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ G, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using GlobalTheory.DerEx.smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using GlobalTheory.DerEx.smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ G) hσ hder hsm
  obtain ⟨α, T, h1, h2, h3, h4, h5⟩ := exists_garding_kMap n ε μ H σ S hσ hK
  haveI := hK.1
  refine ⟨_, E, _, hE, GlobalTheory.Dec.FormF.rangeType n ε μ H σ S H σ (LinearMap.toContinuousLinearMap T) hK h4
    (fun h => h5 (LinearMap.ext fun x => DFunLike.congr_fun h x)), ?_⟩
  rintro _ ⟨s, rfl⟩
  exact Submodule.subset_span ⟨α, s, h1, h2, fun y => (h3 s y).symm⟩

end GlobalTheory.SmoothKType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureFundamentalDomainLtOfDeepPointBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_fundamentalDomain_lt_of_deepPoint_bound : GlobalTheory.FlagMeas.AbsoluteVolume → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → B.I.muA B.μf B.fund < ⊤ ∧ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal * (B.I.muA B.μf B.fund).toReal ≤ Real.exp (-((B.I.n : ℝ) ^ 2 * B.I.f)) := by
  first | exact @GlobalTheory.DeepArith.deep_mul_volume_le | exact GlobalTheory.DeepArith.deep_mul_volume_le | (intros; apply GlobalTheory.DeepArith.deep_mul_volume_le <;> assumption)
end

