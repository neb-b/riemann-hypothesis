module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerSurj

open GlobalTheory.MixModel (rat sandwich HypDec)
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition (isoPart midPart res IsIsoSplit)

variable {D : D7}

section Emb

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

def embMat : Matrix (Fin V.rank) (Fin H.rank) D.host.E := d.e * dH.qX + d.e' * dH.qY

theorem ee_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e) = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.ee

theorem e'e'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e') = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e'

theorem e'e_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e) = 1 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e

theorem ee'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e') = 1 := by
  have h := congrArg Matrix.conjTranspose d.e'e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one] at h
  exact h

theorem ei₀_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.i₀) = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_zero] at h
  exact h

theorem embMat_e : embMat d dH * dH.e = d.e := by
  have h1 := e'e_assoc dH
  have h0 := ee_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem embMat_e' : embMat d dH * dH.e' = d.e' := by
  have h1 := ee'_assoc dH
  have h0 := e'e'_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem iso_embMat : d.eᴴ * V.gram * embMat d dH = dH.eᴴ * H.gram := by
  have h1 : d.eᴴ * V.gram * d.e' = 1 := by
    rw [Matrix.mul_assoc]
    exact ee'_assoc d
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.ee, h1, Matrix.zero_mul, Matrix.one_mul,
    zero_add]
  rfl

theorem mid_embMat : d.i₀ᴴ * V.gram * embMat d dH = 0 := by
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.i₀e, d.i₀e', Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

end Emb

section Form

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r) (W : HSp D)

theorem hO_rank_zero (hZ : Z.rank = 0) (x y : WO Z W) : hO Z W x y = 0 := by
  haveI : IsEmpty (Fin Z.rank) := by
    rw [hZ]
    infer_instance
  rw [GlobalTheory.MixModel.hO_eq_trace]
  simp [Matrix.trace]

theorem mul_embMat_jX (x : WO V W) : x * rat (embMat d dH) * dH.jX = x * d.jX := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e = rat d.e
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e]

theorem mul_embMat_jY (x : WO V W) : x * rat (embMat d dH) * dH.jY = x * d.jY := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e' = rat d.e'
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e']

theorem hO_split (hZ : Z.rank = 0) (x y : WO V W) :
    hO V W x y = hO V' W (x * rat d.i₀) (y * rat d.i₀) + hO H W (x * rat (embMat d dH)) (y * rat (embMat d dH)) := by
  rw [GlobalTheory.MixModel.HypDec.hO_coordS d, GlobalTheory.MixModel.HypDec.hO_coordS dH, hO_rank_zero W hZ,
    mul_embMat_jX d dH W x, mul_embMat_jX d dH W y, mul_embMat_jY d dH W x, mul_embMat_jY d dH W y]
  show _ = hO V' W (x * d.j0) (y * d.j0) + _
  abel

theorem symplOH_split (hZ : Z.rank = 0) (x y : WO V W) :
    symplOH V W x y =
      symplOH V' W (sandwich (rat 1) (rat d.i₀) x) (sandwich (rat 1) (rat d.i₀) y) +
        symplOH H W (sandwich (rat 1) (rat (embMat d dH)) x) (sandwich (rat 1) (rat (embMat d dH)) y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [hO_split d dH W hZ, map_add (f := _)]

end Form

section Res

variable {V V' H Z W : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

theorem sand_B (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat d.i₀) (isoPart V W d.e y + midPart V V' W d.i₀ x) = x := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat d.i₀ = 0 := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat d.i₀ = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, ei₀_assoc d, GlobalTheory.MixModel.rat_zero]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat d.i₀ = 1 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat d.i₀ = 1
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.iso,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V'), GlobalTheory.MixModel.rat_one]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, Matrix.mul_one, zero_add]

theorem sand_A (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat (embMat d dH)) (isoPart V W d.e y + midPart V V' W d.i₀ x) = isoPart H W dH.e y := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat (embMat d dH) =
      (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram).map (incA D) := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat (embMat d dH) = rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram)
    rw [← GlobalTheory.MixModel.rat_mul, hadj, hadj, iso_embMat]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat (embMat d dH) = 0 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat (embMat d dH) = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, mid_embMat,
      Matrix.mul_zero, GlobalTheory.MixModel.rat_zero]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero]

theorem surj_core (hZ : Z.rank = 0) (hsH : IsIsoSplit H Z dH.e dH.i₀) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) (f' : WO V' W → ℂ) (hf' : IsThetaFunO ψ V' W f') :
    ∃ f, IsThetaFunO ψ V W f ∧ f' = res V V' W d.e d.i₀ μ 𝓨 f := by
  obtain ⟨fH, hfH, hne⟩ := (GlobalTheory.TowerRestrict.res_theta D H Z W r dH.e dH.i₀ hsH ψ hψ μ 𝓨 hμ).2
  generalize hcv : res H Z W dH.e dH.i₀ μ 𝓨 fH 0 = c
  have hc : c ≠ 0 := by
    rintro rfl
    apply hne
    funext z
    have hz : z = 0 := by
      haveI : IsEmpty (Fin Z.rank) := by
        rw [hZ]
        infer_instance
      exact Matrix.ext fun _ j => isEmptyElim j
    subst hz
    exact hcv
  have hint : ∫ y in 𝓨, fH (isoPart H W dH.e y) ∂μ = c := by
    rw [← hcv]
    simp only [res, GlobalTheory.TowerRestrict.midPart_zero, add_zero]
  refine ⟨fun w => f' (sandwich (rat 1) (rat d.i₀) w) * (c⁻¹ • fH) (sandwich (rat 1) (rat (embMat d dH)) w), ?_, ?_⟩
  · exact GlobalTheory.MixModel.isThetaFunO_prod 1 d.i₀ 1 (embMat d dH) (symplOH_split d dH W hZ) hf'
      (GlobalTheory.OrientedHeis.theta_smul c⁻¹ hfH)
  · funext x
    simp only [res, sand_B, sand_A, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hint, inv_mul_cancel₀ hc, mul_one]

private theorem isIsoSplit_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm.trans (Nat.add_comm _ _ ▸ rfl)⟩
  · apply Fintype.linearIndependent_iff.2
    intro g hg
    have h1 : d.e.mulVec g = 0 := by
      funext k
      have hk := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, smul_eq_mul, Pi.zero_apply] at hk
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hk]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (d.e'ᴴ * S.gram * d.e).mulVec g = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rw [d.e'e, Matrix.one_mulVec] at h2
    exact fun i => congrFun h2 i
  · rw [GlobalTheory.MixModel.cT_sig]
    exact d.ee
  · rw [hadj]
    exact d.iso
  · rw [hadj, Matrix.mul_assoc]
    exact ei₀_assoc d

end Res

theorem res_surjective : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f', IsThetaFunO ψ V' W f' → ∃ f, IsThetaFunO ψ V W f ∧ f' = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ f' hf'
  obtain ⟨d, hdC, hdB, -⟩ := _root_.GlobalTheory.WittSect.exists_hypDec_mem_NI D V V' r C B hs
  subst hdC hdB
  exact surj_core d (GlobalTheory.Core.Rk.SWLaw.dblDec (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral r)) rfl
    (isIsoSplit_of_hypDec _ hs.frame.1) ψ hψ μ 𝓨 hμ f' hf'

end GlobalTheory.TowerSurj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree.KapOnto

variable {D : D7}

theorem inv_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom x.1 ∈
      HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have hx : (x.1.1 : Matrix (Fin d) (Fin d) (AE D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J *
      (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  show (((x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram *
    (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize (x.1.1 : Matrix (Fin d) (Fin d) (AE D)) = Y at hx ⊢
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D (D.host.xi0)⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at hx'
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram)ᵀ := rfl
  rw [e1] at hx'
  have hs := congrArg (fun y => y.submatrix e e) hx'
  simp only [reindex_apply] at hs
  rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at hs
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, ← transpose_submatrix,
    ← Matrix.submatrix_map] at hs
  have ht := congrArg transpose hs
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, ← Matrix.mul_assoc] at ht
  exact ht


set_option maxHeartbeats 1600000 in
theorem kapX_onto : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v), ∃ h' ∈ GfC X, kapX X e hJ h' = h := by
  intro D X d e Wd hJ v h hh
  let h' : GA D X := ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom h.1, inv_mem X e hJ h⟩
  refine ⟨h', ?_, ?_⟩
  · set a : AF D.host.F := 1 - GlobalTheory.EmbChart.atPlace v 1 with ha
    have h0 : GlobalTheory.AdelicU.evFin D.host.F v a = 0 := by
      rw [ha, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h1 : fstA D.host.F a = 1 := by
      show (1 : Ainf D.host.F) - (0 : Ainf D.host.F) = 1
      exact sub_zero 1
    let f := Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    have hf1 : f (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, h1]
      rfl
    have hz : ∀ i j, f ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) i j) = 0 := by
      intro i j
      have k := congrFun (congrFun (hh a h0) i) j
      rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] at k
      have k2 := congrArg f k
      rw [map_mul, map_zero, hf1, one_mul] at k2
      exact k2
    rw [GfC, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    show f (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j) =
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) (e i) (e j) + (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e2, map_add (f := _), hz, zero_add]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq (α := AF D.host.F ⊗[D.host.F] D.host.E), map_one,
        Matrix.one_apply_eq (α := Ainf D.host.F ⊗[D.host.F] D.host.E)]
    · rw [Matrix.one_apply_ne (α := AF D.host.F ⊗[D.host.F] D.host.E) (e.injective.ne hij), map_zero,
        Matrix.one_apply_ne (α := Ainf D.host.F ⊗[D.host.F] D.host.E) hij]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    show (h.1.1 : Matrix (Fin d) (Fin d) (AE D)) (e (e.symm i)) (e (e.symm j)) = h.1.1 i j
    simp only [Equiv.apply_symm_apply]

end GlobalTheory.SquareAgree.KapOnto
end
end

