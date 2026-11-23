module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnScalarFormNormBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.ColBound

theorem colForm_bound : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK), ∃ C : ℝ, ∀ (ξ : X.Vpi u) (a : GA D A), ‖B.colForm T.1 ξ a‖ ≤ C * ‖ξ‖ := by
  intro D X h u ψ A B hK T
  have hca := (GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T).1
  obtain ⟨K, hKc, hKg⟩ := B.cpt
  have hb : ∀ ξ, ∃ c : ℝ, 0 ≤ c ∧ ∀ a, ‖B.colForm T.1 ξ a‖ ≤ c := by
    intro ξ
    obtain ⟨c, hc⟩ := hKc.exists_bound_of_continuousOn ((hca ξ).2.continuousOn)
    refine ⟨max c 0, le_max_right _ _, fun a => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKg a
    rw [← (hca ξ).1 γ hγ a]
    exact (hc _ hγK).trans (le_max_left _ _)
  let b := Module.finBasis ℂ (X.Vpi u)
  choose c hc0 hc using fun i => hb (b i)
  let L : ∀ i, X.Vpi u →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖L i‖ * c i, fun ξ a => ?_⟩
  have hlin : B.colForm T.1 ξ a = ∑ i, L i ξ * B.colForm T.1 (b i) a := by
    have hξ : ξ = ∑ i, b.repr ξ i • b i := (b.sum_repr ξ).symm
    have e1 : B.colForm T.1 ξ a = (T.1 ξ) (B.toH a) := rfl
    rw [e1]
    conv_lhs => rw [hξ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hlin, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  calc ‖L i ξ‖ * ‖B.colForm T.1 (b i) a‖ ≤ (‖L i‖ * ‖ξ‖) * c i :=
        mul_le_mul ((L i).le_opNorm ξ) (hc i a) (norm_nonneg _) (by positivity)
    _ = ‖L i‖ * c i * ‖ξ‖ := by ring

end GlobalTheory.Core.Mi.ColBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjDoublingIsotropicUnipotentMemSiegel
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem exists_leftInv_of_linInd {K : Type} [Field K] {a b : ℕ} (C : Matrix (Fin a) (Fin b) K)
    (hC : LinearIndependent K C.transpose) : ∃ L : Matrix (Fin b) (Fin a) K, L * C = 1 := by
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 fun x y h => hinj (by simpa [Matrix.toLin'_apply] using h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  calc LinearMap.toMatrix' g * C = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' C) := by
        rw [LinearMap.toMatrix'_toLin']
    _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' C) := (LinearMap.toMatrix'_comp _ _).symm
    _ = 1 := by rw [hg, LinearMap.toMatrix'_id]

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem conj_io_gen_mem (V : HSp D) (γ : GA D (dblSp V)) (hγ : γ ∈ GQ (dblSp V))
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E)
    (hγi : (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 = γi.map (incA D)) (r : ℕ)
    (K : Matrix (Fin V.rank) (Fin r) D.host.E) (hK : diagSnd γi * K = 0)
    (hC : IsIsoFrame V (leviMat finSumFinEquiv γi * K)) (g : GA D V)
    (h1 : HMul.hMul ((Formalism.L2.Theta.matHom V g).1 - 1) ((leviMat finSumFinEquiv γi * K).map (incA D)) = 0)
    (h3 : ∀ x : Fin V.rank → D.host.E,
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (leviMat finSumFinEquiv γi * K) * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, ((Formalism.L2.Theta.matHom V g).1 - 1).mulVec (fun i => incA D (x i)) =
        ((leviMat finSumFinEquiv γi * K).map (incA D)).mulVec a) :
    ∃ h : γ * io V (g, 1) * γ⁻¹ ∈ siegel V, aP V ⟨_, h⟩ = 1 := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJ
  have hinjA : Function.Injective (incA D) := by
    haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
    exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective
  obtain ⟨g0, hg0, -, hinv⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g0⁻¹).1 := Matrix.map_injective hinjA (hγi.symm.trans hinv)
  have hu : Formalism.UG.cT σ γi * GlobalTheory.Doubling.dblGram finSumFinEquiv J * γi = GlobalTheory.Doubling.dblGram finSumFinEquiv J := by
    rw [hγi', hJ, ← gram_hdbl V]; exact (Formalism.UG.UJ _ _).inv_mem hg0
  have hiso := isotropic_diag hu
  set P := leviMat finSumFinEquiv γi with hP
  set Q' := diagSnd γi with hQ'
  set C := P * K with hCdef
  have hCJP : Formalism.UG.cT σ C * J * P = 0 := by
    calc Formalism.UG.cT σ C * J * P = Formalism.UG.cT σ K * (Formalism.UG.cT σ P * J * P) := by
          rw [hCdef, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (Q' * K) * J * Q' := by rw [hiso, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hK]; simp [Formalism.UG.cT]
  have hcol : ∀ i, (Formalism.UG.cT σ C * J).mulVec (fun j => P j i) = 0 := fun i => by
    funext k
    have := congrFun (congrFun hCJP k) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  choose a ha using fun i => h3 _ (hcol i)
  set G := (Formalism.L2.Theta.matHom V g).1 with hG
  set m := G - 1 with hm
  let A : Matrix (Fin r) (Fin V.rank) (AE D) := Matrix.of fun k i => a i k
  have hmP : m * P.map (incA D) = HMul.hMul (C.map (incA D)) A := by
    ext j i
    have := congrFun (ha i) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, A] using this
  have hCm : C.map (incA D) = HMul.hMul (P.map (incA D)) (K.map (incA D)) := Matrix.map_mul
  obtain ⟨L, hL⟩ := exists_leftInv_of_linInd C hC.2.1
  have hAK : A * K.map (incA D) = 0 := by
    have e1 : C.map (incA D) * (A * K.map (incA D)) = 0 := by
      rw [← Matrix.mul_assoc, ← hmP, Matrix.mul_assoc, ← hCm, h1]
    have e2 : L.map (incA D) * C.map (incA D) = 1 := by
      rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
    calc A * K.map (incA D) = L.map (incA D) * C.map (incA D) * (A * K.map (incA D)) := by
          rw [e2, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
  set Γ := (Formalism.L2.Theta.matHom (dblSp V) γ).1 with hΓ
  set Γi := (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 with hΓi
  have hΓΓi : Γ * Γi = 1 := by
    rw [hΓ, hΓi, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hMg : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1 = Γ * blkMat finSumFinEquiv G 1 * Γi := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, matHom_io, val_blkGL, map_one, Units.val_one]
  have hdiag : ∀ x : Fin V.rank → AE D, Γi *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (P.map (incA D) *ᵥ x) (Q'.map (incA D) *ᵥ x) := fun x => by
    rw [hγi, mulVec_pairVec_diag, leviMat_map, diagSnd_map]
  have hact : ∀ x : Fin V.rank → AE D, (Γ * blkMat finSumFinEquiv G 1 * Γi) *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) := fun x => by
    have hy : Γi *ᵥ pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) =
        blkMat finSumFinEquiv G 1 *ᵥ (Γi *ᵥ pairVec finSumFinEquiv x x) := by
      rw [hdiag, hdiag, blkMat_mulVec, one_mulVec]
      congr 1
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← hCm, ← hmP, ← mulVec_mulVec,
          show G = m + 1 from (sub_add_cancel G 1).symm, add_mulVec, one_mulVec, add_comm]
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.map_mul, hK,
          Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_mulVec, add_zero]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hy, mulVec_mulVec, hΓΓi, one_mulVec]
  have hKD : KeepsDiag finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) :=
    keepsDiag_of_mulVec fun w hw => by
      obtain ⟨x, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
      rw [hact]; exact (pairVec_mem_diagSub finSumFinEquiv).2 rfl
  have hmem : γ * io V (g, 1) * γ⁻¹ ∈ siegel V := mem_siegelOf.2 (by
    change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1
    rw [hMg]; exact hKD)
  have hlevi : leviMat finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) = 1 + K.map (incA D) * A := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hKD.mulVec_diag (Pi.single j 1)).symm.trans (hact _)
    funext i
    have := congrFun h (finSumFinEquiv (.inl i))
    rw [pairVec_inl, pairVec_inl] at this
    rw [this, add_mulVec, one_mulVec]
  refine ⟨hmem, Units.ext ?_⟩
  rw [Units.val_one]
  change (leviMat finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1).det = 1
  rw [hMg, hlevi, Matrix.det_one_add_mul_comm, hAK, add_zero, Matrix.det_one]

theorem conj_io_unip_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ n ∈ NI V (leviMat finSumFinEquiv γi * K), ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1 := by
  intro D V γ hγ γi hγi r K hK hC n hn
  let φ : GA D V →* GA D (dblSp V) := (MulAut.conj γ).toMonoidHom.comp ((io V).comp (MonoidHom.inl _ _))
  let H : Subgroup (GA D (dblSp V)) := (aP V).ker.map (siegel V).subtype
  have hle : NI V (leviMat finSumFinEquiv γi * K) ≤ H.comap φ := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    obtain ⟨h1, -, h3⟩ := hg
    obtain ⟨hmem, ha⟩ := conj_io_gen_mem V γ hγ γi hγi r K hK hC g h1 h3
    exact ⟨⟨_, hmem⟩, ha, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hle hn
  refine ⟨p, ?_, hp⟩
  have : (p : GA D (dblSp V)) = γ * io V (n, 1) * γ⁻¹ := hpe
  rw [this, inv_mul_cancel_right]

end GlobalTheory.Core.Rk.Dich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowMultCusp

theorem mem_NI_iff_iota : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range (C : Matrix (Fin (Formalism.IndefR.RationalEmbedding.inst D).n) (Fin r) (Formalism.IndefR.RationalEmbedding.inst D).E).col)) := by
  intro D r C hC g
  let I := Formalism.IndefR.RationalEmbedding.inst D
  let T := (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  obtain ⟨L, R, hL, hR⟩ :=
    GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E) (J := (D.sp.Y 0).gram) I.J_det hC.2.1
  have key : ∀ h : GA D (D.sp.Y 0),
      T h ∈ I.NA (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) ↔
      GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (starRingEnd D.host.E) C * (D.sp.Y 0).gram) L
        ((matHom (D.sp.Y 0) h).1 - 1) := fun h => by
    have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (T h) = h := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply h
    refine GlobalTheory.CuspCompare.mem_NA_iff I (fun v => Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (fun v => Formalism.IndefR.Eqv.isInfFam_thetaC D ((Formalism.L2.Host.tauPl D).symm v)) h (T h) ?_ (fun v => ?_) hL hR
    · have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (T h)).2
      have h2 := hb.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin I) hs)
      unfold Formalism.L2.SG.AdBridge.ofHAFin at h2
      rw [Formalism.L2.SG.EvalTIota.tauF_eq_i] at h2
      exact h2
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hb := Formalism.L2.SG.EvalTIota.infMat_brg_i (T h) ρ
      rw [hs] at hb
      simp only [Equiv.symm_apply_apply]
      exact hb.symm
  have hW : I.IsIsot (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff I _).2 ⟨r, C, hC, rfl⟩
  refine GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (_root_.GlobalTheory.UnipApprox.strong_approximation I _ hW).1 (fun g => ?_) g
  rw [key]
  exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)

theorem isCuspFun_of_isCuspFn_iota : ∀ (D : D7) (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (f : I.GA → ℂ), Continuous f →
    (∀ γ ∈ I.GFset, ∀ y, f (γ * y) = f y) → I.IsCuspFn (I.muA μf) f →
    IsCuspFun (D.sp.Y 0) (fun y => f (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)) y)) := by
  intro D I hI μf _ _ f hf hi hcusp
  subst hI
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range (C : Matrix (Fin (Formalism.IndefR.RationalEmbedding.inst D).n) (Fin r) (Formalism.IndefR.RationalEmbedding.inst D).E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (fun g => Formalism.IndefR.RationalEmbedding.iota_rat D g) _ hW (mem_NI_iff_iota D C hC) f hf hi).2
    (fun ν hν => hcusp _ hW ν hν)
  exact key μ 𝓕 hμ h𝓕 g

theorem isCuspFn_of_contRep {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {F : L2X X} {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X F ψ) (hF : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) (X.B.I.ext F)) :
    X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ := by
  obtain ⟨hc, hi, he⟩ := hψ
  have hfund := X.B.fund_spec
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨Γ, hΓ, hcΓ, -⟩ := _root_.GlobalTheory.RatDiscrete.rational_points X.B.I
  obtain ⟨hl, -, -, -, hop⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf
  have : BorelSpace X.B.I.GA := inferInstance
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SFinite (X.B.I.muA X.B.μf) := by unfold Formalism.MainNotions.S.AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, X.B.I.rep X.B.fund y = (γ : X.B.I.GA) * y ∧ X.B.I.rep X.B.fund y ∈ X.B.fund := by
    intro y
    have h := hfund.2.1 y
    have e : X.B.I.rep X.B.fund y = h.choose * y := by
      unfold Formalism.MainNotions.S.AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set X.B.I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  have hext : X.B.I.ext F =ᵐ[X.B.I.muA X.B.μf] ψ := by
    filter_upwards [GlobalTheory.RightRegFund.ae_rep hfund.1 hr he] with y hy
    obtain ⟨γ, h1, -⟩ := hr y
    unfold Formalism.MainNotions.S.AutInst.ext
    rw [hy, h1, hi _ (hΓ ▸ γ.2)]
  intro W hW ν hν
  have := hν.1
  filter_upwards [hF W hW ν hν, GlobalTheory.CuspSubspace.constTerm_congr ν hext] with x a b
  rw [← b, a]

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  intro hDSC D X h θ S M J χ t c hS hθ hgap hE hM hrep Φ hΦ hcont u
  obtain ⟨ψ, hψ⟩ := hcont u
  obtain ⟨hd, hl, hH, hb, -⟩ := GlobalTheory.Core.Mi.seeData_of_gap D X hgap
  have hSL : GlobalTheory.DSId.StrictLow := GlobalTheory.ClassificationConsequences.strictLow_of_dsClass
    (GlobalTheory.Published.discreteSeriesClassification_iff.1 hDSC)
  have hL2 := ((GlobalTheory.Dec.CuspAll.cusp_all hSL X.B X.dv _ hd (GlobalTheory.PinScale.one_le_g X) hb hl hH Φ hΦ).2
    (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))).1
  have hψc := isCuspFn_of_contRep X hψ hL2
  have hY := isCuspFun_of_isCuspFn_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hψc
  have e : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (ψ (iotaX X h (y * t⁻¹))) := by
    funext y
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  rw [e]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hz : ∫ n in 𝓕, ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * (g * t⁻¹))) ∂μ = 0 := hY r C hC μ 𝓕 hμ h𝓕 (g * t⁻¹)
  show ∫ n in 𝓕, star (ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * g * t⁻¹))) ∂μ = 0
  simp only [mul_assoc]
  have := congrArg (starRingEnd ℂ) hz
  rw [← integral_conj, map_zero] at this
  exact this

end GlobalTheory.ConjRowMultCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePow
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont.Shift

open Set Metric

theorem holValueAt_of_continuousAt {h : ℂ → ℂ} (a : GlobalTheory.Cont.Continues h) {t : ℂ}
    (b : ContinuousAt (GlobalTheory.Cont.cont h) t) : GlobalTheory.Cont.HolValueAt h t (GlobalTheory.Cont.cont h t) := by
  obtain ⟨H₀, hH⟩ := a
  have ha := hH.isExtAt (mem_univ t)
  exact ha.holValueAt_iff.2 ((b.tendsto.mono_left nhdsWithin_le_nhds).congr' ha.cont_eventuallyEq)

theorem differentiable_npow_sub {c : ℝ≥0} (hc : 0 < c) (s₁ : ℂ) : Differentiable ℂ fun s => npow c (s₁ - s) :=
  (GlobalTheory.Eis.differentiable_npow hc).comp (differentiable_const _ |>.sub differentiable_id)

theorem contMod_shift (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ) (hc : 0 < c)
    (he : ∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) (hm : ContMod T e) : ContMod T e' := by
  have hd := differentiable_npow_sub hc s₁
  have hfun : ∀ g, (fun z => e' z g) = fun z => npow c (s₁ - z) * (fun w => e w (g * x)) (z + s₂) :=
    fun g => funext fun z => he z g
  refine ⟨fun g => ?_, fun s₀ => ?_⟩
  · obtain ⟨H₀, hH⟩ := hm.1 (g * x)
    rw [GlobalTheory.Cont.isMerExt_univ] at hH
    obtain ⟨σ, hσ⟩ := hH.2
    refine ⟨fun z => npow c (s₁ - z) * H₀ (z + s₂), GlobalTheory.Cont.isMerExt_univ.2 ⟨fun z => ?_, σ - s₂.re, fun z hz => ?_⟩⟩
    · exact (hd.analyticAt z).meromorphicAt.fun_mul
        ((hH.1 (z + s₂)).comp_analyticAt (g := (· + s₂)) (by fun_prop))
    · simp only [he]
      congr 1
      exact hσ (by simpa [GlobalTheory.Cont.mem_rightOf] using sub_lt_iff_lt_add.1 hz)
  · obtain ⟨k, r, H, hr, h1, h2, h3, C, N, h4⟩ := hm.2 (s₀ + s₂)
    have hball : ∀ s ∈ ball s₀ r, s + s₂ ∈ ball (s₀ + s₂) r := fun s hs => by
      simpa [mem_ball, dist_eq_norm] using hs

    have hval : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g,
        GlobalTheory.Cont.cont (fun z => e' z g) s = npow c (s₁ - s) * GlobalTheory.Cont.cont (fun z => e z (g * x)) (s + s₂) := by
      intro s hs hne g
      have hne' : s + s₂ ≠ s₀ + s₂ := fun h => hne (add_right_cancel h)
      have hopen : ball (s₀ + s₂) r ∩ {s₀ + s₂}ᶜ ∈ 𝓝 (s + s₂) :=
        (isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hball s hs, hne'⟩
      have hcont : ContinuousAt (GlobalTheory.Cont.cont fun z => e z (g * x)) (s + s₂) := by
        have hq : ContinuousAt (fun t => H t (g * x) / (t - (s₀ + s₂)) ^ k) (s + s₂) :=
          (((h2 (g * x)).continuousOn.continuousAt (isOpen_ball.mem_nhds (hball s hs)))).div
            (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hne'))
        refine hq.congr (Filter.eventually_of_mem hopen fun t ht => ?_)
        have := h1 t ht.1 ht.2 (g * x)
        show H t (g * x) / _ = _
        rw [this, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht.2))]
      have hv := holValueAt_of_continuousAt (hm.1 (g * x)) hcont
      have hn : GlobalTheory.Cont.HolValueAt (fun z => npow c (s₁ - z)) s (npow c (s₁ - s)) :=
        GlobalTheory.Cont.IsHolExt.holValueAt ⟨GlobalTheory.Cont.isRightDomain_univ, fun z _ => hd.analyticAt z, .refl _⟩ (mem_univ s)
      have hp := hn.mul hv.comp_add
      rw [hfun g]
      exact hp.valueAt.cont_eq
    obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hd.continuous.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s₀ (mem_closedBall_self hr.le))
    refine ⟨k, r, fun s g => npow c (s₁ - s) * H (s + s₂) (g * x), hr, fun s hs hne g => ?_, fun g => ?_, ?_,
      B * |C| * GlobalTheory.Grow.height T x ^ N, N, fun s hs g => ?_⟩
    · show npow c (s₁ - s) * H (s + s₂) (g * x) = _
      rw [hval s hs hne g, h1 _ (hball s hs) (fun h => hne (add_right_cancel h)) (g * x)]
      rw [show s + s₂ - (s₀ + s₂) = s - s₀ by ring]
      ring
    · refine (hd.differentiableOn).mul ((h2 (g * x)).comp (by fun_prop) fun s hs => hball s hs)
    · refine (hd.continuous.comp continuous_fst).continuousOn.mul ?_
      exact h3.comp (f := fun p : ℂ × GA D T => (p.1 + s₂, p.2 * x)) (by fun_prop)
        fun (p : ℂ × GA D T) (hp : p ∈ ball s₀ r ×ˢ univ) => ⟨hball p.1 hp.1, mem_univ _⟩
    · have hH := h4 _ (hball s hs) (g * x)
      have hn := hB s (ball_subset_closedBall hs)
      have hg := GlobalTheory.Grow.height_mul_le T g x
      have hg0 := (GlobalTheory.Grow.height_pos T g).le
      have hx0 := (GlobalTheory.Grow.height_pos T x).le
      have hgx0 := (GlobalTheory.Grow.height_pos T (g * x)).le
      have e1 : ‖H (s + s₂) (g * x)‖ ≤ |C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N :=
        hH.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hgx0 N)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgx0 hg N) (abs_nonneg C)))
      rw [norm_mul]
      calc ‖npow c (s₁ - s)‖ * ‖H (s + s₂) (g * x)‖ ≤ B * (|C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N) :=
            mul_le_mul hn e1 (norm_nonneg _) hB0
        _ = B * |C| * GlobalTheory.Grow.height T x ^ N * GlobalTheory.Grow.height T g ^ N := by rw [mul_pow]; ring

end GlobalTheory.EisCont.Shift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.RealHeight

set_option maxHeartbeats 16000000 in
theorem continuous_hgtW (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F)
    (hI : GlobalTheory.Doubling.HasIwasawa D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram
      (GlobalTheory.Doubling.KArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a))) :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) := by
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hK := GlobalTheory.Doubling.isCompact_KArch (Q := (GlobalTheory.Doubling.dblSp V).gram) hc w
    (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a)
  have h1 := hI.continuous_hgtH (GlobalTheory.Doubling.continuous_absEw w) hK
  have h2 := GlobalTheory.Doubling.continuous_ioH (R := w.Completion) (σ := D.sp.cm.sig) (GlobalTheory.Doubling.gram_hdbl V)
  have h3 : Continuous fun g : GlobalTheory.Doubling.Gw V w => ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a) (GlobalTheory.Doubling.ioH w.Completion D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.continuous_coe.comp (h1.comp (h2.comp (continuous_id.prodMk continuous_const)))
  exact h3
theorem hgtW_pos (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F) (g : GlobalTheory.Doubling.Gw V w) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g := by
  have h : 0 < ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a) (GlobalTheory.Doubling.ioH w.Completion D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.coe_pos.2 (GlobalTheory.Doubling.hgtH_pos _)
  exact h

theorem hgtW_cont_pos_le_one : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), GlobalTheory.Doubling.IsMaj V a → ∀ w, Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) ∧ ∀ g, 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ≤ 1 := fun D V a ha w =>
  ⟨continuous_hgtW D V a w (_root_.GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch D V a ha w), fun g => ⟨hgtW_pos D V a w g, _root_.GlobalTheory.Core.Rk.HgtArch.hgtW_le_one D V a ha w g⟩⟩

end GlobalTheory.Corev.RealHeight
end

