module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisati
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RealParamSize

variable {D : D7} {m n : ℕ}

theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [map_add, map_add]

theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) :
    compAt θ τ (-x) = -compAt θ τ x := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.neg_apply]
  rw [(infPart D).map_neg, (θ τ).map_neg]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) :
    (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

theorem realSize_add_le (θ : InfFam D) (x y : Mx D m n) :
    GlobalTheory.Unf.realSize θ (x + y) ≤ GlobalTheory.Unf.realSize θ x + GlobalTheory.Unf.realSize θ y := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_add, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem realSize_neg (θ : InfFam D) (x : Mx D m n) : GlobalTheory.Unf.realSize θ (-x) = GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_neg, Matrix.neg_apply, norm_neg]

theorem continuous_realVec {θ : InfFam D} (hθ : IsInfFam θ) {k : ℕ} {L : (Fin k → ℝ) →+ Mx D m n}
    (hL : Continuous L) : Continuous (realVec θ L) :=
  continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp ((continuous_apply i).comp hL))

end GlobalTheory.RealParamSize


open GlobalTheory.RealParamSize in
theorem GlobalTheory.Unf.realParam_size_bounds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L → (∃ C : ℝ, ∀ t, GlobalTheory.Unf.realSize θ (L t) ≤ C * ‖t‖) ∧ (Function.Injective L → ∃ C : ℝ, ∀ (x : Mx D m n) t, ‖t‖ ≤ C * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x)) := by
  intro D θ hθ m n k L hL
  have hc := continuous_realVec hθ hL.1
  set A := (realVec θ L).toRealLinearMap hc with hA
  have hAt : ∀ t, A t = realVec θ L t := fun t => rfl
  have hvec : ∀ t, realVec θ L t = (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    fun t => rfl
  refine ⟨⟨(Fintype.card D.what₂.Tau * (m * n) : ℝ) * ‖A‖, fun t => ?_⟩, fun hinj => ?_⟩
  · refine (realSize_le θ (L t)).trans ?_
    rw [mul_assoc _ ‖A‖, ← hvec, ← hAt]
    exact mul_le_mul_of_nonneg_left (A.le_opNorm t) (by positivity)
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    have hker : (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAt]; exact ht
      have hLt : L t = 0 := by
        ext i j
        refine hσ.ext _ ?_ fun τ => ?_
        · have h := congrFun (congrFun (hL.2 t) i) j
          simpa only [Matrix.map_apply, Matrix.zero_apply] using h
        · have h := congrFun (congrFun (congrFun h0 τ) i) j
          exact h
      exact hinj (hLt.trans L.map_zero.symm)
    obtain ⟨K, -, hK⟩ := (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    refine ⟨K, fun x t => ?_⟩
    have h1 : ‖t‖ ≤ K * ‖A t‖ := by
      have := hK.le_mul_dist t 0
      simpa [dist_eq_norm] using this
    have h2 : ‖A t‖ ≤ GlobalTheory.Unf.realSize θ (L t) := by rw [hAt, hvec]; exact norm_vec_le θ (L t)
    have h3 : GlobalTheory.Unf.realSize θ (L t) ≤ GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x := by
      have := realSize_add_le θ (x + L t) (-x)
      rwa [realSize_neg, add_neg_cancel_comm] at this
    calc ‖t‖ ≤ K * ‖A t‖ := h1
      _ ≤ K * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) K.coe_nonneg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7}

abbrev finf (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finf D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n)
    (y : Mx D n k) (hm : m.map (finf D) = 1) :
    (x * m * y).map (finf D) = (x * y).map (finf D) := by
  have e1 : (x * m * y).map (finf D) = x.map (finf D) * m.map (finf D) * y.map (finf D) := by
    rw [Matrix.map_mul (f := finf D), Matrix.map_mul (f := finf D)]
  have e2 : (x * y).map (finf D) = x.map (finf D) * y.map (finf D) := Matrix.map_mul (f := finf D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one, ← Matrix.map_add _ (map_add (finf D)),
    o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem witt_embedding_mem_finite_unitary_points {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finf D)), Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ hg, ← Matrix.map_add _ (map_add (finf D)), ← Matrix.map_add _ (map_add (finf D)),
    d.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (ha : a ∈ GfC A) : embA d o a ∈ GfC S := by
  rw [embA_apply]
  exact witt_embedding_mem_finite_unitary_points d (orth_emb_mem_GfC o ha)

theorem castGA_fst {I I' : AutInst} (e : I = I') (x : I.GA) : (castGA e x).1 = 1 ↔ x.1 = 1 := by
  subst e
  exact Iff.rfl

theorem iotaX_fst {X : HidaSetting D} (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) {k : GA D (D.sp.Y 0)}
    (hk : k ∈ GfC (D.sp.Y 0)) : (iotaX X h k).1 = 1 := by
  have e := (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)).1 (by simpa using hk)
  exact (castGA_fst h.symm (Formalism.IndefR.RationalEmbedding.iota D k)).2 e

end GlobalTheory.Core.Mi.CenAct

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7} {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem toH_mul (B : SBes X h u ψ A) (a b : GA D A) : B.toH (a * b) = B.toH a * B.toH b := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (iotaX X h (embA B.d B.o (a * b))).1 = (iotaX X h (embA B.d B.o a)).1 * (iotaX X h (embA B.d B.o b)).1
    rw [map_mul, map_mul]
    rfl
  · show (iotaX X h (embA B.d B.o (a * b))).2 = (iotaX X h (embA B.d B.o a)).2 * (iotaX X h (embA B.d B.o b)).2
    rw [map_mul, map_mul]
    rfl

theorem toH_fst (B : SBes X h u ψ A) {a : GA D A} (ha : a ∈ GfC A) : (B.toH a).1 = 1 :=
  Subtype.ext (iotaX_fst h (embA_mem_GfC B.d B.o ha))

theorem toH_surj (B : SBes X h u ψ A) (k : Hfin X u) : ∃ a : GA D A, B.toH a = (1, k) := by
  obtain ⟨a, ha⟩ := (B.tieH ((iotaX X h).symm (1, (k : X.B.I.Gf)))).2 (by
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact ⟨one_mem _, k.2⟩)
  refine ⟨a, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · show (iotaX X h (embA B.d B.o a)).1 = 1
    rw [ha, ContinuousMulEquiv.apply_symm_apply]
  · show (iotaX X h (embA B.d B.o a)).2 = k
    rw [ha, ContinuousMulEquiv.apply_symm_apply]

theorem toH_snd_comm (B : SBes X h u ψ A) {a : GA D A} (hc : a ∈ Subgroup.center (GA D A)) (k : Hfin X u) :
    (B.toH a).2 * k = k * (B.toH a).2 := by
  obtain ⟨a', ha'⟩ := toH_surj B k
  have e : B.toH (a * a') = B.toH (a' * a) := by rw [(Subgroup.mem_center_iff.1 hc a').symm]
  rw [toH_mul, toH_mul, ha'] at e
  exact congrArg Prod.snd e

theorem rtr_mem_Cu (hK : X.LevelSubgroupCharacter) {δ : Hfin X u} (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) :
    Formalism.L2.SG.ColDict.rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ : Hfin X u)) :=
      Prod.ext rfl (hδ κ).symm
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (congrArg (T ξ) e).trans ((h1 ξ).2 _ κ)
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

end GlobalTheory.Core.Mi.CenAct


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.Mi.Shift

variable {D : D7}

theorem inner_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (γ * h) n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨-, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  set δ : GA D B.V := embA B.d B.o γ with hδdef
  have hδ : δ ∈ GQ B.V := by
    have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    rwa [one_mul] at this
  have hmem : ∀ n : flagN B.d, δ⁻¹ * n.1 * δ ∈ flagN B.d := fun n => by
    have := hconj n.1 n.2 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have hmem' : ∀ n : flagN B.d, δ * n.1 * δ⁻¹ ∈ flagN B.d := fun n => hconj n.1 n.2 γ
  let c : flagN B.d ≃ₜ* flagN B.d :=
    { toFun := fun n => ⟨δ⁻¹ * n.1 * δ, hmem n⟩
      invFun := fun n => ⟨δ * n.1 * δ⁻¹, hmem' n⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ B.V B.d.e ↔ n ∈ NFlagQ B.V B.d.e := fun n => by
    change δ⁻¹ * (n : GA D B.V) * δ ∈ GQ B.V ↔ (n : GA D B.V) ∈ GQ B.V
    rw [Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (inv_mem hδ)]
  have hK : ∀ γ' ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ' * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ u1 u2 u3 c hc _ hK)
  congr 1
  funext n
  change _ = besFun ψ 1 B.d B.o B.ζ φ f h ⟨δ⁻¹ * n.1 * δ, hmem n⟩
  simp only [besFun]
  have e1 : psiBes ψ B.d 1 (vecB B.o B.ζ) (δ⁻¹ * n.1 * δ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 := by
    have := hψconj n.1 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have e2 : f (δ⁻¹ * n.1 * δ * embA B.d B.o h) = f (n.1 * embA B.d B.o (γ * h)) := by
    rw [map_mul, ← hδdef, mul_assoc, mul_assoc, hf _ (inv_mem hδ)]
  rw [e1, e2, hφ γ hγ h]

theorem map_mul_right {ρ : ℕ} (B : BesLev D ρ) (a : GA D B.A) : B.vA.μ.map (· * a) = B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  exact Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vA.μ (GQ B.A) hK hcov a

theorem setIntegral_mul_right {ρ : ℕ} (B : BesLev D ρ) (G : GA D B.A → ℂ) (hG : ∀ γ ∈ GQ B.A, ∀ h, G (γ * h) = G h)
    (a : GA D B.A) : ∫ h in B.vA.𝓕, G (h * a) ∂B.vA.μ = ∫ h in B.vA.𝓕, G h ∂B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  have hmp : MeasurePreserving (· * a) B.vA.μ B.vA.μ := ⟨measurable_mul_const a, map_mul_right B a⟩
  have hmp' : MeasurePreserving (· * a⁻¹) B.vA.μ B.vA.μ := ⟨measurable_mul_const a⁻¹, map_mul_right B a⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G B.vA.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ B.A) ((· * a⁻¹) ⁻¹' B.vA.𝓕) B.vA.μ :=
    B.vA.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (B.vA.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

end GlobalTheory.Core.Mi.Shift


open GlobalTheory.Core.Mi.Shift in
theorem GlobalTheory.Core.Mi.per_rTrans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ)
    (f : GA D B.V → ℂ) (a : GA D B.A), IsStdChar D ψ (-1) → IsContAut B.A φ → IsContAut B.V f →
    B.per ψ (rTrans a φ) (rTrans (embA B.d B.o a) f) = B.per ψ φ f := by
  intro D ψ ρ B φ f a hψ hφ hf
  have hshift : ∀ h, ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (rTrans a φ) (rTrans (embA B.d B.o a) f) h n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (h * a) n ∂B.vN.ν := fun h => by
    simp only [besFun, rTrans, map_mul, mul_assoc]
  unfold BesLev.per besPer
  simp_rw [hshift]
  exact setIntegral_mul_right B (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν)
    (fun γ hγ h => inner_left B ψ hψ.1 φ f hφ.1 hf.1 hγ h) a

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedAutomorphicParametersStarStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LFun.StarParam

open GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.FinZeta

theorem isParamVec_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : IsParamVec σ J L h ρ' (f x) B) : IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem param_star (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ f ∈ GlobalTheory.FinZeta.bddAut V, ∀ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFunV V S f B →
    ∀ w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' →
        B w' = (B w).map star) ∧
      (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w) := by
  intro f hf B hB w hw
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hv : w.under (𝓞 D.host.F) ∉ S := hw
  have hd := SelfDual.isSelfDualAt_frameLat D V (w.under (𝓞 D.host.F))
  have hun := (_root_.GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D V).1
  have hloc : GlobalTheory.LGrp.IsUnitarisable ((bddRep V).comp (embV V (w.under (𝓞 D.host.F)))) := by
    obtain ⟨b, b1, b2, b3⟩ := hun
    exact ⟨b, b1, b2, fun g => b3 _⟩
  have hpar : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (h : u.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)),
      IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((bddRep V).comp (embV V (w.under (𝓞 D.host.F))))
        (⟨f, hf⟩ : bddAut V) (B u) :=
    fun u h => isParamVec_of_map (bddAut V).subtype (fun _ _ => rfl) Subtype.val_injective
      (hB _ hv u h)
  refine ⟨fun w' h' hne => ?_, fun hns => ?_⟩
  · have hB' : B w' = (B w).map (·⁻¹) :=
      ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w rfl) (hpar w' h')
    rcases hpar w rfl with ⟨-, e, he, hsat⟩ | ⟨hi, -⟩
    · rw [hB', GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable _ w _ _ _ _ (B w) (hloc.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat]
    · exact absurd (ConjPlace.isSplit_of_ne hne rfl h') (not_isSplit_of_isInertAt hi)
  · rcases hpar w rfl with ⟨hs, -⟩ | ⟨-, c, ϖ, e, α, hUI, he, hsat, hBw⟩
    · exact absurd hs hns
    · rw [hBw]
      have := bcParam_eq_of_satU_eq (α := fun i => star (α i)) hUI
        (_root_.GlobalTheory.LFun.ConjParam.satU_star_eq _ ϖ c _ _ hUI _ _ _ α (hloc.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat)
      conv_rhs => rw [← this]
      simp [GlobalTheory.LGrp.bcParam, star_inv, Function.comp_def]

end GlobalTheory.LFun.StarParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow : ∀ (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ), 0 < c → (∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) → ContMod T e → ContMod T e' := by
  first | exact @GlobalTheory.EisCont.Shift.contMod_shift | exact GlobalTheory.EisCont.Shift.contMod_shift | (intros; apply GlobalTheory.EisCont.Shift.contMod_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotentStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | exact GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC <;> assumption)
end

