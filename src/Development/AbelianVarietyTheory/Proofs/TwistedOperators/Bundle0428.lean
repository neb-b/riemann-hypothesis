module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanHeisenbergLineContinuousFiniteZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

noncomputable section

namespace GlobalTheory.ArchLineCont

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)

theorem continuous_ofMixed' (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_realAd' (F : Type) [Field F] [NumberField F] : Continuous (realAd F) :=
  Continuous.prodMk ((continuous_ofMixed' F).comp (continuous_algebraMap ℝ _)) continuous_const


set_option synthInstance.maxHeartbeats 400000 in
theorem archLine_continuous_finPart : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  intro D S X d e g cS hcS u
  have hform : ∀ t, GlobalTheory.VacTransfer.archLine cS u t =
      (HMul.hMul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)ᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun t => by
    rw [GlobalTheory.VacTransfer.archLine_apply, hcS]
  refine ⟨?_, fun t => ?_⟩
  · have hsm : Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u : Matrix (Fin S.rank) (Fin d) (AE D)) :=
      (continuous_realAd' D.host.F).smul continuous_const
    have : (GlobalTheory.VacTransfer.archLine cS u : ℝ → WO S X) = fun t =>
        (HMul.hMul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)ᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) :
          Matrix (Fin X.rank) (Fin S.rank) (AE D)) := funext hform
    rw [this]
    exact (hsm.matrix_transpose.matrix_submatrix e id).matrix_mul continuous_const
  · rw [hform]
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.map_apply, Matrix.zero_apply, Matrix.mul_apply, map_sum (finPart D)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [(finPart D).map_mul, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.ArchLineSum.finPart_smul,
      show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul, zero_mul, zero_mul]

end GlobalTheory.ArchLineCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct

noncomputable section
open Matrix
open Classical

namespace GlobalTheory.FlagRealUnip

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

def single (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) : ℂ →+ AE D :=
  σ.comp (AddMonoidHom.single (fun _ : D.what₂.Tau => ℂ) τ)

theorem single_apply (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (c : ℂ) :
    single σ τ c = σ (Pi.single τ c) := rfl

set_option maxHeartbeats 2000000 in
theorem chart_mul_incA {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (z : D.what₂.Tau → ℂ) (y : D.host.E) :
    σ z * incA D y = σ (fun τ => z τ * tauE D τ y) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, hσ.fin, hσ.fin, zero_mul, sub_zero]
  · have hy : θ τ (infPart D (incA D y)) = tauE D τ y := by
      show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ y)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      exact (hσ.inf τ).1 y
    have e1 := (infPart D).map_sub (σ z * incA D y) (σ fun τ => z τ * tauE D τ y)
    have e2 := (infPart D).map_mul (σ z) (incA D y)
    have e3 := (θ τ).map_sub (infPart D (σ z * incA D y)) (infPart D (σ fun τ => z τ * tauE D τ y))
    have e4 := (θ τ).map_mul (infPart D (σ z)) (infPart D (incA D y))
    rw [e1, e3, e2, e4, hσ.comp, hσ.comp, hy, sub_self]

theorem single_mul_incA {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) (c : ℂ) (y : D.host.E) :
    single σ τ c * incA D y = single σ τ (c * tauE D τ y) := by
  rw [single_apply, single_apply, chart_mul_incA hσ]
  congr 1
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem map_mulVec_single {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) {m k : ℕ} (M : Matrix (Fin m) (Fin k) D.host.E) (c : Fin k → ℂ) :
    (M.map (incA D)) *ᵥ (fun j => single σ τ (c j)) = fun i => single σ τ ((M.map (tauE D τ) *ᵥ c) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, single_mul_incA hσ, mul_comm]

end GlobalTheory.FlagRealUnip

namespace GlobalTheory.FlagRealUnip

variable {D : D7}

theorem subOne_mulVec {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (B : HSp D)
    (τ : D.what₂.Tau) {u : Matrix (Fin B.rank) (Fin B.rank) ℂ} {h : GA D B} (hh : IsAtTau θ B τ u h)
    (x : Fin B.rank → D.host.E) :
    subOne B h *ᵥ ratV x = fun i => single σ τ (((u - 1) *ᵥ fun k => tauE D τ (x k)) i) := by
  funext i
  have hent : ∀ j, subOne B h i j = single σ τ ((u - 1) i j) := fun j => by
    unfold subOne
    rw [Matrix.sub_apply, GlobalTheory.PointAtPlaceHom.entry_eq hσ B τ hh i j, add_sub_cancel_left, Matrix.sub_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, hent, ratV, single_mul_incA hσ, ← map_sum]

theorem conj_gram (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau) :
    (e.map (tauE D τ))ᴴ * gramAt D B τ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).map (tauE D τ) := by
  rw [Matrix.map_mul]
  congr 1
  ext k i
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
  exact (tauE_sig τ (e i k)).symm

end GlobalTheory.FlagRealUnip

namespace GlobalTheory.FlagRealUnip

theorem atTau_mem_NFlag : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  intro D θ hθ B ρ e τ u hu
  obtain ⟨huU, h1, h2⟩ := hu
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ huU
  refine Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := h1 i
    refine ⟨fun k => single σ τ (a k), fun j hj => by show single σ τ (a j) = 0; rw [ha0 j hj, map_zero], ?_⟩
    rw [subOne_mulVec hσ B τ hs, map_mulVec_single hσ]
    funext k
    exact congrArg (fun v => single σ τ (v k)) ha
  · obtain ⟨a, ha⟩ := h2 (fun k => tauE D τ (x k)) (by
      rw [conj_gram]
      funext k
      have := RingHom.map_mulVec (tauE D τ) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram) x k
      rw [hx] at this
      exact this.symm.trans (map_zero _))
    refine ⟨fun k => single σ τ (a k), ?_⟩
    rw [subOne_mulVec hσ B τ hs, map_mulVec_single hσ]
    funext k
    exact congrArg (fun v => single σ τ (v k)) ha

end GlobalTheory.FlagRealUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colFn_cont_left : Big fun ch => ∀ a, Continuous (colFn ch a) ∧
    ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ a
  exact ⟨GlobalTheory.RowBplus.pairVec_cont ch.G ch.W.θ ch.W.θ_is ch.ξ (col_mem ch a),
    fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ch.ξ (col_mem ch a) hγ g⟩

end GlobalTheory.RowClaim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusLaws

private theorem norm_besChar_eq_one {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (d : BesDat A B ι) (n : GA D B) :
    ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, hv⟩ := h.choose_spec
    rw [hv]
    exact hψ _
  · simp

private theorem coCpt_gridData_V_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.Unf.CoCpt (G.V (.top 0)) := by
  have hV := GlobalTheory.FunObj.isV_Xp G
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact (G.V (.top 0)) fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (by
      have h1 := hV.sigOK (tauE D τ)
      rw [hV.sig (tauE D τ)] at h1
      exact h1)
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [← mul_assoc, inv_mul_cancel, one_mul]⟩

private theorem integrableOn_besInt_of_bounded {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (M : Vol G) (hM : M.IsRow) {φ : GA D (G.V (.top 0)) → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hCφ : ∀ g, ‖φ g‖ ≤ Cφ) (hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤)
    {F : GA D (G.V (.grid D.R.m 0)) → ℂ} (hFc : Continuous F) {K : ℝ}
    (hK : ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K) :
    (∀ h, IntegrableOn (besInt W φ F h) M.fdN M.νN) ∧
      IntegrableOn (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
  have hψ : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  obtain ⟨-, -, hBor, -⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA (G.V (.top 0))
  have hemb : Continuous (embTop G) :=
    GlobalTheory.Per.Inhab.emb_continuous (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
      (fun h => (GlobalTheory.FunObj.embRel_iff _ h _).2 rfl)
  have hχ : Continuous fun n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besChar W.ψ G.besTop (n : GA D _) :=
    GlobalTheory.BesselChar.besChar_continuous _ W.ψ_std.1 _
  have hjoint : Continuous fun q : GA D (G.V (.top 0)) × NFlag (G.V (.grid D.R.m 0)) G.besTop.e =>
      besInt W φ F q.1 q.2 := by
    unfold besInt
    refine ((hφc.comp continuous_fst).mul (hFc.comp ?_)).mul ((hχ.comp continuous_snd).star)
    exact (continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)
  have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
    intro h n
    unfold besInt
    rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one hψ, mul_one]
    exact mul_le_mul (hCφ h) (hK h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
  have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
  refine ⟨fun h => Measure.integrableOn_of_bounded hNlt.ne ?_ (ae_of_all _ (hbd h)), ?_⟩
  · exact (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · have hT : GlobalTheory.Unf.EvalCont.Tame fun h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) => besInt W φ F h n :=
      GlobalTheory.Unf.EvalCont.tame_of_bounded hjoint hbd
    have hcont := GlobalTheory.Unf.EvalCont.Tame.continuous_integral M.νN M.fdN hNlt hT
    exact Measure.integrableOn_of_bounded hvol.ne hcont.aestronglyMeasurable
      (ae_of_all _ fun h => norm_setIntegral_le_of_norm_le_const hNlt fun n _ => hbd h n)

theorem bplus_add_bound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  intro D T L sc G W M hM Ω hΩc hΩ φ hφ
  have hcpt := coCpt_gridData_V_zero G
  obtain ⟨haar, fund⟩ := GlobalTheory.FunObj.Vol.IsAt.haar_fund hM.top
  have hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤ := GlobalTheory.Unf.EvalCont.vol_lt_top hcpt ⟨_, _, haar, fund⟩
  have hOrb : ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) →
      ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K := by
    intro F hF K hK h n
    obtain ⟨γ, hγ, hmem⟩ := hΩ h n
    rw [← hF.2 γ hγ]
    exact hK _ hmem
  have hconv : ∀ ψ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)),
      (∀ h, IntegrableOn (besInt W ψ F h) M.fdN M.νN) ∧
        IntegrableOn (fun h => ∫ n in M.fdN, besInt W ψ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
    intro ψ hψ F hF
    obtain ⟨Cψ, hCψ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hψ.2, hψ.1⟩
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hF.1.continuousOn
    exact integrableOn_besInt_of_bounded W M hM hψ.1 hCψ hvol hF.1 (hOrb F hF K hK)
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hφ.2, hφ.1⟩
  refine ⟨Cφ * (M.ν (.top 0)).real (M.fd (.top 0)), ?_, ?_, ?_⟩
  · intro F hF F' hF'
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ hφ F' hF') fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro φ' hφ' F hF
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ' hφ' F hF) fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro F hF K hK
    have hK' := hOrb F hF K hK
    have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
    have hNr : M.νN.real M.fdN = 1 := by simp [Measure.real, hM.unip.2.2]
    have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
      intro h n
      unfold besInt
      rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one W.ψ_std.1.2.1, mul_one]
      exact mul_le_mul (hCφ h) (hK' h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
    unfold Bplus
    calc ‖∫ h in M.fd (.top 0), ∫ n in M.fdN, besInt W φ F h n ∂M.νN ∂M.ν (.top 0)‖
        ≤ (Cφ * K) * (M.ν (.top 0)).real (M.fd (.top 0)) := by
          refine norm_setIntegral_le_of_norm_le_const hvol fun h _ => ?_
          have := norm_setIntegral_le_of_norm_le_const hNlt fun n (_ : n ∈ M.fdN) => hbd h n
          rwa [hNr, mul_one] at this
      _ = Cφ * (M.ν (.top 0)).real (M.fd (.top 0)) * K := by ring

end GlobalTheory.BplusLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusUnip

variable {D : D7}

theorem setIntegral_mul_right {B : HSp D} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e)
    {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)} (hN : GlobalTheory.Per.IsUnitN B e ν 𝓝) (f : NFlag B e → ℂ)
    (hf : ∀ γ ∈ NFlagQ B e, ∀ n, f (γ * n) = f n) (y : NFlag B e) :
    ∫ n in 𝓝, f (n * y) ∂ν = ∫ n in 𝓝, f n ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B he
  obtain ⟨u1, u2, u3⟩ := hN
  haveI : DiscreteTopology (NFlagQ B e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcov' : ∀ x : NFlag B e, ∃ s ∈ NFlagQ B e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : NFlag B e, ν.map (· * a) = ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice ν (NFlagQ B e) hK hcov' a
  have hmp : MeasurePreserving (· * y) ν ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) ν ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) f 𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B e) ((· * y⁻¹) ⁻¹' 𝓝) ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hf γ γ.2 x).symm

theorem bplus_rTr_unip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  intro D T L sc G W M hM φ F hF u hu
  have hn : ∀ n, ‖besChar W.ψ G.besTop n‖ = 1 := fun n => by
    unfold besChar
    split_ifs with h
    · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
      rw [e]
      exact W.ψ_std.1.2.1 _
    · exact norm_one
  have hu1 : besChar W.ψ G.besTop u * star (besChar W.ψ G.besTop u) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have inner : ∀ h, ∫ n in M.fdN, besInt W φ (rTr _ u F) h n ∂M.νN =
      besChar W.ψ G.besTop u * ∫ n in M.fdN, besInt W φ F h n ∂M.νN := fun h => by
    have hs : EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h := (embRel_iff _ h _).2 rfl
    obtain ⟨hy, hyc⟩ := GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop (embTop G h) h hs u hu
    let y : NFlag (G.V (.grid D.R.m 0)) G.besTop.e := ⟨_, hy⟩
    have hinv : ∀ γ ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n,
        besInt W φ F h (γ * n) = besInt W φ F h n := fun γ hγ n => by
      have hγQ : (γ : GA D (G.V (.grid D.R.m 0))) ∈ GQ (G.V (.grid D.R.m 0)) := Subgroup.mem_subgroupOf.1 hγ
      simp only [besInt, Subgroup.coe_mul]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ.2 n.2,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ.2 hγQ, one_mul, mul_assoc (γ : GA D (G.V (.grid D.R.m 0))) (n : GA D (G.V (.grid D.R.m 0))) (embTop G h),
        hF.2 _ hγQ]
    have hpt : ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e, besInt W φ (rTr _ u F) h n =
        besChar W.ψ G.besTop u * besInt W φ F h (n * y) := fun n => by
      simp only [besInt, rTr, Subgroup.coe_mul, y]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ n.2 hy, hyc, star_mul]
      have e1 : (n : GA D (G.V (.grid D.R.m 0))) * (embTop G h * u * (embTop G h)⁻¹) * embTop G h =
          (n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u := by group
      rw [e1]
      linear_combination (-(φ h * F ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u) *
        star (besChar W.ψ G.besTop (n : GA D (G.V (.grid D.R.m 0)))))) * hu1
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_mul_right G.besTop.e_iso hM.unip _ hinv y]
  unfold Bplus
  simp_rw [inner]
  exact integral_const_mul _ _

end GlobalTheory.BplusUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemConjSum

theorem idemSum_add_conj_idem : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z →
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  intro D Z e he
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : e * cA D e = 0 := he.2
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  refine ⟨?_, ?_⟩
  · have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
    calc (e + cA D e) * (e + cA D e) = e * e + e * cA D e + cA D e * e + cA D e * cA D e := by ring
      _ = e + cA D e := by rw [h1, h2, h4, h3]; ring
  · rw [map_add (f := _), cA_cA, add_comm]

end GlobalTheory.IdemConjSum
end

