module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTwAn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptXZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.DefCpt

theorem coCpt_X_zero : ∀ (D : D7), GlobalTheory.Unf.CoCpt (D.sp.X 0) := fun D =>
  GlobalTheory.Unf.Inhab.coCpt_of_isAniso
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite (D.sp.X 0) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _)))

end GlobalTheory.Unf.DefCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionMatrixBoundedRationalAutIntegral
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem isGL_int_of_bdd {X : Fields} {Pr : Primes X} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∉ Pr.vGs)
    (hc : GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ) (j c : ℕ) (a : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k)
    (hg : IsGL ι a g)
    (hb : ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P) :
    IntM (g⁻¹ : GL _ k).val ∧ IntM ((ϖ : k) ^ j • g.val) := by
  obtain ⟨e, -, he⟩ := hg
  have hb' : TwBdd (Pr := Pr) j P a := hb
  have hi : (g⁻¹ : GL _ k).val = GlobalTheory.SymBridge.toLoc ι e e a.symm.toLinearMap := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [he, Model.toLoc_mul, LinearEquiv.comp_symm, Model.toLoc_eq]
    simp
  refine ⟨fun r s => ?_, fun r s => ?_⟩
  · rw [hi]
    show ι (a.symm (Pi.single (e s) 1) (e r)) ∈ 𝒪[k]
    rw [hc.int]
    exact twAn_bdd_inv hP hb' (Pi.single (e s) 1) (fun l => twAn_single_int (e s) l) (e r)
  · rw [he, Matrix.smul_apply, hc.unif]
    show ι ((qOf P : ℕ) : X.E) ^ j • ι (a (Pi.single (e s) 1) (e r)) ∈ 𝒪[k]
    rw [smul_eq_mul, ← map_pow, ← map_mul, hc.int]
    exact twAn_bdd_q hP hb' (Pi.single (e s) 1) (fun l => twAn_single_int (e s) l) (e r)

end GlobalTheory.TwBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowAut

theorem conj_lie {n : ℕ} {P H J E : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hs : Pᴴ * H * P = J)
    (hE : Eᴴ * J + J * E = 0) : (P * E * P⁻¹)ᴴ * H + H * (P * E * P⁻¹) = 0 := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  calc _ = (P⁻¹)ᴴ * Eᴴ * Pᴴ * H * (P * P⁻¹) + ((P⁻¹)ᴴ * Pᴴ) * H * (P * E * P⁻¹) := by
        rw [hPi, hPiH]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = (P⁻¹)ᴴ * (Eᴴ * J + J * E) * P⁻¹ := by
        rw [← hs]; simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hE]; simp

theorem exp_conj {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (E : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • (P * E * P⁻¹)) * P = NormedSpace.exp (t • E) := by
  have h : t • (P * E * P⁻¹) = P * (t • E) * P⁻¹ := by simp
  rw [h, Matrix.exp_conj _ _ hP]
  exact (GlobalTheory.IotaReal.conj_eq_iff _ _ _ hP).2 rfl

theorem iota_data {D : D7} (θ : InfFam D) (hθ : IsInfFam θ)
    (hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)
    (∀ k ∈ GQ (D.sp.Y 0), ι k ∈ I.GFset) ∧ (∀ k ∈ GfC (D.sp.Y 0), (ι k).1 = 1) ∧
    (∀ k ∈ GinfC (D.sp.Y 0), (ι k).2 = 1) ∧
    (∀ v E, Formalism.REAL.inG (I.ε v) E → ∃ τ, ∃ Y ∈ lieAt (D.sp.Y 0) τ, ∀ t : ℝ,
      (ι (oneP θ (D.sp.Y 0) τ Y t)).2 = 1 ∧ uMat ((ι (oneP θ (D.sp.Y 0) τ Y t)).1 v) = NormedSpace.exp (t • E) ∧
        ∀ w, w ≠ v → uMat ((ι (oneP θ (D.sp.Y 0) τ Y t)).1 w) = 1) ∧
    (1 ≤ I.n → ∀ v, ∃ c : ℝ, 0 ≤ c ∧ ∀ g, Real.exp (GlobalTheory.Count.dOp (uMat ((ι g).1 v))) ≤ c * normInf θ (D.sp.Y 0) g) := by
  intro ι
  subst h
  have key : ∀ k, (∀ v, uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k * (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit
  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  have hsnd : ∀ k ∈ GinfC (D.sp.Y 0), (ι k).2 = 1 := by
    intro k hk
    apply Subtype.ext
    apply Units.ext
    refine (key k).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) k).val = 1 := by
      rw [show finHom (D.sp.Y 0) k = 1 from hk]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨fun k hk => (Formalism.IndefR.RationalEmbedding.iota_rat D k).1 hk, fun k hk => ?_, hsnd, fun v E hE => ?_, fun hn v => ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := GlobalTheory.IotaReal.infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · have hY : (Formalism.L2.SG.InstExistsPf.instOf D).P v * E * ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ∈
        lieAt (D.sp.Y 0) ((Formalism.L2.Host.tauPl D).symm v) :=
      conj_lie (hPu v) ((Formalism.L2.SG.InstExistsPf.instOf D).P_spec v) hE
    refine ⟨_, _, hY, fun t => ?_⟩
    have hat := GlobalTheory.IotaReal.isAtTau_atTau θ hθ _ _ (hexp _ _ hY t)
    refine ⟨hsnd _ hat.1, ?_, fun w hw => ?_⟩
    · refine (hinf _ v).trans (Eq.trans ?_ (exp_conj (hPu v) E t))
      exact congrArg (fun M : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M *
        (Formalism.L2.SG.InstExistsPf.instOf D).P v) hat.2.1
    · refine (hinf _ w).trans ?_
      refine (congrArg (fun M : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ => ((Formalism.L2.SG.InstExistsPf.instOf D).P w)⁻¹ * M *
        (Formalism.L2.SG.InstExistsPf.instOf D).P w) (hat.2.2 _ fun e => hw ((Formalism.L2.Host.tauPl D).symm.injective e))).trans ?_
      show ((Formalism.L2.SG.InstExistsPf.instOf D).P w)⁻¹ * (1 : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ) * (Formalism.L2.SG.InstExistsPf.instOf D).P w = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd w)]
  · obtain ⟨c, hc0, hc⟩ := GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹
      ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
    refine ⟨c, hc0, fun g => ?_⟩
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero _ hn (ι g) v
    rw [hinf g v] at h0 ⊢
    exact (hc _ h0).trans (mul_le_mul_of_nonneg_left (GlobalTheory.TauNorm.sum_le_normInf θ g _) hc0)


set_option maxHeartbeats 800000 in
theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsAutFunSm θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  intro hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  have he : GlobalTheory.RepSmooth.IsEquiv θ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    _root_.GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  have hs : GlobalTheory.RepSmooth.IsSob (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    _root_.GlobalTheory.ConjRowCont.conjMap_cont hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  obtain ⟨hrat, hfst, hsnd, hone, hgr⟩ := iota_data θ hθ
    (fun τ Y hY s => GlobalTheory.SmVec.exp_mem_UH (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ)) hY s) X.B.I h
  change ∀ k ∈ _, iotaX X h k ∈ _ at hrat
  change ∀ k ∈ _, (iotaX X h k).1 = 1 at hfst
  change ∀ k ∈ _, (iotaX X h k).2 = 1 at hsnd
  choose f hf using hrep
  have hval : ∀ u y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = star (f u (iotaX X h (y * t⁻¹))) := fun u y => by
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X (hf u)]
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlev : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨A, -, hA⟩ := hΦ
    have hA' : Φ = X.B.Re.comp A := hA.symm
    have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) (1, k)
    have h2 : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)) := by
      rw [hA']
      exact congrArg (fun L : L2X X →L[ℂ] L2X X => L (A (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))))
        (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk)
    rw [h2] at h1
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 (hf u)) y
  have ht : t ∈ GfC (D.sp.Y 0) := hm.1
  have hcomm : ∀ a b : X.B.I.GA, a.1 = 1 → b.2 = 1 → a * b = b * a := fun a b ha hb =>
    Prod.ext (by simp [ha]) (by simp [hb])
  have hcont : ∀ u, Continuous (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := fun u => by
    have : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (f u (iotaX X h (y * t⁻¹))) := funext (hval u)
    rw [this]
    exact ((hf u).1.comp ((iotaX X h).continuous.comp (continuous_mul_const _))).star
  have haut : ∀ u, IsAutFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
    intro u
    refine ⟨fun γ hγ y => ?_, ?_, hcont u⟩
    · rw [hval, hval, mul_assoc, map_mul, (hf u).2.1 _ (hrat γ hγ)]
    · obtain ⟨hKo, ⟨K, hK⟩, -⟩ := (GlobalTheory.CongTop.adelic_topology X.B.I).2.2.2.2.2.2 X.B.g hg
      refine ⟨K.comap ((MonoidHom.snd _ _).comp ((iotaX X h).toMulEquiv.toMonoidHom.comp
        (MulAut.conj t).toMonoidHom)), ?_, fun k hk hkf y => ?_⟩
      · rw [← hK] at hKo
        exact hKo.preimage (f := fun k => (iotaX X h (t * k * t⁻¹)).2)
          (continuous_snd.comp ((iotaX X h).continuous.comp
            ((continuous_mul_const _).comp (continuous_const_mul _))))
      · have hk' : (iotaX X h (t * k * t⁻¹)).2 ∈ X.B.I.Kg X.B.g := by rw [← hK]; exact hk
        have h1 : (iotaX X h (t * k * t⁻¹)).1 = 1 :=
          hfst _ ((GfC _).mul_mem ((GfC _).mul_mem ht hkf) ((GfC _).inv_mem ht))
        have e : y * k * t⁻¹ = y * t⁻¹ * (t * k * t⁻¹) := by group
        have e2 : iotaX X h (t * k * t⁻¹) = (1, (iotaX X h (t * k * t⁻¹)).2) := Prod.ext h1 rfl
        rw [hval, hval, e, map_mul, e2, hlev u _ hk']
  intro u
  refine ⟨haut u, GlobalTheory.RepSmooth.smooth hθ he hs hcont u, GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  have key : ∃ N : ℕ, ∀ v x, ∃ C : ℝ, ∀ a ∈ GinfC (D.sp.Y 0),
      ‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v (x * a)‖ ≤ C * normInf θ (D.sp.Y 0) a ^ N := by
    rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
    · refine ⟨0, fun v x => ⟨‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v x‖, fun a _ => ?_⟩⟩
      have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
      rw [this, mul_one, pow_zero, mul_one]
    have hn' : 1 ≤ X.B.I.n := by rw [← rank_eq X h]; exact hn
    have hti : (iotaX X h t⁻¹).1 = 1 := hfst _ ((GfC _).inv_mem ht)
    obtain ⟨m, hm⟩ := _root_.GlobalTheory.SobolevBound.derivative_closed_class_bound X.B hn' hg
    refine ⟨m, fun v x => ?_⟩
    obtain ⟨C, hC⟩ := hm (Set.range f) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨⟨_, hf u⟩, hlev u, fun w E => ?_⟩
      obtain ⟨τ, Y, hY, hι⟩ := hone w E.1 E.2
      refine ⟨_, ⟨Function.update u τ (GlobalTheory.RepSmooth.der u τ hY), rfl⟩, fun y => ?_⟩
      have h1 := (GlobalTheory.RepSmooth.hasDerivAt_apply he hs τ u hY ((iotaX X h).symm y * t)).star
      simp only [hval, star_star, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply] at h1
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      have e1 : iotaX X h (oneP θ (D.sp.Y 0) τ Y s) =
          GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B w E) s :=
        GlobalTheory.RepSmooth.eq_onePar X.B w E s (hι s).1 (hι s).2.1 (hι s).2.2
      have e2 : iotaX X h ((iotaX X h).symm y * t * oneP θ (D.sp.Y 0) τ Y s * t⁻¹) =
          y * iotaX X h (oneP θ (D.sp.Y 0) τ Y s) := by
        have h3 : (iotaX X h (oneP θ (D.sp.Y 0) τ Y s)).2 = 1 := (hι s).1
        rw [map_mul, map_mul, mul_assoc, ← hcomm _ _ hti h3, ← mul_assoc, ← map_mul, mul_inv_cancel_right,
          ContinuousMulEquiv.apply_symm_apply]
      show f u _ = f u _
      rw [e2, e1]) _ ⟨v, rfl⟩
    choose b hb0 hb using hgr hn'
    have hp := (GlobalTheory.TauLipschitz.tauLip X.B.I hn').1
    have hB : 0 ≤ ∑ w, b w := Finset.sum_nonneg fun w _ => hb0 w
    refine ⟨|C| * ((GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹)))⁻¹ * ∑ w, b w) ^ m, fun a ha => ?_⟩
    have hN : 0 ≤ normInf θ (D.sp.Y 0) a := by unfold normInf; positivity
    have e : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
      rw [map_mul, map_mul, map_mul, mul_assoc, ← hcomm _ _ hti (hsnd a ha), mul_assoc]
    have h2 := GlobalTheory.TauNorm.inv_tau_mul_le X.B.I hn' (iotaX X h (x * t⁻¹)) (iotaX X h a) (hsnd a ha)
      ((∑ w, b w) * normInf θ (D.sp.Y 0) a) fun w => (hb w a).trans
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun w _ => hb0 w) (Finset.mem_univ w)) hN)
    rw [hval, norm_star, e]
    refine (hC _).trans ?_
    have h0 := inv_nonneg.2 (hp (iotaX X h (x * t⁻¹) * iotaX X h a)).le
    rw [mul_assoc, ← mul_pow, mul_assoc]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 h2 m) (pow_nonneg h0 m) (abs_nonneg _)
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun l hl x => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
  rw [hv]
  exact hN v x

end GlobalTheory.ConjRowAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousComplEquivSymm
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

namespace GlobalTheory.Core.Rk.SplitIota

open GlobalTheory.AdelicU.Supp GlobalTheory.LFun.ConjPlace
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem sigR_compFin' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compFin F E v z) = compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem continuous_complEquiv_symm {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    Continuous (complEquiv hE h hτ).symm := by
  let _ : Algebra (Fv F v) (w.adicCompletion E) := (GlobalTheory.LFun.complMap h).toAlgebra
  have : ContinuousSMul (Fv F v) (w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ (GlobalTheory.LFun.SplitChart.continuous_complMap h)
  let _ : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  let f : Fv F v ≃ₐ[Fv F v] w.adicCompletion E :=
    { complEquiv hE h hτ with commutes' := fun a => rfl }
  have : FiniteDimensional (Fv F v) (w.adicCompletion E) := f.toLinearEquiv.finiteDimensional
  have : IsModuleTopology (Fv F v) (w.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  exact IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap

theorem continuous_compW {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) :
    Continuous fun a : AF F ⊗[F] E => GlobalTheory.LFun.toCompl h (compFin F E v a) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) ((GlobalTheory.LFun.toCompl h).comp (compFin F E v)) ?_
  have e : (((GlobalTheory.LFun.toCompl h).comp (compFin F E v)).comp (algebraMap (AF F) (AF F ⊗[F] E)) :
      AF F → w.adicCompletion E) = fun a => GlobalTheory.LFun.complMap h (evFin F v a) := by
    funext a
    exact (GlobalTheory.LFun.toCompl_tmul h (evFin F v a) (1 : E)).trans (by rw [map_one, mul_one])
  rw [e]
  exact (GlobalTheory.LFun.SplitChart.continuous_complMap h).comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)

theorem exists_iota_gen {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    ∃ ι : w.adicCompletion E →+ AF F ⊗[F] E, Continuous ι ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (ι x)) = x) ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι x))) = 0) ∧
      (∀ x, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * ι x = ι x) ∧
      (∀ a x, a * ι x = ι (GlobalTheory.LFun.toCompl h (compFin F E v a) * x)) ∧
      (∀ a, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * a =
        ι (GlobalTheory.LFun.toCompl h (compFin F E v a)) +
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι (GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ a))))) ∧
      ι 1 = singleTens E v (splitIdem hE τ) := by
  set c := complEquiv hE h hτ
  have hcw : ∀ y, GlobalTheory.LFun.toCompl h y = c (splitProj τ y) := fun y => toCompl_eq hE h hτ y
  have hcc : Continuous c.symm := continuous_complEquiv_symm hE h hτ
  let s : w.adicCompletion E →+ Fv F v ⊗[F] E :=
    (splitAlgEquiv hE τ).symm.toRingEquiv.toAddEquiv.toAddMonoidHom.comp
      ((AddMonoidHom.inl _ _).comp c.symm.toAddEquiv.toAddMonoidHom)
  have s1 : ∀ x, splitProj τ (s x) = c.symm x := fun x => splitProj_symm hE τ _
  have s2 : ∀ x, splitProj (τ.comp σ) (s x) = 0 := fun x => splitProj_comp_symm hE τ _
  have hs1 : s 1 = splitIdem hE τ := by
    show (splitAlgEquiv hE τ).symm (c.symm 1, 0) = _
    rw [map_one]; rfl
  have hsc : Continuous s :=
    (continuous_splitAlgEquiv_symm hE τ).comp ((continuous_id.prodMk continuous_const).comp hcc)
  clear_value s
  have hst : Continuous (singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  have hpl : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) = singleTens E v 1 := rfl
  refine ⟨(singleTens E v).toAddMonoidHom.comp s, hst.comp hsc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (singleTens E v (s x))) = x
    rw [compFin_singleTens_self, hcw, s1, RingEquiv.apply_symm_apply]
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s x)))) = 0
    rw [sigR_singleTens, compFin_singleTens_self, hcw, ← splitProj_comp, s2, map_zero]
  · intro x
    show _ * singleTens E v (s x) = singleTens E v (s x)
    rw [hpl, singleTens_mul, compFin_singleTens_self, one_mul]
  · intro a x
    show a * singleTens E v (s x) = singleTens E v (s _)
    rw [mul_comm, singleTens_mul]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_mul, s1, s1, hcw, map_mul, RingEquiv.symm_apply_apply, mul_comm]
    · rw [map_mul, s2, s2, zero_mul]
  · intro a
    show _ = singleTens E v (s _) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s _))
    rw [hpl, singleTens_mul, one_mul, sigR_singleTens, ← map_add (f := _)]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_add (f := _), s1, hcw, RingEquiv.symm_apply_apply, ← splitProj_comp, s2, add_zero]
    · rw [map_add (f := _), s2, zero_add, splitProj_comp_sigR hE, s1, hcw, RingEquiv.symm_apply_apply,
        ← sigR_compFin', splitProj_comp]
  · show singleTens E v (s 1) = _
    rw [hs1]

end GlobalTheory.Core.Rk.SplitIota

open scoped TensorProduct


open GlobalTheory.Core.Rk.SplitIota in
theorem GlobalTheory.Core.Rk.SplitIota.exists_iota : ∀ (D : D7) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = q), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → ∃ ι : w.adicCompletion D.host.E →+ AE D, Continuous ι ∧ (∀ x, cw h (ι x) = x) ∧ (∀ x, cw h (cA D (ι x)) = 0) ∧ (∀ x, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * ι x = ι x) ∧ (∀ a x, a * ι x = ι (cw h a * x)) ∧ (∀ a, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * a = ι (cw h a) + cA D (ι (cw h (cA D a)))) ∧ IsSplitIdem D (ι 1) ∧ Continuous (cw h) := by
  intro D q w h hs
  have hE := isCMExt_host D
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hs
  have hPu : P.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hP
  have hQu : Q.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hQ
  obtain ⟨w', hw', hw'u⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' ∧ w'.under (𝓞 D.host.F) = q := by
    by_cases e : w = P
    · exact ⟨Q, e ▸ hPQ, hQu⟩
    · exact ⟨P, e, hPu⟩
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hw' h hw'u
  obtain ⟨ι, h1, h2, h3, h4, h5, h6, h7⟩ := exists_iota_gen hE h hτ
  exact ⟨ι, h1, h2, h3, h4, h5, h6, GlobalTheory.AdelicU.Supp.isSplitIdem_iff_exists.2 ⟨q, τ, h7⟩, continuous_compW h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousTraceMul
section
noncomputable section

section Cont

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

theorem GlobalTheory.Core.Rk.SplitPsi.continuous_trace_mul (D : D7) (a : AE D) :
    Continuous fun z : AE D => Algebra.trace (AF D.host.F) (AE D) (a * z) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hT : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hT.comp (continuous_const.mul continuous_id)

end Cont

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

namespace GlobalTheory.Core.Rk.SplitPsi

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

end GlobalTheory.Core.Rk.SplitPsi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalRepLevelDecompositionFiniteUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem exists_isDec_finM : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (g : GA D (D.sp.X 0)), ∃ p, GlobalTheory.AdForm.IsDec F.cls0.lev F.cls0.y (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p :=
  fun D _ F g => GlobalTheory.AdForm.Model.exists_dec (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij.2 g

end GlobalTheory.Core.Mi
end

