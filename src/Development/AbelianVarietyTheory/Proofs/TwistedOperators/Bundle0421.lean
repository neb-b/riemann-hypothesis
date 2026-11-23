module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLOfIsVecBasisAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

theorem transportSt (D : D7) : TransportSt D := by
  intro W Y hr L Λ hL hΛ S hS n be be' h h'
  refine ⟨exists_transport W Y hr L Λ hL hΛ S hS n be be' h h', fun x hx x' => ?_⟩
  first
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' (selfDual_isFullLattice hL) h x hx x'
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' hL.1 h x hx x'

private theorem fullLattice_of_glueVec {X : HSp D} {u : D.what₂.Word} {L₀ : Lat X}
    {f : Fin X.rank → EAf D} (hL : L₀.FG) (hf : IsGlueVec X u L₀ f) :
    Submodule.IsFullLattice D.host.E L₀ := by
  let β₀ : GL (Fin X.rank) (EAf D) := 1
  have hstd := GlobalTheory.NormSum.AdLattice.lat_isLattice β₀
  have hfull : Submodule.IsFullLattice D.host.E (L₀ ⊔ lat β₀) :=
    Submodule.IsFullLattice.of_le_of_fg _ le_sup_right (hL.sup hstd.fg)
  obtain ⟨β, hβ⟩ := exists_eq_lat hfull
  obtain ⟨β', hβ', -⟩ := exists_dual_frame X β
  have hle : L₀ ≤ lat β := hβ ▸ le_sup_left
  have := GlobalTheory.NormSum.AdLattice.lat_isLattice β'
  have := Submodule.IsLattice.of_fg D.host.E hL
  let t : D.host.Eˣ := Units.mk0 (Tu D u) (Tu_ne_zero u)
  refine Submodule.IsFullLattice.of_le D.host.E (M := t • lat β') ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  apply GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL
  let xA : Fin X.rank → EAf D := fun i => inc D (x i)
  have hxA : ∀ z ∈ hat L₀, hA X z xA ∈ OA D :=
    fun z hz => (dual_hat_lat hβ' xA).2 (inc_mem_hat hx) z (hat_mono hle hz)
  obtain ⟨a, ha, hxa⟩ := hf.dual xA hxA
  have htx := add_mem_hat (smul_mem_hat (inc_Tu_mem u) hxa) (smul_mem_hat ha hf.mul_mem)
  rw [smul_sub, smul_comm (inc D (Tu D u)) a, sub_add_cancel] at htx
  convert htx using 1
  funext i
  change inc D (Tu D u * x i) = inc D (Tu D u) * inc D (x i)
  exact map_mul _ _ _

theorem gluedSt (D : D7) : GluedSt D := by
  intro u π hπ Y X ι z hz L₀ f₀ hb
  obtain ⟨f, hf, hff⟩ := GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData D u π hπ X L₀ f₀ hb
  have hL₀ := fullLattice_of_glueVec hb.1.fg hf
  obtain ⟨x, hx⟩ := exists_sub_inc_mem_hat (D := D) (Λ := L₀) hL₀.span_eq_top f
  obtain ⟨x₀, hx₀⟩ := vA_surj X x
  rw [← hx₀] at hx
  have hg : IsGlueVec X u L₀ (vA X x₀) := hf.congr hx
  have hgl : IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
    refine _root_.GlobalTheory.GluedCmp.isGlued_glueLat D u π Y X ι z hz L₀ x₀ f₀ hL₀.toIsLattice hg (fun w hw => ⟨?_, ?_⟩)
    · rw [← hff w hw, smul_smul, idem_mul_self]
    · rw [← hff w hw, ← smul_sub]
      exact smul_mem_hat (idem_mem w) hx
  have huniq : ∀ L, IsGlued Y X ι z u π L₀ f₀ L → L = glueLat Y X ι z u L₀ x₀ :=
    fun L hL => GlobalTheory.T.gluedHermitianLattice_unique D u π hπ Y X ι z L₀ f₀ L _ hL hgl
  refine ⟨⟨_, hgl, huniq⟩, fun L hL => ?_⟩
  rw [huniq L hL]
  exact GlobalTheory.T.gluedLattice_selfDual_primitive_meet D u Y X ι z hz L₀ x₀ hL₀ hg

theorem ungluedSt (D : D7) : UngluedSt D := by
  intro u π hπ Y X ι z hz L hSD hP
  obtain ⟨hlat, x₀, hL⟩ := GlobalTheory.T.primitive_lattice_glued_from_intersection D u Y X ι z hz L hSD hP

  have hg : IsGlueVec X u (capX Y X ι L) (vA X x₀) := by
    have key := GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive D u Y X ι z hz (capX Y X ι L) x₀ hlat
    rw [← hL] at key
    exact key hSD hP
  have := hlat
  refine ⟨fun w => idem w • vA X x₀,
    GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector D u π hπ X _ _ (by infer_instance) hg, ?_⟩
  have key := _root_.GlobalTheory.GluedCmp.isGlued_glueLat D u π Y X ι z hz (capX Y X ι L) x₀ (fun w => idem w • vA X x₀) hlat.toIsLattice hg
    (fun w _ => ⟨by simp only [smul_smul, idem_mul_self], by simp only [sub_self]; exact zero_mem_hat⟩)
  rwa [← hL] at key

theorem adelicIsometries (D : D7) : AdelicIsometries D := by
  unfold AdelicIsometries LamNSt
  exact ⟨plIdemSt D, transportSt D, _root_.GlobalTheory.AdIsomCorrection.correction_of_transport D (transportSt D),
    splitGlueSt_of D (fun n Λ Λ' hΛ hΛ' v => _root_.GlobalTheory.LocHat.locL_eq_iff_idem D n Λ Λ' hΛ hΛ' v),
    GlobalTheory.T.selfDualLattice_image_adelicUnitary D, GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D, _root_.GlobalTheory.StdIsom.stdIsomSt_of_rationalSt D (GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D), GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof D,
    gluedSt D, ungluedSt D,
    ⟨fun u Y X ι z ρ e f h L hL nn hn => _root_.GlobalTheory.HypLattice.isSelfDualC_lamN D u Y X ι z ρ e f h L hL nn hn,
      (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).1, (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).2⟩,
    frameSt D⟩

end GlobalTheory.AdIsom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem cmp_mul' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (a b : GA D V) :
    cmp θ τ (a * b) = cmp θ τ a * cmp θ τ b := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) (a * b) = infMat D.sp.cm.sig V.gram (θ τ) a * infMat D.sp.cm.sig V.gram (θ τ) b
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]

theorem cmp_one' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) : cmp θ τ (1 : GA D V) = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) 1 = 1
  rw [e, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem frConj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  change _ * _ * _ = _
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem rep_one' (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul'' (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (frConj_mem M τ hg) _ (frConj_mem M τ hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_inner' (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (a b : M.H τ) : ⟪M.rep τ g a, M.rep τ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(M.rep τ g : M.H τ →ₗ[ℂ] M.H τ), fun v => (M.ds τ).2.2.1.2.1 _ (frConj_mem M τ hg) v⟩ :
    M.H τ →ₗᵢ[ℂ] M.H τ).inner_map_map a b

end GlobalTheory.PoinConj

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem poin_conj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  intro D θ hθ V S M K v₀ g₀ hg₀ c g
  unfold poin
  congr 1
  funext γ
  have ez : g₀⁻¹ * c * γ * (g * g₀) = g₀⁻¹ * (c * γ * g) * g₀ := by group
  rw [ez]
  set z := c * γ * g
  have h1 : Lev.finE V g₀ = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V g₀ = 1 from hg₀, map_one]
  have hf : Lev.finE V (g₀⁻¹ * z * g₀) = Lev.finE V z := by
    rw [map_mul, map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  unfold coef
  rw [hf]
  split_ifs with hK
  · unfold coefR
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hU : ∀ x : GA D V, cmp θ τ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun x => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ
    rw [cmp_mul', cmp_mul', rep_mul'' M τ (by rw [← cmp_mul']; exact hU _) (hU _),
      rep_mul'' M τ (hU _) (hU _), ← rep_inner' M τ (hU g₀), ← rep_mul'' M τ (hU g₀) (hU g₀⁻¹), ← cmp_mul',
      mul_inv_cancel, cmp_one', rep_one']
  · rfl

end GlobalTheory.PoinConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjInstanceCharacterEqProdResidueFieldAddCharsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjInstanceCharacter_eq_prod_residueField_addChars : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  first | exact @GlobalTheory.SeeConjProd.chiS_eq_prod | exact GlobalTheory.SeeConjProd.chiS_eq_prod | (intros; apply GlobalTheory.SeeConjProd.chiS_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMultiplicityValueExceedsHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SupVal

theorem tprod_ne_zero' {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_bound_half_lt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)), GlobalTheory.Unf.Vol V → ∀ t ∈ MultT θ M J 1, t ≠ 0 →
    ∀ w : M.Vec, (∀ τ, (w τ : M.H τ) ≠ 0) → ∃ b : ℝ, ∃ x : GA D V,
      (∀ h, ‖t (PiTensorProduct.tprod ℂ w) h‖ ≤ b) ∧ b / 2 < ‖t (PiTensorProduct.tprod ℂ w) x‖ := by
  intro hP D θ hθ V S M J vol t ht ht0 w hw
  have hw' : PiTensorProduct.tprod ℂ w ≠ 0 :=
    tprod_ne_zero' fun τ h => hw τ (by simp [h])
  have hS := _root_.GlobalTheory.SchurConst.schurMult_all hP D θ hθ V S M J 1 vol.μ vol.𝓕 vol.haar vol.fund
  set φ := t (PiTensorProduct.tprod ℂ w) with hφ
  have hφ0 : φ ≠ 0 := fun h => ht0 (_root_.GlobalTheory.multT_eq_zero_of_apply_eq_zero θ M J 1 vol.μ vol.𝓕 hθ vol.haar vol.fund hS t ht _ hw' h)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  have hR := (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J 1 t ht
    (PiTensorProduct.tprod ℂ w)).2.2
  obtain ⟨C, hC⟩ := hR.2.2 0
  have hbdd : BddAbove (Set.range fun g => ‖φ g‖) := ⟨C, by
    rintro _ ⟨g, rfl⟩
    simpa using hC g⟩
  have hle : ∀ h, ‖φ h‖ ≤ sSup (Set.range fun g => ‖φ g‖) := fun h => le_csSup hbdd ⟨h, rfl⟩
  have hpos : 0 < sSup (Set.range fun g => ‖φ g‖) := lt_of_lt_of_le (norm_pos_iff.2 hx₀) (hle x₀)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) (half_lt_self hpos)
  exact ⟨_, x, hle, hx⟩

end GlobalTheory.SupVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementLatticeBetweenPrimeMulSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

end GlobalTheory.HeckeLocStep

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem hat_mono {D : D7} {n : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : L ≤ L') :
    GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin n → D.host.E)) := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, ha, x, h hx, rfl⟩

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem mem_iff_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    ∀ v ∈ latG V g, (v ∈ M ↔ finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e g M he hPM hMΛ v hv
  obtain ⟨h1, h2, -, -, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ h1
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ h2).symm.le.trans (Submodule.span_mono hPM))
  have hrat := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank M hMfg hMsp).1
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  have hvM : ∀ {w}, w ∈ M → GlobalTheory.AdLat.fv D.host.F w ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E)) :=
    fun hw => (hrat _).2 hw
  constructor
  · intro hm
    exact smul_mem_hat D M hint (hvM hm)
  · intro h
    refine (hrat v).1 ?_
    have hΛ : GlobalTheory.AdLat.fv D.host.F v ∈ GlobalTheory.AdLat.hat D.host.F ((latG V g : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) :=
      ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).2 hv
    have h3 := hat_mono hPM (_root_.GlobalTheory.ComplOffPlace.one_sub_smul_mem D P e V.rank (latG V g) he _ hΛ)
    have hsplit : GlobalTheory.AdLat.fv D.host.F v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]; rfl
    rw [hsplit]
    exact add_mem h h3

theorem mem_latG_iff (D : D7) (V : HSp D) (x : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V x ↔ finVec V v ∈ latGHat V x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [h5]
  exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).symm

theorem exists_hecke : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  obtain ⟨a₀, hH, hloc⟩ := _root_.GlobalTheory.HeckeLocLift.exists_hecke_ePart D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  refine ⟨a₀, hH, ?_, _root_.GlobalTheory.HeckeConjPart.conj_part D V P e ϖ k g a₀ he h1 h2 hH⟩
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  ext v
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨ha, hg⟩
    refine (mem_iff_ePart D V P e g M he hPM hMΛ v hg).2 ((hloc v hg).1 ?_)
    have := (mem_latG_iff D V (g * a₀) v).1 ha
    rw [(GlobalTheory.Member.latG_lattice_and_completion D V (g * a₀)).2.2.2.2.1] at this ⊢
    exact smul_mem_hat D _ hint this
  · intro hv
    have hg := hMΛ hv
    refine ⟨(mem_latG_iff D V (g * a₀) v).2 ?_, hg⟩
    have hsplit : finVec V v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [hsplit]
    exact add_mem ((hloc v hg).2 ((mem_iff_ePart D V P e g M he hPM hMΛ v hg).1 hv))
      (_root_.GlobalTheory.HeckeOffParts.off_parts D V e ϖ k g a₀ he.1 hH _ ((mem_latG_iff D V g v).1 hg))

end GlobalTheory.HeckeLocStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDiagonalStabilizerGeneratedHermitianDoStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  first | exact @GlobalTheory.DblVac.gen_diag_anti_split_herm | exact GlobalTheory.DblVac.gen_diag_anti_split_herm | (intros; apply GlobalTheory.DblVac.gen_diag_anti_split_herm <;> assumption)
end

