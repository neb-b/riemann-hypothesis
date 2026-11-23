module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0Statement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_schwartzBruhat_finitePlaceCompletion_le_aleph0 : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (κ : Type) [Fintype κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.SBCount.rank_sb_localField_le | exact GlobalTheory.SBCount.rank_sb_localField_le | (intros; apply GlobalTheory.SBCount.rank_sb_localField_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem norm_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  intro D θ hθ V A fr hP x w
  symm
  refine Fintype.prod_equiv (Formalism.L2.Host.tauPl D) _ _ fun τ => ?_
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  unfold nrm eu GlobalTheory.SepPer.cmp
  rw [← map_inv (Formalism.IndefR.Eqv.UI.brg fr) x, (GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr).2.1 x⁻¹ τ _ rfl, hP τ]
  have key : ∀ (U Q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin V.rank → ℂ),
      A.fr τ *ᵥ (((A.fr τ)⁻¹ * U * Q) *ᵥ y) = U *ᵥ (Q *ᵥ y) := fun U Q y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  erw [key]
  have hP' : (Formalism.IndefR.Eqv.UI.instV fr).P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := hP τ
  have hφ : (Formalism.IndefR.Eqv.UI.instV fr).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
    show Formalism.IndefR.Eqv.UI.phiV D _ = _
    simp only [Formalism.IndefR.Eqv.UI.phiV, Equiv.symm_apply_apply]
  erw [hP', hφ]
  rfl

end GlobalTheory.NormDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf
section
noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def opInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Set (Module.End ℂ ↥(G.M.Pol Bs.ψ Bs.emb)) :=
  {g | (∃ k ∈ KInf σ G.W Bs.emb, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ G.W, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin a × Fin (a + a')))
        ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)}

def relInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ G.V, ∃ f ∈ G.M.Pol Bs.ψ Bs.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin a × Fin (a + a')))) ∨
    ∃ k ∈ KInf σ G.V Bs.emb, ∃ f f₁ : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑(f₁ : SInf F (Fin a × Fin (a + a'))) ∧ x = f₁ - f}

def opFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) :
    Set (Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v))) :=
  {g | ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ : ↥(SB (Fin a × Fin (a + a') → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ)}

def relFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) :=
  (augAt om v).comap (SB (Fin a × Fin (a + a') → Fv F v)).subtype

end GlobalTheory.HoweGlobal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWeilDataTwistCharacterTrivialSplitPla
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}
theorem mt_mul'' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one'' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
end GlobalTheory.HalfAverage

namespace GlobalTheory.HalfAverage

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

variable {D : D7}

theorem res_add {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    {F G : WO V W → ℂ} (hF : ∀ x, IntegrableOn (fun y => F (isoPart V W C y + midPart V V' W B x)) 𝓨 μ)
    (hG : ∀ x, IntegrableOn (fun y => G (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) :
    res V V' W C B μ 𝓨 (F + G) = res V V' W C B μ 𝓨 F + res V V' W C B μ 𝓨 G :=
  funext fun x => integral_add (hF x) (hG x)

theorem res_smul {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (a : ℂ) (F : WO V W → ℂ) : res V V' W C B μ 𝓨 (a • F) = a • res V V' W C B μ 𝓨 F :=
  funext fun x => integral_const_mul a _

theorem res_zero {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} :
    res V V' W C B μ 𝓨 (0 : WO V W → ℂ) = 0 :=
  funext fun x => integral_zero _ _

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := (GlobalTheory.SplitScalar.heisL ψ S T w).map_add f g

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := (GlobalTheory.SplitScalar.heisL ψ S T w).map_zero

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem charTwist_eq_one_at_split : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e W g → c g = 1 := by
  intro D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ c hc e he g hg
  have hψ := hω.std
  obtain ⟨K, hKC, hKB⟩ := _root_.GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb D V V' r C B hs
  have hR := (_root_.GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hμ).1
  obtain ⟨ℓ', hℓ', f₀, hf₀, hA⟩ := GlobalTheory.T.exists_halfInvariantForm_isotropicAverage_ne_zero D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he
  have hth : ∀ {f : WO V W → ℂ}, IsThetaFunO ψ V W f → ∀ u, IsThetaFunO ψ V W (heisO ψ V W u f) :=
    fun hf u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have hadd : ∀ u w : WO V W, IsHalf (cA D e) u → IsHalf (cA D e) w → ∀ f,
      heisO ψ V W (u + w) f = heisO ψ V W u (heisO ψ V W w f) := fun u w hu hw f =>
    GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W (GlobalTheory.SplitScalar.symplO_eq_zero V W hee hu hw) f

  have hint : ∀ f, IsThetaFunO ψ V W f → Integrable (fun t : halfMx (cA D e) W.rank r =>
      ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f))) (haarHalf (cA D e) W.rank r) := by
    intro f hf
    obtain ⟨L, Kc, hL, hKc, h0, hloc⟩ := GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he f hf
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.intro hKc fun t ht => by rw [h0 t ht, map_zero])
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hn : {s : halfMx (cA D e) W.rank r | s - t ∈ L} ∈ nhds t := by
      refine IsOpen.mem_nhds (hL.preimage (continuous_id.sub continuous_const)) ?_
      show t - t ∈ L
      rw [sub_self]; exact L.zero_mem
    filter_upwards [hn] with s hs
    have h1 := hloc t (s - t) hs
    rw [show t + (s - t) = s by abel] at h1
    simp only [h1]

  let P : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {f | (∀ (t : halfMx (cA D e) W.rank r) x, IntegrableOn
          (fun y => heisO ψ V W (restEmb V W K t) f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧
        Integrable (fun t : halfMx (cA D e) W.rank r =>
          ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f))) (haarHalf (cA D e) W.rank r)}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨fun t x => ?_, ?_⟩
        · rw [heisO_add']; exact (hf1 t x).add (hg1 t x)
        · refine (hf2.add hg2).congr (Filter.Eventually.of_forall fun t => ?_)
          simp only [Pi.add_apply, heisO_add', res_add (hf1 t) (hg1 t), map_add (f := _)]
      zero_mem' := by
        refine ⟨fun t x => ?_, ?_⟩
        · rw [heisO_zero']; exact integrableOn_zero
        · simp only [heisO_zero', res_zero, map_zero]; exact integrable_zero _ _ _
      smul_mem' := by
        rintro a f ⟨hf1, hf2⟩
        refine ⟨fun t x => ?_, ?_⟩
        · rw [GlobalTheory.SplitScalar.heisO_smul]; exact (hf1 t x).const_mul a
        · refine (hf2.const_mul a).congr (Filter.Eventually.of_forall fun t => ?_)
          simp only [GlobalTheory.SplitScalar.heisO_smul, res_smul, map_smul, smul_eq_mul] }
  have hP : ∀ f, IsThetaFunO ψ V W f → f ∈ P := fun f hf => ⟨fun t x => (hR _ (hth hf _)).1 x, hint f hf⟩
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun f => avgForm ψ V V' W C B μ 𝓨 K e ℓ' f.1
      map_add' := by
        rintro ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
        show avgForm ψ V V' W C B μ 𝓨 K e ℓ' (f + g) = avgForm ψ V V' W C B μ 𝓨 K e ℓ' f + avgForm ψ V V' W C B μ 𝓨 K e ℓ' g
        unfold avgForm
        rw [← integral_add hf2 hg2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [heisO_add', res_add (hf1 t) (hg1 t), map_add (f := _)]
      map_smul' := by
        rintro a ⟨f, hf1, hf2⟩
        show avgForm ψ V V' W C B μ 𝓨 K e ℓ' (a • f) = a • avgForm ψ V V' W C B μ 𝓨 K e ℓ' f
        unfold avgForm
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [GlobalTheory.SplitScalar.heisO_smul, res_smul, map_smul, smul_eq_mul] }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓP : ∀ f, f ∈ P → ℓ f = avgForm ψ V V' W C B μ 𝓨 K e ℓ' f := fun f hf =>
    LinearMap.congr_fun hℓ ⟨f, hf⟩

  have hsum : ∀ {p q : WO V W}, IsHalf (cA D e) p → IsHalf (cA D e) q → IsHalf (cA D e) (p + q) :=
    fun hp hq => (halfMx (cA D e) W.rank V.rank).add_mem hp hq
  have hinv : ∀ u : WO V W, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ V W f →
      ℓ (heisO ψ V W u f) = ℓ f := by
    intro u hu f hf
    rw [hℓP _ (hP _ (hth hf u)), hℓP _ (hP f hf)]
    obtain ⟨y, x, t₀, hy, hx, ht₀, rfl⟩ := _root_.GlobalTheory.HalfDecomp.half_decomp D V V' W r C B hs K hKC hKB (cA D e) u hu
    unfold avgForm
    let t₀' : halfMx (cA D e) W.rank r := ⟨t₀, ht₀⟩
    have h1 : IsHalf (cA D e) (isoPart V W C y) := isHalf_mul hy _
    have h2 : IsHalf (cA D e) (midPart V V' W B x) := isHalf_mul hx _
    have h3 : IsHalf (cA D e) (restEmb V W K t₀) := isHalf_mul ht₀ _
    have key : ∀ t : halfMx (cA D e) W.rank r,
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t)
          (heisO ψ V W (isoPart V W C y + midPart V V' W B x + restEmb V W K t₀) f))) =
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑(t + t₀')) f)) := by
      intro t
      have h4 : IsHalf (cA D e) (restEmb V W K ↑t) := isHalf_mul t.2 _
      have h5 : IsHalf (cA D e) (restEmb V W K ↑(t + t₀')) := isHalf_mul (t + t₀').2 _
      rw [← hadd _ _ h4 (hsum (hsum h1 h2) h3)]
      have e1 : restEmb V W K ↑t + (isoPart V W C y + midPart V V' W B x + restEmb V W K t₀) =
          isoPart V W C y + (midPart V V' W B x + restEmb V W K ↑(t + t₀')) := by
        rw [show ((t + t₀' : halfMx (cA D e) W.rank r) : Mx D W.rank r) = ↑t + t₀ from rfl, restEmb_add]
        abel
      rw [e1, hadd _ _ h1 (hsum h2 h5), hadd _ _ h2 h5]
      have g1 := hth hf (restEmb V W K ↑(t + t₀'))
      have g2 := hth g1 (midPart V V' W B x)
      rw [(hR _ g2).2.2.2 y, (hR _ g1).2.2.1 x]
      exact hℓ' x hx _ (hR _ g1).2.1
    rw [integral_congr_ae (Filter.Eventually.of_forall key)]
    exact integral_add_right_eq_self (fun t : halfMx (cA D e) W.rank r =>
      ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑t) f))) t₀'

  have hmi : mt W g * mt W g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  have him : mt W g⁻¹ * mt W g = 1 := by rw [← mt_mul'', inv_mul_cancel, mt_one'']
  have hdet : IsUnit (mt W g).det := Matrix.isUnit_det_of_right_inverse hmi
  set s : AE D := ((hdet.unit : (AE D)ˣ) : AE D) with hs_def
  set s' : AE D := (((hdet.unit)⁻¹ : (AE D)ˣ) : AE D) with hs'_def
  have hss : s * s' = 1 := hdet.unit.mul_inv
  have hss' : s' * s = 1 := hdet.unit.inv_mul
  have he1 : e * e = e := he.1
  let y : (AE D)ˣ := ⟨e * s + (1 - e), e * s' + (1 - e),
    by linear_combination (s * s' - s - s' + 1) * he1 + e * hss,
    by linear_combination (s' * s - s' - s + 1) * he1 + e * hss'⟩
  have hy : IsDetAt e W g y := by
    show e * s + (1 - e) = e * (mt W g).det + (1 - e)
    rw [hs_def, IsUnit.unit_spec]
  have hV1 : ∀ X : HSp D, SuppAt e X 1 := fun X i j => by
    rw [mt_one'', sub_self]; simp
  have hD1 : ∀ X : HSp D, IsDetAt e X 1 1 := fun X => by
    show (1 : AE D) = e * (mt X 1).det + (1 - e)
    rw [mt_one'', Matrix.det_one]; ring
  obtain ⟨r₁, hr₁, hsp⟩ := hω.om_split e he 1 g (hV1 V) hg 1 y (hD1 V) hy
  obtain ⟨r₂, hr₂, hsp'⟩ := hω'.om_split e he 1 g (hV1 V') hg 1 y (hD1 V') hy
  have E1 := hsp ℓ hinv f₀ hf₀
  obtain ⟨κ, hκ, hscale⟩ := _root_.GlobalTheory.HalfAverage.integral_leftMul_eq_smul D (cA D e) W.rank r (mt W g⁻¹) (mt W g) him hmi
  have E2 : ℓ (ω (1, g) f₀) = ((c g : ℂ) * r₂ * splitFacO χS χT' 1 y * κ) * ℓ f₀ := by
    rw [hℓP _ (hP _ (hω.om_pres _ _ hf₀)), hℓP _ (hP _ hf₀)]
    unfold avgForm
    have key2 : ∀ t : halfMx (cA D e) W.rank r,
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) (ω (1, g) f₀))) =
        ((c g : ℂ) * r₂ * splitFacO χS χT' 1 y) *
          ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t)) f₀)) := by
      intro t
      have hG := hth hf₀ (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t))
      have hcomm : ω (1, g) (heisO ψ V W (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t)) f₀) =
          heisO ψ V W (restEmb V W K ↑t) (ω (1, g) f₀) := by
        rw [hω.om_heis 1 g _ f₀ hf₀]
        congr 1
        show HMul.hMul (HMul.hMul (mt W g) (HMul.hMul (HMul.hMul (mt W g⁻¹) (t : Mx D W.rank r)) (K.map (incA D))))
          (mt V 1⁻¹) = HMul.hMul (t : Mx D W.rank r) (K.map (incA D))
        rw [inv_one, mt_one'', Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmi, Matrix.one_mul]
      rw [← hcomm, hc g _ hG, map_smul, hsp' ℓ' hℓ' _ (hR _ hG).2.1, smul_eq_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall key2), integral_const_mul,
      hscale (fun t => ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑t) f₀)))]
    ring

  have hχ : ((χS y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hL : ℓ f₀ ≠ 0 := by rw [hℓP _ (hP _ hf₀)]; exact hA
  have hsf : ∀ χ' : (AE D)ˣ →* Circle, (splitFacO χS χ' 1 y : ℂ) = (χS y : ℂ) := fun χ' => by
    simp [splitFacO]
  rw [E1, hsf, hsf] at E2
  have h1 : ((r₁ : ℂ) * (χS y : ℂ)) = (c g : ℂ) * r₂ * (χS y : ℂ) * κ := mul_right_cancel₀ hL E2
  have h2 : ((c g : ℂ) * ((r₂ : ℂ) * κ)) * (χS y : ℂ) = (r₁ : ℂ) * (χS y : ℂ) := by linear_combination -h1
  have h3 := mul_right_cancel₀ hχ h2
  have hpos : (0 : ℝ) < r₂ * κ := mul_pos hr₂ hκ
  have h4 : (c g : ℂ) = ((r₁ / (r₂ * κ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (by exact_mod_cast hpos.ne'), h3]
  have hn : ‖(c g : ℂ)‖ = 1 := by
    first | exact Circle.norm_coe (c g) | exact Circle.abs_coe (c g) | exact mem_sphere_zero_iff_norm.1 (c g).2
  rw [h4, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr₁ hpos)] at hn
  have h5 : (c g : ℂ) = 1 := by rw [h4, hn, Complex.ofReal_one]
  exact Circle.ext (by rw [h5, Circle.coe_one])

end GlobalTheory.HalfAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowLevelMatchAtOfLevelConjugation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem conj_mem_and_char_eq_of_levelConjugation {H : Type} [Group H] (t s : H) (J J' : Set H) (χ χ' : H → ℂ)
    (hc : ∀ k, (k ∈ J ↔ t⁻¹⁻¹ * k * t⁻¹ ∈ J') ∧ (k ∈ J → χ' (t⁻¹⁻¹ * k * t⁻¹) = χ k)) (hs : s ∈ J') :
    t⁻¹ * s * t ∈ J ∧ χ (t⁻¹ * s * t) = χ' s := by
  have e : t⁻¹⁻¹ * (t⁻¹ * s * t) * t⁻¹ = s := by group
  have h := hc (t⁻¹ * s * t)
  rw [e] at h
  exact ⟨h.1.2 hs, (h.2 (h.1.2 hs)).symm⟩

theorem conj_mul_eq_mul_conj_group {H : Type} [Group H] (t a b : H) : t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by
  group

theorem rowLevelMatchAt_of_conjLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hPin hE0 ht hConj hFrame
  obtain ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ := hPin
  refine ⟨(R.eG.trans cG).symm, fun k => cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))), ?_, ?_, ?_⟩
  · intro k hk
    have e2 : (iotaX X h).toMulEquiv ((iotaX X h).symm (1, k)) = (1, k) :=
      (iotaX X h).toMulEquiv.apply_symm_apply (1, k)
    have hs : (iotaX X h).symm (1, k) ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} := by
      rw [Set.mem_preimage, e2]; exact ⟨rfl, hk⟩
    have hA := conj_mem_and_char_eq_of_levelConjugation (H := GA D (Yc D 0)) t ((iotaX X h).symm (1, k)) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) (fun k' => hConj k') hs
    refine ⟨hA.1, hA.2.trans ?_⟩
    show star (X.chi2 ((iotaX X h).toMulEquiv ((iotaX X h).symm (1, k))).2) = _
    rw [e2]
  · obtain hl := _root_.GlobalTheory.KapLevel.kap_mem_parLev R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame
    refine ⟨⟨_root_.GlobalTheory.RedFrame.goodAt_kap_red R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame, ?_,
      _root_.GlobalTheory.SeeMatchOnto.onto R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame,
      _root_.GlobalTheory.KapRed.red_kap_eq_one_iff R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame⟩, ?_⟩
    · intro k hk k' hk'
      have e1 : (iotaX X h).symm (1, k * k') = (iotaX X h).symm (1, k) * (iotaX X h).symm (1, k') := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      have e : kap X h t (k * k') = kap X h t k * kap X h t k' := by
        unfold kap; rw [e1]; exact conj_mul_eq_mul_conj_group (H := GA D (Yc D 0)) t _ _
      show cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t (k * k')))) = cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) * cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k')))
      rw [e, map_mul, Formalism.L2.DIV.rTup_mul (hl k hk).2 (hl k' hk').2]
      exact map_mul cG _ _
    · intro k hk T hT v g
      rw [_root_.GlobalTheory.RowActLift.act_kap R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame k hk T hT v g]
      have e3 : R.eG ((R.eG.trans cG).symm (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))))) = rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)) := by
        rw [MulEquiv.symm_trans_apply]
        exact (congrArg (fun y => R.eG (R.eG.symm y)) (cG.symm_apply_apply _)).trans (R.eG.apply_symm_apply _)
      rw [e3]
  · intro γ
    unfold RealDat.eC
    rw [hE0 γ, hcoef, MulEquiv.apply_symm_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecay
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurConst

theorem schurMult_all : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 :=
  fun hP _ _ _ _ _ _ _ _ μ 𝓕 _ _ => GlobalTheory.MultFinite.schurMult hP μ 𝓕

end GlobalTheory.SchurConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeparationLineOfBessel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_prod_of_separately {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (b : ∀ i, X i → ℂ) (β : (∀ i, X i) → ℂ)
    (h : ∀ i x, ∃ c : ℂ, ∀ y, β (Function.update x i y) = c * b i y) : ∃ l : ℂ, ∀ x, β x = (∏ i, b i (x i)) * l := by
  by_cases h0 : ∃ i, ∀ y, b i y = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun x => ?_⟩
    obtain ⟨c, hc⟩ := h i x
    have := hc (x i)
    rw [Function.update_eq_self, hi] at this
    simp [this]
  push_neg at h0
  choose x₀ hx₀ using h0
  have key : ∀ s : Finset ι, ∀ x, (∀ i, i ∉ s → x i = x₀ i) →
      β x * ∏ i ∈ s, b i (x₀ i) = β x₀ * ∏ i ∈ s, b i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; rw [show x = x₀ from funext fun i => hx i (by simp)]
    | insert j s hj ih =>
      intro x hx
      obtain ⟨c, hc⟩ := h j x
      have e1 := hc (x j)
      rw [Function.update_eq_self] at e1
      have e2 := ih (Function.update x j (x₀ j)) fun i hi => by
        by_cases e : i = j
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hx i (by simp [e, hi])
      have e3 : ∏ i ∈ s, b i (Function.update x j (x₀ j) i) = ∏ i ∈ s, b i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [hc, e3] at e2
      rw [Finset.prod_insert hj, Finset.prod_insert hj, e1]
      linear_combination b j (x j) * e2
  have hn : ∏ i, b i (x₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx₀ i
  refine ⟨β x₀ / ∏ i, b i (x₀ i), fun x => ?_⟩
  have := key Finset.univ x (by simp)
  field_simp
  linear_combination this

end GlobalTheory.SepRows

end
end

