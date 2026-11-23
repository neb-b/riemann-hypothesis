module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import GroundTheory.GlobalFields.Adele.Approximation
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryHaarEqMapProdRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarSplit
open scoped ENNReal NNReal

theorem haar_eq_map_prod : ∀ (D : D7) (Y : HSp D) (ν : Measure (GA D Y)), ν.IsHaarMeasure → ∃ (m : Measure (GinfC Y)) (μ : Measure (GfC Y)), m.IsHaarMeasure ∧ μ.IsHaarMeasure ∧ SigmaFinite m ∧ SigmaFinite μ ∧ MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) ∧ ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) := by
  intro D Y ν hν
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  haveI : LocallyCompactSpace (GfC Y) := (GlobalTheory.AdelicSplit.isClosed_GfC' Y).locallyCompactSpace
  set e := GlobalTheory.AdelicSplit.splitEquiv Y with he_def
  have he : (⇑e : GinfC Y × GfC Y → GA D Y) = fun q => (q.1 : GA D Y) * q.2 := rfl
  let m₀ : Measure (GinfC Y) := Measure.haar
  let μ : Measure (GfC Y) := Measure.haar
  haveI hρ : ((m₀.prod μ).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ e
  set c := Measure.haarScalarFactor ν ((m₀.prod μ).map e) with hc_def
  have hc : ν = c • (m₀.prod μ).map e := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  haveI hm : ((c : ℝ≥0∞) • m₀).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (by simpa using hc0) ENNReal.coe_ne_top
  refine ⟨(c : ℝ≥0∞) • m₀, μ, hm, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← he]; exact e.toHomeomorph.measurableEmbedding
  · rw [← he, Measure.prod_smul_left, Measure.map_smul, hc, ENNReal.smul_def]
    exact e.continuous.measurable.aemeasurable

end GlobalTheory.HaarSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedinger
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchHeis

variable {F : Type} [Field F] [NumberField F]

def intFin (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intFin_mem (κ : Type) [Fintype κ] : intFin (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intFin, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intFin, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

def refFin (κ : Type) (x : κ → AF F) : ℂ := intFin κ (fun i => (x i).2)

theorem fst_eq_zero_of_ev {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp h

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have := congrArg Prod.snd (congrFun (hz (0, 1) h0) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

theorem refFin_of_zero (κ : Type) (x : κ → AF F) (hx : ∀ i, (x i).2 = 0) : refFin κ x = 1 := by
  have : (fun i => (x i).2) = 0 := funext hx
  simp only [refFin, this, intFin]
  rw [Set.indicator_of_mem (show (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
    fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
      fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
  rfl

theorem refFin_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : refFin κ (liftV y) = 1 :=
  refFin_of_zero κ _ fun _ => rfl

theorem refFin_add_liftV {κ : Type} (x : κ → AF F) (y : κ → mixedEmbedding.mixedSpace F) :
    refFin κ (x + liftV y) = refFin κ x := by
  have : (fun i => ((x + liftV y) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + 0 = (x i).2
    rw [add_zero]
  simp only [refFin, this]

theorem rest_refFin (κ : Type) [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFin κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intFin κ, intFin_mem κ, rfl⟩⟩
  have : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [snd_eq_zero_of_at hz i, add_zero]
  simp only [refFin, this]

theorem liftV_locV_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) : liftV (locV z) = z := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact (snd_eq_zero_of_at hz i).symm

theorem evI_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (liftV y i) = y i :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem evH_invTwo : evH F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h1 : evH F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evH F) 2, ← map_mul, invOf_mul_self, map_one]
  have h2 : (2 : mixedEmbedding.mixedSpace F) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  calc evH F (⅟(2 : AF F)) = evH F (⅟(2 : AF F)) * (2 * algebraMap ℝ _ (1 / 2)) := by rw [h2, mul_one]
    _ = algebraMap ℝ _ (1 / 2) := by rw [← mul_assoc, h1, one_mul]

theorem schr_tens {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ (liftV v.1, liftV v.2) (tens (evI F) g (refFin κ)) = tens (evI F) (schrF (trP F κ) v g) (refFin κ) := by
  funext x
  set z : AF F := x ⬝ᵥ liftV v.2 + ⅟(2 : AF F) * (liftV v.1 ⬝ᵥ liftV v.2) with hz
  let finH : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have hfin : finH z = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, dotProduct, map_add (f := _), map_mul, map_sum]
    have e : ∀ i, finH (liftV v.2 i) = 0 := fun _ => rfl
    simp only [e, mul_zero, Finset.sum_const_zero, add_zero]
  have hAt : At (evI F) z := by
    intro c hc
    refine Prod.ext ?_ ?_
    · change c.1 * z.1 = 0
      rw [fst_eq_zero_of_ev hc, zero_mul]
    · change c.2 * finH z = 0
      rw [hfin, mul_zero]
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F z) =
      trP F κ (fun i => evI F (x i)) v.2 + trP F κ v.1 v.2 / 2 := by
    rw [evI_eq, hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_mul, map_sum, ← evI_eq, evI_liftV, trP]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show evI F (⅟(2 : AF F)) = algebraMap ℝ _ (1 / 2) from evH_invTwo, ← Algebra.smul_def, map_smul, map_sum,
      smul_eq_mul]
    ring
  have hloc : (fun i => evI F ((x + liftV v.1) i)) = (fun i => evI F (x i)) + v.1 := by
    funext i
    simp only [Pi.add_apply, evI_eq, map_add (f := _)]
    exact congrArg (evH F (x i) + ·) (evI_liftV v.1 i)
  simp only [schr, tens, schrF]
  rw [hψ.2.2 z hAt, htr, hloc, refFin_add_liftV]
  ring

end GlobalTheory.ArchHeis

namespace GlobalTheory.ArchHeis

theorem archOp_schrF : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
      ⇑(archOp om h f₁) = schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW hex h hh v f f₁ hf₁
  have hS := IsUWeilPair.isUSplitting hW
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  set u' := actAB (cA σ) ((1 : UA σ X.J), h) u with hu'
  have hAt : ∀ c : AF F, evI F c = 0 → c • u' = 0 := by
    intro c hc
    have h0 : c • u = 0 := by
      have hl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, c • liftV y = 0 := by
        intro y
        funext i
        refine Prod.ext ?_ ?_
        · change c.1 * _ = 0
          rw [fst_eq_zero_of_ev hc, zero_mul]
        · change c.2 * 0 = 0
          rw [mul_zero]
      rw [hu, ← LinearEquiv.map_smul, Prod.smul_mk, hl, hl, Prod.mk_zero_zero, LinearEquiv.map_zero]
    simp only [hu', actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul]
  have hAt₁ : At (evI F) (M.co.e u').1 := by
    intro c hc
    have := congrArg Prod.fst (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have hAt₂ : At (evI F) (M.co.e u').2 := by
    intro c hc
    have := congrArg Prod.snd (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have he' : M.co.e u' = (liftV (archAct M h v).1, liftV (archAct M h v).2) := by
    change M.co.e u' = (liftV (locV (M.co.e u').1), liftV (locV (M.co.e u').2))
    rw [liftV_locV_of_at hAt₁, liftV_locV_of_at hAt₂]
  have hA₁ := acts_archOp om h f₁ (hex h hh f₁) (refFin _) (rest_refFin _ f₁)
  have hA := acts_archOp om h f (hex h hh f) (refFin _) (rest_refFin _ f)
  have himpl := hS.impl (1, h) u (tens (evI F) ⇑f (refFin _)) (rest_refFin _ f).2
  have h1 : M.co.rho ψ u (tens (evI F) ⇑f (refFin _)) = tens (evI F) ⇑f₁ (refFin _) := by
    simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
    rw [schr_tens ψ hψ v, hf₁]
  have h2 : M.co.rho ψ u' (tens (evI F) ⇑(archOp om h f) (refFin _)) =
      tens (evI F) (schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f)) (refFin _) := by
    simp only [Darboux.rho]
    rw [he', schr_tens ψ hψ]
  rw [h1, hA₁, hA, ← hu', h2] at himpl
  funext y
  have := congrFun himpl (liftV y)
  simp only [tens, refFin_liftV, mul_one] at this
  have hy : (fun i => evI F (liftV y i)) = y := funext fun i => evI_liftV y i
  rwa [hy] at this

end GlobalTheory.ArchHeis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMul
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.Laws

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def intInd (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hOo : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    unfold GroundTheory.Global.integralFiniteAdeles
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hOc : IsCompact (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hOcl : IsClosed (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    hOc.isClosed
  have hU : IsClopen (Set.pi Set.univ fun _ : κ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    ⟨isClosed_set_pi fun _ _ => hOcl, isOpen_set_pi Set.finite_univ fun _ _ => hOo⟩
  show IsLocallyConstant (intInd (F := F) κ) ∧ HasCompactSupport (intInd (F := F) κ)
  refine ⟨(LocallyConstant.indicator (1 : LocallyConstant (κ → FiniteAdeleRing (𝓞 F) F) ℂ) hU).isLocallyConstant, ?_⟩
  exact HasCompactSupport.intro' (isCompact_univ_pi fun _ => hOc) hU.isClosed
    fun x hx => Set.indicator_of_notMem hx _

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hu : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h0 : u * z i = 0 := congrFun (hz u hu) i
  have h1 : (u * z i).2 = (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 := rfl
  rw [h0, one_mul] at h1
  exact h1.symm

def refFun (κ : Type) : (κ → AF F) → ℂ := fun x => intInd κ (fun i => (x i).2)

theorem refFun_rest {κ : Type} [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩⟩
  show intInd κ (fun i => (x i + z i).2) = intInd κ (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [snd_eq_zero_of_at hz i, add_zero]

theorem refFun_lift {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : refFun κ (liftV t) = 1 := by
  show intInd κ (fun i => (liftV t i).2) = 1
  unfold intInd
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _
    change (0 : FiniteAdeleRing (𝓞 F) F) ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
    exact zero_mem _

theorem tens_lift {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (t : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (refFun κ) (liftV t) = φ t := by
  show φ (fun i => evI F (liftV t i)) * refFun κ (liftV t) = φ t
  rw [refFun_lift, mul_one]
  congr 1
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem eq_of_tens {κ : Type} [Fintype κ] {f₁ f₂ : SInf F κ}
    (h : tens (evI F) (f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) = tens (evI F) (f₂ : _ → ℂ) (refFun κ)) :
    f₁ = f₂ := by
  ext t
  have key := congrFun h (liftV t)
  rwa [tens_lift, tens_lift] at key

theorem tens_add {κ : Type} [Fintype κ] (f f' : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(f + f') : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = tens (evI F) ⇑f r + tens (evI F) ⇑f' r := by
  funext x
  change (f + f') (fun i => evI F (x i)) * r x = f (fun i => evI F (x i)) * r x + f' (fun i => evI F (x i)) * r x
  rw [SchwartzMap.add_apply, add_mul]

theorem tens_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(c • f) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = c • tens (evI F) ⇑f r := by
  funext x
  change (c • f) (fun i => evI F (x i)) * r x = c • (f (fun i => evI F (x i)) * r x)
  rw [SchwartzMap.smul_apply, smul_mul_assoc]

theorem img (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    om (1, h) (tens (evI F) ⇑f (refFun _)) = tens (evI F) ⇑(archOp om h f) (refFun _) := acts_archOp om h f hx _ (refFun_rest f)

theorem archOp_eq_of_acts (om : Rep σ X W) (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d))
    (hA : Acts (evI F) (om (1, h)) ⇑f ⇑f₁) : archOp om h f = f₁ := by
  apply eq_of_tens
  rw [← img om h f ⟨f₁, hA⟩]
  exact hA _ (refFun_rest f)

end GlobalTheory.ArchLine.Laws

namespace GlobalTheory.ArchLine


open GlobalTheory.ArchLine.Laws in
theorem archOp_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hex
  refine ⟨fun h hh f f' => ?_, fun h hh c f => ?_, fun f => ?_, fun h hh h' hh' f => ?_⟩
  · apply eq_of_tens
    rw [tens_add, ← img om h (f + f') (hex h hh _), ← img om h f (hex h hh f), ← img om h f' (hex h hh f'),
      tens_add, map_add]
  · apply eq_of_tens
    rw [tens_smul, ← img om h (c • f) (hex h hh _), ← img om h f (hex h hh f), tens_smul, map_smul]
  · apply archOp_eq_of_acts
    intro r _
    have e1 : om (1, 1) = 1 := map_one om
    rw [e1]
    rfl
  · have hmul : h * h' ∈ UAt σ W (evI F) := by
      intro u hu
      have e : mat (h * h') - 1 = (mat h - 1) * mat h' + (mat h' - 1) := by
        change mat h * mat h' - 1 = _
        noncomm_ring
      have a1 : u • (mat h - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h - 1) = 0 from hh) u hu
      have a2 : u • (mat h' - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h' - 1) = 0 from hh') u hu
      rw [e, smul_add, ← Matrix.smul_mul, a1, a2, zero_mul, add_zero]
    apply eq_of_tens
    rw [← img om (h * h') f (hex _ hmul f), ← img om h (archOp om h' f) (hex h hh _),
      ← img om h' f (hex h' hh' f)]
    have e2 : ((1 : UA σ X.J), h * h') = (1, h) * (1, h') := by rw [Prod.mk_mul_mk, one_mul]
    rw [e2, map_mul]
    rfl

end GlobalTheory.ArchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEqTranslatedEvaluationCuspFormMap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

theorem conj_row_eq_eval_mult : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hH hιE t c v₀ ht hCL hc hv₀ φ hφ
  have hL := (GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hH).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := _root_.GlobalTheory.ConjRowRepR.exists_contRep_rows hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ
  refine ⟨GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t, Submodule.subset_span
    ⟨_root_.GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep,
     GlobalTheory.T.conjIntertwinerMap_values_isCuspFun hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep,
     _root_.GlobalTheory.ConjRowLevel.conjMap_level hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep, ?_, ?_⟩, ?_⟩
  · intro τ g hg v w hw
    exact _root_.GlobalTheory.ConjEquivReal.conjMap_update_real hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep τ g hg v w hw
  · intro τ v x
    exact _root_.GlobalTheory.ConjRowCont.conjMap_sobCont hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep τ v x
  · have hw : GlobalTheory.ConjRowMult.vecC X (MP R) c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X (MP R) c v₀ X.B.w hv₀
    obtain ⟨ψ, hψ⟩ := hrep v₀
    rw [hw, hΦw] at hψ
    have key : ∀ x, ev (MP R) v₀ (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = star (ψ x) := by
      intro x
      rw [ev_apply]
      apply (GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v₀ _).trans
      rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
      have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
      erw [e, ContinuousMulEquiv.apply_symm_apply]
    filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
    rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.ConjRowMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePartStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateDatumLift_jointEigenspace_into_one_part : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ a : Pl D.host.E → List ℤ → ℂ, ∃ ev, ∀ u : H.H, GlobalTheory.ConjScalar.EigF R i a (H.e u) → th u ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  first | exact @GlobalTheory.ConjScalar.LiftPart.lift_eig_mem_part | exact GlobalTheory.ConjScalar.LiftPart.lift_eig_mem_part | (intros; apply GlobalTheory.ConjScalar.LiftPart.lift_eig_mem_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  first | exact @GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | exact GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | (intros; apply GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefLinks

theorem exists_ioP_of_realDat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hω hv i
  obtain ⟨-, io, hio⟩ := GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R h0 hf hm hω hv
  exact ⟨io i, fun t => hio i t⟩

end GlobalTheory.IndefLinks
end

