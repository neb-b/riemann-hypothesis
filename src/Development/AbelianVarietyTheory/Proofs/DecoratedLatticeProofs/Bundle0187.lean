module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLattice
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_toCompl_tmul_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (b : Fv D.host.F v) (o m : D.host.E) :
    secW hw h (toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m) =
      pairA D.host.F 0 (singleFin v b) ⊗ₜ[D.host.F] (o * m) := by
  have e : toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m =
      toCompl h (b ⊗ₜ[D.host.F] (o * m)) := by
    rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
  have e2 : toCompl h (b ⊗ₜ[D.host.F] (o * m)) = GlobalTheory.LFun.InertChart.complEquiv hw h (b ⊗ₜ[D.host.F] (o * m)) := rfl
  rw [e, e2]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) = _
  rw [RingEquiv.symm_apply_apply, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]

theorem secW_rank_one_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ frameLat S)
    {t : Fin T.rank → D.host.E} (ht : t ∈ frameLat T) {z : w.adicCompletion D.host.E} (hz : z ∈ Ov D.host.E w) :
    (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E)
      (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  obtain ⟨y, rfl⟩ := GlobalTheory.LFun.InertChart.toCompl_surjective h z
  have hy := (GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h y).2 hz
  refine intLoc_induction (p := fun y => (Matrix.of fun i j => secW hw h (toCompl h y *
      algebraMap D.host.E (w.adicCompletion D.host.E) (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v)) (fun b hb o => ?_) ?_ (fun y y' h1 h2 => ?_)
      (fun y h1 => ?_) hy
  · refine AddSubgroup.subset_closure ⟨singleFin v b, fun u => ?_, fun u hu => evalV_singleFin_ne hu _, a, ha, s, hs,
      o • t, Submodule.smul_mem _ o ht, ?_⟩
    · by_cases e : u = v
      · subst e; rw [evalV_singleFin_self]; exact hb
      · rw [evalV_singleFin_ne e]; exact zero_mem _
    · ext i j
      rw [Matrix.of_apply, Matrix.of_apply, secW_toCompl_tmul_mul]
      congr 1
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  · convert add_mem h1 h2 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, map_add (f := _), add_mul]
  · convert neg_mem h1 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, map_neg, neg_mul]

theorem secW_span_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : IsConjAt D.sp.cm.sig h c) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {p : Fin T.rank → w.adicCompletion D.host.E} (hp : p ∈ latAt w (frameLat T))
    {y : Fin S.rank → w.adicCompletion D.host.E} (hy : y ∈ latAt w (frameLat S)) :
    ∀ z ∈ Ov D.host.E w, (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E) a * p i *
      ∑ k, c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  have hst : ∀ x : D.host.E, star x = D.sp.cm.sig x := fun _ => rfl
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t, ht, rfl⟩ := hp
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      intro z hz
      convert secW_rank_one_mem hw h ha hs ht hz using 1
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.of_apply, GlobalTheory.LFun.InertChart.conj_algebraMap hc, map_mul, map_sum, hst]
      ring_nf
    | zero =>
      intro z hz
      convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
      ext i j
      simp
    | add y y' _ _ h1 h2 =>
      intro z hz
      convert add_mem (h1 z hz) (h2 z hz) using 1
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]
    | smul o y _ h1 =>
      intro z hz
      convert h1 (z * c o) (mul_mem hz (GlobalTheory.LFun.InertChart.conj_mem hw hc o.2)) using 1
      ext i j
      have e : ∀ k, c ((o • y) k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j) =
          c o * (c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) := fun k => by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, mul_assoc]
      simp only [Matrix.of_apply, e, ← Finset.mul_sum]
      congr 1
      ring
  | zero =>
    intro z hz
    convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  | add p p' _ _ h1 h2 =>
    intro z hz
    convert add_mem (h1 z hz) (h2 z hz) using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, mul_add]
  | smul o p _ h1 =>
    intro z hz
    convert h1 (z * o) (mul_mem hz o.2) using 1
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    congr 1
    ring

theorem uPt_mem_latO : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  intro D v w hw h S T k aS aT hk haS haT x hx
  obtain ⟨-, ⟨a₀, ha₀, rfl⟩, -⟩ := hk
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt D.sp.cm.sig hw h
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt_host D) hw hc
  have hcc : ∀ z, c (c z) = z := hU.1
  set ι := algebraMap D.host.E (w.adicCompletion D.host.E) with hι
  set Gw := S.gram.map ι with hGw
  set Gi := (S.gram⁻¹).map ι with hGi
  have hGG : Gi * Gw = 1 := by
    rw [hGi, hGw, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  set N := (aS⁻¹).1 * Gi with hN
  have hG : ∀ l i, c (ι (S.gram l i)) = ι (S.gram i l) := fun l i => by
    rw [GlobalTheory.LFun.InertChart.conj_algebraMap hc, (GlobalTheory.Doubling.isHermND_gram S).1 i l]
  have hY : ∀ j, (fun l => c (N j l)) ∈ latAt w (frameLat S) := by
    intro j
    rw [GlobalTheory.LFun.InertChart.mem_latAt_iff hw hc (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D S v)]
    intro y hy
    have hu := (haS ((aS⁻¹).1 *ᵥ y)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) j
    have e : Formalism.UG.hform c (S.gram.map ι) y (fun l => c (N j l)) = c ((N *ᵥ (Gw *ᵥ y)) j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hG, hGw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, hGG, Matrix.mul_one]
    exact GlobalTheory.LFun.InertChart.conj_mem hw hc hu
  have hcol : ∀ j l, ∑ m, c (c (N j m)) * ι (S.gram m l) = (aS⁻¹).1 j l := fun j l => by
    simp only [hcc]
    have := congrFun (congrFun (show N * Gw = (aS⁻¹).1 by rw [hN, Matrix.mul_assoc, hGG, Matrix.mul_one]) j) l
    rw [← this, Matrix.mul_apply]
    rfl
  have hT : ∀ i, (fun r => aT.1 r i) ∈ latAt w (frameLat T) := fun i => by
    have := (haT (Pi.single i 1)).1 fun m => by
      by_cases e : m = i
      · subst e; simp
      · simp [e]
    convert this using 1
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdec : uPt hw h (ι a₀) aS aT x = ∑ i, ∑ j, (Matrix.of fun r l => secW hw h (x i j * ι a₀ * aT.1 r i *
      ∑ m, c (c (N j m)) * ι (S.gram m l)) : WO S T) := by
    ext r l
    simp only [uPt, Matrix.map_apply, Matrix.sum_apply, Matrix.of_apply, hcol]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ∀ f : Fin T.rank → Fin S.rank → w.adicCompletion D.host.E, ∑ i, ∑ j, secW hw h (f i j) =
        secW hw h (∑ i, ∑ j, f i j) from fun f => by simp only [map_sum]]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdec]
  exact sum_mem fun i _ => sum_mem fun j _ => secW_span_mem hw h hc ha₀ (hT i) (hY j) (x i j) (hx i j)

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
section
noncomputable section

namespace GlobalTheory.Core.Rk.RapidInt

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont GlobalTheory.GaugeEx
open NumberField.mixedEmbedding
open scoped Classical

section Mixed

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

end Mixed

section Tup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (M n : ℕ)

def crdTup : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin n → Fin M → Fin d → Ainf F) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ =>
    (Algebra.TensorProduct.basis (Ainf F) b).equivFun

def mixTup : (Fin n → Fin M → Fin d → Ainf F) ≃+ (Fin n → Fin M → Fin d → mixedSpace F) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

theorem continuous_crdTup : Continuous (crdTup F E b M n) :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).toLinearMap

theorem continuous_crdTup_symm : Continuous (crdTup F E b M n).symm :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).symm.toLinearMap

theorem continuous_mixTup : Continuous (mixTup F M n (d := d)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_toMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem continuous_mixTup_symm : Continuous (mixTup F M n (d := d)).symm :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_ofMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

def tupEquiv : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin n → Fin M → Fin d → mixedSpace F) where
  toAddEquiv := (crdTup F E b M n).toAddEquiv.trans (mixTup F M n)
  continuous_toFun := (continuous_mixTup F M n).comp (continuous_crdTup F E b M n)
  continuous_invFun := (continuous_crdTup_symm F E b M n).comp (continuous_mixTup_symm F M n)


end Tup


end GlobalTheory.Core.Rk.RapidInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubini
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Core.Rk.FubiniPlace


set_option maxHeartbeats 1000000 in
theorem integral_split_place : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  intro D A m hm v μ hμ J hJo hJ1 E hE hEr F ζ hζ hζJ hF hFi
  have hec : Continuous (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_emb _ _ v
  have hpc : Continuous (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_proj _ _ v
  have hPm : MeasurableSet {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J} := (hJo.preimage hpc).measurableSet
  have hUm : MeasurableSet (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) := hE.inter hPm
  have hJm : MeasurableSet (J : Set (GlobalTheory.FinZeta.Gv A v)) := hJo.measurableSet

  have hright : ∀ k ∈ J, μ.map (fun y => y * k) = μ := by
    intro k hk
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
    have h2 := congrArg (fun m' : Measure (GlobalTheory.FinZeta.Gv A v) => m' (J : Set (GlobalTheory.FinZeta.Gv A v))) h
    simp only [Measure.coe_nnreal_smul_apply] at h2
    rw [Measure.map_apply (measurable_mul_const _) hJm,
      show (fun x => x * k) ⁻¹' (J : Set (GlobalTheory.FinZeta.Gv A v)) = J from Set.ext fun x => J.mul_mem_cancel_right hk,
      hJ1, mul_one] at h2
    have h3 : Measure.modularCharacterFun k = 1 := by exact_mod_cast h2.symm
    rw [h, h3, one_smul]

  have dec : ∀ x : GA D A, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) = 1 := by
    intro x; rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have dec2 : ∀ x : GA D A, x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x; rw [map_inv, inv_mul_cancel_right]
  have shift : ∀ (x : GA D A) (y : GlobalTheory.FinZeta.Gv A v),
      GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x y
    have hc := (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig A.gram y (dec x)).eq
    calc GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
          rw [mul_assoc, ← dec2]
      _ = _ := by rw [hc, mul_assoc, ← map_mul]
  have hEl : ∀ (y : GlobalTheory.FinZeta.Gv A v) (x : GA D A), GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x ∈ E ↔ x ∈ E := by
    intro y x
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    rw [shift, hEr, h1]
  have key : ∀ x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}), ∀ y, F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x) = F x * ζ (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x hx y
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    have hx' : x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ ∈ E := h1.1 hx.1
    have h2 := hF _ hx' (dec x) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h2
    rw [shift, hF _ hx' (dec x), h2, hζJ _ hx.2, one_mul, mul_comm]
  classical

  let c : GA D A → GlobalTheory.FinZeta.Gv A v := fun x => if GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J then GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x else 1
  have hcm : Measurable c := Measurable.ite hPm hpc.measurable measurable_const
  have hR : MeasurePreserving (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) (m.prod μ) (m.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun x y => y * c x) (MeasurePreserving.id m)
      (measurable_snd.mul (hcm.comp measurable_fst) : Measurable fun p : GA D A × GlobalTheory.FinZeta.Gv A v => p.2 * c p.1)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · simp only [c, if_pos hx]; exact hright _ hx
    · simp only [c, if_neg hx, mul_one, Measure.map_id']
  let g0 : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F q.1 * ζ q.2
  have hg0 : Integrable g0 (m.prod μ) := Integrable.mul_prod ((integrable_indicator_iff hUm).2 hFi) hζ
  let f : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * x)) q.1
  have hfg : f = g0 ∘ (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) := by
    funext q
    by_cases hx : q.1 ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J})
    · have hx2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1 ∈ J := hx.2
      simp only [f, g0, Function.comp_apply, c, if_pos hx2]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, key q.1 hx]
    · simp only [f, g0, Function.comp_apply, Set.indicator_of_notMem hx, zero_mul]
  have hf : Integrable f (m.prod μ) := by
    rw [hfg]; exact (hR.integrable_comp hg0.aestronglyMeasurable).2 hg0
  have hfint : ∫ q, f q ∂(m.prod μ) = ∫ q, g0 q ∂(m.prod μ) := by
    have h := integral_map (μ := m.prod μ) hR.measurable.aemeasurable (f := g0)
      (by rw [hR.map_eq]; exact hg0.aestronglyMeasurable)
    rw [hR.map_eq] at h
    rw [hfg]; exact h.symm

  let T : GA D A × GlobalTheory.FinZeta.Gv A v → GA D A × GlobalTheory.FinZeta.Gv A v := fun q => (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * q.1, q.2)
  have hTp : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2)) (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × GlobalTheory.FinZeta.Gv A v → GlobalTheory.FinZeta.Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : GlobalTheory.FinZeta.Gv A v × GA D A → GA D A × GlobalTheory.FinZeta.Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  let Te : (GA D A × GlobalTheory.FinZeta.Gv A v) ≃ᵐ (GA D A × GlobalTheory.FinZeta.Gv A v) :=
    { toFun := T
      invFun := fun q => ((GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2)⁻¹ * q.1, q.2)
      left_inv := fun q => by simp [T]
      right_inv := fun q => by simp [T]
      measurable_toFun := (((hec.comp continuous_snd).mul continuous_fst).prodMk continuous_snd).measurable
      measurable_invFun := ((((hec.comp continuous_snd).inv).mul continuous_fst).prodMk continuous_snd).measurable }
  have hT : MeasurePreserving Te (m.prod μ) (m.prod μ) := hTp
  let f₂ : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ :=
    fun q => {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) q
  have hf₂T : ∀ q, f₂ (Te q) = f q := by
    rintro ⟨x, y⟩
    have hp : (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y = (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) =
      (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x)) x
    by_cases h2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∈ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp]; exact J.inv_mem h2
      rw [Set.indicator_of_mem hq]
      by_cases h1 : x ∈ E
      · rw [Set.indicator_of_mem ((hEl y x).2 h1), Set.indicator_of_mem (show x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) from ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (hEl y x).1 h1), Set.indicator_of_notMem (by exact fun h => h1 h.1)]
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∉ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show ¬ (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp, inv_mem_iff]; exact h2
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (by exact fun h => h2 h.2)]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (hT.integrable_comp_emb Te.measurableEmbedding).1 ?_
    have : f₂ ∘ Te = f := funext hf₂T
    rw [this]; exact hf
  have hCm : ∀ a : GlobalTheory.FinZeta.Gv A v, MeasurableSet {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} :=
    fun a => (hJo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : GlobalTheory.FinZeta.Gv A v, μ {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} = 1 := by
    intro a
    rw [← hJ1]
    exact measure_preimage_mul μ a⁻¹ _
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = E.indicator F w := by
    intro w
    have : (fun y => f₂ (w, y)) = {y : GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ J}.indicator (fun _ => E.indicator F w) := by
      funext y; rfl
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hFE : Integrable (E.indicator F) m := by
    have h := hf₂.integral_prod_left
    simp_rw [inner] at h
    exact h
  refine ⟨(integrable_indicator_iff hE).1 hFE, ?_⟩
  calc ∫ g in E, F g ∂m = ∫ w, E.indicator F w ∂m := (integral_indicator hE).symm
    _ = ∫ q, f₂ q ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ q, f₂ (Te q) ∂(m.prod μ) := (hT.integral_comp' f₂).symm
    _ = ∫ q, f q ∂(m.prod μ) := by simp_rw [hf₂T]
    _ = ∫ q, g0 q ∂(m.prod μ) := hfint
    _ = (∫ x, (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F x ∂m) * ∫ y, ζ y ∂μ := integral_prod_mul _ _
    _ = _ := by rw [integral_indicator hUm, mul_comm]

end GlobalTheory.Core.Rk.FubiniPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_isotropic_stabiliser_split_place : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  first | exact @GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_stab_split | exact GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_stab_split | (intros; apply GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_stab_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpannedBySatakeEigenElements
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem eigSpan_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  intro hC D hF _ hL c hc j hj s hs
  have hspan := _root_.GlobalTheory.OntoDecomp.multT_span_partFull hC D hF hL c hc j hj s hs
  have hpar := _root_.GlobalTheory.ChainOnto.partPar hC D c hc j hj s hs
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro u ⟨e, he⟩
  by_cases h0 : u = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact Submodule.subset_span ((hpar u e he).1 h0)

end GlobalTheory.ChainOnto
end

