module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumIsFockVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOneParamSubgroupGaussVacuumSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

theorem smooth_vacuum_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) → ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := _root_.GlobalTheory.LineGroup.archOp_oneParam B G X om om' hT γ hγ T hTa
  have hU := _root_.GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq B G X om om' hT γ hγ T hTa Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := _root_.GlobalTheory.ArchLineAct.intertwine B G X om om' hT γ hγ T hTa
  have hC := _root_.GlobalTheory.ArchLineCont.continuous_apply B G X om om' hT γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := _root_.GlobalTheory.GaussFockJ.exists_complex_structure B G X om om' hT f₀ hf₀
  haveI : BorelSpace (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, n, qs, qs', cs, c, hd⟩ := _root_.GlobalTheory.WeilVacuum.smooth_flow (V := Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')))
    (_root_.GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ G.M.Pol B.ψ B.emb := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := _root_.GlobalTheory.PolMul.pol_mul_pairInf B G X om om' hT
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.GaussLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory Filter Topology
open scoped SchwartzMap Classical Matrix

noncomputable section

namespace GlobalTheory.ArchLinePair

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ := by
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) κ
  have hΦ₀ : tens (evI F) (⇑f) r₀ ∈ schA F κ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch _ (hpres _ hΦ₀)
  refine ⟨f₁, fun r hr => funext fun y => ?_⟩
  set u : AF F := (0, 1) with hu_def
  have hu : evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have hmul : ∀ a : AF F, u * a = (0, a.2) := fun a => Prod.ext (zero_mul _) (one_mul _)
  set ya : κ → AF F := fun i => ((y i).1, 0) with hya
  have hy : ∀ i, y i = ya i + u * y i := fun i => by
    rw [hmul]
    exact Prod.ext (add_zero _).symm (zero_add _).symm

  have hτx : ∀ (Φ : (κ → AF F) → ℂ) x, schr ψ (u • y, u • (0 : κ → AF F)) Φ x = Φ (x + u • y) := fun Φ x => by
    simp only [schr, smul_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  have step1 : T (tens (evI F) ⇑f r) y = T (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r)) ya := by
    have e : ya + u • y = y := funext fun i => (hy i).symm
    rw [hcomm u hu y 0 _ hr.2, hτx, e]
  have hmemτ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) ∈ schA F κ := by
    have e : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) = fun x => tens (evI F) ⇑f r (x + u • y) :=
      funext fun x => hτx _ x
    rw [e]
    exact GlobalTheory.SchwartzTranslate.schA_translate F (u • y) hr.2
  have hΨ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀ ∈ schA F κ :=
    Submodule.sub_mem _ hmemτ (Submodule.smul_mem _ _ hΦ₀)
  have hvan : ∀ z, At (evI F) z →
      (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀) (ya + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := GlobalTheory.ArchLocality.snd_eq_zero_of_at hz
    have e1 : ya + z + u • y = y + z := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      conv_rhs => rw [hy i]
      abel
    have e2 : (fun i => evI F ((ya + z) i)) = fun i => evI F ((y + z) i) := rfl
    have e3 : r₀ (ya + z) = 1 := hr₀1 _ fun i => by
      show (0 : FiniteAdeleRing (𝓞 F) F) + (z i).2 = 0
      rw [hz2 i, add_zero]
    rw [Pi.sub_apply, Pi.smul_apply, hτx, e1]
    simp only [tens]
    rw [hr.1 y z hz, e2, e3, smul_eq_mul]
    ring
  have hfib := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm _ hΨ ya hvan
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hfib
  have hya' : ya = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) := by
    funext i
    simp only [hya, evI, RingEquiv.symm_apply_apply]
  have hf₁' := hf₁ (fun i => evI F (y i))
  rw [step1, hfib, hya', hf₁']
  simp only [tens]
  ring

private theorem hTens_eq_trace_twisted_operators {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * (JA * y.map c * JBᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem map_mul_lemma_2 {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β γ : Type}
    [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem hTens_actAB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB)
    (x y : Matrix α β E) : hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  obtain ⟨⟨G, hG⟩, ⟨H, hH⟩⟩ := p
  have hG' : (G : Matrix α α E)ᵀ * JA * (G : Matrix α α E).map c = JA := hG
  have hH' : (H : Matrix β β E)ᵀ * JB * (H : Matrix β β E).map c = JB := hH
  have hG2 : ∀ N : Matrix α β E, (G : Matrix α α E)ᵀ * (JA * ((G : Matrix α α E).map c * N)) = JA * N :=
    fun N => by simpa only [Matrix.mul_assoc] using congrArg (· * N) hG'
  have hH2 : ((H : Matrix β β E).map c)ᵀ * (JBᵀ * (H : Matrix β β E)) = JBᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose hH'
  simp only [actAB, hTens_eq_trace_twisted_operators, map_mul_lemma_2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hG2, hH2]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem actAB_smul (p : UA σ X.J × UA σ W.J) (u : AF F) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (u • w) = u • actAB (cA σ) p w := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_add (p : UA σ X.J × UA σ W.J) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (w + w') = actAB (cA σ) p w + actAB (cA σ) p w' := by
  simp only [actAB, Matrix.mul_add, Matrix.add_mul]

theorem actAB_mul (p q : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) (p * q) w = actAB (cA σ) p (actAB (cA σ) q w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actAB_one (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) (1 : UA σ X.J × UA σ W.J) w = w := by
  simp only [actAB, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem actAB_fin {p : UA σ X.J × UA σ W.J} (h1 : p.1 ∈ UAt σ X (evI F)) (h2 : p.2 ∈ UAt σ W (evI F)) (u : AF F)
    (hu : evI F u = 0) (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (u • w) = u • w := by
  have e1 : u • mat p.1 = u • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    have h := h1 u hu
    rwa [smul_sub, sub_eq_zero] at h
  have e2 : u • mat p.2 = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    have h := h2 u hu
    rwa [smul_sub, sub_eq_zero] at h
  simp only [mat] at e1 e2
  simp only [actAB]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul,
    ← Matrix.transpose_smul, e2, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]

def amap (M : Model σ X W) (p : UA σ X.J × UA σ W.J) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (actAB (cA σ) p (GlobalTheory.ArchFam.wv M v))
  map_add' v v' := by
    simp only [GlobalTheory.ArchFam.wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add (f := _), actAB_add,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [GlobalTheory.ArchFam.wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, actAB_smul,
      Coord.coordI_smul, RingHom.id_apply]

theorem amap_coordI (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    amap M p (Coord.coordI M w) = Coord.coordI M (actAB (cA σ) p w) := by
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.ArchFam.wv]
  rw [Coord.lift_coordI, actAB_smul, Coord.coordI_one]

theorem continuous_amap (M : Model σ X W) (v) : Continuous fun p : UA σ X.J × UA σ W.J => amap M p v := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    (inferInstance : IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hev : Continuous (evI F) := by
    show Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
        ((continuous_apply _).comp continuous_fst)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
        ((continuous_apply _).comp continuous_fst)
  have hloc : Continuous fun x : Fin n × Fin d → AF F => locV x :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have he : Continuous fun u : Matrix (Fin n) (Fin d) (AE F E) => M.co.e u :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hg : Continuous fun p : UA σ X.J × UA σ W.J => ((p.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
  have hh : Continuous fun p : UA σ X.J × UA σ W.J => ((p.2 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  have hact : Continuous fun p : UA σ X.J × UA σ W.J => actAB (cA σ) p (GlobalTheory.ArchFam.wv M v) :=
    (hg.matrix_mul continuous_const).matrix_mul hh.matrix_transpose
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, Coord.coordI]
  exact (hloc.comp (continuous_fst.comp (he.comp hact))).prodMk (hloc.comp (continuous_snd.comp (he.comp hact)))

end GlobalTheory.ArchLinePair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer

theorem schwartz_diffQuotient_eval_mul_eq_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (s : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (y : κ → mixedEmbedding.mixedSpace F) (R : ℂ) (t : ℝ) :
    (t⁻¹ • (s t - s 0)) y * R = slope (fun t => s t y * R) 0 t := by
  simp only [slope_def_module, sub_zero, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_mul_assoc, sub_mul]

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {m : ℕ}
    (Φ : Fin m → (Fin n × Fin d → AF F) → ℂ) (hΦ : ∀ i, Φ i ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, Φ i)) = ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (Φ i)) := by
  have hsum : M.co.rho ψ u (∑ i, Φ i) = ∑ i, M.co.rho ψ u (Φ i) := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]
  have hmem : ∀ i, M.co.rho ψ u (Φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i => GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u (Φ i) (hΦ i)
  rw [hsum]
  have key := map_sum (GlobalTheory.WeilM.thetaLin F (Fin n × Fin d))
    (fun i => (⟨M.co.rho ψ u (Φ i), hmem i⟩ : GlobalTheory.WeilM.schA F (Fin n × Fin d))) Finset.univ
  simpa only [GlobalTheory.WeilM.thetaLin_apply, Submodule.coe_sum] using key

end GlobalTheory.ThetaLineDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorOneParamGaussianVacuumSmoothPair
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussLinePair

theorem smooth_vacuum_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ f₀, M.IsGauss ψ τ f₀ →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := _root_.GlobalTheory.LineGroupPair.archOp_oneParam_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hU := _root_.GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa MeasureTheory.Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := _root_.GlobalTheory.ArchLineAct.intertwine_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hC := _root_.GlobalTheory.ArchLineContPair.continuous_apply F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := _root_.GlobalTheory.FockPair.exists_fock_cx F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW f₀ hf₀
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, k, qs, qs', cs, c, hd⟩ := _root_.GlobalTheory.WeilVacuum.smooth_flow (V := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    MeasureTheory.Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ M.Pol ψ τ := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := _root_.GlobalTheory.PolMul.pol_mul_pairInf_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.GaussLinePair

end
end

