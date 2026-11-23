module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0036
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaLiftLinearInSchwartz
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
namespace UpperTheory.TP.LiftLin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
theorem integrand_int_k (T : _root_.UpperTheory.TP.Tools_k) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) {φ : UA σ X.J → ℂ} (hφ : IsFn φ)
    (h : UA σ W.J) : IntegrableOn (fun g => theta om Φ g h * star (φ g)) M.dom M.μ := by
  have hc : Cpt σ X.J := T.cpt F E σ B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  have ht := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hP).1 Φ hΦ
  obtain ⟨h1, h2, -⟩ := ht
  have hcont : Continuous fun g => theta om Φ g h * star (φ g) :=
    (h1.comp (continuous_id.prodMk continuous_const)).mul (continuous_star.comp hφ.1)
  obtain ⟨C, hC⟩ := hc.bdd hcont fun γ hγ g => by
    have e := h2 γ hγ 1 (one_mem _) g h
    rw [one_mul] at e
    simp only [e, hφ.2 γ hγ g]
  exact Measure.integrableOn_of_bounded (M := C) (hc.fin M.μ M.dom hP.good.haar hP.good.dom).ne
    hcont.aestronglyMeasurable (Eventually.of_forall hC)
end UpperTheory.TP.LiftLin
open UpperTheory.TP.LiftLin in
theorem UpperTheory.thetaLift_linear_in_schwartz :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → (∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (Φ + Φ') φ = lift M om Φ φ + lift M om Φ' φ) ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (c • Φ) φ = c • lift M om Φ φ) ∧ (∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ φ' : UA σ X.J → ℂ, IsFn φ → IsFn φ' → lift M om Φ (φ + φ') = lift M om Φ φ + lift M om Φ φ') ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om Φ (c • φ) = (starRingEnd ℂ) c • lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  refine ⟨fun Φ hΦ Φ' hΦ' φ hφ => ?_, fun c Φ hΦ φ hφ => ?_, fun Φ hΦ φ φ' hφ hφ' => ?_, fun c Φ hΦ φ hφ => ?_⟩
  · funext h
    have e : ∀ g, theta om (Φ + Φ') g h * star (φ g) = theta om Φ g h * star (φ g) + theta om Φ' g h * star (φ g) := fun g => by
      have : theta om (Φ + Φ') g h = theta om Φ g h + theta om Φ' g h := by
        simp only [theta, map_add (f := _)]
        exact thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΦ')
      rw [this, add_mul]
    simp only [lift, Pi.add_apply, e]
    exact integral_add (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ hφ h) (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ' hφ h)
  · funext h
    have e : ∀ g, theta om (c • Φ) g h * star (φ g) = c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [theta, map_smul, thetaSum_smul, mul_assoc]
    simp only [lift, Pi.smul_apply, smul_eq_mul, e, integral_const_mul]
  · funext h
    have e : ∀ g, theta om Φ g h * star ((φ + φ') g) = theta om Φ g h * star (φ g) + theta om Φ g h * star (φ' g) := fun g => by
      simp only [Pi.add_apply, star_add, mul_add]
    simp only [lift, Pi.add_apply] at e ⊢
    simp only [e]
    exact integral_add (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ hφ h) (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ hφ' h)
  · funext h
    have e : ∀ g, theta om Φ g h * star ((c • φ) g) = (starRingEnd ℂ) c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring
    simp only [lift, Pi.smul_apply, smul_eq_mul] at e ⊢
    simp only [e, integral_const_mul]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaLiftWeilTranslateEquivariant
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.thetaLift_weil_translate_equivariant :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → ∀ (a : UA σ X.J) (b h : UA σ W.J), lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = lift M om Φ φ (h * b) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ a b h
  have c : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have hTB := T.basic F E σ B n d X W M χX χW om n 0 d 0 hp
  let G : UA σ X.J → ℂ := fun x => theta om Φ x (h * b) * star (φ x)
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    have h1 := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (h * b)
    rw [one_mul] at h1
    simp only [G]
    rw [h1, hφ.2 γ hγ x]
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := c.right _ hp.good.haar
  haveI := c.cnt
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = ∫ x in M.dom, G (x * a) ∂M.μ := by
    unfold lift
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [G, theta]
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ a
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight a) G
    ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * a) ⁻¹' ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ a⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * a⁻¹ = γ.1 * (x * a⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd.setIntegral_eq hp.good.dom (f := G) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def unipotentNilpotentPart {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := ((L.rng (L.em j)).2 ⟨j, rfl⟩)
theorem unipotent_nilpotent_mul_eq_zero {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L v = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L _
theorem continuous_unipotent_nilpotent {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have : (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact (continuous_apply j).smul continuous_const
def muF_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) 0 0 (((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ))
def muF'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) 0 0 (((1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ))
theorem one_add_mul_one_sub_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) :
    (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) * (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero, add_zero, add_sub_cancel_right]
theorem muF_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k L u = 1 := by
  have e1 := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.one_add_mul_one_sub_k L u
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]
theorem inFrame_uM_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) 0 0 a' at ha
  have hf := kunf.frame_eq hε (uM u)
  rw [ha] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.one_add_mul_one_sub_k, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  have e3 : a' = ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ) := by
    rw [← e2]
    ext i j
    simp [Matrix.map_apply, kfour.cA_cA' σ hσ]
  rw [ha, e3]
  rfl
theorem continuous_uM_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const
      (hcA.comp (continuous_const.sub hN).matrix_transpose)
  have hc' : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const
      (hcA.comp (continuous_const.add hN).matrix_transpose)
  have h1 : Continuous fun u => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun u => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun u => ?_
    show _ = mat2 (uM u)
    rw [kunf.matrix_eq_inFrame_conj d.b, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L h]
  · refine h2.congr fun u => ?_
    show _ = mat2 (uM u)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L h,
      Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_mul_k L u)]
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilPairGlobalCharacter
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.weil_pair_global_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  first | exact @_root_.PositivityTheory.ThKW.weil_pair_global_character_lift | exact _root_.PositivityTheory.ThKW.weil_pair_global_character_lift | (intros; apply _root_.PositivityTheory.ThKW.weil_pair_global_character_lift <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepMemPolynomialFockOfFinitePlace
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.weilRep_mem_polynomialFock_of_finite_place :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v g hg h hh Φ hΦ
  classical
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, hf, φ, hSB, hcof, rfl⟩
  obtain ⟨φ₁, ⟨s1, a1⟩, -⟩ := (T.acts F E σ B n d X W M χX χW om r s r' s' hp v).1 g hg h hh (φ v) (hSB v)
  have e := (PositivityTheory.ThKF.pureAct F _ v (om (g, h)) f φ hSB
    ((hcof.and hp.good.std).mono fun _ k => k.1.trans k.2)).2.2 φ₁ a1
  refine e ▸ Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun u => ?_, ?_, ?_⟩
  · by_cases hu : u = v
    · subst hu; simpa using s1
    · simpa [Function.update_of_ne hu] using hSB u
  · have : ∀ᶠ u in cofinite, u ≠ v := (Set.finite_singleton v).compl_mem_cofinite
    exact (hcof.and this).mono fun u k => by rw [Function.update_of_ne k.2, k.1]
  · congr!
end
end

