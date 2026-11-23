module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import GroundTheory.GlobalFields.TateThesis.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.BMat
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

def eA : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)

def elt (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1

def uA (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)

def uMat (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (uA L u) 0 0 ((uA L (-u))ᵀ.map (cA σ))

def bMat (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 β 0 1

def sB (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(eA R * cA σ (b j))))

def aB (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E := E) (AF F) δ)

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def nilpotentFrameMatrix {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne {d : SD σ} (L : LD d) (j : Fin L.n) : L.em j ≠ L.i₀ := ((L.rng (L.em j)).2 ⟨j, rfl⟩)

theorem nilpotent_frame_mul_zero {d : SD σ} (L : LD d) (u v : Fin L.n → AE F E) : nilpotentFrameMatrix L u * nilpotentFrameMatrix L v = 0 := by
  simp only [nilpotentFrameMatrix, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  exact em_ne L _

theorem continuous_nilpotentFramePart {d : SD σ} (L : LD d) : Continuous (nilpotentFrameMatrix L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have : (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact (continuous_apply j).smul continuous_const

def muF {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 (((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ))

def muF' {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 - nilpotentFrameMatrix L u) 0 0 (((1 + nilpotentFrameMatrix L u)ᵀ).map (cA σ))

theorem one_add_mul_one_sub {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) :
    (1 + nilpotentFrameMatrix L u) * (1 - nilpotentFrameMatrix L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, nilpotent_frame_mul_zero, add_zero, add_sub_cancel_right]

theorem muF_mul {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : muF L u * muF' L u = 1 := by
  have e1 := one_add_mul_one_sub L u
  simp only [muF, muF', Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]

theorem inFrame_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = muF L u := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 a' at ha
  have hf := kunf.frame_eq hε (uM u)
  rw [ha] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - nilpotentFrameMatrix L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - nilpotentFrameMatrix L u)ᵀ * (1 + nilpotentFrameMatrix L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, one_add_mul_one_sub, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - nilpotentFrameMatrix L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  have e3 : a' = ((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ) := by
    rw [← e2]
    ext i j
    simp [Matrix.map_apply, kfour.cA_cA' σ hσ]
  rw [ha, e3]
  rfl

theorem continuous_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := continuous_nilpotentFramePart L
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hc : Continuous (muF (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const
      (hcA.comp (continuous_const.sub hN).matrix_transpose)
  have hc' : Continuous (muF' (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const
      (hcA.comp (continuous_const.add hN).matrix_transpose)
  have h1 : Continuous fun u => incM F d.b.1 * muF L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun u => incM F d.b.1 * muF' L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun u => ?_
    show _ = mat2 (uM u)
    rw [kunf.matrix_eq_inFrame_conj d.b, inFrame_uM L h]
  · refine h2.congr fun u => ?_
    show _ = mat2 (uM u)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, inFrame_uM L h,
      Matrix.inv_eq_right_inv (muF_mul L u)]

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := h.2.1.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hc
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (w.embedding x) = w.embedding x
  rw [← h.2.2.2 w.embedding, hne]

theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := exists_sigma_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sigma_sigma_cm h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst
section
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adeleHaarB {m : MeasurableSpace (AF F)} (hB : @BorelSpace (AF F) _ m) :
    ∃ μ : @Measure (AF F) m, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ ∀ r : GroundTheory.Global.IdeleGroup F,
      μ.map (fun y => (r : AF F) * y) =
        (((((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal : NNReal) : ENNReal) • μ := by
  have h1 : m = GroundTheory.Global.measurableSpace_adeleRing F :=
    hB.measurable_eq.trans (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  subst h1
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GroundTheory.Global.instIsAddHaarMeasureAdeleRingRingOfIntegersAdeleMeasure F
  refine ⟨GroundTheory.Global.adeleMeasure F, inferInstance, inferInstance, fun r => ?_⟩
  exact GroundTheory.Global.map_smul_adeleMeasure r

theorem pi_map_const {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → X) (hf : Measurable f)
    (c : NNReal) (hμ : μ.map f = (c : ENNReal) • μ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Measure.pi fun _ : ι => μ).map (fun y i => f (y i)) = ((c : ENNReal) ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  haveI : SigmaFinite (μ.map f) := by
    rw [hμ]
    exact (inferInstance : SigmaFinite (c • μ))
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hμ]
  haveI : SigmaFinite ((c : ENNReal) • μ) := (inferInstance : SigmaFinite (c • μ))
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem measN (n k : ℕ) (bs : Module.Basis (Fin n) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (n * k + 2)) • κ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI hBA : BorelSpace (AF F) := ⟨rfl⟩
  haveI hBE : BorelSpace (AE F E) := ⟨rfl⟩
  obtain ⟨ν, hνH, hνS, hν⟩ := adeleHaarB (F := F) hBA
  let ψ := (Algebra.TensorProduct.basis (AF F) bs).equivFun
  have hψ : Continuous ψ :=
    IsModuleTopology.continuous_of_linearMap (ψ : AE F E →ₗ[AF F] (Fin n → AF F))
  have hψs : Continuous ψ.symm :=
    IsModuleTopology.continuous_of_linearMap (ψ.symm : (Fin n → AF F) →ₗ[AF F] AE F E)
  let e : ((Fin k → Fin n → AF F) × AF F) ≃+ ((Fin k → AE F E) × AF F) :=
    AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ψ.symm.toAddEquiv) (AddEquiv.refl _)
  have he : Continuous e := by
    change Continuous fun p : (Fin k → Fin n → AF F) × AF F => ((fun j => ψ.symm (p.1 j)), p.2)
    exact (continuous_pi fun j => hψs.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  have hes : Continuous e.symm := by
    change Continuous fun p : (Fin k → AE F E) × AF F => ((fun j => ψ (p.1 j)), p.2)
    exact (continuous_pi fun j => hψ.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  let μW : Measure (Fin k → Fin n → AF F) := Measure.pi fun _ => Measure.pi fun _ => ν
  refine ⟨(μW.prod ν).map e, e.isAddHaarMeasure_map _ he hes, fun r => ?_⟩
  set a : AF F := (r : AF F) with ha
  set b : AF F := ((r⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) with hb
  have hab : b * a = 1 := r.inv_mul
  have hba : a * b = 1 := r.mul_inv
  let S : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => a • c.1 j, (a * a) • c.2)
  let S' : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => b • c.1 j, (b * b) • c.2)
  have hS : Continuous S :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul a).prodMk
      (continuous_snd.const_smul (a * a))
  have hS' : Continuous S' :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul b).prodMk
      (continuous_snd.const_smul (b * b))
  let sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F) :=
    { toFun := S
      invFun := S'
      left_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show b • a • c.1 j = c.1 j
          rw [smul_smul, hab, one_smul]
        · show (b * b) • (a * a) • c.2 = c.2
          rw [smul_smul, show b * b * (a * a) = (b * a) * (b * a) by ring, hab, one_mul, one_smul]
      right_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show a • b • c.1 j = c.1 j
          rw [smul_smul, hba, one_smul]
        · show (a * a) • (b * b) • c.2 = c.2
          rw [smul_smul, show a * a * (b * b) = (a * b) * (a * b) by ring, hba, one_mul, one_smul]
      measurable_toFun := hS.measurable
      measurable_invFun := hS'.measurable }
  refine ⟨sc, fun c => rfl, ?_⟩
  let T1 : (Fin k → Fin n → AF F) → (Fin k → Fin n → AF F) := fun w j i => a * w j i
  let T2 : AF F → AF F := fun t => (a * a) * t
  have hT1 : Continuous T1 := continuous_pi fun j => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply j))
  have hT2 : Continuous T2 := continuous_const.mul continuous_id
  have hcomm : (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) ∘ e = e ∘ Prod.map T1 T2 := by
    funext p
    refine Prod.ext (funext fun j => ?_) rfl
    show a • ψ.symm (p.1 j) = ψ.symm (fun i => a * p.1 j i)
    rw [← map_smul]
    rfl
  set c : NNReal := (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal with hc
  have h1 : ν.map (fun y => a * y) = (c : ENNReal) • ν := hν r
  have hm1 : Measurable fun y : AF F => a * y := (continuous_const.mul continuous_id).measurable
  have hin : (Measure.pi fun _ : Fin n => ν).map (fun y i => a * y i) =
      ((c ^ n : NNReal) : ENNReal) • Measure.pi fun _ : Fin n => ν := by
    rw [pi_map_const ν (fun y => a * y) hm1 c h1 (Fin n), Fintype.card_fin, ENNReal.coe_pow]
  have hW : μW.map T1 = ((c : ENNReal) ^ n) ^ k • μW := by
    have hm2 : Measurable fun y : Fin n → AF F => fun i => a * y i :=
      (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
    have := pi_map_const (Measure.pi fun _ : Fin n => ν) (fun y i => a * y i) hm2 (c ^ n) hin (Fin k)
    rw [Fintype.card_fin, ENNReal.coe_pow] at this
    exact this
  have hA : ν.map T2 = (c : ENNReal) ^ 2 • ν := by
    have : T2 = (fun y => a * y) ∘ (fun y => a * y) := by
      funext t
      simp [T2, mul_assoc]
    rw [this, ← Measure.map_map hm1 hm1, h1, Measure.map_smul, h1, smul_smul, sq]
    exact hm1.aemeasurable
  rw [show ((μW.prod ν).map e).map sc = ((μW.prod ν).map e).map (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) from rfl,
    Measure.map_map sc.measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (hT1.measurable.prodMap hT2.measurable),
    ← Measure.map_prod_map μW ν hT1.measurable hT2.measurable, hW, hA,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul] <;>
    try exact he.measurable.aemeasurable
  congr 1
  have hx : (0 : ℝ) ≤ ((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule F r).2)
  rw [ENNReal.ofReal_pow hx, ← pow_mul, ← pow_add]
  rfl

theorem measEx' (k : ℕ) (bs : Module.Basis (Fin 2) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (2 * k + 2)) • κ :=
  measN 2 k bs

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ptEx' (d : SD σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  have hone : incM F (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hPQ : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.mul_inv, hone]
  have hQP : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.inv_mul, hone]
  have hM'M : ∀ c, M' c * M c = 1 := fun c => by
    first
    | exact mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_symm (h c)
  let N : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M c * incM F (d.b⁻¹).1
  let N' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M' c * incM F (d.b⁻¹).1
  have hNN' : ∀ c, N c * N' c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M c) (M' c), h c, Matrix.one_mul, hPQ]
  have hN'N : ∀ c, N' c * N c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M' c) (M c), hM'M c, Matrix.one_mul, hPQ]
  let u : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨N c, N' c, hNN' c, hN'N c⟩
  have mem : ∀ c, u c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε (M c) (M' c) (h c) (hu c)
    have hx' : x.1.1 = N c := by
      show x.1.1 = incM F d.b.1 * M c * incM F (d.b⁻¹).1
      rw [← hx]
      show x.1.1 = incM F d.b.1 * (incM F (d.b⁻¹).1 * x.1.1 * incM F d.b.1) * incM F (d.b⁻¹).1
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have e : u c = x.1 := Units.ext hx'.symm
    rw [e]
    exact x.2
  refine ⟨fun c => ⟨u c, mem c⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · intro c
    show incM F (d.b⁻¹).1 * N c * incM F d.b.1 = M c
    simp only [N, Matrix.mul_assoc]
    rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

