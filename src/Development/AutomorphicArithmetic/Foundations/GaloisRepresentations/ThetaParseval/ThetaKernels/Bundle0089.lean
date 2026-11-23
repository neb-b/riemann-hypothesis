module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0078
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0088
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0087
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0069
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0045
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0081
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0058
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0086
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.SiegelMultW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ConjRationalParabolicEmbed
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem paddedMatrix_mul_submatrix (A : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L A * N).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = A * N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L A _ hl', Matrix.one_apply_ne, zero_mul]
    rintro rfl
    exact hl' ⟨a, rfl⟩
  · intro b
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem mul_paddedMatrix_submatrix (B : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (N * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L B).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * B := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L B hl', Matrix.one_apply_ne, mul_zero]
    rintro rfl
    exact hl' ⟨c, rfl⟩
  · intro b
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem conj_rationalParabolic_embed (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  have hx : (L.j p')⁻¹ * cM c.1 * L.j p' ∈ rat2 σ d.Y :=
    mul_mem (mul_mem (inv_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h c.2.1 c.2.2)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr)
  have hf : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L ((L.j p')⁻¹ * cM c.1 * L.j p') :=
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_inv_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k p')) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c.1)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k p')
  obtain ⟨s, c₂, γ', hs, hsP, -, hγ', hx'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.stab_dec_k h hx hf
  have hsub : (inFrame d.b ((L.j p')⁻¹ * cM c.1 * L.j p')).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_inv, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k,
      _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mul_paddedMatrix_submatrix, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.paddedMatrix_mul_submatrix, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.emS_cM_k h, Matrix.mul_one, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hγ1 : γ' = 1 := kunf.inFrame_injective L.b (by rw [hγ', hsub, GlobalTheory.EisBL.DoubledParabolic.inFrame_one])
  rw [hγ1, map_one, mul_one] at hx'
  refine ⟨L.j p' * (w₁ * s * w₁⁻¹), mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hp) hsP,
    mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr) (mul_mem (mul_mem h.wr hs) (inv_mem h.wr)), c₂, ?_⟩
  have hw := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.weyl_commutes_embedding h p'
  calc w₁ * (cM c.1 * L.j p') = w₁ * L.j p' * ((L.j p')⁻¹ * cM c.1 * L.j p') := by group
    _ = L.j p' * w₁ * (s * cM c₂.1) := by rw [hw, hx']
    _ = L.j p' * (w₁ * s * w₁⁻¹) * (w₁ * cM c₂.1) := by group
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledWeilApplyBoxFunEqBoxFunLeft
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.doubled_weil_apply_boxFun_eq_boxFun_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @_root_.GlobalTheory.DblTargetRestrict.restrict_boxFun_k | exact _root_.GlobalTheory.DblTargetRestrict.restrict_boxFun_k | (intros; apply _root_.GlobalTheory.DblTargetRestrict.restrict_boxFun_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameDilK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rEx_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : ∃ r : ℝ → GroundTheory.Global.IdeleGroup F,
    (∀ τ τ', r (τ + τ') = r τ * r τ') ∧ r 0 = 1 ∧
    (∀ τ, (GroundTheory.Global.IdeleGroup.ideleModule F (r τ) : ℝ) = Real.exp τ) ∧
    (∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ)) ∧
    (∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1) ∧
    (∀ τ, finOne F * (r τ : AF F) = finOne F) := by
  have := d.cm.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let u : ℝ → ℝˣ := fun τ => ⟨Real.exp τ, Real.exp (-τ), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩
  let r : ℝ → GroundTheory.Global.IdeleGroup F := fun τ => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u τ))
  have hu : ∀ τ τ', u (τ + τ') = u τ * u τ' := fun τ τ' => Units.ext (Real.exp_add τ τ')
  have hu0 : u 0 = 1 := Units.ext Real.exp_zero
  have hr1 : ∀ τ, ((r τ : AF F)).1 = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) := fun τ => rfl
  have hr2 : ∀ τ, ((r τ : AF F)).2 = 1 := fun τ => rfl
  have hee : ∀ x : ℝ, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm x) = x := fun x => e.apply_symm_apply x
  have hext : ∀ τ, InfinitePlace.Completion.extensionEmbedding w (e.symm (Real.exp τ)) = (Real.exp τ : ℂ) := by
    intro τ
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hee]
  refine ⟨r, fun τ τ' => by simp only [r, hu, map_mul], by simp only [r, hu0, map_one], fun τ => ?_, fun τ => ?_,
    fun τ w' hw' => ?_, fun τ => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, hw.mult_eq_one, pow_one]
    show ‖e.symm (Real.exp τ)‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hee,
      Real.norm_of_nonneg (Real.exp_pos τ).le]
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_same]
    exact hext τ
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw', map_one]
  · refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * _ = 0
      rw [zero_mul]
    · show (1 : Af F) * (r τ : AF F).2 = 1
      rw [hr2, mul_one]
theorem frame_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (r : ℝ → GroundTheory.Global.IdeleGroup F)
    (hw : ∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ))
    (ho : ∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1)
    (hf : ∀ τ, finOne F * (r τ : AF F) = finOne F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = dM i₀ ((r τ : AF F) • (1 : AE F E)) ((r (-τ) : AF F) • (1 : AE F E)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hC : Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ)) 0 0
      (Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)) = dM i₀ (Real.exp τ : ℂ) (Real.exp (-τ) : ℂ) := by
    ext u v
    rw [dM_apply]
    rcases u with u | u <;> rcases v with v | v <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, Matrix.zero_apply] <;>
      by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;> simp_all [Pi.single_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      rw [R.cw_iota_pf w' y, hy, dZ_conj_diag hζ0, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, hw, hw]
    · rw [R.off_w w w' y hw', _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, ho τ w' hw', ho (-τ) w' hw']
      ext u v
      rw [dM_apply, Matrix.one_apply]
      split_ifs <;> rfl
  · rw [R.off_f w y]
    ext u v
    rw [Matrix.smul_apply, Matrix.smul_apply, dM_apply, Matrix.one_apply]
    have e : ∀ t, finOne F • ((r t : AF F) • (1 : AE F E)) = finOne F • (1 : AE F E) := fun t => by
      rw [smul_smul, hf]
    split_ifs <;> simp [e]
theorem par_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    ∃ t, IsPar (R.ι w y) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (2 * τ) ∧
      (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 := by
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ) with hAdef
  set D : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)
  have hy' : mR y = Matrix.fromBlocks A 0 0 D := hy
  obtain ⟨-, hA, -, hoA, hfA, -⟩ := R.frame_diag w y A D hy'
  have h21 : (mR y).toBlocks₂₁ = 0 := by rw [hy', Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w y h21
  have hdetA : A.det = (Real.exp τ : ℂ) := by
    rw [hAdef, Matrix.det_diagonal, Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  refine ⟨t, ht, ?_, ?_⟩
  · rw [habs, hy', Matrix.toBlocks_fromBlocks₁₁, hdetA, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos τ).le,
      ← Real.exp_nat_mul]
    norm_num
  · have ht1 := ((kunf.isPar_frame ht0 (R.ι w y) t).1 ht).2
    set P := (inFrame d.b (R.ι w y)).toBlocks₁₁ with hP
    have hcw : ∀ w', d.cw w' t.1 = d.cw w' (incM F t0.1) * d.cw w' P * d.cw w' (incM F (t0⁻¹).1) := by
      intro w'; rw [ht1]; simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul]
    have hI : incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
      rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
    have hT : ∀ w', d.cw w' (incM F t0.1) * d.cw w' (incM F (t0⁻¹).1) = 1 := by
      intro w'; rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, ← Matrix.map_mul, hI, Matrix.map_one _ (map_zero _) (map_one _)]
    have ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1 := fun w' h => by rw [hcw, (hoA w' h).1, Matrix.mul_one, hT]
    have hf : finOne F • t.1 = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      rw [ht1, ← Matrix.smul_mul, ← Matrix.mul_smul, hfA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hI]
    have hdet : (d.cw w t.1).det = (Real.exp τ : ℂ) := by
      have hXY := congrArg Matrix.det (hT w)
      rw [Matrix.det_mul, Matrix.det_one] at hXY
      rw [hcw, Matrix.det_mul, Matrix.det_mul, hA, hdetA]
      linear_combination ((Real.exp τ : ℝ) : ℂ) * hXY
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (d := d) w t _ rfl ho hf, hdet]
    exact d.chiW_pos w _ (Real.exp_pos τ)
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HandsCoordkTau
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
def kom_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) : d.G :=
  L.j (nb' p.2) * uM p.1 * (L.j (nb' p.2))⁻¹ * (uM p.1)⁻¹
variable (L) in
def tau_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (δ : E) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    (Fin L.n → AE F E) × AF F :=
  (fun k => inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr (L.em k)),
    ellA δ (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr L.i₀)))
variable (L) in
def Du_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)
theorem frame_uM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L u) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k ha (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u)]
  rfl
theorem Du_mul_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-u) = 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  rw [← Matrix.map_mul, ← Matrix.transpose_mul, neg_neg, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u]
  ext i j
  simp [Matrix.one_apply, Matrix.map_apply]
theorem uM_neg'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d ?_)
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k, Matrix.fromBlocks_one]
theorem continuous_uA_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k (σ := σ) L) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
      fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]; exact (continuous_apply j).smul continuous_const
theorem continuous_frame_uM_k : Continuous fun u : Fin L.n → AE F E =>
    (Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L u) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
  refine Continuous.matrix_fromBlocks _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_uA_k continuous_const continuous_const ?_
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  exact ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_uA_k.comp continuous_neg).matrix_transpose).matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
theorem frame_kom_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) = inFrame d.b (L.j (nb' p.2)) * Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L p.1) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L p.1) *
      inFrame d.b (L.j (nb' (-p.2))) * Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-p.1)) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-p.1)) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k
  rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.uM_neg'_k h, ← map_inv, ← kunf.nb_neg h.nb', GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h]
theorem continuous_kom_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous fun p => inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) := by
  have hj : Continuous fun β : nA σ L.Y L.b => inFrame d.b (L.j (nb' β)) :=
    (GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame d.b).comp (L.cont.comp (kunf.continuous_nb h.nb'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_kom_k h]
  exact (((hj.comp continuous_snd).matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_frame_uM_k.comp continuous_fst)).matrix_mul
    ((hj.comp continuous_neg).comp continuous_snd)).matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_frame_uM_k.comp continuous_neg).comp continuous_fst)
theorem continuous_tau_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ) := by
  have hk := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_kom_k h
  refine Continuous.prodMk (continuous_pi fun k => hk.matrix_elem _ _) ?_
  exact (IsModuleTopology.continuous_of_linearMap (R := AF F) (ellA δ)).comp (hk.matrix_elem _ _)
theorem Du_neg_row_k (u : Fin L.n → AE F E) (k : Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L (-u) L.i₀ k = if k = L.i₀ then 1 else 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  rw [neg_neg, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hk : k = L.i₀
  · subst hk
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun j => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j]
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, hk, Ne.symm hk]
theorem sM_zero'_k : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L 0 = 1 := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L 0 = 0 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k]
  rw [this, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_one]
theorem cM_zero'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : cM (u, 0) = uM u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k]
theorem move_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) (b : Fin L.n → AE F E) (a : AF F) :
    L.j (nb' β'') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'')).1) * cM (u, a + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'')).2) * L.j (nb' β'') := by
  obtain ⟨B, A, hBA⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_move_k (R := R) h u β''
  suffices hτ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'') = (B, A) by rw [hτ]; exact hBA b a
  have e0 := hBA 0 0
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.sM_zero'_k, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.cM_zero'_k h, zero_add, zero_add] at e0
  have hk : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L B * cM (u, A) * (uM u)⁻¹ := by
    show L.j (nb' β'') * uM u * (L.j (nb' β''))⁻¹ * (uM u)⁻¹ = _
    rw [e0, mul_inv_cancel_right]
  have hf : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) =
      Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ A * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-u) + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L B) 0 1 := by
    rw [hk, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.uM_neg'_k h, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k]
    rw [show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L u from rfl]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k]
    rw [Matrix.add_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k, Matrix.mul_one]
  have hrow : ∀ k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ A * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L (-u)) L.i₀ k = if k = L.i₀ then A • inclR (F := F) (AF F) δ else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single L.i₀]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_neg_row_k]; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k]
    · intro m _ hm; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm hm]
    · simp
  refine Prod.ext (funext fun k => ?_) ?_
  · show inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr (L.em k)) = B k
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_neg (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k), zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k]
  · show ellA δ (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr L.i₀)) = A
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_pos rfl, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, add_zero, map_smul, ellA_self h.δ0,
      smul_eq_mul, mul_one]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisMult
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem siegelMult_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hn : 1 ≤ n) (χ : Chr F E) (hχ : IsHecke F E χ) (c : ℕ)
    (hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c) {b : GL (Fin n ⊕ Fin n) E}
    {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a)
    (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ (A : ℂ → ℂ) (H : ℂ → modFun σ Y) (t : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧
      (∀ μ, IsGrowForm μ → Differentiable ℂ (fun s => μ (H s))) ∧
      ∀ s : ℂ, t < s.re → ∀ x, HasSum (fun q => A s * eisTerm (flat a f s₁ s) x q) ((H s).1 x) := by
  have hSec : SecLaw := Hd.secLaw
  have hWL : WallLaw := Hd.wallLaw_of Hd.secLaw
  have hD : Dict := Hd.dict
  have hDI : DictInf := Hd.dictInf
  have hCM : CMGood := Hd.cmGood_of Hd.stdGood Hd.dict Hd.dictInf
  have hGT : GrpTop := Hd.grpTop
  have hBd : BdetLaw := Hd.bdetLaw
  have hPar : ParLaw := Hd.parLaw_of Hd.bdetLaw Hd.extLaw Hd.grpTop
  have hSg : SgAll := Hd.sgAll
  obtain ⟨⟨ε, hε⟩, t₀, ht₀⟩ := hb
  have hb' : IsFrame2 σ Y b := ⟨⟨ε, hε⟩, t₀, ht₀⟩
  have hcm := hB.cm
  have hunr := hB.unram
  have hgood : (adCM σ χ).Good := hCM F E σ χ c hcm hunr hχ hres
  obtain ⟨-, -, -, ht2', hlc', hsc', hKc⟩ := hGT E (AE F E) (adCM σ χ) hgood (Fin n) ε
  let Φ := frameEquiv (Y := Y) χ ε b hε
  have hΓ : ∀ x, x ∈ rat2 σ Y ↔ Φ x ∈ (adCM σ χ).uΓ ε (Fin n) := rat_iff χ ε b hε
  have hKK : ∀ x, x ∈ K ↔ Φ x ∈ (adCM σ χ).uK ε (Fin n) := fun x => GlobalTheory.T.standard_compact_frame_equiv F E σ n Y hD hDI hcm χ ε b hε B K hK x
  have hIP : ∀ x, (∃ t, IsPar x t) ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := _root_.GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ F E σ n Y χ ε b hε t₀ ht₀
  have hPP : ∀ x, x ∈ par2 σ Y ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
    intro x
    constructor
    · intro hx
      have : par2 σ Y ≤ ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))).comap Φ.toMonoidHom :=
        (Subgroup.closure_le _).2 fun p hp => (hIP p).1 hp
      exact this hx
    · intro hx
      exact Subgroup.subset_closure ((hIP x).2 hx)
  have hH := fun x => uH_eq hD hBd χ hgood ε b hε t₀ ht₀ K hKK a ha x
  have hiwa : Iwa ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))) ((adCM σ χ).uK ε (Fin n)) := by
    intro y
    obtain ⟨p, t, hp, k, hk, e⟩ := ha.iwa (Φ.symm y)
    refine ⟨Φ p, (hIP p).1 ⟨t, hp⟩, Φ k, (hKK k).1 hk, ?_⟩
    rw [← map_mul, ← e, MulEquiv.apply_symm_apply]
  obtain ⟨-, hparU⟩ := hPar E (AE F E) (adCM σ χ) hgood (Fin n) ε (Set.univ : Set (Fin n))
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  haveI := ht2'
  haveI := hlc'
  have hW := hSg F E σ χ c hcm hunr hχ hres ε (Fin n) (by simpa using hn) hiwa
  obtain ⟨σ₀, hσ₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb' hK ha
  refine eis_from_U hSec hWL Φ (continuous_frameEquiv χ ε b hε) _ _ _ ((adCM σ χ).uC ε (Fin n))
    ((adCM σ χ).uH ε (Set.univ : Set (Fin n))) hKc hIP' hIH ?_ K a χ s₁ f hf hΓ hKK hPP hIP hH
    (continuous_frameEquiv_symm χ ε b hε) ?_ ⟨σ₀, fun σ' h => ?_⟩
  · simpa using hW
  · intro p t hp
    refine ⟨?_, ?_⟩
    · show (((adCM σ χ).χ (bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hε p).1) : Circle) : ℂ) = _
      rw [GlobalTheory.T.block_det_parabolic_frame F E σ n Y χ ε b hε t₀ ht₀ p t hp]
      rfl
    · have := ha.val p t hp 1 (one_mem _)
      rwa [mul_one] at this
  · obtain ⟨C, N, h⟩ := hσ₀ σ' h
    exact ⟨C, N, fun x => (h x).2⟩
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

