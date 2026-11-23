module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMultilinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def pullBil {V₁ V₂ W₁ W₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (a : V₁ →ₗ[ℂ] W₁) (b : V₂ →ₗ[ℂ] W₂) :
    (W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] (V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) where
  toFun f := f.compl₁₂ a b
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp

theorem invLine_of_iso [DecidableEq D.what₂.Tau] (ch : Choice R) {μ0 : T} (hL : R.toLevCh.Is μ0)
    (hlf : (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
      ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (hc : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support,
        ∀ y Q ξ η, GenConv ch t a M d y Q ξ η)
    (Aψ : weylSub ((rowSizes D).nR (0 : Fin ((rowSizes D).m + 1))) (psiWt (rowEntries D ch.sc.cGap)) ≃ₗ[ℂ]
      Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W)
    (hA : ∀ g F, Aψ (psiRep (rowEntries D ch.sc.cGap) g F) =
      Aψ F ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ ((kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)
    (Bf : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
      Module.Dual ℂ R.cX.W)
    (hB : ∀ g φ, Bf ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
      Bf φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹) :
    InvLine ch := by
  classical
  obtain ⟨tc, tr, htr⟩ := GlobalTheory.RowReal.exists_fock_transport hL ch.W
  refine ⟨D.what₂.Tau, inferInstance, inferInstance, rowSizes D, rowEntries D ch.sc.cGap,
    fun τ => rowEntries_good D _ τ, fun Q => PiTensorProduct.tprod ℂ (fun j => tc j (Q.1 j)) ⊗ₜ[ℂ]
      (PiTensorProduct.tprod ℂ (fun i => tr i (Q.2 i)) ⊗ₜ[ℂ] (Aψ.symm ch.ξ ⊗ₜ[ℂ] Bf.symm (R.prX.flip ch.cv.v))), ?_⟩
  intro t a hS β hβ M hM τ hτ d hd y
  obtain ⟨Φ0, hΦ0⟩ := GlobalTheory.RowReal.genPer_multilinear ch t a M d y (hc t a hS β hβ M hM τ hτ d hd y)
  let Irow := (LinearMap.compMultilinearMapₗ ℂ (pullBil Aψ.toLinearMap Bf.toLinearMap)) ∘ₗ
    (MultilinearMap.compLinearMapₗ (σ₂₃ := RingHom.id ℂ) (σ₁₃ := RingHom.id ℂ) (fun i : Fin D.R.m => (tr i).symm.toLinearMap))
  let Φ := (Irow.compMultilinearMap Φ0).compLinearMap (fun j : Fin D.R.m => (tc j).symm.toLinearMap)
  have hΦ : ∀ x₁ y₁ v₁ φ₁, Φ x₁ y₁ v₁ φ₁ =
      genPer ch t a M d y (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁) :=
    fun x₁ y₁ v₁ φ₁ => hΦ0 (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁)
  have hv := hS.vec β τ hτ d hd
  have hinv : ∀ g x₁ y₁ v₁ φ₁, Φ (fun j => rowFock (rowEntries D ch.sc.cGap) j g (x₁ j))
      (fun i => colFock (rowEntries D ch.sc.cGap) i g (y₁ i)) (psiRep (rowEntries D ch.sc.cGap) g v₁)
      ((baseRep (rowEntries D ch.sc.cGap)).dual g φ₁) = Φ x₁ y₁ v₁ φ₁ := by
    intro g x₁ y₁ v₁ φ₁
    rw [hΦ, hΦ, hA, hB]
    obtain ⟨h1, h2⟩ := htr ch.S.toGridChoice g t
    have e1 : ptTop ch.W g 0 = (kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩ := ptTop_lt ch.W g _
    have e2 : ptGrid ch.W g 0 = (kappa ch.W g).2 0 := ptGrid_le ch.W g (Nat.succ_pos _)
    have key := GlobalTheory.RowReal.genPer_move ch hL t a M d y (fun j => ⟨_, hM.1 j j.2⟩) (fun i => ⟨_, hM.2 i (Nat.le_of_lt_succ i.2)⟩)
      hv.1 hv.2 (hlf.1 a) (hlf.2 t y) g (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i))
      (fun j => (tc j).symm (rowFock (rowEntries D ch.sc.cGap) j g (x₁ j)),
        fun i => (tr i).symm (colFock (rowEntries D ch.sc.cGap) i g (y₁ i)))
      (fun j => by simpa using h1 j (d.1 j) (hv.1 j) ((tc j).symm (x₁ j)))
      (fun i => by simpa using h2 i (d.2 i) (hv.2 i) ((tr i).symm (y₁ i))) (Aψ v₁) (Bf φ₁)
    rw [e1, e2] at key
    exact key
  obtain ⟨l, hl, hle⟩ := GlobalTheory.RowReal.invFun_of_multilinear (rowEntries D ch.sc.cGap) Φ hinv
  refine ⟨l, hl, fun Q => ?_⟩
  rw [hle]
  refine Eq.trans ?_ (hΦ _ _ _ _).symm
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem invLine_big : Big fun ch => InvLine ch := by
  obtain ⟨C1, h1⟩ := GlobalTheory.RowReal.gen_left
  obtain ⟨C2, h2⟩ := GlobalTheory.GenConvProof.genPer_conv
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, h1'⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, h2'⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  classical
  have hlf := h1' D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hc := h2' D large₂ he (le_of_max_le_right hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hL := hS.core.lev
  obtain ⟨Aψ, hA⟩ := GlobalTheory.CoefPsi.coefPsi ch.W (posOnb_of_defNode ch.W A.μ0 hL (X := .top 0) (Nat.zero_le _))
  obtain ⟨Bf, hB⟩ := GlobalTheory.CoefBase.coefBase ch hS.core.models.inf hS.core.models.cX hS.core.models.prX hch.weil
    (posOnb_of_defNode ch.W A.μ0 hL (X := .grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩)
  exact invLine_of_iso ch hL hlf hc Aψ hA Bf hB

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipRowsIntegralGLInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.SquareFlipRows

theorem squareFlip_one_rows : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ u ∈ KO k A, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      (ν (gdet u) : ℂ) * squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ
          (fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂)) =
        squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ X := by

  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ u hu X
  have hM : (invT u⁻¹).val = u.valᵀ := by rw [invT_val, inv_inv]
  have hMK : invT u⁻¹ ∈ KO k A := invT_mem_KO (inv_mem hu)
  have hdep : HasDepth ϖ e (blockLat ϖ e (Assignment.two.block D₁ D₂))
      (phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    have h1 := (FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e (Assignment.one.block D₁ D₂) hϖ hψ).1 Φ hΦ
    have h2 := @FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' (D₁ ⊕ D₂) _ _ _ _ _ _ μ (by assumption) σ ν ϖ e
      (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν h1
    rw [← compl_block_one, ← latA_blockLat]; exact h2
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hφu : ∀ Y, (ν (gdet u) : ℂ) * phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) (u.valᵀ * Y) =
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) Y := by
    intro Y
    classical
    rw [phiA, phiA, ← hM, GlobalTheory.PrimFrameLeft.isPrimFrame_gl_mul_iff _ _ hMK]
    by_cases hY : IsPrimFrame (latA ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))) Y
    · rw [if_pos hY, if_pos hY]
      obtain ⟨h, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hY.1
      rw [hM]
      exact _root_.GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO μ σ ν _ u hu h
    · rw [if_neg hY, if_neg hY, mul_zero]
  have hb : ∀ (Q : D₁ ⊕ D₂ → Prop), (∀ j ∈ Assignment.two.block D₁ D₂, Q j) ↔ ∀ c, Q (Sum.inr c) := by
    intro Q
    refine ⟨fun h c => h _ (by simp [Assignment.block]), fun h j hj => ?_⟩
    cases j with
    | inl c => simp [Assignment.block] at hj
    | inr c => exact h c
  set X' : Matrix A (D₁ ⊕ D₂) k := fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂) with hX'
  have hcond : (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X' i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]) := by
    simp only [hb]
    have := mul_mul_mem_matLat_iff (inv_mem hu) (one_mem (KO k D₂)) X.toCols₂
    rw [mem_matLat_stdLat, mem_matLat_stdLat, Units.val_one, Matrix.mul_one] at this
    simpa [hX', Matrix.toCols₂] using this
  have hset : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      setCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) =
        u.valᵀ * setCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [hM]
    ext i j
    rcases j with c | c
    · simp [setCols, Assignment.block, hX', Matrix.mul_apply, Matrix.toCols₁]
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      first | rfl | exact Matrix.mul_apply | (erw [Matrix.mul_apply]; simp)
  have hsub : X'.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) =
      (u⁻¹).val * X.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) := by
    ext i ⟨j, hj⟩
    rcases j with c | c
    · simp [Assignment.block] at hj
    · simp [hX', Matrix.mul_apply, Matrix.toCols₂]
  have hpair : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      pairCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) = pairCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [pairCols_eq_trace, pairCols_eq_trace, hsub, hM, transpose_mul, ← Matrix.mul_assoc, trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]
  unfold squareFlip
  rw [compl_block_one, invFourierSum_inv_apply, invFourierSum_inv_apply]
  by_cases hX : ∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]
  · rw [if_pos hX, if_pos (hcond.2 hX)]
    set φ := phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
    have hg : ∀ Z Z' : Matrix A (Assignment.two.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) →
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) (Z + Z') =
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) Z := by
      intro Z Z' hZ'
      have e1 : setCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          setCols (Assignment.two.block D₁ D₂) X' Z + setCols (Assignment.two.block D₁ D₂) 0 Z' := by
        ext i j; by_cases h : j ∈ Assignment.two.block D₁ D₂ <;> simp [setCols, h]
      have e2 : pairCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          pairCols (Assignment.two.block D₁ D₂) X' Z + pairCols (Assignment.two.block D₁ D₂) X' Z' := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      have e3 : pairCols (Assignment.two.block D₁ D₂) X' Z' ∈ 𝒪[k] :=
        Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (hZ' i j) (hcond.2 hX i j j.2)
      simp only
      rw [e1, e2, hdep.2, AddChar.map_add_eq_mul, triv _ e3, mul_one]
      apply FourierDepth.mem_matLat_smul_blockLat.2
      constructor
      · intro i j hj
        simpa [setCols, hj] using hZ' i ⟨j, hj⟩
      · intro i j hj
        simp [setCols, hj]
    have key := GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left ϖ e hϖ (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) hg (invT u⁻¹) hMK
    beta_reduce at key
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hset, hpair, ← mul_assoc, hφu]
  · rw [if_neg hX, if_neg (mt hcond.1 hX), mul_zero]

end GlobalTheory.SquareFlipRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridLastRowColumnCharactersDiffer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = rankX D j :=
  (G.isV (X := .top j) hj (fun _ h => by cases h)).rank

theorem rank_grid (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) :
    (G.V (.grid D.R.m j)).rank = rankV D D.R.m j :=
  (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h => by
    have := D.R.two_le_m; have := (Node.grid.inj h).1; omega)).rank

theorem rankX_mod (j : ℕ) : rankX D j % 2 = rankX D 0 % 2 := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  have : rankX D j = rankX D 0 + 2 * (j * (c + 1)) := by
    simp only [rankX, hc]; ring
  omega

theorem rankV_row (j : ℕ) : rankV D D.R.m j + 1 + j = rankX D j + D.R.m := by
  have h : sLen D - 1 = D.R.r + 5 := by simp only [sLen]; omega
  simp only [rankV, rankX, rankP, nRk]
  rw [h]
  simp only [sLen]
  ring

theorem rankV_succ (j : ℕ) : rankV D D.R.m (j + 1) = rankV D D.R.m j + D.R.t := by
  simp only [rankV]; ring

noncomputable def chiZ (L : LevCh D T) : (AE D)ˣ →* Circle := if Odd (rankX D 0) then L.eta else L.eta⁻¹

theorem chr_top (G : GridData L sc) (t : T) {j : ℕ} (hj : j < D.R.m) :
    G.chrS (.top t j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankX D j) ∧
    G.chrT (.top t j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankX D (j + 1)) := by
  refine ⟨?_, ?_⟩
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.top j)).rank = _
    rw [rank_top G hj.le]; rfl
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.top (j + 1))).rank = _
    rw [rank_top G hj]; rfl

theorem chr_mu (G : GridData L sc) (t : T) {j : ℕ} (hj : j < D.R.m) :
    G.chrS (.mu t D.R.m j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankV D D.R.m j) ∧
    G.chrT (.mu t D.R.m j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankV D D.R.m (j + 1)) := by
  refine ⟨?_, ?_⟩
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m j)).rank = _
    rw [rank_grid G hj.le]; rfl
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m (j + 1))).rank = _
    rw [rank_grid G hj]; rfl

theorem chiZ_eq (G : GridData L sc) (t : T) :
    chiZ L = (G.chrS (.top t 0))⁻¹ * G.chrS (.mu t D.R.m 0) := by
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  rw [(chr_top G t (by omega)).1, (chr_mu G t (by omega)).1]
  have h1 := rankV_row (D := D) 0
  simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
  split_ifs <;> first | (exfalso; omega) | group

theorem rowChars {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) :
    ∃ χz : (AE D)ˣ →* Circle, IsHeckeChar D χz ∧ ResEta D χz 1 ∧
      (∀ j, j < D.R.m → G.chrS (.top t j) = G.chrT (.top t j)) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 0 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j) * χz) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 1 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j)) := by
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := D.R.t_odd
  have HA := Wl.om_is (.top t 0) (show 0 + 1 ≤ D.R.m by omega)
  have HB := Wl.om_is (.mu t D.R.m 0) (show D.R.m ≤ D.R.m ∧ 0 + 1 ≤ D.R.m by omega)
  refine ⟨chiZ L, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chiZ_eq G t]
    refine ⟨?_, fun x => ?_⟩
    · exact (HA.hecS.1.inv).mul HB.hecS.1
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, HA.hecS.2 x, HB.hecS.2 x, inv_one, one_mul]
  · rw [chiZ_eq G t]
    have rA : (G.pS (.top t 0)).rank = rankX D 0 := rank_top G (by omega)
    have rB : (G.pS (.mu t D.R.m 0)).rank = rankV D D.R.m 0 := rank_grid G (by omega)
    have eA := HA.resS
    have eB := HB.resS
    rw [rA] at eA
    rw [rB] at eB
    refine ⟨eA.1, fun η hη x => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, eA.2 η hη x, eB.2 η hη x]
    have hx : η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη x
    have hn : rankV D D.R.m 0 = rankX D 0 + 2 * (a - 1) + 1 := by
      have := rankV_row (D := D) 0
      omega
    rw [hn, pow_add, pow_add, pow_mul, pow_two, hx, one_pow, mul_one, inv_mul_cancel_left]
  · intro j hj
    rw [(chr_top G t hj).1, (chr_top G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    simp only [Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    rw [h1, h2]
  · intro j hj hp
    rw [(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    have h3 := rankV_row (D := D) j
    have h4 := rankV_succ (D := D) j
    simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group
  · intro j hj hp
    rw [(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    have h3 := rankV_row (D := D) j
    have h4 := rankV_succ (D := D) j
    simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group

end GlobalTheory.RowChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacAlg

open GlobalTheory.MovedAlg

theorem isAlg_sqrt_inv (n : ℕ) : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹) := by
  have h : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, Rat.cast_natCast]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  rw [← mem_algebraicClosure_iff] at h ⊢
  exact inv_mem h

section Comb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isAlgComb_heis {u : WO S T} (hu : u.map (infPart D) = 0) : IsAlgComb ψ S T f₀ (heisO ψ S T u f₀) :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩

theorem isAlgComb_sum (Δ : Finset (WO S T)) (hΔ : ∀ u ∈ Δ, u.map (infPart D) = 0) :
    IsAlgComb ψ S T f₀ (∑ u ∈ Δ, heisO ψ S T u f₀) := by
  classical
  induction Δ using Finset.induction_on with
  | empty => simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isAlgComb_heis (hΔ a (Finset.mem_insert_self a s))).add
      (ih fun u hu => hΔ u (Finset.mem_insert_of_mem hu))

theorem isAlgComb_self : IsAlgComb ψ S T f₀ f₀ := by
  have := isAlgComb_heis (ψ := ψ) (f₀ := f₀) (u := (0 : WO S T)) (by simp)
  rwa [GlobalTheory.SplitScalar.heisO_zero ψ S T f₀] at this

end Comb


end GlobalTheory.SplitVacAlg

end
end

