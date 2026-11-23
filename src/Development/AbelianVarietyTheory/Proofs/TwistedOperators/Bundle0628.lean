module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInterOfSubfield
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodStepInvMulPointShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

section Shape
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem basePt_eq_zero_of_stepVar (y : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c y r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp only [Free, Kept, or_false, false_or] at h <;>
    simp only [basePt, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply]
  rw [if_neg (by omega)]


omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem stepVar_fixed_of_ordL_lt (y : Matrix n n' k) {r t : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) (hlt : GlobalTheory.DiagVol.ordL c r < GlobalTheory.DiagVol.ordL c t) :
    ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) ∧ basePt c y t s = 0 := by
  rcases r with r | r <;> rcases t with t | t <;> rcases s with s | s <;>
    simp only [Free, Kept, GlobalTheory.DiagVol.ordL, Sum.elim_inl, Sum.elim_inr, basePt, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, of_apply, not_or,
      Nat.even_iff, Nat.odd_iff, not_and, true_and, and_true, not_false_eq_true, not_true_eq_false] at hv hlt ⊢
  all_goals first | omega | (refine ⟨⟨by omega, by omega⟩, ?_⟩; rw [if_neg (by omega)]) | (refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]) | skip

end Shape

section Shape2
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


omit [Fintype n'] [DecidableEq n'] in
theorem unipSub_mul_fixed {u : GL (n ⊕ Fin c) k} (hu : u ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c))
    (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (u.val * M) r s = basePt c y r s := by
  intro r s hv
  have hu' : ∀ r t, GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r →
      u.val r t = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t := hu
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [hu' r r le_rfl, Matrix.one_apply_eq, one_mul, hM r s hv]
  · intro t _ htr
    by_cases h : GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r
    · rw [hu' r t h, Matrix.one_apply_ne (Ne.symm htr), zero_mul]
    · obtain ⟨h1, h2⟩ := stepVar_fixed_of_ordL_lt y hv (not_le.1 h)
      rw [hM t s h1, h2, mul_zero]
  · simp


omit [Fintype n'] [DecidableEq n'] in
theorem embX_mul_fixed (κ : GL n k) (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) →
      ((embX c κ).val * M) r s = basePt c (κ.val * y) r s := by
  intro r s hv
  have hE : (embX c κ).val = (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) := rfl
  rw [hE, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases r with a | l
  · simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have hb : ∀ b, M (Sum.inl b) s = basePt c y (Sum.inl b) s := fun b =>
      hM _ _ (by rcases s with s | s <;> simpa only [Free, Kept] using hv)
    simp only [hb]
    rcases s with s | s <;> simp [basePt, Matrix.mul_apply]
  · simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]) (by simp),
      Matrix.one_apply_eq, one_mul, hM _ _ hv]
    rcases s with s | s <;> simp [basePt]

end Shape2

theorem inv_mul_stepPt_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  intro k _ n n' _ _ _ _ c v hv κ x₀ e
  have hg : ((v * embX c κ)⁻¹).val = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [_root_.mul_inv_rev, map_inv, Units.val_mul]
  have hu : v⁻¹ ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c) := GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → stepPt x₀ e r s = basePt c x₀ r s :=
    fun r s h => by rw [stepPt, Matrix.add_apply, of_apply, dif_neg h, add_zero]
  have hA := embX_mul_fixed κ⁻¹ x₀ _ (unipSub_mul_fixed hu x₀ _ hM)
  have hR : ∀ (y : Matrix n n' k) (e' : StepVar n c n' → k) r s, stepPt y e' r s =
      basePt c y r s + (if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e' ⟨(r, s), h⟩ else 0) :=
    fun _ _ _ _ => rfl
  ext r s
  by_cases h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · conv_rhs => rw [hR, dif_pos h, basePt_eq_zero_of_stepVar _ h, zero_add]
  · conv_rhs => rw [hR, dif_neg h, add_zero]
    rw [hg, Matrix.mul_assoc, hA r s h]

end GlobalTheory.StepLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveFrameDatumBlockSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.FrameSubst

theorem vecMul_bound {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k)
    (hx : ∀ j, valuation k (x j) ≤ valuation k c) (j : n) : valuation k ((x ᵥ* G.val) j) ≤ valuation k c := by
  have hG' := ((mem_KO_iff G).1 hG).1
  simp only [vecMul, dotProduct]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hx i) ((Valuation.mem_integer_iff _ _).1 (hG' i j))).trans (by rw [mul_one])

theorem vecMul_bound_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k) :
    (∀ j, valuation k ((x ᵥ* G.val) j) ≤ valuation k c) ↔ ∀ j, valuation k (x j) ≤ valuation k c := by
  refine ⟨fun h j => ?_, fun h => vecMul_bound hG c x h⟩
  have := vecMul_bound ((KO k n).inv_mem hG) c _ h j
  rwa [vecMul_vecMul, Units.mul_inv, vecMul_one] at this

theorem mem_glLat_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D₁ D₂ : Type} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ϖ : kˣ) (e : ℕ)
    {G₁ : GL D₁ k} {G₂ : GL D₂ k} (h₁ : G₁ ∈ KO k D₁) (h₂ : G₂ ∈ KO k D₂) (G : GL (D₁ ⊕ D₂) k)
    (hG : G.val = fromBlocks G₁.val 0 0 G₂.val) : G ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) := by
  intro x
  have hl : ∀ j, (x ᵥ* G.val) (Sum.inl j) = ((fun i => x (Sum.inl i)) ᵥ* G₁.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  have hr : ∀ j, (x ᵥ* G.val) (Sum.inr j) = ((fun i => x (Sum.inr i)) ᵥ* G₂.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  rw [mem_blockLat_two, mem_blockLat_two]
  simp only [hl, hr]
  refine and_congr ?_ (vecMul_bound_iff h₂ _ _)
  have := vecMul_bound_iff h₁ 1 (fun i => x (Sum.inl i))
  simpa using this

theorem isPrimFrame_mul_glLat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] {Λ : Submodule 𝒪[k] (D → k)} (g : GL D k)
    (hg : g ∈ glLat Λ) (X : Matrix A D k) : IsPrimFrame Λ (X * g.val) ↔ IsPrimFrame Λ X := by
  refine ⟨fun h => ?_, fun h => Model.isPrimFrame_mul h g hg⟩
  have := Model.isPrimFrame_mul h g⁻¹ ((glLat Λ).inv_mem hg)
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem fFun_comp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (H : GL D k) (hH : apow (gdet H) ((Fintype.card D : ℂ) / 2) = 1) (X : Matrix A D k) :
    fFun μ σ ν (fun Y => Ψ (Y * H.val)) X = (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) * fFun μ σ ν Ψ (X * (invT H).val) := by
  classical
  by_cases hX : ∃ h : GL D k, X = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have e1 : X0 k σ * (invT h).val * (invT H).val = X0 k σ * (invT (h * H)).val := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc]
    have e2 : smallF μ ν (fun Y => Ψ (Y * H.val)) (Y0 k σ * h.val) = smallF μ ν Ψ (Y0 k σ * (h * H).val) := by
      unfold smallF; congr 1; funext g; simp only [Units.val_mul, Matrix.mul_assoc]
    rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, gdet_mul, map_mul, apow_mul, hH, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have hn : (ν (gdet H) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    simp only [Units.val_mul]
    ring
  · have hX' : ¬ ∃ h : GL D k, X * (invT H).val = X0 k σ * (invT h).val := by
      rintro ⟨h, hh⟩
      apply hX
      refine ⟨h * H⁻¹, ?_⟩
      have := congrArg (· * ((invT H)⁻¹).val) hh
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
      rw [this, map_mul, map_inv, Units.val_mul]
    rw [fFun, dite_eq_right hX, fFun, dite_eq_right hX', mul_zero]

theorem phiA_blockSubst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' (D₁ ⊕ D₂) k → ℂ), ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂,
    ∀ X : Matrix A (D₁ ⊕ D₂) k,
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
          (fun Y => Ψ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) Ψ (X * fromBlocks M₁.val 0 0 (invT M₂).val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ν ϖ e Ψ M₁ hM₁ M₂ hM₂ X
  classical
  let H : GL (D₁ ⊕ D₂) k := ⟨fromBlocks (invT M₁).val 0 0 M₂.val, fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  have hHinv : (invT H).val = fromBlocks M₁.val 0 0 (invT M₂).val := by
    rw [invT_val]
    show (fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val)ᵀ = _
    rw [fromBlocks_transpose, invT_inv_val, transpose_transpose, transpose_zero, transpose_zero, ← invT_val]
  have hdet : gdet H = (gdet M₁)⁻¹ * gdet M₂ := by
    rw [← gdet_invT]
    ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_fromBlocks_zero₁₂ _ _ _
  have habs : apow (gdet H) ((Fintype.card (D₁ ⊕ D₂) : ℂ) / 2) = 1 := by
    rw [hdet, apow_mul, apow_inv, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₁),
      apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₂), one_mul]
  have hfac : (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) = (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) := by
    rw [hdet, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  have hgl : invT H ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) :=
    mem_glLat_fromBlocks ϖ e hM₁ (invT_mem_KO hM₂) _ hHinv
  show phiA μ σ ν ϖ e _ (fun Y => Ψ (Y * H.val)) X = _
  rw [← hHinv]
  unfold phiA
  rw [latA_blockLat, compl_block_one, isPrimFrame_mul_glLat (invT H) hgl]
  split_ifs
  · rw [fFun_comp_mul μ σ ν Ψ H habs X, hfac]
  · simp

end GlobalTheory.FrameSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_col (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t := by
  change (columnBlock L j).sp.rank = _
  rcases hj.eq_or_lt with rfl | hk
  · rw [colY_m]; exact D.sp.X'_rank
  · rw [colY_lt L hk]; exact Comparison₂.rank_Yc hk.le


open Classical in
def topPl (L : LevCh D T) (t : T) : Finset (Pl D.host.E) := L.Pg ∪ L.Q t


open Classical in
def topFn {G : GridData L sc} (B : Frames G) (t : T) (e : AE D) (j : ℕ) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Mx D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : ℂ :=
  if IsHalf e x ∧ IsIntM (Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) then
    ∏ w ∈ topPl L t, stepFn L t w j
      (((Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb)
        (Comparison₂.ixOf G t w ha))
  else 0

end GlobalTheory.FlipTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem latO_tgt_le {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)}
    (v : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal)
    (h : ∀ t ∈ LT, (((c : D.host.F) : D.host.E)) • t ∈ LT') :
    latO S T LS LT (· = v) ≤ latO S T LS LT' (· = v) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.IdeleAA.gam v c * α, GlobalTheory.IdeleAA.gam_mul_int v c hc hα,
    GlobalTheory.IdeleAA.gam_mul_supp v c α, a, ha, s, hs, _, h t ht, ?_⟩
  ext i j
  simp only [Matrix.of_apply]
  rw [← GlobalTheory.IdeleAA.pair_scale v c α hsupp]
  congr 1
  have h0 := GlobalTheory.IdeleAA.coe_ne_zero v c hc
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem coe_alg (c : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) = ((c : D.host.F) : D.host.E) := rfl

theorem exists_c {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modulBar sc := by
  classical
  set J : Ideal (𝓞 D.host.F) := ∏ v' ∈ P.S0, v'.asIdeal ^ P.depth sc v' with hJdef
  have hJ : ¬ J ≤ v.asIdeal := by
    intro h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le v.isPrime).1 h
    have h1 : v'.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := v.isPrime) hle
    have : v' = v := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top h1)
    exact hv (this ▸ hv')
  obtain ⟨c, hcJ, hcv⟩ := Set.not_subset.1 hJ
  have hmap : J.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.modul sc := by
    rw [hJdef]
    change Ideal.mapHom (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [map_prod]
    refine Finset.prod_le_prod' fun v' hv' => ?_
    rw [map_pow]
    refine pow_le_pow_left' ?_ _
    refine Ideal.map_le_iff_le_comap.2 (le_of_eq ?_)
    have := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    exact this.symm
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc := hmap (Ideal.mem_map_of_mem _ hcJ)
  refine ⟨c, hcv, hmod, ?_⟩
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [Formalism.L2.Pj.algebraMap_conj_smul, coe_alg]
    exact GlobalTheory.IdeleAA.conj_F c
  unfold Places.modulBar
  rw [← hfix]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hmod

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem smul_mem_idLat (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hc : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modul sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {y : Fin n → D.host.E} (hy : y ∈ Λ) : ((c : D.host.F) : D.host.E) • y ∈ idLat (shiftId G) Λ := by
  refine Submodule.subset_span ⟨_, ?_, y, hy, rfl⟩
  unfold shiftId
  rw [← mul_one ((c : D.host.F) : D.host.E)]
  exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hc, coe_alg c⟩)
    (FractionalIdeal.one_mem_inv_coe_ideal hne)

theorem smul_idLat_mem (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hcb : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modulBar sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {z : Fin n → D.host.E} (hz : z ∈ idLat (shiftId G) Λ) : ((c : D.host.F) : D.host.E) • z ∈ Λ := by
  refine Submodule.span_induction (p := fun z _ => ((c : D.host.F) : D.host.E) • z ∈ Λ) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, y, hy, rfl⟩
    have hm : ((c : D.host.F) : D.host.E) * s ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hcb, coe_alg c⟩) hs
      have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
      rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
    obtain ⟨o, -, ho⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  · simp
  · intro x y _ _ hx hy; rw [smul_add]; exact add_mem hx hy
  · intro a x _ hx; rw [smul_comm]; exact Λ.smul_mem a hx

end GlobalTheory.BigLoc

theorem GlobalTheory.BigLoc.latBig_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0,
    ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u →
      (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  obtain ⟨c, hcv, hc, hcb⟩ := GlobalTheory.BigLoc.exists_c G.pl sc hv
  have hne : G.pl.modulBar sc ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hcb
    apply GlobalTheory.IdeleAA.coe_ne_zero v c hcv
    rw [← GlobalTheory.BigLoc.coe_alg, hcb, map_zero]
  unfold latBig
  rw [GlobalTheory.AscFinWit.mem_latO_at hu]
  exact ⟨fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_idLat_mem G hcb hne ht) h,
    fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_mem_idLat G hc hne ht) h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitCharacterValueAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCharAlg

open Formalism.L2.Host
open scoped TensorProduct

theorem isAlgebraic_loc {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {n : I → ℤ}
    {χ : HChar E} (h : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    IsAlgebraic ℚ ((χ.loc v x : ℂˣ) : ℂ) := by
  have h2 : (χ ^ 2).HasInf φ (fun i => 2 * n i) := by
    intro k
    have e1 : (((χ ^ 2).inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) ^ 2 := rfl
    rw [e1, h k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = _ ^ (2 * n i)
    rw [mul_comm, zpow_mul]
    norm_cast
  obtain ⟨M, hM, hv⟩ := GlobalTheory.HeckeLocVals.locVals_of_even h2
  have hx := hv v x
  have e2 : (((χ ^ 2).loc v x : ℂˣ) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) ^ 2 := rfl
  rw [e2] at hx
  have hint : IsIntegral ℚ (((⟨_, hx⟩ : M) : ℂ)) := (IsIntegral.of_finite ℚ (⟨_, hx⟩ : M)).map M.val
  exact IsAlgebraic.of_pow two_pos hint.isAlgebraic


open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem exists_locIdele {D : D7} {e : AE D} (he : IsSplitIdem D e) (x : (AE D)ˣ) (hx : (x : AE D) = e * x + (1 - e)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ), x = GlobalTheory.LFun.locIdele D.host.F w y := by
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 he
  have hA : At (evFin D.host.F v) (splitIdemAd (isCMExt_host D) τ) := by
    intro u hu
    rw [Algebra.smul_def, mul_comm]
    change singleTens D.host.E v _ * _ = 0
    rw [singleTens_mul]
    have : compFin D.host.F D.host.E v (algebraMap (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) u) = 0 := by
      change (evFin D.host.F v u) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [hu, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  have h1 : (x : AE D) - 1 = splitIdemAd (isCMExt_host D) τ * ((x : AE D) - 1) := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [hx]
    ring
  refine ⟨_, _, GlobalTheory.ChrLocal.eq_locIdele_splitPrime (isCMExt_host D) τ x ?_ ?_⟩
  · intro u hu
    rw [h1, ← smul_mul_assoc, hA u hu, zero_mul]
  · obtain ⟨-, e0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd (isCMExt_host D) τ
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, e0]
    ring

end GlobalTheory.SplitCharAlg

namespace GlobalTheory.SplitCharAlg

end GlobalTheory.SplitCharAlg
end
end

