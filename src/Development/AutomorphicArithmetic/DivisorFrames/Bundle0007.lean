module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis :
    ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
        (b : GL (Fin S.rank) (Fv D.host.F v)), IsSplitBasis τ (GlobalTheory.TripleSpaceW.conjSub Λ) b →
        ∃ g ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin S.rank),
          g.val = (β.val.map (GlobalTheory.BotMatch.evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val := by
  intro D S Λ β hΛ hβ v τ b hb
  have hJ := GlobalTheory.Doubling.isHermND_gram S
  have hL := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
  have h1 := GlobalTheory.FlipMatch.RowChart.isSplitBasis_conj τ
    (GlobalTheory.FlipMatch.RowChart.isFrameAt_loc hβ (splitPrime τ))
  have e : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      splitLat (t.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ) = splitLat t Λ := fun t => by
    refine le_antisymm (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, hx, fun i => rfl⟩)
      (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, ?_, fun i => ?_⟩)
    · rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx
    · change t (x i) = t (star (star (x i)))
      rw [star_star]
  have e2 := e (τ.comp D.sp.cm.sig)
  rw [comp_conj_conj (isCMExt_host D)] at e2
  set β' := GeneralLinearGroup.map (complEquiv τ (splitPrime_under τ)).symm.toRingHom (loc (splitPrime τ) β) with hβ'
  have hv : β'.val = β.val.map (GlobalTheory.BotMatch.evW τ) := rfl
  have h2 : IsSplitBasis τ Λ β' := fun u => by rw [← e τ]; exact h1 u
  have h3 : IsSplitBasis (τ.comp D.sp.cm.sig) Λ b := fun u => by rw [← e2]; exact hb u
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : GL (Fin S.rank) (Fv D.host.F v), g₀.val = b.valᵀ * S.gram.map τ * β'.val :=
    ⟨dualConj 1 b⁻¹ * splitGram hJ τ * β', by
      rw [Units.val_mul, Units.val_mul, dualConj_one_val, inv_inv, splitGram_val]⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.FlipMatch.RowChart.pairing_int (isCMExt_host D) hJ hL h2 h3 hg₀
  refine ⟨dualConj 1 g₀⁻¹, ?_, ?_⟩
  · rw [← (GLint_eq_KO_and_princ_eq_KOne v S.rank).1, mem_GLint_iff, ← map_inv, dualConj_one_val, dualConj_one_val,
      inv_inv]
    exact ⟨fun i j => k1 j i, fun i j => k2 j i⟩
  · rw [dualConj_one_val, inv_inv, hg₀, hv, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsScaledStandardPairSectionsOfMaxCompactTran
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private noncomputable def subst {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) :
    Matrix (Fin m) (Fin n) k ≃ₜ Matrix (Fin m) (Fin n) k where
  toFun X := g.val * X * h.val
  invFun X := (g⁻¹).val * X * (h⁻¹).val
  left_inv X := by
    show (g⁻¹).val * (g.val * X * h.val) * (h⁻¹).val = X
    rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc (g⁻¹).val, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    show g.val * ((g⁻¹).val * X * (h⁻¹).val) * h.val = X
    rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc g.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem subst_SB {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k)) :
    (fun X => f (g.val * X * h.val)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k) :=
  ⟨hf.1.comp_continuous (subst g h).continuous, hf.2.comp_homeomorph (subst g h)⟩

private theorem subst_ne {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    {Y : Matrix (Fin m) (Fin n) k} (hf : f Y ≠ 0) : ∃ X : Matrix (Fin m) (Fin n) k, f (g.val * X * h.val) ≠ 0 := by
  obtain ⟨X, rfl⟩ := (subst g h).surjective Y
  exact ⟨X, hf⟩

open GlobalTheory.StdPairCone in
private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ X, stdA ν ϖ c a a' X ≠ 0 := by
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append ((1 : Matrix (Fin a) (Fin a) k) i) (fun _ => 0)
  have h1 : blk₁ X = 1 := by ext i j; simp [blk₁, X]
  have h2 : blk₂ X = 0 := by ext i j; simp [blk₂, X]
  refine ⟨X, ?_⟩
  have h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdA, dite_eq_left h]
  exact Units.ne_zero _

open GlobalTheory.StdPairCone in
private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ Y, stdB ν ϖ c a a' Y ≠ 0 := by
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append (fun _ => 0) ((1 : Matrix (Fin a') (Fin a') k) i)
  have h1 : blk₂ X = 1 := by ext i j; simp [blk₂, X]
  have h2 : blk₁ X = 0 := by ext i j; simp [blk₁, X]
  refine ⟨X, ?_⟩
  have h : (blk₂ X).det ≠ 0 ∧ IsGLO (blk₂ X) ∧ ∀ i j, blk₁ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdB, dite_eq_left h]
  exact Units.ne_zero _

end SlopeTestRemainingChoices

theorem UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
        (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
        GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
        ∀ (gA : GL (Fin a) k) (gB : GL (Fin a') k) (cc : GL (Fin (a + a')) k), gA ∈ GlobalTheory.SplitWeil.KO k (Fin a) →
        ∃ (lam : ℂ) (Ξ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ), lam ≠ 0 ∧
          (∀ X, Ξ X = GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (cc⁻¹).valᵀ)) ∧
          (∀ Y, Ψ Y = lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val)) ∧
          Ξ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) ∧ Ξ ≠ 0 ∧ Ψ ≠ 0 ∧
          GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β Ξ =
            GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α Ψ := by
  intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ gA gB cc hgA
  obtain ⟨hz, -⟩ := _root_.GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ
  obtain ⟨hA, hB⟩ := _root_.GlobalTheory.StdPairSB.stdPair_mem_SB ν ϖ c a a' hϖ hcν
  have hab : ν * β = α := by
    rw [hν]
    ext x
    simp
  obtain ⟨lam, hl, H⟩ := _root_.GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change k a a rfl (Fin a') (Fin a') (Fin (a + a')) (Fin (a + a')) (Equiv.refl _)
    (Equiv.refl _) finSumFinEquiv finSumFinEquiv (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a')))
    (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) ϖ ν β gA gB cc hgA
  rw [hab] at H
  have H' := H _ _ hz
  refine ⟨lam, fun X => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (GlobalTheory.SplitFlip.invT cc).val),
    fun Y => lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val), hl, fun _ => rfl, fun _ => rfl,
    subst_SB gA _ hA, (GlobalTheory.WeilM.SB _).smul_mem lam (subst_SB gB cc hB), ?_, ?_, H'⟩
  · obtain ⟨Y, hY⟩ := stdA_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gA (GlobalTheory.SplitFlip.invT cc) hY
    exact fun h => hX (congrFun h X)
  · obtain ⟨Y, hY⟩ := stdB_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gB cc hY
    exact fun h => mul_ne_zero hl hX (congrFun h X)
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitIdempotentMulEqOfPiWEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v),
        ∃ a : AE D, IsSplitIdem D a ∧ ∀ z : AE D, At (evFin D.host.F v) z → piW t z = 0 → a * z = z := by
  intro D v t
  refine ⟨GlobalTheory.EmbChart.idem (t.comp D.sp.cm.sig), GlobalTheory.EmbChart.isSplitIdem_idem _, fun z hz h0 => ?_⟩
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v (1 : Fv D.host.F v)) • z = 0 :=
    hz _ (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero, Algebra.smul_def] at h1
  have h2 : z = GlobalTheory.EmbChart.tensAt D.host.E v (1 * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) :=
    h1.trans (GlobalTheory.EmbChart.tensAt_mul_right v 1 z)
  have h3 : GlobalTheory.AdelicU.splitIdem (GlobalTheory.AdelicU.isCMExt_host D) t * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z = 0 :=
    (GlobalTheory.AdelicU.splitProj_eq_zero_iff _ t _).1 h0
  rw [GlobalTheory.EmbChart.idem_mul, GlobalTheory.AdelicU.splitIdem_comp, sub_mul, h3, sub_zero]
  exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

open GlobalTheory.StdFrames (cpt comp_toAd)
open GlobalTheory.LFun (complMap)
open GlobalTheory.AdelicU (splitPrime_under)

variable {D : D7}

private theorem ext_cpt {a b : AE D} (h1 : infPart D a = infPart D b)
    (h2 : ∀ Q, cpt (D := D) Q (toEAf D a) = cpt (D := D) Q (toEAf D b)) : a = b :=
  (comp_toAd D).ext' h1 h2

private theorem cpt_base {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : Q.under (𝓞 D.host.F) = v) (u : AF D.host.F) :
    cpt (D := D) Q (toEAf D (algebraMap _ (AE D) u)) = complMap h (evFin D.host.F v u) := by
  subst h
  exact (comp_toAd D).base u Q

private theorem cpt_split {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    cpt (D := D) (splitPrime τ) (toEAf D z) = complMap (splitPrime_under τ) (piW τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    have e1 : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap _ (AE D) a * incA D x := by
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : piW τ (a ⊗ₜ[D.host.F] x : AE D) = evFin D.host.F v a * τ x := rfl
    have e3 : cpt (D := D) (splitPrime τ) (toEAf D (incA D x)) = algebraMap _ _ x :=
      congrArg (fun s => s (splitPrime τ)) ((comp_toAd D).inc x)
    rw [e2, e1, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cpt_base (splitPrime_under τ), e3,
      GlobalTheory.LFun.SplitTie.complMap_apply_emb]

private theorem piW_comp {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piW (τ.comp D.sp.cm.sig) z = piW τ (cA D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

private theorem first_half {e₀ : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e₀ S)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hP : ∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) (ht : ∀ v : P, splitPrime (t v) ∈ S) (z : AE D) :
    e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z := by
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  have one : ∀ {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ ∈ S →
      piW τ e₀ = 1 := fun τ h =>
    (complMap (splitPrime_under τ)).injective (by rw [← cpt_split, e1 _ h, RingHom.map_one])
  constructor
  · intro hz
    refine ⟨fun u hu => ?_, fun v => ?_⟩
    · have h0 : algebraMap _ (AE D) u * e₀ = 0 := by
        refine ext_cpt (by rw [RingHom.map_mul, e0, mul_zero, RingHom.map_zero]) fun Q => ?_
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_zero, RingHom.map_zero]
        by_cases hQ : Q ∈ S
        · rw [cpt_base rfl, hu _ ((hP _).2 ⟨Q, hQ, rfl⟩), RingHom.map_zero, zero_mul]
        · rw [e2 Q hQ, mul_zero]
      rw [Algebra.smul_def, ← hz, ← mul_assoc]
      exact (congrArg (· * z) h0).trans (zero_mul z)
    · have h0 := congrArg (piW (t v)) he.2
      rw [RingHom.map_mul, one _ (ht v), one_mul, RingHom.map_zero, ← piW_comp] at h0
      change piW ((t v).comp D.sp.cm.sig) z = 0
      rw [← hz, RingHom.map_mul, h0, zero_mul]
  · rintro ⟨h1, h2⟩
    have h1' : ∀ u : AF D.host.F, (∀ v ∈ P, evFin D.host.F v u = 0) → algebraMap _ (AE D) u * z = 0 :=
      fun u hu => (Algebra.smul_def u z).symm.trans (h1 u hu)
    refine ext_cpt ?_ fun Q => ?_
    · have h3 := congrArg (infPart D) (h1' ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) fun v _ => rfl)
      have h4 : infPart D (algebraMap (AF D.host.F) (AE D) ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) = 1 := rfl
      rw [RingHom.map_mul, h4, one_mul, RingHom.map_zero] at h3
      rw [RingHom.map_mul, h3, mul_zero]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hQ : Q ∈ S
      · rw [e1 Q hQ, one_mul]
      rw [e2 Q hQ, zero_mul, eq_comm]
      by_cases hv : Q.under (𝓞 D.host.F) ∈ P
      · have hm : Q.asIdeal ∈ (Q.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨rfl⟩⟩
        rw [GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) (t ⟨_, hv⟩)] at hm
        rcases hm with e | e
        · exact absurd ((HeightOneSpectrum.ext e : Q = _) ▸ ht ⟨_, hv⟩) hQ
        · have h5 := cpt_split ((t ⟨_, hv⟩).comp D.sp.cm.sig) z
          rw [h2 ⟨_, hv⟩, RingHom.map_zero] at h5
          have e' : Q = splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) := HeightOneSpectrum.ext e
          generalize splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) = Q' at h5 e'
          subst e'
          exact h5
      · let u : AF D.host.F := ((0, singleV D.host.F (Q.under (𝓞 D.host.F)) 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
        have h3 := congrArg (fun y => cpt (D := D) Q (toEAf D y)) (h1' u fun v hv' =>
          Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F)
            (fun e : v = Q.under (𝓞 D.host.F) => hv (e ▸ hv')) 1)
        have h4 : evFin D.host.F (Q.under (𝓞 D.host.F)) u = 1 :=
          Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (Q.under (𝓞 D.host.F)) 1
        simp only [RingHom.map_mul, RingHom.map_zero] at h3
        rwa [cpt_base rfl, h4, RingHom.map_one, one_mul] at h3

private theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, GlobalTheory.IdemSupport.cA_algebraMap]

end

theorem UpperTheory.idempotentSum_fixes_iff_halfEl :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        (∀ z : AE D, e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z) ∧ ∀ z : AE D, cA D e₀ * z = z ↔ HalfEl P t z := by
  intro D e₀ S he P t hP ht
  refine ⟨first_half he P t hP ht, fun z => ?_⟩
  have hc : ∀ y : AE D, cA D (cA D y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (fun s => a ⊗ₜ[D.host.F] s) (star_star x)
  have hi : Function.Injective (cA D) := Function.LeftInverse.injective hc
  have h := first_half he P t hP ht (cA D z)
  rw [← hi.eq_iff, RingHom.map_mul, hc] at h
  refine h.trans (and_congr (forall_congr' fun u => imp_congr_right fun _ => ?_) (forall_congr' fun v => ?_))
  · change u • cA D z = 0 ↔ u • z = 0
    rw [← cA_smul, ← hi.eq_iff, hc, RingHom.map_zero]
  · change piW ((t v).comp D.sp.cm.sig) (cA D z) = 0 ↔ _
    rw [piW_comp, hc]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.LocalCharConductorLeOfHeckeExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.localChar_conductor_le_of_heckeExponent :
    ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH →
        ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : ℕ), GlobalTheory.CMVal.ExpAt νH (splitPrime τ) c →
        GlobalTheory.SplitFlip.CondLE (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) c (chrW ν τ) ∧ (¬ GlobalTheory.LFun.UnrAt ν (splitPrime τ) → 1 ≤ c) := by
  intro D ν νH h v τ c hc
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · have h1 : Valued.v (x : Fv D.host.F v) = 1 := (GlobalTheory.FlipMatch.isEquiv_Fv v).eq_one_iff_eq_one.1 hx.1
    have h2 : Valued.v ((x : Fv D.host.F v) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      refine ((GlobalTheory.FlipMatch.isEquiv_Fv v _ _).1 hx.2).trans_eq ?_
      rw [Units.val_pow_eq_pow_val, map_pow, GlobalTheory.ChrWUnif.valued_unifAt, ← WithZero.exp_nsmul]
      simp
    have h3 := (hc c).2 le_rfl (Units.map (complMap (splitPrime_under τ)).toMonoidHom x)
      ((SplitTie.valued_complMap τ (splitPrime_under τ) _).trans h1) (by
        refine le_of_eq_of_le ?_ h2
        rw [← SplitTie.valued_complMap τ (splitPrime_under τ), RingHom.map_sub, RingHom.map_one]
        rfl)
    rw [← locChar_eq_of_chrEq h] at h3
    exact h3
  · by_contra h0
    apply hn
    rw [unrAt_iff_of_chrEq h]
    intro x hx
    refine (hc 0).2 (by omega) x hx ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (le_of_eq hx) (le_of_eq (map_one _))
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.PtOSgnMemLatAtVIffMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_eq {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (p : Fin S.rank) (q : Fin d) : ptO S.gram e x p q = GlobalTheory.BigDat.divG S x (e q) p := rfl

private noncomputable def ptH {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) :
    Matrix (Fin n) (Fin S.rank) (AE D) →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
  AddMonoidHom.mk' (ptO S.gram e) fun x y => by
    ext p q
    rw [Matrix.add_apply, ptO_eq, ptO_eq, ptO_eq, GlobalTheory.BigDat.divG, Matrix.add_mul]
    rfl

private theorem ptO_inj {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) {x y : Matrix (Fin n) (Fin S.rank) (AE D)}
    (h : ptO S.gram e x = ptO S.gram e y) : x = y := by
  have h1 : GlobalTheory.BigDat.divG S x = GlobalTheory.BigDat.divG S y := by
    ext q p
    obtain ⟨q, rfl⟩ := e.surjective q
    rw [← ptO_eq, ← ptO_eq, h]
  rw [← GlobalTheory.BigDat.mulG_divG S x, h1, GlobalTheory.BigDat.mulG_divG]

private theorem ptO_gen {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (β : AF D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin n → D.host.E) :
    ptO S.gram e (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (fun q => a * t (e q))) := by
  ext p q
  refine (ptO_eq S e _ p q).trans ((GlobalTheory.BigDat.divG_gen S β a s t (e q) p).trans ?_)
  rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
  rfl

private theorem at_eq_pairA {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {b : AF F}
    (hb : At (evFin F v) b) (hi : evFin F v b ∈ v.adicCompletionIntegers F) : ∃ α ∈ intAf F, b = pairA F 0 α := by
  refine ⟨GlobalTheory.AdelicU.singleFin v (evFin F v b), fun w => ?_, GlobalTheory.VacAny.eq_atPlace_of_at v b hb⟩
  by_cases h : w = v
  · subst h
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    exact hi
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h]
    exact zero_mem _

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
    (hL : IsLat e Vs Ws ΛS ΛX) :
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO S X), ptO S.gram e x ∈ latAtV Vs Ws v → x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO S.gram e x ∈ latAtV Vs Ws v := by
  refine ⟨fun v x hx => ?_, fun v b hb hi x hx => ?_⟩
  · have key : latAtV Vs Ws v ≤ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E))
        fun _ => True).map (ptH S e) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨b, hb, hi, x, hx, y, hy, rfl⟩
      obtain ⟨α, hα, rfl⟩ := at_eq_pairA hb hi
      have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ GlobalTheory.SkewLat.DualPair.AA_ne]
        exact FractionalIdeal.one_mem_one _
      have h2 : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)),
          pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) ∈
            (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True).map (ptH S e) := by
        intro z hz
        refine Submodule.mul_induction_on hz (fun a ha c hc => ?_) (fun z z' hz hz' => ?_)
        · refine ⟨_, AddSubgroup.subset_closure ⟨α, hα, fun _ h => (h trivial).elim, a, ha, star x, (hL.1 x).1 hx,
            c • fun k => y (e.symm k), (hL.2 y).1 hy c hc, rfl⟩, ?_⟩
          refine (ptO_gen S e _ a _ _).trans ?_
          rw [star_star]
          congr 3
          funext q
          simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
        · have h3 : pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x ((z + z') • y)) =
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) +
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z' • y)) := by
            refine Matrix.ext fun p q => ?_
            rw [Matrix.add_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply,
              ← TensorProduct.tmul_add]
            simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add]
          rw [h3]
          exact add_mem hz hz'
      have h4 := h2 1 h1
      rwa [one_smul] at h4
    obtain ⟨x', hx', h⟩ := key hx
    rwa [← ptO_inj S e h]
  · refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom _ b).comp (ptH S e)) ?_ hx
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine (congrArg (fun z => b • z ∈ latAtV Vs Ws v) (ptO_gen S e (pairA _ 0 α) a s t)).mpr ?_
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, (hL.1 _).2 (by rw [star_star]; exact hs), _, (hL.2 _).2 ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, hb u hu, zero_mul]
    · rw [map_mul]
      exact mul_mem hi (hα v)
    · simp only [Equiv.apply_symm_apply]
      exact GlobalTheory.BigDat.smul_mem_scLat_of_mem ha ht

theorem UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO (sgn ε S) X), ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v → x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v := by
  intro D ψ ε S X d e Bs Vs Ws M _ ΛS ΛX hL
  exact finiteRing_sq_sub_mul_sq_eq_of_card (sgn ε S) X e Vs Ws ΛS ΛX hL
end

