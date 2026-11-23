module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGenerator
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOne
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.NsubHaarCovol

theorem exists_haar_covol_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hcl : IsClosed (Nsub (AF F) σ J P : Set (HA (AF F) σ J)) :=
    PI.UnitaryGroupMassFormula.MeasWCore.isClosed_Nsub (AF F) σ J P
  let μ0 : Measure (Nsub (AF F) σ J P) := Measure.haar
  have hμ0 : μ0.IsHaarMeasure := inferInstance
  obtain ⟨⟨𝓕, h𝓕⟩, hall, hscale⟩ :=
    GlobalTheory.ClosedSubgroupCovol.fundamentalDomain_covol F E σ hCM n J hJ _ hcl μ0 hμ0
  obtain ⟨Kc, hKc, hcov⟩ := GlobalTheory.UnipFlagCore.nsub_cocompact F E σ hCM n J hJ r P T hP
  obtain ⟨hcv, hne, hle⟩ := hall 𝓕 h𝓕
  have hfin : μ0 𝓕 ≠ ∞ :=
    ((hle Kc hKc.isClosed.measurableSet hcov).trans_lt hKc.measure_lt_top).ne
  have hpos : 0 < (μ0 𝓕).toReal := ENNReal.toReal_pos hne hfin
  have hc0 : ((μ0 𝓕).toNNReal)⁻¹ ≠ 0 := inv_ne_zero (by
    intro h; rw [ENNReal.toNNReal_eq_zero_iff] at h; exact h.elim hne hfin)
  refine ⟨((μ0 𝓕).toNNReal)⁻¹ • μ0, Measure.IsHaarMeasure.nnreal_smul _ hc0, ?_⟩
  rw [hscale _ hc0, hcv, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
  exact inv_mul_cancel₀ hpos.ne'

end GlobalTheory.NsubHaarCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfSteps
section
noncomputable section

open scoped Classical
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

theorem exists_row_level_analytic (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticP) : StepAnalyticConstantsP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀),
    fun C' Cl e1 e2 D large₂ X Y u u' hTies hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, hBk',
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hTies hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'⟩

end GlobalTheory.NGRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReading
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinScale

open Formalism.L2.SG.RealObj

theorem ptEntry_row_zero {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (a b : ℕ), a < b → b < (bs.map Prod.snd).sum →
      blkOf bs a = blkOf bs b → ∃ c, c < b ∧ ∀ j, j ≤ c → Formalism.MainNotions.S.ptEntry bs c j = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro a b hab hb hbl
    simp at hb
  | cons block rest ih =>
    obtain ⟨t, s⟩ := block
    intro a b hab hb hbl
    by_cases ha : a < s
    · by_cases hbs : b < s
      · refine ⟨0, by omega, fun j hj => ?_⟩
        have hj0 : j = 0 := by omega
        subst hj0
        have hs : 0 < s := by omega
        simp only [Formalism.MainNotions.S.ptEntry]
        rw [if_pos ⟨hs, hs⟩, if_neg (by omega)]
      · exfalso
        simp [blkOf, ha, hbs] at hbl
    · have hbs : ¬ b < s := by omega
      simp only [blkOf, ha, hbs, if_false] at hbl
      have hbl' : blkOf rest (a - s) = blkOf rest (b - s) := by omega
      have hb' : b - s < (rest.map Prod.snd).sum := by simp at hb; omega
      obtain ⟨c, hc, hz⟩ := ih (a - s) (b - s) (by omega) hb' hbl'
      refine ⟨c + s, by omega, fun j hj => ?_⟩
      simp only [Formalism.MainNotions.S.ptEntry]
      rw [if_neg (by omega)]
      split_ifs with h
      · have hcs : c + s - s = c := by omega
        rw [hcs]
        exact hz _ (by omega)
      · rfl

theorem isEmpty_freeE_of_reg {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hreg : RegX X u u' γ) (hrep : IsPtRep X u u' w γ) :
    IsEmpty (FreeE w) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨⟨a, b⟩, hab, hbl⟩ := p
  have hab' : a.1 < b.1 := hab
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hb := b.2
  obtain ⟨c, hcb, hz⟩ := ptEntry_row_zero w.1 a.1 b.1 hab' (by rw [hsum]; exact b.2) hbl
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hle : c + 1 ≤ D.R.rS + 1 := by omega
  apply (hreg v).1 (c + 1) (by omega) (by omega)
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hle]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨c, by omega⟩
  intro j
  simp only [Matrix.submatrix_apply]
  have hrow := congrFun (congrFun (hrep v) (Fin.castLE hle ⟨c, by omega⟩)) (Fin.castLE hle j)
  simp only [ptC, Formalism.MainNotions.S.ptMat, Matrix.map_apply, Formalism.L2.SG.RealObj.ZhatO, Fin.val_castLE] at hrow
  rw [hz j.1 (by omega), map_zero, map_zero] at hrow
  rcases mul_eq_zero.mp hrow with h | h
  · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · exact h

theorem ptRep_unique {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) {w w' : Point D.host.E (D.R.rS + 1)}
    {γ : X.B.I.Ginf} (h : IsPtRep X u u' w γ) (h' : IsPtRep X u u' w' γ) : w = w' := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have e := (h v).symm.trans (h' v)
  apply GlobalTheory.IntTerm.ptMat_injective
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun e i) j
  simp only [ptC, Matrix.map_apply] at hij
  exact X.ιE.symm.injective ((X.B.I.φ v).injective hij)

theorem one_le_g {D : D7} (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem scale_pin : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  intro D X u u'
  have hg : (1 : NNReal) ≤ (X.B.g : NNReal) := by exact_mod_cast one_le_g X
  let sc : X.B.I.Ginf → NNReal := fun γ =>
    if h : ∃ w, IsPtRep X u u' w γ then ((X.B.g : NNReal) ^ (D.R.f * Fintype.card (FreeE h.choose)))⁻¹ else 1
  refine ⟨sc, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    simp only [sc]
    split_ifs with h
    · have := isEmpty_freeE_of_reg X u u' _ γ hγ h.choose_spec
      simp [Fintype.card_eq_zero]
    · rfl
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_pos.mpr (pow_pos (lt_of_lt_of_le one_pos hg) _)
    · exact one_pos
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    · exact le_rfl
  · rintro w ⟨γ0, hγ0⟩
    have hex0 : ∃ γ, IsPtRep X u u' w γ := ⟨γ0, hγ0⟩
    have hw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW
      rw [dif_pos hex0]
      exact hex0.choose_spec
    have hex : ∃ w', IsPtRep X u u' w' (gamW X u u' w) := ⟨w, hw⟩
    simp only [sc, dif_pos hex]
    rw [ptRep_unique X u u' hex.choose_spec hw]
    push_cast
    rfl

end GlobalTheory.PinScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasure
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open Formalism.REAL (Jm UJ muG)

noncomputable section

namespace GlobalTheory.LeviIso

theorem detNorm_pos_iff {E : Type} [Field E] [NumberField E] {j : ℕ} (x : MatInf E j) :
    0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw]; simp)] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem gram_place (I : AutInst) (v : InfinitePlace I.F) {p q : Type} (X : Matrix (Fin I.n) p I.E)
    (Y : Matrix (Fin I.n) q I.E) :
    ((I.P v)⁻¹ * X.map (I.φ v))ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * Y.map (I.φ v)) = (Xᴴ * I.J * Y).map (I.φ v) := by
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hX : (X.map (I.φ v))ᴴ = Xᴴ.map (I.φ v) := by
    ext r s
    exact (I.cm.cmUnram.2.1 (I.φ v) (X s r)).symm
  rw [← I.P_spec v, Matrix.map_mul, Matrix.map_mul, ← hX]
  calc _ = (I.P v * (I.P v)⁻¹ * X.map (I.φ v))ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹ * Y.map (I.φ v)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.one_mul, Matrix.one_mul]

theorem conjT_map {τ : ℂ →+* ℂ} (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) {p q : Type} (X : Matrix p q ℂ) :
    (X.map τ)ᴴ = Xᴴ.map τ := by
  rcases hτ with rfl | rfl <;> ext r s <;> simp

theorem Jm_map {n : ℕ} (ε : Fin n → Bool) (τ : ℂ →+* ℂ) : (Jm ε).map τ = Jm ε := by
  ext r s
  simp only [Jm, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem inv_map {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (τ : ℂ →+* ℂ) :
    P.map τ * P⁻¹.map τ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
  simp

theorem exists_charts (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) (v : InfinitePlace I.F)
    (v₀ : InfinitePlace I₀.F) (τ τ₀ : ℂ →+* ℂ) (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ)
    (hτ₀ : τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) (hv : ∀ y, I.φ v (e y) = τ₀ (I₀.φ v₀ y)) :
    ∃ θ, IsLeviChart (I.ε v) (I₀.ε v₀) (flagAt I S v) (fun i => (I.P v)⁻¹ * (T i).map (I.φ v))
      ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P v₀).map τ₀) τ τ₀ θ := by
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  have hsp := _root_.GlobalTheory.LeviIso.spansFlag_flagAt I I₀ e xf a j S Λ x₀ T T' T₀ h v
  obtain ⟨-, hn, -, h1, h2, h3, -, -⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  have sw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := by
    intro i k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  refine _root_.GlobalTheory.LeviIso.Chart.exists_leviChart _ _ a j _ _ _ _ (fun i => ((I.P v)⁻¹ * (T' i).map (I.φ v))ᴴ * Jm (I.ε v)) _ τ τ₀ hτ hτ₀ hn
    (fun i => ?_) (fun i k hik => ?_) (fun i k => ?_) (fun i => ?_) ?_ hsp (_root_.GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag I _ a j S hsat v)
  · rw [gram_place, sw, (h2 i).1]
    simp
  · rw [gram_place, sw, (h1 k i).2.2 hik.symm]
    simp
  · rw [gram_place, (h1 i k).1]
    simp
  · rw [← Matrix.mul_assoc, gram_place, (h2 i).2.1]
    simp
  · have e1 : (I₀.J.map e).map (I.φ v) = (I₀.J.map (I₀.φ v₀)).map τ₀ := by
      ext r s
      exact hv _
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm _),
      ← Matrix.mul_assoc _ _ ((I₀.P v₀).map τ₀), ← Matrix.mul_assoc _ (Jm _), gram_place, h3, e1,
      conjT_map hτ₀, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, I₀.P_spec, Jm_map]

theorem size_solve {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) {s t D : ℝ} (hs : 0 < s) (ht : 0 < t) (hD : 0 < D)
    (h : t ^ f = s ^ f * D ^ (-(1 : ℝ) / (2 * k))) :
    t = (D / s ^ (2 * f * k)) ^ (-(1 / (2 * (f : ℝ) * k))) := by
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 := congrArg Real.log h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_rpow hD] at h1
  apply Real.log_injOn_pos ht (Real.rpow_pos_of_pos (by positivity) _)
  rw [Real.log_rpow (by positivity), Real.log_div hD.ne' (by positivity), Real.log_pow]
  push_cast
  field_simp
  field_simp at h1
  linarith

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] {a : ℕ} (j : Fin a → ℕ) :
    ∀ᵐ z ∂(Measure.pi fun i => haarGL E (j i)), ∀ i, 0 < detNorm E (j i) (z i) := by
  have hσ : ∀ i, SigmaFinite (haarGL E (j i)) := fun i => by
    rw [_root_.GlobalTheory.HaarPi.haarGL_eq_pi]
    exact inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => haarLoc (j i)))
  have h1 : ∀ i, ∀ᵐ x ∂(haarGL E (j i)), 0 < detNorm E (j i) x := by
    intro i
    rw [_root_.GlobalTheory.HaarPi.haarGL_eq_pi]
    have h2 : ∀ᵐ x ∂(Measure.pi fun _ : InfinitePlace E => haarLoc (j i)), ∀ w, (Matrix.of (x w)).det ≠ 0 := by
      refine ae_all_iff.2 fun w => ?_
      have h3 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
        rw [ae_iff]
        simpa using (_root_.GlobalTheory.LeviIso.haarLoc_conj_and_null (j i)).2
      exact (Measure.quasiMeasurePreserving_eval (fun _ : InfinitePlace E => haarLoc (j i)) w).ae h3
    exact h2.mono fun x hx => (detNorm_pos_iff x).2 hx
  exact ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval (fun i => haarGL E (j i)) i).ae (h1 i)

theorem levi_product : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj h μM _ c₀ hμ hc₀
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  obtain ⟨β, σ, τ, τ₀, hτ, hτ₀, hβ, hσ⟩ := _root_.GlobalTheory.LeviIso.Places.places_match I I₀ e h.1
  choose θ hθ using fun v => exists_charts I I₀ e xf a j S Λ x₀ T T' T₀ hj h v (σ v) (τ v) (τ₀ v) (hτ v) (hτ₀ v)
    (hσ v)
  have hcard : Fintype.card (InfinitePlace I.F) = I.f := GlobalTheory.Count.FrameMajorant.card_places I
  have hf : 1 ≤ I.f := Module.finrank_pos
  let R : (∀ i, MatInf I.E (j i)) × I₀.Ginf →
      ∀ v : InfinitePlace I.F, (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ (I₀.ε (σ v)) :=
    fun z v => (fun i => z.1 i (β v), z.2 (σ v))
  have hR := GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures _ _ _ β σ a (fun i => Fin (j i) → Fin (j i) → ℂ) (fun w => UJ (I₀.ε w))
    (fun i => haarLoc (j i)) (fun w => muG (I₀.ε w)) (fun i => 2 ^ (j i ^ 2)) c₀ (fun i => by positivity)
    (fun w => ((_root_.GlobalTheory.GaugeWhole.gauge_whole _ _).1 _ (hc₀ w)).1.le)
  have hRm : Measurable R := hR.measurable
  have hΘ : Measurable fun (z : (∀ i, MatInf I.E (j i)) × I₀.Ginf) v => θ v (R z v) :=
    Measurable.of_eval fun v => (hθ v).1.comp ((measurable_pi_apply v).comp hRm)
  have hdet : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v i, (Matrix.of ((R z v).1 i)).det ≠ 0 := fun z hz v i => (detNorm_pos_iff _).1 (hz i) (β v)
  have hM : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v, θ v (R z v) ∈ flagM (I.ε v) (flagAt I S v) := fun z hz v =>
    ((hθ v).2.1 _).2 ⟨R z v, hdet z hz v, rfl⟩
  have hpos := fun g : I.Ginf => _root_.GlobalTheory.LeviIso.sizeQ_flag_pos I (g, xf) a j S hsat
  refine ⟨fun z v => θ v (R z v), fun i => sizesAt I xf S 1 i ^ (2 * I.f * j i), hΘ,
    fun i => pow_pos (hpos 1 i) _, fun m => ⟨fun hm => ?_, ?_⟩, fun z z' hz1 hz2 hz' => ?_, fun z hz i => ?_,
    fun z z' hz hz' hzz => ?_, fun φ hφ => ?_⟩
  · choose y hy1 hy2 using fun v => ((hθ v).2.1 (m v)).1 (hm v)
    refine ⟨(fun i w => (y (β.symm w)).1 i, Equiv.piCongrLeft (fun w => UJ (I₀.ε w)) σ fun v => (y v).2),
      fun i => (detNorm_pos_iff _).2 fun w => hy1 _ i, funext fun v => ?_⟩
    rw [← hy2 v]
    refine congrArg (θ v) (Prod.ext (funext fun i => ?_) ?_)
    · exact congrArg (fun u => (y u).1 i) (β.symm_apply_apply v)
    · exact Equiv.piCongrLeft_apply_apply (fun w => UJ (I₀.ε w)) σ (fun v => (y v).2) v
  · rintro ⟨z, hz, rfl⟩
    exact hM z hz
  · choose γ hγ1 hγ2 using hz1
    obtain ⟨g, hg, Γ, γ₀, g1, g2, g3, g4⟩ := _root_.GlobalTheory.LeviRat.exists_rat_block I I₀ e xf a j S Λ x₀ T T' T₀ h γ hγ1 z.2 hz2
    have hz : ∀ i, 0 < detNorm I.E (j i) (z.1 i) := by
      intro i
      refine (detNorm_pos_iff _).2 fun w => ?_
      have : Matrix.of (z.1 i w) = (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E).map w.embedding := by
        ext r s
        exact hγ2 i w r s
      rw [this]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((γ i).isUnit.map w.embedding.mapMatrix)).ne_zero
    have hP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
    have hact : ∀ (v) {p : Type} (X : Matrix (Fin I.n) p I.E),
        uMat (g v) * ((I.P v)⁻¹ * X.map (I.φ v)) = (I.P v)⁻¹ * (Γ * X).map (I.φ v) := by
      intro v p X
      rw [g1, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), hP, Matrix.one_mul, Matrix.map_mul, Matrix.mul_assoc]
    have hA : ∀ v i, uMat (g v) * ((I.P v)⁻¹ * (T i).map (I.φ v)) =
        (I.P v)⁻¹ * (T i).map (I.φ v) * (Matrix.of ((R z v).1 i)).map (τ v) := by
      intro v i
      rw [hact, g3, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext r s
      exact (hβ v _).trans (congrArg (τ v) (hγ2 i (β v) r s).symm)
    have hA₀ : ∀ v, uMat (g v) * ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v)) =
        (I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v) * (uMat (R z v).2).map (τ₀ v) := by
      intro v
      have e1 : (γ₀.map e).map (I.φ v) = (γ₀.map (I₀.φ (σ v))).map (τ₀ v) := by
        ext r s
        exact hσ v _
      have e2 : uMat (R z v).2 = _ := g2 (σ v)
      rw [← Matrix.mul_assoc, hact, g4, Matrix.map_mul, e1, e2, Matrix.map_mul, Matrix.map_mul,
        Matrix.mul_assoc _ ((I₀.P (σ v)).map (τ₀ v)), ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)),
        ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)), inv_map _ (I₀.P_unit _), Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    refine ⟨fun v => θ v (R z v), ⟨hM z hz, g, ⟨hg, fun v k y hy => ?_⟩, g * (fun v => θ v (R z v))⁻¹,
      fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).2 (g v) (hA v) (hA₀ v), (inv_mul_cancel_right _ _).symm⟩,
      funext fun v => ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).1⟩
    have hsp := _root_.GlobalTheory.LeviIso.spansFlag_flagAt I I₀ e xf a j S Λ x₀ T T' T₀ h v
    obtain ⟨u, hu, rfl⟩ := (hsp k y).1 hy
    refine (hsp k _).2 ⟨fun i => (Matrix.of ((R z v).1 i)).map (τ v) *ᵥ u i, fun i hi => ?_, ?_⟩
    · simp only [hu i hi, Matrix.mulVec_zero]
    · simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, hA]
  · have h0 : ∀ v, uMat ((1 : I.Ginf) v) = 1 := fun v => rfl
    have h1 := _root_.GlobalTheory.FlagMeas.SizeMove.size_move I xf a j hj S hsat 1 (fun v => θ v (R z v)) 1
      (fun v => ⟨fun i y _ => by rw [h0]; simp, fun y _ => by rw [h0]; simp⟩) (hM z hz)
      (fun v => show (uMat ((1 : I.Ginf) v))ᴴ * uMat ((1 : I.Ginf) v) = 1 by rw [h0]; simp) i
    rw [one_mul, mul_one] at h1
    refine size_solve hf (hj i) (hpos 1 i) (hpos _ i) (hz i) (h1.trans ?_)
    congr 1
    simp only [fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).1 i]
    have hj' : (j i : ℝ) ≠ 0 := by have := hj i; positivity
    rw [detNorm, ← Real.finsetProd_rpow _ _ (fun w _ => by positivity)]
    refine Fintype.prod_equiv β _ _ fun v => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    field_simp
  · have h1 : ∀ v, R z v = R z' v := fun v =>
      ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).2 (congrFun hzz v)
    refine Prod.ext (funext fun i => funext fun w => ?_) (funext fun w => ?_)
    · obtain ⟨v, rfl⟩ := β.surjective w
      exact congrFun (congrArg Prod.fst (h1 v)) i
    · obtain ⟨v, rfl⟩ := σ.surjective w
      exact congrArg Prod.snd (h1 v)
  · have hd : I.n - 2 * ∑ i, j i = I₀.n := by rw [h.2.1]; omega
    rw [hd] at hμ
    have h1 := funext fun v => (hθ v).2.2.2.2 (μM v) (c₀ (σ v)) (hμ v) (hc₀ (σ v))
    have h2 := measurePreserving_pi _ μM (f := θ) fun v => ⟨(hθ v).1, (congrFun h1 v).symm⟩
    have h3 := (h2.comp hR).lintegral_comp hφ
    have h4 : (Measure.pi fun i => haarGL I.E (j i)).restrict {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)} =
        Measure.pi fun i => haarGL I.E (j i) := Measure.restrict_eq_self_of_ae_mem (ae_detNorm_pos I.E j)
    rw [← h3, lintegral_smul_measure, h4, smul_eq_mul, hcard]
    simp only [_root_.GlobalTheory.HaarPi.haarGL_eq_pi]
    congr 1
    · simp only [← pow_mul, mul_comm]
    · exact lintegral_prod _ (hφ.comp hΘ).aemeasurable

end GlobalTheory.LeviIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmulStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε)), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → (∀ g, g ∈ S ↔ uMat g - 1 ∈ A) → IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → ∀ (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → L.det ≠ 0 → μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  first | exact @GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | exact GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | (intros; apply GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGeneratorStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt) ∧ ∃ x₀ ∈ X.Lb, (VS D).hT (X.zu u) x₀ = 1 ∧ ∃ d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), Fintype.linearCombination D.host.E (qFr wt) d = x₀ + (((D.mem u).A.T : D.host.E))⁻¹ • X.zu u ∧ ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ a : 𝓞 D.host.E, y - (a : D.host.E) • d ∈ Mq wt := by
  first | exact @GlobalTheory.St.G.mlat_main | exact GlobalTheory.St.G.mlat_main | (intros; apply GlobalTheory.St.G.mlat_main <;> assumption)
end

