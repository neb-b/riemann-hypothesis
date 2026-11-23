module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationMultilinearNormSq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem norm_sq_toLp_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

def phi (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : X.B.I.GA → ℂ :=
  fun x => ev (MP R) (vecOf R X c y) S
    (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)

theorem vecOf_update [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau)
    (z : Wsub R X c τ) :
    vecOf R X c (Function.update y τ z) =
      Function.update (vecOf R X c y) τ ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    simp [vecOf]
  · simp [vecOf, Function.update_of_ne hσ]

theorem phi_add [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (z₁ + z₂)) =
      phi R X h t c S (Function.update y τ z₁) + phi R X h t c S (Function.update y τ z₂) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.add_apply]
  have e : (⟨(c τ).symm ((z₁ + z₂ : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (z₁ + z₂)⟩ :
      (MP R).sm τ) = ⟨(c τ).symm (z₁ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₁⟩ +
        ⟨(c τ).symm (z₂ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₂⟩ :=
    Subtype.ext (by simp)
  rw [e, S.map_update_add]
  rfl

theorem phi_smul [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (a • z)) =
      (starRingEnd ℂ a) • phi R X h t c S (Function.update y τ z) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.smul_apply]
  have e : (⟨(c τ).symm ((a • z : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (a • z)⟩ :
      (MP R).sm τ) = (starRingEnd ℂ a) • ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ :=
    Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ])
  rw [e, S.map_update_smul]
  rfl

end GlobalTheory.RowEvalHHNorm

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem phi_memLp_integral (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (K : ℝ)
    (hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K)
    (y : ∀ τ, Wsub R X c τ) :
    MemLp (phi R X h t c S y) 2 (muX X) ∧
      ∫ x, ‖phi R X h t c S y x‖ ^ 2 ∂(muX X) = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  by_cases h0 : ∃ τ, (y τ : X.B.H (X.pl.symm τ)) = 0
  · obtain ⟨τ, hτ⟩ := h0
    have hv : vecOf R X c y τ = 0 := Subtype.ext (by simp [vecOf, hτ])
    have hz : phi R X h t c S y = 0 := by
      funext x
      simp only [phi, ev_apply, S.map_coord_zero τ hv]
      rfl
    have hp : ∏ σ, ‖(y σ : X.B.H (X.pl.symm σ))‖ ^ 2 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [hτ])
    rw [hz, hp]
    refine ⟨MeasureTheory.MemLp.zero, ?_⟩
    simp
  · push Not at h0
    have hn : ∀ τ, ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = ‖(y τ : X.B.H (X.pl.symm τ))‖ :=
      fun τ => LinearIsometryEquiv.norm_map _ _
    have hpos : ∀ τ, 0 < ‖(y τ : X.B.H (X.pl.symm τ))‖ := fun τ => norm_pos_iff.2 (h0 τ)
    let u : (MP R).Vec := fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹ : ℝ) : ℂ) • vecOf R X c y τ
    have hu : ∀ τ, ‖(u τ : (MP R).H τ)‖ = 1 := by
      intro τ
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      show |‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹| * ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = 1
      rw [hn, abs_of_pos (inv_pos.2 (hpos τ)), inv_mul_cancel₀ (hpos τ).ne']
    have hvec : vecOf R X c y = fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) • u τ := by
      funext τ
      apply Subtype.ext
      simp only [u, Submodule.coe_smul, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hpos τ).ne', Complex.ofReal_one, one_smul]
    set a : ℂ := ∏ τ, ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) with ha
    have hphi : phi R X h t c S y = fun x => a * ev (MP R) u S
        (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) := by
      funext x
      simp only [phi, ev_apply]
      rw [hvec, S.map_smul_univ]
      rfl
    obtain ⟨hm, hi⟩ := hK u hu
    have hna : ‖a‖ = ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ := by
      rw [ha, norm_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hphi]
    refine ⟨hm.const_mul a, ?_⟩
    simp only [norm_mul, mul_pow]
    rw [integral_const_mul, hi, hna, Finset.prod_pow]
    ring

theorem evF_multilinear_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ∀ S ∈ EP R F, ∃ (f : MultilinearMap (RingHom.id ℂ) (fun τ => ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)) (L2X X)) (K : ℝ), (∀ y, f y = GlobalTheory.RowEvalHH.evF R X h t c S y) ∧ ∀ y, ‖f y‖ ^ 2 = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t c ht S hS
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.EvalNormTransfer.evalTranslate_norm R F X h hL hG hM t ht
  set K : ℝ := c0 * (ipM (MP R) R.ν0 R.fd0 S S).re with hKdef
  have hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K := fun v₀ hv =>
    ⟨(hc0 v₀ hv S hS).1, (hc0 v₀ hv S hS).2.1⟩
  have hmem : ∀ y, MemLp (phi R X h t c S y) 2 (muX X) := fun y =>
    (phi_memLp_integral R X h t c S K hK y).1
  let L : (∀ τ, Wsub R X c τ) → L2X X := fun y => (hmem y).toLp (phi R X h t c S y)
  have hL_add : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ),
      L (Function.update y τ (z₁ + z₂)) = L (Function.update y τ z₁) + L (Function.update y τ z₂) := by
    intro _ y τ z₁ z₂
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_add R X h t c S y τ z₁ z₂) x)
  have hL_smul : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ),
      L (Function.update y τ (a • z)) = (starRingEnd ℂ a) • L (Function.update y τ z) := by
    intro _ y τ a z
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_smul R X h t c S y τ a z) x)
  let f : MultilinearMap (RingHom.id ℂ) (fun τ => ↥(Wsub R X c τ)) (L2X X) :=
    { toFun := fun y => conjL (muX X) (L y)
      map_update_add' := fun y τ z₁ z₂ => by
        rw [hL_add, map_add (f := _)]
      map_update_smul' := fun y τ a z => by
        rw [hL_smul, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply, RingHom.id_apply] }
  refine ⟨f, K, fun y => ?_, fun y => ?_⟩
  · show conjL (muX X) (L y) = evF R X h t c S y
    unfold evF
    split
    · rfl
    · exact absurd (hmem y) ‹_›
  · show ‖conjL (muX X) (L y)‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map, norm_sq_toLp_eq]
    exact (phi_memLp_integral R X h t c S K hK y).2

end GlobalTheory.RowEvalHHNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ConjHol
variable {D : D7} {S T : HSp D}

theorem gram_conj_emb (C : Ctx S T) (hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ) (ρ : D.what₂.Tau)
    (M : Matrix (Fin T.rank) (Fin T.rank) ℂ) :
    FD.gram (C.m.e ρ).1 C.X.Gm (M.map (starRingEnd ℂ)) = Mᴴ * gramAt D T ρ * M := by
  ext a b
  have hh : ∀ i k, conj (gramAt D T ρ k i) = gramAt D T ρ i k := fun i k => by
    have := congrFun (congrFun (hH ρ) i) k
    rwa [Matrix.conjTranspose_apply] at this
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, C.m.e_emb, C.m.gT, Matrix.transpose_apply,
    NumberField.ComplexEmbedding.conjugate_coe_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [gramAt, Matrix.map_apply] at hh ⊢
  simp only [Complex.conj_conj, hh, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

theorem unitFr_conj_moved : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  intro D S T C B hB
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hT := _root_.GlobalTheory.Ker.onBasis_frame_period D S T C
  have hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ := fun τ => (R.1 τ).1
  refine ⟨fun a => ?_, fun y hy => ?_, fun a ha a' ha' h => ?_⟩
  · exact (hT.2 _ ((hT.2 B hB).2.2.2.2.2 a).1).1
  · let Y : C.Bas := fun ρ => (FD.mat y (C.m.e ρ)).map (starRingEnd ℂ)
    have hY : ∀ ρ, (Y ρ)ᴴ * gramAt D T ρ * Y ρ = sgnM C.X := by
      intro ρ
      rw [← gram_conj_emb C hH ρ]
      have e : (Y ρ).map (starRingEnd ℂ) = FD.mat y (C.m.e ρ) := by
        ext i j; simp [Y]
      rw [e]
      exact hy (C.m.e ρ)
    have hu : ∀ ρ, Y ρ * (B ρ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
      intro ρ
      have hd := isUnit_det_B C hB ρ
      have hd' : IsUnit (B ρ)ᴴ.det := by rw [det_conjTranspose]; exact hd.star
      show (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) = gramAt D T ρ
      have e1 : (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) =
          ((B ρ)⁻¹)ᴴ * ((Y ρ)ᴴ * gramAt D T ρ * Y ρ) * (B ρ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [e1, hY, ← hB ρ, conjTranspose_nonsing_inv]
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd', Matrix.one_mul]
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
    obtain ⟨a, ha, hau⟩ := R.2.1 (fun ρ => Y ρ * (B ρ)⁻¹) hu
    refine ⟨a, ha, ?_⟩
    have hm : ∀ ρ, C.mvB a B ρ = Y ρ := by
      intro ρ
      simp only [Ctx.mvB]
      rw [show compAt C.θ ρ (mt T a) = Y ρ * (B ρ)⁻¹ from hau ρ, Matrix.mul_assoc,
        nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
    funext σ i j
    obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
    simp only [Ctx.xB, Equiv.symm_apply_apply, hm, Y, Matrix.map_apply, Complex.conj_conj, FD.mat, Matrix.of_apply]
  · have hm : ∀ ρ, C.mvB a B ρ = C.mvB a' B ρ := by
      intro ρ
      ext i j
      have := congrFun (congrFun (congrFun h (C.m.e ρ)) i) j
      simp only [Ctx.xB, Equiv.symm_apply_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    refine R.2.2.1 a ha a' ha' fun ρ => ?_
    have e := congrArg (· * (B ρ)⁻¹) (hm ρ)
    simp only [Ctx.mvB, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_B C hB ρ), Matrix.mul_one] at e
    exact e

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombination
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjLiftHecke

variable {D : D7}

theorem theta_form_conj {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hs : S.SigOK) (hp : S.IsPosDef) {Kf : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {ν : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hν : IsMeasDef S Kf ν 𝓕) (hfix : GlobalTheory.Hk3.VacFix ψ om P) {cS cT : List ℤ →₀ ℂ}
    (hM : GlobalTheory.Hk3.Match ψ om P (GlobalTheory.Hk3.dualC cS) cT) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    (hG : ∀ k ∈ GlobalTheory.Hk3.hyp S P, k ∈ GfC S) {f f' : Bridge.Gf S → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (hsph : ∀ k ∈ GlobalTheory.Hk3.hyp S P, ∀ h, f (h * (finHom S).rangeRestrict k) = f h) (hf' : f' = GlobalTheory.Hk3.hkF S P cS f)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ φ, GlobalTheory.Hk3.IsVacAt ψ S T P (pt φ))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {u u' : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f h))) ∂ν)
    (hu' : ∀ g, u' g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f' h))) ∂ν) : u' = GlobalTheory.Hk3.hk T P cT u := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  funext g
  have key := GlobalTheory.DefLiftHecke.theta_comb hW hpos hν.1.1 hν.2 hfix hM (pt ∘ₗ io) (fun w => hpt _) (c.ext f)
    (GlobalTheory.ConjThetaIntegral.ext_continuous c hc β L χ' hχ hf) (GlobalTheory.ThetaIntegrand.ext_invariant c hf)
    (fun k hk h => by
      rw [GlobalTheory.DefLiftHecke.ext_mul c hc f (hG k hk) h, hsph k hk]
      rfl) g
  rw [hu', funext hu, hf']
  simp only [GlobalTheory.DefLiftHecke.ext_hkF c hc]
  exact key

theorem theta_right_hyp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {P : Pl D.host.E} (hfix : GlobalTheory.Hk3.VacFix ψ om P) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)}
    {φ : GA D S → (WO S T → ℂ)} (hφ : ∀ h, GlobalTheory.Hk3.IsVacAt ψ S T P (φ h)) {u : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (φ h) ∂ν) : ∀ k ∈ GlobalTheory.Hk3.hyp T P, ∀ g, u (g * k) = u g := by
  intro k hk g
  rw [hu, hu]
  refine congrArg (fun w : GA D S → ℂ => ∫ h in 𝓕, w h ∂ν) (funext fun h => ?_)
  unfold thetaKO
  rw [show ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) by simp, map_mul, Module.End.mul_apply,
    hfix _ (hφ h) 1 (GlobalTheory.DefLiftHecke.one_mem_hyp _ P) k hk]

theorem gaL_hk_of_hyp {G : Type} [Group G] [Fintype G] {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (eG : G ≃* G0 L.Pg L.r) (z : G → ℂ) (c : List ℤ →₀ ℂ) {Φ : GA D V → ℂ}
    (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    gaL V β L eG z (GlobalTheory.Hk3.hk V P c Φ) = GlobalTheory.Hk3.hk V P c (gaL V β L eG z Φ) := by
  obtain ⟨n, hB⟩ := hβ
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.LevOp.level_operators V β Λ _ L hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP
  exact GlobalTheory.DefLiftHecke.gaL_hk eG z fun g0 => h4 c g0 _ hΦ

theorem eq_of_eval {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {Hh : Type} [NormedAddCommGroup Hh]
    [InnerProductSpace ℂ Hh] (e : Hh →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) {Wa : Submodule ℂ (MMap M)} (hr : LinearMap.range e = Wa)
    (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) {a : Hh} {U : MMap M} (hU : U ∈ Wa) (h : e a v = U v) : e a = U := by
  rw [← hr] at hU
  obtain ⟨b, rfl⟩ := hU
  exact congrArg e (GlobalTheory.EvalAtUnitVector.eval_injective M Hh e d μ 𝓕 hip v hv h)

set_option maxHeartbeats 1000000 in
theorem lift_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L hT i σ c c₁ H j hK hj μ' η' th ω f₀ f B io thP hD hPr P hG hfix cV cW hM y y' hy
  have hW := hD.1
  have hV := hD.2.1
  have hIo := hD.2.2.1
  have hTh := hD.2.2.2
  refine hj.model.elim fun χ' hm => ?_
  have hχ := hm.1
  have hH := hm.2
  have hvac := _root_.GlobalTheory.ConjVacua.isVacAt_ptAt R hC.lev hC.models.inf i σ f₀ f B hV P hG
  have hform : ∀ x, H.e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).J χ' :=
    fun x => hH.2.1.le (LinearMap.mem_range_self _ x)
  have hχ1 : ∀ k, (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k = 1 → χ' k = 1 := fun k hk =>
    Units.ext (GlobalTheory.ConjThetaIntegral.conjVal_one (hχ k) (congrArg Units.val hk))
  have hsph := (GlobalTheory.ConjSph.conjForms_spherical R hC.lev i σ c c₁ H j _ hj P hG cV y).1
  refine (hC.lev.βV i).elim fun nV hBV => ?_
  have hlevV := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (R.datVt i A.μ0) hBV P
    (GlobalTheory.DefLiftHecke.one_pow_notMem P nV) hG).1
  have hStep : ∀ w : LowT (R.MW i σ), thP ((c.ext ∘ₗ H.e).rangeRestrict y') w =
      GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w) := fun w => by
    refine theta_form_conj hW (D.sp.V_sig _) (hC.models.vpos i) (hC.models.νV i A.μ0) hfix hM c hj.coef (R.βV i)
      (R.datVt i A.μ0) χ' hχ1 (fun k hk => (hlevV k hk).1.1) (hform y) hsph hy
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hvac (io w)
      (fun g => hTh.eq _ w g) (fun g => hTh.eq _ w g)
  have hWinv : ∀ (w : LowT (R.MW i σ)), ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, ∀ g,
      thP ((c.ext ∘ₗ H.e).rangeRestrict y) w (g * k) = thP ((c.ext ∘ₗ H.e).rangeRestrict y) w g := fun w =>
    theta_right_hyp hfix (fun h => hvac _) (fun g => hTh.eq _ w g)
  have hGW : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P :=
    fun PP h => hG PP (h.imp_right fun h => absurd h (Finset.notMem_empty _))
  have hcomm : ∀ w : LowT (R.MW i σ), R.eWf i σ (GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) =
      GlobalTheory.Hk3.hk (Wc D i) P cW (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) := fun w =>
    gaL_hk_of_hyp (hC.lev.βW i) hGW R.eG _ cW (hWinv w)
  have hmod := hC.models.HW i σ
  have hU : (R.HW i σ).e (th y) ∈ R.Wall i σ := hmod.2.1.le (LinearMap.mem_range_self _ _)
  have hU' : postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) ∈ R.Wall i σ :=
    (GlobalTheory.DefLiftHecke.mult_laws hC.models.inf (R.MW i σ) (hC.lev.βW i) (L := R.datWp i R.triv) hGW R.eG
      (RealDat.eC (A := A) σ) cW hU).1
  refine hIo.2.2.elim fun v hv => hv.elim fun _ hw => ?_
  refine eq_of_eval (R.MW i σ) (R.HW i σ).e _ (R.νW i) (R.fdW i) hmod.2.2 hmod.2.1 (fun ρ => v ρ) hw.1 hU' ?_
  exact (hPr y' v).trans ((congrArg (R.eWf i σ) (hStep _)).trans ((hcomm _).trans
    ((congrArg (GlobalTheory.Hk3.hk (Wc D i) P cW) (hPr y v).symm).trans (postOn_apply _ _ _ _).symm)))

end GlobalTheory.ConjLiftHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoMean

theorem isThetaFunO_bounded {D : D7} (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := hF.quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ') = ratW W V γ' := rfl
  rw [e] at hx
  have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ') x))
  have := hC _ hx
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (emb V W P Q) := by
  unfold emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_meanX : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ F hF
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : FirstCountableTopology (WO V W) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := isThetaFunO_bounded V W ψ hψ F hF
  unfold meanX
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_) (integrable_const C) ?_
  · exact (hF.cont.comp ((continuous_emb V W P Q).add continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hC _
  · exact Filter.Eventually.of_forall fun y => hF.cont.comp (continuous_const.add continuous_id)

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomains
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.NormRed

theorem sq_norm_two_haar : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  intro D V' W μ' 𝓕' hμ' hF' μ'' 𝓕'' h''
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (WO V' W) := i1
  haveI : LocallyCompactSpace (WO V' W) := i2
  haveI : SecondCountableTopology (WO V' W) := i3
  haveI : T2Space (WO V' W) := i4
  haveI : DiscreteTopology (ratL W V') := i5
  haveI : TopologicalSpace.SeparableSpace (ratL W V') := inferInstance
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : MeasurableConstVAdd (ratL W V') (WO V' W) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  obtain ⟨hμ'', hF'', -⟩ := h''
  haveI : VAddInvariantMeasure (ratL W V') (WO V' W) μ'' :=
    ⟨fun c s _ => measure_preimage_add μ'' (c : WO V' W) s⟩
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ''
  set c := Measure.addHaarScalarFactor μ' μ''
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ'').ne'
  have hac : μ'' ≪ μ' := by
    rw [e]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have hF2 : IsAddFundamentalDomain (ratL W V') 𝓕' μ'' := hF'.mono hac
  refine ⟨(c : ENNReal), fun g hg hper => ?_⟩
  have hp : ∀ (γ : ratL W V') (x : WO V' W), ‖g (γ +ᵥ x)‖ₑ ^ 2 = ‖g x‖ₑ ^ 2 := by
    intro γ x
    rw [AddSubgroup.vadd_def, vadd_eq_add]
    have h1 : ‖g ((γ : WO V' W) + x)‖₊ = ‖g x‖₊ := NNReal.eq (hper γ γ.2 x)
    simp only [enorm_eq_nnnorm, h1]
  rw [e, Measure.restrict_smul, lintegral_smul_measure, hF2.setLIntegral_eq hF'' _ hp]
  rfl

end GlobalTheory.Twist.NormRed
end

