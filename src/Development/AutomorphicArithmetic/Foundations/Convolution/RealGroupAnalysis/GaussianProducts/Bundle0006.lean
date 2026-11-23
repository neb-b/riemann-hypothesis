module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GaussSchwartz
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FockGauss
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem sq_le_qInf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ e : F →+* ℝ, e δ < 0) (v : V4 F) : ∑ w, TR.pInf F (v 1) w ^ 2 ≤ qInf δ v := by
  rw [qInf]
  refine Finset.sum_le_sum fun w _ => ?_
  have hd : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
    congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F δ) w
  have hneg := hδ (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  simp only [map_add (f := _), map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, map_ofNat, Pi.ofNat_apply, hd]
  have h3 : 0 ≤ -(InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ) * TR.pInf F (v 3) w ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [sq_nonneg (TR.pInf F (v 0) w), sq_nonneg (TR.pInf F (v 2) w)]

private theorem exp_le_gauss {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ e : F →+* ℝ, e δ < 0) (R : ℝ) (v : V4 F) :
    Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * Real.exp (-(Real.pi / 2) * qInf δ v) ≤
      Real.exp (∑ _w : InfinitePlace F, R ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hq := sq_le_qInf δ hδ v
  have hs : 0 ≤ ∑ w, TR.pInf F (v 1) w ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have h1 : ∑ w, TR.pInf F (v 1) w ^ 2 ≤ Real.pi / 2 * qInf δ v := by nlinarith
  have h2 : R * ∑ w, |TR.pInf F (v 1) w| ≤ ∑ w, TR.pInf F (v 1) w ^ 2 + ∑ _w : InfinitePlace F, R ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have h := sq_abs (TR.pInf F (v 1) w)
    nlinarith [sq_nonneg (|TR.pInf F (v 1) w| - R), sq_nonneg R, sq_nonneg (|TR.pInf F (v 1) w|)]
  linarith

theorem UpperTheory.ConvolutionTheory.R2.G.fockGauss :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ χ ∈ FockFn δ, ∀ (R : ℝ) (N : ℕ), ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧
    ∀ v, Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖χ v‖ ≤ B * wt4 L N v := by
  intro F _ _ _ δ hδ χ hχ
  induction hχ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨p, hp, g, hg, rfl⟩ := h
    intro R N
    have hmem := UpperTheory.ConvolutionTheory.R2.G.pgMem F δ hδ (Real.pi / 2) (by positivity) p hp g hg
    obtain ⟨M, L, hM, hb⟩ := GlobalTheory.CompanionTheory.EpConvB.exists_majorant hmem (C := {1}) isCompact_singleton N
    refine ⟨Real.exp (∑ _w : InfinitePlace F, R ^ 2) * M, L, mul_nonneg (Real.exp_pos _).le hM, fun v => ?_⟩
    have h1 := hb 1 rfl v
    rw [Units.val_one, Matrix.one_mulVec] at h1
    have hsplit : ‖p v * gauss δ v * g (finPartPi v)‖ =
        Real.exp (-(Real.pi / 2) * qInf δ v) *
          ‖p v * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)‖ := by
      have hg2 : ‖gauss δ v‖ = Real.exp (-(Real.pi / 2) * qInf δ v) * Real.exp (-(Real.pi / 2) * qInf δ v) := by
        rw [gauss_eq, ← Real.exp_add, Complex.norm_exp]
        congr 1
        simp
        ring
      have hg3 : ‖Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ))‖ = Real.exp (-(Real.pi / 2) * qInf δ v) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      simp only [norm_mul, hg2, hg3]
      ring
    rw [hsplit, ← mul_assoc]
    calc _ ≤ Real.exp (∑ _w : InfinitePlace F, R ^ 2) *
          ‖p v * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)‖ :=
          mul_le_mul_of_nonneg_right (exp_le_gauss δ hδ R v) (norm_nonneg _)
      _ ≤ Real.exp (∑ _w : InfinitePlace F, R ^ 2) * (M * wt4 L N v) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := by ring
  | zero =>
    intro R N
    exact ⟨0, 1, le_rfl, fun v => by simp⟩
  | add f g _ _ hf hg =>
    intro R N
    obtain ⟨B₁, L₁, h₁, hb₁⟩ := hf R N
    obtain ⟨B₂, L₂, h₂, hb₂⟩ := hg R N
    have hmono : ∀ {L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ},
        (L' : FractionalIdeal (𝓞 F)⁰ F) ≤ (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) →
        ∀ v : V4 F, wt4 L' N v ≤ wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v := fun h v =>
      Finset.prod_le_prod₀ (fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _)
        fun i _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_mono h N _
    refine ⟨B₁ + B₂, GroundTheory.Global.fractionalIdealSupUnit L₁ L₂, add_nonneg h₁ h₂, fun v => ?_⟩
    have he := (Real.exp_pos (R * ∑ w, |TR.pInf F (v 1) w|)).le
    calc Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖(f + g) v‖
        ≤ Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * (‖f v‖ + ‖g v‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) he
      _ = Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖f v‖ + Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖g v‖ := by ring
      _ ≤ B₁ * wt4 L₁ N v + B₂ * wt4 L₂ N v := add_le_add (hb₁ v) (hb₂ v)
      _ ≤ B₁ * wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v + B₂ * wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (hmono le_sup_left v) h₁)
            (mul_le_mul_of_nonneg_left (hmono le_sup_right v) h₂)
      _ = _ := by ring
  | smul r f _ hf =>
    intro R N
    obtain ⟨B, L, hB, hb⟩ := hf R N
    refine ⟨‖r‖ * B, L, by positivity, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg r)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatSurj
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective

variable {F : Type} [Field F] [NumberField F]

private def rf {R : Type} [Neg R] (v : Fin 4 → R) : Fin 4 → R := Function.update v 1 (-v 1)

private theorem rf_rf {R : Type} [InvolutiveNeg R] (v : Fin 4 → R) : rf (rf v) = v := by
  funext i
  by_cases h : i = 1
  · subst h
    simp [rf]
  · simp [rf, h]

private theorem rf_ne {R : Type} [Neg R] (v : Fin 4 → R) {i : Fin 4} (h : i ≠ 1) : rf v i = v i := by
  simp [rf, h]

private theorem rf_one {R : Type} [Neg R] (v : Fin 4 → R) : rf v 1 = -v 1 := by
  simp [rf]

private def rfH (R : Type) [TopologicalSpace R] [AddGroup R] [IsTopologicalAddGroup R] :
    (Fin 4 → R) ≃ₜ (Fin 4 → R) where
  toFun := rf
  invFun := rf
  left_inv := rf_rf
  right_inv := rf_rf
  continuous_toFun := continuous_id.update 1 (continuous_apply 1).neg
  continuous_invFun := continuous_id.update 1 (continuous_apply 1).neg

private theorem fin_rf {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun z => g (rf z)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  exact (mem_finiteSchwartzBruhatPi F).2
    ⟨h1.comp_continuous (rfH _).continuous, h2.comp_homeomorph (rfH _)⟩

private theorem finPart_rf (v : V4 F) : finPartPi (rf v) = rf (finPartPi v) := by
  funext i
  by_cases h : i = 1
  · subst h
    rw [rf_one]
    change (finPartPi (rf v)) 1 = -(finPartPi v 1)
    simp only [GroundTheory.Heights₂.Theta.finPartPi_eq_adeleFinHom, rf_one, map_neg]
  · rw [rf_ne _ h]
    change (rf v i).2 = (v i).2
    rw [rf_ne _ h]

private theorem poly_rf [IsTotallyReal F] {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    (fun v => p (rf v)) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, w, rfl⟩ := hp
    by_cases h : i = 1
    · subst h
      have e : (fun v : V4 F => ((TR.pInf F (rf v 1) w : ℝ) : ℂ)) =
          (-1 : ℂ) • (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) := by
        funext v
        simp [rf_one]
      have hm : (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) :=
        Algebra.subset_adjoin ⟨1, w, rfl⟩
      rw [e]
      exact Subalgebra.smul_mem _ hm _
    · have e : (fun v : V4 F => ((TR.pInf F (rf v i) w : ℝ) : ℂ)) =
          (fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) := by
        funext v
        rw [rf_ne _ h]
      rw [e]
      exact Algebra.subset_adjoin ⟨i, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add p q _ _ hp hq => exact add_mem hp hq
  | mul p q _ _ hp hq => exact mul_mem hp hq

private theorem gauss_rf [IsTotallyReal F] (δ : F) (v : V4 F) : gauss δ (rf v) = gauss δ v := by
  have h0 : rf v 0 = v 0 := rf_ne _ (by decide)
  have h2 : rf v 2 = v 2 := rf_ne _ (by decide)
  have h3 : rf v 3 = v 3 := rf_ne _ (by decide)
  simp only [gauss, h0, h2, h3, rf_one, neg_sq]

private theorem fock_rf [IsTotallyReal F] {δ : F} {χ : V4 F → ℂ} (hχ : χ ∈ FockFn δ) :
    (fun v => χ (rf v)) ∈ FockFn δ := by
  induction hχ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, poly_rf hp, _, fin_rf hg, ?_⟩
    funext v
    simp only [gauss_rf, finPart_rf]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

private theorem fock_le [IsTotallyReal F] {δ : F} (hδ : ∀ e : F →+* ℝ, e δ < 0) {χ : V4 F → ℂ}
    (hχ : χ ∈ FockFn δ) : χ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  refine (Submodule.span_le.2 ?_) hχ
  rintro _ ⟨p, hp, g, hg, rfl⟩
  have h := pgMem F δ hδ Real.pi Real.pi_pos p hp g hg
  change _ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)
  simpa only [gauss_eq] using h

end UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective

open UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective in
theorem UpperTheory.ConvolutionTheory.R2.G.hatSurj :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ χ ∈ FockFn δ, ∃ φ ∈ Fock δ, hat φ.1 = χ := by
  intro F _ _ _ δ hδ χ hχ
  have h1 := fock_rf hχ
  have h2 := hatFock F δ _ h1
  refine ⟨⟨hat fun v => χ (rf v), fock_le hδ h2⟩, h2, ?_⟩
  funext v
  exact (hatInv F ⟨fun v => χ (rf v), fock_le hδ h1⟩ v).trans (congrArg χ (rf_rf v))
end

