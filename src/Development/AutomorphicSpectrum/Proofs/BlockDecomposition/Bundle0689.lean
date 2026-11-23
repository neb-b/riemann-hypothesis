module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

def phiA (G : Ainf F → ℝ) (a : (AF F)ˣ) : (Unit → Ainf F) → ℝ := fun y => G ((a : AF F).1 * y ())

def psiA (S : Finset (HeightOneSpectrum (𝓞 F))) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (Unit → Fv F v) → ℝ := fun y =>
  if v ∈ S then g v ((a : AF F).2 v * y ())
  else if (a : AF F).2 v * y () ∈ v.adicCompletionIntegers F then 1 else 0

theorem md_mul (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_pos (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem md_pr (t : Fˣ) : md (pr t) = 1 := by
  have h := IdeleGroup.ideleModule_diagonal (K := F) t
  have h2 : pr t = IdeleGroup.diagonal F t := rfl
  rw [md, h2, h]
  rfl

theorem th_pr (f : (AF F)ˣ → ℝ≥0∞) (k : Fˣ) (a : (AF F)ˣ) : th f (pr k * a) = th f a := by
  unfold th
  rw [← (Equiv.mulRight k).tsum_eq (fun t : Fˣ => f (pr t * a))]
  refine tsum_congr fun t => ?_
  have : pr (t * k) = pr t * pr k := by simp [pr, map_mul]
  simp only [Equiv.coe_mulRight, this, mul_assoc]

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesSiegelBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilMaj

theorem schwartz_col_bound {T : Type} [Fintype T] {M n : ℕ} (f : SchwartzMap (T → Fin M → Fin n → ℂ) ℂ)
    (P : ℝ) (hP : 1 ≤ P) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : T → Fin M → Fin n → ℂ, ‖b‖ ≤ P * ‖a‖ →
      ‖f a‖ ≤ C * ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
  obtain ⟨C0, hC0, hC0'⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ a, (1 + ‖a‖) ^ (N * n) * ‖f a‖ ≤ C0 := by
    refine ⟨(2 : ℝ) ^ (N * n, 0).1 * ((Finset.Iic (N * n, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f,
      by positivity, fun a => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N * n, 0)) (k := N * n) (n := 0)
      le_rfl le_rfl f a
    simpa using h
  refine ⟨C0 * P ^ (N * n), by positivity, fun a b hab => ?_⟩
  have hP0 : 0 < P := by linarith
  have ha : 0 < 1 + ‖a‖ := by positivity
  have hb : 0 < 1 + ‖b‖ := by positivity
  have h1 : 1 + ‖b‖ ≤ P * (1 + ‖a‖) := by nlinarith [norm_nonneg a]
  have hcol : ∀ j, ‖fun τ i => b τ i j‖ ≤ ‖b‖ := fun j => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact (norm_le_pi_norm (b τ i) j).trans ((norm_le_pi_norm (b τ) i).trans (norm_le_pi_norm b τ))
  have h2 : ((1 + ‖b‖) ^ (N * n))⁻¹ ≤ ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
    have e : ((1 + ‖b‖) ^ (N * n))⁻¹ = ∏ _j : Fin n, ((1 + ‖b‖) ^ N)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, pow_mul]
    rw [e]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
    have : 0 < 1 + ‖fun τ i => b τ i j‖ := by positivity
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ this.le ?_ N)
    linarith [hcol j]
  have h3 : ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hC0' a
  have h4 : ((1 + ‖a‖) ^ (N * n))⁻¹ ≤ P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow, mul_comm (1 + ‖a‖)]
    exact pow_le_pow_left₀ hb.le h1 _
  calc ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := h3
    _ ≤ C0 * (P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹) := by gcongr
    _ = C0 * P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by ring
    _ ≤ _ := by gcongr

variable {D : D7}

theorem mt_mul_inv (V : HSp D) (y : GA D V) :
    (HMul.hMul (Formalism.L2.Theta.mt V y) (Formalism.L2.Theta.mt V y⁻¹) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  have h : (Formalism.L2.Theta.matHom V y) * (Formalism.L2.Theta.matHom V y⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg Units.val h

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = HMul.hMul (compAt θ τ x) (compAt θ τ y) :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem real_compare {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ ≤
        P * ‖(fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j :
          D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ := by
  let B : GA D V → (D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) := fun y τ i k => compAt θ τ (Formalism.L2.Theta.mt V y) i k
  have hB : Continuous B := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_
    exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp (GlobalTheory.RealWeil.continuous_mt V).1).matrix_elem i k
  obtain ⟨R, hR⟩ := hC₁.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨1 + V.rank * |R|, by have := abs_nonneg R; nlinarith [Nat.cast_nonneg (α := ℝ) V.rank, mul_nonneg (Nat.cast_nonneg (α := ℝ) V.rank) (abs_nonneg R)], fun y hy x => ?_⟩
  set u : D.what₂.Tau → Fin V.rank → Fin n → ℂ :=
    fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j with hu
  have hx : ∀ τ, compAt θ τ x = HMul.hMul (compAt θ τ (Formalism.L2.Theta.mt V y))
      (compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)) := fun τ => by
    rw [← compAt_mul', ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have hN : 0 ≤ (1 + V.rank * |R|) * ‖u‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hN).2 fun τ => (pi_norm_le_iff_of_nonneg hN).2 fun i =>
    (pi_norm_le_iff_of_nonneg hN).2 fun j => ?_
  rw [hx τ, Matrix.mul_apply]
  have hk : ∀ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ |R| * ‖u‖ := fun k => by
    rw [norm_mul]
    have e1 : ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k‖ ≤ |R| :=
      ((norm_le_pi_norm (B y τ i) k).trans ((norm_le_pi_norm (B y τ) i).trans (norm_le_pi_norm (B y) τ))).trans
        ((hR y hy).trans (le_abs_self R))
    have e2 : ‖compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ ‖u‖ :=
      (norm_le_pi_norm (u τ k) j).trans ((norm_le_pi_norm (u τ) k).trans (norm_le_pi_norm u τ))
    exact mul_le_mul e1 e2 (norm_nonneg _) (abs_nonneg _)
  calc _ ≤ ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin V.rank, |R| * ‖u‖ := Finset.sum_le_sum fun k _ => hk k
    _ = V.rank * |R| * ‖u‖ := by simp [Finset.sum_const, mul_assoc]
    _ ≤ _ := by nlinarith [norm_nonneg u]


set_option synthInstance.maxHeartbeats 400000 in
theorem finite_compare (V : HSp D) (n : ℕ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) ≠ 0 →
        ∀ j, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L := by
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hS : IsCompact (tsupport g) := hg.2
  let Φ : GA D V × (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun p i j => ∑ k, finPart D (Formalism.L2.Theta.mt V p.1 i k) * p.2 k j
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ => ?_
    refine Continuous.mul ?_ ?_
    · exact GlobalTheory.SchwartzSch.continuous_finPart'.comp
        (((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_fst).matrix_elem i k)
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_snd)
  have hK := (hC₁.prod hS).image hΦ
  let col : Fin n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun j w => Matrix.of fun i' _ => w i' j
  have hcol : ∀ j, Continuous (col j) := fun j =>
    continuous_pi fun i => continuous_pi fun _ => (continuous_apply j).comp (continuous_apply i)
  refine ⟨⋃ j, col j '' (Φ '' (C₁ ×ˢ tsupport g)), isCompact_iUnion fun j => hK.image (hcol j),
    fun y hy x hne j => Set.mem_iUnion.2 ⟨j, fun i j => finPart D (x i j),
      ⟨(y, fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)),
        ⟨hy, subset_tsupport _ hne⟩, ?_⟩, rfl⟩⟩
  funext i j
  have e : (HMul.hMul (Formalism.L2.Theta.mt V y) (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) : Mx D V.rank n) = x := by
    rw [← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.mul_apply] at e2
  show ∑ k, finPart D (Formalism.L2.Theta.mt V y i k) * finPart D _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e2, map_sum]
  exact Finset.sum_congr rfl fun k _ => ((finPart D).map_mul _ _).symm

theorem schwartz_translate_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ∀ (C₁ : Set (GA D V)), IsCompact C₁ → ∀ N : ℕ, ∃ (C : ℝ) (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n, ‖f (fun τ i j => compAt θ τ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j) * g (fun i j => finPart D ((HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j))‖ₑ ≤ ENNReal.ofReal C * ∏ j : Fin n, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))) := by
  intro D θ hθ V n f g hg C₁ hC₁ N
  obtain ⟨P, hP, hPx⟩ := real_compare hθ V n C₁ hC₁
  obtain ⟨C, hC, hf⟩ := schwartz_col_bound f P hP N
  obtain ⟨L, hL, hLx⟩ := finite_compare V n g hg C₁ hC₁
  obtain ⟨G, hG⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  refine ⟨C * |G|, L, hL, fun y hy x => ?_⟩
  by_cases h0 : g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) = 0
  · have e : ∀ a : ℂ, ‖a * g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j))‖ₑ = 0 := fun a => by
      rw [h0, mul_zero, enorm_zero]
    exact (e _).le.trans zero_le
  · have hm := hLx y hy x h0
    have hb := hf _ _ (hPx y hy x)
    have hterm : ∀ j : Fin n, 0 ≤ ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ *
        Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) := fun j => by
      rw [Set.indicator_of_mem (hm j)]
      positivity
    rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => hterm j,
      ← ENNReal.ofReal_mul (mul_nonneg hC (abs_nonneg G)), ← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.indicator_of_mem (hm _), mul_one]
    rw [norm_mul]
    calc _ ≤ (C * ∏ j : Fin n, ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹) * |G| :=
          mul_le_mul hb ((hG _).trans (le_abs_self G)) (norm_nonneg _)
            (mul_nonneg hC (Finset.prod_nonneg fun j _ => by positivity))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.WeilMaj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolume
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  intro F E _ _ _ _ _ σ hσ M d b v lam hlam u S hS
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  haveI := hW 1 M
  haveI : (coordW (Fv F v) b lam 1 M).Regular := by
    let K : TopologicalSpace.PositiveCompacts (Fin 1 → Fin M → Fv F v ⊗[F] E) := Classical.choice inferInstance
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_ne_top
  have hchar : distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    let bE := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    let e : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
      { bE.equivFun.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.symm.toLinearMap }
    borelize (Fv F v ⊗[F] E)
    set A := Algebra.leftMulMatrix bE (u : Fv F v ⊗[F] E)
    have hdet : A.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det bE _).symm
    have hA : IsUnit A.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
    have hN : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hA).ne_zero
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
    have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport e.symm (GlobalTheory.ModuLR.mulVecCE A hA)
    have hext : ((e.symm.symm.trans (GlobalTheory.ModuLR.mulVecCE A hA)).trans e.symm) = GlobalTheory.ModuNorm.mulUnitCE u := by
      ext x
      show bE.equivFun.symm (Matrix.mulVec A (bE.equivFun x)) = (u : Fv F v ⊗[F] E) * x
      rw [show Matrix.mulVec A (bE.equivFun x) = bE.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr bE _ x, LinearEquiv.symm_apply_apply]
    rw [hext] at ht
    rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu, dite_eq_left (hdet ▸ hA)]
    convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN using 2
    exact Units.ext rfl
  let U1 : (Fin M → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin M) (Fv F v ⊗[F] E)).toMonoidHom u
  let U : (Fin 1 → Fin M → Fv F v ⊗[F] E)ˣ :=
    Units.map (Pi.constRingHom (Fin 1) (Fin M → Fv F v ⊗[F] E)).toMonoidHom U1
  have hc1 : distribHaarChar (Fin M → Fv F v ⊗[F] E) U1 = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin M => Fv F v ⊗[F] E) U1]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin M => Fv F v ⊗[F] E) i).toMonoidHom U1 = u :=
      fun i => Units.ext rfl
    simp only [hU, hchar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) U]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) i).toMonoidHom U = U1 :=
      fun i => Units.ext rfl
    simp only [hU, hc1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  have hm : coordW (Fv F v) b lam 1 M ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X) '' S) =
      distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U * coordW (Fv F v) b lam 1 M S := by
    open scoped Pointwise in
    exact (distribHaarChar_mul (coordW (Fv F v) b lam 1 M) U S).symm
  have himg : (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) =
      fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X := rfl
  rw [himg, hm, hc]
  push_cast
  rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompact
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

open GlobalTheory.CompanionTheory.KFin Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem matHom_mapH_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 =
      (matHom A σ J g).1.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  ext i j
  exact GlobalTheory.AutFunCompare.mat_mapH _ _ _ _ _ _

theorem map_adMat_kfin {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (X : Matrix (Fin n) (Fin r) E) :
    (X.map (inclR (F := F) A)).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = X.map (inclR (F := F) A') := by
  ext i j
  simp [inclR]

theorem flag_map_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E))
    (h : (matHom A σ J g).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 * X.map (inclR (F := F) A') =
      X.map (inclR (F := F) A') * B.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin r) (A ⊗[F] E) =>
    M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) h
  rw [Matrix.map_mul, Matrix.map_mul, map_adMat_kfin] at this
  rw [matHom_mapH_kfin]
  exact this

theorem exists_compact_iwasawa_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW
  let L₀ := stdLattice E n
  haveI : Submodule.IsFullLattice E L₀ := isLattice_stdLattice
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2, star_star])
  have hae : ∀ᶠ v in cofinite,
      IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v) := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
      eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
      with v h1 h2 h3 h4 h5
    exact AE.isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5
  have hT : ∀ v, FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) := fun v => _root_.GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive _ _ (_root_.GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc hCM v) (_root_.GlobalTheory.CompanionTheory.KFin.Base.hasBase_place hCM v)
  have hex : ∀ v, ∃ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E),
      IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ ∧
      (IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v) → Λ = latLoc F L₀ v) := by
    intro v
    by_cases hg : IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v)
    · exact ⟨_, hg.1, hg.2, fun _ => rfl⟩
    · obtain ⟨L, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted _ (intLoc F E v) (_root_.GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc hCM v) (hR (Fv F v) σ J) (_root_.GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR hCM hJ v).1
        (_root_.GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR hCM hJ v).2 (colV v X) (colV v Y) (_root_.GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV hCM hJ hW v)
      exact ⟨L, h1, h2, fun h => absurd h hg⟩
  choose Λ hΛ1 hΛ2 hΛ3 using hex
  have hev : ∀ᶠ v in cofinite, Λ v = latLoc F L₀ v := hae.mono fun v h => hΛ3 v h
  have hstab : ∀ v, Λ v = latLoc F L₀ v → (stabLat σ J (Λ v) : Subgroup (GLoc σ J v)) = stabLoc σ J L₀ v := by
    intro v e
    rw [e]
    rfl
  let K : Subgroup (GAd σ J) := finPts σ J ⊓ ⨅ v, (stabLat σ J (Λ v)).comap (proj σ J v)
  have memK : ∀ g, g ∈ K ↔ g ∈ finPts σ J ∧ ∀ v, proj σ J v g ∈ stabLat σ J (Λ v) := fun g => by
    simp [K, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨K, inf_le_left, ?_, ?_, ?_⟩
  ·
    obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Λ v = latLoc F L₀ v :=
      ⟨(eventually_cofinite.1 hev).toFinset, fun v hv => by simpa using hv⟩
    have hc := (isRestrGroup_GFin σ J L₀).isCompact_cyl S (fun _ => Set.univ)
      (fun v => (stabLat σ J (Λ v) : Set (GLoc σ J v))) (fun e => e.elim)
      (fun v _ => _root_.GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat hCM hJ v (Λ v) (hΛ1 v).1)
    convert hc.image (continuous_ofFin σ J) using 1
    ext g
    rw [SetLike.mem_coe, memK]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ : g ∈ (ofFin σ J).range := by rwa [range_ofFin]
      refine ⟨y, ⟨fun e => e.elim, fun v _ => ?_, fun v hv => ?_⟩, rfl⟩
      · simpa using h2 v
      · rw [← hstab v (hS v hv)]
        simpa using h2 v
    · rintro ⟨y, ⟨-, h1, h2⟩, rfl⟩
      refine ⟨mem_finPts.2 (by simp), fun v => ?_⟩
      rw [proj_ofFin]
      by_cases hv : v ∈ S
      · exact h1 v hv
      · rw [hstab v (hS v hv)]
        exact h2 v hv
  ·
    intro g hg
    have hfin : {v | proj σ J v g ∉ stabLat σ J (Λ v)}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [hev, eventually_proj_mem_stabLoc σ J L₀ g] with v e hv
      rw [hstab v e]
      exact hv
    let S : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
    choose pl kl hkl hgl Bl hBl hpl using fun v => GlobalTheory.T.max_even_lattice_flag_transitive_local (X := X) hCM hJ hW v (hT v) (Λ v) (hΛ1 v) (proj σ J v g)
    let x : ∀ v : S, GLoc σ J v := fun v => pl v
    have hp1 : embAt σ J S x ∈ minPar σ J X := by
      have : embAt σ J S x ∈ minParSub X hCM hJ hW := by
        refine Subgroup.noncommProd_mem _ (f := fun v : S => emb σ J v (x v))
          (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => ?_
        exact GlobalTheory.T.block_triangular_mem_minimal_parabolic_local (Y := Y) v.1 _ (Bl v.1) (hBl v.1) (hpl v.1)
      exact this
    have hp2 := mem_atPts.1 (embAt_mem σ J S x)
    refine ⟨embAt σ J S x, hp1, hp2.1, (embAt σ J S x)⁻¹ * g, (memK _).2 ⟨mul_mem (inv_mem hp2.1) hg, fun v => ?_⟩, by simp⟩
    rw [map_mul, map_inv]
    by_cases hv : v ∈ S
    · have : proj σ J v (embAt σ J S x) = pl v := proj_embAt σ J S x ⟨v, hv⟩
      rw [this, hgl v, inv_mul_cancel_left]
      exact hkl v
    · rw [hp2.2 v hv, inv_one, one_mul]
      by_contra hc
      exact hv (hfin.mem_toFinset.2 hc)
  ·
    rintro p ⟨B, hB, hpB⟩ hpK
    obtain ⟨hpf, hpv⟩ := (memK p).1 hpK
    obtain ⟨m, hm, ⟨d, hd⟩, ⟨d', hd'⟩, ⟨B', hB', hB1, hu⟩, hz⟩ := GlobalTheory.T.block_triangular_mem_minimal_parabolic hCM hJ hW (AF F) p B hB hpB
    have hmf : m ∈ finPts σ J := by
      refine mem_finPts.2 (Subtype.ext (Units.ext ?_))
      have e1 : (matHom _ σ J (projInf σ J m)).1 = 1 := by
        refine (matHom_mapH_kfin (fstA F) m).trans ?_
        rw [hm, ← _root_.GlobalTheory.CompanionTheory.KFin.leviMat_map]
        have e2 : (matHom _ σ J p).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
          rw [← matHom_mapH_kfin]
          have := mem_finPts.1 hpf
          change (matHom _ σ J (projInf σ J p)).1 = 1
          rw [this, map_one]
          rfl
        rw [e2]
        exact _root_.GlobalTheory.CompanionTheory.KFin.LeviOne.leviMat_one hCM hJ hW _
      exact e1
    have hmK : m ∈ K := by
      refine (memK m).2 ⟨hmf, fun v => ?_⟩
      refine GlobalTheory.T.max_even_lattice_adapted_basis hCM hJ hW v (Λ v) (hΛ1 v) (hΛ2 v) (proj σ J v p) (proj σ J v m) (hpv v) _
        (hB.map _) (flag_map_kfin (evFin F v) p B hpB) ?_
      refine (matHom_mapH_kfin (evFin F v) m).trans ?_
      rw [hm, ← _root_.GlobalTheory.CompanionTheory.KFin.leviMat_map, ← matHom_mapH_kfin]
      rfl
    refine ⟨m, ⟨d, d', hd, ?_⟩, hmK, m⁻¹ * p, ⟨B', hB', hB1, hu, fun z hz' => ?_⟩, mul_mem (inv_mem hmK) hpK, by simp⟩
    · exact hd'
    · refine hz _ ?_
      funext i
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) (cT (σ : E →+* E) X * J) z i).symm.trans ?_
      rw [hz']
      simp

end GlobalTheory.CompanionTheory.KFin

end
end

