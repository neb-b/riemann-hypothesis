module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.CurveField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_periodPair (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ L : PeriodPair, ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s := by
  have hd : 7 ≤ H.d := by have := H.d_mod; omega
  have hs : √(H.d : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < H.d))).ne'
  refine ⟨⟨1, (1 + Complex.I * Real.sqrt H.d) / 2, LinearIndependent.pair_iff.2 fun a b h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hs] at h1 h2
    simp [h2] at h1
    exact ⟨h1, h2⟩
  · rw [GlobalTheory.CompRat.Weber.exists_wC_iff, PeriodPair.mem_lattice]
    simp only [_root_.mul_one]
    exact ⟨fun ⟨m, n, e⟩ => ⟨m, n, e.symm⟩, fun ⟨m, n, e⟩ => ⟨m, n, e.symm⟩⟩

theorem actsBy_of_dvd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (C : Curve H) (τ : ℂ ≃+* ℂ) (ι : _) {n m : ℕ}
    (hn : 0 < n) (hm : m ∣ n) (s : ℤ × ℤ) (h : C.ActsBy τ ι n s) : C.ActsBy τ ι m s := by
  obtain ⟨k, rfl⟩ := hm
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left hn).ne'
  have e : ∀ a : ℤ × ℤ, wC H (k * a.1, k * a.2) = k * wC H a := fun a => by
    simp only [wC]; push_cast; ring
  refine ⟨h.1, fun a => ?_⟩
  have h2 := h.2 (k * a.1, k * a.2)
  rw [e, Nat.cast_mul, mul_left_comm, mul_comm (m : ℂ), mul_div_mul_left _ _ hk, mul_div_mul_left _ _ hk] at h2
  exact h2

theorem curveOver_of_weberIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (F : IntermediateField ℚ ℂ) (n : ℕ), 0 < n → (H.rt0 ∈ F → WeberIn H F n → CurveOver H F n) ∧ ∀ m, m ∣ n → CurveOver H F n → CurveOver H F m := by
  intro E _ _ _ H F n hn
  refine ⟨fun h0 hW τ hτ => ?_, fun m hm h τ hτ => ?_⟩
  · obtain ⟨L, hL⟩ := exists_periodPair H
    exact GlobalTheory.CompRat.Weber.fixesCurve_of_weber E H L n hn hL τ (hτ _ h0) (hτ _ (hW L hL).1)
      fun s hs => hτ _ ((hW L hL).2 s hs)
  · obtain ⟨C, ι, h'⟩ := h τ hτ
    exact ⟨C, ι, actsBy_of_dvd C τ ι hn hm _ h'⟩

end GlobalTheory.FinalJoin.CurveField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosLowerBoundSections
section
noncomputable section

namespace GlobalTheory.BignessCompare

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)


end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}






end Inst

end GlobalTheory.BignessCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem weberSet_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : weberSet L n = weberSet L' n := by
  have hG : ∀ k, L.G k = L'.G k := fun k => by unfold PeriodPair.G; rw [h]
  have h2 : L.g₂ = L'.g₂ := by unfold PeriodPair.g₂; rw [hG]
  have h3 : L.g₃ = L'.g₃ := by unfold PeriodPair.g₃; rw [hG]
  have hP : ∀ z, L.weierstrassP z = L'.weierstrassP z := fun z => by unfold PeriodPair.weierstrassP; rw [h]
  unfold weberSet
  simp only [h2, h3, hP, h]

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier
open MeasureTheory Matrix Formalism.REAL GlobalTheory.TypeSum

variable {n : ℕ}

theorem rder_mem (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d) (l : List (Mx n))
    (hl : ∀ X ∈ l, inK ε X) : rder ε l φ ∈ polyV ε d := by
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    have h := (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε d _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)).1
    exact h

theorem hs_mul_toMK (ε : Fin n → Bool) (y : Mx n) (k : KG ε) : hs (y * toMK k) = hs y :=
  ((hermitian_small_ball n ε).2 y _ k.2).1

theorem toMK_expK_mul (ε : Fin n → Bool) (X : Mx n) (hK : inK ε X) (t : ℝ) (x : KG ε) :
    toMK (expK ε X t * x) = NormedSpace.exp (t • X) * toMK x := by
  rw [toMK_mul, toMK_expK hK, Complex.coe_smul]

theorem summable_listSum {ι : Type} (U : List ι) (b : ι → ℕ → ℝ) (hb : ∀ u ∈ U, Summable (b u)) :
    Summable fun i => (U.map fun u => b u i).sum := by
  induction U with
  | nil => simp
  | cons u U ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hb u List.mem_cons_self).add (ih fun v hv => hb v (List.mem_cons_of_mem _ hv))

theorem exists_rightKFourier : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  intro n ε
  have hker : ∀ i, IsKer ε i (kerE ε i) := fun i => isKer_kerE (GlobalTheory.T.exists_compactUnitary_fourierKernel ε i)
  refine ⟨kerE ε, fun i => continuous_of_mem (hker i).1, fun i => kFinFun_of_mem (hker i).1, ?_⟩
  intro f hf hU
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  have hcF : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hdec : ∀ u : List (Mx n), ∃ b : ℕ → ℝ, Summable b ∧ ((∀ X ∈ u, inK ε X) → ∀ i, ∀ y ∈ UJset ε,
      ‖∫ k, kerE ε i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N) := by
    intro u
    by_cases hu : ∀ X ∈ u, inK ε X
    · obtain ⟨b, hb, hb'⟩ := _root_.GlobalTheory.KFourier.kFourier_coeff_decay ε N F hFd hFg hcF (kerE ε) hker u hu
      exact ⟨b, hb, fun _ => hb'⟩
    · exact ⟨0, summable_zero, fun h => absurd h hu⟩
  choose b hbs hbb using hdec
  choose U C hC0 hUK hC using _root_.GlobalTheory.KFourier.rder_bound_basisWords ε
  have hQ : ∀ i, ∀ y ∈ UJset ε, avgK ε (kerE ε i) f y ∈ polyV ε i := fun i y hy =>
    _root_.GlobalTheory.KFourier.avgK_mem ε i _ (hker i).1 f hf y hy
  have hbound : ∀ i m (w : List (Mx n)), w.length ≤ m → (∀ X ∈ w, X ∈ GlobalTheory.SmoothGlob.lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖rder ε w (avgK ε (kerE ε i) f y) 1‖ ≤ C m * ((U m).map fun u => b u i).sum * (1 + hs y) ^ N := by
    intro i m w hw hwX y hy
    have hwK : ∀ X ∈ w, inK ε X ∧ hs X ≤ 1 := fun X hX =>
      ⟨inK_of_skew (hwX X hX).1 (hwX X hX).2.1, (hwX X hX).2.2⟩
    have h1 := hC m i _ (hQ i y hy) w hw hwK
    have h2 : ((U m).map fun u => ‖rder ε u (avgK ε (kerE ε i) f y) 1‖).sum ≤
        ((U m).map fun u => b u i * (1 + hs y) ^ N).sum := by
      refine List.sum_le_sum fun u hu => ?_
      rw [GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq ε N F hFd hFg f hf hF0 _ (continuous_of_mem (hker i).1) (_root_.GlobalTheory.KFourier.isKer_class ε i _ (hker i)) u (hUK m u hu) y hy]
      exact hbb u (hUK m u hu) i y hy
    rw [List.sum_map_mul_right] at h2
    calc _ ≤ _ := h1
      _ ≤ C m * (((U m).map fun u => b u i).sum * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_left h2 (hC0 m)
      _ = _ := by ring
  refine ⟨N, fun i l y => rder ε l (avgK ε (kerE ε i) f y) 1,
    fun i m => C m * ((U m).map fun u => b u i).sum, ?_, ?_, hbound, ?_, ?_⟩
  · intro i y hy
    simp [avgK, toMK_one]
  · intro i l hl X hX hXs y hy
    have hK := inK_of_skew hX hXs
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => inK_of_skew (hl Y hY).1 (hl Y hY).2
    have hR := rder_mem ε i _ (hQ i y hy) l hlK
    have e1 : (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1) =
        fun t : ℝ => rder ε l (avgK ε (kerE ε i) f y) (1 * expK ε X t) := by
      funext t
      rw [one_mul, ← mul_one (expK ε X t), ← rder_left ε l _ (expK ε X t) 1]
      congr 1
      funext x
      unfold avgK
      rw [toMK_expK_mul ε X hK t x]
      simp only [Matrix.mul_assoc]
    show HasDerivAt (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1)
      (rder ε [X] (rder ε l (avgK ε (kerE ε i) f y)) 1) 0
    rw [e1]
    exact (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε i _ hR X hK).2 1
  · intro m
    exact (summable_listSum (U m) b fun u _ => hbs u).mul_left (C m)
  · intro y hy
    have key := GlobalTheory.T.hasSum_compactUnitaryFourier_value_one ε (kerE ε) hker (fun k => f (y * toMK k)) ?_ (fun i => C 0 * ((U 0).map fun u => b u i).sum * (1 + hs y) ^ N)
      (((summable_listSum (U 0) b fun u _ => hbs u).mul_left (C 0)).mul_right _) ?_
    · simpa [toMK_one] using key
    · exact hf.comp_continuous ((continuous_const.mul (continuous_toMK ε))) fun k => mul_mem_UJ hy (K_le_UJ k.2)
    · intro i k'
      have hyk : y * toMK k' ∈ UJset ε := mul_mem_UJ hy (K_le_UJ k'.2)
      have := hbound i 0 [] le_rfl (by simp) _ hyk
      rw [hs_mul_toMK] at this
      simpa [avgK, toMK_one, toMK_mul, Matrix.mul_assoc] using this

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.InvariantIsAlgebraic
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FinalJoin GlobalTheory.CompRat Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.WeberField

theorem weber_isAlgebraic (L : PeriodPair) (hj : IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)))
    {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ∉ L.lattice) (hnt : (n : ℂ) * t ∈ L.lattice) :
    IsAlgebraic ℚ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hm.symm)
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have e2 : L'.g₂ ^ 3 = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [H.g₂_eq, ← hm]; field_simp
  have e3 : L'.g₃ ^ 2 = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1) / 27 := by
    rw [H.g₃_eq, mul_pow, inv_pow, ← pow_mul, hm]; field_simp; ring
  have hjm := mem_algebraicClosure_iff.mpr hj
  have h2 : L'.g₂ ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (e2 ▸ hj))
  have h3 : L'.g₃ ∈ algebraicClosure ℚ ℂ := by
    refine mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)
    rw [← mem_algebraicClosure_iff, e3]
    exact div_mem (sub_mem hjm (one_mem _)) (ofNat_mem _ 27)
  have hp := (GlobalTheory.CurveAlgebraic.weierstrassP_mem L' h2 h3 hn (t := m * t) (fun h => ht ((H t).1 h))
    (by rw [mul_left_comm]; exact (H _).2 hnt)).1
  have e : L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (m * t) := by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hm]; field_simp
  rw [e]
  exact mem_algebraicClosure_iff.mp (mul_mem (mul_mem h2 h3) hp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem invariant_isAlgebraic (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) :
    IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  have hi : IsIntegral ℤ (modularJ τ) := by
    refine isIntegral_modularJ_of_mul_mem (α := wC H (0, 1)) (fun m hm => ?_) fun x hx => ?_
    · have e : H.rt0 = ((2 * m - 1 : ℤ) : ℂ) := by
        simp only [wC] at hm
        push_cast at hm ⊢
        linear_combination 2 * hm
      have e' := H.sqrt_neg_disc_sq
      rw [e] at e'
      have e'' : (2 * m - 1) ^ 2 = -(H.d : ℤ) := by exact_mod_cast e'
      have := H.d_prime.pos
      nlinarith [sq_nonneg (2 * m - 1)]
    · rw [key] at hx ⊢
      obtain ⟨s, hs⟩ := (hL _).1 hx
      obtain ⟨b, hb⟩ := Weber.wC_mul H (0, 1) s
      rw [mul_left_comm, hs, hb]
      exact (hL _).2 ⟨b, rfl⟩
  rw [← g₂_cube_div_eq_modularJ ha h] at hi
  have := div_mem (mem_algebraicClosure_iff.mpr (hi.tower_top (A := ℚ)).isAlgebraic)
    (ofNat_mem (algebraicClosure ℚ ℂ) 1728)
  rw [mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)] at this
  exact mem_algebraicClosure_iff.mp this

end GlobalTheory.WeberField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RowsOfPageFix
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize Formalism.MainNotions.WeightAlgebra

theorem rows_of_pageFix : ∀ (eps : ℝ) (Fm : FamP eps), DC.PageFix Fm → 1000 ≤ Fm.CP → ∃ x₁ : ℝ, ∀ x (hx : Fm.x1 < x), x₁ ≤ x → ∀ i : Fm.Ix x, SizesAt (Fm.L x i) ∧ (Fm.params x hx i).CnW = 10 ∧ (∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1) ∧ 1000 ≤ (Fm.parT x hx i).CP ∧ (Fm.parT x hx i).CP ^ 20 ≤ zBase (Fm.L x i) ∧ DV.KapDef (Fm.D x i) ∧ Nonempty (ErrX (Fm.D x i)) ∧ (Fm.L x i).sc.x = x ∧ (JointQ (Fm.D x i) → FieldSmall (Fm.D x i) (Fm.L x i)) := by
  intro eps Fm hP hCP
  refine ⟨max ((10 : ℝ) ^ 60) (Fm.CP ^ 20), ?_⟩
  intro x hx hx₁ i
  have hS : SizesAt (Fm.L x i) := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hCnW : (Fm.params x hx i).CnW = 10 := (Fm.fixed.2.2.2.2.2.2.2 x hx i).1

  have hg : ∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1 := by
    intro k
    have hpr := (Fm.D x i).host.g_prime k
    have hpos : (0 : ℝ) < ((Fm.D x i).host.g k : ℝ) := by exact_mod_cast hpr.pos
    have hle := (hP.2.2.2.2.2.2.2.2 x hx i).2.2.1 k
    have := (Real.log_le_iff_le_exp hpos).2 hle
    linarith
  have h60 : (10 : ℝ) ^ 60 ≤ (Fm.L x i).sc.x := by
    rw [hLx]; exact le_trans (le_max_left _ _) hx₁
  obtain ⟨hH, hF⟩ := hostSz_of_sizes (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) hS hg h60

  have hCPeq : (Fm.parT x hx i).CP = Fm.CP := by
    unfold FamP.CP
    rw [← Fm.parT_K x hx i]
    rfl
  have hL4 : (4 : ℝ) ≤ (Fm.L x i).sc.L := hH.len

  have hf : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have hK := hS.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    rcases Nat.eq_zero_or_pos (Fm.D x i).R.f with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, zero_mul] at hK
      have hxpos : 0 < (Fm.L x i).sc.x ^ szTh (Fm.L x i) :=
        Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _
      have := mul_pos hxpos (by linarith : (0 : ℝ) < (Fm.L x i).sc.L)
      linarith
    · exact_mod_cast hpos
  refine ⟨hS, hCnW, hg, ?_, ?_, (Fm.ex x hx i).kap_def, ⟨(Fm.ex x hx i).errX⟩, hLx, ?_⟩
  · rw [hCPeq]; exact hCP
  ·
    unfold zBase
    rw [hCPeq]
    have hr : x ≤ ((Fm.D x i).R.r : ℝ) := by
      have h := scale_le_rank hS
      rw [hLx] at h
      exact h
    have hr0 : (0 : ℝ) ≤ ((Fm.D x i).R.r : ℝ) := Nat.cast_nonneg _
    have h1 : ((Fm.D x i).R.r : ℝ) ≤ (Fm.D x i).R.f * (Fm.D x i).R.r := le_mul_of_one_le_left hr0 hf
    have h2 : ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r ≤ (Fm.D x i).R.f * (Fm.D x i).R.r * (Fm.L x i).sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith [le_trans (le_max_right _ _) hx₁]
  · intro hJ
    exact hF (hJ.2.2.2.2 _ hH)

end GlobalTheory.FinalRows

end
end

