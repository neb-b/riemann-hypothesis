module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosets
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolution
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay.Mean

open GlobalTheory.LeviHC GlobalTheory.LeviHC.LineLie GlobalTheory.SmoothForms

section OnePlace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem norm_le_of_entries {X : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i j, ‖X i j‖ ≤ r) :
    ‖X‖ ≤ n * r := by
  have key : ‖X‖₊ ≤ (n : ℝ≥0) * r.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖X i j‖₊ ≤ ∑ _j : Fin n, r.toNNReal :=
          Finset.sum_le_sum fun j _ => by
            rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hr]
            exact h i j
      _ = (n : ℝ≥0) * r.toNNReal := by simp
  have key' := NNReal.coe_le_coe.mpr key
  simpa [Real.coe_toNNReal _ hr] using key'

theorem expMap_zero (h : IsCMExt F E σ) (τ : EmbOver E w) :
    expMap (jA (J.map τ.1)) (secA σ J τ) 0 = 1 := by
  show secA σ J τ (NormedSpace.exp ((jA (J.map τ.1)) 0)) = 1
  rw [map_zero, NormedSpace.exp_zero, ← map_one (archMat σ J τ), secA_archMat h, map_one]

theorem expMap_add (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Z : LieL (J.map τ.1)) (s t : ℝ) :
    expMap (jA (J.map τ.1)) (secA σ J τ) ((s + t) • Z) =
      expMap (jA (J.map τ.1)) (secA σ J τ) (s • Z) * expMap (jA (J.map τ.1)) (secA σ J τ) (t • Z) := by
  obtain ⟨y1, e1, a1⟩ := isLineOf_expMap h hJ τ Z s
  obtain ⟨y2, e2, a2⟩ := isLineOf_expMap h hJ τ Z t
  obtain ⟨y3, e3, a3⟩ := isLineOf_expMap h hJ τ Z (s + t)
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply archMat_injective h τ
  rw [map_mul, a1, a2, a3, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

theorem one_place (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℝ → GAd σ J) (K : Set (GArch σ J w)) (C δ₁ : ℝ),
      (∀ i, IsRealLine σ J (b i)) ∧ IsCompact K ∧ 1 ∈ K ∧ 0 < δ₁ ∧ 0 ≤ C ∧
      ∀ (y : GArch σ J w) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → (∀ i j, ‖(archMat σ J τ y - 1) i j‖ ≤ δ) →
        y ∈ K ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g : GAd σ J) (c : ι → ℝ),
          (∀ i, ∀ x ∈ K, ‖lineDer (b i) ψ (g * embArch σ J w x)‖ ≤ c i) →
          ‖ψ (g * embArch σ J w y) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  have hA := isUnit_det_map hJ τ.1
  obtain ⟨δ₁, C₀, h1, hlog⟩ := GlobalTheory.UnitaryLog.exists_log_unitary n (J.map τ.1) hA
  haveI : FiniteDimensional ℝ (LieL (J.map τ.1)) := inferInstance
  haveI : ProperSpace (LieL (J.map τ.1)) := FiniteDimensional.proper_real _
  let b := Module.finBasis ℝ (LieL (J.map τ.1))
  obtain ⟨K₀, hK₀, hco⟩ := GlobalTheory.CuspGeo.MeanValue.exists_coord_bound b
  choose yOf hy1 hy2 using fun Y : LieL (J.map τ.1) => isLineOf_expMap h hJ τ Y 1
  simp only [one_smul] at hy1 hy2
  have hyc : Continuous yOf := (GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff.2 (by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun Y => archMat σ J τ (yOf Y) i j
    simp only [hy2]
    have : Continuous fun Y : LieL (J.map τ.1) => NormedSpace.exp Y.1 :=
      (NormedSpace.exp_continuous).comp continuous_subtype_val
    exact (continuous_apply j).comp ((continuous_apply i).comp this))
  have hy0 : yOf 0 = 1 := archMat_injective h τ (by
    rw [hy2, map_one]; simp)
  set C₁ : ℝ := n * |C₀| with hC₁
  have hC₁0 : 0 ≤ C₁ := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine ⟨_, inferInstance, fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • b i),
    yOf '' Metric.closedBall 0 (C₁ * δ₁), K₀ * C₁, δ₁, fun i => (isLineOf_expMap h hJ τ (b i)).isRealLine h,
    (isCompact_closedBall _ _).image hyc, ⟨0, ?_, hy0⟩, h1, mul_nonneg hK₀ hC₁0, fun y δ h0 hδ hy => ?_⟩
  · simpa using mul_nonneg hC₁0 h1.le
  have hU : (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 := by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h τ y).2
  obtain ⟨X, hX, hE, hB⟩ := hlog (archMat σ J τ y) δ hU hδ hy
  let Z : LieL (J.map τ.1) := ⟨X, hX⟩
  have hZ : ‖Z‖ ≤ C₁ * δ := by
    have := norm_le_of_entries (mul_nonneg (abs_nonneg C₀) h0) fun i j =>
      (hB i j).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) h0)
    rw [hC₁, mul_assoc]
    exact this
  have hyZ : yOf Z = y := archMat_injective h τ (by rw [hy2, ← hE])
  have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • Z ∈ Metric.closedBall (0 : LieL (J.map τ.1)) (C₁ * δ₁) := fun t ht => by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (hZ.trans (mul_le_mul_of_nonneg_left hδ hC₁0))
  refine ⟨⟨Z, by simpa using hball 1 (by simp), hyZ⟩, fun ψ hψ g c hc => ?_⟩
  rw [← hyZ, ← hy1 Z]
  refine GlobalTheory.CuspGeo.MeanValue.norm_sub_le _ (expMap_zero h τ) (expMap_add h hJ τ) b (sm_of_isSm h hJ τ hψ) g Z _
    (fun i => (hco Z i).trans ?_) c fun i t ht => ?_
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ hK₀
  · have := hc i (yOf (t • Z)) ⟨_, hball t ht, rfl⟩
    rw [← hy1] at this
    exact this

end OnePlace

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def pt (a : ∀ w, GArch σ J w) : GAd σ J := ofInf σ J (embArchPi σ J a)

theorem pt_mul_single [DecidableEq (InfinitePlace F)] (a : ∀ w, GArch σ J w) (w : InfinitePlace F) (x : GArch σ J w) :
    pt (a * Pi.mulSingle w x) = pt a * embArch σ J w x := by
  show ofInf σ J (embArchPi σ J (a * Pi.mulSingle w x)) = ofInf σ J (embArchPi σ J a) * embArch σ J w x
  rw [map_mul, map_mul, embArchPi_mulSingle]
  rfl

theorem pt_one : pt (1 : ∀ w, GArch σ J w) = 1 := by
  simp only [pt, map_one]

theorem pt_proj {u : GAd σ J} (hu : u ∈ infPts σ J) : pt (fun w => projArch σ J w u) = u := by
  refine GAd_ext σ J (fun w' => ?_) (fun v => ?_)
  · rw [pt, projArch_ofInf, projInfArch_embArchPi]
  · rw [pt, proj_ofInf, mem_infPts_iff_forall.mp hu v]

theorem continuous_pt : Continuous (pt : (∀ w, GArch σ J w) → GAd σ J) := by
  show Continuous fun a => ofInf σ J (embArchPi σ J a)
  exact (continuous_ofInf σ J).comp (continuous_embArchPi σ J)


open Classical in
theorem telescope {ι : InfinitePlace F → Type} [∀ w, Fintype (ι w)] {b : ∀ w, ι w → ℝ → GAd σ J}
    {K : ∀ w, Set (GArch σ J w)} {C : InfinitePlace F → ℝ} (h1 : ∀ w, 1 ∈ K w) {ψ : GAd σ J → ℂ} (g : GAd σ J)
    {y : ∀ w, GArch σ J w} (hyK : ∀ w, y w ∈ K w) {δ : ℝ} {c : ∀ w, ι w → ℝ}
    (hstep : ∀ w (g : GAd σ J), (∀ i, ∀ x ∈ K w, ‖lineDer (b w i) ψ (g * embArch σ J w x)‖ ≤ c w i) →
      ‖ψ (g * embArch σ J w (y w)) - ψ g‖ ≤ C w * δ * ∑ i, c w i)
    (hc : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c w i)
    (S : Finset (InfinitePlace F)) :
    ‖ψ (g * pt fun w => if w ∈ S then y w else 1) - ψ g‖ ≤ ∑ w ∈ S, C w * δ * ∑ i, c w i := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (fun w => if w ∈ (∅ : Finset (InfinitePlace F)) then y w else 1) = (1 : ∀ w, GArch σ J w) := by
      funext w
      simp
    rw [h0, pt_one, mul_one, sub_self, norm_zero, Finset.sum_empty]
  | @insert v S hv ih =>
    set a : ∀ w, GArch σ J w := fun w => if w ∈ S then y w else 1 with ha
    have hsplit : (fun w => if w ∈ insert v S then y w else 1) = a * Pi.mulSingle v (y v) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha, Finset.mem_insert, hw, false_or]
    have hK : ∀ x ∈ K v, a * Pi.mulSingle v x ∈ Set.pi Set.univ K := by
      intro x hx
      rw [Set.mem_univ_pi]
      intro w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv, hx]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha]
        split_ifs
        · exact hyK w
        · exact h1 w
    have step := hstep v (g * pt a) (fun i x hx => by
      rw [mul_assoc, ← pt_mul_single]
      exact hc v i _ ⟨_, hK x hx, rfl⟩)
    rw [hsplit, pt_mul_single, Finset.sum_insert hv, ← mul_assoc]
    calc _ = ‖(ψ (g * pt a * embArch σ J v (y v)) - ψ (g * pt a)) + (ψ (g * pt a) - ψ g)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add step ih)

end Places

theorem mean_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  have τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  choose ι hι b K C d hb hK h1K hd hC key using fun w => one_place (J := J) h hJ (τ w)
  letI : ∀ w, Fintype (ι w) := hι
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ > 0, ∀ w, δ₁ ≤ d w := by
    obtain ⟨w₀, h0⟩ := Finite.exists_min d
    exact ⟨d w₀, hd w₀, h0⟩
  let e := Fintype.equivFin (Σ w, ι w)
  have hCs : 0 ≤ ∑ w, C w := Finset.sum_nonneg fun w _ => hC w
  refine ⟨_, fun i => b (e.symm i).1 (e.symm i).2, pt '' Set.pi Set.univ K, ∑ w, C w, δ₁, fun i => hb _ _,
    (isCompact_univ_pi hK).image continuous_pt, hδ₁, hCs, fun ψ hψ g u δ h0 hδ hu c hc => ?_⟩
  let c' : ∀ w, ι w → ℝ := fun w i => c (e ⟨w, i⟩)
  have hc' : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c' w i := fun w i x hx => by
    have aux : ∀ p q : Σ w, ι w, p = q → lineDer (b p.1 p.2) ψ = lineDer (b q.1 q.2) ψ := by
      rintro _ _ rfl; rfl
    have := hc (e ⟨w, i⟩) x hx
    rwa [aux _ ⟨w, i⟩ (e.symm_apply_apply _)] at this
  have hnn : ∀ w i, 0 ≤ c' w i := fun w i =>
    (norm_nonneg _).trans (hc' w i 1 ⟨1, fun w _ => h1K w, pt_one⟩)
  have hclose := fun w => key w (projArch σ J w u) δ h0 (hδ.trans (hle w)) (hu.2 w (τ w))
  have T := telescope (b := b) (K := K) (C := C) h1K (ψ := ψ) g (y := fun w => projArch σ J w u)
    (fun w => (hclose w).1) (δ := δ) (c := c') (fun w g' hg' => (hclose w).2 ψ hψ g' (c' w) hg') hc' Finset.univ
  have hfull : (fun w => if w ∈ (Finset.univ : Finset (InfinitePlace F)) then projArch σ J w u else 1) =
      fun w => projArch σ J w u := by
    funext w; simp
  rw [hfull, pt_proj hu.1] at T
  refine T.trans ?_
  have hsum : ∑ i, c i = ∑ w, ∑ i, c' w i := by
    rw [← Equiv.sum_comp e c, Fintype.sum_sigma]
  have hT : ∀ w, ∑ i, c' w i ≤ ∑ i, c i := fun w => by
    rw [hsum]
    exact Finset.single_le_sum (f := fun w => ∑ i, c' w i)
      (fun w _ => Finset.sum_nonneg fun i _ => hnn w i) (Finset.mem_univ w)
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hT w) (mul_nonneg (hC w) h0)

end GlobalTheory.CompanionTheory.RapidDecay.Mean

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.KerQuot

theorem exists_subQuot_top_ker_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (R : ρ.IntertwiningMap τ) (hR : Function.Surjective R) :
    ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧
      Nonempty ((subQuot ⊤ S).Equiv τ) := by
  refine ⟨Representation.IntertwiningMap.ker ρ τ R, rfl, ?_⟩
  let T : Subrepresentation ρ := ⊤
  let f : T.toSubmodule →ₗ[ℂ] W := R.toLinearMap ∘ₗ T.toSubmodule.subtype
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, rfl⟩ := hR w
    exact ⟨⟨v, by first | exact Submodule.mem_top | trivial | simp [T]⟩, rfl⟩
  have hker : Submodule.comap T.toSubmodule.subtype
      (Representation.IntertwiningMap.ker ρ τ R).toSubmodule = LinearMap.ker f :=
    (LinearMap.ker_comp T.toSubmodule.subtype R.toLinearMap).symm
  let e := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)
  refine ⟨⟨⟨e.toLinearMap, fun g => ?_⟩, e.symm, e.left_inv, e.right_inv⟩⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  first
    | exact Representation.IntertwiningMap.isIntertwining ρ τ R g x.1
    | exact R.isIntertwining g x.1
    | simp [e, f, T, GlobalTheory.SmGL.subQuot, Representation.quotient_apply,
        Subrepresentation.toRepresentation, Representation.IntertwiningMap.isIntertwining]

end GlobalTheory.CompanionTheory.BZRes.KerQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolution
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvF

def twistEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H)
    (hc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) : H × H ≃ₜ* H × H where
  toFun y := (y.1, σ y.2)
  invFun y := (y.1, σ y.2)
  left_inv y := by simp [hσ]
  right_inv y := by simp [hσ]
  map_mul' a b := by simp
  continuous_toFun := continuous_fst.prodMk (hc.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (hc.comp continuous_snd)

theorem twOrb_conj_of_biinv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K K' : Subgroup G) (δ g : G) (F : G → ℂ) (hθ : Continuous θ) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) :
    twOrb θ K (g⁻¹ * δ * θ g) F = twOrb θ K δ F :=
  GlobalTheory.TwOrbConj.twOrb_twConj G θ K δ g F
    (GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact θ K K' δ F hθ hK hK' hF)

theorem splitConv_of_finite : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ σ K hc hσ hσK hKo hKc d d' f₁ f₂ K' hK'o hK'K hσK' h₁ h₂ hG hfin
  set θ := (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom with hθ
  have hθc : Continuous θ := (hc.comp continuous_snd).prodMk (hc.comp continuous_fst)
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hK'K'o : IsOpen ((K'.prod K' : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hK'o.prod hK'o
  have hinv : ∀ k ∈ K'.prod K', ∀ x : H × H,
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (k * x) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x ∧
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (x * k) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x := by
    rintro ⟨k₁, k₂⟩ hk ⟨x₁, x₂⟩
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hk₂' : σ k₂ ∈ K' := hσK' _ hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).1, map_mul, (h₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).2, map_mul, (h₂.2 _ hk₂' _).2]
  have hconj : ((1, d') : H × H)⁻¹ * (d, d') * θ (1, d') = (d * σ d', 1) := by
    have e : θ (1, d') = (σ d', 1) := by simp [hθ]
    rw [e]
    ext <;> simp
  have step₁ := twOrb_conj_of_biinv θ (K.prod K) (K'.prod K') (d, d') (1, d')
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) hθc hKKc hK'K'o hinv
  rw [hconj] at step₁
  rw [← step₁]
  have step₂ := GlobalTheory.EulerTw.Transport.twOrb_transport (H × H) (H × H) (twistEquiv σ hc hσ) θ
    (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom (K.prod K) (K.prod K) (d * σ d', 1)
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (fun y : H × H => f₁ y.1 * f₂ y.2)
    (by
      rintro ⟨x₁, x₂⟩
      show (σ x₂, σ (σ x₁)) = (σ x₂, x₁)
      rw [hσ])
    (by
      rintro ⟨x₁, x₂⟩
      show x₁ ∈ K ∧ x₂ ∈ K ↔ x₁ ∈ K ∧ σ x₂ ∈ K
      refine and_congr_right fun _ => ⟨hσK _, fun h => ?_⟩
      simpa [hσ] using hσK _ h)
    (fun _ => rfl)
  have he : (twistEquiv σ hc hσ) (d * σ d', 1) = (d * σ d', 1) := by
    show (d * σ d', σ 1) = (d * σ d', 1)
    rw [map_one]
  rw [he] at step₂
  rw [step₂]
  exact _root_.GlobalTheory.CompanionTheory.SplitSwap.main H K K' (d * σ d') f₁ f₂ hKo hKc hK'o hK'K h₁ h₂ hG
    (_root_.GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets H K (d * σ d') hKc hfin)

end GlobalTheory.CompanionTheory.SplitConvF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ResidueInvolution

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (e : E) :
    sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl

theorem sigR_sigR {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [sigR_tmul, sigR_tmul, sigma_sigma h]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (c : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R (R ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, sigR_tmul]
  simp

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

theorem eq_zero_of_forall_pow {v : HeightOneSpectrum (𝓞 F)} {ϖ c : Fv F v} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hc : ∀ j : ℕ, (ϖ⁻¹) ^ j * c ∈ v.adicCompletionIntegers F) : c = 0 := by
  by_contra hne
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hne) h1
  have h2 : ‖(ϖ⁻¹) ^ j * c‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (hc j)
  rw [norm_mul, norm_pow, norm_inv, inv_pow] at h2
  have h3 : 0 < ‖ϖ‖ ^ j := pow_pos (norm_pos_iff.2 h0) j
  rw [inv_mul_le_iff₀ h3, mul_one] at h2
  exact absurd hj (not_lt.2 h2)

theorem q1 : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ
  obtain ⟨hσ, -, hcar, hsig, h0, h1, -, -⟩ := hH
  refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, ?_, ?_, one_lt_absNorm v⟩
  · rw [hsig, hsig, sigR_sigR hσ]
  · rw [hsig, sigR_algebraMap]
  · intro x y hxy
    have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (x : Fv F v ⊗[F] E) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (y : Fv F v ⊗[F] E) := congrArg Subtype.val hxy
    rw [← Algebra.smul_def, ← Algebra.smul_def] at e
    exact Subtype.ext (smul_right_injective _ h0 e)
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (b : Fv F v ⊗[F] E) = 1 := congrArg Subtype.val hb
    have hb2 : (b : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ := by
      have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
          algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h0, map_one]
      calc (b : Fv F v ⊗[F] E)
          = (algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
              algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) * (b : Fv F v ⊗[F] E) := by rw [e, one_mul]
        _ = _ := by rw [mul_assoc, hb1, mul_one]
    have hc : ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr 1 k = 0 := fun k => by
      refine eq_zero_of_forall_pow h0 h1 fun j => ?_
      have hm : ((b ^ j : S) : Fv F v ⊗[F] E) ∈ Rv bs v := by
        rw [← hcar]
        exact (b ^ j).2
      have e : ((b ^ j : S) : Fv F v ⊗[F] E) = ((ϖ : Fv F v)⁻¹ ^ j) • (1 : Fv F v ⊗[F] E) := by
        rw [Subring.coe_pow, hb2, ← map_pow, Algebra.algebraMap_eq_smul_one]
      have := hm k
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    have h10 : (1 : Fv F v ⊗[F] E) = 0 :=
      (Algebra.TensorProduct.basis (Fv F v) bs).repr.map_eq_zero_iff.1 (Finsupp.ext hc)
    exact one_ne_zero h10

end GlobalTheory.CompanionTheory.ResidueInvolution

end
end

