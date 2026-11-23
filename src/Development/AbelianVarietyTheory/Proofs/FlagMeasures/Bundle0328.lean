module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProductStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_frequencies_and_conductor_product : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ ψ : AddChar (AF I.F) ℂ, IsCharAF I.F ψ → ∃ (lamv : InfinitePlace I.F → ℝ) (m : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) → ℤ), (∀ v, lamv v ≠ 0) ∧ (∀ x, psiInf I.F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) ∧ (Function.support m).Finite ∧ (∀ u (t : Fv I.F u), (∀ s ∈ u.adicCompletionIntegers I.F, psiV I.F ψ u (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp (m u)) ∧ ∏ᶠ u, (Ideal.absNorm u.asIdeal : ℝ) ^ m u = |(discr I.F : ℝ)| * ∏ v, |lamv v| := by
  first | exact @GlobalTheory.AdeleCharConductor.real_part_and_conductors | exact GlobalTheory.AdeleCharConductor.real_part_and_conductors | (intros; apply GlobalTheory.AdeleCharConductor.real_part_and_conductors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosen
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameFull

variable {D : D7}

theorem mL_div (I : Formalism.MainNotions.S.AutInst) (m : ℕ) :
    ∀ v ∈ mL I m, ∃ z ∈ I.Lf, v = (m : I.E ⊗[I.F] Af I.F) • z := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, I.Lf.zero_mem, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, I.Lf.add_mem ha hb, (smul_add _ _ _).symm⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, I.Lf.smul_mem c ha, smul_comm _ _ _⟩

theorem embA_smul (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
  simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem embA_zero (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA 0 = 0 := by
  simp [embA]

theorem step (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hmem : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F)
    (m : ℕ) (w : VA X.B.I) (hw : w ∈ X.B.I.Lf)
    (hwe : embA X wt ιA (c • y) = (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) :
    ∃ z ∈ hat D.host.F (Mq wt), c • y = (m : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero]
    apply hinj
    rw [hwe, embA_zero, Nat.cast_zero, zero_smul]
  · have hF : IsUnit ((m : D.host.F)) := (Nat.cast_ne_zero.mpr hm.ne').isUnit
    have hR : IsUnit ((m : D.host.E ⊗[D.host.F] Ad D.host.F)) := by
      simpa using hF.map (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))
    obtain ⟨t, ht⟩ := hR.exists_right_inv
    refine ⟨t • (c • y), ?_, ?_⟩
    · rw [hmem, embA_smul, hwe, smul_smul, ← map_natCast ιA.symm m, ← map_mul, mul_comm, ht, map_one, one_smul]
      exact hw
    · rw [smul_smul, ht, one_smul]

theorem symm_unit (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA) :
    ιA.symm (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) =
      1 - X.ew - sigA X.B.I X.ew := by
  have h := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI X.ew
  apply ιA.injective
  rw [RingEquiv.apply_symm_apply, map_sub, map_sub, map_one]
  exact congrArg (fun t => 1 - ιA X.ew - t) h.symm

theorem emb_mem (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA)
    (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (hy : embA X wt ιA y ∈ X.B.I.Lf) :
    ∃ w ∈ X.B.I.Lf, embA X wt ιA
      ((1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y) =
      ((D.host.g 0 * D.host.g 1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w := by
  rw [embA_smul, symm_unit X ιA hI]
  obtain ⟨w, hw, hw'⟩ := mL_div X.B.I X.B.g _ (X.ew_full _ hy)
  exact ⟨w, hw, by rw [hw', X.g_eq]⟩

theorem eps_full : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  intro D X u wt ιA hW hI y hy
  obtain ⟨hmem, -, hinj, -⟩ := _root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hI
  obtain ⟨w, hw, hwe⟩ := emb_mem X wt ιA hI y ((hmem y).1 hy)
  exact step X wt ιA hmem hinj _ y _ w hw hwe

end GlobalTheory.St.G.FrameFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicEmbeddingBasisLiesInModule
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.TransportCong


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem inModL_of_inMod_embA : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hA b bd y hy
  obtain ⟨h1, -, hinj, -⟩ := _root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hA
  have hadd : ∀ x x', embA X wt ιA (x + x') = embA X wt ιA x + embA X wt ιA x' := by
    intro x x'; simp only [embA, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : D.host.E ⊗[D.host.F] Ad D.host.F) x,
      embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
    intro c x; simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  have hzero : embA X wt ιA 0 = 0 := by simp [embA]
  have hsub : ∀ x x', embA X wt ιA (x - x') = embA X wt ιA x - embA X wt ιA x' := by
    intro x x'
    have := hadd (x - x') x'
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have hS : (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) =
      embA X wt ιA '' (Set.range b ∪ Set.range bd) := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]; rfl
  have hspan : ∀ s ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (embA X wt ιA '' (Set.range b ∪ Set.range bd)),
      ∃ s' ∈ Submodule.span (OAd D.host.F D.host.E) (Set.range b ∪ Set.range bd), embA X wt ιA s' = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact ⟨t, Submodule.subset_span ht, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, hzero⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      obtain ⟨s2, hs2, rfl⟩ := ihx'
      exact ⟨s1 + s2, Submodule.add_mem _ hs1 hs2, hadd _ _⟩
    | smul a x _ ihx =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      have ha : ιA (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hA.2 a).1 a.2
      refine ⟨(⟨_, ha⟩ : OAd D.host.F D.host.E) • s1, Submodule.smul_mem _ _ hs1, ?_⟩
      rw [Subring.smul_def, hsmul, RingEquiv.symm_apply_apply, Subring.smul_def]
  have hmL : ∀ w ∈ mL X.B.I X.B.g, ∃ x ∈ X.B.I.Lf,
      w = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨x', hx', rfl⟩ := hx; exact ⟨x', hx', rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, (smul_zero _).symm⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      obtain ⟨a2, h2, rfl⟩ := ihx'
      exact ⟨a1 + a2, Submodule.add_mem _ h1 h2, (smul_add _ _ _).symm⟩
    | smul a x _ ihx =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      refine ⟨a • a1, Submodule.smul_mem _ _ h1, ?_⟩
      simp only [Subring.smul_def, smul_smul, mul_comm]
  unfold InMod at hy
  rw [hS] at hy
  obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s', hs', rfl⟩ := hspan s hs
  obtain ⟨x, hx, rfl⟩ := hmL w hw
  rw [X.g_eq] at hsw
  rcases Nat.eq_zero_or_pos (D.host.g 0 * D.host.g 1) with h0 | hpos
  · refine ⟨s', hs', 0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero, add_zero]
    apply hinj
    rw [← hsw, h0, Nat.cast_zero, zero_smul, add_zero]
  · have hu : IsUnit (((D.host.g 0 * D.host.g 1 : ℕ)) : D.host.E ⊗[D.host.F] Ad D.host.F) := by
      rw [← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')).map _
    obtain ⟨c, hc⟩ := hu
    refine ⟨s', hs', ((c⁻¹ : (D.host.E ⊗[D.host.F] Ad D.host.F)ˣ) : D.host.E ⊗[D.host.F] Ad D.host.F) • (y - s'), ?_, ?_⟩
    · rw [h1, hsmul, hsub, ← hsw, add_sub_cancel_left, smul_smul, ← map_natCast ιA.symm, ← hc,
        ← map_mul, Units.inv_mul, map_one, one_smul]
      exact hx
    · rw [smul_smul, ← hc, Units.mul_inv, one_smul, add_sub_cancel]

end GlobalTheory.St.G.TransportCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselCoefficientNonzero
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKOne

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt GlobalTheory.AmpTK

variable {k r : ℕ}

theorem besselIntg_sum (L : LocBessel k r) {ι : Type} (s : Finset ι)
    (F : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) :
    besselIntg L (fun q => ∑ a ∈ s, F a q) g p = ∑ a ∈ s, besselIntg L (F a) g p := by
  ext η
  set_option synthInstance.maxHeartbeats 100000 in
    simp [besselIntg, ContinuousLinearMap.sum_apply, map_sum, Finset.smul_sum]

end GlobalTheory.AmpTKOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselCoefficientNonzeroExists
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : BranchingSupport.Hyps → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.AmpTK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCusp

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  obtain ⟨hR1, hRmul, hRnorm, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B

  have hπ1 : (fun a : B.I.Gf => B.R (1, a)) 1 = 1 := hR1
  have hπmul : ∀ a b : B.I.Gf, (fun a : B.I.Gf => B.R (1, a)) (a * b) =
      (fun a : B.I.Gf => B.R (1, a)) a * (fun a : B.I.Gf => B.R (1, a)) b := by
    intro a b
    have hab : ((1 : B.I.Ginf), a * b) = ((1 : B.I.Ginf), a) * (1, b) := by
      simp [Prod.mk_mul_mk]
    simp only
    rw [hab, hRmul]
  have hadj : ∀ (a : B.I.Gf) (u v : B.I.L2 B.μf B.fund),
      ⟪u, B.R (1, a) v⟫_ℂ = ⟪B.R (1, a⁻¹) u, v⟫_ℂ :=
    GlobalTheory.IdemProj.inner_rep (fun a : B.I.Gf => B.R (1, a)) hπ1 hπmul (fun a v => hRnorm _ v)

  have hone : (1 : B.I.Gf) ∈ B.I.Kg B.g := by
    refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · show ((1 : B.I.Gf) : GL (Fin B.I.n) (TensorProduct B.I.F B.I.E (Af B.I.F))) ∈ Formalism.UG.stabGL B.I.Lf
      simpa using (Formalism.UG.stabGL B.I.Lf).one_mem
    · simp [AutInst.fmat]
  have he : ∀ x, B.e (k * x) = B.e x := by
    intro x
    have h' := B.e_adm.2.2.2.2.2.1 x k hk 1 hone
    rwa [mul_one] at h'
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [ContinuousLinearMap.comp_apply, hadj, B.Re_spec.2, B.Re_spec.2]
  have hshift : ∀ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ =
      (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) := by
    intro g
    simp only
    rw [he, ← inv_inv k, ← hadj, inv_inv, ← ContinuousLinearMap.mul_apply, ← hπmul]
  calc ∫ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ ∂B.μf
      = ∫ g, (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) ∂B.μf := by
        congr 1
        funext g
        exact hshift g
    _ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf :=
        integral_mul_left_eq_self (μ := B.μf) (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hcont, hbound, hmaj⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl

  have hgap : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hqR : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hq
      have hnR : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hsq : (0 : ℝ) < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.mpr hqR
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
          (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hqR, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have hv := hh v
      rw [hpow] at hv
      have hpos : 0 < (B.I.n : ℝ) * (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        positivity
      nlinarith
  have hint : Integrable (majPh B d h) (muInf B.I) := by
    simpa using hmaj 0 le_rfl hgap
  exact hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem row_isCuspFn : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro hSL B d h hd hg hh hl hH T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  ·
    intro W hW
    exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.2 (by omega)
  have hn : 1 ≤ B.I.n := hnpos

  obtain ⟨A₀, hA₀, hAeq⟩ := Submodule.mem_map.mp hA
  have hAc : A = B.Re.comp A₀ := hAeq.symm
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hcomm : ∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re :=
    (GlobalTheory.IdemProj.re_orth_proj B).2.1
  have hAS : A ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, A.comp (B.σs g) = (B.R (g, 1)).comp A
    intro g
    rw [hAc, ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]

  have hfix : ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w) := by
    intro k hk
    rw [hAc]
    exact congrArg (fun L : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => L (A₀ (B.tens B.w)))
      (level_comp_Re B k hk hg)
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.EvalBound.exists_contRep_bound hSL B d hd hn hg
  obtain ⟨f, hf, hfb⟩ := hC A hAS hfix

  have hTy : T (A (B.tens B.w)) = A (B.tens B.w) :=
    ((GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hn hh hl)).2.2.2 T hT).2.1 A hA
  exact (_root_.GlobalTheory.CuspFixed.cusp_of_fixed B d h hd (_root_.GlobalTheory.RealFibre.integral_phe_eq_zero hSL B d h hd hl hh) hl hH T hT (A (B.tens B.w)) f
    (C * ‖A (B.tens B.w)‖) hTy hf (fun x => (hfb x).trans_eq (by ring))).2

end GlobalTheory.RowCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
section
namespace GlobalTheory

theorem localMass_le_genericMass_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP R d0 h0 d t ht Y0 hZ
  exact GlobalTheory.mass_pairingClass_bounds M hM H r k P hk hV hP R d0 h0 d t ht Y0 _ rfl hZ _ rfl

end GlobalTheory
end

