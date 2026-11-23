module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0630
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacter
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Level

variable {D : D7} {r : ℕ}

def eFin (D : D7) : AF D.host.F := 1 - GlobalTheory.FinTranslate.eInf D

theorem eFin_mul (D : D7) (x : AF D.host.F) : eFin D * x = pairA D.host.F 0 (sndA D.host.F x) := by
  show ((1 : Ainf D.host.F × Af D.host.F) - (1, 0)) * (x : Ainf D.host.F × Af D.host.F) =
    ((0 : Ainf D.host.F), (x : Ainf D.host.F × Af D.host.F).2)
  refine Prod.ext ?_ ?_
  · show ((1 : Ainf D.host.F) - 1) * x.1 = 0
    rw [sub_self, zero_mul]
  · show ((1 : Af D.host.F) - 0) * x.2 = x.2
    rw [sub_zero, one_mul]

theorem finPart_eInf (D : D7) : finPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 0 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem infPart_eInf (D : D7) : infPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem rs_one {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    rs σ 1 = GlobalTheory.FinTranslate.eInf D • (1 : AE D) := by
  refine sub_eq_zero.mp (hσ.ext _ ?_ ?_)
  · rw [map_sub, finPart_eInf, sub_zero]
    exact hσ.fin _
  · intro τ
    rw [map_sub, map_sub, infPart_eInf, map_one]
    simp only [rs, hσ.comp]
    simp

theorem diff_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1).1 = eFin D • a.1.map (incA D) := by
  show GlobalTheory.MixModel.rat a.1 - rs σ 1 • a.1.map (incA D) = eFin D • a.1.map (incA D)
  rw [rs_one hσ, smul_one_smul, eFin, sub_smul, one_smul]
  rfl

def S (V : HSp D) (A : Mx D r r) (y : Mx D V.rank r) : AF D.host.F :=
  halfTr (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))

theorem halfTr_smul (c : AF D.host.F) (x : AE D) : halfTr (c • x) = c * halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_smul, smul_eq_mul]
  ring

theorem halfTr_nsmul (n : ℕ) (x : AE D) : halfTr (n • x) = n • halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA]
  rw [map_nsmul]
  simp only [nsmul_eq_mul]
  ring

theorem halfTr_trace_nsmul (n : ℕ) (M B : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (n • M) B : Mx D r r)) = n • halfTr (Matrix.trace (HMul.hMul M B : Mx D r r)) := by
  rw [Matrix.smul_mul, Matrix.trace_smul, halfTr_nsmul]

theorem pow_eq_one_of_compact {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    {C : Set (Af F)} (hC : IsCompact C) : ∃ N : ℕ, 0 < N ∧ ∀ c ∈ C, ψ (pairA F 0 c) ^ N = 1 := by
  obtain ⟨N1, hN1, hK⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_mem_Oh_of_isCompact F C hC
  obtain ⟨N2, hN2, hU⟩ :=
    GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_Oh_subset F _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  refine ⟨N2 * N1, Nat.mul_pos hN2 hN1, fun c hc => ?_⟩
  have h1 : ψ (pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c))) = 1 := hU _ (hK c hc)
  have h2 : (N2 * N1) • pairA F 0 c = pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c)) := by
    show (N2 * N1) • ((0 : Ainf F), c) = ((0 : Ainf F), (N2 : Af F) * ((N1 : Af F) * c))
    rw [Prod.smul_mk, smul_zero, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul]
  rw [← AddChar.map_nsmul_eq_pow, h2, h1]

private theorem supp_lemma_5 {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (hφ : φ ∈ schwartzA θ m n) :
    ∃ K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact K ∧
      ∀ y, φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ K := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨tsupport g, (show IsLocallyConstant g ∧ HasCompactSupport g from hg).2, fun y hy => subset_tsupport g ?_⟩
    exact right_ne_zero_of_mul hy
  | zero => exact ⟨∅, isCompact_empty, fun y hy => (hy rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨K1, hK1, h1⟩ := hx
    obtain ⟨K2, hK2, h2⟩ := hy
    refine ⟨K1 ∪ K2, hK1.union hK2, fun z hz => ?_⟩
    by_cases hxz : x z = 0
    · right
      apply h2
      simpa [hxz] using hz
    · left
      exact h1 z hxz
  | smul a x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    refine ⟨K, hK, fun y hy => h y ?_⟩
    intro h0
    apply hy
    simp [h0]

private theorem continuous_sigRf_lemma_7 : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig) := by
  let f : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig
      map_add' := map_add _
      map_smul' := fun c z => by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
        | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap f

private theorem trace_bc_lemma_8 (z : AE D) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) =
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a e =>
    have h1 : (a ⊗ₜ[D.host.F] e : AE D) = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : finPart D (a ⊗ₜ[D.host.F] e) = sndA D.host.F a • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [Formalism.L2.Theta.finPart]
    rw [h2, h1]
    simp only [map_smul, GlobalTheory.CompanionTheory.HermPoisson.trace_one_tmul', smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem level_pow {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (A : Mx D r r)
    {θ : InfFam D} {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) :
    ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (eFin D * S V A y) ^ N = 1 := by
  obtain ⟨K, hK, hKy⟩ := supp_lemma_5 hφ
  let Φ : (Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → Af D.host.F := fun w =>
    algebraMap D.host.F (Af D.host.F) (1 / 2) *
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
        (Matrix.trace (A.map (finPart D) *
          (((Matrix.of w).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
            ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of w))))
  have hΦ : Continuous Φ := by
    have hσc := continuous_sigRf_lemma_7 (D := D)
    have htr : Continuous (Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) := by fun_prop
    have hof : Continuous (fun w : Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => Matrix.of w) :=
      continuous_id
    exact continuous_const.mul (htr.comp (Continuous.matrix_trace (continuous_const.matrix_mul
      ((hof.matrix_map hσc).matrix_transpose.matrix_mul (continuous_const.matrix_mul hof)))))
  have hS : ∀ y : Mx D V.rank r, sndA D.host.F (S V A y) = Φ (fun i j => finPart D (y i j)) := by
    intro y
    have hM : (HMul.hMul A (inner V y y) : Mx D r r).map (finPart D) =
        A.map (finPart D) * (((Matrix.of fun i j => finPart D (y i j)).map
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
          ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of fun i j => finPart D (y i j))) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, GlobalTheory.MixModel.adj, GlobalTheory.StdUnn.inner, map_sum, GlobalTheory.CompanionTheory.WSum.finPart_cA]
    have ht : ∀ M : Mx D r r, finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
      intro M
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    show sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))) = _
    rw [map_mul, AlgHom.commutes, trace_bc_lemma_8, ht, hM]
  obtain ⟨N, hN, hC⟩ := pow_eq_one_of_compact hψ (hK.image hΦ)
  refine ⟨N, hN, fun y hy => ?_⟩
  rw [eFin_mul, hS y]
  exact hC _ ⟨_, hKy y hy, rfl⟩

theorem level : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  intro D r V ψ hψ θ σ hσ a φ hφ
  obtain ⟨N, hN, hy⟩ := level_pow hψ V (a.1.map (incA D)) hφ
  refine ⟨N, hN, fun y hy0 => ?_⟩
  rw [AddSubgroup.coe_nsmul, diff_eq hσ a, halfTr_trace_nsmul, Matrix.smul_mul, Matrix.trace_smul, halfTr_smul,
    AddChar.map_nsmul_eq_pow]
  exact hy y hy0

end GlobalTheory.CompanionTheory.WSum.Level
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModule
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.StableMod

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isCuspForm_fin (k : GL (Fin a) (Af E)) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (finRep E a k φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
    rw [mul_assoc, hA.left]
  · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
        (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
      ext k'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · intro e
        rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply]
      · intro e
        have := congrArg (finRep E a k) e
        rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply] at this
    change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
    rw [e]
    exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
      (finRep E a k)) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
  · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
    rw [mul_assoc, infGL_comm, ← mul_assoc]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)

theorem isCuspForm_cpt (c : Kinf E a) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (cptRep E a c φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
    rw [mul_assoc, hA.left]
  · exact level_of_le hA.level fun k hk => by
      change finRep E a k (cptRep E a c φ) = cptRep E a c φ
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨c', rfl⟩
    refine Submodule.subset_span ⟨c' * c, ?_⟩
    change _ = (cptRep E a c' * cptRep E a c) φ
    rw [← map_mul]
  · exact zfin_of_comm _ (fun z hz => _root_.GlobalTheory.ZalgCpt.zalg_comm_cptRep E a c z hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := growth_mul (Unitary.toUnits c) (hA.growth g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
    rw [mul_assoc, ← map_mul]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))

theorem lieD_left {φ : Sm E a} (X : Lie E a) {u : GA E a} (hu : ∀ g, φ.1 (u * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (u * g) = (lie E a X φ).1 g := by
  change lieD X φ.1 (u * g) = lieD X φ.1 g
  have e : chart φ.1 (u * g) = chart φ.1 g := by
    funext x
    unfold chart
    split_ifs
    · rw [mul_assoc, hu]
    · rfl
  unfold lieD
  rw [e]

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Submodule ℂ (L2 (latticeGL E a) μ))

def formSpace (hH : IsSubrep (R (latticeGL E a) μ) H) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
    ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H}
  zero_mem' := by
    refine ⟨⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩, fun _ _ => rfl, ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (0 : Sm E a).1 := ⟨fun _ _ _ => rfl, MemLp.zero⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = 0 := MemLp.toLp_zero _
    rw [this]
    exact zero_mem _
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, h8⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a 1 φ ψ h1 h5
    rw [one_smul] at e
    refine ⟨e, fun t g => ?_, ?_⟩
    · exact congrArg₂ (· + ·) (h2 t g) (h6 t g)
    · have h : MemL2Quotient (latticeGL E a) μ (φ + ψ).1 := ⟨fun γ hγ g => congrArg₂ (· + ·) (h3.1 γ hγ g) (h7.1 γ hγ g), h3.2.add h7.2⟩
      refine ⟨h, ?_⟩
      have : h.toL2 = h3.toL2 + h7.toL2 := MemLp.toLp_add h3.2 h7.2
      rw [this]
      exact add_mem h4 h8
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    have hz : IsCuspForm (0 : Sm E a) :=
      ⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a c φ 0 h1 hz
    rw [add_zero] at e
    refine ⟨e, fun t g => congrArg (c • ·) (h2 t g), ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (c • φ).1 := ⟨fun γ hγ g => congrArg (c • ·) (h3.1 γ hγ g), h3.2.const_smul c⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = c • h3.toL2 := MemLp.toLp_const_smul c h3.2
    rw [this]
    exact H.smul_mem c h4


open GroundTheory.Automorphic in
theorem exists_stable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)) (_ : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) :
    ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ _root_.GlobalTheory.CuspRep.IsStable V := by
  have hS : IsSubrep (R (latticeGL E a) μ) H := hi.1
  refine ⟨formSpace μ H hS, fun φ => Iff.rfl, ?_⟩
  rintro o φ ⟨h1, h2, h3, h4⟩
  cases o with
  | fin k =>
    refine ⟨isCuspForm_fin k h1, fun t g => ?_, h3.mul_right (finGL E a k), ?_⟩
    · change φ.1 (splitCentre E a t * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | cpt k =>
    refine ⟨isCuspForm_cpt k h1, fun t g => ?_, h3.mul_right (infGL E a (Unitary.toUnits k)), ?_⟩
    · change φ.1 (splitCentre E a t * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | lie X =>
    letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _
    haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩
    obtain ⟨D, hD, hDc, hrep⟩ := _root_.GlobalTheory.CompanionTheory.LieConv.lie_eq_conv E a (Measure.haar : Measure (AutomorphicForm.archGroup E a)) φ h1.1 X
    have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h1.1.level
    obtain ⟨h', hW⟩ := GlobalTheory.T.l2_convolution_locally_compact_mem (latticeGL E a) μ (Measure.haar : Measure (AutomorphicForm.archGroup E a))
      (AutomorphicForm.infEmb E a) AutomorphicForm.continuous_infEmb D hD hDc φ.1 (lie E a X φ).1 hc h3 hrep
    refine ⟨⟨⟨fun γ g => lieD_left X (h1.1.left γ) g, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ h1.1.kfin,
      GlobalTheory.CuspStab.zfin_of_comm _ (fun z hz => _root_.GlobalTheory.CuspRep.Zalg_mul_lie E a X z hz) h1.1.zfin,
      _root_.GlobalTheory.CompanionTheory.GrowthConv.growth_conv E a _ φ.1 _ hc h1.1.growth D hD hDc hrep⟩, _root_.GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm E a X φ h1⟩,
      fun t g => lieD_left X (h2 t) g, h', hW H hS h4⟩
    exact GlobalTheory.CuspStab.level_of_le h1.1.level fun k hk => by
      change finRep E a k (lie E a X φ) = lie E a X φ
      change (rt E a (finGL E a k) * lie E a X) φ = _
      rw [← lie_rt_fin, Module.End.mul_apply]
      exact congrArg (lie E a X) hk

end GlobalTheory.CompanionTheory.StableMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
section
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisSo

theorem jCh : StdGood → BdetLaw → JTop → JCh := by
  intro hS hB _ F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hBase hi hJ
  have hL : (adStd F).GoodL := hS F
  obtain ⟨-, -, -, -, hk, hd⟩ := hB F 𝔸[F] (adStd F) hL (ι ⊕ ι) Set.univ
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) := by
    have h := Continuous.units_map (Matrix.detMonoidHom (n := ι ⊕ ι) (R := 𝔸[F]))
      (Continuous.matrix_det continuous_id)
    convert h using 1
    funext x
    apply Units.ext
    rfl
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hfst : Continuous fun x : cover A ν ι => x.1.1 := continuous_fst.comp continuous_subtype_val
  have hadd : ∀ p g : cover A ν ι, ld (p * g) = ld p + ld g := by
    intro p g
    simp only [ld, map_mul]
    exact hL.lgmul _ _
  have hK : ∀ k ∈ cK α j, ld k = 0 := by
    intro k hk'
    obtain ⟨κ, hκ, he⟩ := hk'.2
    have hdk : Matrix.GeneralLinearGroup.det (prj A ν ι k) = Matrix.GeneralLinearGroup.det κ := by
      rw [← he]
      simp [MulAut.conj_apply, map_mul, map_inv, mul_comm]
    have := hk κ (by intro r hr; exact absurd (Set.mem_univ r) hr) hκ
    rw [hd] at this
    simp only [ld, hdk]
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p _ q _
    simp [c0]
  · intro p _
    exact Circle.norm_coe _
  · intro γ hγ _
    obtain ⟨⟨x, hx⟩, -⟩ := hγ
    have := hG.toGoodL.χi x
    simp only [c0]
    have hx' : Units.map A.i.toMonoidHom x = γ.1.1 := hx
    rw [← hx', this]
    simp
  · exact (continuous_subtype_val.comp (hG.toGoodL.χcont.comp hfst)).continuousOn
  · intro p _ g
    exact hadd p g
  · intro g k hk'
    rw [hadd, hK k hk', add_zero]
  · intro γ hγ _
    obtain ⟨-, ⟨g, hg⟩⟩ := hγ
    have e : Matrix.GeneralLinearGroup.det (prj A ν ι γ) = Units.map (adStd F).i.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
      have hg' : Matrix.GeneralLinearGroup.map (adStd F).i g = γ.1.2 := hg
      show Matrix.GeneralLinearGroup.det γ.1.2 = _
      rw [← hg']
      apply Units.ext
      show ((Matrix.GeneralLinearGroup.map (adStd F).i g : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).det =
        (adStd F).i (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det
      rw [RingHom.map_det]
      rfl
    simp only [ld, e]
    exact hL.lgi _
  · exact hL.lgcont.comp (hdet.comp hprj)

end GlobalTheory.CompanionTheory.EisSo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactor
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelNM
open GlobalTheory.StdUnn.Model

theorem unip_mul_levi : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
    ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  intro D p q hq a ha
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  obtain ⟨m', hm'⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) (n := p) a⁻¹
  rw [inv_inv] at hm'
  have hmm : m * m' = 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_one, hm, hm',
      GlobalTheory.StdUnn.LeftInvSect.levi_mul_inv])
  have hmm' : m' * m = 1 := by
    rw [eq_inv_of_mul_eq_one_right hmm, inv_mul_cancel]
  have h2 : (adj (a⁻¹).1 : Mx D p p) * adj a.1 = 1 := by
    rw [← adj_mul]; simp [adj_one]
  refine ⟨m * u * m', m, a.1 * b * adj a.1, ?_, ?_, hm⟩
  · rw [mul_assoc (m * u), hmm', mul_one, e]
  · rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm, hu, hm']
    simp [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, h2, -Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.SiegelNM
end

