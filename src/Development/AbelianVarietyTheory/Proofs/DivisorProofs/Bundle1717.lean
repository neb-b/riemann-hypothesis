module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBlockScaledHasLatticeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PurityDepth

theorem hasDepth_scaled : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  intro k _ _ _ _ A' C _ _ _ _ ϖ P Ψ hΨ hϖ
  have hΨ' : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix A' C k) := hΨ
  have hϖ' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := fun x => by rw [hϖ, le_uniformizer_iff]
  obtain ⟨Λ, hΛ, hinv⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k A' C Ψ hΨ'
  let f : (A' × C → k) → Matrix A' C k := fun z => Matrix.of fun i j => z (i, j)
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_apply (i, j)
  have hΛn : f ⁻¹' (Λ : Set (Matrix A' C k)) ∈ nhds (0 : A' × C → k) :=
    (hΛ.preimage hf).mem_nhds (by
      show f 0 ∈ Λ
      exact (show f 0 = 0 from rfl) ▸ Λ.zero_mem)
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ q : A' × C, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix A' C k => x q.1 q.2) '' tsupport Ψ ⊆ GlobalTheory.SplitWeil.cball (ϖ ^ e)⁻¹ := fun q =>
    GlobalTheory.AdaptedExp.eventually_subset_cball hϖ' (hc.image (by fun_prop))
  obtain ⟨M, hM1, hM2⟩ := ((Filter.eventually_all.2 h1).and (GlobalTheory.AdaptedExp.eventually_box_subset hϖ' hΛn)).exists
  refine ⟨M, fun n hn => ?_⟩

  set w := valuation k (ϖ : k) with hw
  have hw1 : w ≤ 1 := hϖ.mem
  set u := valuation k ((ϖ ^ M : kˣ) : k) with hu
  have hu0 : 0 < u := zero_lt_iff.2 (by simp [hu])
  have huw : u = w ^ M := by rw [hu, Units.val_pow_eq_pow_val, map_pow]
  have hinvu : valuation k (((ϖ ^ M)⁻¹ : kˣ) : k) = u⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hn' : valuation k ((ϖ ^ n : kˣ) : k) ≤ u * u := by
    rw [Units.val_pow_eq_pow_val, map_pow, huw, ← pow_add, ← two_mul]
    exact pow_le_pow_right_of_le_one' hw1 hn
  have hd : ∀ (X : Matrix A' C k) i j, (X * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) i j = X i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)) :=
    fun X i j => mul_diagonal _ _ _ _
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · by_contra hne
    apply hY
    have hs := subset_tsupport _ hne
    have he : ∀ i j, valuation k (Y i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k))) ≤ u⁻¹ :=
      fun i j => by
        have := hM1 (i, j) ⟨_, hs, rfl⟩
        simpa only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, hd, hinvu] using this
    refine GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
    · have h := he i j
      rw [if_pos hj, map_mul, ← hu] at h
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j) ≤ u * u * valuation k (Y i j) :=
            mul_le_mul_left hn' _
        _ = u * (valuation k (Y i j) * u) := by rw [mul_assoc, mul_comm u (valuation k (Y i j))]
        _ ≤ u * u⁻¹ := mul_le_mul_right h _
        _ = 1 := mul_inv_cancel₀ hu0.ne'
    · have h := he i j
      rw [if_neg hj, map_mul, hinvu] at h
      rw [Valuation.mem_integer_iff]
      have := mul_le_mul_left h u
      rwa [mul_assoc, inv_mul_cancel₀ hu0.ne', mul_one] at this
  · obtain ⟨h1, h2⟩ := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.1 hZ
    show Ψ ((Y + Z) * _) = Ψ (Y * _)
    rw [Matrix.add_mul]
    refine hinv _ _ ?_
    refine hM2 (fun q => (Z * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) q.1 q.2) ?_
    unfold GlobalTheory.StepData.box
    intro q
    beta_reduce
    rw [hd, map_mul, ← hu]
    by_cases hj : q.2 ∈ P
    · rw [if_pos hj, ← hu]
      calc valuation k (Z q.1 q.2) * u ≤ 1 * u := mul_le_mul_left (h1 q.1 q.2 hj) _
        _ = u := one_mul u
    · rw [if_neg hj, hinvu]
      calc valuation k (Z q.1 q.2) * u⁻¹ ≤ u * u * u⁻¹ := mul_le_mul_left ((h2 q.1 q.2 hj).trans hn') _
        _ = u := by rw [mul_assoc, mul_inv_cancel₀ hu0.ne', mul_one]

end GlobalTheory.PurityDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  first | exact @GlobalTheory.VacUniq.sa_bd_uniq | exact GlobalTheory.VacUniq.sa_bd_uniq | (intros; apply GlobalTheory.VacUniq.sa_bd_uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductChar
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylTwist

open GlobalTheory.SympChange GlobalTheory.HeisSchA

theorem pure_mul_psi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  intro F _ _ ψ hψ hunr κ _ f φ y hφ hφO
  have hlc := GlobalTheory.SympUnip.psiAt_isLocallyConstant ψ hψ.1
  have hyint : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
    eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (y i)
  refine ⟨fun v => ⟨(hφ v).1.mul ((hlc v).comp_continuous (continuous_id.dotProduct continuous_const)),
    (hφ v).2.mul_right⟩, ?_, fun x => ?_⟩
  · filter_upwards [hunr, hφO, hyint] with v hv hφv hy
    funext z
    rw [hφv]
    by_cases hz : z ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · have hm : (z ⬝ᵥ fun i => evFin F v (y i)) ∈ v.adicCompletionIntegers F :=
        sum_mem fun i _ => mul_mem (hz i) (hy i)
      have h4 := (hv 1).2 (one_mem _) _ hm
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, mul_one]
    · rw [indO, Set.indicator_of_notMem hz, zero_mul]
  · have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφO, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl (F := F), evalV F v (p2 (x ⬝ᵥ y)) =
        (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := fun v =>
      RingHom.map_dotProduct (evFin F v : AF F →+* Fv F v) x y
    obtain ⟨hs, hp⟩ := GlobalTheory.SympUnip.finChar_eq_finprod ψ hψ.1 (p2 (x ⬝ᵥ y))
    simp only [hq] at hs hp
    let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    have h3 : ψ (mk (p1 (x ⬝ᵥ y)) 0) = eInf (fun i => evI F (x i)) (fun i => evI F (y i)) := by
      have e1 : evI F (mk (p1 (x ⬝ᵥ y)) 0) = (fun i => evI F (x i)) ⬝ᵥ fun i => evI F (y i) :=
        RingHom.map_dotProduct q x y
      rw [hψ.2.2 _ (at_mk _), e1, eInf]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [finprod_mul_distrib hfin hs, ← hp, map_eq_mul ψ (x ⬝ᵥ y), h3]
    ring

end GlobalTheory.WeylTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStable
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.SchwartzGaussDense

theorem dense_of_stdGaussian_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap E ℂ)) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  obtain ⟨W, hWN, hGW, hLW, hFW⟩ := _root_.GlobalTheory.exists_fourier_stable_gaussian_submodule E N G hG hGN hD hL
  obtain ⟨hLM, hFM⟩ := _root_.GlobalTheory.schwartz_closure_stable_linearForm_fourier E W hLW hFW
  set M := W.topologicalClosure with hMdef
  have hcl : IsClosed (M : Set (SchwartzMap E ℂ)) := W.isClosed_topologicalClosure
  have hGM : G ∈ M := W.le_topologicalClosure hGW
  have hgauss := _root_.GlobalTheory.GaussWidths.all_widths E M hcl hLM hFM G hG hGM
  have key : ∀ (h f : SchwartzMap E ℂ), (∃ b : ℝ, 0 < b ∧ ∀ y, f y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y) →
      f ∈ M := by
    rintro h f ⟨b, hb, hf⟩
    have hsub : {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
        ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} ⊆ (M : Set (SchwartzMap E ℂ)) := by
      rintro u ⟨c, s, hc, hu⟩
      by_cases hs : s = 0
      · have : u = 0 := by ext y; simp [hu y, hs]
        rw [this]; exact M.zero_mem
      · have hu' : ∀ y, (s⁻¹ • u) y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
            Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
          intro y
          rw [SchwartzMap.smul_apply, hu y, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
          congr 1; funext a; rw [hf a]
        have hmem := _root_.GlobalTheory.ConvSeries.mem_of_conv_gaussian E M hcl hLM b c hb hc (hgauss c hc) h (s⁻¹ • u) hu'
        have : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
        rw [this]; exact M.smul_mem s hmem
    exact closure_minimal hsub hcl (_root_.GlobalTheory.narrowGauss_convolution_dense E f)
  have hall : ∀ h : SchwartzMap E ℂ, h ∈ M := by
    intro h
    exact closure_minimal (fun f hf => key h f hf) hcl (_root_.GlobalTheory.GaussCutoff.mem_closure_gauss_mul E h)
  have htop : N.topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro h _
    exact Submodule.topologicalClosure_mono hWN (hall h)
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 htop

theorem dense_of_gaussian_mem : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  intro V _ _ _ N g Q c hc hQ hg hgN hD hL
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re V Q c hc hQ
  obtain ⟨N₂, hD₂, hL₂, hG₂, hdense⟩ := _root_.GlobalTheory.GaussTransport.transport V _ A Q N hA hD hL
  apply hdense
  let G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
  have hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    simp only [G, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    congr 1; push_cast; ring
  exact dense_of_stdGaussian_mem _ N₂ G hG (hG₂ g G hg hgN hG) hD₂ hL₂

end GlobalTheory.SchwartzGaussDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem comp_ev_mem_adm {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (hE : IsEv B M M₁ ι ι' I e)
    {l : Fn F n₁ d₁ →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) :
    l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have key := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  induction key using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨φ, h1, h2, rfl⟩ := hp
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := (h2.and hM.std).mono fun v h => h.1.trans h.2.symm
    have hψSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (h1 v)
    have hψstd : ∀ᶠ v in cofinite, ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM₁.std).mono fun v h => by rw [h.1, (hev v).1, h.2]
    obtain ⟨T, hT⟩ := hl _ ⟨isLocallyConstant_finprod_evalV _ hψSB hψstd,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ hψSB hψstd⟩
    refine ⟨T.comp ei, fun f => ?_⟩
    have h := hloc f φ h1 hvac
    rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l h
  | zero =>
    refine ⟨0, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) 0 = 0 := by
      funext x; simp [pureA]
    rw [this, map_zero, ContinuousLinearMap.zero_apply]
  | add p q _ _ hp hq =>
    obtain ⟨T₁, h₁⟩ := hp
    obtain ⟨T₂, h₂⟩ := hq
    refine ⟨T₁ + T₂, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (p + q) = pureA F f p + pureA F f q := by
      funext x; simp [pureA, mul_add]
    rw [this, map_add (f := _), h₁, h₂, ContinuousLinearMap.add_apply]
  | smul c p _ hp =>
    obtain ⟨T, hT⟩ := hp
    refine ⟨c • T, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (c • p) = c • pureA F f p := by
      funext x; simp [pureA]; ring
    rw [this, map_smul, hT, ContinuousLinearMap.smul_apply]

def schrLin {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := schr ψ w Φ
  map_add' Φ Ψ := by funext x; simp [schr, mul_add]
  map_smul' c Φ := by funext x; simp [schr]; ring

theorem schrLin_apply {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) : schrLin ψ w Φ = schr ψ w Φ := rfl

theorem schr_mem_schA {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have : schA F κ ≤ (schA F κ).comap (schrLin ψ w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
    show schrLin ψ w (pureA F f g) ∈ schA F κ
    rw [schrLin_apply, hT]
    exact Submodule.subset_span ⟨T f, g', hg', rfl⟩
  exact this hΦ

theorem comp_schr_mem_adm {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ schrLin ψ w ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
  obtain ⟨L, hL⟩ := hl g' hg'
  refine ⟨L.comp T, fun f => ?_⟩
  rw [LinearMap.comp_apply, schrLin_apply, hT, hL, ContinuousLinearMap.comp_apply]

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

end GlobalTheory.ConeMeasV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeCentraliserClassNumberFiniteBorel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls.Fin

theorem classes_finite_of_locus (hloc : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  fun D _ _ _ σ β y p _ => GlobalTheory.TorCls.Borel.classes_finite hloc GlobalTheory.classNumberFinite_holds D σ β y p

theorem classes_finite :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  classes_finite_of_locus GlobalTheory.TorLoc.exists_locus

end GlobalTheory.CentCls.Fin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartzStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitting_preserves_local_schwartz : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl (F := F)) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  first | exact @GlobalTheory.LocSplitOp.exists_locOp | exact GlobalTheory.LocSplitOp.exists_locOp | (intros; apply GlobalTheory.LocSplitOp.exists_locOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosetsStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_height_rpow_parabolicCosets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsFullLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  let _ : Submodule.IsFullLattice E L := hL
  first
  | exact GlobalTheory.SphEis.summable_height_rpow F E σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  | exact GlobalTheory.SphEis.summable_height_rpow F E σ n J j m C D Z J₀ hF L a (inferInstance : Submodule.IsLattice E L) hI h hh g t ht
end

