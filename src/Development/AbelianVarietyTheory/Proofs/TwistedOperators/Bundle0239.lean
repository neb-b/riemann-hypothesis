module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingSkew
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspL2

theorem exists_toLp_ext {G : Type} [MeasurableSpace G] (ν : Measure G) :
    ∃ E : (G → ℂ) →ₗ[ℂ] Lp ℂ 2 ν, ∀ φ, MemLp φ 2 ν → E φ =ᵐ[ν] φ := by
  classical
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | MemLp φ 2 ν}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := by
        first
          | exact MemLp.zero
          | exact MemLp.zero'
          | exact zero_memLp
          | simp
      smul_mem' := fun c _ h => h.const_smul c }
  let f : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun φ => MemLp.toLp (φ : G → ℂ) φ.2
      map_add' := fun φ ψ => MemLp.toLp_add φ.2 ψ.2
      map_smul' := fun c φ => MemLp.toLp_const_smul c φ.2 }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend f
  refine ⟨E, fun φ hφ => ?_⟩
  have hval : E φ = f ⟨φ, hφ⟩ := LinearMap.congr_fun hE ⟨φ, hφ⟩
  rw [hval]
  exact MemLp.coeFn_toLp hφ

theorem inner_eq {G : Type} [MeasurableSpace G] {ν : Measure G} {f f' : Lp ℂ 2 ν} {φ φ' : G → ℂ}
    (h : f =ᵐ[ν] φ) (h' : f' =ᵐ[ν] φ') : ⟪f, f'⟫_ℂ = ∫ g, (starRingEnd ℂ) (φ g) * φ' g ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with g hg hg'
  rw [hg, hg']
  first
    | (rw [RCLike.inner_apply]; try ring)
    | simp [mul_comm]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bounded (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) :
    ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B := by
  obtain ⟨ha, hs, hc, hg⟩ := h
  obtain ⟨-, -, hd⟩ := GlobalTheory.Size.rapidDec_of_cuspDecaySobolev hP hθ ha hs hg hc
  obtain ⟨C, hC⟩ := hd 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem conj_mul {G : Type} [TopologicalSpace G] {φ φ' : G → ℂ} (c : Continuous φ) (c' : Continuous φ')
    (b : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) (b' : ∃ B : ℝ, ∀ g, ‖φ' g‖ ≤ B) :
    Continuous (fun g => (starRingEnd ℂ) (φ g) * φ' g) ∧ ∃ B : ℝ, ∀ g, ‖(starRingEnd ℂ) (φ g) * φ' g‖ ≤ B := by
  obtain ⟨B, hB⟩ := b
  obtain ⟨B', hB'⟩ := b'
  refine ⟨(Complex.continuous_conj.comp c).mul c', max B 0 * max B' 0, fun g => ?_⟩
  calc ‖(starRingEnd ℂ) (φ g) * φ' g‖ = ‖φ g‖ * ‖φ' g‖ := by simp [norm_mul]
    _ ≤ max B 0 * max B' 0 :=
      mul_le_mul ((hB g).trans (le_max_left _ _)) ((hB' g).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)

theorem exists_embedding_skew : GlobalTheory.Published.CuspDecaySobolev → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧ (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' → IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') → ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  intro hP D θ V μ 𝓕 hθ hμ h𝓕
  haveI := hμ
  obtain ⟨-, -, -, iB, iT, -, iC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := iB
  haveI := iT
  haveI := iC
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 (And.intro hμ h𝓕)).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hmem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := bounded hP hθ hφ
    exact MemLp.of_bound hφ.1.cont.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hint : ∀ F : GA D V → ℂ, Continuous F → (∃ B : ℝ, ∀ g, ‖F g‖ ≤ B) → Integrable F (μ.restrict 𝓕) := by
    rintro F hF ⟨B, hB⟩
    exact memLp_one_iff_integrable.1 (MemLp.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall hB))
  obtain ⟨E, hE⟩ := exists_toLp_ext (μ.restrict 𝓕)
  refine ⟨E, fun φ hφ => ⟨hmem φ hφ, fun h0 => ?_⟩, ?_⟩
  · have h1 := hE φ (hmem φ hφ)
    rw [h0] at h1
    have hz : ⇑(0 : Lp ℂ 2 (μ.restrict 𝓕)) =ᵐ[μ.restrict 𝓕] (0 : GA D V → ℂ) := Lp.coeFn_zero ..
    have hae : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0 := by
      filter_upwards [h1, hz] with g a b
      rw [← a, b]
      rfl
    have hopen : IsOpen {g | φ g ≠ 0} := isOpen_ne_fun hφ.1.cont continuous_const
    haveI : SMulInvariantMeasure (GQ V) (GA D V) μ := by
      first
        | exact inferInstance
        | exact ⟨fun γ s _ => measure_preimage_mul μ (γ : GA D V) s⟩
    open Pointwise in
    have hinv : ∀ γ : GQ V, γ • {g | φ g ≠ 0} = {g | φ g ≠ 0} := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show φ ((γ⁻¹ : GQ V) * x) ≠ 0 ↔ φ x ≠ 0
      rw [hφ.1.left _ (γ⁻¹).2 x]
    have hnull : μ {g | φ g ≠ 0} = 0 := by
      refine h𝓕.measure_zero_of_invariant _ hinv ?_
      rw [← Measure.restrict_apply hopen.measurableSet]
      exact ae_iff.1 hae
    have hempty := (hopen.measure_eq_zero_iff μ).1 hnull
    funext g
    by_contra hne
    have hg : g ∈ {g | φ g ≠ 0} := hne
    rw [hempty] at hg
    exact hg
  · intro τ X hX φ φ' h1 h2 h3 h4
    rw [inner_eq (hE _ (hmem _ h3)) (hE _ (hmem _ h2)), inner_eq (hE _ (hmem _ h1)) (hE _ (hmem _ h4))]
    obtain ⟨c1, B1, b1⟩ := conj_mul h3.1.cont h2.1.cont (bounded hP hθ h3) (bounded hP hθ h2)
    obtain ⟨c2, B2, b2⟩ := conj_mul h1.1.cont h4.1.cont (bounded hP hθ h1) (bounded hP hθ h4)
    obtain ⟨c0, B0, b0⟩ := conj_mul h1.1.cont h2.1.cont (bounded hP hθ h1) (bounded hP hθ h2)
    rw [← integral_add (hint _ c1 ⟨B1, b1⟩) (hint _ c2 ⟨B2, b2⟩)]
    have key : ∀ ψ : GA D V → ℂ, ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → ∀ g t,
        HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X s)) (Rder θ V τ X ψ (g * oneP θ V τ X t)) t := by
      intro ψ hψ g t
      have d0 : HasDerivAt (fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) 0 :=
        ((GlobalTheory.Mem.AutSpace.differentiable_oneP hψ hX (g * oneP θ V τ X t)) 0).hasDerivAt
      have d1 : HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t)))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) t :=
        HasDerivAt.comp_sub_const (f := fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u)) t t
          (by rw [sub_self]; exact d0)
      refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show ψ (g * oneP θ V τ X s) = ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t))
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, show t + (s - t) = s by ring]
    have hd : ∀ g t, HasDerivAt
        (fun s : ℝ => (starRingEnd ℂ) (φ (g * oneP θ V τ X s)) * φ' (g * oneP θ V τ X s))
        ((starRingEnd ℂ) (Rder θ V τ X φ (g * oneP θ V τ X t)) * φ' (g * oneP θ V τ X t) +
          (starRingEnd ℂ) (φ (g * oneP θ V τ X t)) * Rder θ V τ X φ' (g * oneP θ V τ X t)) t := by
      intro g t
      exact ((key φ h1.2.1 g t).star).mul (key φ' h2.2.1 g t)
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (Φ' := fun g => (starRingEnd ℂ) (Rder θ V τ X φ g) * φ' g + (starRingEnd ℂ) (φ g) * Rder θ V τ X φ' g)
      (fun γ hγ g => by
        show (starRingEnd ℂ) (φ (γ * g)) * φ' (γ * g) = (starRingEnd ℂ) (φ g) * φ' g
        rw [h1.1.left γ hγ g, h2.1.left γ hγ g])
      c0 (c1.add c2) b0
      (fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero hθ) hd

end GlobalTheory.Chain.CuspL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DenInt

open IsDedekindDomain

theorem intRing_of_isIntegral {F : Type} [Field F] [NumberField F] {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Af F) c ∈ GlobalTheory.HolDict.ShortVec.intRing F := by
  refine GlobalTheory.HolDict.ShortVec.mem_intRing.2 fun v => ?_
  rw [AlgHom.commutes]
  refine Valued.toNormedField.norm_le_one_iff.2 ?_
  have := HeightOneSpectrum.valuation_le_one (K := F) v (⟨c, hc⟩ : 𝓞 F)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c).trans_le this

theorem exists_den (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  set b := Module.finBasis D.host.F D.host.E
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E
  obtain ⟨b', hb⟩ : ∃ b' : Fin (Module.finrank D.host.F D.host.E) → D.host.E,
      ∀ x k, Algebra.trace D.host.F D.host.E (b' k * x) = b.repr x k :=
    ⟨fun k => ((Algebra.traceForm D.host.F D.host.E).toDual (traceForm_nondegenerate D.host.F D.host.E)).symm (b.coord k),
      fun x k => LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate D.host.F D.host.E) (b.coord k) x⟩
  obtain ⟨d, hd, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (integralClosure ℤ D.host.E).toSubring b' fun k => by
    obtain ⟨k, hk, r, hr⟩ := GlobalTheory.SmoothForms.denom_exists_int (b' k)
    exact ⟨k, hk, hr ▸ r.2⟩
  refine ⟨d, hd, fun x hx k => ?_⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k = algebraMap D.host.F (Af D.host.F) (b.repr x k) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.algebraMap_eq_smul_one]
  have e2 : (d : D.host.F) * b.repr x k = Algebra.trace D.host.F D.host.E (((d : D.host.E) * b' k) * x) := by
    rw [← hb, mul_assoc, ← nsmul_eq_mul d (b' k * x), map_nsmul, nsmul_eq_mul]
  have hi : IsIntegral ℤ ((d : D.host.F) * b.repr x k) := by
    rw [e2]
    exact Algebra.isIntegral_trace ((h k).mul hx)
  rw [e1, ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul]
  exact intRing_of_isIntegral hi

end GlobalTheory.DenInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  first | exact @GlobalTheory.TwistDecomp.decomp_exists | exact GlobalTheory.TwistDecomp.decomp_exists | (intros; apply GlobalTheory.TwistDecomp.decomp_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatPairSep

variable {D : D7}

theorem eq_zero_of_trace_integralBasis (D : D7) (q : D.host.E)
    (h : ∀ k, Algebra.trace ℚ D.host.E (q * integralBasis D.host.E k) = 0) : q = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_
  have hl : (Algebra.traceForm ℚ D.host.E) q = 0 :=
    (integralBasis D.host.E).ext fun k => by
      rw [LinearMap.zero_apply, Algebra.traceForm_apply]; exact h k
  rw [hl, LinearMap.zero_apply]

theorem pairQ_sub (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E) :
    pairQ W y - pairQ W y' = pairQ W (y - y') := by
  have : adj D (y - y') = adj D y - adj D y' := by
    ext i j; simp [adj, Formalism.UG.cT]
  simp only [pairQ, this, Matrix.sub_mul, smul_sub]

theorem eq_of_pairQ_eq (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E)
    (h : pairQ W y = pairQ W y') : y = y' := by
  have h1 : adj D y * W.gram = adj D y' * W.gram := by
    have := congrArg (fun M => (D.host.xi0)⁻¹ • M) h
    simpa [pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] using this
  have h2 : adj D y = adj D y' := by
    have := congrArg (fun M => M * W.gram⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 j) i
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact (D.sp.cm.sig : D.host.E →+* D.host.E).injective this

theorem exists_sep (D : D7) (W : HSp D) (r : ℕ) :
    ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧
      ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  let ι := Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let e := Fintype.equivFin ι
  let Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E := fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)
  refine ⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩
  · intro j a b
    simp only [Y, Matrix.single_apply]
    split_ifs
    · rw [integralBasis_apply]; exact (RingOfIntegers.basis D.host.E _).isIntegral_coe
    · exact isIntegral_zero
  · intro y y' h
    apply eq_of_pairQ_eq W y y'
    rw [← sub_eq_zero, pairQ_sub]
    refine Matrix.ext fun l i => ?_
    rw [Matrix.zero_apply]
    refine eq_zero_of_trace_integralBasis D _ fun k => ?_
    have hj := h (e (i, l, k))
    simp only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj
    rw [← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub,
      Matrix.trace_mul_single] at hj
    simpa [MulOpposite.smul_eq_mul_unop] using hj

end GlobalTheory.RatPairSep

theorem GlobalTheory.RatPairSep.main : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E),
    (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E,
    (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := GlobalTheory.RatPairSep.exists_sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isKAct_of_stable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (hs : ∀ x ∈ kFin M τ, x ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
    (hd : ∀ X ∈ lieAt V τ, ∀ x ∈ kFin M τ, dRep (M.rep τ) X x ∈ kFin M τ) :
    ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  have hU : IsUnit (M.fr τ) := M.fr_unit τ
  have hG : IsUnit (gramAt D V τ) := GlobalTheory.SmVec.gram_unit hU (M.fr_gram τ)
  have hπ := GlobalTheory.SmVec.isURepOn_trRep hU (M.fr_gram τ) (M.ds τ).2.2.1
  refine ⟨fun X => if hX : X ∈ lieAt V τ then
    { toFun := fun v => ⟨dRep (M.rep τ) X v, hd X hX v v.2⟩
      map_add' := fun v w => Subtype.ext (GlobalTheory.SmVec.dRep_add (hs v v.2) (hs w w.2) hX)
      map_smul' := fun c v => Subtype.ext (GlobalTheory.SmVec.dRep_smul c (hs v v.2) hX) } else 0, ⟨?_, ?_⟩⟩
  · intro X hX v
    rw [dite_eq_left hX]
    exact GlobalTheory.SmVec.hasDerivAt_dRep (hs v v.2) hX
  · intro X hX v w
    rw [dite_eq_left hX, Submodule.coe_inner, Submodule.coe_inner]
    have key : ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = -⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ :=
      GlobalTheory.SmVec.inner_dRep hG hπ (hs v v.2) (hs w w.2) hX
    change ⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ + ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = 0
    linear_combination key

theorem kFin_smooth_isKAct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  intro D V S M τ p q T R φ m U hM
  have hk : ∀ y : M.H τ, y ∈ kFin M τ ↔ U y ∈ Set.range R.ι := fun y => hM.kfin y
  have hsm : ∀ y ∈ kFin M τ, y ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) := fun y hy =>
    GlobalTheory.SmVec.mem_smSub.2 (hM.smooth y ((hk y).1 hy))
  refine ⟨fun y hy => Submodule.subset_span (hM.smooth y ((hk y).1 hy)), exists_isKAct_of_stable M τ hsm ?_⟩
  intro X hX y hy
  rw [← hM.lie] at hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  obtain ⟨v, hv⟩ := (hk y).1 hy
  exact (hk _).2 ⟨_, (hM.der Z hZ v y hv.symm).symm⟩

end GlobalTheory.Chain.IoLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseIsotropicFrameKillingEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem exists_leftInv_frame_kill_emb : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  intro D V V' r C B hs
  have hadj : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), adj D X = Xᴴ := fun X => rfl
  have hG : V.gramᴴ = V.gram := by
    ext i j; simp [Matrix.conjTranspose_apply, GlobalTheory.LatVac.gram_star]
  have hBC : adj D B * V.gram * C = 0 := by
    have h := congrArg Matrix.conjTranspose hs.orth
    rw [hadj] at h ⊢
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f := C.mulVecLin.coprod B.mulVecLin
  have hf : ∀ c b, f (c, b) = C *ᵥ c + B *ᵥ b := fun c b => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨c, b⟩ h => ?_
    rw [hf] at h
    have h1 := congrArg ((adj D B * V.gram).mulVec) h
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBC, hs.isom, Matrix.zero_mulVec,
      zero_add, Matrix.mulVec_zero] at h1
    have hb : b = 0 := Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.LatVac.gram_det_isUnit V')) (by rw [h1, Matrix.mulVec_zero])
    subst hb
    rw [Matrix.mulVec_zero, add_zero] at h
    have hc : c = 0 := Matrix.mulVec_injective_iff.2 hs.frame.2.1 (by rw [h, Matrix.mulVec_zero])
    subst hc
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have key : ∀ c b, g (C *ᵥ c + B *ᵥ b) = (c, b) := fun c b => by
    rw [← hf]; exact LinearMap.congr_fun hg (c, b)
  have k1 : ∀ c, g (C *ᵥ c) = (c, 0) := fun c => by simpa using key c 0
  have k2 : ∀ b, g (B *ᵥ b) = (0, b) := fun b => by simpa using key 0 b
  refine ⟨LinearMap.toMatrix' (LinearMap.fst _ _ _ ∘ₗ g), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k1]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k2]

end GlobalTheory.HalfAverage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPosIntegralHalfAdelicMatrixLeftMulEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem integral_leftMul_eq_smul : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)),
    M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ,
      ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  intro D a m n M M' h1 h2
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : SecondCountableTopology (Mx D m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : SecondCountableTopology (halfMx a m n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hc : ∀ N : Matrix (Fin m) (Fin m) (AE D), Continuous (leftMul a (n := n) N) := fun N =>
    (continuous_const.matrix_mul continuous_subtype_val).subtype_mk _
  let e : halfMx a m n ≃ₜ+ halfMx a m n :=
    { toFun := leftMul a M
      invFun := leftMul a M'
      left_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h2, Matrix.one_mul])
      right_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h1, Matrix.one_mul])
      map_add' := fun x y => Subtype.ext (by
        rw [AddSubgroup.coe_add, leftMul_coe, leftMul_coe, leftMul_coe, AddSubgroup.coe_add, Matrix.mul_add])
      continuous_toFun := hc M
      continuous_invFun := hc M' }
  haveI : ((haarHalf a m n).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have heq := Measure.isAddLeftInvariant_eq_smul ((haarHalf a m n).map e) (haarHalf a m n)
  refine ⟨(Measure.addHaarScalarFactor ((haarHalf a m n).map e) (haarHalf a m n) : ℝ),
    by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, fun φ => ?_⟩
  let em : halfMx a m n ≃ᵐ halfMx a m n := e.toHomeomorph.toMeasurableEquiv
  have h3 : ∫ t, φ (leftMul a M t) ∂haarHalf a m n = ∫ t, φ t ∂((haarHalf a m n).map e) := by
    have := integral_map_equiv (μ := haarHalf a m n) em φ
    exact this.symm
  have h4 := congrArg (fun μ : Measure (halfMx a m n) => ∫ t, φ t ∂μ) heq
  rw [h3, h4, integral_smul_nnreal_measure]
  simp [Complex.real_smul, NNReal.smul_def]

end GlobalTheory.HalfAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → (∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, heckeVec ρ (KGL w (n := n)) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound | exact GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound | (intros; apply GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratMx D m n) 𝓕 μ → ∀ c : Mx D m n → ℂ, Integrable c μ → (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧ ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  first | exact @GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | exact GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | (intros; apply GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum <;> assumption)
end

