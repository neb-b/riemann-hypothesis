module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
section
open NumberField Matrix

namespace GlobalTheory.FlagMeas

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_congr_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature M p q) (f : Fin n ≃ Fin p ⊕ Fin q) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.det ≠ 0 ∧
      Aᵀ * Mᵀ * A.map (starRingEnd ℂ) = ((Formalism.UG.Jpq p q).submatrix f f)ᵀ := by
  obtain ⟨e, P, hP⟩ := h
  have hPu : IsUnit (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f, ?_, ?_⟩
  · have hσ : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f =
        ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j; simp
    rw [hσ, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    exact mul_ne_zero (by simp) hPu.ne_zero
  · have hM : M = (M.reindex e e).submatrix e e := by ext i j; simp
    have hA : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f)ᴴ * M *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f = (Formalism.UG.Jpq p q).submatrix f f := by
      rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hP]
      congr 1
    rw [← hA]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.conjTranspose]
    rfl

theorem sameKindIsometric : SameKindIsometric := by
  intro E _ _ _ hE n J J' hJ hJ' hd hd' hΛ hΛ' hsig
  obtain ⟨hTC, hφ, hun⟩ := hE
  have hne : ∃ z : E, star z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc := hTC.isComplex w
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hφ, hcon]
  obtain ⟨hcm, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff E star).1
    ⟨fun φ z => by rw [hφ]; rfl, hne⟩
  have := hcm
  have hcc : ∀ z : E, star z = cc z := fun z => congrFun hst z
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    refine Formalism.L2.Pj.unramBridge_holds E fun P hP => ?_
    obtain ⟨θ, t, ht, hθ⟩ := hun P hP
    refine ⟨θ, ?_⟩
    convert hθ using 2
    ext
    simp [ht, hcc, cc]
  have hform : ∀ (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
      ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y = star y ⬝ᵥ (M *ᵥ x) := by
    intro M x y
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Pi.star_apply, hcc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ z ∈ (algebraMap (𝓞 E) E).range := by
    intro z
    rw [FractionalIdeal.mem_one_iff, RingHom.mem_range]
  have hmod : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      ∀ x, x ∈ L ↔ ∀ y ∈ L, ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro M L h x
    simp only [hone, hform]
    exact h x
  have hherm : ∀ M : Matrix (Fin n) (Fin n) E, Mᴴ = M → ∀ a b, cc (Mᵀ a b) = Mᵀ b a := by
    intro M hM a b
    rw [← hcc]
    have := congrFun (congrFun hM a) b
    simpa [Matrix.conjTranspose_apply] using this
  have hc : ∀ z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), cc z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro z hz
    rw [FractionalIdeal.mem_one_iff] at hz ⊢
    obtain ⟨x, rfl⟩ := hz
    exact ⟨IsCMField.ringOfIntegersComplexConj E x, by simp [cc]⟩
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      J'ᵀ.map τ = Qᵀ * Jᵀ.map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨p, q, h1, h2⟩ := hsig τ
    obtain ⟨e, -, -⟩ := id h1
    obtain ⟨A, hA, hA'⟩ := exists_congr_of_hasSignature h1 e
    obtain ⟨B, hB, hB'⟩ := exists_congr_of_hasSignature h2 e
    have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hB)
    refine ⟨A * B⁻¹, by simp [Matrix.det_nonsing_inv, hA, hB], ?_⟩
    rw [Matrix.transpose_map, Matrix.transpose_map]
    have h1' : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBi, Matrix.transpose_one]
    have h2' : B.map (starRingEnd ℂ) * (B⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hBi]
      simp
    have hY : (J'.map τ)ᵀ = (B⁻¹)ᵀ * (Bᵀ * (J'.map τ)ᵀ * B.map (starRingEnd ℂ)) *
        (B⁻¹).map (starRingEnd ℂ) := by
      simp only [← Matrix.mul_assoc]
      rw [h1', Matrix.one_mul, Matrix.mul_assoc, h2', Matrix.mul_one]
    rw [hY, hB', ← hA', Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Λ, hΛl, hΛm⟩ := hΛ
  obtain ⟨Λ', hΛl', hΛm'⟩ := hΛ'
  have hspan : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsLattice E L →
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    intro M L hl hm
    classical
    obtain ⟨s, hs⟩ := hl.fg
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
      (s.image fun y => star y ⬝ᵥ (M *ᵥ z))
    have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 E) E).ne (nonZeroDivisors.ne_zero d.2)
    have hdz : (algebraMap (𝓞 E) E d) • z ∈ L := by
      apply (hm _).2
      intro y hy
      rw [← hs] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha⟩ := hd _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
        refine ⟨a, ?_⟩
        rw [Matrix.mulVec_smul, dotProduct_smul]
        simpa only [smul_eq_mul, Algebra.smul_def] using ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        simpa [star_add, add_dotProduct] using add_mem ihx ihy
      | smul a x hx ih =>
        have ha : star (algebraMap (𝓞 E) E a) ∈ (algebraMap (𝓞 E) E).range := by
          rw [hcc]
          exact ⟨IsCMField.ringOfIntegersComplexConj E a, by simp [cc]⟩
        have he : star (a • x) = star (algebraMap (𝓞 E) E a) • star x := by
          ext i
          simp [Algebra.smul_def]
        rw [he, smul_dotProduct]
        simpa only [smul_eq_mul] using mul_mem ha ih
    have hz : z = (algebraMap (𝓞 E) E d)⁻¹ • ((algebraMap (𝓞 E) E d) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdz)
  obtain ⟨P, hPd, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt
    (by
      intro h
      have h1 : (1 : E) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [FractionalIdeal.mem_one_iff]
        exact ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at h1
      exact one_ne_zero h1) hc (hherm J hJ) (hherm J' hJ') (by rwa [Matrix.det_transpose])
    (by rwa [Matrix.det_transpose]) ⟨hΛl.fg, hspan J Λ hΛl hΛm⟩
    ⟨hΛl'.fg, hspan J' Λ' hΛl' hΛm'⟩
    (hmod J Λ hΛm) (hmod J' Λ' hΛm') hs
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hPd, ?_⟩
  have hT := congrArg Matrix.transpose hP
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at hT
  change Pᴴ * J * P = J'
  rw [hT, Matrix.mul_assoc]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, hcc]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF

variable {n : ℕ}

lemma toMK_cont (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

lemma inner_rep {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn G σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G)
    (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map (⟨(σ g : H →ₗ[ℂ] H), h.2.1 g hg⟩ : H →ₗᵢ[ℂ] H) x y

lemma inner_rep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (Kset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε) (x y : H) : ⟪σ g x, y⟫_ℂ = ⟪x, σ (star g) y⟫_ℂ := by
  rw [← inner_rep h hg x, ← ContinuousLinearMap.comp_apply (σ g) (σ (star g)), ← h.1.2 _ hg _ (Kset_star ε hg),
    Unitary.mul_star_self_of_mem hg.1, h.1.1, ContinuousLinearMap.one_apply]

theorem rangeType : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : S →L[ℂ] H'), IsKTypeOf ε σ abelian₂ S → (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ' k (T x)) → T ≠ 0 → IsKTypeOf ε σ' abelian₂ (LinearMap.range (T : S →ₗ[ℂ] H')) := by
  intro n ε abelian₂ H _ _ σ S H' _ _ σ' T hS hT hT0
  haveI := hS.1
  have hinj : Function.Injective T := by
    rcases hS.2.2.1 ((LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x = 0 := hx
      change T _ = 0
      rw [hT k hk x _ rfl, hx', map_zero]) with h | h
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext this
    · exfalso
      apply hT0
      ext x
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  have hT' : ∀ k (hk : k ∈ Kset ε) (x : S), σ' k (T x) = T ⟨σ k x, hS.2.1 k hk x x.2⟩ :=
    fun k hk x => (hT k hk x _ rfl).symm
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro k hk _ ⟨x, rfl⟩
    exact ⟨_, (hT' k hk x).symm⟩
  · intro S' hle hst
    rcases hS.2.2.1 ((S'.comap (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x ∈ S' := hx
      change T _ ∈ S'
      rw [← hT' k hk x]
      exact hst k hk _ hx') with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := hle hz
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hz, rfl⟩
      rw [h] at this
      have : x = 0 := Subtype.ext this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, rfl⟩
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨T ⟨v, hv⟩, ⟨_, rfl⟩, fun h => hv0 (congrArg Subtype.val (hinj (h.trans (map_zero T).symm))), ?_⟩
    intro θ hθ
    rw [← map_smul]
    exact (hT _ hθ ⟨v, hv⟩ _ (hwt θ hθ).symm).symm
  · rintro μ _ ⟨x, rfl⟩ h0 hwt
    refine hS.2.2.2.2 μ x x.2 (fun h => h0 (by have : x = 0 := Subtype.ext h; simp [this])) fun θ hθ => ?_
    have := hwt θ hθ
    change σ' _ (T x) = _ • T x at this
    rw [hT' _ hθ, ← map_smul] at this
    exact congrArg Subtype.val (hinj this)

theorem psEntry : PhiPos → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → (∀ v : W, ContinuousOn (fun k => τ k v) (Kset ε)) → ∀ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef → ∀ u y : W, ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  intro hP n ε lam W _ _ τ w hW hτ x hx u y
  haveI := FiniteDimensional.complete ℂ W
  have hk : Continuous (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) := (hτ w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finsetProd _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix _ _).matrix_det
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1))).1 i
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

theorem muConj : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), ∫ k : KG ε, F ((toMK k).map star) ∂(muK ε) = ∫ k : KG ε, F (toMK k) ∂(muK ε) := by
  intro n ε F
  let c0 : (Matrix (Fin n) (Fin n) ℂ)ˣ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.map (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom
  let c : KG ε → KG ε := fun k => ⟨⟨c0 k.1.1, UJ_star k.1.2⟩, K_star k.2⟩
  have hc : ∀ k, toMK (c k) = (toMK k).map star := fun k => rfl
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hcc : ∀ k, c (c k) = k := fun k => hemb.injective (by simp only [hc, map_star_star])
  have hcont : Continuous c := by
    rw [hemb.continuous_iff]
    exact hemb.continuous.matrix_map continuous_star
  let e : KG ε ≃ₜ* KG ε :=
    { toFun := c, invFun := c, left_inv := hcc, right_inv := hcc
      map_mul' := fun a b => hemb.injective (by
        change (toMK a * toMK b).map star = (toMK a).map star * (toMK b).map star
        exact map_star_mul _ _)
      continuous_toFun := hcont, continuous_invFun := hcont }
  haveI := (compact_haar_holds n ε).1
  haveI : IsProbabilityMeasure ((muK ε).map e) := inferInstance
  haveI : ((muK ε).map e).IsHaarMeasure := e.isHaarMeasure_map _
  have h : (muK ε).map e = muK ε := Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  have := integral_map_equiv (μ := muK ε) e.toHomeomorph.toMeasurableEquiv (fun k => F (toMK k))
  rw [show (muK ε).map e.toHomeomorph.toMeasurableEquiv = muK ε from h] at this
  exact this.symm

theorem avgMap : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (u : H), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → CompleteSpace H → IsURepOn (Kset ε) σ → ∃ T : W →L[ℂ] H, (∀ k ∈ Kset ε, ∀ x, T (ρ k x) = σ k (T x)) ∧ ∀ (x : W) (φ : H →L[ℂ] ℂ), Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u)) (muK ε) ∧ φ (T x) = ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u) ∂(muK ε) := by
  intro n ε W _ _ ρ w H _ _ σ u hW hρ hH hσ
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h2 : Continuous (fun k : KG ε => σ (toMK k) u) := (hσ.2.2 u).comp_continuous (toMK_cont ε) fun k => k.2
  have hi : ∀ x : W, Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u) (muK ε) := fun x =>
    ((h1.inner continuous_const).smul h2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T : W →ₗ[ℂ] H :=
    { toFun := fun x => ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)
      map_add' := fun x y => by simp only [inner_add_right, add_smul]; exact integral_add (hi x) (hi y)
      map_smul' := fun c x => by simp only [inner_smul_right, mul_smul, integral_smul, RingHom.id_apply] }
  refine ⟨LinearMap.toContinuousLinearMap T, fun k hk x => ?_, fun x φ => ⟨?_, ?_⟩⟩
  · obtain ⟨k0, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
    change ∫ k : KG ε, ⟪ρ (toMK k) w, ρ (toMK k0) x⟫_ℂ • σ (toMK k) u ∂(muK ε) =
      σ (toMK k0) (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x), ← integral_mul_left_eq_self _ k0]
    congr 1
    funext k
    have e : toMK (k0 * k) = toMK k0 * toMK k := rfl
    simp only [e, hρ.1.2 _ k0.2 _ k.2, hσ.1.2 _ k0.2 _ k.2, ContinuousLinearMap.comp_apply, inner_rep hρ k0.2,
      map_smul]
  · simpa using φ.integrable_comp (hi x)
  · change φ (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x)]
    simp

theorem avgSchur : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ W, IsKStableOn ε ρ S → S = ⊥ ∨ S = ⊤) → w ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ (x : W) (φ : W →L[ℂ] ℂ), ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (ρ (toMK k) w) ∂(muK ε) = c * φ x := by
  intro n ε W _ _ ρ w hW hρ hirr hw
  haveI := FiniteDimensional.complete ℂ W
  haveI : Nontrivial W := ⟨⟨w, 0, hw⟩⟩
  obtain ⟨T, hT, hTi⟩ := avgMap n ε W ρ w W ρ w hW hρ inferInstance hρ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : W →ₗ[ℂ] W)
  have hTc : ∀ x, T x = c • x := by
    rcases hirr (Module.End.eigenspace (T : W →ₗ[ℂ] W) c) (fun k hk x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change T _ = _ at hx ⊢
      rw [hT k hk, hx, map_smul]) with h | h
    · exact absurd h hc
    · intro x
      have : x ∈ Module.End.eigenspace (T : W →ₗ[ℂ] W) c := by rw [h]; trivial
      exact Module.End.mem_eigenspace_iff.1 this
  refine ⟨c, ?_, fun x φ => by rw [← (hTi x φ).2, hTc, map_smul, smul_eq_mul]⟩
  rintro rfl
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h0 := (hTi w (innerSL ℂ w)).2
  rw [hTc, zero_smul, map_zero] at h0
  have e : ∀ k : KG ε, ⟪ρ (toMK k) w, w⟫_ℂ * innerSL ℂ w (ρ (toMK k) w) =
      ((‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [innerSL_apply_apply, ← inner_conj_symm, Complex.conj_mul']; simp
  simp only [e, integral_ofReal] at h0
  have hc2 : Continuous (fun k : KG ε => ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2) := (continuous_const.inner h1).norm.pow 2
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := 1)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (by
      have : toMK (1 : KG ε) = 1 := rfl
      simpa [this, hρ.1.1] using hw)
  have : (0 : ℝ) = ∫ k : KG ε, ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) := by exact_mod_cast h0
  linarith

end GlobalTheory.Dec.FormF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPointsStatement
section
open NumberField GlobalTheory.HL
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabiliser_commensurable_integralPoints : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  exact GlobalTheory.HL.CommInt.stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le A r k G hk Λ
    (by first | exact hΛ | exact hΛ.toIsLattice)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDecOfDecGapGapGe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem locDec_of_decGap_gapGe : DecGap → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h →
    (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h := by
  intro hD B d h hds hgap hh v g
  obtain ⟨h1, h2, h3, -⟩ := hds v
  have hw : B.w v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v) := h3.2
  have hn : ‖B.w v‖ = 1 := h3.1
  have := (hD _ _ _ _ _ h1 h2 h (hgap v) (hh v) (uMat g) g.2 _ hw _ hw).2
  simpa [hn] using this

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Count.CartanSize

open GlobalTheory.Count.Cartan

theorem cartan_size : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  intro n ε
  have hU : ∀ g : UJ ε, Formalism.REAL.inUJ ε (uMat g) := fun g => g.2
  have hnn : ∀ g : Matrix (Fin n) (Fin n) ℂ, 0 ≤ dHS g := fun g => Real.sqrt_nonneg _
  obtain ⟨-, hB, -, hC, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro g
    refine ⟨hnn _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.Dec.dOp_fin_zero]
      exact hnn _
    · obtain ⟨h0, -, -, h2, -⟩ := hB g g (by omega)
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
  · intro g
    exact ⟨uMat g * NormedSpace.exp (-Formalism.REAL.polarLog (uMat g)), Formalism.REAL.mul_exp_neg_polarLog_mem_compact (hU g),
      Formalism.REAL.polarLog (uMat g), Formalism.REAL.polarLog_mem_hermitian_part (hU g), Formalism.REAL.polar_decomposition_eq,
      GlobalTheory.Count.Cartan.dHS_eq_log (hU g)⟩
  · intro hr g
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dHS]
    · obtain ⟨-, -, -, -, h3⟩ := hB g g (by omega)
      simp only [hr, Nat.cast_zero, mul_zero, Real.sqrt_zero, zero_mul] at h3
      exact le_antisymm h3 (hnn _)

end GlobalTheory.Count.CartanSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfanStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (ρ : Gn g i → ℂ), i ≤ k → IsClass ρ → ∀ h : Gn g k, indR ψ i (k + 1) ρ (diag1 h (k + 1)) = hc i (k - i) ρ (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.indR_diag1_eq_hc_gg | exact GlobalTheory.GLm.indR_diag1_eq_hc_gg | (intros; apply GlobalTheory.GLm.indR_diag1_eq_hc_gg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointConjMemCongruenceSubgroupOfCongrLatticeStatement
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointConj_mem_congruenceSubgroup_of_congr_lattice : ∀ (I : AutInst) (x a : I.GA) (g : ℕ) (γ : GL (Fin I.n) I.E), I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (∀ y ∈ lamX I x, ∃ z ∈ lamX I x, ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y = (g : I.E) • z) → (∀ y ∈ lamX I x, ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) → (x⁻¹ * a * x).2 ∈ I.Kg g := by
  first | exact @GlobalTheory.PointLattice.conj_mem_Kg_of_congr | exact GlobalTheory.PointLattice.conj_mem_Kg_of_congr | (intros; apply GlobalTheory.PointLattice.conj_mem_Kg_of_congr <;> assumption)
end

