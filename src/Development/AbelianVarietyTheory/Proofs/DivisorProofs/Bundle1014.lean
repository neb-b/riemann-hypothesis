module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.StdCharWeilDatum

section Char

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : At (evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) : ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (y : Af F) : ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Char

section Trace

variable {F : Type} [Field F] [NumberField F]

theorem sum_eq_trace (x : Ainf F) :
    ∑ v : InfinitePlace F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_infFam [IsTotallyReal F] (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (hθ : Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ) (x : Ainf F) :
    ∑ w, θ w (x ⊗ₜ[F] (1 : E)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) := by
  rw [← sum_eq_trace]
  push_cast
  refine Fintype.sum_congr _ _ fun w => ?_
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x,
    InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
    Complex.ofReal_re]
  simp

theorem isStdCharF_of_isGood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring

end GlobalTheory.StdCharWeilDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummablePartialFourierAdelicSchwartzRationalPair
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.PartialFourierSum

open GroundTheory.Global NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adelicFourierPi_mul (f : (κ → mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ → AdeleRing (𝓞 F) F) :
    adelicFourierPi F (fun x => f (infPartPi x) * g (finPartPi x)) y =
      mixedFourierPi F f (infPartPi y) * finiteFourierPi F g (finPartPi y) := by
  have h := integral_prod_mul (μ := mixedMeasurePi F) (ν := finiteMeasurePi F)
    (fun u ↦ 𝐞 (-mixedPairingPi F u (infPartPi y)) • f u)
    (fun v ↦ g v * (finiteAdelicChar F (∑ i, v i * finPartPi y i) : ℂ))
  have e := measurePreserving_splitEquivPi.integral_comp' (μ := adeleMeasurePi F)
    (f := splitEquivPi F κ) (fun p : (κ → mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) ↦
      (𝐞 (-mixedPairingPi F p.1 (infPartPi y)) • f p.1) *
        (g p.2 * (finiteAdelicChar F (∑ i, p.2 i * finPartPi y i) : ℂ)))
  rw [mixedFourierPi, finiteFourierPi, ← h, ← e, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [splitEquivPi_apply, adelicChar_sum_mul_eq_pi, Circle.smul_def, smul_eq_mul]
  ring

theorem exists_summable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (κ → mixedSpace F) ≃L[ℝ] E)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Summable fun ξ : κ → F => ((1 + ‖L (embPi F ξ)‖) ^ k)⁻¹ *
      ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ := by
  obtain ⟨k₀, M, hM, hb⟩ := GlobalTheory.SchwartzMajorant.exists_majorant_pureA F (g := g) hg 0
  refine ⟨k₀, fun k hk => ?_⟩
  set c : ℝ := ‖(L.symm : E →L[ℝ] (κ → mixedSpace F))‖ with hc
  have hn : ∀ v, ‖((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ)‖ = ((1 + ‖L v‖) ^ k)⁻¹ := fun v => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb' := hb 1 (c ^ k₀) (fun v => ((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ))
    (fun v => by
      rw [hn]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (L v)])))
    (fun v => by
      rw [hn, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have h1 : ‖v‖ ≤ c * ‖L v‖ := by
        simpa using (L.symm : E →L[ℝ] (κ → mixedSpace F)).le_opNorm (L v)
      have hc0 : 0 ≤ c := norm_nonneg _
      calc ‖v‖ ^ k₀ ≤ (c * (1 + ‖L v‖)) ^ k₀ :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans (by nlinarith [norm_nonneg (L v)])) _
        _ = c ^ k₀ * (1 + ‖L v‖) ^ k₀ := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [norm_nonneg (L v)]) hk) (by positivity))
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) (hM.mul_left (1 + c ^ k₀))
  have h := hb' ξ
  rw [GlobalTheory.SchwartzMajorant.pureA_add_algebraMap, norm_mul, hn] at h
  have e1 : ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((0 : κ → AdeleRing (𝓞 F) F) j).1) = embPi F ξ := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, embPi]
    rw [show (0 : AdeleRing (𝓞 F) F).1 = 0 from rfl, map_zero, add_zero]
  have e2 : ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j =>
      ((0 : κ → AdeleRing (𝓞 F) F) j).2) = fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j) := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [show (0 : AdeleRing (𝓞 F) F).2 = 0 from rfl, add_zero]
  rw [e1, e2] at h
  exact h

def shear : ((κ → mixedSpace F) × EuclidPi F κ) ≃L[ℝ] (κ ⊕ κ → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => Sum.elim ((toEuclidPi F).symm p.2 + p.1) ((toEuclidPi F).symm p.2)
      map_add' := fun p q => by
        funext i
        rcases i with i | i
        · simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Sum.elim_inl, Pi.add_apply]; abel
        · simp only [Prod.snd_add, map_add (f := _), Sum.elim_inr, Pi.add_apply]
      map_smul' := fun a p => by
        funext i
        rcases i with i | i
        · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
            RingHom.id_apply, smul_add]
        · simp only [Prod.smul_snd, map_smul, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      invFun := fun x => (fun i => x (Sum.inl i) - x (Sum.inr i), toEuclidPi F fun i => x (Sum.inr i))
      left_inv := fun p => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]; abel
        · simp only [Sum.elim_inr]
          exact (toEuclidPi F).apply_symm_apply p.2
      right_inv := fun x => by
        funext i
        rcases i with i | i
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inr] }

theorem arch_bound (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ u v : κ → mixedSpace F, ‖mixedFourierPi F (fun t => f (Sum.elim (t + u) t)) v‖ ≤
      C * (((1 + ‖u‖) ^ k)⁻¹ * ((1 + ‖toEuclidPiConj F v‖) ^ k)⁻¹) := by
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay (κ → mixedSpace F) (EuclidPi F κ)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (shear (F := F) (κ := κ)) f) k
  refine ⟨C, fun u v => ?_⟩
  have h := hC u (toEuclidPiConj F v)
  rw [mixedFourierPi_eq, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem finiteTensor_shift (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)
    (u t : κ → FiniteAdeleRing (𝓞 F) F) :
    finiteTensor (fun i => cosetIndicator J (b i)) (Sum.elim (t + u) t) =
      finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) u *
        finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) t := by
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [cosetIndicator_apply]
  by_cases h : t i - b (Sum.inr i) ∈ idealFiniteAdeles J
  · have : t i + u i - b (Sum.inl i) ∈ idealFiniteAdeles J ↔
        u i - (b (Sum.inl i) - b (Sum.inr i)) ∈ idealFiniteAdeles J := by
      rw [show t i + u i - b (Sum.inl i) = (t i - b (Sum.inr i)) + (u i - (b (Sum.inl i) - b (Sum.inr i))) by ring]
      exact AddSubgroup.add_mem_cancel_left _ h
    simp only [this]
  · simp only [if_neg h, mul_zero]

theorem summable_gen (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F =>
      schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  set g₁ := finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) with hg₁
  set g₂ := finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) with hg₂
  have m₁ : g₁ ∈ finiteSchwartzBruhatPi F :=
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _
  have m₂ : finiteFourierPi F g₂ ∈ finiteSchwartzBruhatPi F :=
    finiteFourierPi_mem (finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _)
  obtain ⟨k₁, h₁⟩ := exists_summable (ContinuousLinearEquiv.refl ℝ (κ → mixedSpace F)) m₁
  obtain ⟨k₂, h₂⟩ := exists_summable (toEuclidPiConj F) m₂
  obtain ⟨C, hC⟩ := arch_bound f (max k₁ k₂)
  have hs := ((h₁ _ (le_max_left k₁ k₂)).mul_of_nonneg (h₂ _ (le_max_right k₁ k₂))
    (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) hs
  have key : (fun t : κ → AF F => schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) =
      fun t => (fun s => f (Sum.elim (s + embPi F uv.1) s)) (infPartPi t) *
        (g₁ (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) • g₂) (finPartPi t) := by
    funext t
    have e1 : infPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (infPartPi t + embPi F uv.1) (infPartPi t) := by
      rw [← infPartPi_algebraMap]
      funext i
      rcases i with i | i
      · simp only [infPartPi, Sum.elim_inl, Pi.add_apply, homeomorphMixedSpace_apply]
        exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
      · rfl
    have e2 : finPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (finPartPi t + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) (finPartPi t) := by
      rw [← finPartPi_algebraMap]
      funext i
      rcases i with i | i <;> rfl
    rw [schwartzBruhatTensorPi, e1, e2, finiteTensor_shift]
    rfl
  rw [key, adelicFourierPi_mul (fun s => f (Sum.elim (s + embPi F uv.1) s)), finiteFourierPi_smul, infPartPi_algebraMap, finPartPi_algebraMap, norm_mul,
    Pi.smul_apply, smul_eq_mul, norm_mul]
  refine (mul_le_mul_of_nonneg_right (hC _ _) (by positivity)).trans (le_of_eq ?_)
  simp only [ContinuousLinearEquiv.refl_apply]
  ring

theorem summable_partial_fourier : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  intro F _ _ κ _ φ hφ
  have hS : schA F (κ ⊕ κ) = cosetSpanPi F (κ ⊕ κ) := by
    rw [← schwartzBruhatPi_eq_cosetSpanPi]
    refine congrArg (Submodule.span ℂ) (Set.ext fun Φ => ?_)
    exact ⟨fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩, fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩⟩
  have hI : ∀ ψ ∈ cosetSpanPi F (κ ⊕ κ), ∀ u : κ → AF F,
      Integrable (fun t : κ → AF F => ψ (Sum.elim (t + u) t)) (adeleMeasurePi F) := fun ψ hψ u =>
    integrable_of_mem_schwartzBruhatPi (GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi F κ ψ (hS ▸ hψ) u)
  rw [hS] at hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    exact summable_gen f J b
  | zero =>
    simp only [Pi.zero_apply, adelicFourierPi, zero_mul, integral_zero, norm_zero]
    exact summable_zero
  | add G H hG hH ihG ihH =>
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) (ihG.add ihH)
    have h := congrFun (adelicFourierPi_add (hI G hG fun i => algebraMap F (AF F) (uv.1 i))
      (hI H hH fun i => algebraMap F (AF F) (uv.1 i))) (fun i => algebraMap F (AF F) (uv.2 i))
    exact (congrArg norm h).le.trans (norm_add_le _ _)
  | smul c G _ ih =>
    refine (ih.mul_left ‖c‖).congr fun uv => ?_
    have h := congrFun (adelicFourierPi_smul c (fun t : κ → AF F =>
      G (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))) (fun i => algebraMap F (AF F) (uv.2 i))
    rw [← _root_.norm_smul]
    exact (congrArg norm h).symm

end GlobalTheory.PartialFourierSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCartanInvolutionInvariantAndPositive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CartanTensor

open Matrix
open scoped Kronecker ComplexOrder

variable {n d : ℕ}

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

theorem cartan_comm {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M * θ.map star = θᵀ * M := by
  obtain ⟨h1, h2, -⟩ := h
  have h1' : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1]
    exact Matrix.map_one star (star_zero _) (star_one _)
  calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [h2]
    _ = θᵀ * M := by rw [Matrix.mul_assoc (θᵀ * M), h1', Matrix.mul_one]

theorem cartan_posDef {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) :
    (θᵀ * M).PosDef := by
  have hH : (θᵀ * M).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, ← cartan_comm h]
    congr 1 <;> ext i j <;> simp [hM]
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun c hc => Complex.pos_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self c).symm⟩⟩
  have hx : star c ≠ 0 := by simpa using hc
  have := h.2.2 (star c) hx
  rw [star_star] at this
  convert this using 2
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem quadruple_sum_eq_trace_transpose_mul (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * A i k * B j l * star (y k l)) = trace (xᵀ * (A * y.map star * Bᵀ)) := by
  rw [← trace_transpose_mul, transpose_transpose]
  simp only [trace, diag_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadruple_sum_eq_kronecker_quadraticForm (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) (x : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * P i k * Q j l * star (x k l)) =
      star (fun p : Fin n × Fin d => star (x p.1 p.2)) ⬝ᵥ ((P ⊗ₖ Q) *ᵥ fun p : Fin n × Fin d => star (x p.1 p.2)) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem map_star_smulI {a b : Type} (M : Matrix a b ℂ) : (Complex.I • M).map star = (-Complex.I) • M.map star := by
  ext i j; simp

theorem cancelI {A B : Matrix (Fin d) (Fin d) ℂ} (h : Complex.I • A = Complex.I • B) : A = B :=
  smul_right_injective _ Complex.I_ne_zero h

theorem tensor_cartan_invariant_pos : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  intro n d JX θX JW θW hJX hX hJW hW x y
  have hWc : θWᵀ * JW * θW.map star = JW := by
    have h := hW.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cW : JW * θW.map star = θWᵀ * JW := by
    have h := cartan_comm hW
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cX := cartan_comm hX
  have hIW : ∀ i j, star ((Complex.I • JW) j i) = (Complex.I • JW) i j := by
    intro i j; simp [hJW]
  constructor
  · rw [quadruple_sum_eq_trace_transpose_mul, quadruple_sum_eq_trace_transpose_mul]
    have e1 : (Complex.I • (θX * x * θWᵀ))ᵀ * (JX * (Complex.I • (θX * y * θWᵀ)).map star * JWᵀ) =
        θW * (xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ) := by
      rw [map_star_smulI, transpose_smul, map_star_mul, map_star_mul, transpose_mul, transpose_mul, transpose_transpose,
        transpose_map]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_mul]
    have e2 : xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ * θW =
        xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θWᵀ * JW * θW.map star)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e1, trace_mul_comm, e2, hX.2.1, hWc]
    simp only [Matrix.mul_assoc]
  · intro hx
    have e3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
        -(xᵀ * ((θXᵀ * JX) * x.map star * (θWᵀ * (Complex.I • JW))ᵀ)) := by
      have h3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
          (-Complex.I) • (xᵀ * (JX * θX.map star) * x.map star * (JW * θW.map star)ᵀ) := by
        rw [map_star_smulI, map_star_mul, map_star_mul, transpose_map, transpose_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [h3, cX, cW]
      simp only [Matrix.smul_mul, Matrix.mul_smul, transpose_smul, neg_smul, Matrix.mul_assoc]
    rw [quadruple_sum_eq_trace_transpose_mul, e3, trace_neg, Complex.neg_re, neg_neg,
      ← quadruple_sum_eq_trace_transpose_mul (θXᵀ * JX) (θWᵀ * (Complex.I • JW)) x x, quadruple_sum_eq_kronecker_quadraticForm]
    have hK := (cartan_posDef hJX hX).kronecker (cartan_posDef hIW hW)
    have hc : (fun p : Fin n × Fin d => star (x p.1 p.2)) ≠ 0 := by
      intro h; apply hx; ext i j; have := congrFun h (i, j); simpa using this
    exact (Complex.pos_iff.1 ((posDef_iff_dotProduct_mulVec.1 hK).2 hc)).1

end GlobalTheory.CartanTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom) (KHT p G.m G.n r G.Fw)) ∧ (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧ (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  first | (exact @GlobalTheory.heckeOperator_integral) | (exact GlobalTheory.heckeOperator_integral) | (intros; apply GlobalTheory.heckeOperator_integral  <;> assumption)
end

