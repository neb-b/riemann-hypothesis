module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTerm
section
open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem summable_seminorm_term : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  intro E _ _ _ _ _ b c hb hc h t ht k n

  set δ : ℝ := min 1 (b / (6 * c)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ b / (6 * c) := min_le_right _ _
  set θ : ℝ := 1 + δ with hθ
  set α : ℝ := (2 * c + b) / (2 * (b + c)) with hα
  have hθ1 : 1 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hθα : c * θ ^ 2 ≤ α * (b + c) := by
    have e1 : α * (b + c) = c + b / 2 := by rw [hα]; field_simp
    have e2 : δ * (6 * c) ≤ b := by rwa [le_div_iff₀ (by positivity)] at hδ2
    rw [e1, hθ]; nlinarith

  choose K hK using fun m => _root_.GlobalTheory.GaussDerivBound.weighted_bound E c α hc hα1 k m
  set M : ℕ → ℝ := fun i => ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => integral_nonneg fun a => by positivity
  set B : ℝ := θ ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M (n - i) * K i with hB
  have hK0 : ∀ m, 0 ≤ K m := fun m => le_trans (by positivity) (hK m 0)
  have hB0 : 0 ≤ B := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (by positivity) (hM0 _)) (hK0 _)
  have hbound : ∀ j, SchwartzMap.seminorm ℂ k n (t j) ≤ θ⁻¹ ^ j * B := by
    intro j
    refine SchwartzMap.seminorm_le_bound ℂ k n (t j) (by positivity) fun y => ?_
    set s : ℝ := (2 * c) ^ j / (j.factorial : ℝ) with hs
    have hs0 : 0 ≤ s := by positivity
    set f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ :=
      ((s : ℝ) : ℂ) • GlobalTheory.ConvSeries.coef b c (⇑h) j with hf
    have hfun : (⇑(t j)) = fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y) := by
      funext y
      rw [ht, GlobalTheory.ConvSeries.term, hf, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_assoc]
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) := by
      refine Complex.contDiff_exp.comp ?_
      refine ContDiff.neg ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => f (fun _ => y)) :=
      f.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
    have hL := norm_iteratedFDeriv_mul_le hG hP y (n := n) (by exact_mod_cast le_top)
    rw [hfun]
    have hfn : ‖f‖ ≤ s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
      rw [hf, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral E b c hb.le hc.le h j) hs0
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) ≤
        θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      set m := n - i
      have h1 := _root_.GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le E j f m y
      have h3 := _root_.GlobalTheory.TermEst.main E b c θ α hc hθ1 hα0 hθα h j m y
      have hPm : ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖ ≤
          θ⁻¹ ^ (j - m) * Real.exp (c * α * ‖y‖ ^ 2) * M m := by
        refine h1.trans (le_trans ?_ h3)
        have := mul_le_mul_of_nonneg_left hfn (by positivity : (0:ℝ) ≤ (j.descFactorial m : ℝ))
        calc (j.descFactorial m : ℝ) * ‖f‖ * ‖y‖ ^ (j - m)
            ≤ (j.descFactorial m : ℝ) * (s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) * ‖y‖ ^ (j - m) := by
              gcongr
          _ = _ := by rw [hs]; ring
      have hθj : θ⁻¹ ^ (j - m) ≤ θ⁻¹ ^ j * θ ^ n := by
        have hinv : 0 < θ⁻¹ := inv_pos.2 hθpos
        have hle : θ⁻¹ ^ (j - m + m) ≤ θ⁻¹ ^ j :=
          pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hθ1) (by omega)
        have e : θ⁻¹ ^ (j - m) = θ⁻¹ ^ (j - m + m) * θ ^ m := by
          rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hθpos.ne', one_pow, mul_one]
        rw [e]
        exact mul_le_mul hle (pow_le_pow_right₀ hθ1 (by omega)) (by positivity) (by positivity)
      have hGk := hK i y
      have hch : (0:ℝ) ≤ n.choose i := by positivity
      calc ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖)
          ≤ ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            (θ⁻¹ ^ j * θ ^ n * Real.exp (c * α * ‖y‖ ^ 2) * M m)) := by
            gcongr
            exact hPm.trans (by gcongr)
        _ = θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
              Real.exp (c * α * ‖y‖ ^ 2)))) := by ring
        _ ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * K i)) := by
            gcongr
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y)) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), ‖y‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) :=
            Finset.sum_le_sum hterm
      _ = θ⁻¹ ^ j * B := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : Summable fun j : ℕ => θ⁻¹ ^ j * B :=
    (summable_geometric_of_lt_one (inv_nonneg.2 hθpos.le) (inv_lt_one_of_one_lt₀ (by linarith))).mul_right B
  exact Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound hgeom

end GlobalTheory.ConvSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfTraceOfSmulMemRange
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem surjective_of_trace_of_smul_mem_range (S A B : Type) [CommRing S] [IsLocalRing S]
    [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A]
    [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B]
    [Algebra.Etale S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ) (s : S) (hs : s ≠ 0)
    (hcok : ∀ b : B, s • b ∈ φ.range)
    (htr : ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) : Function.Surjective φ := by
  classical
  have htf : ∀ b : B, s • b = 0 → b = 0 := by
    intro b hb
    let e := Module.Free.chooseBasis S B
    apply e.repr.injective
    ext i
    have := congrArg (fun x => e.repr x i) hb
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    simpa using (mul_eq_zero.mp this).resolve_left hs
  let L : A →ₗ[S] B := φ.toLinearMap
  have hL : Function.Injective L := hφ
  let E : A ≃ₗ[S] LinearMap.range L := LinearEquiv.ofInjective L hL
  let g : B →ₗ[S] LinearMap.range L :=
    { toFun := fun b => ⟨s • b, by obtain ⟨a, ha⟩ := hcok b; exact ⟨a, ha⟩⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun c x => by ext; simp [smul_comm s c] }
  have hg : Function.Injective g := by
    intro x y hxy
    have : s • x = s • y := congrArg Subtype.val hxy
    have h0 : s • (x - y) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf _ h0)
  have h1 : Module.finrank S A ≤ Module.finrank S B :=
    LinearMap.finrank_le_finrank_of_injective hL
  have h2 : Module.finrank S B ≤ Module.finrank S A :=
    LinearMap.finrank_le_finrank_of_injective (f := E.symm.toLinearMap ∘ₗ g)
      (E.symm.injective.comp hg)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex S A) =
      Fintype.card (Module.Free.ChooseBasisIndex S B) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex]
    omega
  let eι := Fintype.equivOfCardEq hcard
  let a := (Module.Free.chooseBasis S A).reindex eι
  let bB := Module.Free.chooseBasis S B
  let v : Module.Free.ChooseBasisIndex S B → B := fun i => φ (a i)
  have htm : Algebra.traceMatrix S v = Algebra.traceMatrix S a := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul, htr]
  have hdv : Algebra.discr S v = Algebra.discr S a := by
    rw [Algebra.discr_def, Algebra.discr_def, htm]
  let P := bB.toMatrix v
  have hv : Matrix.vecMul (⇑bB) (P.map (algebraMap S B)) = v := by
    funext j
    rw [← bB.sum_toMatrix_smul_self v j]
    simp [Matrix.vecMul, dotProduct, P, Algebra.smul_def, mul_comm]
  have hdisc : Algebra.discr S v = P.det ^ 2 * Algebra.discr S bB := by
    rw [← hv, Algebra.discr_of_matrix_vecMul]
  have hu : IsUnit (P.det ^ 2 * Algebra.discr S bB) := by
    rw [← hdisc, hdv]; exact discr_isUnit S A a
  have hPu : IsUnit P.det := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hu)
  have hbd : IsUnit (bB.det v) := by rw [Module.Basis.det_apply]; exact hPu
  have hspan := ((Module.Basis.is_basis_iff_det bB).mpr hbd).2
  intro y
  have hy : y ∈ Submodule.span S (Set.range v) := by rw [hspan]; trivial
  have hle : Submodule.span S (Set.range v) ≤ LinearMap.range L := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩
  obtain ⟨x, hx⟩ := hle hy
  exact ⟨x, hx⟩

end GlobalTheory.EtaleCoker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymm
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.SympBlocks

open scoped ComplexOrder

theorem herm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (Aᵀ + I • Bᵀ) * (C - I • D) - (Cᵀ + I • Dᵀ) * (A - I • B) = (-(2 * I)) • (1 : Matrix l l ℂ) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
    I_mul_I]
  rw [← h1, ← h2, e3, e4]
  module

theorem symm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (A - I • B)ᵀ * (C - I • D) = (C - I • D)ᵀ * (A - I • B) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← h1, ← h2, e3, e4]
  module

end GlobalTheory.SympBlocks

namespace GlobalTheory.SympBlocks

open scoped ComplexOrder

theorem det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ),
    (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) →
    s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  intro l _ _ s P Q hP hQ hs
  have hs' : fromBlocks s.toBlocks₁₁ s.toBlocks₁₂ s.toBlocks₂₁ s.toBlocks₂₂ ∈
      Matrix.symplecticGroup l ℝ := by rwa [fromBlocks_toBlocks]
  obtain ⟨r1, r2, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hs'
  set A := s.toBlocks₁₁.map Complex.ofRealHom
  set B := s.toBlocks₁₂.map Complex.ofRealHom
  set C := s.toBlocks₂₁.map Complex.ofRealHom
  set D := s.toBlocks₂₂.map Complex.ofRealHom
  have h1 : Aᵀ * C = Cᵀ * A := by
    simp only [A, C, ← transpose_map, ← Matrix.map_mul, r1]
  have h2 : Bᵀ * D = Dᵀ * B := by
    simp only [B, D, ← transpose_map, ← Matrix.map_mul, r2]
  have h3 : Aᵀ * D - Cᵀ * B = 1 := by
    simp only [A, B, C, D, ← transpose_map, ← Matrix.map_mul]
    rw [← Matrix.map_sub _ (fun a b => map_sub Complex.ofRealHom a b), r3]; simp
  have ePQ : P = A - I • B ∧ Q = C - I • D := by
    constructor <;> ext a b <;> simp [A, B, C, D, hP, hQ, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
      toBlocks₂₂]
  obtain ⟨eP, eQ⟩ := ePQ
  have hPc : Pᴴ = Aᵀ + I • Bᵀ := by
    rw [eP]; ext a b; simp [A, B, conjTranspose_apply, transpose_apply]
  have hQc : Qᴴ = Cᵀ + I • Dᵀ := by
    rw [eQ]; ext a b; simp [C, D, conjTranspose_apply, transpose_apply]
  have hH : Pᴴ * Q - Qᴴ * P = (-(2 * I)) • (1 : Matrix l l ℂ) := by
    rw [hPc, hQc, eP, eQ]; exact herm_identity A B C D h1 h2 h3
  have hS : Pᵀ * Q = Qᵀ * P := by
    rw [eP, eQ]; exact symm_identity A B C D h1 h2 h3
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have key : star v ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ v) = 0 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hv,
        star_zero, zero_dotProduct]
    rw [hH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at key
    have h2I : (-(2 * I)) ≠ 0 := by simp [I_ne_zero]
    have : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 key).resolve_left h2I
    exact hv0 (dotProduct_star_self_eq_zero.1 this)
  refine ⟨hdet, ?_⟩
  have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hdet
  have huT : IsUnit Pᵀ.det := by rwa [det_transpose]
  apply Matrix.IsSymm.neg
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_nonsing_inv]
  calc Pᵀ⁻¹ * Qᵀ = Pᵀ⁻¹ * (Qᵀ * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Pᵀ⁻¹ * (Pᵀ * Q) * P⁻¹ := by rw [hS]
    _ = Q * P⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul]

end GlobalTheory.SympBlocks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOver
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_isLocalRing_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  intro P T L _ _ _ _ _ _ _ 𝔐 _ hM huniq hres

  let fκ : P →ₐ[P] L ⧸ maximalIdeal L := Algebra.ofId P _
  have hfκ : ∀ a, fκ a = Ideal.Quotient.mk (maximalIdeal L) (algebraMap P L a) := fun a => rfl
  have hsurj : Function.Surjective fκ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hres y
    exact ⟨a, by rw [hfκ]; exact (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : RingHom.ker fκ = (maximalIdeal L).comap (algebraMap P L) := by
    ext a
    rw [RingHom.mem_ker, hfκ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let e : (P ⧸ RingHom.ker fκ) ≃ₐ[P] L ⧸ maximalIdeal L := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let q : (P ⧸ RingHom.ker fκ) →ₐ[P] T ⧸ 𝔐 :=
    Ideal.quotientMapₐ 𝔐 (Algebra.ofId P T) (le_of_eq (by rw [hker, ← hM]; rfl))
  let g : L →ₐ[P] T ⧸ 𝔐 := (q.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ P (maximalIdeal L))
  have hg : ∀ a : P, ∀ y : L, y - algebraMap P L a ∈ maximalIdeal L →
      g y = Ideal.Quotient.mk 𝔐 (algebraMap P T a) := by
    intro a y hy
    have h1 : Ideal.Quotient.mkₐ P (maximalIdeal L) y = Ideal.Quotient.mkₐ P (maximalIdeal L) (algebraMap P L a) := by
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq.mpr hy
    have h2 : g y = g (algebraMap P L a) := by
      simp only [g, AlgHom.comp_apply]; rw [h1]
    rw [h2, AlgHom.commutes]; rfl
  let ψ : TensorProduct P T L →ₐ[P] T ⧸ 𝔐 :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P 𝔐) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ t y, ψ (t ⊗ₜ[P] y) = Ideal.Quotient.mk 𝔐 t * g y := by
    intro t y; simp [ψ, Algebra.TensorProduct.lift_tmul]
  haveI : Nontrivial (T ⧸ 𝔐) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨t ⊗ₜ[P] 1, by rw [hψ, map_one, mul_one]⟩
  haveI : Nontrivial (TensorProduct P T L) := hψs.nontrivial

  letI : Algebra L (TensorProduct P T L) := Algebra.TensorProduct.rightAlgebra
  have hmap : ∀ x, algebraMap L (TensorProduct P T L) x = (1 : T) ⊗ₜ[P] x := fun _ => rfl
  have hint : Algebra.IsIntegral L (TensorProduct P T L) := by
    constructor
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | add a b ha hb => exact ha.add hb
    | tmul a b =>
      have h1 : a ⊗ₜ[P] b = (a ⊗ₜ[P] (1 : L)) * algebraMap L (TensorProduct P T L) b := by
        rw [hmap]; simp
      rw [h1]
      refine IsIntegral.mul ?_ isIntegral_algebraMap
      have ha : IsIntegral P a := Algebra.IsIntegral.isIntegral a
      have h2 : IsIntegral P (a ⊗ₜ[P] (1 : L)) :=
        ha.map (Algebra.TensorProduct.includeLeft : T →ₐ[P] TensorProduct P T L)
      obtain ⟨p, hp, hp0⟩ := h2
      refine ⟨p.map (algebraMap P L), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) = algebraMap P _ := by
        ext x
        exact (Algebra.TensorProduct.includeRight : L →ₐ[P] TensorProduct P T L).commutes x
      rw [this]; exact hp0
  have hPB : ∀ a : P, (algebraMap P T a) ⊗ₜ[P] (1 : L) = (1 : T) ⊗ₜ[P] (algebraMap P L a) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have key : ∀ 𝔫 : Ideal (TensorProduct P T L), 𝔫.IsMaximal → 𝔫 = RingHom.ker ψ := by
    intro 𝔫 h𝔫
    have hLmax : (𝔫.comap (algebraMap L (TensorProduct P T L))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap L (TensorProduct P T L)) (by
          intro x
          exact hint.isIntegral x) 𝔫
    have hL : 𝔫.comap (algebraMap L (TensorProduct P T L)) = maximalIdeal L :=
      IsLocalRing.eq_maximalIdeal hLmax
    let iT : T →+* TensorProduct P T L := Algebra.TensorProduct.includeLeftRingHom
    have hiT : ∀ t, iT t = t ⊗ₜ[P] (1 : L) := fun _ => rfl
    have hcomp : iT.comp (algebraMap P T) = (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) := by
      ext a; simp only [RingHom.comp_apply, hiT, hmap]; exact hPB a
    have hT : 𝔫.comap iT = 𝔐 := by
      apply huniq
      · exact Ideal.comap_isPrime iT 𝔫
      · rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hL]
    let j : T ⧸ 𝔐 →+* TensorProduct P T L ⧸ 𝔫 := Ideal.quotientMap 𝔫 iT hT.ge
    have hj : Function.Injective j := Ideal.quotientMap_injective' hT.le
    have hφ : ∀ b, Ideal.Quotient.mk 𝔫 b = j (ψ b) := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
      | tmul t y =>
        obtain ⟨a, ha⟩ := hres y
        have hy1 : (1 : T) ⊗ₜ[P] (y - algebraMap P L a) ∈ 𝔫 := by
          rw [← hmap, ← Ideal.mem_comap, hL]; exact ha
        have hsplit : t ⊗ₜ[P] y - (t * algebraMap P T a) ⊗ₜ[P] (1 : L) = (t ⊗ₜ[P] (1 : L)) * ((1 : T) ⊗ₜ[P] (y - algebraMap P L a)) := by
          rw [TensorProduct.tmul_sub, mul_sub, ← hPB]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [hψ, hg a y ha, ← map_mul]
        show _ = Ideal.quotientMap 𝔫 iT hT.ge (Ideal.Quotient.mk 𝔐 (t * algebraMap P T a))
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hiT, hsplit]
        exact 𝔫.mul_mem_left _ hy1
    ext b
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, RingHom.mem_ker, map_eq_zero_iff j hj]
  obtain ⟨𝔫₀, h0⟩ := Ideal.exists_maximal (TensorProduct P T L)
  exact IsLocalRing.of_unique_max_ideal ⟨𝔫₀, h0, fun 𝔫 h => (key 𝔫 h).trans (key 𝔫₀ h0).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEt
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialGenericFibreOfStrictHenselClosedFibStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialGenericFibre_of_strictHenselClosedFibre : GlobalTheory.LocAcyc.KeyLocal → GlobalTheory.LocAcyc.KeyAll := by
  first | (exact @GlobalTheory.LocAcyc.keyAll_of_keyLocal) | (exact GlobalTheory.LocAcyc.keyAll_of_keyLocal) | (intros; apply GlobalTheory.LocAcyc.keyAll_of_keyLocal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
section
noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

def TraceOpen (R : Type) [CommRing R] [TopologicalSpace R] (a b : R) : Prop :=
  ∀ g : ℍ[R, a, b], nrm g = 1 → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g →
    ∃ O : Set R, IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t

def SqOpen (K : Type) [Monoid K] [TopologicalSpace K] : Prop :=
  ∀ V ∈ 𝓝 (1 : K), ∃ U ∈ 𝓝 (1 : K), ∀ r ∈ U, ∃ μ ∈ V, μ ^ 2 = r

end GlobalTheory.QSA
end
end

