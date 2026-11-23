module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq
section
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.PrimeSquareSum

theorem sum_inv_sq_le_one (t : Finset ℕ) (ht : ∀ n ∈ t, 2 ≤ n) :
    ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  have hs := hasSum_zeta_two
  have h1 : (1 : ℕ) ∉ t := fun h => by
    have := ht 1 h
    omega
  have hsum : ∑ n ∈ insert 1 t, ((n : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    rw [← hs.tsum_eq]
    have e : (fun n : ℕ => 1 / (n : ℝ) ^ 2) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
      funext n
      rw [one_div]
    rw [e]
    exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (e ▸ hs.summable)
  rw [Finset.sum_insert h1] at hsum
  norm_num at hsum
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  linarith

theorem sum_absNorm_inv_sq_le (K : Type) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ w ∈ s, (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.exists_colouring_maximal_ideals K
  have hp : ∀ w : HeightOneSpectrum (𝓞 K), ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal ∧
      p ≤ Ideal.absNorm w.asIdeal := by
    intro w
    haveI := w.isMaximal
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
    exact ⟨q, hq, hqP, H ▸ Nat.le_self_pow hn.ne' q⟩
  choose p hp hpm hple using hp
  rw [← Finset.sum_fiberwise s (fun w => c w.asIdeal)]
  calc _ ≤ ∑ _i : Fin (Module.finrank ℚ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hinj : Set.InjOn p (s.filter fun w => c w.asIdeal = i) := by
          intro v hv w hw h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
          exact HeightOneSpectrum.ext (hc (p v) (hp v) _ _ v.isMaximal w.isMaximal (hpm v)
            (h ▸ hpm w) (hv.2.trans hw.2.symm))
        calc _ ≤ ∑ w ∈ s.filter (fun w => c w.asIdeal = i), ((p w : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun w _ => ?_
              have h0 : (0 : ℝ) < p w := by exact_mod_cast (hp w).pos
              have h1 : (p w : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast hple w
              gcongr
          _ = ∑ n ∈ (s.filter (fun w => c w.asIdeal = i)).image p, ((n : ℝ) ^ 2)⁻¹ :=
              (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm
          _ ≤ 1 := by
              refine sum_inv_sq_le_one _ fun n hn => ?_
              obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hn
              exact (hp w).two_le
    _ = _ := by simp

theorem summable_absNorm_inv_sq : ∀ (K : Type) [Field K] [NumberField K], Summable (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) ∧ ∑' w : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  intro K _ _
  have hnn : 0 ≤ fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ :=
    fun w => by positivity
  exact ⟨summable_of_sum_le hnn (sum_absNorm_inv_sq_le K),
    tsum_le_of_sum_le' (by positivity) (sum_absNorm_inv_sq_le K)⟩

end GlobalTheory.PrimeSquareSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegTraceTotallyPositiveFractionalIdea
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.LatExpSum

theorem trace_eq_sum_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ τ : Emb F, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [eq_ratCast] at h
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ τ : Emb F, ((τ x : ℝ) : ℂ) := by
    refine (Fintype.sum_bijective (fun τ : Emb F => (ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)).symm
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  rw [h2, ← ofReal_sum] at h
  exact_mod_cast h

theorem summable_pi_prod {ι : Type} [Fintype ι] {f : ι → ℤ → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ι → ℤ => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image (· i), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          fun n _ _ => Finset.prod_nonneg fun i _ => h0 i _
    _ = ∏ i, ∑ x ∈ s.image (· i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

theorem summable_exp_neg_abs {ε : ℝ} (hε : 0 < ε) : Summable fun n : ℤ => Real.exp (-ε * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-ε) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_nat_of_neg
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (by positivity)]; ring_nf
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf

end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

theorem repr_eq_trace (F : Type) [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F) (y : F) (i : ι) :
    b.repr y i = Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i * y) := by
  rw [← Algebra.traceForm_apply]
  symm
  calc _ = (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = b.repr y i := by simp [LinearMap.BilinForm.apply_dualBasis_left]
end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

theorem summable_exp_neg_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  intro F _ _ _ L δ hδ
  classical
  obtain ⟨a, ha, hint⟩ := L.isFractional
  have hz : ∀ x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x}, ∃ w : 𝓞 F,
      algebraMap (𝓞 F) F w = algebraMap (𝓞 F) F a * x.1 := fun x => by
    obtain ⟨w, hw⟩ := hint x.1 x.2.1
    exact ⟨w, by rw [hw, Algebra.smul_def]⟩
  choose z hz using hz
  let b := integralBasis F
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  have hrepr : ∀ (y : F) i, b.repr y i = Algebra.trace ℚ F (d i * y) := fun y i => repr_eq_trace F b y i
  let c : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ :=
    fun x => (RingOfIntegers.basis F).repr (z x)
  have hc : ∀ x i, ((c x i : ℚ)) = Algebra.trace ℚ F ((d i * algebraMap (𝓞 F) F a) * x.1) := by
    intro x i
    have := integralBasis_repr_apply (K := F) (z x) i
    rw [hz x] at this
    rw [mul_assoc, ← hrepr]
    rw [this, eq_intCast]
  let Mi : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ := fun i => ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)|
  have hMi : ∀ i, 0 ≤ Mi i := fun i => Finset.sum_nonneg fun τ _ => abs_nonneg _
  let M : ℝ := ∑ i, Mi i + 1
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hMi i
    show 0 < ∑ i, Mi i + 1
    linarith
  have hbound : ∀ x, ∑ i, |(c x i : ℝ)| ≤ M * ∑ τ : Emb F, τ x.1 := by
    intro x
    have hT : 0 ≤ ∑ τ : Emb F, τ x.1 := Finset.sum_nonneg fun τ _ => (x.2.2 τ).le
    have h1 : ∀ i, |(c x i : ℝ)| ≤ Mi i * ∑ τ : Emb F, τ x.1 := by
      intro i
      have e : (c x i : ℝ) = ∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1 := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (hc x i)
        simp only [Rat.cast_intCast] at h
        rw [h, trace_eq_sum_emb]
        simp only [map_mul]
      rw [e]
      calc |∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1|
          ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a) * τ x.1| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * τ x.1 := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [abs_mul, abs_of_pos (x.2.2 τ)]
        _ ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * ∑ σ : Emb F, σ x.1 :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun σ : Emb F => σ x.1) (fun σ _ => (x.2.2 σ).le) (Finset.mem_univ τ)) (abs_nonneg _)
        _ = Mi i * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
    calc ∑ i, |(c x i : ℝ)| ≤ ∑ i, Mi i * ∑ τ : Emb F, τ x.1 := Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ i, Mi i) * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
      _ ≤ M * ∑ τ : Emb F, τ x.1 := mul_le_mul_of_nonneg_right (by simp [M]) hT
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero ha)
  have hinj : Function.Injective c := by
    intro x y hxy
    have h1 : z x = z y := (RingOfIntegers.basis F).repr.injective (Finsupp.ext fun i => congrFun hxy i)
    have h2 : algebraMap (𝓞 F) F a * x.1 = algebraMap (𝓞 F) F a * y.1 := by rw [← hz, ← hz, h1]
    exact Subtype.ext (mul_left_cancel₀ ha0 h2)
  have hε : 0 < δ / M := div_pos hδ hM
  have hg : Summable fun n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ => ∏ i, Real.exp (-(δ / M) * |(n i : ℝ)|) :=
    summable_pi_prod (f := fun _ x => Real.exp (-(δ / M) * |(x : ℝ)|)) (fun _ _ => (Real.exp_pos _).le) fun _ => summable_exp_neg_abs hε
  refine (hg.comp_injective hinj).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun x => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
  have h3 : δ / M * ∑ i, |(c x i : ℝ)| ≤ δ * ∑ τ : Emb F, τ x.1 := by
    calc δ / M * ∑ i, |(c x i : ℝ)| ≤ δ / M * (M * ∑ τ : Emb F, τ x.1) := mul_le_mul_of_nonneg_left (hbound x) hε.le
      _ = δ * ∑ τ : Emb F, τ x.1 := by field_simp
  linarith

end GlobalTheory.LatExpSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEqStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_centralizer_injective_commutant_eq : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  first | (exact @GlobalTheory.tensor_centralizer_flat) | (exact GlobalTheory.tensor_centralizer_flat) | (intros; apply GlobalTheory.tensor_centralizer_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirst
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  intro R A _ _ _ k F
  classical
  set S := firstAndFinite R A k F with hS
  let g : Fin (k + 1) × F → S := fun p =>
    ⟨PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) p.1 p.2.1,
      Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨p.1, p.2.1, p.2.2, rfl⟩))⟩
  refine ⟨Finset.univ.image g, ?_⟩
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  conv_rhs => rw [hS, firstAndFinite]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  · ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨⟨i, a, ha⟩, rfl⟩, rfl⟩
      exact ⟨i, a, ha, rfl⟩
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨g (i, ⟨a, ha⟩), ⟨(i, ⟨a, ha⟩), rfl⟩, rfl⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegral
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_isIntegral (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A) :
    Algebra.IsIntegral R (firstAndFinite R A k F) := by
  unfold firstAndFinite
  apply Algebra.IsIntegral.adjoin
  rintro x (⟨a, rfl⟩ | hx)
  · exact (Algebra.IsIntegral.isIntegral a).map _
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, -, rfl⟩ := hi
    exact (Algebra.IsIntegral.isIntegral a).map _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRatAlgebraDecompFactorwiseStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_rat_algebra_decomp_factorwise : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B],
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, CharZero (L i))
      (_ : ∀ i, Algebra F (L i)) (Φ : S ⊗[ℚ] B ≃+* ((i : ι) → L i ⊗[F] B)) (ψ : S ⊗[ℚ] F ≃+* ((i : ι) → L i)),
      (∀ b : B, Φ ((1 : S) ⊗ₜ[ℚ] b) = fun i => (1 : L i) ⊗ₜ[F] b) ∧
      (∀ z : S ⊗[ℚ] F, Φ (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) z) =
        fun i => algebraMap (L i) (L i ⊗[F] B) (ψ z i)) := by
  first | (exact @GlobalTheory.tensor_decomp_factorwise) | (exact GlobalTheory.tensor_decomp_factorwise) | (intros; apply GlobalTheory.tensor_decomp_factorwise  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
section
open scoped TensorProduct
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

abbrev GenFib (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Type :=
  Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))

def TorsorsTrivial (B : Type) [CommRing B] (q : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
    Module.FaithfullyFlat B D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[B] B)

def AbsIntClosed (T : Type) [CommRing T] : Prop :=
  ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0

def KeyAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocalWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocal : Prop := KeyLocalWith (fun _ _ _ _ => True)

def KeyGeneric : Prop :=
  KeyLocalWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyClosedPts : Prop :=
  KeyLocalWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyOrigin : Prop :=
  KeyLocalWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

end GlobalTheory.LocAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMonicOverMvPolynomialStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure : ∀ {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] {ι : Type} (z : ι → K), (∀ i, z i ∈ F) → ∀ (v : K), IsIntegral (Subring.closure (Set.range z)) v → ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧ f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  first | exact @GlobalTheory.trace_monic_over_mvPolynomial | exact GlobalTheory.trace_monic_over_mvPolynomial | (intros; apply GlobalTheory.trace_monic_over_mvPolynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionLatticeEq
section
open NumberField Polynomial IntermediateField

namespace GlobalTheory.LatticeTrace

theorem trace_lattice_eq : ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] [Algebra (𝓞 F) O] (La : Type) [AddCommGroup La] [Module O La] [Module.Free ℤ La] [Module.Finite ℤ La] (k : ℕ), Module.finrank ℤ La = k * Module.finrank ℚ F → ∀ c : 𝓞 F, ((LinearMap.trace ℤ La (DistribSMul.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap : ℤ) : ℂ) = (k : ℂ) * ∑ τ : F →+* ℂ, τ (c : F) := by
  intro F _ _ O _ _ La _ _ _ _ k hk c
  classical
  set n := Module.finrank ℤ La with hn

  let φ : 𝓞 F →+* Module.End ℤ La :=
    ((addMonoidEndRingEquivInt La).toRingHom.comp (Module.toAddMonoidEnd O La)).comp (algebraMap (𝓞 F) O)
  have hφ : φ c = (DistribSMul.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap := rfl
  let b := Module.finBasis ℤ La
  set M := LinearMap.toMatrix b b (φ c) with hM
  set M' := M.map (algebraMap ℤ ℚ) with hM'
  have hx : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
  set f := minpoly ℚ (c : F) with hf
  have hfmon : f.Monic := minpoly.monic hx
  have hfirr : Irreducible f := minpoly.irreducible hx
  have hfZ : f = (minpoly ℤ c).map (algebraMap ℤ ℚ) := by
    rw [hf, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe c),
      RingOfIntegers.minpoly_coe]
  have hT : aeval (φ c) (minpoly ℤ c) = 0 := by
    rw [show φ c = (RingHom.toIntAlgHom φ) c from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hMz : aeval M (minpoly ℤ c) = 0 := by
    have hMe : M = LinearMap.toMatrixAlgEquiv b (φ c) := rfl
    rw [hMe, aeval_algHom_apply, hT, map_zero]
  have hM'f : aeval M' f = 0 := by
    rw [hfZ, aeval_map_algebraMap, hM', show M.map (algebraMap ℤ ℚ) = (Algebra.ofId ℤ ℚ).mapMatrix M from rfl,
      aeval_algHom_apply, hMz, map_zero]

  set r := Module.finrank ℚ⟮(c : F)⟯ F with hr
  have hdeg : Module.finrank ℚ F = f.natDegree * r := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮(c : F)⟯ F, IntermediateField.adjoin.finrank hx]
  have hsize : n = f.natDegree * (k * r) := by
    rw [hk, hdeg]; ring
  have hcp : M'.charpoly = f ^ (k * r) :=
    GlobalTheory.charpoly_eq_pow_of_aeval_irreducible_eq_zero ℚ n (k * r) M' f hfmon hfirr hM'f hsize

  have htr : (M'.trace : ℚ) = (k * r : ℚ) * -(f.nextCoeff) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hk0 : k * r = 0 := by
        have := hsize; rw [h0] at this
        rcases Nat.mul_eq_zero.1 this.symm with h | h
        · exact absurd h (Irreducible.natDegree_pos hfirr).ne'
        · exact h
      have : M'.trace = 0 := by
        haveI : IsEmpty (Fin (Module.finrank ℤ La)) := by rw [← hn, h0]; infer_instance
        simp [Matrix.trace]
      rw [this]
      have : (k * r : ℚ) = 0 := by exact_mod_cast hk0
      rw [this, zero_mul]
    · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, hcp, Fintype.card_fin]
      have hnd : (f ^ (k * r)).natDegree = n := by rw [hfmon.natDegree_pow, hsize]; ring
      have hne : (f ^ (k * r)).nextCoeff = (f ^ (k * r)).coeff (n - 1) := by
        rw [nextCoeff, hnd, if_neg hpos.ne']
      rw [← hne, hfmon.nextCoeff_pow, nsmul_eq_mul]
      push_cast; ring

  have hTr : (∑ τ : F →+* ℂ, τ (c : F)) = algebraMap ℚ ℂ (Algebra.trace ℚ F c) := by
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hTr2 : Algebra.trace ℚ F c = (r : ℚ) * -(f.nextCoeff) := trace_eq_finrank_mul_minpoly_nextCoeff ℚ _
  have hL : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ) = M'.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℤ b, hM', ← hM]
    exact AddMonoidHom.map_trace (algebraMap ℤ ℚ) M
  rw [← hφ, hTr, hTr2]
  have : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℂ) = algebraMap ℚ ℂ (((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ)) := by simp
  rw [this, hL, htr]
  simp only [map_mul, map_neg, map_natCast]
  ring

end GlobalTheory.LatticeTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourierStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_poincareSeries_lattice_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ, (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ → ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) → (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) → ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) → l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) → (∀ v, ∑' x, Q x * F (j x + v) = ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) → ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  first | exact @GlobalTheory.PoincareUnfold.unfold_poincare_fourier | exact GlobalTheory.PoincareUnfold.unfold_poincare_fourier | (intros; apply GlobalTheory.PoincareUnfold.unfold_poincare_fourier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralClStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_eq_pow_ramificationIdx_mul_unit_integralClosure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (P : Ideal (integralClosure S L)) [P.IsMaximal], Irreducible π → algebraMap S (integralClosure S L) π ∈ P → ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ, algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  first | (exact @GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit) | (exact GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit) | (intros; apply GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit  <;> assumption)
end

