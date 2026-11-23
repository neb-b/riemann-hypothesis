module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPfH

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

namespace DescPf

variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

noncomputable def trT [FiniteDimensional K K₂] : K₂ ⊗[K] V →ₗ[K] V :=
  TensorProduct.lid K V ∘ₗ LinearMap.rTensor V (Algebra.trace K K₂)

lemma trT_tmul [FiniteDimensional K K₂] (x : K₂) (v : V) :
    trT (x ⊗ₜ[K] v) = Algebra.trace K K₂ x • v := by
  simp [trT]

lemma galAct_tmul (σ : K₂ ≃ₐ[K] K₂) (x : K₂) (v : V) :
    galAct σ (x ⊗ₜ[K] v) = σ x ⊗ₜ[K] v := by
  simp [galAct]

lemma sum_galAct [FiniteDimensional K K₂] [IsGalois K K₂] (y : K₂ ⊗[K] V) :
    ∑ σ : K₂ ≃ₐ[K] K₂, galAct σ y = (1 : K₂) ⊗ₜ[K] trT y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    simp only [galAct_tmul, trT_tmul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add y z hy hz =>
    simp only [map_add (f := _), Finset.sum_add_distrib, hy, hz, TensorProduct.tmul_add]

lemma expand [FiniteDimensional K K₂] [Algebra.IsSeparable K K₂] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K K₂) (w : K₂ ⊗[K] V) :
    w = ∑ i, ((Algebra.traceForm K K₂).dualBasis
      (traceForm_nondegenerate (K := K) (L := K₂)) b i) • ((1 : K₂) ⊗ₜ[K] trT (b i • w)) := by
  set d := (Algebra.traceForm K K₂).dualBasis (traceForm_nondegenerate (K := K) (L := K₂)) b
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    have hx : x = ∑ i, Algebra.trace K K₂ (b i * x) • d i := by
      conv_lhs => rw [← d.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm]
    conv_lhs => rw [hx]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, trT_tmul]
    exact TensorProduct.smul_tmul _ _ _
  | add y z hy hz =>
    simp only [smul_add, map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]

end DescPf

theorem galoisDescent_holds : GaloisDescentStatement := by
  intro K K₂ V _ _ _ _ _ _ _ W hW
  classical
  apply le_antisymm
  · intro w hw
    rw [DescPf.expand (Module.finBasis K K₂) w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply]
    rw [← DescPf.sum_galAct]
    exact Submodule.sum_mem _ fun σ _ => hW σ _ (W.smul_mem _ hw)
  · rw [baseSpan, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    simpa only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply] using hu

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobQuotH
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

lemma unzero_toAdd_eq_log (y : WithZero (Multiplicative ℤ)) (hy : y ≠ 0) :
    (WithZero.unzero hy).toAdd = WithZero.log y := by
  induction y using WithZero.recZeroCoe with
  | zero => exact absurd rfl hy
  | coe a => rfl

lemma norm_emb_eq (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordAt v x)) := by
  have hv : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h1 : Valued.v (FinitePlace.embedding v x) = v.valuation K x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [FinitePlace.norm_def, h1, WithZeroMulInt.toNNReal_neg_apply _ hv, ordAt, neg_neg]
  push_cast
  rfl

lemma one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma log_norm_emb (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((ordAt v x : ℝ) * logN v) := by
  rw [norm_emb_eq v hx, Real.log_zpow, logN]
  push_cast
  ring

lemma finite_mulSupport_emb {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖).Finite := by
  have h : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  refine (h.image FinitePlace.maximalIdeal).subset ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [Function.mem_mulSupport, FinitePlace.mk_apply] using hv

lemma support_ordAt_sub {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v) ⊆
      Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖ := by
  intro v hv
  rw [Function.mem_support] at hv
  rw [Function.mem_mulSupport]
  intro h
  apply hv
  have h2 := log_norm_emb v hx
  rw [h, Real.log_one] at h2
  linarith

lemma finite_ordAt {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v).Finite :=
  (finite_mulSupport_emb hx).subset (support_ordAt_sub hx)

lemma finsum_ordAt {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ x) := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  have hprod := NumberField.prod_abs_eq_one hx
  have hA : 0 < ∏ w : InfinitePlace K, w x ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 hx) _
  set s := hfin.toFinset with hs
  have hBs : ∏ᶠ w : FinitePlace K, w x = ∏ w ∈ s, w x :=
    finprod_eq_prod_of_mulSupport_subset _ (by simp [s])
  have hB : 0 < ∏ w ∈ s, w x := Finset.prod_pos fun w _ => FinitePlace.pos_iff.2 hx
  rw [hBs] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA.ne' hB.ne', Real.log_one,
    Real.log_prod (fun w _ => (pow_pos (InfinitePlace.pos_iff.2 hx) _).ne'),
    Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hx).ne')] at hlog
  simp only [Real.log_pow] at hlog
  have hfs : ∑ w ∈ s, Real.log (w x) = ∑ᶠ w : FinitePlace K, Real.log (w x) := by
    rw [finsum_eq_sum_of_support_subset]
    intro w hw
    simp only [Function.mem_support] at hw
    simp only [s, Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    rw [h1, Real.log_one]
  have heq : ∑ᶠ w : FinitePlace K, Real.log (w x) =
      -∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v := by
    rw [← finsum_neg_distrib, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun v => ?_
    have h3 : (FinitePlace.equivHeightOneSpectrum.symm v) x = ‖FinitePlace.embedding v x‖ := by
      rw [← FinitePlace.mk_apply]
      rfl
    rw [h3, log_norm_emb v hx]
  linarith

lemma log_det_le {ρ : ℕ} (m : Matrix (Fin ρ) (Fin ρ) K) (hdet : m.det ≠ 0) (σ : InfinitePlace K)
    (a b : Fin ρ → ℝ) (harch : ∀ i j, m i j ≠ 0 → Real.log (σ (m i j)) + a i ≤ b j) :
    Real.log (σ m.det) ≤ ∑ j, b j - ∑ i, a i + (ρ : ℝ) / 2 * Real.log ρ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · simp [Matrix.det_fin_zero]
  have hpos : 0 < σ m.det := InfinitePlace.pos_iff.2 hdet
  let A : Matrix (Fin ρ) (Fin ρ) ℂ := fun i j => (Real.exp (a i) : ℂ) * σ.embedding (m i j)
  have hAdet : A.det = (∏ i, (Real.exp (a i) : ℂ)) * σ.embedding m.det := by
    have h : A = Matrix.diagonal (fun i => (Real.exp (a i) : ℂ)) * (σ.embedding.mapMatrix m) := by
      ext i j
      simp [A, Matrix.diagonal_mul]
    rw [h, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  have hnormA : ‖A.det‖ = Real.exp (∑ i, a i) * σ m.det := by
    rw [hAdet, norm_mul, norm_prod, InfinitePlace.norm_embedding_eq, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hentry : ∀ i j, ‖A i j‖ ≤ Real.exp (b j) := by
    intro i j
    by_cases h : m i j = 0
    · simp [A, h, (Real.exp_pos _).le]
    · have hp : 0 < σ (m i j) := InfinitePlace.pos_iff.2 h
      have h2 := harch i j h
      simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        InfinitePlace.norm_embedding_eq]
      calc Real.exp (a i) * σ (m i j) = Real.exp (a i + Real.log (σ (m i j))) := by
            rw [Real.exp_add, Real.exp_log hp]
        _ ≤ Real.exp (b j) := Real.exp_le_exp.2 (by linarith)
  have hcol : ∀ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt ρ * Real.exp (b j) := by
    intro j
    rw [← Real.sqrt_sq (Real.exp_pos (b j)).le, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin ρ, Real.exp (b j) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
      _ = ρ * Real.exp (b j) ^ 2 := by simp
  have hH := ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le A.transpose
  rw [Matrix.det_transpose, hnormA] at hH
  simp only [Matrix.transpose_apply] at hH
  have hprod : ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ ∏ j : Fin ρ, (Real.sqrt ρ * Real.exp (b j)) :=
    Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) fun j _ => hcol j
  have key : Real.exp (∑ i, a i) * σ m.det ≤ Real.sqrt ρ ^ ρ * Real.exp (∑ j, b j) := by
    calc _ ≤ _ := hH
      _ ≤ _ := hprod
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.exp_sum]
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by exact_mod_cast hρ)
  have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) key
  rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp,
    Real.log_mul (pow_pos hs _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg _)] at h1
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable def lenLa {K : Type*} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (N : Type*) [AddCommGroup N] [Module (𝓞 K) N] : ℕ∞ :=
  Module.length (Localization.AtPrime la.asIdeal) (LocalizedModule la.asIdeal.primeCompl N)

def LiesOver {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁)) = la.asIdeal

abbrev QuotMW {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (W : Submodule K V) :=
  M ⧸ (W.restrictScalars (𝓞 K)).comap M.subtype

noncomputable def lenW {K K₁ V : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
    [Algebra K K₁] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K₁)) (M : Submodule (𝓞 K) V) (W : Submodule K V) {ρ : ℕ}
    (θ : Fin ρ → M) : ℕ∞ :=
  let Rw := (w.valuationSubringAtPrime K₁).toSubring
  letI : Module Rw (K₁ ⊗[K] V) := Module.compHom _ Rw.subtype
  let Mw := Submodule.span Rw ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V))
  let Nw := (Submodule.span Rw (Submodule.span K₁
      ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓ Mw) ⊔
    Submodule.span Rw (Set.range fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  Module.length Rw (Mw ⧸ Nw.comap Mw.subtype)

def LenDescentStatement : Prop :=
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M) (la : HeightOneSpectrum (𝓞 K))
      (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
      lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
        lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
          (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W)))

def QuotCoreStatement : Prop :=
  LenDescentStatement →
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) (θ : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → M),
      Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤ →
    ∀ (c : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V)),

      (∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
        x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) →
    ∀ (be : HeightOneSpectrum (𝓞 K) → ℝ)
      (s : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → HeightOneSpectrum (𝓞 K₁) → ℝ),
      (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∀ i, (Function.support (s i)).Finite) →

      (∀ (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
        ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
          -((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la) ≤
            (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i w) →
    ∀ (supN : (K →+* ℂ) → V → ℝ) (a : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → InfinitePlace K₁ → ℝ)
      (Bθ Carch Bdeg : ℝ),

      (∀ τ v, supN ((starRingEnd ℂ).comp τ) v = supN τ v) →

      (∀ j, (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Bθ) →

      (∀ (σ : InfinitePlace K₁) i j, c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) ≠ 0 →
        Real.log (σ (c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)))) + a i σ ≤
          Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch) →

      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ Bdeg) →
      ∃ nn : HeightOneSpectrum (𝓞 K) →₀ ℝ,
        (∀ la, ∃ ℓ : ℕ,
          lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
            (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) = ℓ ∧
          (ℓ : ℝ) ≤ nn la + (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * be la) ∧
        (nn.sum fun la v => v * logN la) / (Module.finrank ℚ K : ℝ) ≤
          (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * (Bθ + Carch + Bdeg) +
            (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) / 2 *
              Real.log (Module.finrank (𝓞 K) (QuotMW M W) : ℝ)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open IsDedekindDomain QuotShiftPfH

private theorem ordAt_mul_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((v.valuation F).ne_zero_iff.mpr hx)
    ((v.valuation F).ne_zero_iff.mpr hy)]
  ring

private theorem ordAt_zpow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (x : F) (k : ℤ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

private theorem ordAt_prod_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {ι : Type} (S : Finset ι)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) : ordAt v (∏ i ∈ S, f i) = ∑ i ∈ S, ordAt v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    unfold ordAt
    rw [map_one]
    rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordAt_mul_rationality v (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]

theorem exists_length_quotient_span_le (hL : QuotLocalStatement) {R F : Type} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (Q : Type)
    [AddCommGroup Q] [Module (Rv F v) Q] (ρ : ℕ) (hb : Nonempty (Module.Basis (Fin ρ) (Rv F v) Q))
    (c : Fin ρ → (Q →ₗ[Rv F v] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q)
    (hc : ∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) = n ∧
      (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rv F v)
  set π : F := (ϖ : F) with hπdef
  have hπ0 : π ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπ1 : ordAt v π = 1 := by
    have h1 := (addVal_eq_ord v ϖ hπ0).symm.trans (IsDiscreteValuationRing.addVal_uniformizer hϖ)
    have h2 : (ordAt v π).toNat = 1 := by exact_mod_cast h1
    have h3 := ord_nonneg v ϖ hπ0
    omega

  have hne : ∀ i, ∃ q, c i q ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [h])

  have hex : ∀ i, ∃ μ : ℤ, (∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = μ) ∧
      ∀ q, c i q ≠ 0 → μ ≤ ordAt v (c i q) := by
    intro i
    obtain ⟨lb, ⟨q, hq, rfl⟩, hlb⟩ := Int.exists_least_of_bdd
      (P := fun z => ∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = z)
      ⟨⌈-β - s i⌉, by
        rintro z ⟨q, hq, rfl⟩
        refine Int.ceil_le.mpr ?_
        have := hc i q hq
        linarith⟩
      (by obtain ⟨q, hq⟩ := hne i; exact ⟨_, q, hq, rfl⟩)
    exact ⟨_, ⟨q, hq, rfl⟩, fun q' hq' => hlb _ ⟨q', hq', rfl⟩⟩
  choose μ hμ1 hμ2 using hex
  have hμβ : ∀ i, -(μ i : ℝ) ≤ β + s i := by
    intro i
    obtain ⟨q, hq, hqμ⟩ := hμ1 i
    have := hc i q hq
    rw [hqμ] at this
    linarith

  have hmem : ∀ i q, π ^ (-μ i) * c i q ∈ Rv F v := by
    intro i q
    by_cases hq : c i q = 0
    · rw [hq, mul_zero]; exact (Rv F v).zero_mem
    · refine (mem_Rv_iff_ord v (mul_ne_zero (zpow_ne_zero _ hπ0) hq)).mpr ?_
      rw [ordAt_mul_rationality v (zpow_ne_zero _ hπ0) hq, ordAt_zpow, hπ1]
      have := hμ2 i q hq
      linarith
  let c' : Fin ρ → (Q →ₗ[Rv F v] Rv F v) := fun i =>
    { toFun := fun q => ⟨π ^ (-μ i) * c i q, hmem i q⟩
      map_add' := fun a b => by ext; simp [mul_add]
      map_smul' := fun r q => by
        ext
        simp only [LinearMap.map_smul, RingHom.id_apply, Subring.coe_mul, Subring.smul_def,
          smul_eq_mul]
        ring }
  have hmap : ((Matrix.of fun i j => c' i (th j)).map (Rv F v).subtype) =
      Matrix.diagonal (fun i => π ^ (-μ i)) * Matrix.of fun i j => c i (th j) := by
    ext i j
    simp [Matrix.diagonal_mul, c']
  have hdetF : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (∏ i, π ^ (-μ i)) * (Matrix.of fun i j => c i (th j)).det := by
    have := RingHom.map_det (Rv F v).subtype (Matrix.of fun i j => c' i (th j))
    simp only [RingHom.mapMatrix_apply] at this
    rw [show (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (Rv F v).subtype (Matrix.of fun i j => c' i (th j)).det from rfl, this, hmap,
      Matrix.det_mul, Matrix.det_diagonal]
  have hP0 : (∏ i, π ^ (-μ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ hπ0
  have hdF0 : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) ≠ 0 := by
    rw [hdetF]; exact mul_ne_zero hP0 hdet
  have hdet' : (Matrix.of fun i j => c' i (th j)).det ≠ 0 := fun h => hdF0 (by rw [h]; rfl)
  have hlen := hL (Rv F v) Q ρ hb c' th hdet'
  rw [addVal_eq_ord v _ hdF0] at hlen
  have hord : ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      ∑ i, -μ i + ordAt v (Matrix.of fun i j => c i (th j)).det := by
    rw [hdetF, ordAt_mul_rationality v hP0 hdet, ordAt_prod_rationality v _ _ fun i => zpow_ne_zero _ hπ0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ordAt_zpow, hπ1, mul_one]
  have hnn := ord_nonneg v _ hdF0
  have htop : Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  refine ⟨(Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat,
    (ENat.coe_toNat htop).symm, ?_⟩
  have hle : (Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)).toNat := by
    rw [← ENat.coe_toNat htop] at hlen
    exact_mod_cast hlen
  have hle' : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℝ) ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) : ℝ) := by
    have : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℤ) ≤
        ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) := by omega
    exact_mod_cast this
  rw [hord] at hle'
  push_cast at hle'
  have hsum : ∑ i, (-(μ i : ℝ)) ≤ ∑ i, (β + s i) := Finset.sum_le_sum fun i _ => hμβ i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

