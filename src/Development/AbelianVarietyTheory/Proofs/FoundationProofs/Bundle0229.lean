module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0216
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Matrix

noncomputable section

namespace GlobalTheory.RatEqui

variable (D : D7) {N N' : ℕ}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) :=
  Formalism.HC.HostAx.conjE_apply D.host.toHostAx _ _

def adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  (M.map D.host.conj).transpose

theorem adj_map {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (adj D M).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp [adj, embT_conj]

def mulV (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) :
    VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ => (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ)
  map_add' z w := by
    funext τ
    change M'.map (embT D τ) * (Matrix.of (z τ) + Matrix.of (w τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    funext τ
    change M'.map (embT D τ) * (c • Matrix.of (z τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem mulV_apply (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') (τ : D.what₂.Tau) :
    mulV D M' M z τ = (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ) := rfl

theorem mulV_mulV (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M₁' M₁ (mulV D M₂' M₂ z) = mulV D (M₁' * M₂') (M₂ * M₁) z := by
  funext τ
  change M₁'.map (embT D τ) * (M₂'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)) * M₁.map (embT D τ) =
    (M₁' * M₂').map (embT D τ) * Matrix.of (z τ) * (M₂ * M₁).map (embT D τ)
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem mulV_one (z : VC D N N') : mulV D 1 1 z = z := by
  funext τ
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem mulV_sub_left (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D (M₁' - M₂') M z = mulV D M₁' M z - mulV D M₂' M z := by
  funext τ
  change (M₁' - M₂').map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) =
    M₁'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) - M₂'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, Matrix.sub_mul]

theorem mulV_sub_right (M' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M' (M₁ - M₂) z = mulV D M' M₁ z - mulV D M' M₂ z := by
  funext τ
  change M'.map (embT D τ) * Matrix.of (z τ) * (M₁ - M₂).map (embT D τ) =
    M'.map (embT D τ) * Matrix.of (z τ) * M₁.map (embT D τ) - M'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.mul_sub]

theorem Hf_eq_trace (T : Tor D) (z w : VC D N N') :
    Hf D T z w = (∑ τ, Matrix.trace (Matrix.of (z τ) * (Matrix.of (w τ))ᴴ)) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

theorem Hf_mulV (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T (mulV D M' M z) w = Hf D T z (mulV D (adj D M') (adj D M) w) := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change Matrix.trace (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) * (Matrix.of (w τ))ᴴ) =
    Matrix.trace (Matrix.of (z τ) * ((adj D M').map (embT D τ) * Matrix.of (w τ) * (adj D M).map (embT D τ))ᴴ)
  rw [adj_map, adj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pull_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' G = fun z => G (mulV D (adj D γ') γ z) := by
  funext z
  unfold pull
  congr 1
  funext τ
  rw [mulV_apply, adj_map]
  rfl

theorem mulV_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mulV D M' M (pt D (tor0 D cc δ) δ z) = pt D (tor0 D cc δ) δ (M' * z * M) := by
  unfold pt
  rw [map_smul]
  congr 1
  funext τ
  change M'.map (embT D τ) * z.map (embT D τ) * M.map (embT D τ) = (M' * z * M).map (embT D τ)
  simp only [Matrix.map_mul]

theorem adj_mul {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) D.host.E) : adj D (M₁ * M₂) = adj D M₂ * adj D M₁ := by
  unfold adj
  rw [← Matrix.transpose_mul]
  congr 1
  exact Matrix.map_mul (f := (D.host.conj : D.host.E →+* D.host.E))

theorem adj_one {n : ℕ} : adj D (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end GlobalTheory.RatEqui
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegRankMulLogLeLogCovolumeHermitian
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LcvSub

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_eq {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m k ℂ) (B : Matrix n k ℂ) (h : Aᴴ * A = Bᴴ * B) (u : k → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ u) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  apply Complex.ofReal_injective
  rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fcoord_std {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  congr 1

theorem gram_eq {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))ᴴ *
      ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding)) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, fcoord_std, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply]

theorem gram_single {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) :
    gram X v (fun i => (Pi.single i 1 : Fin d → K)) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  have h : (Matrix.of (fun i => (Pi.single i 1 : Fin d → K)))ᵀ.map v.embedding = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Function.swap, Pi.single_apply]
    · simp [hab, Matrix.one_apply]
  rw [gram_eq, h, Matrix.mul_one]

end GlobalTheory.LcvSub


open GlobalTheory.LcvSub in
theorem GlobalTheory.neg_rank_mul_log_le_lcv : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ v₀ hv₀ d H X hH s hs L hL hint
  classical
  set j := Formalism.HN.rkK L with hj
  let W : Submodule K (Fin d → K) := Submodule.span K (L : Set (Fin d → K))
  let b : Module.Basis (Fin j) K W := Module.finBasis K W
  let e : Fin j → Fin d → K := fun a => (b a : Fin d → K)
  have he : LinearIndependent K e := b.linearIndependent.map' W.subtype W.ker_subtype
  let ψ : (Fin j → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Injective ψ := W.injective_subtype.comp b.equivFun.symm.injective
  have hψE : ∀ x, ψ x = (Matrix.of e)ᵀ *ᵥ x := by
    intro x
    ext i
    simp [ψ, e, Matrix.mulVec, dotProduct, mul_comm]
  have hrange : LinearMap.range ψ = W := by
    simp [ψ, LinearMap.range_comp]
  obtain ⟨hne, hpos⟩ := GlobalTheory.TestLat.gramR_ne_zero_and_gram_posDef K v₀ hv₀ d j H X hH.2 e he
  choose X' hX' hX'g using fun v => GlobalTheory.posDef_exists_frame j _ (hpos v)
  let L' : Submodule (𝓞 K) (Fin j → K) := L.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L'.map (ψ.restrictScalars (𝓞 K)) = L := by
    apply Submodule.map_comap_eq_self
    intro x hx
    have : x ∈ LinearMap.range ψ := by
      rw [hrange]; exact Submodule.subset_span hx
    exact this
  have hfg : L'.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hψ (by rw [hmap]; exact hL)
  have hlat : Submodule.IsFullLattice K L' := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }
    apply LinearMap.map_injective (LinearMap.ker_eq_bot.mpr hψ)
    have himage : ψ '' (L' : Set (Fin j → K)) = (L : Set (Fin d → K)) :=
      congrArg (fun M : Submodule (𝓞 K) (Fin d → K) => (M : Set (Fin d → K))) hmap
    rw [← Submodule.span_image, himage, Submodule.map_top, hrange]
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin j)) X' v x := by
    intro v x
    unfold Formalism.HermitianLatticesTheory.normAt
    rw [fcoord_std, fcoord_std,
      cnorm_mulVec_eq (X' v)⁻¹ ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))
        (by rw [hX'g, gram_eq]), ← Matrix.mulVec_mulVec]
    congr 2
    ext i
    rw [hψE]
    simp [Matrix.mulVec, dotProduct]
  have hht := (Formalism.HN.rerealize K (Fin j → K) (Fin j) (Fin d → K) (Fin d) (Pi.basisFun K (Fin j)) X'
    (Pi.basisFun K (Fin d)) X ψ hX' (fun v => (hH.2 v).1) hψ hnorm L' hfg).1
  rw [hmap] at hht
  have hlcv : lcv X L = lcv X' L' := by
    unfold lcv; rw [hht]
  rw [hlcv]
  refine GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j X' hX' (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) s hs hne ?_ L' (by first | exact hlat | exact hlat.toIsLattice) ?_
  · have h := GlobalTheory.GramMean.prod_norm_gramR_le K d j H X hH e
    simp only [gram_single, hX'g]
    exact h
  · intro x hx y hy
    have h := hint (ψ x) hx (ψ y) hy
    have hG : (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) =
        ((Matrix.of e)ᵀ)ᴴ * (H * (Matrix.of e)ᵀ) := by
      ext a c
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hψE, hψE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] at h
    rw [hG]
    exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormJetExpNegMulLe
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ExpJets

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expPS_eq_subst (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    expPS F = (PowerSeries.exp ℂ_[p]).subst F := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' hF), expPS, coeff_mk,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp, div_eq_inv_mul]
  · intro k hk
    by_contra h
    apply hk
    have hlt : n < k := by simpa using h
    have h0 : coeff n (F ^ k) = 0 := by
      have : (X : PowerSeries ℂ_[p]) ^ k ∣ F ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.2 hF) k
      exact X_pow_dvd_iff.1 this n hlt
    simp [h0]

theorem derivative_expPS (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    d⁄dX (expPS F) = expPS F * d⁄dX F := by
  rw [expPS_eq_subst F hF, PowerSeries.derivative_subst (HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp]

theorem norm_jet_mul_le (A B : PowerSeries ℂ_[p]) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, i + j = n →
      ‖(i.factorial : ℂ_[p]) * coeff i A‖ * ‖(j.factorial : ℂ_[p]) * coeff j B‖ ≤ C) :
    ‖(n.factorial : ℂ_[p]) * coeff n (A * B)‖ ≤ C := by
  rw [coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun x hx => ?_
  obtain ⟨i, j⟩ := x
  have hij : i + j = n := by simpa using hx
  have e : (n.factorial : ℂ_[p]) * (coeff i A * coeff j B) =
      (((i + j).choose j : ℕ) : ℂ_[p]) *
        (((i.factorial : ℂ_[p]) * coeff i A) * ((j.factorial : ℂ_[p]) * coeff j B)) := by
    rw [← hij, ← Nat.add_choose_mul_factorial_mul_factorial i j]
    push_cast
    ring
  simp only
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(((i + j).choose j : ℕ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  calc _ ≤ 1 * C := mul_le_mul h1 (h i j hij) (by positivity) zero_le_one
    _ = C := one_mul C

theorem jet_derivative (A : PowerSeries ℂ_[p]) (n : ℕ) :
    (n.factorial : ℂ_[p]) * coeff n (d⁄dX A) =
      ((n + 1).factorial : ℂ_[p]) * coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem norm_jet_expPS_le (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) (s : ℝ)
    (hs : 0 ≤ s) (h : ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * coeff n F‖ ≤ s ^ n) (n : ℕ) :
    ‖(n.factorial : ℂ_[p]) * coeff n (expPS F)‖ ≤ s ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expPS]
    | succ n =>
      rw [← jet_derivative, derivative_expPS F hF]
      refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
      rw [jet_derivative, ← hij, add_assoc, pow_add]
      exact mul_le_mul (ih i (by omega)) (h (j + 1)) (norm_nonneg _) (by positivity)

theorem norm_jet_exp_neg_mul_le : ∀ (p : ℕ) [Fact p.Prime] (ph : PowerSeries ℂ_[p]) (s : ℝ), 1 ≤ s → PowerSeries.constantCoeff ph = 0 → (∀ i, i ≠ 2 → ‖(i.factorial : ℂ_[p]) * PowerSeries.coeff i ph‖ ≤ 1) → ‖(2 : ℂ_[p]) * PowerSeries.coeff 2 ph‖ ≤ s ^ 2 → ∀ (f : PowerSeries ℂ_[p]), (∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (expPS (-ph) * f)‖ ≤ s ^ n := by
  intro p _ ph s hs h0 h1 h2 f hf n
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hE := norm_jet_expPS_le (-ph) (by simp [h0]) s hs0 fun m => by
    rw [map_neg, mul_neg, norm_neg]
    by_cases hm : m = 2
    · subst hm
      simpa using h2
    · exact (h1 m hm).trans (one_le_pow₀ hs)
  refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
  rw [← hij, pow_add]
  exact mul_le_mul (hE i) ((hf j).trans (one_le_pow₀ hs)) (norm_nonneg _) (by positivity)

end GlobalTheory.ExpJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalProductThetaMemThetaSpace
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OrthoProdTheta

variable {D : D7}

theorem coordB_add (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_sum (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (i : Fin r) (c : Fin r → ℂ) :
    coordB D T b i (∑ k, c k • embV D T (b k)) = c i := by
  let L : VC D N N' →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b i
      map_add' := coordB_add T b i
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  have hL : ∀ z, coordB D T b i z = L z := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, map_sum]
  have h2 : ∀ k, L (c k • embV D T (b k)) = if i = k then c k else 0 := by
    intro k
    rw [map_smul, ← hL, hb]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun k _ => h2 k]
  simp

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    (-1 : ℂ) ^ (∑ k ∈ s, m k) = ∏ k ∈ s, (-1 : ℂ) ^ m k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem exists_coord (T : Tor D) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} {x : VC D a d} (hx : x ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ x = ∑ j, w j • embV D T (b j) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, j, rfl⟩ := hx
    refine ⟨Pi.single j w, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hw
      · simp [h]
    · rw [Finset.sum_eq_single j] <;> simp +contextual
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', fun j => add_mem (hw j) (hw' j), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨-w, fun j => neg_mem (hw j), by simp⟩

theorem hf_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (c : Fin r → ℂ)
    (z : VC D a d) :
    Hf D T z (∑ k, c k • embV D T (b k)) = (∑ k, coordB D T b k z * (starRingEnd ℂ) (c k)) / (area T.abelian₂ : ℂ) := by
  unfold Hf coordB
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, embV]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pullB_mem_ThSp : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  intro D T N N' r b hb g hg hq
  refine ⟨?_, ?_⟩
  · unfold pullB coordB
    fun_prop
  · intro x hx z
    obtain ⟨w, hw, rfl⟩ := exists_coord T hx
    choose m hm hU using fun k => hq _ (hw k)
    have hre : Real.sqrt D.host.d / 2 *
        (Hf D T (∑ k, w k • embV D T (b k)) (∑ k, w k • embV D T (b k))).re = ((∑ k, m k : ℤ) : ℝ) := by
      rw [hf_sum, Complex.div_ofReal_re, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coordB_sum T b hb, ← hm k, q1, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hal : al D T (∑ k, w k • embV D T (b k)) = ∏ k, (-1 : ℂ) ^ m k := by
      unfold al
      rw [hre, round_intCast, neg_one_zpow_sum]
    have hUU : U D T (∑ k, w k • embV D T (b k)) (pullB D T b g) z = ∏ k, U1 T.abelian₂ (w k) g (coordB D T b k z) := by
      unfold U U1 pullB
      rw [hf_sum, hf_sum, Finset.prod_mul_distrib, ← Complex.exp_sum]
      simp only [coordB_add, coordB_sum T b hb]
      congr 2
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hal, hUU, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hU k _

end GlobalTheory.OrthoProdTheta
end

