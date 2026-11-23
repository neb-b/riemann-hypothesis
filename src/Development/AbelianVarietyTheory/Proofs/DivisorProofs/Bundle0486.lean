module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreDerivativePolynomialValueAdd
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_add : ∀ (k n : ℕ) (c s y : ℂ), lag k n (c + s) y =
    ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y := by
  intro k n c s y
  have hR : ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y
      = ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.Ico j (n + 1),
        (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j) := by
    simp only [lag, Finset.mul_sum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1) (fun j m ↦
      (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j))).symm
  rw [hR, lag]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.sum_Ico_eq_sum_range, add_pow, show n + 1 - j = n - j + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have h := _root_.GlobalTheory.HilbFam.rco_mul_rco k n (j + p) j (by omega) (by omega)
  have e1 : j + p - j = p := by omega
  have e2 : n - (j + p) = n - j - p := by omega
  rw [e1] at h
  have h' : (rco k n (j + p) : ℂ) * (rco k (j + p) j : ℂ)
      = (rco k n j : ℂ) * ((n - j).choose p : ℂ) := by exact_mod_cast h
  rw [e1, e2]
  linear_combination (-(s ^ (n - j - p) * c ^ p * y ^ j)) * h'

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStrips
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.LaplaceStrip

theorem norm_integrand {α : Type} (ℓ : α → ℝ) (g : α → ℂ) (s : ℂ) (x : α) :
    ‖g x * Complex.exp (s * (ℓ x : ℂ))‖ = ‖g x‖ * Real.exp (s.re * ℓ x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr

end GlobalTheory.LaplaceStrip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem ratM_mulVec_tmul (γ : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ratM F γ *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (γ *ᵥ x) i := by
  ext i
  simp only [mulVec, dotProduct, ratM, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem ratM_mulVec_fv (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratM F γ *ᵥ fv F x = fv F (γ *ᵥ x) :=
  ratM_mulVec_tmul γ 1 x

theorem ratM_mul (γ δ : Matrix (Fin n) (Fin n) E) : ratM F (γ * δ) = ratM F γ * ratM F δ := by
  have h : ∀ ε : Matrix (Fin n) (Fin n) E,
      ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε := by
    intro ε; ext i j; simp [ratM]
  rw [h, h, h, map_mul]

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  ext i; simp [fv, TensorProduct.tmul_sub]

theorem fv_nsmul (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  ext i
  simp only [fv, Pi.smul_apply]
  exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem nsmul_cancel {V : Type} [AddCommGroup V] [Module F V] {M : ℕ} (hM : 1 ≤ M) {u w : V}
    (h : M • u = M • w) : u = w := by
  have h0 : (M : F) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  simpa [h0] using congrArg (fun z => (M : F)⁻¹ • z) h

theorem stab_cong_iff_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E) (hM : 1 ≤ M)
    (hrat : ∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) :
    ((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧
        ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔
      ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧
        ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x) := by
  set B : Matrix (Fin n) (Fin n) E := (β : Matrix (Fin n) (Fin n) E) with hB
  set C : Matrix (Fin n) (Fin n) E := ((β⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hC
  have hBC : B * C = 1 := Units.mul_inv β
  have hCB : C * B = 1 := Units.inv_mul β
  have hRBC : ∀ z, ratM F B *ᵥ (ratM F C *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hBC, ratM_one, one_mulVec]
  have hRCB : ∀ z, ratM F C *ᵥ (ratM F B *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hCB, ratM_one, one_mulVec]
  have gen : ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      (fun i => a ⊗ₜ[F] x i) ∈ hat F (Λ : Set (Fin n → E)) :=
    fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩
  constructor
  · rintro ⟨hstab, hcong⟩
    refine ⟨fun z hz => ?_, fun z hz => ⟨ratM F C *ᵥ z, ?_, hRBC z⟩⟩
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨y, hy, hxy⟩ := hcong x hx
        refine ⟨fun i => a ⊗ₜ[F] y i, gen a ha y hy, ?_⟩
        rw [ratM_mulVec_tmul]
        ext i
        have := congrFun hxy i
        simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
        rw [← TensorProduct.tmul_sub, this]
        exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) M (y i)
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add z w _ _ h1 h2 =>
        obtain ⟨y1, hy1, e1⟩ := h1
        obtain ⟨y2, hy2, e2⟩ := h2
        refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
        rw [mulVec_add, smul_add, ← e1, ← e2]; abel
      | neg z _ h =>
        obtain ⟨y, hy, e⟩ := h
        refine ⟨-y, neg_mem hy, ?_⟩
        rw [mulVec_neg, smul_neg, ← e]; abel
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        rw [ratM_mulVec_tmul]
        refine gen a ha _ ((hstab _).2 ?_)
        rw [mulVec_mulVec, hBC, one_mulVec]; exact hx
      | zero => simp
      | add z w _ _ h1 h2 => rw [mulVec_add]; exact add_mem h1 h2
      | neg z _ h => rw [mulVec_neg]; exact neg_mem h
  · rintro ⟨hcong, hsurj⟩
    have himg : ∀ x ∈ Λ, B *ᵥ x ∈ Λ := by
      intro x hx
      obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      rw [← hrat, ← ratM_mulVec_fv, sub_eq_iff_eq_add.mp e]
      exact add_mem (nsmul_mem hy M) ((hrat x).2 hx)
    refine ⟨fun x => ⟨himg x, fun hx => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := hsurj _ ((hrat _).2 hx)
      rw [← ratM_mulVec_fv] at e
      have hyx : y = fv F x := by
        have := congrArg (fun z => ratM F C *ᵥ z) e
        simpa only [hRCB] using this
      rw [← hrat, ← hyx]; exact hy
    · obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      set w : Fin n → E := (M : E)⁻¹ • (B *ᵥ x - x) with hw
      have hMw : M • w = B *ᵥ x - x := by
        rw [hw, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hM0]
      have hfw : fv F w = y := by
        apply nsmul_cancel (F := F) hM
        rw [← fv_nsmul, hMw, fv_sub, ← ratM_mulVec_fv, e]
      exact ⟨w, (hrat w).1 (hfw ▸ hy), hMw.symm⟩

end GlobalTheory.LocGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasure
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
namespace GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)

def entEquiv : Ent X ≃ Ent X' := Equiv.prodCongr e (Equiv.refl _)

def idxEquiv : Fin (nd X) ≃ Fin (nd X') :=
  (Fintype.equivFin (Ent X)).symm.trans ((entEquiv X X' e).trans (Fintype.equivFin (Ent X')))

def coordIso : V (nd X) ≃ₗᵢ[ℂ] V (nd X') := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idxEquiv X X' e)

theorem coordIso_apply (z : V (nd X)) (k : Fin (nd X')) :
    coordIso X X' e z k = z ((idxEquiv X X' e).symm k) := rfl

theorem idxEquiv_symm_equivFin (τ' : X'.Ψ) (p : {p : Fin r × Fin r // p.2 < p.1}) :
    (idxEquiv X X' e).symm (Fintype.equivFin (Ent X') (τ', p)) = Fintype.equivFin (Ent X) (e.symm τ', p) := by
  show Fintype.equivFin (Ent X) ((entEquiv X X' e).symm
    ((Fintype.equivFin (Ent X')).symm (Fintype.equivFin (Ent X') (τ', p)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem nmat_coordIso (z : V (nd X)) (τ' : X'.Ψ) :
    nmat X' (coordIso X X' e z) τ' = nmat X z (e.symm τ') := by
  funext a b
  unfold nmat
  split_ifs with h
  · refine (coordIso_apply X X' e z _).trans ?_
    exact congrArg (fun k : Fin (nd X) => z k) (idxEquiv_symm_equivFin X X' e τ' _)
  · rfl
  · rfl

def coordIsoR : V (nd X) ≃ₗᵢ[ℝ] V (nd X') :=
  { (coordIso X X' e).toLinearEquiv.restrictScalars ℝ with norm_map' := (coordIso X X' e).norm_map }

theorem coordIso_mp : MeasurePreserving (coordIso X X' e) := (coordIsoR X X' e).measurePreserving

theorem map_restrict_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} (S : α ≃ᵐ β) (hS : MeasurePreserving S μ ν) {Ω : Set α} {Ω' : Set β}
    (hΩ : S ⁻¹' Ω' = Ω) {d : α → ℝ≥0∞} {d' : β → ℝ≥0∞} (hd : ∀ x, d' (S x) = d x) :
    Measure.map S ((μ.restrict Ω).withDensity d) = (ν.restrict Ω').withDensity d' := by
  ext A hA
  rw [S.map_apply, withDensity_apply _ hA, withDensity_apply _ (S.measurable hA), ← hS.map_eq,
    S.restrict_map, S.restrict_map, lintegral_map_equiv, hΩ]
  simp_rw [hd]

theorem trF_cpt (z : V (nd X)) :
    trF X X' e (cpt X (baseFr X) z) = cpt X' (baseFr X') (coordIso X X' e z) := by
  funext τ'
  have hB : IsUnit (mat (baseFr X) (e.symm τ')).det :=
    isUnit_iff_ne_zero.2 (X.signature (e.symm τ')).choose_spec.1
  have h1 : mat (cpt X (baseFr X) z) (e.symm τ') =
      mat (baseFr X) (e.symm τ') * mat (nmat X z) (e.symm τ') := rfl
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat (cpt X (baseFr X) z) (e.symm τ') :
      Matrix (Fin r) (Fin r) ℂ) = (mat (baseFr X') τ' * mat (nmat X' (coordIso X X' e z)) τ' : Matrix (Fin r) (Fin r) ℂ)
  rw [h1, h2, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem gram_cpt_base {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    gram τ.1 Y.Gm (mat (cpt Y (baseFr Y) z) τ) =
      (mat (nmat Y z) τ)ᵀ * sgnMat r Y.p0 * (mat (nmat Y z) τ).map (starRingEnd ℂ) := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  rw [h1, gram_mul_right, baseFr_mem Y τ]

variable {X X'} in
theorem dmin_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) (τ' : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (cpt X' (baseFr X') (coordIso X X' e z)) τ' i = dmin X.Gm (cpt X (baseFr X) z) (e.symm τ') i := by
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  unfold dmin
  rw [gram_cpt_base, gram_cpt_base, h2, hp]

theorem det_cpt_base_ne {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    (mat (cpt Y (baseFr Y) z) τ).det ≠ 0 ↔ (mat (nmat Y z) τ).det ≠ 0 := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  have hB : (mat (baseFr Y) τ).det ≠ 0 := (Y.signature τ).choose_spec.1
  rw [h1, Matrix.det_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hB, h⟩⟩

variable {X X'} in
theorem mem_dom_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    cpt X' (baseFr X') (coordIso X X' e z) ∈ X'.dom ↔ cpt X (baseFr X) z ∈ X.dom := by
  show (∀ τ' : X'.Ψ, _ ∧ _) ↔ (∀ τ : X.Ψ, _ ∧ _)
  refine Iff.trans ?_ e.symm.forall_congr_right
  refine forall_congr' fun τ' => ?_
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  rw [det_cpt_base_ne, det_cpt_base_ne, h2, hp]
  simp only [dmin_coordIso e hp]

variable {X X'} in
theorem densF_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    densF X' (baseFr X') (coordIso X X' e z) = densF X (baseFr X) z := by
  unfold densF
  simp only [dmin_coordIso e hp]
  exact (Fintype.prod_equiv e.symm _ _ fun _ => rfl)

variable {X X'} in
theorem map_muF (hp : X.p0 = X'.p0) :
    Measure.map (coordIso X X' e).toHomeomorph.toMeasurableEquiv (muF X (baseFr X)) = muF X' (baseFr X') := by
  unfold muF
  refine map_restrict_withDensity _ (coordIso_mp X X' e) ?_ ?_
  · ext z
    exact mem_dom_coordIso e hp z
  · intro z
    exact congrArg ENNReal.ofReal (densF_coordIso e hp z)

end

theorem lintegral_trF_cpt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
        ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  rw [← map_muF e hp, lintegral_map_equiv]
  simp_rw [trF_cpt]
  rfl

end GlobalTheory.FlagTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameRealUnitary
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

theorem secondCountable_GL_complex (r : ℕ) : SecondCountableTopology (GL (Fin r) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  have : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountable_Upq (r p : ℕ) : SecondCountableTopology (Upq r p) := by
  have := secondCountable_GL_complex r
  exact TopologicalSpace.Subtype.secondCountableTopology _

theorem sigmaFinite_haarU (r p : ℕ) : SigmaFinite (haarU r p) := by
  have := secondCountable_Upq r p
  unfold haarU
  infer_instance

theorem lintegral_pi_haarU_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (r p q : ℕ) (h : p = q)
    (F : (ι' → Matrix (Fin r) (Fin r) ℂ) → ℝ≥0∞) :
    ∫⁻ g : ι → Upq r p, F (fun i' => ((g (e.symm i') : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        ∂Measure.pi (fun _ => haarU r p) =
      ∫⁻ g : ι' → Upq r q, F (fun i' => ((g i' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        ∂Measure.pi (fun _ => haarU r q) := by
  subst h
  have := sigmaFinite_haarU r p
  have hmp := measurePreserving_piCongrLeft (fun _ : ι' => haarU r p) e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  funext g
  congr 1
  funext i'
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem trF_frameOf {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E']
    [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ) (g : RealGrp X) :
    trF X X' e (frameOf X g) = rmul (baseFr X')
      (fun τ' => (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  funext τ'
  have h : (mat (baseFr X) (e.symm τ')).det ≠ 0 := (X.signature (e.symm τ')).choose_spec.1
  show mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ *
      (mat (baseFr X) (e.symm τ') * (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
    mat (baseFr X') τ' * (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (mat (baseFr X) (e.symm τ')), Matrix.nonsing_inv_mul _ h.isUnit,
    Matrix.one_mul]

theorem lintegral_trF_frameOf : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  simp_rw [trF_frameOf]
  exact lintegral_pi_haarU_reindex e r X.p0 X'.p0 hp (fun M => φ (rmul (baseFr X') M))

end GlobalTheory.FlagQuotHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDual
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def rankOneHerm (G : Matrix (Fin r) (Fin r) E) (l y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => l a * ∑ k, G b k * cc (y k)

theorem rankOneHerm_mulVec (G : Matrix (Fin r) (Fin r) E) (l y x : Fin r → E) :
    rankOneHerm G l y *ᵥ x = herm G x y • l := by
  ext a
  simp only [rankOneHerm, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, herm]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trace_mul_rankOneHerm (G Y : Matrix (Fin r) (Fin r) E) (l y : Fin r → E) :
    (Y * rankOneHerm G l y).trace = herm G (Y *ᵥ l) y := by
  simp only [trace, diag, Matrix.mul_apply, rankOneHerm, of_apply, herm, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem rankOneHerm_mem_endLat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hΛ : SelfDualLat G Λ) {l y : Fin r → E} (hl : l ∈ Λ) (hy : y ∈ Λ) :
    rankOneHerm G l y ∈ endLat Λ := fun x hx => by
  rw [rankOneHerm_mulVec]
  exact smul_mem_of_isIntegral (((hΛ.2.2.2.2 x).mpr hx) y hy) hl

theorem mem_endLat_of_trace_integral (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E)
    (hΛ : SelfDualLat G Λ) (hY : ∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) : Y ∈ endLat Λ := by
  intro l hl
  refine (hΛ.2.2.2.2 _).mp fun y hy => ?_
  rw [← trace_mul_rankOneHerm]
  exact hY _ (rankOneHerm_mem_endLat hΛ hl hy)

end GlobalTheory.LieDisc
end

