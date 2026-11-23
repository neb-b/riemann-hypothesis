module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_span_eq_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J K : Ideal R) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a : R) (A : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * A ∧ IsCoprime A K := by
  classical
  have hJK : J * K ≠ ⊥ := mul_ne_zero hJ hK

  obtain ⟨a₀, ha₀⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : J * K ≤ J) hJK
  obtain ⟨b, hbJK, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJK

  have key : ∃ a : R, a ≠ 0 ∧ J * K ⊔ Ideal.span {a} = J := by
    by_cases h0 : a₀ = 0
    · refine ⟨b, hb0, ?_⟩
      have hJKJ : J * K = J := by simpa [h0] using ha₀
      rw [sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJK)), hJKJ]
    · exact ⟨a₀, h0, ha₀⟩
  obtain ⟨a, ha0, ha⟩ := key
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.mpr haJ
  refine ⟨a, A, ha0, hA, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]

  have h1 : J * (K ⊔ A) = J * ⊤ := by
    rw [Ideal.mul_sup, ← hA, ha, Ideal.mul_top]
  rw [sup_comm]
  exact mul_left_cancel₀ hJ h1

theorem exists_generator_at_primes_dividing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  intro E _ _ _ 𝔍 M h𝔍 hM
  have hK : Ideal.span {(M : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  exact exists_span_eq_mul_coprime 𝔍 _ h𝔍 hK

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Extend

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (a b : GL (Fin r) E) (L : Lt E r) : mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

omit [NumberField E] [IsCMField E] in
theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) (x b : Frame Ψ r) :
    lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) a) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro i
  rw [differentiable_pi]; intro j
  simp only [lact, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

variable {X : Data E r}

theorem gramE {a : GL (Fin r) E} (ha : IsUn X a) :
    (a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc = X.Gm := by
  ext i j
  have h := ha (Pi.single i 1) (Pi.single j 1)
  simp only [FD.herm, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, _root_.one_mul] at h
  have hL : ((a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc) i j =
      ∑ c, ∑ d, (a : Matrix (Fin r) (Fin r) E) c i * X.Gm c d * FD.cc ((a : Matrix (Fin r) (Fin r) E) d j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hL, h]
  simp [apply_ite FD.cc]

omit [NumberField E] [IsCMField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dmin_lact {a : GL (Fin r) E} (ha : IsUn X a) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact a x) τ i = dmin X.Gm x τ i := by
  have hc : ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((a : Matrix (Fin r) (Fin r) E).map FD.cc).map τ.1 := by
    ext i j
    simp only [Matrix.map_apply]
    exact (IsCMField.complexEmbedding_complexConj E τ.1 _).symm
  have key : ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, gramE ha]
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  unfold dmin
  congr 1
  rw [gram_eq, gram_eq, e1, Matrix.transpose_mul, Matrix.map_mul]
  calc (mat x τ).transpose * ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        (((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ))
      = (mat x τ).transpose * (((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) * (mat x τ).map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lact_mem {a : GL (Fin r) E} (ha : IsUn X a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a x ∈ X.dom := by
  intro τ
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (a.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · rw [dmin_lact ha]
    exact (hx τ).2 i

end GlobalTheory.Dict.Extend

theorem GlobalTheory.Dict.exists_form_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  intro E _ _ _ r X Δ 𝓛 mu la Jx _ L Q hun hmu hcoc hL hsep hst hQ
  let F : Lt E r → Frame X.Ψ r → ℂ := fun L' x =>
    if h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L' then
      (mu h.choose.2 (L h.choose.1))⁻¹ * Q h.choose.1 (lact h.choose.2⁻¹ x) else 0
  have key : ∀ k, ∀ a ∈ Δ, ∀ x ∈ X.dom,
      F (mapL a (L k)) x = (mu a (L k))⁻¹ * Q k (lact a⁻¹ x) := by
    intro k a ha x hx
    have h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = mapL a (L k) := ⟨(k, a), ha, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    generalize h.choose = p at h1 h2
    obtain ⟨k', b⟩ := p
    dsimp only at h1 h2 ⊢
    have hs : a⁻¹ * b ∈ Δ := Δ.mul_mem (Δ.inv_mem ha) h1
    have h3 : mapL (a⁻¹ * b) (L k') = L k := by
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
    obtain rfl := hsep k' k _ hs h3
    have h4 : mu b (L k') = mu a (L k') := by
      have := hcoc a ha _ hs _ (hL k')
      rwa [mul_inv_cancel_left, h3, hst _ _ hs h3, _root_.mul_one] at this
    have h5 := (hQ k').inv _ hs h3 _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx)
    rw [Extend.lact_lact, mul_inv_cancel_right] at h5
    rw [h4, h5]
  have zero : ∀ L', (¬ ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L') → ∀ x, F L' x = 0 :=
    fun L' h x => by simp only [F, dif_neg h]
  choose C hC using fun k => (hQ k).bdd
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  refine ⟨F, ⟨fun L' _ => ?_, fun L' _ x hx b hb => ?_, fun g hg L' hL' x hx => ?_,
    max B 0, fun L' _ x hx => ?_⟩, fun k x hx => ?_⟩
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      refine DifferentiableOn.congr ?_ (key k a ha)
      exact ((hQ k).hol.comp (Extend.differentiable_lact a⁻¹).differentiableOn
        fun x hx => Extend.lact_mem (hun _ (Δ.inv_mem ha)) hx).const_mul _
    · exact (differentiableOn_const 0).congr fun x _ => zero L' h x
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨h1, -⟩ := h.choose_spec
      simp only [F, dif_pos h]
      rw [Extend.lact_rmul, (hQ _).bor _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx) b hb]
      ring
    · rw [zero L' h, zero L' h, mul_zero]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      rw [← Extend.mapL_mul, key k _ (Δ.mul_mem hg ha) _ (Extend.lact_mem (hun g hg) hx), key k a ha x hx,
        hcoc g hg a ha _ (hL k), Extend.lact_lact, _root_.mul_inv_rev g a, inv_mul_cancel_right, mul_inv,
        _root_.mul_assoc]
    · rw [zero L' h, mul_zero]
      refine zero _ ?_ _
      rintro ⟨⟨k, a⟩, ha, h2⟩
      refine h ⟨(k, g⁻¹ * a), Δ.mul_mem (Δ.inv_mem hg) ha, ?_⟩
      dsimp only at h2 ⊢
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      have hu := hun _ (Δ.inv_mem ha)
      have h1 := hC k _ (Extend.lact_mem hu hx)
      refine le_trans (le_of_eq ?_) (h1.trans ((hB ⟨k, rfl⟩).trans (le_max_left _ _)))
      simp only [Data.pnorm, Extend.dmin_lact hu]
      rw [key k a ha x hx, norm_mul, norm_inv, (hmu a ha _ (hL k)).2, inv_one, _root_.one_mul]
    · simp only [Data.pnorm]
      rw [zero L' h, norm_zero, zero_mul]
      exact le_max_right _ _
  · have h := key k 1 Δ.one_mem x hx
    rw [hst k 1 Δ.one_mem (Extend.mapL_one _), Extend.mapL_one, inv_one, inv_one, _root_.one_mul,
      Extend.lact_one] at h
    exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColPoly

section Deriv

variable {σ κ W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

theorem polyDeriv_comp_linear {F : W' → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (A : W →L[ℂ] W')
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) :
    I2.polyDeriv P u (fun z => F (A z)) x = I2.polyDeriv P (fun l => A (u l)) F (A x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hcomp := A.iteratedFDeriv_comp_right hF x
    (i := Multiset.card (Finsupp.toMultiset m)) (by exact_mod_cast le_top)
  rw [show (fun z => F (A z)) = F ∘ A from rfl, hcomp]
  rfl

private theorem polyDeriv_C_indep (a : ℂ) (u v : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) u F x =
      I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) v F x := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
  subst hm0
  congr 1

theorem polyDeriv_subst [Fintype κ] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [MvPolynomial.algHom_C]
    exact polyDeriv_C_indep a _ _ F x
  | add p q hp hq => rw [map_add (f := _), I2.polyDeriv_add, I2.polyDeriv_add, hp, hq]
  | mul_X p l hp =>
    have e1 : (fun y => I2.polyDeriv (Φ p) u F y) =
        fun y => I2.polyDeriv p (fun l => ∑ k, s l k • u (j l k)) F y := funext hp
    rw [polyDeriv_mul_X hF p _ l x, map_mul, hΦ l, Finset.mul_sum, I2.jof_polyDeriv_sum]
    simp_rw [MvPolynomial.C_mul', mul_smul_comm, I2.polyDeriv_smul, polyDeriv_mul_X hF (Φ p) u _ x, e1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, smul_eq_mul]

end Deriv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

noncomputable def hActL (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (h : Matrix (Fin n) (Fin n) E) :
    (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hAct X idx h
      map_add' := fun x y => by funext k i; simp [hAct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext k i; simp [hAct, Finset.mul_sum, mul_left_comm] }

end GlobalTheory.Dict.ColPoly


open GlobalTheory.Dict.ColPoly in
theorem GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  intro E _ _ _ r X g q0 hr bas idx n _hs _hn h hh k k' P hP
  classical
  let A : X.Ψ → Matrix (Fin n) (Fin n) ℂ := fun t => (h.map (t.1 : E →+* ℂ))ᵀ
  let B : X.Ψ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => h.map (ComplexEmbedding.conjugate (t.1 : E →+* ℂ))
  have hAB : ∀ t, A t * B t = 1 := by
    intro t
    have h1 := congrArg (fun M => M.map (t.1 : E →+* ℂ)) hh
    simp only [Matrix.map_mul, GlobalTheory.SW.Base.ccT_map, Matrix.map_one _ (map_zero _) (map_one _)] at h1
    ext i j
    have h2 := congrFun (congrFun h1 j) i
    simp only [A, B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.conjTranspose_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.one_apply] at h2 ⊢
    convert h2 using 1
    · exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]; rfl
    · by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
  let s : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ :=
    fun l k₁ => rowType X (rowOf X hr (l.1, l.2.1)) (h k₁ l.2.2)
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) :=
    fun l k₁ => (l.1, l.2.1, k₁)
  have hΦ : ∀ l, GlobalTheory.Harm.colSubst A B (MvPolynomial.X l) =
      ∑ k₁, MvPolynomial.C (s l k₁) * MvPolynomial.X (j l k₁) := by
    rintro ⟨t, (a | b), k₀⟩
    · have e : rowType X (t, rowIdx hr (Sum.inl a)) = t.1 := by
        simpa using rowType_rowOf_inl X hr t a
      simp [GlobalTheory.Harm.xForm, GlobalTheory.Harm.rowForm_apply, A, s, j, e]
    · have e : rowType X (t, rowIdx hr (Sum.inr b)) = ComplexEmbedding.conjugate t.1 := by
        simpa using rowType_rowOf_inr X hr t b
      simp [GlobalTheory.Harm.yForm, GlobalTheory.Harm.rowForm_apply, B, s, j, e, ComplexEmbedding.conjugate_coe_eq]
  have hdir : (fun l => hActL X idx h (letterDir X hr idx l)) =
      fun l => ∑ k₁, s l k₁ • letterDir X hr idx (j l k₁) := by
    funext l k₁ i
    show hAct X idx h (letterDir X hr idx l) k₁ i = _
    by_cases hi : i = idx.symm (rowOf X hr (l.1, l.2.1))
    · subst hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, ite_apply, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp only [rowOf_apply] at hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, hi, ite_apply, mul_ite]
  refine ⟨GlobalTheory.Harm.colSubst A B P, GlobalTheory.Harm.colSubst_mem_rowHighest hAB hP, fun F hF => ?_⟩
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  have e0 := polyDeriv_comp_linear hF' (hActL X idx h) P (letterDir X hr idx) 0
  rw [map_zero, hdir] at e0
  rw [show (fun z => F (hAct X idx h z)) = fun z => F (hActL X idx h z) from rfl, e0]
  exact (polyDeriv_subst hF' s j (GlobalTheory.Harm.colSubst A B) hΦ (letterDir X hr idx) P 0).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
  (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem fock_hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, mulVec_add, add_dotProduct]

theorem fock_hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, mulVec_add, star_add, dotProduct_add]

theorem fock_hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem fock_hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul]
  rfl

theorem fock_hx_zero_right (z : Fin g → ℂ) : hx X bas idx x z 0 = 0 := by
  simp [hx]

theorem fock_hx_differentiable (w : Fin g → ℂ) : Differentiable ℂ fun z => hx X bas idx x z w := by
  simp only [hx, dotProduct, mulVec]
  fun_prop

theorem fock_hx_conj (hs : IsSympl X bas) (hd : x ∈ X.dom) (z w : Fin g → ℂ) :
    hx X bas idx x w z = conj (hx X bas idx x z w) := by
  have h := imInv_isSymm idx hs hd
  have hr : ∀ i j, conj (imInv X bas idx x i j) = imInv X bas idx x j i := by
    intro i j
    rw [h.apply i j]
    simp [ThFr.imInv]
  simp only [hx]
  generalize hMat X bas idx x *ᵥ z = u
  generalize hMat X bas idx x *ᵥ w = v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply, hr, RCLike.star_def,
    conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem fock_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), (∀ a b, fock X bas idx x k a (fock X bas idx x k b θ) = cexp (-((k : ℂ) * Real.pi * I * ((hx X bas idx x a b).im : ℂ))) • fock X bas idx x k (a + b) θ) ∧ fock X bas idx x k 0 θ = θ ∧ (∀ (N : ℕ) a, fock X bas idx x (N ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock X bas idx x 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ (Differentiable ℂ θ → ∀ a, Differentiable ℂ (fock X bas idx x k a θ)) ∧ ∀ (th : Fin n → (Fin g → ℂ) → ℂ) (κ : ℂ) (φ : TF n g), IsSB φ → (∀ z : Fin n → Fin g → ℂ, ∏ b, th b (z b) = κ * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x 1 (pv X idx x (y b)) (th b) (z b) = κ * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hs hn x hd k θ
  refine ⟨fun a b => ?_, ?_, fun N a => ?_, fun hθ a => ?_, fun th κ φ hφ h y z => ?_⟩
  · funext z
    simp only [fock, Pi.smul_apply, smul_eq_mul]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    rw [add_assoc z a b]
    congr 2
    simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left, smul_add]
    rw [fock_hx_conj X bas idx x hs hd a b]
    have := Complex.sub_conj (hx X bas idx x a b)
    push_cast at this
    linear_combination (-(k : ℂ) * Real.pi / 2) * this
  · funext z
    simp [fock, fock_hx_zero_right]
  · funext z
    simp only [fock, smul_add]
    congr 2
    simp only [fock_hx_add_left, fock_hx_smul_left, fock_hx_smul_right, map_natCast]
    push_cast
    ring
  · have h1 := fock_hx_differentiable X bas idx x a
    unfold fock
    refine Differentiable.mul (Differentiable.cexp (Differentiable.neg (Differentiable.const_mul ?_ _))) ?_
    · exact h1.comp (differentiable_id.add_const _)
    · exact hθ.comp (differentiable_id.add_const _)
  · rw [((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hd z]
    simp only [fock, Finset.prod_mul_distrib]
    rw [h fun b => z b + pv X idx x (y b), ← Complex.exp_sum, mul_left_comm]
    congr 2
    simp only [hx, pv, Finset.mul_sum, Finset.sum_neg_distrib, Nat.cast_one, _root_.one_mul]

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndexStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLattice_selfDual_semicharacter_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (tens Λ L).FG ∧ (∀ y, y ∈ tens Λ L ↔ ∀ y' ∈ tens Λ L, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k) ∧ (∀ y ∈ tens Λ L, epsW X w y ^ 2 = 1 ∧ ∀ y' ∈ tens Λ L, epsW X w (y + y') = epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ y : Matrix (Fin n) (Fin r) E, y ∈ tens (stdL E n) L ↔ ∀ k, y k ∈ L) ∧ (∀ L', SelfD X L' → (tens Λ L').relIndex (tens Λ L) = L'.toAddSubgroup.relIndex L.toAddSubgroup ^ n ∧ tens Λ L ⊓ tens Λ L' = tens Λ (L ⊓ L')) ∧ ∀ Λ' ∈ Vset E n M, (tens Λ' L).relIndex (tens Λ L) = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup ^ r := by
  first | exact @GlobalTheory.SW.TensLat.tens_selfDual_semichar_index | exact GlobalTheory.SW.TensLat.tens_selfDual_semichar_index | (intros; apply GlobalTheory.SW.TensLat.tens_selfDual_semichar_index <;> assumption)
end

