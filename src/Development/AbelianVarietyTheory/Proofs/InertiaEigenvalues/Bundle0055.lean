module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonEigenvectorCommuting
section
open scoped BigOperators

namespace GlobalTheory.CommTriang

theorem exists_common_eigenvector_commuting {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : ι → Module.End k V) (hc : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ → (∀ i, ∀ w ∈ W, f i w ∈ W) →
      ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : k, f i x = c • x := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | (apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target ..)

theorem exists_common_eigenvector : ∀ (k ι : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (T : ι → Matrix (Fin (n+1)) (Fin (n+1)) k), (∀ i j, T i * T j = T j * T i) →
    ∃ v : Fin (n+1) → k, v ≠ 0 ∧ ∃ χ : ι → k, ∀ i, (T i).mulVec v = χ i • v := by
  intro k ι _ _ n T hT
  have hc : ∀ i j, Matrix.toLin' (T i) * Matrix.toLin' (T j) = Matrix.toLin' (T j) * Matrix.toLin' (T i) := by
    intro i j
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]
  obtain ⟨x, -, hx0, hx⟩ := exists_common_eigenvector_commuting (fun i => Matrix.toLin' (T i)) hc _ ⊤ rfl
    (by simp) (fun _ _ _ => Submodule.mem_top)
  choose χ hχ using hx
  exact ⟨x, hx0, χ, fun i => by simpa using hχ i⟩

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

theorem exists_unit_col_zero : ∀ (k : Type) [Field k] (n : ℕ) (v : Fin (n+1) → k), v ≠ 0 →
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) k, IsUnit P ∧ ∀ a, P a 0 = v a := by
  first
  | exact @_root_.GlobalTheory.IntegralCriterion.main
  | exact _root_.GlobalTheory.IntegralCriterion.main
  | (apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCriterion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCriterion.main ..)

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

theorem lift_eigen : ∀ (k ι V : Type) [Field k] [AddCommGroup V] [Module k V] (f : ι → Module.End k V) (v u : V) (χ μ r : ι → k),
    (∀ i j, f i * f j = f j * f i) → v ≠ 0 → (∀ t : k, u + t • v ≠ 0) → (∀ i, f i v = χ i • v) →
    (∀ i, f i u = μ i • u + r i • v) → ∃ x : V, x ≠ 0 ∧ ∀ i, f i x = μ i • x := by
  intro k ι V _ _ _ f v u χ μ r hc hv0 hu0 hv hu
  by_cases h : ∀ i, χ i = μ i
  · exact ⟨v, hv0, fun i => by rw [hv, h]⟩
  push_neg at h
  obtain ⟨i₀, hi₀⟩ := h
  have hd : μ i₀ - χ i₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hi₀)
  set t : k := r i₀ / (μ i₀ - χ i₀) with ht
  have htd : t * (μ i₀ - χ i₀) = r i₀ := div_mul_cancel₀ _ hd
  have hfx : ∀ j, f j (u + t • v) = μ j • (u + t • v) + (r j + t * χ j - t * μ j) • v := by
    intro j
    rw [map_add (f := _), map_smul, hu, hv]
    module
  have h0 : f i₀ (u + t • v) = μ i₀ • (u + t • v) := by
    rw [hfx]
    have : r i₀ + t * χ i₀ - t * μ i₀ = 0 := by rw [← htd]; ring
    rw [this, zero_smul, add_zero]
  obtain ⟨x, hx⟩ : ∃ x, x = u + t • v := ⟨_, rfl⟩
  rw [← hx] at hfx h0
  refine ⟨x, hx ▸ hu0 t, fun j => ?_⟩
  have e1 : f i₀ (f j x) = f j (f i₀ x) := by
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
  rw [h0, map_smul, hfx j, map_add (f := _), map_smul, map_smul, h0, hv] at e1
  have e2 : ((r j + t * χ j - t * μ j) * (χ i₀ - μ i₀)) • v = 0 := by
    linear_combination (norm := module) e1
  rcases smul_eq_zero.mp e2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [hfx j, h, zero_smul, add_zero]
    · exact absurd (sub_eq_zero.mp h) hi₀
  · exact absurd h hv0

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

open Matrix

def blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n+1)) (Fin (n+1)) k :=
  Matrix.of fun a b => Fin.cases (motive := fun _ => k) (Fin.cases (motive := fun _ => k) 1 (fun _ => 0) b)
    (fun a' => Fin.cases (motive := fun _ => k) 0 (fun b' => Q a' b') b) a

section
variable {k : Type} [Field k] {n : ℕ}

theorem blockOne_mul (Q R : Matrix (Fin n) (Fin n) k) : blockOne Q * blockOne R = blockOne (Q * R) := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockOne_one : blockOne (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [blockOne, Matrix.one_apply] <;> exact (Fin.succ_ne_zero _).symm

theorem conj_succ_succ (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a b : Fin n) :
    (blockOne R * S * blockOne Q) a.succ b.succ = (R * S.submatrix Fin.succ Fin.succ * Q) a b := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem conj_succ_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a : Fin n) :
    (blockOne R * S * blockOne Q) a.succ 0 = ∑ c, R a c * S c.succ 0 := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem conj_zero_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) :
    (blockOne R * S * blockOne Q) 0 0 = S 0 0 := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

end

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

theorem isUnit_blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) (hQ : IsUnit Q) :
    IsUnit (blockOne Q) ∧ (blockOne Q)⁻¹ = blockOne Q⁻¹ := by
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have h : blockOne Q * blockOne Q⁻¹ = 1 := by
    rw [blockOne_mul, Matrix.mul_nonsing_inv _ hQd, blockOne_one]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h), Matrix.inv_eq_right_inv h⟩

theorem exists_triangular (k ι : Type) [Field k] [IsAlgClosed k] : ∀ (n : ℕ) (T : ι → Matrix (Fin n) (Fin n) k),
    (∀ i j, T i * T j = T j * T i) →
    ∃ P : Matrix (Fin n) (Fin n) k, IsUnit P ∧ (∀ i, (P⁻¹ * T i * P).BlockTriangular id) ∧
      ∀ a, ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, (T i).mulVec x = (P⁻¹ * T i * P) a a • x := by
  intro n
  induction n with
  | zero => intro T _; exact ⟨1, isUnit_one, fun i a b _ => a.elim0, fun a => a.elim0⟩
  | succ n ih =>
    intro T hT
    obtain ⟨v, hv0, χ, hv⟩ := exists_common_eigenvector k ι n T hT
    obtain ⟨P₀, hP₀, hP₀v⟩ := exists_unit_col_zero k n v hv0
    have hP₀d : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det P₀).mp hP₀
    have hl : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hP₀d
    have hr : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP₀d
    set S : ι → Matrix (Fin (n+1)) (Fin (n+1)) k := fun i => P₀⁻¹ * T i * P₀ with hSdef
    have hST : ∀ i, P₀ * S i = T i * P₀ := by
      intro i; simp only [hSdef, ← Matrix.mul_assoc, hr, Matrix.one_mul]
    have hSc : ∀ i j, S i * S j = S j * S i := by
      intro i j
      have e : ∀ i j, S i * S j = P₀⁻¹ * (T i * T j) * P₀ := by
        intro i j
        simp only [hSdef, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P₀ P₀⁻¹, hr, Matrix.one_mul]
      rw [e, e, hT]
    set e0 : Fin (n+1) → k := Pi.single 0 1 with he0
    have hPe : P₀.mulVec e0 = v := by
      ext a; simp [he0, Matrix.mulVec, dotProduct, Pi.single_apply, hP₀v]
    have hSe : ∀ i, (S i).mulVec e0 = χ i • e0 := by
      intro i
      have : P₀⁻¹.mulVec v = e0 := by rw [← hPe, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
      simp only [hSdef]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, hv, Matrix.mulVec_smul, this]
    have hScol : ∀ i a, S i a 0 = χ i * e0 a := by
      intro i a
      have := congrFun (hSe i) a
      simpa [he0, Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hS0 : ∀ i (a : Fin n), S i a.succ 0 = 0 := by
      intro i a; rw [hScol]; simp [he0, Fin.succ_ne_zero]
    have hS00 : ∀ i, S i 0 0 = χ i := by
      intro i; rw [hScol]; simp [he0]
    set B : ι → Matrix (Fin n) (Fin n) k := fun i => (S i).submatrix Fin.succ Fin.succ with hBdef
    have hBc : ∀ i j, B i * B j = B j * B i := by
      intro i j; ext a b
      have := congrFun (congrFun (hSc i j) a.succ) b.succ
      simpa [hBdef, Matrix.mul_apply, Fin.sum_univ_succ, hS0] using this
    obtain ⟨Q, hQ, hQtri, hQev⟩ := ih B hBc
    obtain ⟨hDQ, hDQinv⟩ := isUnit_blockOne Q hQ
    refine ⟨P₀ * blockOne Q, hP₀.mul hDQ, ?_⟩
    have hM : ∀ i, (P₀ * blockOne Q)⁻¹ * T i * (P₀ * blockOne Q) = blockOne Q⁻¹ * S i * blockOne Q := by
      intro i
      rw [Matrix.mul_inv_rev, hDQinv]
      simp only [hSdef, Matrix.mul_assoc]
    refine ⟨?_, ?_⟩
    · intro i a b hab
      rw [hM]
      cases a using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ a =>
        cases b using Fin.cases with
        | zero => rw [conj_succ_zero]; simp [hS0]
        | succ b =>
          rw [conj_succ_succ]
          exact hQtri i (by simpa using hab)
    · intro a
      cases a using Fin.cases with
      | zero =>
        refine ⟨v, hv0, fun i => ?_⟩
        rw [hM, conj_zero_zero, hS00, hv]
      | succ a =>
        obtain ⟨y, hy0, hy⟩ := hQev a
        set μ : ι → k := fun i => (Q⁻¹ * B i * Q) a a with hμ
        set u : Fin (n+1) → k := Fin.cons 0 y with hu
        obtain ⟨x', hx'0, hx'⟩ := lift_eigen k ι (Fin (n+1) → k) (fun i => Matrix.toLin' (S i)) e0 u χ μ
          (fun i => ∑ b, S i 0 b.succ * y b)
          (by intro i j; rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hSc])
          (by simp [he0])
          (by
            intro t h
            obtain ⟨b, hb⟩ := Function.ne_iff.mp hy0
            have := congrFun h b.succ
            simp [hu, he0, Fin.succ_ne_zero] at this
            exact hb this)
          (fun i => by simpa using hSe i)
          (by
            intro i
            ext c
            cases c using Fin.cases with
            | zero => simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            | succ c =>
              have hyi : (B i).mulVec y = μ i • y := hy i
              have := congrFun hyi c
              simp only [hBdef, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at this
              simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hS0, Fin.succ_ne_zero, this])
        refine ⟨P₀.mulVec x', ?_, fun i => ?_⟩
        · intro h
          apply hx'0
          apply (Matrix.mulVec_injective_iff_isUnit.mpr hP₀)
          rw [h, Matrix.mulVec_zero]
        · have hx := hx' i
          simp only [Matrix.toLin'_apply] at hx
          rw [hM, conj_succ_succ, Matrix.mulVec_mulVec, ← hST, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

end GlobalTheory.CommTriang
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_of_mk_le_continuum {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (hΩ : #Ω ≤ 𝔠) (σ : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    simpa [Cardinal.mkRat] using this
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hst : #s ≤ #t := by
    have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK
      (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    rw [← h1, Cardinal.mk_complex]
    exact (Cardinal.mk_subtype_le _).trans hΩ
  obtain ⟨e⟩ := hst
  have hv : AlgebraicIndependent K (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let f : IntermediateField.adjoin K (Set.range ((↑) : s → Ω)) →ₐ[K] ℂ :=
    (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
  have halg := hs.isAlgebraic_field
  obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' f
    (fun (x : Ω) => ⟨(Algebra.IsAlgebraic.isAlgebraic
      (R := IntermediateField.adjoin K (Set.range ((↑) : s → Ω))) x).isIntegral, IsAlgClosed.splits _⟩)
  refine ⟨φ.toRingHom, ?_⟩
  ext x
  exact φ.commutes x

theorem exists_embedding_fractionField :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes →
      ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T hT io
  haveI : Finite (ResidueField T.V) := hT
  have hV := mk_le_continuum_of_finite_residueField T.V
  have hF : #T.Fr ≤ 𝔠 := by
    rw [show #T.Fr = #T.V from IsFractionRing.cardinalMk T.V T.Fr]
    exact hV
  exact @exists_embedding_of_mk_le_continuum K T.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCongruenceNearSymmetricMatrix
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem symm_congr_local_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (H₀ : Matrix (Fin r) (Fin r) F), H₀.IsSymm → H₀.det ≠ 0 →
    ∃ (Ω : Set (Matrix (Fin r) (Fin r) F)) (k : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F),
      IsOpen Ω ∧ H₀ ∈ Ω ∧ ContinuousOn k Ω ∧ k H₀ = 1 ∧ ∀ H ∈ Ω, H.IsSymm → (k H)ᵀ * H₀ * k H = H := by
  intro F E _ _ _ _ hU r H₀ hsym hdet
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI : NormedRing (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin r) (Fin r) F) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete F _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let L : Matrix (Fin r) (Fin r) F ≃L[F] Matrix (Fin r) (Fin r) F :=
    ContinuousLinearEquiv.equivOfInverse ((2 : F) • ContinuousLinearMap.id F _)
      ((2 : F)⁻¹ • ContinuousLinearMap.id F _)
      (by intro x; simp [smul_smul, inv_mul_cancel₀ h2]) (by intro x; simp [smul_smul, mul_inv_cancel₀ h2])
  have hf : HasStrictFDerivAt (fun Y : Matrix (Fin r) (Fin r) F => Y * Y)
      (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) 1 := by
    have h := (hasStrictFDerivAt_id (𝕜 := F) (1 : Matrix (Fin r) (Fin r) F)).mul' (hasStrictFDerivAt_id 1)
    have e : (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) =
        (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) +
          MulOpposite.op (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) := by
      ext1 D
      simp [L, two_smul]
    rw [e]
    exact h
  set P := hf.toOpenPartialHomeomorph _ with hPdef
  have hPc : ∀ Y, P Y = Y * Y := fun Y => by
    rw [hPdef, hf.toOpenPartialHomeomorph_coe]
  have h1s : (1 : Matrix (Fin r) (Fin r) F) ∈ P.source := hf.mem_toOpenPartialHomeomorph_source
  have h1t : (1 : Matrix (Fin r) (Fin r) F) ∈ P.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target
    simpa using this
  have hS1 : P.symm 1 = 1 := by
    have := P.left_inv h1s
    rwa [hPc, one_mul] at this
  have hu : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hdet
  set A := H₀⁻¹ with hA
  have hAH : A * H₀ = 1 := Matrix.nonsing_inv_mul H₀ hu
  have hHA : H₀ * A = 1 := Matrix.mul_nonsing_inv H₀ hu
  have hAT : Aᵀ = A := by
    rw [hA, Matrix.transpose_nonsing_inv, hsym.eq]
  let φ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F := fun Y => A * Yᵀ * H₀
  have hφc : Continuous φ := by
    exact (continuous_const.matrix_mul (continuous_id.matrix_transpose)).matrix_mul continuous_const
  let ψ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F := fun H => A * H
  have hψc : Continuous ψ := continuous_const.matrix_mul continuous_id
  have hT : IsOpen (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)) :=
    P.continuousOn_symm.isOpen_inter_preimage P.open_target (P.open_source.preimage hφc)
  refine ⟨ψ ⁻¹' (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)), fun H => P.symm (A * H), hT.preimage hψc, ?_, ?_, ?_, ?_⟩
  · show A * H₀ ∈ P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)
    rw [hAH]
    refine ⟨h1t, ?_⟩
    show φ (P.symm 1) ∈ P.source
    simp only [φ, hS1, Matrix.transpose_one, Matrix.mul_one, hAH]
    exact h1s
  · exact P.continuousOn_symm.comp hψc.continuousOn (fun H hH => hH.1)
  · show P.symm (A * H₀) = 1
    rw [hAH, hS1]
  · intro H hH hHs
    obtain ⟨hX, hφS⟩ := hH
    set S := P.symm (A * H) with hSdef
    have hSs : S ∈ P.source := P.map_target hX
    have hSS : S * S = A * H := by rw [← hPc]; exact P.right_inv hX
    have hφφ : φ S * φ S = S * S := by
      show A * Sᵀ * H₀ * (A * Sᵀ * H₀) = S * S
      have e1 : A * Sᵀ * H₀ * (A * Sᵀ * H₀) = A * (S * S)ᵀ * H₀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul]
      rw [e1, hSS, Matrix.transpose_mul, hAT, hHs.eq, Matrix.mul_assoc, Matrix.mul_assoc, hAH, Matrix.mul_one]
    have heq : φ S = S := P.injOn hφS hSs (by rw [hPc, hPc]; exact hφφ)
    have hcomm : Sᵀ * H₀ = H₀ * S := by
      have : H₀ * (A * Sᵀ * H₀) = H₀ * S := by rw [show A * Sᵀ * H₀ = φ S from rfl, heq]
      rwa [Matrix.mul_assoc, ← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul] at this
    rw [hcomm, Matrix.mul_assoc, hSS, ← Matrix.mul_assoc, hHA, Matrix.one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_of_card_hom_residueField_le : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)] (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ),
  Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ a →
  ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  first | exact @GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | exact GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | (intros; apply GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletionStatement
section
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E) (e : w.adicCompletion E ⊗[E] E'), e * e = e → ψ e = 1 → ∀ (p q : w.adicCompletion E ⊗[E] E') (n : ℕ), ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧ Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) - Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_global_near_idempotent | exact GlobalTheory.exists_global_near_idempotent | (intros; apply GlobalTheory.exists_global_near_idempotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotXPowDvdAdjugateOfFirstOrderKernelStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_not_X_pow_dvd_adjugate_of_first_order_kernel : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1 → a ≠ 0 → ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  first | exact @GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel | exact GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel | (intros; apply GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueAnnihilatorOfNotStandardColumnFormAStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  first | exact @GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | exact GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | (intros; apply GlobalTheory.exists_residue_annihilator_of_not_standard_column_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplexStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex : ∀ {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K) (t : L0 →+* ℂ) (Z : Set K), (∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) → ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧ ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  first | exact @GlobalTheory.adjoin_roots_of_unity_embeds_complex | exact GlobalTheory.adjoin_roots_of_unity_embeds_complex | (intros; apply GlobalTheory.adjoin_roots_of_unity_embeds_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPosStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_integral_differentiable_real_re_pos : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ), Measurable f → Measurable t → (∀ y, 0 ≤ f y) →
    Integrable f ν → (∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) →
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  first | exact @GlobalTheory.exp_integral_entire_real_pos | exact GlobalTheory.exp_integral_entire_real_pos | (intros; apply GlobalTheory.exp_integral_entire_real_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatricesStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ N : ℕ, ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K), ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) → ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.GenUnr.finite_classes_mod_pow | exact GlobalTheory.GenUnr.finite_classes_mod_pow | (intros; apply GlobalTheory.GenUnr.finite_classes_mod_pow <;> assumption)
end

