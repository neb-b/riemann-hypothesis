module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem contDiffOn_real_transition (i j : A.ι) :
    ContDiffOn ℝ ∞ (A.e j ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' (A.e j).source) :=
  (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real
    ((A.e i).isOpen_inter_preimage_symm (A.e j).open_source) (differentiableOn_euclidean.1 (A.holo i j) a)

theorem exists_smooth_bump [T2Space M] (x : M) :
    ∃ (i : A.ι) (ψ : M → ℝ), A.SmoothOn univ (fun y => (ψ y : ℂ)) ∧ tsupport ψ ⊆ (A.e i).source ∧
      ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  classical
  obtain ⟨i, hxe⟩ := A.cover x
  set e := A.e i with he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
  let β : ContDiffBump (e x) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e x) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e x) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e x) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun y hy => hcb hy)
  have hCsub : C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcb hy)
  let ψ : M → ℝ := fun w => if w ∈ e.source then β (e w) else 0
  have hsupp : Function.support ψ ⊆ C := by
    intro w hw
    simp only [Function.mem_support, ψ] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e x) (ε / 2) := by
        rw [← β.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport ψ ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨i, ψ, ?_, hts.trans hCsub, ?_⟩
  · intro k
    rw [preimage_univ, inter_univ]
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hys : (A.e k).symm y ∈ e.source
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' e.source,
        (A.e k).isOpen_inter_preimage_symm e.open_source, ⟨hy, hys⟩, ?_⟩
      have hβ : ContDiff ℝ ∞ (fun y : V n => ((β y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp β.contDiff
      refine ((hβ.comp_contDiffOn (A.contDiffOn_real_transition k i)).mono inter_subset_right).congr
        fun v hv => ?_
      have hv1 : (A.e k).symm v ∈ e.source := hv.2.2
      simp only [Function.comp, ψ, if_pos hv1]
      rfl
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' Cᶜ,
        (A.e k).isOpen_inter_preimage_symm hCc.isClosed.isOpen_compl,
        ⟨hy, fun h => hys (hCsub h)⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v hv => ?_
      have : ψ ((A.e k).symm v) = 0 := by
        by_contra h
        exact hv.2.2 (hsupp h)
      simp [Function.comp, this]
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hxe, Set.mem_preimage.mpr (Metric.mem_ball_self (by linarith))⟩] with w hw
    simp only [ψ, if_pos hw.1]
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory

theorem exists_finite_smooth_partition_holAtlas {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ}
    (A : GlobalTheory.CxForm.HolAtlas M n) :
    ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧
      (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  classical
  choose E Ψ hΨs hΨt hΨ1 using A.exists_smooth_bump
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior {y | Ψ x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hΨ1 y)⟩)
  let p : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  let ψ : Fin t.card → M → ℝ := fun i => Ψ (p i)
  have hsum : ∀ x, ∑ i, ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x) =
      1 - ∏ i, (1 - ψ i x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun i => E (p i), fun i x => ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x),
    fun i k => ?_, fun i => (tsupport_mul_subset_left).trans (hΨt (p i)), fun x => ?_⟩
  · refine ((hΨs (p i) k).mul (contDiffOn_prod (t := Finset.univ.filter (· < i))
      fun j _ => (contDiffOn_const (c := (1 : ℂ))).sub (hΨs (p j) k))).congr fun v _ => ?_
    simp [Function.comp, ψ]
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : p (t.equivFin ⟨u, hu⟩) = u := by simp [p]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | Ψ u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHermitianForm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RefForm

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {k : ℕ} (X Y : Matrix (Fin k) (Fin k) A) :
    cT σ (X * Y) = cT σ Y * cT σ X := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT_conj {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) : cT (starRingEnd ℂ) (cT (starRingEnd ℂ) X) = X := by
  ext i j; simp [cT]

theorem det_cT_conj {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) : (cT (starRingEnd ℂ) X).det = starRingEnd ℂ X.det := by
  simp only [cT, Matrix.det_transpose]
  exact ((starRingEnd ℂ).map_det X).symm

theorem cT_diag_mul_diag {k : ℕ} (μ : Fin k → ℂ) (hμ : ∀ r, ‖μ r‖ = 1) :
    cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ = 1 := by
  have : cT (starRingEnd ℂ) (Matrix.diagonal μ) = Matrix.diagonal (fun r => starRingEnd ℂ (μ r)) := by
    ext i j; by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [this, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext r
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ r]; simp

theorem assemble (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ H : Matrix (Fin n) (Fin n) E)
    (h : ∀ τ : E →+* ℂ, ∃ (W : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), W.det ≠ 0 ∧ (∀ r, ‖μ r‖ = 1) ∧
      W * γ.map τ = Matrix.diagonal μ * W ∧ H.map τ = cT (starRingEnd ℂ) W * W) :
    IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ * H * γ = H ∧
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) := by
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hστ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj E τ x
  have hmapcT : ∀ (τ : E →+* ℂ) (X : Matrix (Fin n) (Fin n) E),
      (cT σ X).map τ = cT (starRingEnd ℂ) (X.map τ) := by
    intro τ X; ext i j; simp [cT, hστ]
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) E => X.map τ₀) :=
    Matrix.map_injective τ₀.injective
  obtain ⟨W, μ, hW, hμ, hWγ, hH⟩ := h τ₀
  refine ⟨?_, ?_, ?_, fun τ => ?_⟩
  · apply hinj
    change (cT σ H).map τ₀ = H.map τ₀
    rw [hmapcT, hH, cT_mul, cT_cT_conj]
  · intro h0
    have : τ₀ H.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hH, Matrix.det_mul, det_cT_conj] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hW (by simpa using h1)
    · exact hW h1
  · apply hinj
    change (cT σ γ * H * γ).map τ₀ = H.map τ₀
    rw [Matrix.map_mul, Matrix.map_mul, hmapcT, hH]
    calc cT (starRingEnd ℂ) (γ.map τ₀) * (cT (starRingEnd ℂ) W * W) * γ.map τ₀
        = cT (starRingEnd ℂ) (W * γ.map τ₀) * (W * γ.map τ₀) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd ℂ) W * (cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ) * W := by
          rw [hWγ, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd ℂ) W * W := by rw [cT_diag_mul_diag μ hμ, Matrix.mul_one]
  · obtain ⟨W, μ, hW, -, -, hH⟩ := h τ
    exact ⟨W, hW, hH⟩

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

theorem exists_roots_enum (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) :
    ∃ μ : Fin n → ℂ, Function.Injective μ ∧ (∀ r, ‖μ r‖ = 1) ∧ ∀ r, P.eval₂ τ (μ r) = 0 := by
  obtain ⟨hm, hn, hs, hr⟩ := hP
  set s := (P.map τ).roots
  have hnd : s.Nodup := nodup_roots (hs.map)
  have hcard : s.card = n := by
    rw [← hn, ← Polynomial.natDegree_map τ]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hc : s.toFinset.card = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e : Fin n ≃ s.toFinset := (finCongr hc.symm).trans s.toFinset.equivFin.symm
  refine ⟨fun r => ((e r) : ℂ), Subtype.val_injective.comp e.injective, fun r => hr τ _ ?_, fun r => ?_⟩
  · exact Multiset.mem_toFinset.mp (e r).2
  · have hmem : ((e r) : ℂ) ∈ s := Multiset.mem_toFinset.mp (e r).2
    rw [← Polynomial.eval_map]
    exact (mem_roots (hm.map τ).ne_zero).mp hmem

noncomputable def powBasis {E : Type} [Field E] (P : E[X]) (hm : P.Monic) :
    Module.Basis (Fin P.natDegree) E (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis hm.ne_zero).basis.reindex (finCongr (AdjoinRoot.powerBasis_dim hm.ne_zero))

theorem powBasis_apply {E : Type} [Field E] (P : E[X]) (hm : P.Monic) (i : Fin P.natDegree) :
    powBasis P hm i = AdjoinRoot.root P ^ (i : ℕ) := by
  simp [powBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]

noncomputable def compMat {E : Type} [Field E] (P : E[X]) (hm : P.Monic) :
    Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
  Algebra.leftMulMatrix (powBasis P hm) (AdjoinRoot.root P)

theorem vandermonde_mul_compMat (E : Type) [Field E] (P : E[X]) (hm : P.Monic) (τ : E →+* ℂ)
    (μ : Fin P.natDegree → ℂ) (hμ : ∀ r, P.eval₂ τ (μ r) = 0) :
    Matrix.vandermonde μ * (compMat P hm).map τ = Matrix.diagonal μ * Matrix.vandermonde μ := by
  ext r j
  let φ : AdjoinRoot P →+* ℂ := AdjoinRoot.lift τ (μ r) (hμ r)
  have hφ : ∀ a : AdjoinRoot P, φ a = ∑ i, τ ((powBasis P hm).repr a i) * μ r ^ (i : ℕ) := by
    intro a
    conv_lhs => rw [← (powBasis P hm).sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, powBasis_apply, map_pow]
    simp [φ, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have key := hφ (AdjoinRoot.root P * powBasis P hm j)
  rw [map_mul, powBasis_apply, map_pow] at key
  simp only [φ, AdjoinRoot.lift_root] at key
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.map_apply,
    compMat, Algebra.leftMulMatrix_eq_repr_mul, powBasis_apply]
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem charpoly_compMat {E : Type} [Field E] (P : E[X]) (hm : P.Monic) : (compMat P hm).charpoly = P := by
  haveI : Module.Finite E (AdjoinRoot P) := Module.Finite.of_basis (powBasis P hm)
  have h1 : (compMat P hm).charpoly = (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly :=
    LinearMap.charpoly_toMatrix _ _
  have h2 : (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero).basis (AdjoinRoot.root P)).charpoly =
      (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly :=
    LinearMap.charpoly_toMatrix _ _
  rw [h1, ← h2]
  have := (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)
  simpa [AdjoinRoot.powerBasis_gen] using this

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

theorem trace_semiconj {k : ℕ} (W T T' : Matrix (Fin k) (Fin k) ℂ) (μ : Fin k → ℂ) (hμ0 : ∀ r, μ r ≠ 0)
    (hW : W.det ≠ 0) (hWT : W * T = Matrix.diagonal μ * W) (hTT' : T * T' = 1) (i j : ℕ) :
    (T' ^ i * T ^ j).trace = ∑ r, (μ r)⁻¹ ^ i * μ r ^ j := by
  have hinv : Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext r; exact inv_mul_cancel₀ (hμ0 r)
  have hWT' : W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by
    calc W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ * W * T' := by
          rw [hinv, Matrix.one_mul]
      _ = Matrix.diagonal (fun r => (μ r)⁻¹) * (W * T) * T' := by
          rw [hWT, Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal μ) W]
      _ = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hTT', Matrix.mul_one]
  have h1 : SemiconjBy W T' (Matrix.diagonal fun r => (μ r)⁻¹) := hWT'
  have h2 : SemiconjBy W T (Matrix.diagonal μ) := hWT
  have hs := (h1.pow_right i).mul_right (h2.pow_right j)
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal] at hs
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr hW
  have hM : T' ^ i * T ^ j = W⁻¹ * (Matrix.diagonal (fun r => ((fun r => (μ r)⁻¹) ^ i) r * (μ ^ j) r) * W) := by
    rw [← hs.eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [hM, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    Matrix.trace_diagonal]
  simp

theorem exists_model (E : Type) [Field E] [NumberField E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) :
    ∃ (N : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E), N.val.charpoly = P ∧
      ∀ τ : E →+* ℂ, ∃ (W : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), W.det ≠ 0 ∧ (∀ r, ‖μ r‖ = 1) ∧
        W * N.val.map τ = Matrix.diagonal μ * W ∧ H.map τ = cT (starRingEnd ℂ) W * W := by
  have hP' := hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  subst hn
  have h0 : P.coeff 0 ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  have hd : IsUnit (compMat P hm).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_compMat]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  set N : GL (Fin P.natDegree) E := ((Matrix.isUnit_iff_isUnit_det _).mpr hd).unit with hNdef
  have hNval : N.val = compMat P hm := IsUnit.unit_spec _
  refine ⟨N, Matrix.of fun i j => ((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).trace, by rw [hNval, charpoly_compMat],
    fun τ => ?_⟩
  obtain ⟨μ, hμi, hμ1, hμr⟩ := exists_roots_enum E _ P hP' τ
  have hμ0 : ∀ r, μ r ≠ 0 := fun r h => by simpa [h] using hμ1 r
  have hW : (Matrix.vandermonde μ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hμi
  have hWT : Matrix.vandermonde μ * N.val.map τ = Matrix.diagonal μ * Matrix.vandermonde μ := by
    rw [hNval]; exact vandermonde_mul_compMat E P hm τ μ hμr
  have hTT' : N.val.map τ * (N⁻¹).val.map τ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]
  refine ⟨Matrix.vandermonde μ, μ, hW, hμ1, hWT, ?_⟩
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, AddMonoidHom.map_trace τ]
  have hmap : (((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).map τ) =
      ((N⁻¹).val.map τ) ^ (i : ℕ) * (N.val.map τ) ^ (j : ℕ) := by
    simp only [← RingHom.mapMatrix_apply, map_mul, map_pow]
  rw [hmap, trace_semiconj _ _ _ μ hμ0 hW hWT hTT']
  simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_pow, Complex.inv_eq_conj (hμ1 r)]

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

theorem map_cT_complexConj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ)
    (X : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom X).map τ = cT (starRingEnd ℂ) (X.map τ) := by
  ext i j; simp [cT, IsCMField.complexEmbedding_complexConj E τ]

theorem exists_refForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∃ H₀ : Matrix (Fin n) (Fin n) E,
      IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ ∧ H₀.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ ∧
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) := by
  intro E _ _ _ n γ₀ hP
  obtain ⟨N, H, hNc, hmod⟩ := exists_model E n _ hP
  obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable E n N γ₀ hNc (hNc ▸ hP.2.2.1)
  refine ⟨cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * H * h.val,
    assemble E n γ₀.val _ fun τ => ?_⟩
  obtain ⟨W, μ, hW, hμ1, hWN, hH⟩ := hmod τ
  have hinv1 : h.val.map τ * (h⁻¹).val.map τ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hdh : (h.val.map τ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hinv1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨W * h.val.map τ, μ, by rw [Matrix.det_mul]; exact mul_ne_zero hW hdh, hμ1, ?_, ?_⟩
  · rw [hh, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    calc W * h.val.map τ * ((h⁻¹).val.map τ * N.val.map τ * h.val.map τ)
        = W * (h.val.map τ * (h⁻¹).val.map τ) * N.val.map τ * h.val.map τ := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal μ * (W * h.val.map τ) := by
          rw [hinv1, Matrix.mul_one, hWN, Matrix.mul_assoc]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT_complexConj, hH, cT_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.RefForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotients
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotGlue

theorem exists_glueMap (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j)
    (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G)
    (hb : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left)
    (hψ : ∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) (hψF : ∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) :
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  let qL : ∀ j, pullback A.hom (𝒰.f j) ⟶ (B j).left := fun j => (q j).left
  have hq : ∀ j, qL j ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := fun j => Over.w (q j)
  have hb' : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
      (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
      w ≫ pullback.fst _ _ = y ≫ qL j → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ qL k := hb
  have key : ∀ j k, pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j ≫ ψ j =
      pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL k ≫ ψ k := by
    intro j k
    have e : pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f j) =
        pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f k) :=
      pullback.condition
    have hw : (pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j) ≫ ((B j).hom ≫ 𝒰.f j) =
        (pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.snd A.hom (𝒰.f k)) ≫ 𝒰.f k := by
      rw [Category.assoc, reassoc_of% (hq j), ← pullback.condition, ← Category.assoc, e,
        Category.assoc, Category.assoc, pullback.condition]
    have h1 := hb' j k _ _ _ (pullback.lift _ _ hw) e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [← Category.assoc, ← pullback.lift_fst _ _ hw, Category.assoc, hψ, ← Category.assoc, h1, Category.assoc]
  have hc : ∀ j k, pullback.fst ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL j ≫ ψ j) =
      pullback.snd ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL k ≫ ψ k) := key
  have hι : ∀ j, pullback.fst A.hom (𝒰.f j) ≫ Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc =
      qL j ≫ ψ j := fun j => Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc j
  refine ⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc, ?_, fun j => (hι j).symm⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ A.hom) _ _ fun (j : 𝒰.I₀) => ?_
  show pullback.fst A.hom (𝒰.f j) ≫ _ ≫ F = pullback.fst A.hom (𝒰.f j) ≫ A.hom
  rw [reassoc_of% (hι j), hψF, reassoc_of% (hq j), pullback.condition]

end GlobalTheory.QuotGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealFactorIff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem exists_ideal_factor_iff {X Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y)
    (x₀ : X) :
    ∃ J : Ideal (X.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : X.presheaf.stalk x₀ →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z,
        z ≫ i = (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x₀) ≫ f) ↔
        J ≤ RingHom.ker ψ := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd i (X.fromSpecStalk x₀ ≫ f))).1
    inferInstance
  refine ⟨I, fun R' _ ψ => ?_⟩
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ : ∃ w : Spec (CommRingCat.of R') ⟶ pullback i (X.fromSpecStalk x₀ ≫ f),
        w ≫ pullback.fst i (X.fromSpecStalk x₀ ≫ f) = z ∧
          w ≫ pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) :=
      ⟨pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) (hz.trans (Category.assoc _ _ _)),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [he, ← Category.assoc] at hw
    set w' := w ≫ e.hom
    have h3 : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage w' = CommRingCat.ofHom ψ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hw
    intro a ha
    rw [RingHom.mem_ker]
    have h4 := congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at h4
    exact h4.symm
  · intro hI
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
      pullback.fst i (X.fromSpecStalk x₀ ≫ f), ?_⟩
    have key : Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
        pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [he, e.inv_hom_id_assoc, ← Spec.map_comp]
      congr 1
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% key]

end GlobalTheory.KerIdeal

namespace GlobalTheory.KerIdeal

theorem kernel_ideal : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B), IsAbelianScheme B → ∀ x₀ : A.left,
    ∃ J : Ideal (A.left.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ := by
  intro k _ A B _ π _ x₀
  haveI : IsClosedImmersion (η[B]).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) B.hom _ (Over.w _)
  exact exists_ideal_factor_iff (η[B]).left π.left x₀

end GlobalTheory.KerIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [Fintype β] (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ M : InfinitePlace F → Matrix α β ℂ, ∃! u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = M w := by
  first | exact @GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf | exact GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf | (intros; apply GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf <;> assumption)
end

