module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRankAtStalkOfConstFibreDim
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConstFibreFree

theorem finrank_tensor_tower (O k K M : Type) [CommRing O] [Field k] [Field K] [Algebra O k]
    [Algebra O K] [Algebra k K] [IsScalarTower O k K] [AddCommGroup M] [Module O M]
    [Module.Finite O M] :
    Module.finrank K (K ⊗[O] M) = Module.finrank k (k ⊗[O] M) := by
  rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange O k K K M).finrank_eq]
  exact Module.finrank_baseChange

theorem fibreDim_closedPoint (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    fibreDim M (IsLocalRing.closedPoint O) =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] M) := by
  let q := IsLocalRing.closedPoint O
  let φ : IsLocalRing.ResidueField O →+* q.asIdeal.ResidueField :=
    Ideal.Quotient.lift _ (algebraMap O q.asIdeal.ResidueField) fun a ha => by
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]; exact ha
  letI : Algebra (IsLocalRing.ResidueField O) q.asIdeal.ResidueField := φ.toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.Quotient.lift_mk _ _ _).symm
  exact finrank_tensor_tower O _ _ M

theorem exists_one_tmul (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    (y : IsLocalRing.ResidueField O ⊗[O] M) : ∃ m : M, (1 : IsLocalRing.ResidueField O) ⊗ₜ[O] m = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul c m =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a • m, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  | add y z hy hz =>
    obtain ⟨m₁, h₁⟩ := hy
    obtain ⟨m₂, h₂⟩ := hz
    exact ⟨m₁ + m₂, by rw [TensorProduct.tmul_add, h₁, h₂]⟩

theorem nonempty_equiv_fin (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type)
    [AddCommGroup M] [Module O M] [Module.Finite O M] (n : ℕ)
    (h : ∀ q : PrimeSpectrum O, fibreDim M q = n) : Nonempty (M ≃ₗ[O] (Fin n → O)) := by
  let k := IsLocalRing.ResidueField O
  have hk : Module.finrank k (k ⊗[O] M) = n :=
    (fibreDim_closedPoint O M).symm.trans (h _)
  let b : Module.Basis (Fin n) k (k ⊗[O] M) := Module.finBasisOfFinrankEq k _ hk
  choose f hf using fun i => exists_one_tmul O M (b i)
  let g : (Fin n → O) →ₗ[O] M := Fintype.linearCombination O f
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis f b hf
  have hinj : Function.Injective g := by
    let q₀ : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
    let K := q₀.asIdeal.ResidueField
    have hK : Module.finrank K (K ⊗[O] M) = n := h q₀
    let gK := g.baseChange K
    have hgK : Function.Surjective gK := LinearMap.lTensor_surjective K hg
    have hdim : Module.finrank K (K ⊗[O] (Fin n → O)) = Module.finrank K (K ⊗[O] M) := by
      rw [hK, Module.finrank_baseChange, Module.finrank_fin_fun]
    have hgKi : Function.Injective gK :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hgK
    have hO : Function.Injective (algebraMap O K) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : gK ((1 : K) ⊗ₜ x) = 0 := by simp [gK, hx]
    have h2 : (1 : K) ⊗ₜ[O] x = 0 := hgKi (h1.trans (map_zero gK).symm)
    have h3 := congrArg (TensorProduct.piScalarRight O K K (Fin n)) h2
    funext i
    have h4 := congrFun h3 i
    simp at h4
    exact hO (by simpa using h4)
  exact ⟨(LinearEquiv.ofBijective g ⟨hinj, hg⟩).symm⟩

theorem projective_and_rankAtStalk_of_fibreDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
      [Module.Finite O M] (n : ℕ), (∀ q : PrimeSpectrum O, fibreDim M q = n) →
      Module.Projective O M ∧ ∀ q : PrimeSpectrum O, Module.rankAtStalk M q = n := by
  intro O _ _ _ M _ _ _ n h
  obtain ⟨e⟩ := nonempty_equiv_fin O M n h
  haveI : Module.Free O M := Module.Free.of_equiv e.symm
  refine ⟨inferInstance, fun q => ?_⟩
  rw [Module.rankAtStalk_eq]
  exact h q

end GlobalTheory.ConstFibreFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagK

def sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

def fi {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 0 else 1

lemma Jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Jm ε = Matrix.diagonal (fun a => ((sgn ε a : ℝ) : ℂ)) := by
  unfold Jm sgn; congr 1; funext a; split_ifs <;> simp

lemma star_mul_self' (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl

lemma mul_star_self' (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, star_mul_self']

lemma col_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (b : Fin n) :
    ∑ a, sgn ε a * ‖M a b‖ ^ 2 = sgn ε b := by
  have hb := congrFun (congrFun h b) b
  rw [Jm_eq, Matrix.mul_apply] at hb
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at hb
  apply Complex.ofReal_injective
  push_cast
  rw [← hb]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_right_comm, star_mul_self']; push_cast; ring

lemma row_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * Jm ε * Mᴴ = Jm ε) (a : Fin n) :
    ∑ b, sgn ε b * ‖M a b‖ ^ 2 = sgn ε a := by
  have ha := congrFun (congrFun h a) a
  rw [Jm_eq, Matrix.mul_apply] at ha
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at ha
  apply Complex.ofReal_injective
  push_cast
  rw [← ha]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_right_comm, mul_star_self']; push_cast; ring

lemma other_side {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) : M * Jm ε * Mᴴ = Jm ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, hJ]
  have h2 : M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc M * Jm ε * Mᴴ = M * (Jm ε * Mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]

lemma key {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) :
    ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2 = 0 := by
  have h1 : ∑ b, fi ε b * (∑ a, sgn ε a * ‖M a b‖ ^ 2) = ∑ b, fi ε b * sgn ε b := by
    simp only [col_sum ε M h]
  have h2 : ∑ a, fi ε a * (∑ b, sgn ε b * ‖M a b‖ ^ 2) = ∑ a, fi ε a * sgn ε a := by
    simp only [row_sum ε M (other_side ε M h)]
  simp only [Finset.mul_sum] at h1 h2
  rw [Finset.sum_comm] at h1
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ a, ∑ b, fi ε b * sgn ε a * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε b * (sgn ε a * ‖M a b‖ ^ 2) by
      simp only [mul_assoc],
    show (∑ a, ∑ b, fi ε a * sgn ε b * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε a * (sgn ε b * ‖M a b‖ ^ 2) by
      simp only [mul_assoc], h1, h2, sub_self]

lemma offdiag_zero {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0) :
    ∀ a b, ε a = false → ε b = true → M a b = 0 := by
  have hk := key ε M h
  have hs : ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2
      = - ∑ a, ∑ b, (if ε a = false ∧ ε b = true then ‖M a b‖ ^ 2 else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases ha : ε a <;> cases hb : ε b <;> simp [fi, sgn, ha, hb, hTF a b]
  rw [hs, neg_eq_zero] at hk
  intro a b ha hb
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs <;> positivity)).mp hk a (Finset.mem_univ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by
    split_ifs <;> positivity)).mp h0 b (Finset.mem_univ _)
  simp only [ha, hb, and_self, if_true] at h1
  simpa using h1

lemma comm_of {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0)
    (hFT : ∀ a b, ε a = false → ε b = true → M a b = 0) : M * Jm ε = Jm ε * M := by
  ext a b
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases ha : ε a <;> cases hb : ε b <;> simp [sgn, ha, hb, hTF a b, hFT a b]

end GlobalTheory.OffDiagK


open GlobalTheory.OffDiagK in
theorem GlobalTheory.offDiag_zero_iff_mem_K : ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε),
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 = 0 ↔ g ∈ KG ε := by
  intro n ε g
  have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
  rw [Formalism.REAL.mem_KG, Fintype.sum_eq_zero_iff_of_nonneg (fun _ => by positivity)]
  constructor
  · intro h0
    have hTF : ∀ a b, ε a = true → ε b = false → toM g a b = 0 := by
      intro a b ha hb
      have := congrFun h0 ⟨(a, b), ha, hb⟩
      simpa using this
    have hFT := offdiag_zero ε _ hg hTF
    have hc := comm_of ε _ hTF hFT
    refine ⟨?_, hc⟩
    rw [Matrix.mem_unitaryGroup_iff']
    have hJ := Formalism.REAL.Jm_mul_self ε
    calc star (toM g) * toM g = (toM g)ᴴ * (toM g * Jm ε) * Jm ε := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.star_eq_conjTranspose]
      _ = 1 := by rw [hc, ← Matrix.mul_assoc, hg, hJ]
  · rintro ⟨_, hc⟩
    funext z
    obtain ⟨⟨a, b⟩, ha, hb⟩ := z
    simp only at ha hb
    have e := congrFun (congrFun hc a) b
    rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [sgn, ha, hb] at e
    push_cast at e
    have h0 : toM g a b = 0 := by linear_combination (-1/2 : ℂ) * e
    simp [h0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
section
open GlobalTheory.WeilM Matrix

noncomputable section
open Filter
open scoped Topology

namespace GlobalTheory.RankChart

theorem sb_shear_invariant :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D],
      ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k),
        ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ f hf
  obtain ⟨Λ, hΛo, hΛ⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ f hf
  have hK : IsCompact (tsupport f) := hf.2
  have hc : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k =>
      fromRows (0 : Matrix R D k) (p.1 * p.2.toRows₁) := by
    have hm : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => p.1 * p.2.toRows₁ :=
      continuous_fst.matrix_mul (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply (Sum.inl i) j).comp continuous_snd)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simp only [fromRows_apply_inr]
      exact (continuous_apply_apply i j).comp hm
  have hev : ∀ᶠ c in 𝓝 (0 : Matrix T R k), ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ :=
    hK.eventually_forall_of_forall_eventually fun Y _ => by
      have h0 : fromRows (0 : Matrix R D k) ((0 : Matrix T R k) * Y.toRows₁) ∈ Λ := by
        simp
      exact (hc.tendsto ((0 : Matrix T R k), Y)) (hΛo.mem_nhds h0)
  obtain ⟨b, hb⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hev
  refine ⟨b, fun Y c hcb => ?_⟩
  have hZ : ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ := hb c hcb
  by_cases hY : Y ∈ tsupport f
  · rw [← hΛ Y _ (hZ Y hY), ← shear_sub_self, add_sub_cancel]
  by_cases hY' : shear c Y ∈ tsupport f
  · have h1 := hZ _ hY'
    rw [toRows₁_shear, ← shear_sub_self] at h1
    rw [← hΛ (shear c Y) _ (Λ.neg_mem h1), neg_sub, add_sub_cancel]
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']

end GlobalTheory.RankChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
section
open GlobalTheory.WeilM Matrix

namespace GlobalTheory.RankChart

theorem exists_eq_stack (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T]
    [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k)
    (hrank : Y.rank ≤ Fintype.card R) (hdet : (Y.submatrix Sum.inl τ).det ≠ 0) :
    ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  classical
  set Y₁ := Y.toRows₁ with hY₁

  have hA : LinearIndependent k (fun i : R => fun j : R => Y (Sum.inl i) (τ j)) := by
    have hu : IsUnit (Y.submatrix Sum.inl τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    exact Matrix.linearIndependent_rows_of_isUnit hu
  have hli : LinearIndependent k (fun i : R => Y₁ i) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft k k τ)
    exact hA
  have hfin₁ : Module.finrank k (Submodule.span k (Set.range fun i : R => Y₁ i)) = Fintype.card R :=
    finrank_span_eq_card hli
  have hle : Submodule.span k (Set.range fun i : R => Y₁ i) ≤ Submodule.span k (Set.range Y.row) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  have heq : Submodule.span k (Set.range fun i : R => Y₁ i) = Submodule.span k (Set.range Y.row) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hfin₁, ← Matrix.rank_eq_finrank_span_row]
    exact hrank
  have hmem : ∀ t : T, ∃ c : R → k, ∑ i, c i • Y₁ i = Y (Sum.inr t) := by
    intro t
    have : Y (Sum.inr t) ∈ Submodule.span k (Set.range fun i : R => Y₁ i) := by
      rw [heq]; exact Submodule.subset_span ⟨Sum.inr t, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun k).1 this
  choose C hC using hmem
  refine ⟨Matrix.of fun t i => C t i, ?_⟩
  ext (i | t) j
  · simp [stack, hY₁]
  · have := congrFun (hC t) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [stack, fromRows_apply_inr, Matrix.mul_apply, Matrix.of_apply]
    rw [← this]

end GlobalTheory.RankChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqProd
section
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod.UpLatIndex

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ordBall (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (k : ℤ) : AddSubgroup L where
  carrier := {x | (Valued.v x : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-k)}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by simpa using hx

theorem mem_ordBall {k : ℤ} {x : L} : x ∈ ordBall L k ↔ Valued.v x ≤ WithZero.exp (-k) := Iff.rfl

theorem ordBall_mono {k K : ℤ} (h : k ≤ K) : ordBall L K ≤ ordBall L k :=
  fun _ hx => le_trans hx (WithZero.exp_le_exp.2 (neg_le_neg h))

theorem lt_one_iff (a : WithZero (Multiplicative ℤ)) : a < 1 ↔ a ≤ WithZero.exp (-1) := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem relIndex_ordBall_succ {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    (ordBall L (k + 1)).relIndex (ordBall L k) =
      Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ⧸
        IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hp : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := fun m => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  have hle : ∀ (x : L) (a m : ℤ), Valued.v (x * ϖ ^ m) ≤ WithZero.exp (-(a + m)) ↔ Valued.v x ≤ WithZero.exp (-a) :=
    fun x a m => by
      rw [map_mul, hp, neg_add, WithZero.exp_add]
      exact mul_le_mul_iff_left₀ (zero_lt_iff.2 WithZero.exp_ne_zero)
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hm : ∀ x : ordBall L k, x.1 * ϖ ^ (-k) ∈ O := fun x => by
    have := (hle x.1 k (-k)).2 x.2
    rw [add_neg_cancel, neg_zero, WithZero.exp_zero] at this
    exact this
  let g : ordBall L k →+ O :=
    { toFun := fun x => ⟨x.1 * ϖ ^ (-k), hm x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul] }
  let f : ordBall L k →+ O ⧸ IsLocalRing.maximalIdeal O :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).toAddMonoidHom.comp g
  have hf : Function.Surjective f := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y.1 * ϖ ^ k ∈ ordBall L k := by
      have := (hle y.1 0 k).2 (by rw [neg_zero, WithZero.exp_zero]; exact y.2)
      simpa [mem_ordBall] using this
    refine ⟨⟨_, hy⟩, ?_⟩
    change Ideal.Quotient.mk _ (g ⟨_, hy⟩) = _
    congr 1
    ext
    change y.1 * ϖ ^ k * ϖ ^ (-k) = y.1
    rw [mul_assoc, ← zpow_add₀ h0]; simp
  have hc : (ordBall L (k + 1)).addSubgroupOf (ordBall L k) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    change _ ↔ Ideal.Quotient.mk _ (g x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff, lt_one_iff, mem_ordBall,
      ← hle x.1 (k + 1) (-k)]
    have : -(k + 1 + -k) = -1 := by ring
    rw [this]; rfl
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top]

theorem relIndex_ordBall {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {k K : ℤ} (hk : k ≤ K) :
    (ordBall L K).relIndex (ordBall L k) = (q ^ 2) ^ (K - k).toNat := by
  obtain ⟨-, -, -, hϖ, -, -, hq⟩ := h
  obtain ⟨m, rfl⟩ := Int.le.dest hk
  have e : ∀ m : ℕ, (k + m - k).toNat = m := fun m => by omega
  rw [e]
  clear hk
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (ordBall L (k + m + 1)).relIndex (ordBall L (k + m)) = q ^ 2 :=
      (relIndex_ordBall_succ hϖ (k + m)).trans hq
    have h2 := AddSubgroup.relIndex_mul_relIndex (ordBall L (k + m + 1)) (ordBall L (k + m)) (ordBall L k)
      (ordBall_mono (by omega)) (ordBall_mono (by omega))
    rw [Nat.cast_succ, ← add_assoc, ← h2, h1, ih, pow_succ' (q ^ 2)]

theorem relIndex_upLat_eq_prod {n : ℕ} (c C : Fin n → Fin n → ℤ) :
    (upLat L C).relIndex (upLat L c) =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (ordBall L (C p.1.1 p.1.2)).relIndex (ordBall L (c p.1.1 p.1.2)) := by
  let f : upLat L c →+ (∀ p : {p : Fin n × Fin n // p.1 < p.2}, ordBall L (c p.1.1 p.1.2) ⧸
      (ordBall L (C p.1.1 p.1.2)).addSubgroupOf (ordBall L (c p.1.1 p.1.2))) :=
    { toFun := fun x p => QuotientAddGroup.mk ⟨x.1 p.1.1 p.1.2, x.2.2 _ _ p.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i j => if h : i < j then ((y ⟨(i, j), h⟩).out : L) else 0, fun i j h => dif_neg (not_lt.2 h),
      fun i j h => ?_⟩, funext fun p => ?_⟩
    · simp only [dif_pos h]
      exact (y ⟨(i, j), h⟩).out.2
    · refine Eq.trans ?_ (y p).out_eq
      exact congrArg QuotientAddGroup.mk (Subtype.ext (dif_pos p.2))
  have hc : (upLat L C).addSubgroupOf (upLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_upLat]
    constructor
    · intro h p
      exact (QuotientAddGroup.eq_zero_iff _).2 (h.2 _ _ p.2)
    · intro h
      exact ⟨x.2.1, fun i j e => (QuotientAddGroup.eq_zero_iff _).1 (h ⟨(i, j), e⟩)⟩
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem relIndex_upLat : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (q ^ 2) ^ (C p.1 p.2 - c p.1 p.2).toNat := by
  intro L _ _ ϖ σ q n h c C hc
  rw [relIndex_upLat_eq_prod, Finset.prod_subtype (p := fun p : Fin n × Fin n => p.1 < p.2) _ (by simp)]
  exact Finset.prod_congr rfl fun p _ => relIndex_ordBall h (hc _ _ p.2)

end GlobalTheory.BorelUMod.UpLatIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.KumPic

abbrev twZ (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def dv (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ (twZ q)).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

end GlobalTheory.EtC.KumPic

end
end

