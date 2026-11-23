module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
section
open GlobalTheory.RegSS

namespace GlobalTheory.RegSS

theorem eq_zero_of_trace_mul_eq_zero {F L : Type} [Field F] [CharZero F] [CommRing L]
    [Algebra F L] [Module.Finite F L] [IsReduced L] (x : L)
    (hx : ∀ y : L, Algebra.trace F L (x * y) = 0) : x = 0 := by
  have : IsArtinianRing L := IsArtinianRing.of_finite F L
  have : IsSemisimpleRing L := IsArtinianRing.isSemisimpleRing_of_isReduced L

  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have hem : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hem

  have htr : LinearMap.trace F L (Algebra.lmul F L e) = 0 := by
    rw [← Algebra.trace_apply, ← ha, mul_comm]
    exact hx a
  have hidem : IsIdempotentElem (Algebra.lmul F L e) := he.map (Algebra.lmul F L)
  have h0 : Algebra.lmul F L e = 0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr
  have he0 : e = 0 := by
    have := congrArg (fun f => f 1) h0
    simpa using this
  rw [he0] at hI
  exact Ideal.span_singleton_eq_bot.1 (hI.trans (Ideal.span_singleton_eq_bot.2 rfl))

end GlobalTheory.RegSS

namespace GlobalTheory.RegSS

theorem tracePerfect : TracePerfect := by
  unfold TracePerfect
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _
  have : Module.Finite F L := Module.Finite.trans E L
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have inj : Function.Injective (Algebra.traceForm E L) := by
    intro x y hxy

    have h : ∀ z : L, Algebra.trace F L ((x - y) * z) = 0 := by
      intro z
      have hz := LinearMap.congr_fun hxy z
      rw [Algebra.traceForm_apply, Algebra.traceForm_apply] at hz
      rw [← Algebra.trace_trace (S := E), sub_mul, map_sub, hz, sub_self, map_zero]
    exact sub_eq_zero.1 (eq_zero_of_trace_mul_eq_zero (F := F) _ h)
  let b := Module.Free.chooseBasis E L
  let g : L →ₗ[E] L := b.toDualEquiv.symm.toLinearMap ∘ₗ Algebra.traceForm E L
  have ginj : Function.Injective g := b.toDualEquiv.symm.injective.comp inj
  refine ⟨inj, fun f => ?_⟩
  obtain ⟨x, hx⟩ := (IsArtinian.bijective_of_injective_endomorphism g ginj).2
    (b.toDualEquiv.symm f)
  exact ⟨x, b.toDualEquiv.symm.injective hx⟩

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleCentralizerPointsOfCommutantAdj
section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

private lemma cT_mul_mul_eq_iff_mul_adj_eq_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J g : Matrix n n A} (hJ : IsUnit J.det) :
    cT s g * J * g = J ↔ g * adj s J g = 1 := by
  rw [mul_eq_one_comm, adj]
  constructor
  · intro h
    calc J⁻¹ * cT s g * J * g = J⁻¹ * (cT s g * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have key : J * (J⁻¹ * cT s g * J * g) = J := by rw [h, Matrix.mul_one]
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul] using key

theorem pointsCentraliser_of_commutant_of_adjoint :
    PointsCommutant → PointsAdjoint → PointsCentraliser := by
  intro hC hA F E _ _ _ _ n _ _ σ J γ hreg hAlg hPlus R _ _
  obtain ⟨hinj, hcomm⟩ := hC F E n σ J γ hreg hAlg hPlus R
  refine ⟨hinj, fun u => hA F E n σ J γ hreg R u, fun g => ?_⟩
  have hJ : IsUnit (J.map (inclE (F := F) R)).det := by
    have h := hreg.nondeg.map (inclE (F := F) R)
    rw [RingHom.map_det] at h
    exact h
  have hb : ((bc (inclE (F := F) R) γ : GL n (E ⊗[F] R)) : Matrix n n (E ⊗[F] R)) =
      (γ : Matrix n n E).map (inclE (F := F) R) := rfl
  simp only [centPts, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  unfold UPts UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Units.ext_iff, Units.val_mul, hb]
  rw [cT_mul_mul_eq_iff_mul_adj_eq_one _ hJ]
  constructor
  · rintro ⟨hunit, hc⟩
    have hc' := congrArg Units.val hc.eq
    simp only [Units.val_mul, hb] at hc'
    obtain ⟨u, hu⟩ := (hcomm g).1 hc'
    have h1 : u * lConj σ J (γ : Matrix n n E) R u = 1 := by
      apply hinj
      rw [map_mul, hA F E n σ J γ hreg R u, hu, map_one, hunit]
    exact ⟨Units.mkOfMulEqOne u _ h1, h1, hu⟩
  · rintro ⟨u, hu, hg⟩
    have hu' : (u : LPts σ J (γ : Matrix n n E) R) * lConj σ J (γ : Matrix n n E) R u = 1 := hu
    refine ⟨?_, ?_⟩
    · rw [← hg, ← hA F E n σ J γ hreg R, ← map_mul, hu', map_one]
    · change g * _ = _ * g
      apply Units.ext
      simpa only [Units.val_mul, hb] using (hcomm g).2 ⟨u, hg⟩

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijective
section
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem productMap_bijective_of_involution {F E L : Type} [Field F] [CharZero F] [CommRing E]
    [Algebra F E] [CommRing L] [Algebra F L] (f : E →ₐ[F] L) (τ : L ≃ₐ[F] L)
    (hτ : ∀ l, τ (τ l) = l) (P : Subalgebra F L) (hP : ∀ l, l ∈ P ↔ τ l = l)
    (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1) (h1 : τ (f (b 1)) = - f (b 1))
    (hd : d ≠ 0) (hsq : b 1 * b 1 = algebraMap F E d) :
    Function.Bijective (Algebra.TensorProduct.productMap P.val f) := by
  have hδ : f (b 1) * f (b 1) = algebraMap F L d := by rw [← map_mul, hsq, AlgHom.commutes]
  have hinv : algebraMap F L d⁻¹ * (f (b 1) * f (b 1)) = 1 := by
    rw [hδ, ← map_mul, inv_mul_cancel₀ hd, map_one]
  have h2 : algebraMap F L 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F L) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hval : ∀ a c : P, Algebra.TensorProduct.productMap P.val f (a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1) =
      (a : L) + (c : L) * f (b 1) := fun a c => by
    simp [Algebra.TensorProduct.productMap_apply_tmul]
  constructor
  · have hrep : ∀ x : P ⊗[F] E, ∃ a c : P, x = a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1 := by
      intro x
      induction x with
      | tmul p e =>
        refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
        conv_lhs => rw [← b.sum_repr e, Fin.sum_univ_two, h0]
        rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      | add x y hx hy =>
        obtain ⟨a, c, rfl⟩ := hx
        obtain ⟨a', c', rfl⟩ := hy
        exact ⟨a + a', c + c', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := hrep x
    rw [hval] at hx
    have hx' := congrArg τ hx
    rw [map_add (f := _), map_mul, map_zero, (hP _).1 a.2, (hP _).1 c.2, h1] at hx'
    have ha : (a : L) = 0 := by
      linear_combination (algebraMap F L 2⁻¹) * (hx + hx') - (a : L) * h2
    have hc : (c : L) = 0 := by
      linear_combination (algebraMap F L d⁻¹ * f (b 1)) * (hx - ha) - (c : L) * hinv
    rw [show a = 0 from Subtype.ext ha, show c = 0 from Subtype.ext hc]
    simp
  · intro l
    refine ⟨(⟨algebraMap F L 2⁻¹ * (l + τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] 1 +
      (⟨algebraMap F L 2⁻¹ * algebraMap F L d⁻¹ * f (b 1) * (l - τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] b 1,
      ?_⟩
    · rw [map_mul, map_add (f := _), hτ, AlgEquiv.commutes, add_comm]
    · rw [map_mul, map_mul, map_mul, map_sub, hτ, AlgEquiv.commutes, AlgEquiv.commutes, h1]
      ring
    · rw [hval]
      dsimp only
      linear_combination l * h2 + algebraMap F L 2⁻¹ * (l - τ l) * hinv

theorem plusTensorBijective : PlusTensorBijective := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  obtain ⟨τ, -, hτ, hE, hP⟩ := exists_adjEquiv h hA
  obtain ⟨b, d, h0, h1, hd, hsq⟩ := quad_exists_basis h.quad
  refine productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq
  rw [IsScalarTower.toAlgHom_apply, hE, h1, map_neg]

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
section
noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Columns

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def colMat (c : n → Matrix n n A) (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => (c j *ᵥ v) i

omit [DecidableEq n] in
theorem colMat_mulVec (c : n → Matrix n n A) (v a : n → A) :
    colMat c v *ᵥ a = (∑ j, a j • c j) *ᵥ v := by
  rw [Matrix.sum_mulVec]
  funext i
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp [colMat, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq n] in
theorem colMat_map {B : Type} [CommRing B] (f : A →+* B) (c : n → Matrix n n A) (v : n → A) :
    (colMat c v).map f = colMat (fun j => (c j).map f) (fun i => f (v i)) := by
  ext i j
  simp [colMat, Matrix.mulVec, dotProduct]

theorem eq_sum_of_commute_cols {c : n → Matrix n n A} {v : n → A} (hB : IsUnit (colMat c v))
    (hc : ∀ i j, c i * c j = c j * c i) {N : Matrix n n A} (hN : ∀ j, N * c j = c j * N) :
    ∃ a : n → A, ∑ j, a j • c j = N := by
  obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB (N *ᵥ v)
  refine ⟨a, Matrix.toLin'.injective (LinearMap.ext fun y => ?_)⟩
  obtain ⟨t, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB y
  have ha' : (∑ j, a j • c j) *ᵥ v = N *ᵥ v := by rw [← colMat_mulVec]; exact ha
  have h1 : N * (∑ j, t j • c j) = (∑ j, t j • c j) * N := by
    simp [Finset.mul_sum, Finset.sum_mul, hN]
  have h2 : (∑ j, a j • c j) * (∑ j, t j • c j) = (∑ j, t j • c j) * (∑ j, a j • c j) :=
    Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
      (Commute.smul_left (Commute.smul_right (hc i j) _) _)
  simp only [Matrix.toLin'_apply, colMat_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha']

theorem map_commute_of_mem_genAlg {B : Type} [CommRing B] (f : A →+* B) {M l : Matrix n n A}
    {N : Matrix n n B} (h : N * M.map f = M.map f * N) (hl : l ∈ genAlg M) :
    N * l.map f = l.map f * N := by
  unfold genAlg at hl
  induction hl using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap r =>
    have : (algebraMap A (Matrix n n A) r).map f = f r • (1 : Matrix n n B) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; simp
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add f), Matrix.mul_add, Matrix.add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]

end Columns

theorem exists_sum_basis_tmul {F P A : Type} [Field F] [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] {n : Type} [Fintype n] (b : Module.Basis n F P)
    (x : P ⊗[F] A) : ∃ a : n → A, ∑ j, b j ⊗ₜ[F] a j = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left b x
  exact ⟨c, by rw [← hc, Finsupp.sum_fintype]; simp⟩

theorem toMat_tmul_eq_smul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (a : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ a) = a • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l a

theorem pointsCommutant : PointsCommutant := by
  intro F E _ _ _ _ n _ _ σ J γ _ hA hP R _ _
  obtain ⟨-, ⟨b⟩, hbij⟩ := hP
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  let c : n → Matrix n n E := fun j => ((b j : genAlg (γ : Matrix n n E)) : Matrix n n E)
  have hB : IsUnit (colMat c v) := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 fun y => ?_
    obtain ⟨l, rfl⟩ := hv.2 y
    obtain ⟨x, rfl⟩ := hbij.2 l
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b x
    refine ⟨a, ?_⟩
    rw [colMat_mulVec]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
    exact Algebra.smul_def (a j) (c j)
  let f : E →+* E ⊗[F] R := inclE (F := F) R
  have hB' : IsUnit (colMat (fun j => (c j).map f) (fun i => f (v i))) := by
    rw [← colMat_map]; exact hB.map f.mapMatrix
  have hsum : ∀ a : n → E ⊗[F] R, toMat σ J (γ : Matrix n n E) R (∑ j, b j ⊗ₜ[F] a j) =
      ∑ j, a j • (c j).map f := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_congr rfl fun j _ => toMat_tmul_eq_smul _ _ _ _ _ _
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum] at hu
    have : a = 0 := Matrix.mulVec_injective_of_isUnit hB'
      (by rw [colMat_mulVec, hu, Matrix.zero_mulVec, Matrix.mulVec_zero])
    simp [this]
  · obtain ⟨a, ha⟩ := eq_sum_of_commute_cols hB' (fun i j => by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E).map f)
        (mul_comm (b i : genAlg (γ : Matrix n n E)) (b j)))
      (fun j => map_commute_of_mem_genAlg f hN (b j : genAlg (γ : Matrix n n E)).2)
    exact ⟨_, (hsum a).trans ha⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum]
    refine Commute.sum_left _ _ _ fun j _ => Commute.smul_left ?_ _
    exact (map_commute_of_mem_genAlg f rfl (b j : genAlg (γ : Matrix n n E)).2).symm

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExist
section
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem exists_sq_of_not_isField_tensor {F E K : Type} [Field F] [CommRing E] [Algebra F E]
    [Field K] [Algebra F K] (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1)
    (h1 : b 1 * b 1 = algebraMap F E d) (h : ¬ IsField (K ⊗[F] E)) :
    ∃ c : K, c * c = algebraMap F K d := by
  by_contra hc
  push_neg at hc
  apply h
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = 1 := by simp [B, h0, Algebra.TensorProduct.one_def]
  have hB1 : B 1 * B 1 = algebraMap F K d • (1 : K ⊗[F] E) := by
    simp only [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1,
      mul_one, algebraMap_smul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]
  refine ⟨⟨0, 1, ?_⟩, mul_comm, fun {x} hx => ?_⟩
  · rw [← hB0]; exact (B.ne_zero 0).symm
  · have hs := B.sum_repr x
    rw [Fin.sum_univ_two, hB0] at hs
    set s := B.repr x 0
    set t := B.repr x 1
    have hn : s * s - algebraMap F K d * (t * t) ≠ 0 := by
      intro hn
      by_cases ht : t = 0
      · have hs0 : s = 0 := by simpa [ht] using hn
        exact hx (by rw [← hs, hs0, ht]; simp)
      · refine hc (s / t) ?_
        field_simp
        linear_combination hn
    refine ⟨(s * s - algebraMap F K d * (t * t))⁻¹ • (s • (1 : K ⊗[F] E) - t • B 1), ?_⟩
    have : x * (s • (1 : K ⊗[F] E) - t • B 1) =
        (s * s - algebraMap F K d * (t * t)) • (1 : K ⊗[F] E) := by
      rw [← hs]
      simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hB1, one_mul, mul_one]
      module
    rw [mul_smul_comm, this, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem splitIdempotents : SplitIdempotents := by
  intro F E _ _ _ _ σ hσ P _ _ k K _ _ ⟨e⟩
  classical
  obtain ⟨b, d, h0, hb, hd, h1⟩ := quad_exists_basis hσ
  have hc : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∃ c : K i, c * c * algebraMap F _ d = 1 := by
    intro i
    obtain ⟨c, hc⟩ := exists_sq_of_not_isField_tensor b d h0 h1 i.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hd ((algebraMap F (K i)).injective (by simpa using hc.symm))
    exact ⟨c⁻¹, by rw [← hc]; field_simp⟩
  choose c hc using hc
  let u : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 1)
  let v : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 (c i))
  have same : ∀ (i : Fin k) (x y : K i), e.symm (Pi.single i x) * e.symm (Pi.single i y) =
      e.symm (Pi.single i (x * y)) := fun i x y => by rw [← map_mul, Pi.single_mul]
  have diff : ∀ (i j : Fin k) (x : K i) (y : K j), i ≠ j →
      e.symm (Pi.single i x) * e.symm (Pi.single j y) = 0 := fun i j x y hij => by
    rw [← map_mul, ← map_zero e.symm]
    congr 1
    ext l
    by_cases hl : l = i
    · subst hl; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hl]
  have hUU : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (u i ⊗ₜ[F] (1 : E)) = u i ⊗ₜ[F] (1 : E) := fun i => by
    simp [u, same]
  have hUV : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (v i ⊗ₜ[F] b 1) = v i ⊗ₜ[F] b 1 := fun i => by
    simp [u, v, same]
  have hVV : ∀ i, (v i ⊗ₜ[F] b 1) * (v i ⊗ₜ[F] b 1) = u i ⊗ₜ[F] (1 : E) := fun i => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h1, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    simp only [u, v, same]
    rw [← map_smul, ← Pi.single_smul, Algebra.smul_def, mul_comm, hc]
  have hconj : ∀ j, tConj P σ ((2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) + v j ⊗ₜ[F] b 1)) =
      (2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) - v j ⊗ₜ[F] b 1) := fun j => by
    simp [tConj, hb, TensorProduct.tmul_neg, sub_eq_add_neg]
  refine ⟨fun i => (2⁻¹ : F) • (u i ⊗ₜ[F] (1 : E) + v i ⊗ₜ[F] b 1), fun i hi => ?_, fun i => ?_,
    fun i j hij => ?_, fun i j => ?_⟩
  · have hi' : u i ⊗ₜ[F] (b 0) + v i ⊗ₜ[F] b 1 = 0 := by
      rw [h0]; exact (smul_eq_zero.1 hi).resolve_left (inv_ne_zero two_ne_zero)
    have h2 := congrArg (fun x => (Algebra.TensorProduct.basis P b).repr x 0) hi'
    simp only [map_add (f := _), Finsupp.add_apply, Algebra.TensorProduct.basis_repr_tmul] at h2
    have h3 : u i = 0 := by simpa using h2
    have h4 := congrFun (e.symm.injective (h3.trans (map_zero e.symm).symm)) i.1
    simp at h4
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hUU, hVV, hUV,
      mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
    module
  · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [add_mul, mul_add, u, v, diff _ _ _ _ hij']
  · rw [hconj]
    by_cases hij : i = j
    · subst hij
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_sub, hUU, hVV, hUV,
        mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
      module
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [add_mul, mul_sub, u, v, diff _ _ _ _ hij']

end GlobalTheory.RegSS
end

