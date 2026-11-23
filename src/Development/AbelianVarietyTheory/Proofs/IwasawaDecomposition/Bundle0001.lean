module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquiv
section
open IsLocalRing

namespace GlobalTheory.AdicQuot

open AdicCompletion

variable {A : Type} [CommRing A] (J q : Ideal A)

theorem mem_smul_top_iff (n : ℕ) (b : A ⧸ q) :
    b ∈ (J ^ n • ⊤ : Submodule A (A ⧸ q)) ↔ b ∈ (J.map (Ideal.Quotient.mk q)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  rfl

theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (Ideal.Quotient.mk q)) ^ n).comap (Ideal.Quotient.mk q) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* (A ⧸ q) ⧸ (J.map (Ideal.Quotient.mk q)) ^ n :=
  (Ideal.quotientMap _ (Ideal.Quotient.mk q) (pow_le_comap J q n)).comp (evalₐ J n).toRingHom

theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (Ideal.Quotient.mk q (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev J q n) = lev J q m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap J q m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
  AdicCompletion.liftRingHom _ (lev J q) (fun hle ↦ lev_compat J q hle)

theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi J q x) = lev J q n x := by
  simp [psi]

theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : A ⧸ q) :
    (map J (Submodule.mkQ q) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

theorem ker_psi [IsNoetherianRing A] :
    RingHom.ker (psi J q) = q.map (algebraMap A (AdicCompletion J A)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Submodule.mkQ q) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff J q s n 0).mpr (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := q.mkQ)
      Subtype.val_injective (LinearMap.exact_subtype_mkQ q) (Submodule.mkQ_surjective q)) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_psi, _root_.map_zero, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, _root_.map_zero]

theorem psi_surjective [IsNoetherianRing A] : Function.Surjective (psi J q) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J (A ⧸ q) := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (Submodule.mkQ_surjective q) (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff J q s n (t n)).mp ?_
  rw [hx]; rfl

end GlobalTheory.AdicQuot

theorem GlobalTheory.adicCompletion_quotient_ringEquiv :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A),
      Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+*
        AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  intro A _ _ J q
  exact ⟨(Ideal.quotEquivOfEq (GlobalTheory.AdicQuot.ker_psi J q).symm).trans
    (RingHom.quotientKerEquivOfSurjective (GlobalTheory.AdicQuot.psi_surjective J q))⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalTotalDegreeLe
section
universe u_1
namespace GlobalTheory.AevalTotalDegreeBound
open MvPolynomial

theorem aeval_totalDegree_le {σ : Type u_1} (f : σ → MvPolynomial σ ℂ)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (P : MvPolynomial σ ℂ) :
    (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem main : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => aeval_totalDegree_le f hf P

end GlobalTheory.AevalTotalDegreeBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
section
noncomputable section

namespace GlobalTheory.NormalDescent

open Polynomial TensorProduct

variable {A B : Type} [CommRing A] [CommRing B]

def charK (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) : K[X] :=
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly

def normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ) : A :=
  letI := Classical.propDecidable
  if h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k then
    h.choose else 0

theorem algebraMap_normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ)
    (h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k) :
    algebraMap A (FractionRing A) (normCoeff φ hφ b k) = (charK φ hφ (FractionRing A) b).reverse.coeff k := by
  classical
  unfold normCoeff
  rw [dite_eq_left h]
  exact h.choose_spec

theorem charK_monic (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) :
    (charK φ hφ K b).Monic := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  exact LinearMap.charpoly_monic _

end GlobalTheory.NormalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapToZModEq
section
namespace GlobalTheory.AlgebraMapToZMod

theorem algebraMap_toZMod_eq {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type} [inst_1 : Field R]
    [inst_2 : Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  have h := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  set z : ZMod l := PadicInt.toZMod x with hz
  have hc : (ZMod.cast z : ℤ_[l]) = ((z.val : ℕ) : ℤ_[l]) := (ZMod.natCast_val z).symm
  have hx : x = y * (l : ℤ_[l]) + ((z.val : ℕ) : ℤ_[l]) := by
    rw [hy, hc]; ring
  have h1 : f x = ((z.val : ℕ) : R) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, hf, mul_zero, zero_add, map_natCast]
  have h2 : algebraMap (ZMod l) R z = ((z.val : ℕ) : R) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [h1, h2]

end GlobalTheory.AlgebraMapToZMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeInfLatticeEqSubspace
section
open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_inf_lattice_eq_subspace : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  intro O V _ _ _ _ _ _ N hN W
  set K := FractionRing O
  have hV : IsBaseChange K (LinearMap.id : V →ₗ[O] V) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).1
      (isLocalizedModule_id (nonZeroDivisors O) V K)
  have hVt : ∀ (c : K) (v : V), hV.equiv (c ⊗ₜ[O] v) = c • v := fun c v => by
    rw [IsBaseChange.equiv_tmul]; rfl

  let fN : K ⊗[O] N →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N.subtype.baseChange K
  have hfN : ∀ y : N, fN (1 ⊗ₜ y) = y := fun y => by simp [fN, hVt]
  have hinjN : Function.Injective fN := hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N.subtype N.injective_subtype)
  have hsurjN : Function.Surjective fN := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hN, Submodule.span_le]
    exact fun y hy => ⟨1 ⊗ₜ ⟨y, hy⟩, hfN _⟩
  have hbN : IsBaseChange K N.subtype :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective fN ⟨hinjN, hsurjN⟩) (fun y => hfN y)
  haveI hlN : IsLocalizedModule (nonZeroDivisors O) N.subtype :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K N.subtype).2 hbN

  set N' := N ⊓ W.restrictScalars O
  let e : K ⊗[O] N' →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N'.subtype.baseChange K
  have het : ∀ (c : K) (x : N'), e (c ⊗ₜ[O] x) = c • (x : V) := fun c x => by
    simp [e, hVt]
  refine ⟨e, hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N'.subtype N'.injective_subtype), ?_, het⟩
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [het]; exact W.smul_mem c x.2.2
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
  · intro v hv
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalizedModule.surj (nonZeroDivisors O) N.subtype v
    have hdv : (d : O) • v = (n : V) := hd
    have hdK : (d : O) • v = algebraMap O K d • v := (algebraMap_smul K (d : O) v).symm
    have hW : (n : V) ∈ W := by rw [← hdv, hdK]; exact W.smul_mem _ hv
    have hne : algebraMap O K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    refine ⟨(algebraMap O K d)⁻¹ ⊗ₜ[O] (⟨n, n.2, hW⟩ : N'), ?_⟩
    rw [het]
    show (algebraMap O K d)⁻¹ • (n : V) = v
    rw [← hdv, hdK, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
section
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DomainDens

def blockSym {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q,
    X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b))

theorem blockSym_apply {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)
    (i j : Fin p) : blockSym h τ i j =
      ∑ b : Fin q, X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b)) := rfl

end GlobalTheory.DomainDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperOfGenericCharacter
section
namespace GlobalTheory
namespace GenericCharBlock

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mul_rankOne (Q : Matrix ι ι K) (q a b : K) (hQ : Q * Q = q • Q) :
    (1 + a • Q) * (1 + b • Q) = 1 + (a + b + a * b * q) • Q := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hQ, smul_smul, add_smul, smul_add]
  module

noncomputable def rankOneUnit (Q : Matrix ι ι K) (q μ : K) (hQ : Q * Q = q • Q)
    (hμ : 1 + μ * q ≠ 0) : GL ι K where
  val := 1 + μ • Q
  inv := 1 + (-μ / (1 + μ * q)) • Q
  val_inv := by
    rw [mul_rankOne Q q _ _ hQ]
    have : μ + -μ / (1 + μ * q) + μ * (-μ / (1 + μ * q)) * q = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]
  inv_val := by
    rw [mul_rankOne Q q _ _ hQ]
    have : -μ / (1 + μ * q) + μ + -μ / (1 + μ * q) * μ * q = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]

theorem rankOneUnit_val (Q : Matrix ι ι K) (q μ : K) (hQ : Q * Q = q • Q)
    (hμ : 1 + μ * q ≠ 0) : (rankOneUnit Q q μ hQ hμ).val = 1 + μ • Q := rfl

noncomputable def unip (Q : Matrix ι ι K) (h : Q * Q = 0) (y : K) : GL ι K :=
  rankOneUnit Q 0 y (by rw [h, zero_smul]) (by simp)

theorem unip_val (Q : Matrix ι ι K) (h : Q * Q = 0) (y : K) :
    (unip Q h y).val = 1 + y • Q := rfl

noncomputable def diagUnit (f : ι → K) (hf : ∀ a, f a ≠ 0) : GL ι K where
  val := diagonal f
  inv := diagonal fun a => (f a)⁻¹
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact mul_inv_cancel₀ (hf a)
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact inv_mul_cancel₀ (hf a)

theorem diagUnit_val (f : ι → K) (hf : ∀ a, f a ≠ 0) : (diagUnit f hf).val = diagonal f := rfl

theorem conj_one_add (B Bi X : Matrix ι ι K) (h : B * Bi = 1) (y : K) :
    B * (1 + y • X) * Bi = 1 + y • (B * X * Bi) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mul_conj (B Bi X Y : Matrix ι ι K) (h : Bi * B = 1) :
    (B * X * Bi) * (B * Y * Bi) = B * (X * Y) * Bi := by
  calc (B * X * Bi) * (B * Y * Bi) = B * X * (Bi * B) * Y * Bi := by simp only [Matrix.mul_assoc]
    _ = B * (X * Y) * Bi := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem single_eq_smul (i j : ι) (x : K) : single i j x = x • single i j (1 : K) := by
  rw [smul_single, smul_eq_mul, mul_one]

theorem chi_trivial_of_scaled {A : Type} [CommGroup A] (H : Subgroup (GL ι K)) (χ : H →* A)
    (P : Matrix ι ι K) (hP : P * P = 0)
    (hmem : ∀ y : K, ∃ g : GL ι K, g ∈ H ∧ g.val = 1 + y • P)
    (s : GL ι K) (hs : s ∈ H) (l : K) (hl : l ≠ 1) (hsc : s.val * P = l • (P * s.val))
    (g : GL ι K) (hg : g ∈ H) (y : K) (hgy : g.val = 1 + y • P) : χ ⟨g, hg⟩ = 1 := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.mpr hl
  obtain ⟨g1, hg1, hv1⟩ := hmem (y / (l - 1))
  have hinv : s.val * (s⁻¹ : GL ι K).val = 1 := s.mul_inv
  have key : s * g1 * s⁻¹ = g1 * g := by
    ext1
    simp only [Units.val_mul]
    rw [hv1, hgy]
    have e1 : s.val * (1 + (y / (l - 1)) • P) * (s⁻¹ : GL ι K).val
        = 1 + (y / (l - 1) * l) • P := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hinv, Matrix.mul_smul, hsc,
        Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hinv, Matrix.mul_one, smul_smul]
    rw [e1, mul_rankOne P 0 _ _ (by rw [hP, zero_smul])]
    congr 2
    field_simp
    ring
  have e : (⟨s, hs⟩ * ⟨g1, hg1⟩ * (⟨s, hs⟩ : H)⁻¹ : H) = ⟨g1, hg1⟩ * ⟨g, hg⟩ := Subtype.ext key
  have h1 : χ ⟨g1, hg1⟩ = χ ⟨g1, hg1⟩ * χ ⟨g, hg⟩ := by
    calc χ ⟨g1, hg1⟩ = χ ⟨s, hs⟩ * χ ⟨g1, hg1⟩ * (χ ⟨s, hs⟩)⁻¹ := by
          rw [mul_comm (χ ⟨s, hs⟩), mul_inv_cancel_right]
      _ = χ (⟨s, hs⟩ * ⟨g1, hg1⟩ * (⟨s, hs⟩ : H)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = χ (⟨g1, hg1⟩ * ⟨g, hg⟩) := by rw [e]
      _ = χ ⟨g1, hg1⟩ * χ ⟨g, hg⟩ := map_mul _ _ _
  exact (mul_eq_left.mp h1.symm)

end GenericCharBlock
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchySliceEqRemovableExtension
section
open Metric Filter Topology Set

namespace GlobalTheory

theorem cauchy_slice_removable_extension :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  intro n U k f z₀ r M hr hz₀ _hU hball hd hM z hz
  set s : ℂ → ℂ := fun t => f (Function.update z k t) with hs_def

  have hupd : Differentiable ℂ (fun t : ℂ => Function.update z k t) :=
    (contDiff_update (𝕜 := ℂ) 1 z k).differentiable (by norm_num)
  have hzdist : ∀ j, ‖z j - z₀ j‖ < r := by
    intro j
    have h1 : dist z z₀ < r := hz
    rw [dist_pi_lt_iff hr] at h1
    simpa [dist_eq_norm] using h1 j
  have hzk : ‖z k‖ < r := by simpa [hz₀] using hzdist k
  have hmem : ∀ t : ℂ, ‖t‖ < 2 * r → Function.update z k t ∈ Metric.ball z₀ (2 * r) := by
    intro t ht
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj
      simpa [dist_eq_norm, hz₀] using ht
    · rw [Function.update_of_ne hj, dist_eq_norm]
      linarith [hzdist j]
  have hsd : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) (2 * r) \ {0}) := by
    refine hd.comp hupd.differentiableOn ?_
    intro t ht
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact ⟨hball (hmem t ht1), by simpa using ht2⟩
  have hsb : BddAbove (norm ∘ s '' (Metric.ball (0 : ℂ) (2 * r) \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact hM _ (hmem t ht1) (by simpa using ht2)
  have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) (by linarith)) hsd hsb
  set g := Function.update s 0 (limUnder (𝓝[≠] (0 : ℂ)) s) with hg_def
  have hgc : DifferentiableOn ℂ g (Metric.closedBall 0 r) :=
    hg.mono (Metric.closedBall_subset_ball (by linarith))
  have hw : z k ∈ Metric.ball (0 : ℂ) r := by simpa using hzk
  have hcauchy := (hgc.mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hcongr : (∮ t in C(0, r), (t - z k)⁻¹ • g t) = (∮ t in C(0, r), (t - z k)⁻¹ • s t) := by
    refine circleIntegral.integral_congr hr.le ?_
    intro t ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at ht
      linarith
    simp only [hg_def, Function.update_of_ne ht0]
  rw [hcongr] at hcauchy
  rw [hcauchy]
  by_cases h0 : z k = 0
  · rw [if_pos h0, h0, hg_def, Function.update_self]
  · rw [if_neg h0, hg_def, Function.update_of_ne h0, hs_def]
    simp only [Function.update_eq_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeFnFinsetSumSmul
section
open MeasureTheory
namespace GlobalTheory.FinsetSumSmulCoe

theorem coeFn_finset_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type}
    (c : ι → ℂ) (u : ι → Lp ℂ (2 : ENNReal) μ) (s : Finset ι) :
    (((∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * (((u i : α →ₘ[μ] ℂ)) : α → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • u a) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c a) (u a), ih]
      with x h1 h2 h3
    rw [Finset.sum_insert ha]
    change (((c a • u a + ∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ)) : α → ℂ) x = _
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by
  intro α _ μ ι _ c u
  exact coeFn_finset_sum_smul c u Finset.univ

end GlobalTheory.FinsetSumSmulCoe
end

