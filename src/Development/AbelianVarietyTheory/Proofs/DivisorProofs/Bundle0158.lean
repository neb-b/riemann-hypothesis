module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlat
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

theorem smul_comm_of_invertible {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (ψ : L →ₗ[B] B) (e ℓ : L) : ψ e • ℓ = ψ ℓ • e := by
  let T : L ⊗[B] L →ₗ[B] L := TensorProduct.lift ((LinearMap.lsmul B L).compl₁₂ ψ LinearMap.id)
  have h := congrArg T (Module.Invertible.tmul_comm (R := B) (m₁ := e) (m₂ := ℓ))
  simpa [T] using h

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def intersection_update_fsHerm_neg_one (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) : L →ₗ[B] B :=
  φ.toLinearMap (fun _ => e) 0

theorem position_apply (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e ℓ : L) :
    intersection_update_fsHerm_neg_one φ e ℓ = φ (Function.update (fun _ => e) 0 ℓ) := rfl

theorem position_self (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) :
    intersection_update_fsHerm_neg_one φ e e = φ (fun _ => e) := by
  rw [position_apply, Function.update_eq_self]

theorem pow_mul_eq_mul_prod_position [Module.Invertible B L]
    (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) (ℓ : Fin (q + 1) → L) :
    φ (fun _ => e) ^ (q + 1) * φ ℓ = φ (fun _ => e) * ∏ i, intersection_update_fsHerm_neg_one φ e (ℓ i) := by
  have h1 : φ (fun i => φ (fun _ => e) • ℓ i) = φ (fun _ => e) ^ (q + 1) * φ ℓ := by
    rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, RingHom.id_apply]
  have h2 : φ (fun i => intersection_update_fsHerm_neg_one φ e (ℓ i) • e) = (∏ i, intersection_update_fsHerm_neg_one φ e (ℓ i)) * φ (fun _ => e) := by
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul, RingHom.id_apply]
  have h3 : (fun i => φ (fun _ => e) • ℓ i) = (fun i => intersection_update_fsHerm_neg_one φ e (ℓ i) • e) := by
    funext i
    rw [← position_self φ e]
    exact smul_comm_of_invertible (intersection_update_fsHerm_neg_one φ e) e (ℓ i)
  rw [← h1, h3, h2, mul_comm]

theorem algebraMap_mul_gen (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e ℓ : L) :
    algebraMap B (Alg φ) (φ (fun _ => e)) * gen φ ℓ =
      algebraMap B (Alg φ) (intersection_update_fsHerm_neg_one φ e ℓ) * gen φ e := by
  have hA := prod_gen φ (fun _ => e)
  have hB := prod_gen φ (Function.update (fun _ => e) 0 ℓ)
  rw [Fin.prod_univ_succ] at hA hB
  simp only [Function.update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
    Function.update_of_ne] at hB
  rw [position_apply, ← hB, ← hA]
  ring

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg
open MvPolynomial
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

theorem algHom_ext_of_isUnit (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L)
    {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    {g₁ g₂ : Alg φ →ₐ[B] R} (h : g₁ (gen φ e) = g₂ (gen φ e)) : g₁ = g₂ := by
  refine Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => ?_)
  change g₁ (gen φ ℓ) = g₂ (gen φ ℓ)
  have k₁ := congrArg g₁ (algebraMap_mul_gen φ e ℓ)
  have k₂ := congrArg g₂ (algebraMap_mul_gen φ e ℓ)
  simp only [map_mul, AlgHom.commutes] at k₁ k₂
  apply hu.mul_left_cancel
  rw [k₁, k₂, h]

def liftRoot [Module.Invertible B L] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L)
    {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    (x : R) (hx : x ^ (q + 1) = algebraMap B R (φ (fun _ => e))) : Alg φ →ₐ[B] R :=
  Ideal.Quotient.liftₐ (ideal φ)
    (MvPolynomial.aeval fun ℓ => algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) <| by
    intro a ha
    have hle : ideal φ ≤ RingHom.ker (MvPolynomial.aeval (R := B) fun ℓ : L =>
        algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) := ?_
    · exact hle ha
    refine Ideal.span_le.2 ?_
    rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, aeval_X, map_add]
      ring
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_mul, aeval_X, aeval_C, map_smul, smul_eq_mul]
      ring
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_prod, aeval_X, aeval_C]
      rw [sub_eq_zero, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hx]
      have key := congrArg (algebraMap B R) (pow_mul_eq_mul_prod_position φ e ℓ)
      simp only [map_mul, map_pow, map_prod] at key
      set u := hu.unit
      have hu' : (u : R) = algebraMap B R (φ (fun _ => e)) := rfl
      rw [← hu'] at key ⊢
      have hv : (↑u⁻¹ : R) ^ (q + 1) * (u : R) ^ (q + 1) = 1 := by
        rw [← mul_pow, Units.inv_mul, one_pow]
      apply (u ^ (q + 1)).isUnit.mul_right_cancel
      rw [Units.val_pow_eq_pow_val]
      calc (∏ i, algebraMap B R (intersection_update_fsHerm_neg_one φ e (ℓ i))) * ↑u⁻¹ ^ (q + 1) * ↑u * ↑u ^ (q + 1)
          = (↑u * ∏ i, algebraMap B R (intersection_update_fsHerm_neg_one φ e (ℓ i))) * (↑u⁻¹ ^ (q + 1) * ↑u ^ (q + 1)) := by ring
        _ = algebraMap B R (φ ℓ) * ↑u ^ (q + 1) := by rw [hv, mul_one, ← key]; ring

theorem liftRoot_gen [Module.Invertible B L] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B)
    (e : L) {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    (x : R) (hx : x ^ (q + 1) = algebraMap B R (φ (fun _ => e))) :
    liftRoot φ e hu x hx (gen φ e) = x := by
  have h0 : liftRoot φ e hu x hx (gen φ e) =
      MvPolynomial.aeval (fun ℓ => algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) (X e) := rfl
  rw [h0, aeval_X, position_self]
  have : algebraMap B R (φ (fun _ => e)) * ↑hu.unit⁻¹ = 1 := by
    exact hu.mul_val_inv
  rw [this, one_mul]

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg
open MvPolynomial
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

theorem smul_top_ne_top [Module.Invertible B L]
    (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (m : Ideal B) [hm : m.IsMaximal]
    (e : L) (he : φ (fun _ => e) ∉ m) : m • (⊤ : Submodule B (Alg φ)) ≠ ⊤ := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let K := AlgebraicClosure (B ⧸ m)
  have hK : ∀ b : B, algebraMap B K b = algebraMap (B ⧸ m) K (Ideal.Quotient.mk m b) := fun b =>
    IsScalarTower.algebraMap_apply B (B ⧸ m) K b
  have hu : IsUnit (algebraMap B K (φ (fun _ => e))) := by
    rw [hK, isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap (B ⧸ m) K).injective,
      Ideal.Quotient.eq_zero_iff_mem]
    exact he
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B K (φ (fun _ => e)))
    (Nat.succ_pos q)
  let g := liftRoot φ e hu x hx
  intro htop
  have hle : m • (⊤ : Submodule B (Alg φ)) ≤ Submodule.comap g.toLinearMap ⊥ := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [Submodule.mem_comap, Submodule.mem_bot, AlgHom.toLinearMap_apply, map_smul,
      Algebra.smul_def, hK, (Ideal.Quotient.eq_zero_iff_mem).2 hr, map_zero, zero_mul]
  have h1 : (1 : Alg φ) ∈ Submodule.comap g.toLinearMap ⊥ := hle (by rw [htop]; exact Submodule.mem_top)
  simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_one, Submodule.mem_bot] at h1
  exact one_ne_zero h1

def awayEquiv [Module.Invertible B L] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) :
    Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ ≃ₐ[Localization.Away (φ (fun _ => e))]
      AdjoinRoot (Polynomial.X ^ (q + 1) - Polynomial.C
        (algebraMap B (Localization.Away (φ (fun _ => e))) (φ (fun _ => e)))) := by
  set f := φ (fun _ => e)
  set Bf := Localization.Away f
  set P : Polynomial Bf := Polynomial.X ^ (q + 1) - Polynomial.C (algebraMap B Bf f)
  set A := AdjoinRoot P
  set T := Bf ⊗[B] Alg φ
  have hfu : IsUnit (algebraMap B Bf f) := IsLocalization.Away.algebraMap_isUnit f
  have huA : IsUnit (algebraMap B A f) := by
    rw [IsScalarTower.algebraMap_apply B Bf A]; exact hfu.map _
  have huT : IsUnit (algebraMap B T f) := by
    rw [IsScalarTower.algebraMap_apply B Bf T]; exact hfu.map _
  have hxA : AdjoinRoot.root P ^ (q + 1) = algebraMap B A f := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [IsScalarTower.algebraMap_apply B Bf A]
    exact sub_eq_zero.1 h
  have hxT : P.eval₂ (algebraMap Bf T) ((1 : Bf) ⊗ₜ[B] gen φ e : T) = 0 := by
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [sub_eq_zero, Algebra.TensorProduct.tmul_pow, one_pow, ← IsScalarTower.algebraMap_apply,
      ← Algebra.TensorProduct.includeRight.commutes]
    congr 1
    have := prod_gen φ (fun _ => e)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  let fwd : T →ₐ[Bf] A := Algebra.TensorProduct.lift (Algebra.ofId Bf A)
    (liftRoot φ e huA (AdjoinRoot.root P) hxA) (fun _ _ => Commute.all _ _)
  let bwd : A →ₐ[Bf] T := AdjoinRoot.liftAlgHom P (Algebra.ofId Bf T) ((1 : Bf) ⊗ₜ[B] gen φ e) hxT
  have hf : fwd ((1 : Bf) ⊗ₜ[B] gen φ e) = AdjoinRoot.root P := by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact liftRoot_gen φ e huA _ hxA
  have hb : bwd (AdjoinRoot.root P) = (1 : Bf) ⊗ₜ[B] gen φ e := AdjoinRoot.liftAlgHom_root _ _ _ _
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · exact AdjoinRoot.algHom_ext (by simp only [AlgHom.comp_apply, hb, hf, AlgHom.id_apply])
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    exact algHom_ext_of_isUnit φ e huT (by
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
        hf, hb, AlgHom.id_apply])

theorem away_finite_projective [Module.Invertible B L]
    (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) :
    Module.Finite (Localization.Away (φ (fun _ => e))) (Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ) ∧
    Module.Projective (Localization.Away (φ (fun _ => e))) (Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ) := by
  set Bf := Localization.Away (φ (fun _ => e))
  have hmon : (Polynomial.X ^ (q + 1) - Polynomial.C (algebraMap B Bf (φ (fun _ => e)))).Monic :=
    Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero q)
  let pb := AdjoinRoot.powerBasis' hmon
  haveI := Module.Free.of_basis pb.basis
  haveI := Module.Finite.of_basis pb.basis
  let eq := (awayEquiv φ e).toLinearEquiv
  exact ⟨Module.Finite.equiv eq.symm, Module.Projective.of_equiv eq.symm⟩

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg

theorem finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L]
    [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B),
    0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) →
    Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧
      Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  intro B _ L _ _ _ q φ hq hφ
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  let s : Set B := Set.range (fun e : L => φ (fun _ => e))
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    exact he (hsm (Ideal.subset_span ⟨e, rfl⟩))
  let F : s → Type := fun g => Localization.Away g.1 ⊗[B] Alg φ
  let ϕ : ∀ g : s, Alg φ →ₗ[B] F g := fun g => TensorProduct.mk B (Localization.Away g.1) (Alg φ) 1
  have hfp : ∀ g : s, Module.Finite (Localization.Away g.1) (F g) ∧
      Module.Projective (Localization.Away g.1) (F g) := by
    rintro ⟨_, e, rfl⟩
    exact away_finite_projective φ e
  haveI (g : s) : Module.Finite (Localization.Away g.1) (F g) := (hfp g).1
  haveI (g : s) : Module.Projective (Localization.Away g.1) (F g) := (hfp g).2
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2
      (TensorProduct.isBaseChange B (Alg φ) (Localization.Away g.1))
  haveI (g : s) : Module.Flat B (F g) := by
    haveI : Module.Flat B (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    haveI : Module.Flat (Localization.Away g.1) (F g) := Module.Flat.of_projective
    exact Module.Flat.trans B (Localization.Away g.1) (F g)
  haveI : Module.FinitePresentation B (Alg φ) :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat B (Alg φ) :=
    Module.flat_of_isLocalized_span B (Alg φ) s hs F ϕ fun _ => inferInstance
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, ?_⟩
  constructor
  intro m hm
  obtain ⟨e, he⟩ := hφ m hm.isPrime
  exact smul_top_ne_top φ m e he

end GlobalTheory.KummerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShift
section
open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExt
section
open NumberField

namespace GlobalTheory

theorem span_inf_span_eq_span_inf_of_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)),
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓
        (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) =
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) ''
        ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  intro K L _ _ _ _ _ n M W
  obtain ⟨m, ω, η, hη, hsum⟩ := exists_trace_dual_system K L
  let F : Fin m → (Fin n → L) → (Fin n → K) := fun i y j => Algebra.trace K L (η i * y j)
  have Fadd : ∀ i y z, F i (y + z) = F i y + F i z := by
    intro i y z; funext j; simp [F, mul_add, map_add (f := _)]
  have Fzero : ∀ i, F i 0 = 0 := by intro i; funext j; simp [F]
  have hint : ∀ i (a : 𝓞 L), ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Algebra.trace K L (η i * a) := by
    intro i a
    have h := (Submodule.mem_traceDual.mp (hη i)) (a : L) (Submodule.mem_one.mpr ⟨a, rfl⟩)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc, Algebra.traceForm_apply]⟩
  have Ftr : ∀ i (c : L) (x : Fin n → K),
      F i (c • (fun j => algebraMap K L (x j))) = Algebra.trace K L (η i * c) • x := by
    intro i c x; funext j
    simp only [F, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm _ (algebraMap K L (x j)), ← Algebra.smul_def, LinearMap.map_smul,
      smul_eq_mul, mul_comm]
  have hsm : ∀ (a : 𝓞 L) (v : Fin n → L), a • v = (a : L) • v := by
    intro a v; funext j; rfl
  have hM : ∀ y ∈ Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))),
      ∀ i (a : 𝓞 L), F i (a • y) ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      obtain ⟨c, hc⟩ := hint i a
      rw [hsm, Ftr, ← hc, algebraMap_smul]
      exact M.smul_mem c hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact M.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact M.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  have hW : ∀ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))),
      ∀ i (a : L), F i (a • y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      rw [Ftr]
      exact W.smul_mem _ hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact W.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact W.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  apply le_antisymm
  · rintro y ⟨hy1, hy2⟩
    have hy2' : y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))) :=
      hy2
    have hdec : y = ∑ i, ω i • (fun j => algebraMap K L (F i y j)) := by
      funext j
      rw [Finset.sum_apply, hsum (y j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = (ω i : L) * _
      rw [mul_comm]
    rw [hdec]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i y, ?_, rfl⟩)
    refine ⟨?_, ?_⟩
    · simpa using hM y hy1 i 1
    · simpa using hW y hy2' i 1
  · refine le_inf (Submodule.span_mono (Set.image_mono fun x hx => hx.1)) ?_
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx.2, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

def LiftIn {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) (V : X.left.Opens) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤

end GlobalTheory.SecLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLift
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem lift_ringHom_of_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  intro B _ X s hlift U hU V hV e C C₀ _ _ _ _ π hπ hk β φ₀ hcomp

  haveI : Nontrivial C₀ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : (1 : C) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker]; exact Subsingleton.elim _ _
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      have := Ideal.mul_mem_mul h1 h1
      simpa [pow_two] using this
    rw [hk, Ideal.mem_bot] at h2
    exact one_ne_zero h2
  have hsub : ∀ a b : PrimeSpectrum C, a = b := by
    intro a b
    ext1
    rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime a.asIdeal),
      IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime b.asIdeal)]
  have hA := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hx₀ : (Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec) ≫ s =
      spMap π ≫ (Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec) := by
    rw [Category.assoc, ← hA, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, spMap,
      ← Spec.map_comp]
    congr 2
    ext1
    exact hcomp
  obtain ⟨x, hx1, hx2⟩ := hlift C C₀ π hπ hk _ _ hx₀
  have hrange : Set.range x ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum C₀))
    have hp : p = (spMap π) q := hsub _ _
    refine ⟨(Spec.map (CommRingCat.ofHom φ₀)) q, ?_⟩
    rw [hp]
    have := congrArg (fun f : Sp C₀ ⟶ X => f q) hx1
    first
      | exact this.symm
      | (rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this; exact this.symm)
      | (simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this; exact this.symm)
  have hyx : IsOpenImmersion.lift hV.fromSpec x hrange ≫ hV.fromSpec = x :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = IsOpenImmersion.lift hV.fromSpec x hrange :=
    ⟨_, Spec.map_preimage _⟩
  rw [← hφ] at hyx
  refine ⟨φ.hom, ?_, ?_⟩
  · have h3 : Spec.map (CommRingCat.ofHom (π.comp φ.hom)) ≫ hV.fromSpec =
        Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec := by
      rw [← hx1, ← hyx, spMap, ← Category.assoc, ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hV.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4
  · have h3 : Spec.map (CommRingCat.ofHom (φ.hom.comp (s.appLE U V e).hom)) ≫
        hU.fromSpec = Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec := by
      rw [← hx2, ← hyx, Category.assoc, ← hA, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  first | exact @GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | exact GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | (intros; apply GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable <;> assumption)
end

