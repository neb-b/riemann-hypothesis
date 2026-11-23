module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulMemSpanAlgebraicOverPadicIntegers
section
noncomputable section

namespace GlobalTheory.K5.ReprSpan

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_one : IsAlgZp (p := p) (1 : Ω) :=
  ⟨X - C 1, X_sub_C_ne_zero 1, by simp⟩

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  let : Algebra ℤ_[p] Ω := Algebra.compHom Ω (algebraMap ℤ_[p] (O0 p))
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp (p := p) z ↔ IsAlgebraic ℤ_[p] z := fun z => by
    simp only [IsAlgZp, IsAlgebraic, aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy


variable (p Ω) in
def algZpMonoid : Submonoid Ω where
  carrier := {x | IsAlgZp (p := p) x}
  one_mem' := isAlgZp_one
  mul_mem' := isAlgZp_mul

theorem mem_adjoin_iff (z : Ω) :
    z ∈ Algebra.adjoin (O0 p) {x : Ω | IsAlgZp (p := p) x} ↔
      z ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure {x : Ω | IsAlgZp (p := p) x} : Set Ω) = {x | IsAlgZp (p := p) x} := by
    rw [show {x : Ω | IsAlgZp (p := p) x} = (algZpMonoid (p := p) (Ω := Ω) : Set Ω) from rfl,
      Submonoid.closure_eq]
  rw [hcl]

theorem exists_mul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  intro p _ Ω _ _ h b hb
  set B := Algebra.adjoin (O0 p) {x : Ω | IsAlgZp (p := p) x} with hBdef
  let S : Subfield Ω :=
    { carrier := {b | ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ B}
      zero_mem' := ⟨1, one_ne_zero, by rw [mul_zero]; exact B.zero_mem⟩
      one_mem' := ⟨1, one_ne_zero, by rw [map_one, mul_one]; exact B.one_mem⟩
      add_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a + c) =
            algebraMap (O0 p) Ω g' * (algebraMap (O0 p) Ω g * a) +
              algebraMap (O0 p) Ω g * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem _) ha) (B.mul_mem (B.algebraMap_mem _) hc)
      mul_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a * c) =
            (algebraMap (O0 p) Ω g * a) * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.mul_mem ha hc
      neg_mem' := by
        rintro a ⟨g, hg, ha⟩
        exact ⟨g, hg, by rw [mul_neg]; exact B.neg_mem ha⟩
      inv_mem' := by
        rintro a ⟨g, hg, ha⟩
        by_cases ha0 : a = 0
        · exact ⟨1, one_ne_zero, by rw [ha0, inv_zero, mul_zero]; exact B.zero_mem⟩
        have hg0 : algebraMap (O0 p) Ω g ≠ 0 := fun e => hg (h.inj (by rw [e, map_zero]))
        have hy0 : algebraMap (O0 p) Ω g * a ≠ 0 := mul_ne_zero hg0 ha0
        let y : B := ⟨algebraMap (O0 p) Ω g * a, ha⟩
        have halg : IsAlgebraic (O0 p) y :=
          (isAlgebraic_algHom_iff B.val Subtype.val_injective).1 (h.alg.isAlgebraic _)
        have hnz : y ∈ nonZeroDivisors B :=
          mem_nonZeroDivisors_of_ne_zero (fun e => hy0 (congrArg Subtype.val e))
        obtain ⟨r, hr, s, hs⟩ := halg.exists_ne_zero_dvd hnz
        have hs' : algebraMap (O0 p) Ω r = algebraMap (O0 p) Ω g * a * (s : Ω) := by
          have := congrArg Subtype.val hs
          simpa [y] using this
        refine ⟨r, hr, ?_⟩
        have e : algebraMap (O0 p) Ω r * a⁻¹ = algebraMap (O0 p) Ω g * (s : Ω) := by
          rw [hs']; field_simp
        show algebraMap (O0 p) Ω r * a⁻¹ ∈ B
        rw [e]
        exact B.mul_mem (B.algebraMap_mem g) s.2 }
  have hle : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}) ≤ S := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact B.algebraMap_mem c⟩
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  obtain ⟨g, hg, hgb⟩ := hle hb
  exact ⟨g, hg, (mem_adjoin_iff _).1 hgb⟩

end GlobalTheory.K5.ReprSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZeroStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_odd_weight_frame_det_ne_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0) → ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧ (evM s w F τ₀).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | exact GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | (intros; apply GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizer
section
open Polynomial IntermediateField

namespace GlobalTheory.K5.Span

variable (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]

def baseField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x})

variable {p Ω}

theorem algebraMap_mem_baseField (a : O0 p) : algebraMap (O0 p) Ω a ∈ baseField p Ω :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem ggeo_fix_baseField {g : Gal p Ω} (hg : g ∈ Ggeo (p := p) Ω) {x : Ω}
    (hx : x ∈ baseField p Ω) :
    g x = x := by
  have hle : baseField p Ω ≤ RingHom.eqLocusField (g : Ω →+* Ω) (RingHom.id Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro z (⟨a, rfl⟩ | hz)
    · show g (algebraMap (O0 p) Ω a) = algebraMap (O0 p) Ω a
      exact g.commutes a
    · show g z = z
      exact hg z hz
  exact hle hx

noncomputable def toGal (σ : Ω ≃ₐ[baseField p Ω] Ω) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun a =>
    σ.commutes (⟨algebraMap (O0 p) Ω a, algebraMap_mem_baseField a⟩ : baseField p Ω)

theorem toGal_apply (σ : Ω ≃ₐ[baseField p Ω] Ω) (x : Ω) : toGal σ x = σ x := rfl

theorem isAlgebraic_baseField (h : IsClo p Ω) : Algebra.IsAlgebraic (baseField p Ω) Ω := by
  haveI := h.alg
  refine ⟨fun x => ?_⟩
  obtain ⟨P, hP0, hPx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x
  let φ : O0 p →+* baseField p Ω :=
    (algebraMap (O0 p) Ω).codRestrict (baseField p Ω) algebraMap_mem_baseField
  have hφ : Function.Injective φ := fun a b hab => h.inj (congrArg Subtype.val hab)
  refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP0, ?_⟩
  rw [aeval_def, eval₂_map]
  have : (algebraMap (baseField p Ω) Ω).comp φ = algebraMap (O0 p) Ω := by
    ext a; rfl
  rw [this, ← aeval_def, hPx]

end GlobalTheory.K5.Span

open GlobalTheory.K5.Span in
open GlobalTheory.K5 GlobalTheory.K5.Span in
theorem GlobalTheory.K5.span_fixed_ggeo_stab : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ h T N y hy
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  haveI := h.clo
  set L := baseField p Ω
  haveI : CharZero L := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := isAlgebraic_baseField h
  haveI : IsAlgClosure L Ω := ⟨h.clo, inferInstance⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  set M : IntermediateField L Ω := IntermediateField.adjoin L {T.qq N}
  have hyM : y ∈ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, mem_fixedField_iff]
    intro σ hσ
    have hq : σ (T.qq N) = T.qq N :=
      (mem_fixingSubgroup_iff M σ).1 hσ _ (mem_adjoin_simple_self L _)
    refine hy (toGal σ) (Subgroup.mem_inf.2 ⟨fun x hx => ?_, ?_⟩)
    · exact σ.commutes (⟨x, Subfield.subset_closure (Or.inr hx)⟩ : L)
    · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, toGal_apply, hq]
  have hyA : y ∈ (aeval (T.qq N) : L[X] →ₐ[L] Ω).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
      ← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)]
    exact hyM
  obtain ⟨P, hP⟩ := hyA
  set q0 : L := ⟨algebraMap (O0 p) Ω (qO p), algebraMap_mem_baseField _⟩
  set Q : L[X] := X ^ (p ^ N) - C q0
  have hpN : p ^ N ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hQm : Q.Monic := monic_X_pow_sub_C _ hpN
  have hQd : Q.natDegree = p ^ N := natDegree_X_pow_sub_C _
  have hQ1 : Q ≠ 1 := by
    intro e; rw [e, natDegree_one] at hQd; exact hpN hQd.symm
  have hQq : aeval (T.qq N) Q = 0 := by
    simp only [Q, map_sub, map_pow, aeval_X, aeval_C, Basic.qq_pow]
    exact sub_self _
  set R := P %ₘ Q
  have hRd : R.natDegree < p ^ N := hQd ▸ natDegree_modByMonic_lt P hQm hQ1
  have hR : aeval (T.qq N) R = y := by
    have e := congrArg (aeval (T.qq N)) (modByMonic_add_div P Q)
    rw [map_add (f := _), map_mul, hQq, zero_mul, add_zero] at e
    rw [e]; exact hP
  refine ⟨fun j => ((R.coeff j : L) : Ω), fun j g hg => ggeo_fix_baseField hg (R.coeff j).2, ?_⟩
  rw [← hR, aeval_eq_sum_range' hRd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTau
section
open GlobalTheory.K5

namespace GlobalTheory.K5.Span

theorem sum_range_shift_one {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) :
    ∑ i ∈ Finset.range M, f (i + 1) = ∑ i ∈ Finset.range M, f i := by
  have h1 := Finset.sum_range_succ' f M
  have h2 := Finset.sum_range_succ f M
  have h3 : f M = f 0 := by simpa using hf 0
  rw [h3] at h2
  exact add_right_cancel (h1.symm.trans h2)

theorem sum_range_shift {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) (s : ℕ) :
    ∑ i ∈ Finset.range M, f (i + s) = ∑ i ∈ Finset.range M, f i := by
  induction s generalizing f with
  | zero => simp
  | succ s ih =>
    have := sum_range_shift_one (fun i => f (i + s)) (fun i => by
      show f (i + M + s) = f (i + s)
      rw [add_right_comm, hf])
    rw [← ih f hf, ← this]
    exact Finset.sum_congr rfl fun i _ => by congr 1; omega

theorem span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ hΩ T τ hτ hτq N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hprim : IsPrimitiveRoot (T.ζ N) (p ^ N) := T.prim N
  have hMpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hq0 : T.qq N ≠ 0 := Basic.qq_ne_zero T N
  have hqpow : T.qq N ^ p ^ N = algebraMap (O0 p) Ω (qO p) := Basic.qq_pow T N
  have hτqN := hτq N
  set M := p ^ N with hMdef
  set ζ := T.ζ N with hζdef
  set q := T.qq N with hqdef
  have hM0 : (M : Ω) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hζ0 : ζ ≠ 0 := hprim.ne_zero hMpos.ne'

  have hζalg : IsAlgZp (p := p) ζ := by
    refine ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hMpos 1, ?_⟩
    simp [hprim.pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo (p := p) Ω, g ζ = ζ := fun g hg => hg ζ hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) q = ζ ^ i * q := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfixζ τ hτ, hτqN, pow_succ']
      ring
  have hτG : ∀ i : ℕ, τ ^ i ∈ Ggeo (p := p) Ω := fun i => Subgroup.pow_mem _ hτ i
  have hconj : ∀ g ∈ Ggeo (p := p) Ω, g q = q → ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ i) z := by
    intro g hg hgq i
    have hk : (τ ^ i)⁻¹ * g * τ ^ i ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) q := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG i)) hg)
        (hτG i), MulAction.mem_stabilizer_iff.2 ?_⟩
      show ((τ ^ i)⁻¹ * g * τ ^ i) q = q
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτpow, map_mul, map_pow, hfixζ g hg, hgq, ← hτpow,
        AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have hkz := hz _ hk
    have e : τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i) = g * τ ^ i := by group
    calc g ((τ ^ i) z) = (g * τ ^ i) z := rfl
      _ = (τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i)) z := by rw [e]
      _ = (τ ^ i) (((τ ^ i)⁻¹ * g * τ ^ i) z) := rfl
      _ = (τ ^ i) z := by rw [hkz]
  have hdec : ∀ g ∈ Ggeo (p := p) Ω, ∃ s : ℕ, g q = ζ ^ s * q ∧ ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z := by
    intro g hg
    have h1 : (g q / q) ^ M = 1 := by
      rw [div_pow, ← map_pow, hqpow, AlgEquiv.commutes, ← hqpow, div_self (pow_ne_zero _ hq0)]
    obtain ⟨s, -, hse⟩ := hprim.eq_pow_of_pow_eq_one h1
    have hgq : g q = ζ ^ s * q := by rw [hse, div_mul_cancel₀ _ hq0]
    refine ⟨s, hgq, fun i => ?_⟩
    have hh : (τ ^ s)⁻¹ * g ∈ Ggeo (p := p) Ω := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG s)) hg
    have hhq : ((τ ^ s)⁻¹ * g) q = q := by
      rw [AlgEquiv.mul_apply, hgq, ← hτpow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have e : g = τ ^ s * ((τ ^ s)⁻¹ * g) := by group
    rw [e, AlgEquiv.mul_apply, hconj _ hh hhq i, ← AlgEquiv.mul_apply, ← pow_add]

  have hτMz : (τ ^ M) z = z := by
    refine hz _ (Subgroup.mem_inf.2 ⟨hτG M, MulAction.mem_stabilizer_iff.2 ?_⟩)
    show (τ ^ M) q = q
    rw [hτpow, hprim.pow_eq_one, one_mul]
  set η := ζ⁻¹ with hηdef
  have hηprim : IsPrimitiveRoot η M := hprim.inv
  have hfixη : ∀ g ∈ Ggeo (p := p) Ω, g η = η := by
    intro g hg; rw [hηdef, map_inv₀, hfixζ g hg]
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Ω, ∀ j,
      P j = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, η ^ (i * j) * (τ ^ i) z := ⟨_, fun _ => rfl⟩
  have hgP : ∀ g ∈ Ggeo (p := p) Ω, ∀ s : ℕ, (∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z) →
      ∀ j, g (P j) = ζ ^ (s * j) * P j := by
    intro g hg s hs j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_mul, map_inv₀, map_natCast, map_sum]
    have hper : ∀ i, (fun i => η ^ (i * j) * (τ ^ i) z) (i + M) = (fun i => η ^ (i * j) * (τ ^ i) z) i := by
      intro i
      show η ^ ((i + M) * j) * (τ ^ (i + M)) z = η ^ (i * j) * (τ ^ i) z
      rw [add_mul, pow_add, show η ^ (M * j) = 1 by rw [pow_mul, hηprim.pow_eq_one, one_pow],
        mul_one, pow_add, AlgEquiv.mul_apply, hτMz]
    have hsh := sum_range_shift (M := M) (fun i => η ^ (i * j) * (τ ^ i) z) hper s
    rw [← hsh, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hfixη g hg, hs, add_comm s i]
    have hζη : ζ ^ (s * j) * η ^ (s * j) = 1 := by
      rw [← mul_pow, hηdef, mul_inv_cancel₀ hζ0, one_pow]
    calc (M : Ω)⁻¹ * (η ^ (i * j) * (τ ^ (i + s)) z)
        = (M : Ω)⁻¹ * ((ζ ^ (s * j) * η ^ (s * j)) * η ^ (i * j) * (τ ^ (i + s)) z) := by
          rw [hζη, one_mul]
      _ = ζ ^ (s * j) * ((M : Ω)⁻¹ * (η ^ ((i + s) * j) * (τ ^ (i + s)) z)) := by
          rw [add_mul, pow_add]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Ω, ∀ j, c j = P j / q ^ j := ⟨_, fun _ => rfl⟩
  refine ⟨c, ?_, ?_⟩
  · intro j g hg
    obtain ⟨s, hgq, hs⟩ := hdec g hg
    rw [hc, map_div₀, map_pow, hgq, hgP g hg s hs j, mul_pow, ← pow_mul,
      mul_div_mul_left _ _ (pow_ne_zero _ hζ0)]
  · have hgeom : ∀ i ∈ Finset.range M,
        ∑ j ∈ Finset.range M, η ^ (i * j) = if i = 0 then (M : Ω) else 0 := by
      intro i hi
      split_ifs with h0
      · simp [h0]
      · have hne : η ^ i ≠ 1 :=
          hηprim.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.1 hi)
        simp_rw [pow_mul]
        rw [geom_sum_eq hne, pow_right_comm, hηprim.pow_eq_one, one_pow, sub_self, zero_div]
    have e1 : ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z =
        ∑ i ∈ Finset.range M, (if i = 0 then (M : Ω) else 0) * (τ ^ i) z :=
      Finset.sum_congr rfl fun i hi => by rw [hgeom i hi]
    calc z = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z := by
          rw [e1, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hMpos) (fun b _ hb => by simp [hb])]
          simp [hM0]
      _ = ∑ j ∈ Finset.range M, P j := by
          simp only [hP]
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ = ∑ j ∈ Finset.range M, c j * q ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [hc, div_mul_cancel₀ _ (pow_ne_zero j hq0)]

end GlobalTheory.K5.Span
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
section
noncomputable section

namespace GlobalTheory

open IsLocalRing TensorProduct

universe u


open IsLocalRing TensorProduct in
open WithConv in
theorem _root_.GlobalTheory.bialgHom_map_antipode {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (g : A →ₐc[R] B) (a : A) :
    g (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (g a) := by
  have h1 := LinearMap.algHom_comp_convMul_distrib (g : A →ₐ[R] B)
    (toConv (HopfAlgebra.antipode R)) (toConv LinearMap.id)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib (toConv LinearMap.id)
    (toConv (HopfAlgebra.antipode R)) (g : A →ₗc[R] B)
  have e1 : (g : A →ₐ[R] B).toLinearMap ∘ₗ ofConv (1 : WithConv (A →ₗ[R] A)) =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp only [LinearMap.convOne_def]
    exact (g : A →ₐ[R] B).commutes _
  have e2 : ofConv (1 : WithConv (B →ₗ[R] B)) ∘ₗ (g : A →ₗc[R] B).toLinearMap =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp [LinearMap.convOne_def]
  rw [LinearMap.antipode_mul_id, e1] at h1
  rw [LinearMap.id_mul_antipode, e2] at h2
  have h := left_inv_eq_right_inv (ofConv_injective h1).symm (ofConv_injective h2).symm
  simpa using congrArg (fun f : WithConv (A →ₗ[R] B) ↦ (ofConv f) a) h


open IsLocalRing TensorProduct in
theorem _root_.GlobalTheory.henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  _root_.GlobalTheory.henselianLocalRing_of_henselianRing R


open IsLocalRing TensorProduct in
theorem _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable (R : Type u) (L : Type*) [CommRing R]
    [HenselianLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [Module.Finite (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  obtain ⟨A, _, _, hfin, het, hloc, he⟩ := _root_.GlobalTheory.exists_etale_lift_of_isSeparable R L
  exact ⟨A, inferInstance, inferInstance, hfin, het, _root_.GlobalTheory.henselianLocalRing_of_finite R A, he⟩


open IsLocalRing TensorProduct in
open CategoryTheory in
theorem _root_.GlobalTheory.finite_algebras_over_henselian (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      (∃ (ι : Type u) (_ : Finite ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
        (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
        ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i)) ∧
      ∀ c : S ⧸ (maximalIdeal R).map (algebraMap R S), IsIdempotentElem c →
        ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c) ∧
    (CommAlgCat.FiniteEtale.baseChange.{u} R (ResidueField R)).IsEquivalence ∧
    ∀ (L : Type u) [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
      [Algebra.IsSeparable (ResidueField R) L],
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
        HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  refine ⟨fun S _ _ _ ↦ ⟨_root_.GlobalTheory.exists_algEquiv_pi_henselianLocalRing R S,
    fun c hc ↦ _root_.GlobalTheory.existsUnique_idempotent_lift_quotient R hc⟩, ?_,
    fun L _ _ _ _ ↦ _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable R L⟩
  refine
    { faithful := ⟨fun {X Y} f g h ↦ ?_⟩
      full := ⟨fun {X Y} φ ↦ ?_⟩
      essSurj := ⟨fun Y ↦ ?_⟩ }
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    exact ObjectProperty.hom_ext _ (CommAlgCat.hom_ext
      ((_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).1
        (congrArg (fun φ ↦ φ.hom.hom) h)))
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    obtain ⟨f, hf⟩ := (_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).2 φ.hom.hom
    exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom f),
      ObjectProperty.hom_ext _ (CommAlgCat.hom_ext hf)⟩
  · have : Algebra.Etale (ResidueField R) Y.obj := Y.property.2
    obtain ⟨A, _, _, hfin, het, ⟨e⟩⟩ := _root_.GlobalTheory.exists_etale_lift_of_etale.{u, u} R Y.obj
    exact ⟨⟨CommAlgCat.of R A, ⟨hfin, het⟩⟩, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleSubgroupOfStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (U H : Subgroup G), AlmostSep v U → AlmostSep v (U.subgroupOf H) := by
  first | exact @GlobalTheory.AlmostEt.almostSep_subgroupOf | exact GlobalTheory.AlmostEt.almostSep_subgroupOf | (intros; apply GlobalTheory.AlmostEt.almostSep_subgroupOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicitStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeUOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.uOp q f τ) := by
  first | exact @GlobalTheory.Hk.hasSum_uOp | exact GlobalTheory.Hk.hasSum_uOp | (intros; apply GlobalTheory.Hk.hasSum_uOp <;> assumption)
end

