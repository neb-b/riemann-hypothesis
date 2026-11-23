module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnnihilatorKaehlerDerivationPrimitiveRoot
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem pow_four_mul_mem_of_smul_dA_eq_zero : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  intro l _ hl2 Ω _ _ _ A hA N z hz a hrel
  have hlΩ : (l : Ω) ≠ 0 := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hpos : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  have hz1 : (z : Ω) ^ (l ^ N) = 1 := hz.pow_eq_one
  have hzA : z ^ (l ^ N) = 1 := Subtype.ext (by simpa using hz1)
  have hzT : z ∈ cycAlg l A := mem_cycAlg_of_pow hzA
  have hrel' : ∑ i : Fin 1, (fun _ => a) i •
      KaehlerDifferential.D (fixA A) A ((fun _ => z) i) = 0 := by
    simpa using hrel
  obtain ⟨F, hF⟩ := kaehler_rel_local (fixA A) A 1 _ _ hrel'
  obtain ⟨C, tr, m, α, β, hFC, htr⟩ := _root_.GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg l hl2 Ω A hA F
  obtain ⟨D, hD, hDv⟩ := GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra l Ω A hA N z hz
  obtain ⟨D', hD', hD'v⟩ := exists_derOn_ext (fixA A) A (FracA A) (cycAlg l A) C tr m α β _ htr D hD
  have h := hF C hFC (fun _ => htr.le hzT) (FracA A) D' hD'
  rw [Fin.sum_univ_one, hD'v _ hzT, hDv, smul_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  have ht' : (t : Ω) = (a : Ω) * (l : Ω) ^ 3 * ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
    simpa [Algebra.smul_def] using ht
  refine ⟨((t * z ^ (l ^ N - 1) : A) : Ω), (t * z ^ (l ^ N - 1)).2, ?_⟩
  have hzz : (z : Ω) * (z : Ω) ^ (l ^ N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, hz1]
  push_cast
  rw [ht']
  field_simp
  linear_combination (-((a : Ω))) * hzz

end GlobalTheory.RecOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqPrimeSmulKaehlerDerivationEqSmulRootOfUnity
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

section Gen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def evMul (l : ℕ) (A : ValuationSubring Ω) : Submodule A (KaehlerDifferential (fixA A) A) where
  carrier := {ω | ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) →
    ω ∈ Submodule.span A {dA A z}}
  add_mem' := by
    rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, fun N hN z hz =>
      add_mem (h₁ N (le_trans (le_max_left _ _) hN) z hz) (h₂ N (le_trans (le_max_right _ _) hN) z hz)⟩
  zero_mem' := ⟨0, fun _ _ _ _ => zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨N₁, h₁⟩
    exact ⟨N₁, fun N hN z hz => Submodule.smul_mem _ c (h₁ N hN z hz)⟩

theorem dA_mem_evMul (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) {x : A} {n : ℕ}
    (hx : x ^ (l ^ n) = 1) : dA A x ∈ evMul l A := by
  refine ⟨n, fun N hN z hz => ?_⟩
  have : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (x : Ω) ^ (l ^ N) = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h0 : (x : Ω) ^ (l ^ n) = 1 := by
      have := congrArg (fun t : A => (t : Ω)) hx
      simpa using this
    rw [pow_add, pow_mul, h0, one_pow]
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one h1
  have h2 : x = z ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hi]
  rw [h2, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Gen

theorem l_sq_smul_dA_eq_smul : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  intro l _ hl2 Ω _ _ _ A hA v
  have hder : ∀ B : Subalgebra (fixA A) A, IsDerOn B (fun x => dA A x) := fun B =>
    ⟨fun x _ y _ => map_add (dA A) x y, fun x _ y _ => Derivation.leibniz (dA A) x y,
      fun a => (dA A).map_algebraMap a⟩
  obtain ⟨C, tr, k, a, b, hF, htr⟩ := _root_.GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg l hl2 Ω A hA {v}
  have h1 := GlobalTheory.AlmostEt.derOn_mem_span_of_trData (fixA A) A _ (cycAlg l A) C tr k a b _ htr
    (fun x => dA A x) (hder C) v (hF (by simp))
  have h2 : Submodule.span A ((fun x => dA A x) '' (cycAlg l A : Set A)) ≤ evMul l A := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h3 := GlobalTheory.AlmostEt.derOn_adjoin_mem_span (fixA A) A _ {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}
      (fun x => dA A x) (hder _) x hx
    refine Submodule.span_le.2 ?_ h3
    rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
    exact dA_mem_evMul l A hn
  obtain ⟨N₀, h⟩ := h2 h1
  refine ⟨N₀, fun N hN z hz => ?_⟩
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.1 (h N hN z hz)
  exact ⟨y, by rw [pow_two]; exact hy.symm⟩

end GlobalTheory.RecOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdLOfZetaUr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem repIso_symm_srcL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W W' : R2 Ω l}
    (h : RepIso W W') : RepIso W' W := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun s => ?_⟩
  rw [hg s]
  group

theorem vanishOrdL_of_zetaUr : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ZetaUr → VanishOrdL := by
  intro hC hZ l _ hl Ω _ _ _ ι e he W hW hS
  obtain ⟨S, A, W', g, hiso, hnf, hsrc⟩ := _root_.GlobalTheory.Ord2.exists_nf_srcUr l Ω ι e W hl he hW hS
  have hes : ES W' A := hZ l Ω ι e S A W' g hnf hsrc
  have hv : BlochKatoSelmerVanishes l (Loc.colRep W') := GlobalTheory.Ord2.es_vanish hC l Ω e S A W' hnf hes
  exact UpperTheory.V.X.Kato.conj l ℚ Ω 2 W' W (repIso_symm_srcL hiso) hv

end GlobalTheory.Ord2
end

