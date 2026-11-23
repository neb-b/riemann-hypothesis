module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribed
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.AlmostEt

section DerLemmas

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem IsDerOn.mono' {B C : Subalgebra A S} {D : S → M} (h : IsDerOn C D) (hBC : B ≤ C) :
    IsDerOn B D :=
  ⟨fun x hx y hy => h.add x (hBC hx) y (hBC hy), fun x hx y hy => h.mul x (hBC hx) y (hBC hy), h.alg⟩

theorem IsDerOn.pow_succ_der {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    (k : ℕ) : D (x ^ (k + 1)) = (((k + 1 : ℕ) : S) * x ^ k) • D x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ' x (k + 1), h.mul x hx _ (pow_mem hx _), ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem IsDerOn.eq_on_adjoin {s : Set S} {D₁ D₂ : S → M} (h₁ : IsDerOn (Algebra.adjoin A s) D₁)
    (h₂ : IsDerOn (Algebra.adjoin A s) D₂) (hs : ∀ x ∈ s, D₁ x = D₂ x) :
    ∀ x ∈ Algebra.adjoin A s, D₁ x = D₂ x := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap a => rw [h₁.alg, h₂.alg]
  | add x y hx hy ihx ihy => rw [h₁.add x hx y hy, h₂.add x hx y hy, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [h₁.mul x hx y hy, h₂.mul x hx y hy, ihx, ihy]

end DerLemmas

section TowerDer

open GlobalTheory.K5 Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow_p (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.ζpow m)

theorem qS_succ_pow_p (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.qpow m)

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert (zS T m) {qS T m})

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton (qS T m)))

theorem zS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T (m + 1) := by
  rw [← zS_succ_pow_p]; exact pow_mem (zS_mem_levelAlg T (m + 1)) _

theorem qS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T (m + 1) := by
  rw [← qS_succ_pow_p]; exact pow_mem (qS_mem_levelAlg T (m + 1)) _

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) :=
  Algebra.adjoin_le (Set.insert_subset_iff.2 ⟨zS_mem_levelAlg_succ T m,
    Set.singleton_subset_iff.2 (qS_mem_levelAlg_succ T m)⟩)

theorem frac_smul_mk (s : integralClosure (O0 p) Ω) (x : Ω) :
    s • (Submodule.Quotient.mk x : Frac p Ω) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero (s : integralClosure (O0 p) Ω) :
    (Submodule.Quotient.mk (s : Ω) : Frac p Ω) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_relation (hc : CharZero Ω) (T : Tower p Ω) (m : ℕ) :
    (Polynomial.aeval (zS T (m + 1)) (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))) •
      (Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) : Frac p Ω) = 0 := by
  set z := zS T (m + 1)
  set ζ := T.ζ (m + 1)
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  have hξ : IsPrimitiveRoot (ζ ^ p ^ m) p := by
    have := (T.prim (m + 1)).pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this

  set gS : integralClosure (O0 p) Ω := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (ζ ^ p ^ m) ^ j := by
    simp [gS, z, ζ, zS]
  have hg : (gS : Ω) * (ζ ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp

  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (T.prim (m + 1)).isRoot_cyclotomic hpos
  have hid := congrArg (fun f => Polynomial.aeval ζ (Polynomial.derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add (f := _), map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  have hzval : (Polynomial.aeval z (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) : Ω)
      = Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) := by
    exact (Polynomial.aeval_algHom_apply (integralClosure (O0 p) Ω).val z _).symm
  rw [frac_smul_mk, hzval]
  set F := Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))
  have hζ1 : ζ ^ p ^ (m + 1) = 1 := (T.prim (m + 1)).pow_eq_one
  have hF : F * (ζ ^ p ^ m - 1) * ζ = (p : Ω) ^ (m + 1) := by
    have h2 : F * (ζ ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * ζ ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    rw [h2, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : ζ ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : F * (ζ * p / (p : Ω) ^ (m + 1)) = ((-gS : integralClosure (O0 p) Ω) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

end TowerDer

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

open GlobalTheory.K5

theorem IsDerOn.pow_der {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B) {n : ℕ}
    (hn : 0 < n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using h.pow_succ_der hx k

theorem zeta_derivation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
        D (qS T m) = 0 := by
  intro p hp Ω _ _ hc T
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hlev : ∀ m : ℕ, ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (levelAlg T (m + 1)) D ∧
        D (zS T (m + 1)) = Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) ∧
        D (qS T (m + 1)) = 0 := fun m =>
    _root_.GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg p Ω hc T (m + 1) (Nat.succ_pos m) (Frac p Ω) _ 0
      (cyc_relation inferInstance T m) (smul_zero _)
  choose D hD hDz hDq using hlev
  have hval : ∀ m, D m (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
      D m (qS T m) = 0 := by
    intro m
    constructor
    · rw [← zS_succ_pow_p, (hD m).pow_der (zS_mem_levelAlg T (m + 1)) hp.out.pos, hDz m, frac_smul_mk]
      congr 1
      have hc1 : ((zS T (m + 1) : integralClosure (O0 p) Ω) : Ω) = T.ζ (m + 1) := rfl
      push_cast
      rw [hc1, ← T.ζpow m, ← pow_sub_one_mul hp.out.ne_zero (T.ζ (m + 1))]
      field_simp
      ring
    · rw [← qS_succ_pow_p, (hD m).pow_der (qS_mem_levelAlg T (m + 1)) hp.out.pos, hDq m, smul_zero]
  have hcompat : ∀ m, ∀ x ∈ levelAlg T (m + 1), D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zS T (m + 1), qS T (m + 1)})
      ((hD (m + 1)).mono' (levelAlg_le_succ T (m + 1))) (hD m) ?_
    rintro x (rfl | hx)
    · rw [(hval (m + 1)).1, hDz m]
    · rw [Set.mem_singleton_iff.1 hx, (hval (m + 1)).2, hDq m]
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono D hD hcompat
  have hle : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (zS_mem_levelAlg_succ T m)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (qS_mem_levelAlg_succ T m)
  refine ⟨D', hD'.mono' hle, fun m => ⟨?_, ?_⟩⟩
  · rw [hD'eq m _ (zS_mem_levelAlg_succ T m), (hval m).1]
  · rw [hD'eq m _ (qS_mem_levelAlg_succ T m), (hval m).2]

end GlobalTheory.AlmostEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZMod
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNSep

theorem finite_nat_roots (a b c : ℂ) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {n : ℕ | a + (n : ℂ) * b + (n : ℂ) ^ 2 * c = 0}.Finite := by
  set P : Polynomial ℂ := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hPdef
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have e0 := congrArg (fun q => q.coeff 0) h0
    have e1 := congrArg (fun q => q.coeff 1) h0
    have e2 := congrArg (fun q => q.coeff 2) h0
    simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hf := (Polynomial.finite_setOf_isRoot hP).preimage (f := (Nat.cast : ℕ → ℂ)) Nat.cast_injective.injOn
  refine hf.subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  rw [Polynomial.IsRoot.def]
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  linear_combination hn

theorem vmul_apply {N : ℕ} (a b : ZMod N) (α : GL (Fin 2) (ZMod N)) (j : Fin 2) :
    vmul ![a, b] α j = a * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 j + b * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 j := by
  simp [vmul, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (hx : x ≠ 0) : vmul x α ≠ 0 := by
  intro h
  apply hx
  have : Matrix.vecMul (vmul x α) ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [vmul, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  rw [← this, h, Matrix.zero_vecMul]

end GlobalTheory.FNSep

namespace GlobalTheory.FNSep

theorem eq_or_eq_neg_of_rows {N : ℕ} (α β : GL (Fin 2) (ZMod N))
    (h0 : vmul ![1, 0] α = vmul ![1, 0] β ∨ vmul ![1, 0] α = -vmul ![1, 0] β)
    (h1 : vmul ![0, 1] α = vmul ![0, 1] β ∨ vmul ![0, 1] α = -vmul ![0, 1] β)
    (h2 : vmul ![1, 1] α = vmul ![1, 1] β ∨ vmul ![1, 1] α = -vmul ![1, 1] β) :
    α = β ∨ α = -β := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  · have E0 : ∀ j, _ := fun j => congrFun h0 j
    have E1 : ∀ j, _ := fun j => congrFun h1 j
    have E2 : ∀ j, _ := fun j => congrFun h2 j
    simp only [Pi.neg_apply, vmul_apply] at E0 E1 E2
    first
    | (left; apply Units.ext; ext i j; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)
    | (right; apply Units.ext; ext i j; rw [Units.val_neg, Matrix.neg_apply]; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)

theorem sep_family : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  intro N _
  classical
  let u : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N) → (Fin 2 → ZMod N) → ℍ → ℂ :=
    fun p e τ => wp N (vmul e p.1) τ - wp N (vmul e p.2) τ
  let S : Set ℕ := ⋃ p : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N),
    {n : ℕ | ¬ (∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0) ∧
      ∀ τ, u p ![1, 0] τ + (n : ℂ) * u p ![0, 1] τ + (n : ℂ) ^ 2 * u p ![1, 1] τ = 0}
  have hfin : Finite (GL (Fin 2) (ZMod N)) :=
    Finite.of_injective (fun a : GL (Fin 2) (ZMod N) => (a : Matrix (Fin 2) (Fin 2) (ZMod N))) fun a b h => Units.ext h
  have hS : S.Finite := by
    refine Set.finite_iUnion fun p => ?_
    by_cases hz : ∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0
    · exact Set.finite_empty.subset fun n hn => absurd hz hn.1
    · obtain ⟨τ, hτ⟩ := not_forall.mp hz
      exact (finite_nat_roots _ _ _ hτ).subset fun n hn => hn.2 τ
  obtain ⟨n, hn⟩ := hS.infinite_compl.nonempty
  refine ⟨n, n ^ 2, fun α β hfun => ?_⟩
  have hroot : ∀ τ, u (α, β) ![1, 0] τ + (n : ℂ) * u (α, β) ![0, 1] τ + (n : ℂ) ^ 2 * u (α, β) ![1, 1] τ = 0 := by
    intro τ
    have := congrFun hfun τ
    push_cast at this
    simp only [u]
    linear_combination this
  have hz : ∀ τ, u (α, β) ![1, 0] τ = 0 ∧ u (α, β) ![0, 1] τ = 0 ∧ u (α, β) ![1, 1] τ = 0 := by
    by_contra hz
    exact hn (Set.mem_iUnion.mpr ⟨(α, β), hz, hroot⟩)
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    obtain ⟨z0, z1, z2⟩ := hz UpperHalfPlane.I
    have ne0 : (![1, 0] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    have ne1 : (![0, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 1; simp at this
    have ne2 : (![1, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    exact eq_or_eq_neg_of_rows α β
      (_root_.GlobalTheory.FN.WpSep.main N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne0) (vmul_ne_zero _ β ne0) (sub_eq_zero.mp z0))
      (_root_.GlobalTheory.FN.WpSep.main N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne1) (vmul_ne_zero _ β ne1) (sub_eq_zero.mp z1))
      (_root_.GlobalTheory.FN.WpSep.main N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne2) (vmul_ne_zero _ β ne2) (sub_eq_zero.mp z2))
  · have h1 : N = 1 := le_antisymm hN (Nat.pos_of_ne_zero (NeZero.ne N))
    subst h1
    left
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _

end GlobalTheory.FNSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvd
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_le_of_dvd {N N' : ℕ} (hd : N ∣ N') :
    CongruenceSubgroup.Gamma N' ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ x : ℤ, (x : ZMod N) = ZMod.castHom hd (ZMod N) (x : ZMod N') := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem lv_mono : ∀ (E : Subring ℂ) (N N' w w' : ℕ) (f : ℍ → ℂ), 0 < N' → N ∣ N' → w ≤ w' →
    Lv E N w f → Lv E N' w' f := by
  intro E N N' w w' f hN' hd hw hf
  refine ⟨fun γ hγ τ => hf.1 γ (gamma_le_of_dvd hd hγ) τ, fun γ => ?_⟩
  have h1 : QAll (· ∈ E) N' fun τ => DD τ ^ w * f (γ • τ) :=
    QAll.of_dvd hN' hd E.zero_mem (hf.2 γ)
  have h2 : QAll (· ∈ E) N' fun τ => DD τ ^ (w' - w) :=
    QAllSubring.pow (w' - w) (eis_qAll N' hN' DD (Or.inr (Or.inr rfl)) E)
  have h3 := QAllSubring.mul h2 h1
  refine (congrArg (QAll (· ∈ E) N') (funext fun τ => ?_)).mp h3
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hw]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEq
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hs_uniq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  intro Ω _ ε C C' C'' φ φ' h h' hd hd' hs hs' heq
  obtain ⟨hmono, hadd, -, hcongr⟩ := _root_.GlobalTheory.FNHS.hs_props Ω ε
  set C₀ : ℝ := max C (max C' C'') with hC₀
  have h1 : HS ε C₀ φ h := hmono C C₀ φ h (le_max_left _ _) hs
  have h2 : HS ε C₀ φ' h' := hmono C' C₀ φ' h' (le_trans (le_max_left _ _) (le_max_right _ _)) hs'
  have h3 : HS ε C₀ (φ - φ') (h - h') := ((hadd C₀ φ φ' h h') h1 h2).2
  have h4 : HS ε C₀ (fun _ => (0 : ℂ)) (h - h') := by
    refine hcongr C₀ (φ - φ') (fun _ => 0) (h - h') ?_ h3
    intro z hz
    have : C'' < z.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz
    simp [heq z this]
  have hdd : Den (h - h') := (((_root_.GlobalTheory.FN.den_ring Ω).1 h h' hd hd').2.1)
  by_contra hne
  have hne' : h - h' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.fn_hasSum_ne_zero Ω ε C₀ (fun _ => (0 : ℂ)) (h - h') hdd hne' h4
  exact hD ((D + 1 : ℝ) * Complex.I) (by simp) rfl

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRat
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_mul_le (m k : ℕ) : CongruenceSubgroup.Gamma (m * k) ≤ CongruenceSubgroup.Gamma m := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c := fun (x : ℤ) (y : ZMod (m * k)) (e : (x : ZMod (m * k)) = y) =>
    congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ _ h1
  · simpa using c _ _ h2
  · simpa using c _ _ h3
  · simpa using c _ _ h4

theorem inR_cmp : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  intro E g f hE ⟨N, w, hN, hinv, hexp⟩
  obtain ⟨n₁, hn₁, hH⟩ := GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius g
  obtain ⟨n₂, hn₂, hC⟩ := _root_.GlobalTheory.FN.exists_conj_principal_congruence g
  obtain ⟨mob_hs, mob_mul, mob_one, mob_sl, mob_diff, mob_up⟩ := _root_.GlobalTheory.FN.mob_props
  obtain ⟨cmp_one, cmp_mul, cmp_sl, cmp_up⟩ := _root_.GlobalTheory.FN.cmp_props
  refine ⟨N * n₁ * n₂, w * n₁, by positivity, ?_, ?_⟩
  · intro δ hδ τ
    have hδ' : δ ∈ CongruenceSubgroup.Gamma (N * n₂) := by
      have : N * n₁ * n₂ = N * n₂ * n₁ := by ring
      rw [this] at hδ
      exact gamma_mul_le _ _ hδ
    obtain ⟨δ', hδ'm, hgδ⟩ := hC N δ hδ'
    have e1 : GlobalTheory.FN.cmp (g * ofSL δ) f = fun τ => GlobalTheory.FN.cmp g f (δ • τ) := by
      rw [cmp_mul, cmp_sl]
    have e2 : GlobalTheory.FN.cmp (ofSL δ' * g) f = GlobalTheory.FN.cmp g f := by
      rw [cmp_mul, cmp_sl]
      congr 1
      funext σ
      exact hinv δ' hδ'm σ
    have := congrFun (e1.symm.trans (hgδ ▸ e2)) τ
    exact this
  · intro γ₀
    obtain ⟨γ, a, d, b, had, hmob⟩ := hH γ₀
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have key := _root_.GlobalTheory.FNPole.qAll_pole_affine E N w a d b (fun τ => f (γ • τ)) hE hN ha hd (hexp γ)
    rw [had] at key
    have hlift := QAll.of_dvd (N := N * n₁) (N' := N * n₁ * n₂) (by positivity) (dvd_mul_right _ _)
      (p := (· ∈ E)) (Subring.zero_mem E) key
    convert hlift using 2 with τ
    congr 1
    have hz : (((a : ℂ) * τ + b) / d).im > 0 := by
      have : (((a : ℂ) * τ + b) / d) = ((a : ℝ) / d : ℝ) * (τ : ℂ) + ((b : ℝ) / d : ℝ) := by
        push_cast; field_simp
      rw [this]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have : (0 : ℝ) < (a : ℝ) / d := by positivity
      have := τ.im_pos
      simp only [UpperHalfPlane.coe_im]
      positivity
    show up f (mob g ((γ₀ • τ : ℍ) : ℂ)) = up (fun τ => f (γ • τ)) (((a : ℂ) * τ + b) / d)
    have hzc : ((UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hm : mob (ofSL γ) (((a : ℂ) * τ + b) / d) =
        ((γ • UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) := by
      rw [← mob_sl, hzc]
    simp only [up]
    rw [hmob τ, hm, UpperHalfPlane.ofComplex_apply]

end GlobalTheory.FN
end

