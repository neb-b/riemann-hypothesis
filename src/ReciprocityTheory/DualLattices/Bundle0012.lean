module

public import ReciprocityTheory.DualLattices.Bundle0008
public import ReciprocityTheory.DualLattices.Bundle0002
public import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd
public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.ValuationFourierLeOne
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem fourier_apply' {X H : Type} [Fintype X] (e : H → X → C) (u : X → C) (h : H) :
    fourier (R := R) e u h = ∑ a, u a * e h a := rfl

def pairInt {X : Type} [Fintype X] (U : X → C) : Submodule R (X → C) where
  carrier := {F | ∃ r : R, algebraMap R C r = ∑ x, U x * F x}
  add_mem' := by
    rintro F G ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by simp [hr, hs, mul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c F ⟨r, hr⟩
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

def conv (u w : N → C) : N → C := fun c => ∑ a, u a * w (c - a)

theorem fourier_conv {H : Type} (χ : H → AddChar N C) (u w : N → C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (conv u w) h =
      fourier (R := R) (fun h a => χ h a) u h * fourier (R := R) (fun h a => χ h a) w h := by
  rw [fourier_apply' (R := R), fourier_apply' (R := R), fourier_apply' (R := R),
    Finset.sum_mul_sum]
  simp only [conv, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.subRight a) _ _ fun c => ?_
  simp only [Equiv.subRight_apply]
  have hc : χ h c = χ h a * χ h (c - a) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [hc]
  ring

private theorem mem_dualLat_iff_sum_mul_integral {X : Type} [Fintype X] (M : Submodule R (X → C)) (u : X → C) :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl

private theorem mem_pairInt_iff {X : Type} [Fintype X] (U F : X → C) :
    F ∈ pairInt (R := R) U ↔ ∃ r : R, algebraMap R C r = ∑ x, U x * F x :=
  Iff.rfl

theorem conv_mem_dualLat (AA : HopfOrder (C := C) R N) {u w : N → C}
    (hu : u ∈ dualLat AA.carrier) (hw : w ∈ dualLat AA.carrier) :
    conv u w ∈ dualLat AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      pairInt (R := R) (fun p : N × N => u p.1 * w p.2) := by
    rw [tensorSpan, Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_pairInt_iff]
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hu g hg
    obtain ⟨s, hs⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hw k hk
    refine ⟨r * s, ?_⟩
    rw [map_mul, hr, hs, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := (mem_pairInt_iff _ _).1 (key (AA.comul f hf))
  refine ⟨r, hr.trans ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [addPull, LinearMap.funLeft_apply, conv, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => ?_
  simp

theorem single_mem_dualLat (AA : HopfOrder (C := C) R N) :
    (Pi.single 0 1 : N → C) ∈ dualLat AA.carrier := by
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := AA.le_int hf 0
  refine ⟨r, ?_⟩
  rw [hr]
  simp [Pi.single_apply]

def cpow (u : N → C) : ℕ → N → C
  | 0 => Pi.single 0 1
  | k + 1 => conv (cpow u k) u

theorem cpow_mem (AA : HopfOrder (C := C) R N) {u : N → C} (hu : u ∈ dualLat AA.carrier) :
    ∀ k, cpow u k ∈ dualLat AA.carrier
  | 0 => single_mem_dualLat AA
  | k + 1 => conv_mem_dualLat AA (cpow_mem AA hu k) hu

theorem fourier_single {H : Type} (χ : H → AddChar N C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (Pi.single 0 1) h = 1 := by
  rw [fourier_apply' (R := R)]
  simp [Pi.single_apply]

theorem fourier_cpow {H : Type} (χ : H → AddChar N C) (u : N → C) (h : H) :
    ∀ k, fourier (R := R) (fun h a => χ h a) (cpow u k) h =
      fourier (R := R) (fun h a => χ h a) u h ^ k
  | 0 => by rw [pow_zero]; exact fourier_single χ h
  | k + 1 => by
    simp only [cpow]
    rw [fourier_conv, fourier_cpow χ u h k, pow_succ]

private theorem nnreal_le_one_of_forall_pow_le {x M : NNReal} (h : ∀ k : ℕ, x ^ k ≤ M) : x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hx
  exact (not_lt.2 (h k)) hk

private theorem le_sum_sum {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ → NNReal) (i : ι)
    (j : κ) : f i j ≤ ∑ i, ∑ j, f i j :=
  (Finset.single_le_sum (f := fun j => f i j) (fun _ _ => zero_le) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, f i j) (fun _ _ => zero_le) (Finset.mem_univ i))

private theorem hopfOrder_exists_valuation_apply_le (v : Valuation C NNReal) (hv : v.Integers R)
    (AA : HopfOrder (C := C) R N) :
    ∃ M : NNReal, ∀ u ∈ dualLat AA.carrier, ∀ a, v (u a) ≤ M := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  refine ⟨∑ j, ∑ x, v (B⁻¹ j x), fun u hu a => ?_⟩
  rw [hA, mem_dualLat_spanCols_iff] at hu
  have hu' : u = (u ᵥ* B) ᵥ* B⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
  rw [hu']
  change v (∑ j, (u ᵥ* B) j * B⁻¹ j a) ≤ _
  apply v.map_sum_le
  intro j _
  obtain ⟨r, hr⟩ := hu j
  rw [map_mul, ← hr]
  exact (mul_le_of_le_one_left (zero_le) (hv.map_le_one r)).trans
    (le_sum_sum (fun j x => v (B⁻¹ j x)) j a)

theorem valuation_fourier_le_one (v : Valuation C NNReal) (hv : v.Integers R) {H : Type}
    (χ : H → AddChar N C) (AA : HopfOrder (C := C) R N) {u : N → C}
    (hu : u ∈ dualLat AA.carrier) (h : H) :
    v (fourier (R := R) (fun h a => χ h a) u h) ≤ 1 := by
  obtain ⟨M, hM⟩ := hopfOrder_exists_valuation_apply_le v hv AA
  have hχ : ∀ a, v (χ h a) ≤ 1 := fun a =>
    nnreal_le_one_of_forall_pow_le (M := ∑ b, v (χ h b)) fun k => by
      rw [← map_pow, ← AddChar.map_nsmul_eq_pow]
      exact Finset.single_le_sum (f := fun b => v (χ h b)) (fun _ _ => zero_le)
        (Finset.mem_univ _)
  apply nnreal_le_one_of_forall_pow_le (M := M)
  intro k
  rw [← map_pow, ← fourier_cpow (R := R) χ u h k, fourier_apply' (R := R)]
  apply v.map_sum_le
  intro a _
  rw [map_mul]
  exact (mul_le_of_le_one_right (zero_le) (hχ a)).trans
    (hM _ (cpow_mem AA hu k) a)

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.VdetLeOfSpanLe
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]

theorem vdet_le_of_span_le (hv : v.Integers R) {B B' : Matrix X X C}
    (hle : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det ≤ v B'.det := by
  have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
    (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
  choose w hw hBw using hcol
  have hBP : B = B' * Matrix.of fun x j => w j x := by
    ext x j
    have := congrFun (hBw j) x
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hle1 : v (Matrix.of fun x j => w j x).det ≤ 1 :=
    valuation_det_le_one v hv _ fun x j => hw j x
  rw [hBP, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right' hle1

theorem span_eq_of_vdet_eq (hv : v.Integers R) {B B' : Matrix X X C} (hB' : IsUnit B'.det)
    (hle : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) (hdet : v B.det = v B'.det) :
    Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j) := by
  refine le_antisymm hle ?_
  have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
    (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
  choose w hw hBw using hcol
  choose r hr using hw
  set W0 : Matrix X X R := Matrix.of fun x j => r j x with hW0
  have hBW : B = B' * W0.map (algebraMap R C) := by
    ext x j
    rw [show B x j = (B' *ᵥ w j) x from congrFun (hBw j) x]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W0, hr]
  have hne : v B'.det ≠ 0 := (Valuation.ne_zero_iff v).2 hB'.ne_zero
  have hW1 : v (algebraMap R C W0.det) = 1 := by
    have h := hdet
    rw [hBW, Matrix.det_mul, map_mul, det_map_algebraMap] at h
    exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
  have hU : IsUnit W0.det := hv.isUnit_of_one' hW1
  have hB'eq : B' = B * (W0⁻¹).map (algebraMap R C) := by
    rw [hBW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv W0 hU,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_spanCols_iff]
  refine ⟨fun k => algebraMap R C (W0⁻¹ k j), fun k => ⟨_, rfl⟩, ?_⟩
  ext x
  conv_lhs => rw [hB'eq]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable {p : ℕ} [hp : Fact p.Prime]

def finZ (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_cast_of_lt i.2)
  right_inv a := ZMod.natCast_zmod_val a

theorem finZ_val [NeZero p] (i : Fin p) : (finZ p i).val = i := ZMod.val_cast_of_lt i.2

theorem sum_val [NeZero p] : ∑ j : ZMod p, j.val = p * (p - 1) / 2 := by
  rw [← Finset.sum_range_id, Finset.sum_range (fun i => i)]
  exact (Fintype.sum_equiv (finZ p) (fun i : Fin p => (i : ℕ)) (fun j => j.val)
    (fun i => (finZ_val i).symm)).symm

theorem vdet_vandermonde [NeZero p] (ω : ZMod p → C)
    (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) :
    v (Matrix.of fun a j : ZMod p => ω a ^ j.val).det = 1 := by
  rw [← Matrix.det_submatrix_equiv_self (finZ p)]
  have e : (Matrix.of fun a j : ZMod p => ω a ^ j.val).submatrix (finZ p) (finZ p) =
      Matrix.vandermonde (ω ∘ finZ p) := by
    ext i j
    simp [Matrix.vandermonde, finZ_val]
  rw [e, Matrix.det_vandermonde, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_eq_one fun j hj => ?_
  exact hω _ _ fun h => (ne_of_gt (Finset.mem_Ioi.1 hj)) ((finZ p).injective h)

theorem vdet_pow [NeZero p] (ω : ZMod p → C) (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) (c : C) :
    v (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val).det = v c ^ (p * (p - 1) / 2) := by
  have e : (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val) =
      Matrix.of fun a j => c ^ j.val * (Matrix.of fun a j : ZMod p => ω a ^ j.val) a j := by
    ext a j
    simp [mul_pow]
  rw [e, Matrix.det_mul_row, map_mul, vdet_vandermonde ω hω, mul_one, map_prod]
  simp_rw [map_pow]
  rw [Finset.prod_pow_eq_pow_sum, sum_val]

end ReciprocityTheory.PGsh.Up.U3
end
end

-- bundled from ReciprocityTheory.DualLattices.ZmodTrichotomy
section
noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Principal

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

private lemma principal_inj (g : S)
    (h : ∀ m : M, g • m = 0 → (⟨g, mem_span_singleton_self g⟩ : span {g}) ⊗ₜ[S] m = 0) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul S M).comp (span {g}).subtype)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have ex : ∀ t : span {g} ⊗[S] M,
      ∃ m : M, t = (⟨g, mem_span_singleton_self g⟩ : span {g}) ⊗ₜ[S] m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (tmul_zero _ _).symm⟩
    | tmul i m =>
      obtain ⟨i, hi⟩ := i
      obtain ⟨r, rfl⟩ := mem_span_singleton'.1 hi
      refine ⟨r • m, ?_⟩
      rw [← smul_tmul]
      congr 1
    | add x y hx hy =>
      obtain ⟨m₁, rfl⟩ := hx
      obtain ⟨m₂, rfl⟩ := hy
      exact ⟨m₁ + m₂, (tmul_add _ _ _).symm⟩
  intro t ht
  obtain ⟨m, rfl⟩ := ex t
  rw [lift.tmul] at ht
  exact h m ht

end Principal

section ZModSq

variable (p : ℕ) [hp : Fact p.Prime]

private lemma p_sq_zero : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma zmod_trichotomy (g : ZMod (p ^ 2)) :
    IsUnit g ∨ (∃ u : ZMod (p ^ 2), IsUnit u ∧ g = (p : ZMod (p ^ 2)) * u) ∨ g = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hg : g = ((g.val : ℕ) : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val g).symm
  have unit_of : ∀ k : ℕ, ¬ p ∣ k → IsUnit ((k : ℕ) : ZMod (p ^ 2)) := by
    intro k hk
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk))
  by_cases h1 : p ∣ g.val
  · obtain ⟨k, hk⟩ := h1
    by_cases h2 : p ∣ k
    · right; right
      obtain ⟨l, hl⟩ := h2
      rw [hg, hk, hl, Nat.cast_mul, Nat.cast_mul, ← mul_assoc, ← sq, p_sq_zero, zero_mul]
    · right; left
      exact ⟨k, unit_of k h2, by rw [hg, hk, Nat.cast_mul]⟩
  · left
    rw [hg]; exact unit_of _ h1

private lemma zmod_ideal (J : Ideal (ZMod (p ^ 2))) :
    J = span {0} ∨ J = span {(p : ZMod (p ^ 2))} ∨ J = span {1} := by
  by_cases hu : ∃ g ∈ J, IsUnit g
  · right; right
    obtain ⟨g, hgJ, hg⟩ := hu
    rw [span_singleton_one]
    exact eq_top_of_isUnit_mem J hgJ hg
  · by_cases hz : ∀ g ∈ J, g = 0
    · left
      rw [span_singleton_eq_bot.2 rfl]
      exact eq_bot_iff.2 (fun g hg => (mem_bot).2 (hz g hg))
    · right; left
      push Not at hz
      obtain ⟨g, hgJ, hg0⟩ := hz
      apply le_antisymm
      · intro x hx
        rcases zmod_trichotomy p x with h | ⟨u, _, rfl⟩ | rfl
        · exact absurd ⟨x, hx, h⟩ hu
        · exact mem_span_singleton'.2 ⟨u, mul_comm _ _⟩
        · exact zero_mem _
      · rw [span_singleton_le_iff_mem]
        rcases zmod_trichotomy p g with h | ⟨u, hu', rfl⟩ | rfl
        · exact absurd ⟨g, hgJ, h⟩ hu
        · have : (p : ZMod (p ^ 2)) = p * u * ↑hu'.unit⁻¹ := by
            rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
          rw [this]
          exact J.mul_mem_right _ hgJ
        · exact absurd rfl hg0

theorem flat_of_ann {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ 2)) M]
    (h : ∀ m : M, (p : ZMod (p ^ 2)) • m = 0 → ∃ y : M, m = (p : ZMod (p ^ 2)) • y) :
    Module.Flat (ZMod (p ^ 2)) M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro J _
  rcases zmod_ideal p J with rfl | rfl | rfl
  · apply principal_inj
    intro m _
    have : (⟨0, mem_span_singleton_self 0⟩ : span {(0 : ZMod (p ^ 2))}) = 0 := rfl
    rw [this, zero_tmul]
  · apply principal_inj
    intro m hm
    obtain ⟨y, rfl⟩ := h m hm
    rw [← smul_tmul]
    have : (p : ZMod (p ^ 2)) • (⟨p, mem_span_singleton_self _⟩ : span {(p : ZMod (p ^ 2))}) = 0 := by
      apply Subtype.ext
      show (p : ZMod (p ^ 2)) * p = 0
      rw [← sq, p_sq_zero]
    rw [this, zero_tmul]
  · apply principal_inj
    intro m hm
    rw [one_smul] at hm
    rw [hm, tmul_zero]

end ZModSq

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem flatW' : FlatW'Statement p O := by
  intro pflat _
  set T : WittVector p (PreTilt O p) := teichmuller p pflat with hT
  set I : Ideal (WittVector p (PreTilt O p)) := span {(p : WittVector p (PreTilt O p)) ^ 2, T} with hI
  have hpc : ((p : ℕ) : WittVector p (PreTilt O p) ⧸ I) = Ideal.Quotient.mk I (p : WittVector p (PreTilt O p)) :=
    (map_natCast _ p).symm
  have hTI : Ideal.Quotient.mk I T = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (subset_span (by simp))
  have hann : ∀ x : WittVector p (PreTilt O p) ⧸ I, (p : WittVector p (PreTilt O p) ⧸ I) * x = 0 →
      ∃ y, x = (p : WittVector p (PreTilt O p) ⧸ I) * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hpc, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, mem_span_pair] at hx
    obtain ⟨c, d, hcd⟩ := hx
    have hd : d - teichmuller p (d.coeff 0) ∈ span {(p : WittVector p (PreTilt O p))} := by
      rw [mem_span_p_iff]
      have : constantCoeff (d - teichmuller p (d.coeff 0)) = 0 := by
        rw [map_sub, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, sub_self]
      exact this
    obtain ⟨e, he⟩ := mem_span_singleton'.1 hd
    have h1 : teichmuller p (d.coeff 0) * T = (a - c * p - e * T) * p := by
      have hd' : d = teichmuller p (d.coeff 0) + e * p := by rw [he]; ring
      rw [hd'] at hcd
      linear_combination hcd
    have h2 : teichmuller p (d.coeff 0) * T = 0 := by
      have hm : teichmuller p (d.coeff 0) * T ∈ span {(p : WittVector p (PreTilt O p))} :=
        mem_span_singleton'.2 ⟨_, h1.symm⟩
      rw [mem_span_p_iff, mul_coeff_zero, hT, teichmuller_coeff_zero, teichmuller_coeff_zero] at hm
      rw [hT, ← map_mul, hm, teichmuller_zero]
    have h3 : a = c * p + e * T := by
      have := p_mul_eq_zero _ (h1.symm.trans h2)
      linear_combination this
    refine ⟨Ideal.Quotient.mk I c, ?_⟩
    rw [hpc, h3, map_add (f := _), map_mul, map_mul, hTI]
    ring
  refine ⟨?_, ?_, hann, ?_⟩
  · apply le_antisymm
    · rw [span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mem_span_pair.2 ⟨1, 2 * p - T, by ring⟩, subset_span (by simp)⟩
    · rw [span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mem_span_pair.2 ⟨1, T - 2 * p, by ring⟩, subset_span (by simp)⟩
  · rw [hpc, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact subset_span (by simp)
  · intro _
    apply flat_of_ann
    intro m hm
    rw [Algebra.smul_def, map_natCast] at hm
    obtain ⟨y, hy⟩ := hann m hm
    exact ⟨y, by rw [Algebra.smul_def, map_natCast]; exact hy⟩

end Main

end ReciprocityTheory.PGsh
end
end

