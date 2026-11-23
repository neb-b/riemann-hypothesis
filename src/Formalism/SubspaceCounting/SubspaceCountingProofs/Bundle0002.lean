module

public import Formalism.SubspaceCounting.Bundle0001
public import Formalism.SubspaceCounting.SubspaceCountingProofs.Bundle0001
public import Formalism.SubspaceCounting.SubspaceCountingProofs.WalkSharp
public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition

@[expose] public section

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbits
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace ManyOrbitsP

theorem add_pow_ge (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k ≤ (p + q) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpq : 0 ≤ p + q := add_nonneg hp hq
    have h1 := mul_le_mul_of_nonneg_left ih hpq
    have h2 : 0 ≤ ((k : ℝ) + 1) * q ^ 2 * p ^ k := by positivity
    have e : (p + q) * (p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k) -
        (p ^ (k + 1 + 1) + (((k : ℝ) + 1) + 1) * q * p ^ (k + 1)) = ((k : ℝ) + 1) * q ^ 2 * p ^ k := by
      ring
    have e2 : (p + q) * (p + q) ^ (k + 1) = (p + q) ^ (k + 1 + 1) := by ring
    push_cast
    linarith

theorem fact_esymm_le (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    (n.factorial : ℝ) * s.esymm n ≤ s.sum ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
      simp
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ t.sum := Multiset.sum_nonneg ht
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      have e : (a ::ₘ t).esymm (n + 1) = t.esymm (n + 1) + a * t.esymm n := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      have h1 := ih ht (n + 1)
      have h2 := ih ht n
      have h3 := add_pow_ge t.sum a hS ha n
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * a)
      rw [e, Multiset.sum_cons, add_comm a t.sum]
      rw [Nat.factorial_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e5 : ((n : ℝ) + 1) * (n.factorial : ℝ) * (t.esymm (n + 1) + a * t.esymm n) =
          ((n : ℝ) + 1) * (n.factorial : ℝ) * t.esymm (n + 1) + ((n : ℝ) + 1) * a * ((n.factorial : ℝ) * t.esymm n) := by
        ring
      linarith [h1, h3, h4, e5]

section Mod

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem allBut_mono {π : R} {M P : Submodule R X} {g g' E E' : ℕ} (h : AllButLE π M P g E)
    (hg : g ≤ g') (hE : E ≤ E') : AllButLE π M P g' E' := by
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C, hCM, hcard.trans hg, fun x hx => ?_⟩
  have := Submodule.smul_mem _ (π ^ (E' - E)) (hC x hx)
  rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hE] at this

end Mod

end ManyOrbitsP

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.MarkedRun
section
namespace Formalism.G0

namespace MarkedRunP

theorem mem_cell_succ (r u s q x : ℕ) :
    x ∈ cell r u s (q + 1) ↔
      s * ((6 * r + 1) * u) + q * u ≤ x ∧ x < s * ((6 * r + 1) * u) + q * u + u := by
  simp only [cell, Finset.mem_Ico, Nat.add_sub_cancel, add_mul, one_mul, add_assoc]

end MarkedRunP

open MarkedRunP in
theorem marked_run : MarkedRun := by
  intro T r u s hu hM
  have hex : ∀ i : Fin (3 * r), ∃ x, T ∩ cell r u s (2 * i.val + 1 + 1) = {x} ∧ Even x :=
    fun i => (hM (2 * i.val + 1 + 1) (by omega) (by have := i.2; omega)).2 ⟨i.val + 1, by ring⟩
  choose f hf hfe using hex
  have hmem : ∀ i : Fin (3 * r), f i ∈ T ∧
      s * ((6 * r + 1) * u) + (2 * i.val + 1) * u ≤ f i ∧
      f i < s * ((6 * r + 1) * u) + (2 * i.val + 1) * u + u := by
    intro i
    have h1 : f i ∈ T ∩ cell r u s (2 * i.val + 1 + 1) := by
      rw [hf i]
      exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, MarkedRunP.mem_cell_succ] at h1
    exact ⟨h1.1, h1.2⟩
  have hgap : ∀ (i : Fin (3 * r)) (h : i.val + 1 < 3 * r), f i + u < f ⟨i.val + 1, h⟩ := by
    intro i h
    have a := (hmem i).2.2
    have b : s * ((6 * r + 1) * u) + (2 * (i.val + 1) + 1) * u ≤ f ⟨i.val + 1, h⟩ :=
      (hmem ⟨i.val + 1, h⟩).2.1
    nlinarith
  have hmono : StrictMono f := by
    intro i j hij
    have a := (hmem i).2.2
    have b := (hmem j).2.1
    have hij' : i.val + 1 ≤ j.val := hij
    have c := Nat.mul_le_mul_right u (show 2 * i.val + 2 ≤ 2 * j.val + 1 by omega)
    nlinarith
  have hbd : ∀ i : Fin (3 * r), s * ((6 * r + 1) * u) + u ≤ f i ∧
      f i + u < (s + 1) * ((6 * r + 1) * u) := by
    intro i
    have a := (hmem i).2.1
    have b := (hmem i).2.2
    have c := Nat.mul_le_mul_right u (show 2 * i.val + 3 ≤ 6 * r + 1 by have := i.2; omega)
    have d := Nat.zero_le (i.val * u)
    constructor <;> nlinarith
  refine ⟨f, hmono, ?_, hfe, hgap, hbd⟩
  ext y
  simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hyT, hy1, hy2⟩
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hy1
    have hu' : 0 < u := hu
    have hq1 : w / u * u ≤ w := Nat.div_mul_le_self w u
    have hq2 : w < w / u * u + u := Nat.lt_div_mul_add hu'
    have hw : w < (6 * r + 1) * u := by nlinarith
    have hq : w / u < 6 * r + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hq1 hw)
    generalize w / u = Q at hq1 hq2 hq
    have hc : s * ((6 * r + 1) * u) + w ∈ cell r u s (Q + 1) := by
      rw [MarkedRunP.mem_cell_succ]
      constructor
      · linarith
      · linarith
    rcases Nat.even_or_odd (Q + 1) with ⟨m, hm⟩ | ho
    · have hm1 : Q + 1 = 2 * (m - 1) + 1 + 1 := by omega
      have hi : m - 1 < 3 * r := by omega
      have hin : s * ((6 * r + 1) * u) + w ∈ T ∩ cell r u s (2 * (m - 1) + 1 + 1) := by
        rw [← hm1]
        exact Finset.mem_inter.2 ⟨hyT, hc⟩
      have := hf ⟨m - 1, hi⟩
      simp only at this
      rw [this, Finset.mem_singleton] at hin
      exact ⟨⟨m - 1, hi⟩, hin.symm⟩
    · have h0 := (hM (Q + 1) (by omega) (by omega)).1 ho
      have hin : s * ((6 * r + 1) * u) + w ∈ T ∩ cell r u s (Q + 1) :=
        Finset.mem_inter.2 ⟨hyT, hc⟩
      rw [h0] at hin
      exact absurd hin (Finset.notMem_empty _)
  · rintro ⟨i, rfl⟩
    have a := (hmem i).2.1
    have b := hbd i
    exact ⟨(hmem i).1, by nlinarith, by omega⟩

end Formalism.G0
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.TypeIIDown
section
namespace Formalism.G0

namespace TypeIIDownP

open QVandermondeP

theorem gb_self (q : ℕ) : ∀ n : ℕ, gaussBinom q n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [gb_succ_succ, gb_self q n, gb_eq_zero q n (n + 1) (by omega)]
    simp

theorem pascal2 (q M n : ℕ) :
    gaussBinom q (M + 1) (n + 1) = gaussBinom q M (n + 1) + q ^ (M - n) * gaussBinom q M n := by
  induction M generalizing n with
  | zero =>
    cases n with
    | zero =>
      rw [Formalism.G0.QVandermondeP.gb_succ_succ q 0 0,
        Formalism.G0.QVandermondeP.gb_zero_succ q 0,
        Formalism.G0.QVandermondeP.gb_zero_right q 0]
      simp
    | succ k =>
      rw [Formalism.G0.QVandermondeP.gb_eq_zero q (0 + 1) (k + 1 + 1) (by omega),
        Formalism.G0.QVandermondeP.gb_zero_succ q (k + 1),
        Formalism.G0.QVandermondeP.gb_zero_succ q k]
      simp
  | succ M ih =>
    cases n with
    | zero =>
      have s1 := Formalism.G0.QVandermondeP.gb_succ_succ q (M + 1) 0
      have s3 := Formalism.G0.QVandermondeP.gb_succ_succ q M 0
      have d1 := ih 0
      have z1 := Formalism.G0.QVandermondeP.gb_zero_right q (M + 1)
      have z0 := Formalism.G0.QVandermondeP.gb_zero_right q M
      calc gaussBinom q (M + 1 + 1) (0 + 1)
          = 1 + q ^ (0 + 1) * gaussBinom q (M + 1) (0 + 1) := by rw [s1, z1]
        _ = 1 + q ^ (0 + 1) * (gaussBinom q M (0 + 1) + q ^ (M - 0) * gaussBinom q M 0) := by
          rw [d1]
        _ = (gaussBinom q M 0 + q ^ (0 + 1) * gaussBinom q M (0 + 1)) + q ^ (M + 1 - 0) * 1 := by
          rw [z0, Nat.sub_zero, Nat.sub_zero]; ring
        _ = gaussBinom q (M + 1) (0 + 1) + q ^ (M + 1 - 0) * gaussBinom q (M + 1) 0 := by
          rw [s3, z1]
    | succ k =>
      have s1 := Formalism.G0.QVandermondeP.gb_succ_succ q (M + 1) (k + 1)
      have s2 := Formalism.G0.QVandermondeP.gb_succ_succ q M (k + 1)
      have s3 := Formalism.G0.QVandermondeP.gb_succ_succ q M k
      have d1 := ih k
      have d2 := ih (k + 1)
      have e : q ^ (k + 1 + 1) * (q ^ (M - (k + 1)) * gaussBinom q M (k + 1)) =
          q ^ (M - k) * (q ^ (k + 1) * gaussBinom q M (k + 1)) := by
        by_cases h : k + 1 ≤ M
        · rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          have hx : k + 1 + 1 + (M - (k + 1)) = M - k + (k + 1) := by omega
          rw [hx]
        · simp [Formalism.G0.QVandermondeP.gb_eq_zero q M (k + 1) (by omega)]
      rw [Nat.add_sub_add_right]
      calc gaussBinom q (M + 1 + 1) (k + 1 + 1)
          = gaussBinom q (M + 1) (k + 1) + q ^ (k + 1 + 1) * gaussBinom q (M + 1) (k + 1 + 1) := s1
        _ = (gaussBinom q M (k + 1) + q ^ (M - k) * gaussBinom q M k) +
              q ^ (k + 1 + 1) * (gaussBinom q M (k + 1 + 1) +
                q ^ (M - (k + 1)) * gaussBinom q M (k + 1)) := by rw [d1, d2]
        _ = gaussBinom q M (k + 1) + q ^ (M - k) * gaussBinom q M k +
              q ^ (k + 1 + 1) * gaussBinom q M (k + 1 + 1) +
              q ^ (k + 1 + 1) * (q ^ (M - (k + 1)) * gaussBinom q M (k + 1)) := by ring
        _ = gaussBinom q M (k + 1) + q ^ (M - k) * gaussBinom q M k +
              q ^ (k + 1 + 1) * gaussBinom q M (k + 1 + 1) +
              q ^ (M - k) * (q ^ (k + 1) * gaussBinom q M (k + 1)) := by rw [e]
        _ = (gaussBinom q M (k + 1) + q ^ (k + 1 + 1) * gaussBinom q M (k + 1 + 1)) +
              q ^ (M - k) * (gaussBinom q M k + q ^ (k + 1) * gaussBinom q M (k + 1)) := by ring
        _ = gaussBinom q (M + 1) (k + 1 + 1) + q ^ (M - k) * gaussBinom q (M + 1) (k + 1) := by
          rw [s2, s3]

theorem gb_symm (q : ℕ) : ∀ a b : ℕ, gaussBinom q (a + b) a = gaussBinom q (a + b) b
  | 0, b => by rw [Nat.zero_add, gb_zero_right, gb_self]
  | a + 1, 0 => by rw [Nat.add_zero, gb_zero_right, gb_self]
  | a + 1, b + 1 => by
    have hs : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
    rw [hs, gb_succ_succ q (a + b + 1) a, pascal2 q (a + b + 1) b]
    have i1 := gb_symm q a (b + 1)
    have i2 := gb_symm q (a + 1) b
    have h1 : a + (b + 1) = a + b + 1 := by omega
    have h2 : a + 1 + b = a + b + 1 := by omega
    rw [h1] at i1
    rw [h2] at i2
    have h3 : a + b + 1 - b = a + 1 := by omega
    rw [i1, i2, h3]
termination_by a b => a + b

end TypeIIDownP

end Formalism.G0

namespace Formalism.G0

namespace TypeIIDownP

open QVandermondeP

private theorem finrank_map_subtype_eq' {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (A : Submodule F W) (V : Submodule F A) :
    Module.finrank F (V.map A.subtype) = Module.finrank F V :=
  (Submodule.equivMapOfInjective A.subtype (fun _ _ h => Subtype.ext h) V).finrank_eq.symm

theorem countBelow_eq {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (k : ℕ) :
    countBelow A k = countBelow (⊤ : Submodule F A) k := by
  unfold Formalism.G0.countBelow
  exact Nat.card_congr
    { toFun := fun U => ⟨U.1.comap A.subtype, le_top, by
        rw [← finrank_map_subtype_eq' A (U.1.comap A.subtype), Submodule.map_comap_subtype,
          inf_eq_right.mpr U.2.1]
        exact U.2.2⟩
      invFun := fun V => ⟨V.1.map A.subtype, Submodule.map_subtype_le A V.1, by
        rw [finrank_map_subtype_eq']; exact V.2.2⟩
      left_inv := fun U => Subtype.ext (by
        show Submodule.map A.subtype (Submodule.comap A.subtype U.1) = U.1
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr U.2.1])
      right_inv := fun V => Subtype.ext (by
        show Submodule.comap A.subtype (Submodule.map A.subtype V.1) = V.1
        exact Submodule.comap_map_eq_of_injective (fun _ _ h => Subtype.ext h) V.1) }

private theorem finrank_map_mkQ_add_finrank_eq {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    [Module.Finite F Q] (R U : Submodule F Q) (h : R ≤ U) :
    Module.finrank F (U.map R.mkQ) + Module.finrank F R = Module.finrank F U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (R.mkQ.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h1
  rw [← h1, (Submodule.comapSubtypeEquivOfLe h).finrank_eq]

private theorem le_comap_mkQ' {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    (R : Submodule F Q) (V : Submodule F (Q ⧸ R)) : R ≤ V.comap R.mkQ := by
  intro x hx
  have h0 : R.mkQ x = 0 := by simpa using hx
  rw [Submodule.mem_comap, h0]
  exact V.zero_mem

private theorem mkQ_surjective' {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    (R : Submodule F Q) : Function.Surjective R.mkQ :=
  LinearMap.range_eq_top.mp (Submodule.range_mkQ R)

theorem countAboveCodim_eq {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q] [Finite Q]
    (R : Submodule F Q) (n j : ℕ) (hn : Module.finrank F Q = n) :
    Nat.card {U : Submodule F Q // R ≤ U ∧ Module.finrank F U + j = n} =
      Nat.card {V : Submodule F (Q ⧸ R) // Module.finrank F V + j = Module.finrank F (Q ⧸ R)} := by
  have : Module.Finite F Q := Module.Finite.of_finite
  have hQ := Submodule.finrank_quotient_add_finrank R
  exact Nat.card_congr
    { toFun := fun U => ⟨U.1.map R.mkQ, by
        have h1 := finrank_map_mkQ_add_finrank_eq R U.1 U.2.1
        have h2 := U.2.2
        omega⟩
      invFun := fun V => ⟨V.1.comap R.mkQ, le_comap_mkQ' R V.1, by
        have h1 := finrank_map_mkQ_add_finrank_eq R (V.1.comap R.mkQ) (le_comap_mkQ' R V.1)
        rw [Submodule.map_comap_eq_of_surjective (mkQ_surjective' R)] at h1
        have h2 := V.2
        omega⟩
      left_inv := fun U => Subtype.ext (by
        show Submodule.comap R.mkQ (Submodule.map R.mkQ U.1) = U.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr U.2.1])
      right_inv := fun V => Subtype.ext (by
        show Submodule.map R.mkQ (Submodule.comap R.mkQ V.1) = V.1
        exact Submodule.map_comap_eq_of_surjective (mkQ_surjective' R) V.1) }

end TypeIIDownP

end Formalism.G0

namespace Formalism.G0

namespace TypeIIDownP

open QVandermondeP

theorem codimCount (hS : SubspaceCount) {F W : Type} [Field F] [Fintype F] [AddCommGroup W]
    [Module F W] [Finite W] (n j : ℕ) (hn : Module.finrank F W = n) :
    Nat.card {V : Submodule F W // Module.finrank F V + j = n} =
      gaussBinom (Fintype.card F) n j := by
  have h : Formalism.G0.countBelow (⊤ : Submodule F W) (n - j) =
      gaussBinom (Fintype.card F) (Module.finrank F W) (n - j) := hS (n - j)
  unfold Formalism.G0.countBelow at h
  rw [hn] at h
  by_cases hj : j ≤ n
  · have e : Nat.card {V : Submodule F W // Module.finrank F V + j = n} =
        Nat.card {U : Submodule F W // U ≤ ⊤ ∧ Module.finrank F U = n - j} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun V => by
        simp only [le_top, true_and]
        constructor <;> intro h' <;> omega))
    rw [e, h]
    have hs := gb_symm (Fintype.card F) (n - j) j
    rw [Nat.sub_add_cancel hj] at hs
    exact hs
  · have : IsEmpty {V : Submodule F W // Module.finrank F V + j = n} :=
      ⟨fun V => hj (by have := V.2; omega)⟩
    rw [Nat.card_of_isEmpty, Formalism.G0.QVandermondeP.gb_eq_zero _ n j (by omega)]

end TypeIIDownP

open TypeIIDownP QVandermondeP

theorem typeIIDown_of (hS : SubspaceCount) : TypeIIDown := by
  intro F P Q _ _ _ _ _ _ _ _ f N g j hP hQ
  have : Module.Finite F P := Module.Finite.of_finite
  have : Module.Finite F Q := Module.Finite.of_finite
  have : Finite (Q ⧸ LinearMap.range f) :=
    Finite.of_surjective _ (_root_.Formalism.G0.TypeIIDownP.mkQ_surjective' (LinearMap.range f))
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hqr := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have hdim : Module.finrank F (Q ⧸ LinearMap.range f) =
      Module.finrank F (LinearMap.ker f) + g := by omega
  have h7 := Formalism.G0.TypeIIDownP.countAboveCodim_eq (LinearMap.range f) (N + g) j hQ
  have h8 := Formalism.G0.TypeIIDownP.codimCount hS (F := F) (W := Q ⧸ LinearMap.range f)
    (Module.finrank F (Q ⧸ LinearMap.range f)) j rfl
  have hK : ∀ k, countBelow (LinearMap.ker f) k =
      gaussBinom (Fintype.card F) (Module.finrank F (LinearMap.ker f)) k := fun k =>
    (Formalism.G0.TypeIIDownP.countBelow_eq (LinearMap.ker f) k).trans (hS k)
  rw [h7, h8, hdim, Formalism.G0.QVandermondeP.form2, Nat.cast_sum]
  simp only [hK]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  push_cast
  ring

end Formalism.G0

namespace Formalism.G0

theorem countAboveRangeCodimFormula : TypeIIDown :=
  typeIIDown_of countSubspacesEq

end Formalism.G0
end

