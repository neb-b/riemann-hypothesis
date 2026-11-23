module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.CharpolyFactorAnnihilator
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem charpolyFactorAnnihilator : CharpolyFactorAnnihilator := by
  intro K V _ _ _ _ A B γ₀ γ c cγ t P hAB hA₀ hA hB₀ hB ht hchar
  classical
  let gA : Module.End K A := γ₀.restrict hA₀
  let gB : Module.End K B := c • LinearMap.id
  let e : (A × B) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl A B hAB

  have hconj : e.conj (gA.prodMap gB) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp [e, gA, gB, Submodule.coe_prodEquivOfIsCompl', hB₀ b b.2]

  have hcB : gB.charpoly = (X - C c) ^ t := by
    rw [← LinearMap.charpoly_toMatrix gB (Module.finBasis K B)]
    have hm : LinearMap.toMatrix (Module.finBasis K B) (Module.finBasis K B) gB =
        Matrix.diagonal (fun _ => c) := by
      simp only [gB, map_smul, LinearMap.toMatrix_id]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hm, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]
  have hPA : P = gA.charpoly := by
    have h1 : γ₀.charpoly = gA.charpoly * gB.charpoly := by
      rw [← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]
    rw [hchar, hcB] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) h1

  have hrestr : ∀ (p : K[X]) (a : A), (aeval γ₀ p) (a : V) = ((aeval gA p) a : V) := by
    intro p
    induction p using Polynomial.induction_on with
    | C r => intro a; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro a; simp [hp, hq]
    | monomial n r ih =>
      intro a
      rw [pow_succ, ← mul_assoc, map_mul (aeval γ₀), map_mul (aeval gA), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply]
      rw [show γ₀ (a : V) = ((gA a : A) : V) from rfl, ih]
  have h0 : aeval gA P = 0 := by
    rw [hPA]
    exact LinearMap.aeval_self_charpoly gA
  have hkill : ∀ w ∈ A, (aeval γ₀ P) w = 0 := by
    intro w hw
    have h2 := hrestr P ⟨w, hw⟩
    rw [h0] at h2
    simpa using h2
  apply LinearMap.ext
  intro v
  have hv : v ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply,
    Module.algebraMap_end_apply]
  have h3 : γ (a + b) - cγ • (a + b) = γ a - cγ • a := by
    rw [map_add (f := _), hB b hb, smul_add]
    abel
  rw [h3]
  exact hkill _ (A.sub_mem (hA a ha) (A.smul_mem cγ ha))

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.ContinuousCoeffCharpolyRev
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

section
variable {G R : Type} [TopologicalSpace G] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private def CoeffCont (P : G → R[X]) : Prop := ∀ j, Continuous fun g => (P g).coeff j

private theorem CoeffCont.const (p : R[X]) : CoeffCont (fun _ : G => p) := by
  intro j
  exact continuous_const

private theorem CoeffCont.mul {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g * Q g := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)

private theorem CoeffCont.sub {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g - Q g := by
  intro j
  simp only [Polynomial.coeff_sub]
  exact (hP j).sub (hQ j)

private theorem CoeffCont.sum {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∑ i ∈ s, P i g := by
  intro j
  simp only [Polynomial.finsetSum_coeff]
  exact continuous_finsetSum _ fun i hi => hP i hi j

private theorem CoeffCont.prod {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∏ i ∈ s, P i g := by
  classical
  revert hP
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using CoeffCont.const (G := G) (1 : R[X])
  · intro a s ha ih hP
    have h1 := hP a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    have h3 := CoeffCont.mul h1 h2
    simpa only [Finset.prod_insert ha] using h3

private theorem CoeffCont.C {f : G → R} (hf : Continuous f) :
    CoeffCont fun g => Polynomial.C (f g) := by
  intro j
  by_cases h : j = 0
  · subst h
    simpa using hf
  · simpa [Polynomial.coeff_C, h] using (continuous_const : Continuous fun _ : G => (0 : R))

theorem continuous_coeff_charpolyRev {n : ℕ} {r : G → Matrix (Fin n) (Fin n) R}
    (hr : Continuous r) (j : ℕ) : Continuous fun g => (Matrix.charpolyRev (r g)).coeff j := by
  have hsmul : ∀ (u : ℤˣ) {Q : G → R[X]}, CoeffCont Q → CoeffCont fun g => u • Q g := by
    intro u Q hQ j
    simp only [Units.smul_def, Polynomial.coeff_smul]
    exact (hQ j).const_smul (u : ℤ)
  have h : CoeffCont fun g => Matrix.charpolyRev (r g) := by
    simp only [Matrix.charpolyRev, Matrix.det_apply]
    refine CoeffCont.sum _ fun σ _ => ?_
    refine hsmul _ (CoeffCont.prod _ fun i _ => ?_)
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact CoeffCont.sub (CoeffCont.const _) (CoeffCont.mul (CoeffCont.const _) (CoeffCont.C (hr.matrix_elem _ _)))
  exact h j

end

theorem charpolyCoeffClosure : CharpolyCoeffClosure := by
  intro G _ R _ _ _ X _ n r T D hr hT hD hDT g j
  have hc : Continuous fun g => (fun x => (Matrix.charpolyRev (r x g)).coeff j) :=
    continuous_pi fun x => continuous_coeff_charpolyRev (hr x) j
  have hcl : IsClosed {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := hT.preimage hc
  have hsub : D ⊆ {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := fun g hg => hDT g hg j
  have hcs := hcl.closure_subset_iff.mpr hsub
  exact hcs (by rw [hD.closure_eq]; exact Set.mem_univ g)

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.FactorOverLocalSubalgebra
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem factorOverLocalSubalgebra : FactorOverLocalSubalgebra := by
  intro O _ _ X' _ T hT t c F s hF hs
  have := hT
  let c' : T := algebraMap O T c
  have hev_c : ∀ x, ev T x c' = c := fun x => by simp [ev, c']
  have hq : ((X - C c') ^ t : T[X]).Monic := (monic_X_sub_C c').pow t
  have hqO : ((X - C c) ^ t : O[X]).Monic := (monic_X_sub_C c).pow t
  have hqmap : ∀ x, ((X - C c') ^ t : T[X]).map (ev T x) = (X - C c) ^ t := by
    intro x
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hev_c]
  have hR : F %ₘ (X - C c') ^ t = 0 := by
    ext n x
    have h1 : (F %ₘ (X - C c') ^ t).map (ev T x) = 0 := by
      rw [map_modByMonic _ hq, hqmap, hF, (modByMonic_eq_zero_iff_dvd hqO).mpr (dvd_mul_left _ _)]
    have h2 := congrArg (fun p => p.coeff n) h1
    simpa [Polynomial.coeff_map, ev] using h2
  have hmapP : ∀ x, (F /ₘ (X - C c') ^ t).map (ev T x) = s x := by
    intro x
    rw [map_divByMonic _ hq, hqmap, hF, mul_comm, mul_divByMonic_cancel_left _ hqO]
  refine ⟨F /ₘ (X - C c') ^ t, ?_, ?_, hmapP⟩
  · have h := modByMonic_add_div F ((X - C c') ^ t)
    rw [hR, zero_add] at h
    rw [mul_comm]
    exact h.symm
  · obtain ⟨x⟩ : Nonempty X' := by
      by_contra h
      rw [not_nonempty_iff] at h
      have hsub : Subsingleton T := ⟨fun a b => Subtype.ext (funext fun x => (IsEmpty.false x).elim)⟩
      exact not_subsingleton T hsub
    have := IsLocalHom.of_surjective (ev T x) (fun o => ⟨algebraMap O T o, by simp [ev]⟩)
    apply isUnit_of_map_unit (ev T x)
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmapP, hev_c]
    exact hs x

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.LiftingTheExponent
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem sum_one_add_val (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 + padicValNat l (i + 1)) = n + padicValNat l n.factorial := by
  induction n with
  | zero => simp [Nat.padicValNat_def]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
    simp only [Nat.succ_eq_add_one]
    omega

theorem two_mul_val_factorial_le (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (n : ℕ) :
    2 * padicValNat l n.factorial ≤ n := by
  have h3 : 3 ≤ l := by have := hl.out.two_le; omega
  have key : (l - 1) * padicValNat l n.factorial = n - (l.digits n).sum := by
    simpa only [Nat.padicValNat_def] using (hl.out.sub_one_mul_multiplicity_factorial (n := n))
  have hle : (l - 1) * padicValNat l n.factorial ≤ n := by rw [key]; exact Nat.sub_le _ _
  have h2le : 2 * padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

private theorem padicValInt_neg_natCast_add_one (l i : ℕ) :
    padicValInt l (-((i : ℤ) + 1)) = padicValNat l (i + 1) := by
  simp only [padicValInt]
  rw [show (-((i : ℤ) + 1)).natAbs = i + 1 by omega, Nat.padicValNat_def]

private theorem padicValInt_natCast_add_one (l i : ℕ) :
    padicValInt l ((i : ℤ) + 1) = padicValNat l (i + 1) := by
  simp only [padicValInt]
  rw [show ((i : ℤ) + 1).natAbs = i + 1 by omega, Nat.padicValNat_def]

theorem valuationSumBound : LiftExp := by
  intro l h J hl hl2 hJ h0
  have : Fact l.Prime := ⟨hl⟩
  set f : ℤ → ℕ := fun j => 1 + padicValInt l j with hf
  set A : Finset ℤ := (Finset.range h).image (fun i : ℕ => -((i : ℤ) + 1)) with hA
  set B : Finset ℤ := (Finset.range (2 * h)).image (fun i : ℕ => (i : ℤ) + 1) with hB
  have hsub : J ⊆ A ∪ B := by
    intro j hj
    have hm := Finset.mem_Icc.mp (hJ hj)
    have hj0 : j ≠ 0 := fun e => h0 (e ▸ hj)
    rw [Finset.mem_union, hA, hB, Finset.mem_image, Finset.mem_image]
    rcases lt_or_gt_of_ne hj0 with hneg | hpos
    · left
      exact ⟨(-j - 1).toNat, by rw [Finset.mem_range]; omega, by omega⟩
    · right
      exact ⟨(j - 1).toNat, by rw [Finset.mem_range]; omega, by omega⟩
  have hA_sum : ∑ j ∈ A, f j = h + padicValNat l h.factorial := by
    rw [hA, Finset.sum_image (fun x _ y _ e => by simpa using e)]
    rw [← sum_one_add_val l h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, padicValInt_neg_natCast_add_one]
  have hB_sum : ∑ j ∈ B, f j = 2 * h + padicValNat l (2 * h).factorial := by
    rw [hB, Finset.sum_image (fun x _ y _ e => by simpa using e)]
    rw [← sum_one_add_val l (2 * h)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, padicValInt_natCast_add_one]
  have hJle : ∑ j ∈ J, f j ≤ ∑ j ∈ A ∪ B, f j := Finset.sum_le_sum_of_subset hsub
  have hU := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have e1 := two_mul_val_factorial_le l hl2 (2 * (2 * h))
  have e2 := two_mul_val_factorial_le l hl2 h
  have e3 := two_mul_val_factorial_le l hl2 (2 * h)
  have hJ' : ∑ j ∈ J, (1 + padicValInt l j) = ∑ j ∈ J, f j := rfl
  rw [hJ']
  omega

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.PadicDigits
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem padicValIntShiftLe : DigitLemma := by
  intro l a c ρ m hl ha hc0 hcN hρ hdvd hm
  have := Fact.mk hl
  have hl2 : (2:ℤ) ≤ (l:ℤ) := by exact_mod_cast hl.two_le
  have hla : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl.pos
  have hlr : 1 ≤ l ^ ρ := Nat.one_le_pow _ _ hl.pos
  have hNc : ((l ^ a - 1 : ℕ) : ℤ) = (l:ℤ) ^ a - 1 := by
    rw [Nat.cast_sub hla]; push_cast; rfl
  have hcN' : (c:ℤ) < (l:ℤ) ^ a - 1 := by rw [← hNc]; exact_mod_cast hcN
  have hc0' : (0:ℤ) < c := by exact_mod_cast hc0
  have hdvd' : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) * ((l:ℤ) ^ ρ - 1) := by
    have h1 := Int.natCast_dvd_natCast.mpr hdvd
    rw [hNc] at h1
    have h2 : ((c * (l ^ ρ - 1) : ℕ) : ℤ) = (c:ℤ) * ((l:ℤ) ^ ρ - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hlr]; push_cast; rfl
    rw [h2] at h1; exact h1
  have hP : (2:ℤ) ≤ (l:ℤ) ^ ρ := by
    obtain ⟨r, rfl⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
    have : (1:ℤ) ≤ (l:ℤ) ^ r := one_le_pow₀ (by linarith)
    rw [pow_succ]; nlinarith
  by_contra hv
  push Not at hv
  have hdx : (l:ℤ) ^ (ρ + 1) ∣ (c:ℤ) + m * ((l:ℤ) ^ a - 1) :=
    (padicValInt_dvd_iff (ρ + 1) _).2 (Or.inr (by omega))
  obtain ⟨t, ht⟩ := hdx
  have hxN : ((l:ℤ) ^ a - 1) ∣ (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1)) := by
    have e : (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1))
        = (c:ℤ) * ((l:ℤ) ^ ρ - 1) + ((l:ℤ) ^ a - 1) * (m * ((l:ℤ) ^ ρ - 1)) := by
      rw [← mul_assoc, ← ht]; ring
    rw [e]; exact dvd_add hdvd' (dvd_mul_right _ _)
  have hcop : IsCoprime ((l:ℤ) ^ a - 1) ((l:ℤ) ^ (ρ + 1)) := by
    apply IsCoprime.pow_right
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact ⟨-1, (l:ℤ) ^ b, by ring⟩
  have hy : ((l:ℤ) ^ a - 1) ∣ t * ((l:ℤ) ^ ρ - 1) := by
    exact hcop.dvd_of_dvd_mul_left hxN
  have hm' := abs_lt.mp hm
  have hNpos : (0:ℤ) < (l:ℤ) ^ a - 1 := by linarith
  have hxlt : |(c:ℤ) + m * ((l:ℤ) ^ a - 1)| < (l:ℤ) * ((l:ℤ) ^ a - 1) := by
    have u1 : 0 ≤ ((l:ℤ) - 1 - m) * ((l:ℤ) ^ a - 1) :=
      mul_nonneg (by linarith) hNpos.le
    have u2 : 0 ≤ (m + (l:ℤ) - 1) * ((l:ℤ) ^ a - 1) :=
      mul_nonneg (by linarith) hNpos.le
    rw [abs_lt]; constructor <;> nlinarith
  have htlt : (l:ℤ) ^ ρ * |t| < (l:ℤ) ^ a - 1 := by
    rw [ht, abs_mul, abs_of_pos (by positivity : (0:ℤ) < (l:ℤ) ^ (ρ + 1)), pow_succ] at hxlt
    have hl0 : (0:ℤ) < l := by linarith
    nlinarith
  have hylt : |t * ((l:ℤ) ^ ρ - 1)| < (l:ℤ) ^ a - 1 := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℤ) < (l:ℤ) ^ ρ - 1)]
    nlinarith [abs_nonneg t]
  have hy0 := Int.eq_zero_of_abs_lt_dvd hy hylt
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp hy0 with h | h
    · exact h
    · linarith
  rw [ht0, mul_zero] at ht
  have hcd : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) := ⟨-m, by linarith⟩
  have hcz := Int.eq_zero_of_abs_lt_dvd hcd (by rw [abs_of_pos hc0']; exact hcN')
  linarith

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.PadicValCardGL
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem padicValNat_finset_prod {ι : Type} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i ≠ 0) : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp [Nat.padicValNat_def]) ?_
  intro a t ha ih h
  have hrest : ∀ i ∈ t, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
  rw [Finset.prod_insert ha, Finset.sum_insert ha,
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (h a (Finset.mem_insert_self a t)) (Finset.prod_ne_zero_iff.mpr hrest),
    ih hrest]

private theorem pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt (q r i : ℕ) (hq : 0 < q) (hi : i < r) :
    q ^ r - q ^ i = q ^ i * (q ^ (r - i) - 1) := by
  have h1 : q ^ r = q ^ i * q ^ (r - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.le]
  have h2 : 1 ≤ q ^ (r - i) := Nat.one_le_pow _ _ hq
  obtain ⟨k, hk⟩ : ∃ k, q ^ (r - i) = k + 1 := ⟨q ^ (r - i) - 1, (Nat.sub_add_cancel h2).symm⟩
  rw [h1, hk]
  simp [mul_add]

theorem padicValNat_prod_pow_sub (g q r : ℕ) [Fact g.Prime] (hq : 2 ≤ q) :
    padicValNat g (∏ i ∈ Finset.range r, (q ^ r - q ^ i)) =
      (∑ i ∈ Finset.range r, i) * padicValNat g q +
        ∑ a ∈ Finset.Icc 1 r, padicValNat g (q ^ a - 1) := by
  have hq0 : 0 < q := by omega
  have hbig : ∀ i ∈ Finset.range r, q ^ (r - i) - 1 ≠ 0 := by
    intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have h3 : q ≤ q ^ (r - i) := by
      simpa using Nat.pow_le_pow_right hq0 (show 1 ≤ r - i by omega)
    omega
  have hne : ∀ i ∈ Finset.range r, q ^ r - q ^ i ≠ 0 := by
    intro i hi
    rw [pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi)]
    exact Nat.mul_ne_zero (pow_ne_zero _ hq0.ne') (hbig i hi)
  have term : ∀ i ∈ Finset.range r, padicValNat g (q ^ r - q ^ i) =
      i * padicValNat g q + padicValNat g (q ^ (r - i) - 1) := by
    intro i hi
    rw [pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hq0.ne') (hbig i hi), Nat.padicValNat_def, Nat.multiplicity_pow, ← Nat.padicValNat_def]
  rw [padicValNat_finset_prod g _ _ hne, Finset.sum_congr rfl term, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  congr 1
  apply Finset.sum_nbij' (fun i => r - i) (fun a => r - a)
  all_goals intro a ha
  all_goals (try simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢)
  all_goals (first | rfl | omega)

theorem card_GL_zmod (q r : ℕ) [Fact q.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) =
      ∏ i ∈ Finset.range r, (q ^ r - q ^ i) := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [Matrix.card_GL_field, ZMod.card]
  exact Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i) r

theorem padicValCardGeneralLinear : GLCardVal := by
  unfold GLCardVal
  intro g g' r instg instg' hne
  have hg : g.Prime := instg.out
  have hg' : g'.Prime := instg'.out
  constructor
  · rw [card_GL_zmod, padicValNat_prod_pow_sub g g r hg.two_le, Nat.padicValNat_def, Nat.Prime.multiplicity_self,
      mul_one, Finset.sum_range_id, Finset.sum_eq_zero, add_zero]
    intro a ha
    rw [Nat.padicValNat_def]
    apply multiplicity_eq_zero_of_not_dvd
    intro hd
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have h1 : g ∣ g ^ a := dvd_pow_self g (by omega)
    have h2 : 1 ≤ g ^ a := Nat.one_le_pow _ _ hg.pos
    have h3 : g ∣ g ^ a - (g ^ a - 1) := by
      first
        | exact Nat.dvd_sub' h1 hd
        | exact Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self h2] at h3
    exact hg.one_lt.ne' (Nat.dvd_one.mp h3)
  · rw [card_GL_zmod, padicValNat_prod_pow_sub g g' r hg'.two_le]
    have h0 : padicValNat g g' = 0 :=
      by
        rw [Nat.padicValNat_def]
        exact multiplicity_eq_zero_of_not_dvd fun hd => hne ((Nat.prime_dvd_prime_iff_eq hg hg').mp hd)
    rw [h0, mul_zero, zero_add]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TOPSgLe
section
namespace Formalism.IrreducibleCountingLemmas.TOP

private theorem tsum_mul_inv_pow_succ_eq_div_sub_one (ℓ : ℕ) (H : ℝ) (hℓ : (2 : ℝ) ≤ ℓ) :
    ∑' j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = H / ((ℓ : ℝ) - 1) := by
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hl0 : (ℓ : ℝ) ≠ 0 := by positivity
  have hl1 : (ℓ : ℝ) - 1 ≠ 0 := by intro h; linarith
  have e : ∀ j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = (H * (ℓ : ℝ)⁻¹) * ((ℓ : ℝ)⁻¹) ^ j := by
    intro j; ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e2 : (1 : ℝ) - (ℓ : ℝ)⁻¹ = ((ℓ : ℝ) - 1) / ℓ := by field_simp
  rw [e2]
  field_simp

theorem carryFloorLeGeom : SgLe := by
  intro f _ ℓ h H hℓ hH i
  unfold sg
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom : Summable (fun j : ℕ => (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left ((H : ℝ) * (ℓ : ℝ)⁻¹)
    refine this.congr ?_
    intro j; ring
  have hle : ∀ j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) ≤
      (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1) := by
    intro j
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hH _) (by positivity)
  have hnn : ∀ j : ℕ, 0 ≤ (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) :=
    fun j => by positivity
  have hs : Summable (fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)) :=
    hgeom.of_nonneg_of_le hnn hle
  have h1 := hs.tsum_le_tsum hle hgeom
  rw [tsum_mul_inv_pow_succ_eq_div_sub_one ℓ H hℓ'] at h1
  exact (Int.floor_le _).trans h1

end Formalism.IrreducibleCountingLemmas.TOP
end

