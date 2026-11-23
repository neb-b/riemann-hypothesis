module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Equiv

namespace CauchyBinetAlt

variable {R : Type*} [CommRing R] {j N : ℕ}

theorem det_mul_eq_sum (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R) :
    (A * B).det = ∑ p : Fin j → Fin N, (∏ i, B (p i) i) * (A.submatrix id p).det := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_mul_distrib]
  ring

theorem det_submatrix_eq_zero (A : Matrix (Fin j) (Fin N) R) {p : Fin j → Fin N}
    (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall, exists_prop] at hp
  obtain ⟨a, b, hab, hne⟩ := hp
  exact det_zero_of_column_eq hne fun k => by simp [hab]

theorem minor_mul (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) :
    (colsOf A I).det * (rowsOf B I).det =
      ∑ w : Perm (Fin j), (∏ i, B (I.1.orderEmbOfFin I.2 (w i)) i) *
        (A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w)).det := by
  rw [det_apply' (rowsOf B I), mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w) = (colsOf A I).submatrix id w := by
    ext a b
    rfl
  rw [h, det_permute']
  simp only [rowsOf, submatrix_apply, id]
  ring

theorem sum_reindex {M : Type*} [AddCommMonoid M] (g : (Fin j → Fin N) → M)
    (hg : ∀ p, ¬ Function.Injective p → g p = 0) :
    ∑ p, g p = ∑ I : {I : Finset (Fin N) // I.card = j}, ∑ w : Perm (Fin j),
      g (I.1.orderEmbOfFin I.2 ∘ w) := by
  rw [← Finset.sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hg p hp))]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij (fun x _ => x.1.1.orderEmbOfFin x.1.2 ∘ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨I, w⟩ _
    simp only [mem_filter, mem_univ, true_and]
    exact (I.1.orderEmbOfFin I.2).injective.comp w.injective
  · rintro ⟨I, w⟩ _ ⟨J, w'⟩ _ h
    simp only at h
    have key : ∀ (K : {I : Finset (Fin N) // I.card = j}) (v : Perm (Fin j)) (x : Fin N),
        x ∈ K.1 ↔ ∃ a, (K.1.orderEmbOfFin K.2 ∘ v) a = x := by
      intro K v x
      rw [← Finset.mem_coe, ← range_orderEmbOfFin K.1 K.2, Set.mem_range]
      exact ⟨fun ⟨a, ha⟩ => ⟨v.symm a, by simpa using ha⟩, fun ⟨a, ha⟩ => ⟨v a, ha⟩⟩
    have hIJ : I = J := by
      apply Subtype.ext
      ext x
      rw [key I w x, key J w' x, h]
    subst hIJ
    have hw : w = w' := Equiv.ext fun a => (I.1.orderEmbOfFin I.2).injective (congrFun h a)
    rw [hw]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hI : (univ.image p).card = j := by
      rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
    let w0 : Fin j → Fin j := fun a =>
      ((univ.image p).orderIsoOfFin hI).symm ⟨p a, mem_image_of_mem p (mem_univ a)⟩
    have hw0 : Function.Injective w0 := by
      intro a b hab
      exact hp (congrArg Subtype.val (((univ.image p).orderIsoOfFin hI).symm.injective hab))
    refine ⟨(⟨univ.image p, hI⟩, Equiv.ofBijective w0 (Finite.injective_iff_bijective.mp hw0)),
      mem_univ _, ?_⟩
    funext a
    show ((univ.image p).orderEmbOfFin hI) (w0 a) = p a
    rw [← coe_orderIsoOfFin_apply]
    simp only [w0, OrderIso.apply_symm_apply]
  · intro x _
    rfl

end CauchyBinetAlt

theorem CauchyBinet.proof : CauchyBinet.Statement := by
  intro R _ j N A B
  rw [CauchyBinetAlt.det_mul_eq_sum, CauchyBinetAlt.sum_reindex _ (fun p hp => by
    rw [CauchyBinetAlt.det_submatrix_eq_zero A hp, mul_zero])]
  exact Finset.sum_congr rfl fun I _ => (CauchyBinetAlt.minor_mul A B I).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace HermitianFormComparison

theorem sum_norm_sq_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * star U = 1)
    (x : Fin n → ℂ) : ∑ k, ‖(star U *ᵥ x) k‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have h1 : star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, star_eq_conjTranspose,
      conjTranspose_conjTranspose, ← star_eq_conjTranspose, hU, vecMul_one]
  rw [← h1]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem re_quad_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re = ∑ k, hA.eigenvalues k *
      ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) k‖ ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (↑hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hspec : A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := by
    have h := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set y : Fin n → ℂ := star U *ᵥ x with hy
  have hq : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (diagonal (fun k => (hA.eigenvalues k : ℂ)) *ᵥ y) := by
    conv_lhs => rw [hspec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hy, star_mulVec,
      star_eq_conjTranspose U, conjTranspose_conjTranspose]
  rw [hq]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem eigenvectorUnitary_mul_star {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2

theorem re_quad_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ (1 + ∑ k, hM.1.eigenvalues k) * (star x ⬝ᵥ x).re := by
  rw [re_quad_eq hM.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hM.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hle : hM.1.eigenvalues k ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (f := hM.1.eigenvalues) (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ k)
  linarith

theorem re_quad_ge {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef) (x : Fin n → ℂ) :
    (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (N *ᵥ x)).re := by
  rw [re_quad_eq hN.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hN.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hpos := hN.eigenvalues_pos k
  have hle : (hN.1.eigenvalues k)⁻¹ ≤ ∑ j, (hN.1.eigenvalues j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (hN.1.eigenvalues j)⁻¹)
      (fun j _ => (inv_pos.mpr (hN.eigenvalues_pos j)).le) (Finset.mem_univ k)
  rw [inv_le_comm₀ (by linarith [inv_pos.mpr hpos]) hpos]
  linarith

end HermitianFormComparison


open HermitianFormComparison in
theorem HermFormCompare.proof : HermFormCompare.Statement := by
  intro n M N hM hN
  set L : ℝ := 1 + ∑ k, hM.1.eigenvalues k with hL
  set m : ℝ := (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ with hm
  have hL0 : 0 < L := by
    have : 0 ≤ ∑ k, hM.1.eigenvalues k := Finset.sum_nonneg fun k _ => (hM.eigenvalues_pos k).le
    linarith
  have hm0 : 0 < m := by
    have : 0 ≤ ∑ k, (hN.1.eigenvalues k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (hN.eigenvalues_pos k)).le
    exact inv_pos.mpr (by linarith)
  refine ⟨L / m, div_pos hL0 hm0, fun x => ?_⟩
  have hup := re_quad_le hM.posSemidef x
  have hlo := re_quad_ge hN x
  calc (star x ⬝ᵥ (M *ᵥ x)).re ≤ L * (star x ⬝ᵥ x).re := hup
    _ = L / m * (m * (star x ⬝ᵥ x).re) := by field_simp
    _ ≤ L / m * (star x ⬝ᵥ (N *ᵥ x)).re :=
        mul_le_mul_of_nonneg_left hlo (div_pos hL0 hm0).le

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLogCardLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace logCardLength

open Module

variable (R : Type) [CommRing R]

def term (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) : ℝ :=
  ∑ᶠ (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))

def FinLoc (N : Type) [AddCommGroup N] [Module R N] : Prop :=
  ∀ (m : Ideal R) [m.IsPrime],
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) ≠ ⊤

variable {R}

lemma term_eq (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) [hm : m.IsMaximal] :
    term R N m = ((Module.length (Localization.AtPrime m)
      (LocalizedModule m.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (R ⧸ m)) := by
  classical
  rw [term, finsum_eq_if, if_pos hm, locLen, dite_eq_left hm.isPrime]

lemma term_of_not (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) (hm : ¬ m.IsMaximal) :
    term R N m = 0 := by
  classical
  rw [term, finsum_eq_if, if_neg hm]

lemma length_loc_add {N₀ N₁ N₂ : Type} [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₀] [Module R N₁] [Module R N₂] (f : N₀ →ₗ[R] N₁) (g : N₁ →ₗ[R] N₂)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (m : Ideal R) [m.IsPrime] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₁) =
      Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₀) +
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₂) :=
  Module.length_eq_add_of_exact
    ((IsLocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl N₀)
      (LocalizedModule.mkLinearMap m.primeCompl N₁) f).extendScalarsOfIsLocalization
        m.primeCompl (Localization.AtPrime m))
    ((IsLocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl N₁)
      (LocalizedModule.mkLinearMap m.primeCompl N₂) g).extendScalarsOfIsLocalization
        m.primeCompl (Localization.AtPrime m))
    (IsLocalizedModule.map_injective _ _ _ _ hf) (IsLocalizedModule.map_surjective _ _ _ _ hg)
    (LocalizedModule.map_exact m.primeCompl f g H)

lemma length_loc_simple (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (m : Ideal R) [hm : m.IsPrime] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl M) =
      if m = I then 1 else 0 := by
  split_ifs with h
  · subst h
    have hsurj : Function.Surjective (LocalizedModule.mkLinearMap m.primeCompl M) := by
      intro y
      refine LocalizedModule.induction_on (fun x s => ?_) y
      obtain ⟨t, i, hi, hts⟩ := hI.exists_inv (Ideal.mem_primeCompl_iff.mp s.2)
      refine ⟨t • x, ?_⟩
      rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have hx : ((s : R) * t) • x = x := by
        rw [show (s : R) * t = 1 - i by linear_combination hts, sub_smul, one_smul, hkill i hi x,
          sub_zero]
      simp only [one_smul, Submonoid.smul_def, smul_smul, hx]
    apply le_antisymm
    · calc Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl M)
          = Module.length (Localization.AtPrime m)
              (⊤ : Submodule (Localization.AtPrime m) (LocalizedModule m.primeCompl M)) :=
            Module.length_top.symm
        _ ≤ Module.length R
              ((⊤ : Submodule (Localization.AtPrime m) (LocalizedModule m.primeCompl M)).restrictScalars
                R) := Submodule.length_le_length_restrictScalars R ⊤
        _ = Module.length R (LocalizedModule m.primeCompl M) := by
            rw [Submodule.restrictScalars_top]; exact Module.length_top
        _ ≤ Module.length R M := Module.length_le_of_surjective _ hsurj
        _ = 1 := Module.length_eq_one R M
    · have : Nontrivial (LocalizedModule m.primeCompl M) := by
        rw [← not_subsingleton_iff_nontrivial, LocalizedModule.subsingleton_iff]
        push Not
        have := IsSimpleModule.nontrivial R M
        obtain ⟨x, hx⟩ := exists_ne (0 : M)
        refine ⟨x, fun r hr hrx => hx ?_⟩
        obtain ⟨t, i, hi, hts⟩ := hI.exists_inv (Ideal.mem_primeCompl_iff.mp hr)
        calc x = (t * r + i) • x := by rw [hts, one_smul]
          _ = 0 := by rw [add_smul, mul_smul, hrx, smul_zero, hkill i hi x, add_zero]
      exact Order.one_le_iff_pos.mpr Module.length_pos
  · rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    have hle : ¬ I ≤ m := fun hle => h (hI.eq_of_le hm.ne_top hle).symm
    obtain ⟨a, haI, ham⟩ := SetLike.not_le_iff_exists.mp hle
    exact fun x => ⟨a, Ideal.mem_primeCompl_iff.mpr ham, hkill a haI x⟩

lemma term_simple (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (hcard : Nat.card M = Nat.card (R ⧸ I)) (m : Ideal R) :
    term R M m = if m = I then Real.log (Nat.card M) else 0 := by
  by_cases hm : m.IsMaximal
  · rw [term_eq, length_loc_simple M I hI hkill m]
    split_ifs with h
    · subst h; simp [hcard]
    · simp
  · rw [term_of_not M m hm, if_neg (fun (h : m = I) => hm (h ▸ hI))]

theorem main (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module R N] [Finite N], Nat.card N = n →
    FinLoc R N ∧ (Function.support (term R N)).Finite ∧
      Real.log (Nat.card N) = ∑ᶠ m, term R N m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N _ _ _ hn
  rcases subsingleton_or_nontrivial N with hN | hN
  · have h0 : ∀ (m : Ideal R) [m.IsPrime],
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) = 0 :=
      fun m _ => Module.length_eq_zero
    have ht : ∀ m, term R N m = 0 := by
      intro m
      by_cases hm : m.IsMaximal
      · rw [term_eq, h0]; simp
      · exact term_of_not N m hm
    refine ⟨fun m _ => by rw [h0]; exact ENat.zero_ne_top,
      by rw [show term R N = 0 from funext ht, Function.support_zero]; exact Set.finite_empty, ?_⟩
    rw [Nat.card_of_subsingleton (0 : N)]
    simp [ht]
  · have := isArtinian_of_finite (R := R) (M := N)
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R N)
    rw [← isSimpleModule_iff_isAtom] at hS
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
    have hkill : ∀ a ∈ I, ∀ x : S, a • x = 0 := by
      intro a ha x
      apply e.injective
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e x)
      rw [map_smul, ← hr, map_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact I.mul_mem_right r ha
    have hcS : Nat.card S = Nat.card (R ⧸ I) := Nat.card_congr e.toEquiv
    have : Finite (N ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
    have hcard : Nat.card N = Nat.card S * Nat.card (N ⧸ S) := S.card_eq_card_quotient_mul_card
    have := IsSimpleModule.nontrivial R S
    have hS1 : 1 < Nat.card S := Finite.one_lt_card
    have hQpos : 0 < Nat.card (N ⧸ S) := Nat.card_pos
    have hlt : Nat.card (N ⧸ S) < n := by
      rw [← hn, hcard]; exact lt_mul_of_one_lt_left hQpos hS1
    obtain ⟨hQf, hQs, hQl⟩ := ih _ hlt (N ⧸ S) rfl
    have hadd : ∀ (m : Ideal R) [m.IsPrime],
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) =
          Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl S) +
            Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl (N ⧸ S)) :=
      fun m _ => length_loc_add S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
        (LinearMap.exact_subtype_mkQ S) m
    have hSt := term_simple S I hI hkill hcS
    have hterm : ∀ m, term R N m = term R S m + term R (N ⧸ S) m := by
      intro m
      by_cases hm : m.IsMaximal
      · have hQm := hQf m
        rw [term_eq, term_eq, term_eq, hadd, length_loc_simple S I hI hkill m] at *
        split_ifs <;> simp [ENat.toNat_add _ hQm]; ring
      · rw [term_of_not N m hm, term_of_not S m hm, term_of_not _ m hm, add_zero]
    have hSs : (Function.support (term R S)).Finite := by
      refine (Set.finite_singleton I).subset fun m hm => ?_
      by_contra h
      exact hm (by rw [hSt, if_neg (by simpa using h)])
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · rw [hadd, length_loc_simple S I hI hkill m]
      split_ifs <;> simpa using hQf m
    · exact (hSs.union hQs).subset (by
        rw [show term R N = fun m => term R S m + term R (N ⧸ S) m from funext hterm]
        exact Function.support_add _ _)
    · rw [show term R N = fun m => term R S m + term R (N ⧸ S) m from funext hterm,
        finsum_add_distrib hSs hQs, ← hQl,
        finsum_eq_single _ I (fun m hm => by rw [hSt, if_neg hm]), hSt, if_pos rfl, hcard,
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

end logCardLength


open logCardLength in
theorem LogCardLength.proof : LogCardLength.Statement := by
  intro R _ N _ _ _
  exact (main (Nat.card N) N rfl).2.2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerNormSq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset

noncomputable section

namespace PlueckerNormSqAlt

theorem onePipe_mul_conjTranspose {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    onePipe Z * (onePipe Z)ᴴ = 1 + Z * Zᴴ := by
  ext a b
  simp only [Matrix.mul_apply, conjTranspose_apply, onePipe, of_apply, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Matrix.add_apply]
  congr 1
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem rowsOf_conjTranspose {j N : ℕ} (A : Matrix (Fin j) (Fin N) ℂ)
    (I : {I : Finset (Fin N) // I.card = j}) : rowsOf Aᴴ I = (colsOf A I)ᴴ := by
  ext a b
  simp [rowsOf, colsOf, conjTranspose_apply]

end PlueckerNormSqAlt


open PlueckerNormSqAlt in
theorem PlueckerNormSq.proof (h : CauchyBinet.Statement) : PlueckerNormSq.Statement := by
  intro j m Z
  rw [← onePipe_mul_conjTranspose, h ℂ j (j + m) (onePipe Z) (onePipe Z)ᴴ]
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [rowsOf_conjTranspose, det_conjTranspose, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerUnitBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

namespace PlueckerUnitBoundAlt

theorem posSemidef_one_add {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    (1 + Z * Zᴴ).PosSemidef :=
  Matrix.PosSemidef.one.add (Matrix.posSemidef_self_mul_conjTranspose Z)

theorem diag_eq {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, ‖Z a b‖ = 1) (a : Fin j) :
    (1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a = (((1 + m : ℝ)) : ℂ) := by
  have hb : ∀ b, Z a b * Zᴴ b a = 1 := by
    intro b
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hZ a b]
    norm_num
  rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

end PlueckerUnitBoundAlt


open PlueckerUnitBoundAlt in
theorem PlueckerUnitBound.proof (h : HadamardPSD.Statement) : PlueckerUnitBound.Statement := by
  intro j m Z hZ
  calc ‖(1 + Z * Zᴴ).det‖ ≤ ∏ a, ‖(1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a‖ := h j _ (posSemidef_one_add Z)
    _ = ∏ _a : Fin j, (1 + m : ℝ) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [diag_eq Z hZ a, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ = (1 + m : ℝ) ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GroundTheory.Heights₂.Heights
end

