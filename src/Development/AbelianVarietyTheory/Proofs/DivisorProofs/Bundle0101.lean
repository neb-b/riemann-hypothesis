module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealEqOfExpNegTwoPiIDivEq
section
namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq (x y : ℝ) (k : ℕ) (hk : 0 < k)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) :
    ∃ n : ℤ, y - x = n * k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((y - x : ℝ) : ℂ) = ((n * k : ℝ) : ℂ) := by
    push_cast
    field_simp at hn
    linear_combination hn
  exact_mod_cast this

theorem real_eq_of_exp_neg_two_pi_I_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  intro x y h
  obtain ⟨m, hm⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y 1 one_pos (h 1 one_pos)
  simp only [Nat.cast_one, mul_one] at hm
  obtain ⟨n, hn⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y (m.natAbs + 1) (Nat.succ_pos _)
    (h _ (Nat.succ_pos _))
  generalize hK : m.natAbs + 1 = K at hn
  have hmn : m = n * (K : ℤ) := by
    have : ((m : ℤ) : ℝ) = ((n * (K : ℤ) : ℤ) : ℝ) := by push_cast; rw [← hm, hn]
    exact_mod_cast this
  have hm0 : m = 0 := by
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hmn)
    have h1 : m.natAbs = n.natAbs * K := by
      rw [hmn, Int.natAbs_mul]; simp
    have h2 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
    nlinarith
  have : y - x = 0 := by rw [hm, hm0]; simp
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplit
section
open Matrix Polynomial

namespace GlobalTheory

theorem reducedArtinian_exists_idem {R : Type} [CommRing R] [IsReduced R] [IsArtinianRing R]
    (a : R) : ∃ e b : R, e * e = e ∧ e = a * b ∧ a * e = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : R)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination ih + (-(a ^ k * y ^ k)) * hy
  have hm : a ^ (n + 1) = a ^ (n + 1 + (n + 1)) * y ^ (n + 1) := by
    linear_combination a * key (n + 1)
  refine ⟨a ^ (n + 1) * y ^ (n + 1), a ^ n * y ^ (n + 1), ?_, by ring, ?_⟩
  · linear_combination (-(y ^ (n + 1))) * hm
  · have h0 : (1 - a ^ (n + 1) * y ^ (n + 1)) * a ^ (n + 1) = 0 := by linear_combination hm
    have hnil : IsNilpotent ((1 - a ^ (n + 1) * y ^ (n + 1)) * a) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow, pow_succ (1 - a ^ (n + 1) * y ^ (n + 1)) n, mul_assoc, h0, mul_zero]
    have := hnil.eq_zero
    linear_combination -this

theorem reducedArtinian_involution_split :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by
  intro R _ _ _ σ hσ
  let S : Set (Ideal R) := {I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}
  have hS : S.Nonempty := ⟨_, 0, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  have hσe : σ e * σ e = σ e := by rw [← map_mul, he]
  set f := 1 - e - σ e with hfdef
  have hf : f * f = f := by linear_combination he + hσe + 2 * heσ
  have hσf : σ f = f := by simp only [hfdef, map_sub, map_one, hσ]; ring
  have hef : e * f = 0 := by linear_combination -he - heσ
  have hσef : σ e * f = 0 := by linear_combination -hσe - heσ
  refine ⟨e, f, he, hf, heσ, by ring, ?_⟩
  intro w hw
  by_contra hwf
  set w' := w * f with hw'def
  have hw'σ : w' * σ w' = 0 := by
    rw [hw'def, map_mul, hσf]; linear_combination (f * f) * hw
  obtain ⟨ε, a, hε, hεa, hw'ε⟩ := reducedArtinian_exists_idem w'
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hw'ε; exact hwf hw'ε.symm
  have hεσ : ε * σ ε = 0 := by
    rw [hεa, map_mul]; linear_combination (a * σ a) * hw'σ
  have hw'f : w' * f = w' := by rw [hw'def, mul_assoc, hf]
  have hεf : ε * f = ε := by rw [hεa]; linear_combination a * hw'f
  have hσεf : σ ε * f = σ ε := by
    have := congrArg σ hεf; rw [map_mul, hσf] at this; exact this
  have hσε : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have heε : e * ε = 0 := by linear_combination (-e) * hεf + ε * hef
  have heσε : e * σ ε = 0 := by linear_combination (-e) * hσεf + σ ε * hef
  have hσeε : σ e * ε = 0 := by linear_combination (-σ e) * hεf + ε * hσef
  have hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S :=
    ⟨e + ε, by linear_combination he + hε + 2 * heε,
      by rw [map_add (f := _)]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩
  apply hmin _ hmem
  have hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε) := by
    rw [map_add (f := _)]; linear_combination hf - hεf - hσεf
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨_, hff.symm⟩
  · intro hEq
    have : f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)} := by
      rw [hEq]; exact Ideal.mem_span_singleton_self f
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    apply hεne
    have hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0 := by
      rw [map_add (f := _)]; linear_combination -heε - hσeε - hε - hεσ
    linear_combination -hεf - ε * hc + c * hεg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFibresAlmostAllOfSeparableDedekindCurve
section
open Polynomial

namespace GlobalTheory

theorem reduced_fibres_almost_all_sep : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] (y : A), (Polynomial.aeval (R := k) y).Finite → Function.Injective (Polynomial.aeval (R := k) y) → Algebra.IsSeparable (IntermediateField.adjoin k {algebraMap A (FractionRing A) y}) (FractionRing A) → ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ y hfin hinj hsep
  letI : Algebra k[X] A := (Polynomial.aeval (R := k) y).toRingHom.toAlgebra
  have hmap : ∀ p : k[X], algebraMap k[X] A p = Polynomial.aeval y p := fun p => rfl
  haveI : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [hmap, Polynomial.algebraMap_apply, Polynomial.aeval_C]; rfl)
  haveI : Module.Finite k[X] A := hfin
  haveI : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective k[X] A).mpr hinj
  letI : Algebra (FractionRing k[X]) (FractionRing A) := FractionRing.liftAlgebra k[X] (FractionRing A)
  haveI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing A)
  set L := FractionRing A
  set K := FractionRing k[X]
  set ybar : L := algebraMap A L y
  set E := IntermediateField.adjoin k {ybar}
  have hpoly : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) = algebraMap A L (Polynomial.aeval y p) := by
    intro p
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k[X] A L]; rfl
  have hpolyE : ∀ p : k[X], algebraMap A L (Polynomial.aeval y p) ∈ E := by
    intro p
    have : algebraMap A L (Polynomial.aeval y p) = Polynomial.aeval ybar p := by
      rw [Polynomial.aeval_algebraMap_apply]
    rw [this]
    have hy : ybar ∈ E := IntermediateField.mem_adjoin_simple_self k ybar
    have := Polynomial.aeval_algHom_apply E.val (⟨ybar, hy⟩ : E) p
    simp only [IntermediateField.coe_val] at this
    rw [show ybar = ((⟨ybar, hy⟩ : E) : L) from rfl, this]
    exact (Polynomial.aeval (⟨ybar, hy⟩ : E) p).2
  have hrange : ∀ z : K, algebraMap K L z ∈ E := by
    intro z
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k[X]) z
    rw [map_div₀, hpoly, hpoly]
    exact div_mem (hpolyE a) (hpolyE b)
  let f : K →+* E := (algebraMap K L).codRestrict E hrange
  have hf : ∀ z : K, (f z : L) = algebraMap K L z := fun z => rfl
  let S : IntermediateField k L := (algebraMap K L).fieldRange.toIntermediateField (fun c =>
    ⟨algebraMap k[X] K (Polynomial.C c), by
      rw [hpoly, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]⟩)
  have hES : E ≤ S := IntermediateField.adjoin_simple_le_iff.2
    ⟨algebraMap k[X] K Polynomial.X, by rw [hpoly, Polynomial.aeval_X]⟩
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨z, hz⟩ := hES e.2
    exact ⟨z, Subtype.ext (by rw [hf]; exact hz)⟩
  let e₁ : E ≃+* K := (RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm
  have he : (algebraMap K L).comp (e₁ : E →+* K) = (RingEquiv.refl L : L →+* L).comp (algebraMap E L) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, RingEquiv.refl_apply]
    rw [← hf]
    change ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩) ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm x) : L) = _
    rw [RingEquiv.apply_symm_apply]; rfl
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_equiv_equiv e₁ (RingEquiv.refl L) he
  have hD := differentIdeal_ne_bot (A := k[X]) (B := A)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hc := Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨δ, hδ0, fun α hα Q hQ hmem' => hα ?_⟩
  have hmem : algebraMap k[X] A (X - C α) ∈ Q ^ 2 := by
    rw [hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]; exact hmem'
  set p : Ideal k[X] := Ideal.span {X - C α} with hpdef
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)
  have hp0 : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero α
  have hP : Q ^ 2 ∣ p.map (algebraMap k[X] A) := by
    rw [Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact hmem
  have hdiv := pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP
  rw [show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le] at hdiv
  have hδQ : δ ∈ Q.comap (algebraMap k[X] A) := hdiv hδ
  have hXQ : X - C α ∈ Q.comap (algebraMap k[X] A) :=
    Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)
  have hle : p ≤ Q.comap (algebraMap k[X] A) := by
    rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]; exact hXQ
  have heq : p = Q.comap (algebraMap k[X] A) :=
    hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle
  rw [← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot] at hδQ
  exact hδQ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEq
section
namespace GlobalTheory

open Subgroup

theorem relIndex_cocycle_of_ne_zero {A : Type} [Group A] (X Y Z : Subgroup A)
    (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0) (hYZ : Y.relIndex Z ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) (hXZ : X.relIndex Z ≠ 0) (hZX : Z.relIndex X ≠ 0) :
    Y.relIndex X * Z.relIndex Y * X.relIndex Z = X.relIndex Y * Y.relIndex Z * Z.relIndex X := by
  have a1 := relIndex_inf_mul_relIndex Y Z X
  have a2 := relIndex_inf_mul_relIndex Z Y X
  have b1 := relIndex_inf_mul_relIndex Z X Y
  have b2 := relIndex_inf_mul_relIndex X Z Y
  have c1 := relIndex_inf_mul_relIndex X Y Z
  have c2 := relIndex_inf_mul_relIndex Y X Z
  rw [inf_comm Z Y] at a2
  rw [inf_comm Y X] at c2
  rw [inf_comm X Z] at b2
  rw [inf_comm Z Y] at b2
  rw [inf_comm Y X] at a2
  rw [inf_comm X Z] at c2
  have ha : (Y ⊓ Z).relIndex X ≠ 0 := relIndex_inf_ne_zero hYX hZX
  have hb : (Z ⊓ X).relIndex Y ≠ 0 := relIndex_inf_ne_zero hZY hXY
  have hc : (X ⊓ Y).relIndex Z ≠ 0 := relIndex_inf_ne_zero hXZ hYZ
  have hpY : Y.relIndex (Z ⊓ X) ≠ 0 := by
    intro h; apply ha; rw [← a1, h, zero_mul]
  have hpZ : Z.relIndex (X ⊓ Y) ≠ 0 := by
    intro h; apply hb; rw [← b1, h, zero_mul]
  have hpX : X.relIndex (Y ⊓ Z) ≠ 0 := by
    intro h; apply hc; rw [← c1, h, zero_mul]
  have hP : 0 < Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_left hP
  calc Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) *
        (Y.relIndex X * Z.relIndex Y * X.relIndex Z)
      = (Z.relIndex (X ⊓ Y) * Y.relIndex X) * (X.relIndex (Y ⊓ Z) * Z.relIndex Y) *
        (Y.relIndex (Z ⊓ X) * X.relIndex Z) := by ring
    _ = (Y.relIndex (Z ⊓ X) * Z.relIndex X) * (Z.relIndex (X ⊓ Y) * X.relIndex Y) *
        (X.relIndex (Y ⊓ Z) * Y.relIndex Z) := by rw [a2, b2, c2, a1, b1, c1]
    _ = _ := by ring

theorem map_conj_mul {A : Type} [Group A] (K : Subgroup A) (x y : A) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem relIndex_map_conj {A : Type} [Group A] (H L : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).relIndex (L.map (MulAut.conj g).toMonoidHom) =
      H.relIndex L :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem map_conj_one {A : Type} [Group A] (K : Subgroup A) :
    K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x; simp

theorem relIndex_conj_pow_succ {A : Type} [Group A] (K : Subgroup A) (g : A) (i : ℕ) :
    (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ i)).toMonoidHom) =
      (K.map (MulAut.conj g).toMonoidHom).relIndex K ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom) =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  rw [pow_succ, map_conj_mul, relIndex_map_conj, relIndex_map_conj]
  exact ⟨rfl, rfl⟩

theorem relIndex_conj_pow_induction {A : Type} [Group A] (K : Subgroup A) (g : A)
    (ha : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0)
    (hb : K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0) (i : ℕ) :
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K ≠ 0 ∧
    K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) ≠ 0 ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K *
        (K.relIndex (K.map (MulAut.conj g).toMonoidHom)) ^ i =
      K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) *
        ((K.map (MulAut.conj g).toMonoidHom).relIndex K) ^ i := by
  induction i with
  | zero =>
    rw [pow_zero, map_conj_one]
    simp
  | succ i ih =>
    obtain ⟨hu, hv, hi⟩ := ih
    obtain ⟨sa, sb⟩ := relIndex_conj_pow_succ K g i
    set B := K.map (MulAut.conj (g ^ i)).toMonoidHom
    set C := K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom
    set a := (K.map (MulAut.conj g).toMonoidHom).relIndex K
    set b := K.relIndex (K.map (MulAut.conj g).toMonoidHom)
    have hCB : C.relIndex B ≠ 0 := by rw [sa]; exact ha
    have hBC : B.relIndex C ≠ 0 := by rw [sb]; exact hb
    have hCK : C.relIndex K ≠ 0 := relIndex_ne_zero_trans hCB hu
    have hKC : K.relIndex C ≠ 0 := relIndex_ne_zero_trans hv hBC
    have coc := relIndex_cocycle_of_ne_zero K B C hv hu hBC hCB hKC hCK
    rw [sa, sb] at coc
    refine ⟨hCK, hKC, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hv)
    calc C.relIndex K * b ^ (i + 1) * K.relIndex B
        = b * K.relIndex B * C.relIndex K * b ^ i := by ring
      _ = B.relIndex K * a * K.relIndex C * b ^ i := by rw [coc]; ring
      _ = a * K.relIndex C * (B.relIndex K * b ^ i) := by ring
      _ = K.relIndex C * a ^ (i + 1) * K.relIndex B := by rw [hi]; ring

theorem relIndex_conj_eq_of_pow_eq : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 →
    K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 →
    (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  intro A _ K g n hn ha hb heq
  obtain ⟨hu, _, hi⟩ := relIndex_conj_pow_induction K g ha hb n
  rw [heq] at hi hu
  have hpow := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hu) hi
  exact (Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp hn) hpow).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexISupMapEqPow
section
open NumberField

namespace GlobalTheory.SumIndex

theorem relIndex_pi_pi_of {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem eq_zero_of_sum_eq_zero {ι R V : Type} [Fintype ι] [DecidableEq ι] [Ring R] [AddCommGroup V]
    [Module R V] (S : ι → Submodule R V) (hS : iSupIndep S) (y : ι → V) (hy : ∀ a, y a ∈ S a)
    (h0 : ∑ a, y a = 0) (b : ι) : y b = 0 := by
  have hb : y b = -∑ a ∈ Finset.univ.erase b, y a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hmem : y b ∈ ⨆ (a) (_ : a ≠ b), S a := by
    rw [hb]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => ?_)
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase ha) (hy a))
  exact (Submodule.disjoint_def.1 (hS b)) _ (hy b) hmem

theorem relIndex_iSup_map_eq_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  intro K _ _ W V _ _ _ _ _ _ _ _ p M ℓ N hNℓ hinj hind
  classical
  let Φ : (Fin p → W) →ₗ[𝓞 K] V := ∑ a, ((M a).restrictScalars (𝓞 K)).comp (LinearMap.proj a)
  have hΦ : ∀ x, Φ x = ∑ a, M a (x a) := by intro x; simp [Φ]
  have himg : ∀ S : Submodule (𝓞 K) W, (Submodule.pi Set.univ (fun _ : Fin p => S)).map Φ =
      ⨆ a, S.map ((M a).restrictScalars (𝓞 K)) := by
    intro S
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ⟨x a, hx a (Set.mem_univ a), rfl⟩
    · refine iSup_le fun a => ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨Pi.single a w, ?_, ?_⟩
      · intro b _
        by_cases h : b = a
        · subst h; simpa using hw
        · simp [Pi.single_apply, h]
      · rw [hΦ, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
  let Lp : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => ℓ)
  let Np : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => N)
  have hNL : Np ≤ Lp := fun x hx a ha => hNℓ (hx a ha)
  let g : Lp.toAddSubgroup →+ V := Φ.toAddMonoidHom.comp Lp.toAddSubgroup.subtype
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun z hz => ?_
    have h0 : ∑ a, M a (z.1 a) = 0 := by rw [← hΦ]; exact hz
    have hy := eq_zero_of_sum_eq_zero _ hind (fun a => M a (z.1 a))
      (fun a => Submodule.subset_span ⟨z.1 a, z.2 a (Set.mem_univ a), rfl⟩) h0
    exact Subtype.ext (funext fun a => by simpa using hinj a (by simpa using hy a))
  have hL' : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup = (⊤ : AddSubgroup Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp [g, Lp]
  have hN' : (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      (Np.toAddSubgroup.addSubgroupOf Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
      AddSubgroup.mem_addSubgroupOf, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hNL hx, hx, rfl⟩
    · rintro ⟨x, _, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hL', hN', AddSubgroup.relIndex_map_map_of_injective _ _ hg, AddSubgroup.relIndex_top_right]
  change Np.toAddSubgroup.relIndex Lp.toAddSubgroup = _
  have e1 : Np.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => N.toAddSubgroup) := by
    ext x; simp [Np, AddSubgroup.mem_pi, Submodule.mem_pi]
  have e2 : Lp.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => ℓ.toAddSubgroup) := by
    ext x; simp [Lp, AddSubgroup.mem_pi, Submodule.mem_pi]
  rw [e1, e2, relIndex_pi_pi_of, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.SumIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariants
section
namespace GlobalTheory

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

attribute [local instance] Ideal.Quotient.field in
theorem Ideal.Quotient.normal_of_profinite
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
    [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) := by
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have hint' : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  refine normal_iff.2 fun ξ => ⟨Algebra.IsIntegral.isIntegral ξ, ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ξ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let B' := FixedPoints.subalgebra A B N.1.1
  let b' : B' := ⟨b, fun g => hN g.2⟩
  let Q' : Ideal B' := Q.under B'
  have hintB : Algebra.IsIntegral B' B := Algebra.IsIntegral.tower_top A
  have hQ' : Q'.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have : Q'.LiesOver P := ⟨by
    rw [Ideal.under_under (A := A) (B := B') (C := B)]
    exact Ideal.LiesOver.over⟩
  have hn : Normal (A ⧸ P) (B' ⧸ Q') := Ideal.Quotient.normal (G ⧸ N.1.1) P Q'
  let f : (B' ⧸ Q') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.val le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hf : Function.Injective f := f.toRingHom.injective
  have hfb : f (Ideal.Quotient.mk Q' b') = Ideal.Quotient.mk Q b := rfl
  rw [← hfb, minpoly.algHom_eq f hf]
  have hs := hn.splits (Ideal.Quotient.mk Q' b')
  have := hs.map f.toRingHom
  rw [Polynomial.map_map] at this
  have hc : (f : (B' ⧸ Q') →+* B ⧸ Q).comp (algebraMap (A ⧸ P) (B' ⧸ Q')) = algebraMap (A ⧸ P) (B ⧸ Q) := f.comp_algebraMap
  simpa only [AlgHom.toRingHom_eq_coe, hc] using this

end GlobalTheory
end

