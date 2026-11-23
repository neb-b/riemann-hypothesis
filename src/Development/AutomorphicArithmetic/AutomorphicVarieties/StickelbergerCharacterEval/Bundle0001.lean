module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0003
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chcard
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private def chOne {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) :
    Ch Ω c 1 ≃ ((Γ ⧸ Subgroup.zpowers c) →* Ωˣ) where
  toFun χ := QuotientGroup.lift (Subgroup.zpowers c) χ.1 (by
    have h : χ.1 c = 1 := Units.ext (by simpa using χ.2)
    rintro _ ⟨n, rfl⟩
    simp [h])
  invFun ψ := ⟨ψ.comp (QuotientGroup.mk' _), by
    have h : (QuotientGroup.mk c : Γ ⧸ Subgroup.zpowers c) = 1 :=
      (QuotientGroup.eq_one_iff c).2 (Subgroup.mem_zpowers c)
    simp [h]⟩
  left_inv χ := Subtype.ext (MonoidHom.ext fun g => rfl)
  right_inv ψ := MonoidHom.ext fun g => by
    induction g using QuotientGroup.induction_on with
    | H g => rfl

private def chMul {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (χ₀ : Ch Ω c ε) :
    Ch Ω c 1 ≃ Ch Ω c ε where
  toFun χ := ⟨χ₀.1 * χ.1, by simp [χ₀.2, χ.2]⟩
  invFun χ := ⟨χ₀.1⁻¹ * χ.1, by
    have h : χ.1 c = χ₀.1 c := Units.ext (χ.2.trans χ₀.2.symm)
    simp [h]⟩
  left_inv χ := Subtype.ext (inv_mul_cancel_left _ _)
  right_inv χ := Subtype.ext (mul_inv_cancel_left _ _)

theorem UpperTheory.V.B5.card_signedInvolutionChar_eq_card_involutionQuotient :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → Fintype.card (Ch Ω c ε) = Fintype.card (Qc c) := by
  intro Ω _ Γ _ _ _ c ε h2 hc hε
  classical
  have hne₀ : Nonempty (Ch Ω c ε) := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hε with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨⟨1, by simp⟩⟩
    · obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Γ Ω hc
      refine ⟨⟨φ, ?_⟩⟩
      have hsq : (φ c : Ω) * (φ c : Ω) = 1 := by
        rw [← Units.val_mul, ← map_mul, h2, map_one, Units.val_one]
      have hne : (φ c : Ω) ≠ 1 := fun h => hφ (Units.ext (by simpa using h))
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact absurd h hne
      · simpa using h
  obtain ⟨χ₀⟩ := hne₀
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity Ω (Monoid.exponent (Γ ⧸ Subgroup.zpowers c)) :=
    HasEnoughRootsOfUnity.of_dvd Ω (Group.exponent_quotient_dvd _)
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.card_congr ((chMul c ε χ₀).symm.trans (chOne c)),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chitheta
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerTheta_eq_neg_genBernoulli :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (k : ℕ), 2 ≤ N → ev ℚ χ (thetaEl k π) = -genB k (dirOf π χ) / k := by
  intro Ω _ _ N _ Γ _ π χ k hN
  haveI : Fact (1 < N) := ⟨hN⟩
  have hsum : ∀ f : ZMod N → Ω, (∀ x, ¬ IsUnit x → f x = 0) →
      ∑ x, f x = ∑ u : (ZMod N)ˣ, f u := by
    intro f hf
    symm
    rw [show ∑ u : (ZMod N)ˣ, f u = ∑ x ∈ Finset.univ.map ⟨Units.val, Units.val_injective⟩, f x by
      rw [Finset.sum_map]; rfl]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hf
    rintro ⟨u, rfl⟩
    exact hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)
  have h1 : ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k a) =
      ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k (a : ZMod N).val) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨_, h2⟩ := Finset.mem_Icc.1 ha
    rcases h2.lt_or_eq with h | rfl
    · rw [ZMod.val_cast_of_lt h]
    · rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaEl, sumEl, map_neg, map_sum, ev_single, genB, Ek]
  rw [h1, b_sumicc (fun x : ZMod N => dirOf π χ x * algebraMap ℚ Ω (bcoef N k x.val)),
    hsum _ (fun x hx => by simp [MulChar.map_nonunit _ hx])]
  simp only [dirOf_unit]
  rw [neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_div₀, map_natCast]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsIntHigherStickelbergerDenomSmul
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem primorial_dvd_fact (n : ℕ) : primorial n ∣ n.factorial := by
  rw [primorial, ← Finset.prod_Ico_id_eq_factorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_Ico]
  exact ⟨hp.2.one_lt.le, hp.1⟩

private theorem denY_Ek (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k) (b : ZMod N) :
    ∃ z : ℤ, (z : ℚ) = (denY N k : ℚ) * Ek N k b := by
  obtain ⟨z, hz⟩ := b_denint N k b.val hN
  obtain ⟨c, hc⟩ := primorial_dvd_fact (k + 1)
  refine ⟨c * z, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [denY, Ek, den] at hz ⊢
  push_cast [hc] at hz ⊢
  rw [← hz]
  field_simp

theorem UpperTheory.V.B5.exists_int_higherStickelbergerDenom_smul :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 1 ≤ k → ∃ z : MonoidAlgebra ℤ Γ, coefMap ℚ Γ z = (denY N k : ℚ) • yEl k a ha π := by
  intro N _ Γ _ π a ha k hk
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  choose w hw using fun b : ZMod N => denY_Ek N k hN hk b
  refine ⟨(1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) *
    -∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (w b), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [yEl, thetaEl, sumEl, map_mul, map_sub, map_one, map_neg, map_sum, coefMap_single, hw]
  push_cast
  rw [← mul_smul_comm, smul_neg, Finset.smul_sum]
  simp only [MonoidAlgebra.smul_single']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsPadicIntLiftOfIntegralAt
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_padicInt_lift_of_integralAt :
    ∀ {Γ : Type} [CommGroup Γ] [Finite Γ] (l : ℕ) [Fact l.Prime] (y : MonoidAlgebra ℚ Γ), IntAt l 0 y → ∃ Yp : MonoidAlgebra ℤ_[l] Γ, MonoidAlgebra.mapRingHom Γ (algebraMap ℤ_[l] ℚ_[l]) Yp = MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) y := by
  intro Γ _ _ l _ y hy
  have hle : ∀ g : Γ, ‖((y.coeff g : ℚ) : ℚ_[l])‖ ≤ 1 := by
    intro g
    have h := hy g
    rw [pow_zero, div_one, mem_Zl] at h
    exact Padic.norm_rat_le_one h
  let x : Γ → ℤ_[l] := fun g => ⟨((y.coeff g : ℚ) : ℚ_[l]), hle g⟩
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm x), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom]
  change algebraMap ℤ_[l] ℚ_[l] ((Finsupp.equivFunOnFinite.symm x) g) = _
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.LinearIndependentCharactersOnQuotientReps
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.linearIndependent_characters_on_quotientReps :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ), c * c = 1 → LinearIndependent Ω (fun χ : Ch Ω c ε => fun i : Qc c => ((χ.1 (rep i) : Ωˣ) : Ω)) := by
  intro Ω _ Γ _ c ε h2
  classical
  have hw : LinearIndependent Ω (fun χ : Ch Ω c ε => fun g : Γ => ((χ.1 g : Ωˣ) : Ω)) := by
    have := (linearIndependent_monoidHom Γ Ω).comp
      (fun χ : Ch Ω c ε => (Units.coeHom Ω).comp χ.1) (by
        intro χ ψ h
        apply Subtype.ext
        ext g
        exact congrArg (fun f : Γ →* Ω => f g) h)
    exact this
  rw [linearIndependent_iff'] at hw ⊢
  intro s a hs
  apply hw s a
  funext g
  have hg := (mk_eq_mk h2 (rep (Qc.mk c g)) g).mp (mk_rep _)
  have hi := congrFun hs (Qc.mk c g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
  generalize rep (Qc.mk c g) = r at hg hi
  rcases hg with rfl | rfl
  · exact hi
  · calc ∑ χ ∈ s, a χ * ((χ.1 (c * r) : Ωˣ) : Ω)
        = ∑ χ ∈ s, (ε : Ω) * (a χ * ((χ.1 r : Ωˣ) : Ω)) :=
          Finset.sum_congr rfl (fun χ _ => by rw [map_mul, Units.val_mul, χ.2]; ring)
      _ = (ε : Ω) * ∑ χ ∈ s, a χ * ((χ.1 r : Ωˣ) : Ω) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hi, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemSpanOrderTwoRelationIffCoordsEqZero
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem single_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (g : Γ) (b : A) :
    MonoidAlgebra.single g b * rel A c ε =
      MonoidAlgebra.single g (-((ε : A) * b)) + MonoidAlgebra.single (c * g) b := by
  rw [rel, MonoidAlgebra.intCast_def, mul_sub, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_comm g c, mul_comm b,
    MonoidAlgebra.single_neg, sub_eq_add_neg, add_comm]

private theorem coeff_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] {c : Γ} (h2 : c * c = 1) (ε : ℤ)
    (u : MonoidAlgebra A Γ) (g : Γ) :
    (u * rel A c ε).coeff g = u.coeff (c * g) - (ε : A) * u.coeff g := by
  classical
  induction u using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [add_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    ring
  | single a b =>
    rw [single_mul_rel]
    have h : (c * a = g) ↔ (a = c * g) := by
      constructor
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]
    split_ifs <;> ring

theorem UpperTheory.V.B5.mem_span_orderTwoRelation_iff_coords_eq_zero :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ w : MonoidAlgebra A Γ, w ∈ Ideal.span {rel A c ε} ↔ coord c ε w = 0 := by
  intro A _ Γ _ _ c ε h2 hc hε w
  classical
  letI := Fintype.ofFinite Γ
  have hε' : (ε : A) * ε = 1 := by
    have := congrArg (fun n : ℤ => (n : A)) hε
    simpa using this
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨u, rfl⟩
    funext i
    simp only [coord, coeff_mul_rel h2, Pi.zero_apply]
    rw [← mul_assoc c c, h2, one_mul]
    linear_combination (-(u.coeff (c * rep i))) * hε'
  · intro hw
    refine ⟨∑ i : Qc c, MonoidAlgebra.single (rep i) (w.coeff (c * rep i)), ?_⟩
    rw [Finset.sum_mul]
    simp only [single_mul_rel]
    apply MonoidAlgebra.ext
    conv_rhs => rw [← Finsupp.univ_sum_single w.coeff]
    rw [sum_rep h2 hc (fun g => Finsupp.single g (w.coeff g)), MonoidAlgebra.coeff_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := congrFun hw i
    simp only [coord, Pi.zero_apply] at hi
    rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
      show -((ε : A) * w.coeff (c * rep i)) = w.coeff (rep i) by linear_combination -hi]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Mulvec
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem coeff_mul_sum {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (z w : MonoidAlgebra A Γ) (g : Γ) : (z * w).coeff g = ∑ h, z.coeff (g * h⁻¹) * w.coeff h := by
  rw [MonoidAlgebra.mul_apply_right, Finsupp.sum_fintype]
  intro h
  simp

theorem UpperTheory.V.B5.coords_mul_eq_quotientMatrix_mulVec :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z w : MonoidAlgebra A Γ, coord c ε (z * w) = (mat c ε z).mulVec (coord c ε w) := by
  intro A _ Γ _ _ c ε hc hc1 hε z w
  haveI := Fintype.ofFinite Γ
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hεA : (ε : A) * ε = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hε
  funext i
  simp only [coord, Matrix.mulVec, dotProduct, mat, Matrix.of_apply, coeff_mul_sum]
  rw [sum_rep hc hc1, sum_rep hc hc1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : rep i * (c * rep j)⁻¹ = c * (rep i * (rep j)⁻¹) := by
    rw [mul_inv, hci, mul_left_comm]
  have e2 : c * rep i * (c * rep j)⁻¹ = rep i * (rep j)⁻¹ := by
    rw [mul_inv, hci, mul_mul_mul_comm, hc, one_mul]
  have e3 : c * rep i * (rep j)⁻¹ = c * (rep i * (rep j)⁻¹) := mul_assoc _ _ _
  rw [e2, e1, e3]
  linear_combination (-(z.coeff (c * (rep i * (rep j)⁻¹)) * w.coeff (c * rep j))) * hεA
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.SumCharMulQuotientMatrixEqCharEvalMul
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem ev_eq_sum {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (χ : Γ →* Ωˣ) (z : MonoidAlgebra A Γ) :
    ev A χ z = ∑ g, algebraMap A Ω (z.coeff g) * ((χ g : Ωˣ) : Ω) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]
  | single g n =>
    rw [ev_single, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, hb.symm]
    · simp

theorem UpperTheory.V.B5.sum_char_mul_quotientMatrix_eq_charEval_mul :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ∀ (χ : Ch Ω c ε) (z : MonoidAlgebra A Γ) (j : Qc c), ∑ i : Qc c, ((χ.1 (rep i) : Ωˣ) : Ω) * algebraMap A Ω (mat c ε z i j) = ev A χ.1 z * ((χ.1 (rep j) : Ωˣ) : Ω) := by
  intro A _ Ω _ _ Γ _ _ c ε h2 h1 χ z j
  have := Fintype.ofFinite Γ
  have hc : ((χ.1 c : Ωˣ) : Ω) = (ε : Ω) := χ.2
  rw [ev_eq_sum, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight (rep j)⁻¹), sum_rep h2 h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ((χ.1 (rep j) : Ωˣ) : Ω) ≠ 0 := Units.ne_zero _
  simp only [mat, Matrix.of_apply, Equiv.coe_mulRight, map_add (f := _), map_mul, map_intCast, mul_assoc, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, hc, inv_mul_cancel₀ hj]
  ring
end

