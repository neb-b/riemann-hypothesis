module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroup
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.SplitCharacter

open GlobalTheory.NormSum.VacMove

theorem mem_of_local {G : Type} [AddCommGroup G] (T : AddSubgroup G) (x : G)
    (h : ∀ q : ℕ, q.Prime → ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ T) : x ∈ T := by
  by_contra hx
  have h1 : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ≠ 1 := by
    intro h1
    rw [AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff] at h1
    exact hx h1
  obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨m, hm, hT⟩ := h q hq
  have : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ∣ m := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hT
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm (hd.trans this)

variable {D : D7}

def vanish (D : D7) (q : ℕ) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  zero_mem' := fun k => ⟨1, one_pos, by simp, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨m, hm, hc, s, hs, h⟩ := hx k
    obtain ⟨m', hm', hc', s', hs', h'⟩ := hy k
    refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hc hc', m' * s + m * s',
      add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
    push_cast
    linear_combination (m' : AE D) * h + (m : AE D) * h'
  smul_mem' := fun c x hx => by
    have := zeroAt_mul D hq hx c
    rwa [mul_comm] at this

theorem eq_zero_of_zeroAt (x : AE D) (h : ∀ q : ℕ, q.Prime → ZeroAt D q x) : x = 0 := by
  refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 x fun n hn => ?_
  have : x ∈ (OhE D).toAddSubgroup.map (AddMonoidHom.mulLeft (n : AE D)) := by
    refine mem_of_local _ x fun q hq => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    obtain ⟨m, -, hc, s, hs, h⟩ := h q hq a
    refine ⟨m * n', Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, s, hs, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
    push_cast
    linear_combination -(n' : AE D) * h
  obtain ⟨w, hw, h⟩ := this
  exact ⟨w, hw, h.symm⟩

theorem zeroAt_det {N q : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (h : TrivAt D q g) :
    ZeroAt D q (((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) - 1) := by
  have h1 : (Ideal.Quotient.mk (vanish D q hq)).mapMatrix (g : Matrix (Fin N) (Fin N) (AE D)) =
      (Ideal.Quotient.mk (vanish D q hq)).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

def cutHom {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem exists_split_character : ∀ (D : D7) (N₀ : ℕ) (χ : HeckeU D N₀) (N : ℕ), ∃ c : GA D N →* ℂˣ, (∀ k : GA D N, SuppInert D (k : GL (Fin N) (AE D)) → c k = 1) ∧ ∀ (g : GA D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) → x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → c g = χ.f x := by
  intro D N₀ χ N
  obtain ⟨ε, -, h1, h2, h3⟩ := exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  refine ⟨χ.f.comp ((Units.map (cutHom ε h1)).comp
    ((Matrix.GeneralLinearGroup.det (n := Fin N) (R := AE D)).comp (GA D N).subtype)), fun k hk => ?_, fun g x hx hg => ?_⟩
  · have h0 : ε * (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1) = 0 := by
      refine eq_zero_of_zeroAt _ fun q hq => ?_
      by_cases hi : InertQ D q
      · have := zeroAt_mul D hq ((h3 q hq).1 hi)
          (ε * (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1))
        convert this using 1
        linear_combination (-(((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1)) * (h1 + h2)
      · rw [mul_comm]
        exact zeroAt_mul D hq (zeroAt_det hq (hk q hq hi)) ε
    have h4 : Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D))) = 1 := by
      ext
      change (1 - ε) + ε * ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) = 1
      linear_combination h0
    change χ.f (Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)))) = 1
    rw [h4, map_one]
  · have h0 : (1 - (ε + sgA D ε)) * ((x : AE D) - 1) = 0 := by
      refine eq_zero_of_zeroAt _ fun q hq => ?_
      by_cases hi : InertQ D q
      · rw [mul_comm]
        exact zeroAt_mul D hq (hx q hq hi) _
      · exact zeroAt_mul D hq ((h3 q hq).2 hi) _
    have hs : sgU D (Units.map (cutHom (sgA D ε) h1') x) = Units.map (cutHom ε h1) (sgU D x) := by
      ext
      change sgA D ((1 - sgA D ε) + sgA D ε * x) = (1 - ε) + ε * sgA D x
      rw [map_add (f := _), map_mul, map_sub, map_one, sgA_sgA]
    have h5 : Units.map (cutHom ε h1) x * Units.map (cutHom (sgA D ε) h1') x = x := by
      ext
      change ((1 - ε) + ε * x) * ((1 - sgA D ε) + sgA D ε * x) = (x : AE D)
      linear_combination (1 - (x : AE D)) ^ 2 * h2 - h0
    have h6 : Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) *
        (Units.map (cutHom (sgA D ε) h1') x * sgU D (Units.map (cutHom (sgA D ε) h1') x)) = x := by
      rw [hs, mul_comm (Units.map (cutHom (sgA D ε) h1') x), ← mul_assoc, ← map_mul, ← hg, h5]
    change χ.f (Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)))) = χ.f x
    conv_rhs => rw [← h6]
    rw [map_mul, χ.norm, mul_one]

end GlobalTheory.SplitCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsThetaLatticeCorrespondenceWeilOperator
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilCorr

open GlobalTheory.NormSum.MovedTheta

theorem exists_close_two {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P P' : Matrix (Fin a) (Fin a) R) (Q Q' : Matrix (Fin b) (Fin b) R)
    (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      (∀ i j, (P * z.map ι * Q - P * X * Q) i j ∈ I) ∧ ∀ i j, (P' * z.map ι * Q' - P' * X * Q') i j ∈ I := by
  obtain ⟨n₁, hn₁, hP⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P
  obtain ⟨n₂, hn₂, hQ⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q
  obtain ⟨n₃, hn₃, hP'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P'
  obtain ⟨n₄, hn₄, hQ'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q'
  choose e t ht he using fun i j => hA (X i j) (m * n₁ * n₂ * n₃ * n₄) (by positivity)
  have key : ∀ (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R) (n n' c : ℕ),
      (∀ i j, (n : R) * P i j ∈ O) → (∀ i j, (n' : R) * Q i j ∈ O) → m * n₁ * n₂ * n₃ * n₄ = c * n * n' →
      ∀ i j, (P * (Matrix.of e).map ι * Q - P * X * Q) i j ∈ I := by
    intro P Q n n' c hP hQ hc i j
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul, he, hc]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((c * n * n' : ℕ) : R) * t r l) * Q l j =
        ((c : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)
  refine ⟨Matrix.of e, fun i j => ⟨((n₁ * n₂ * n₃ * n₄ : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩,
    key P Q n₁ n₂ (m * n₃ * n₄) hP hQ (by ring), key P' Q' n₃ n₄ (m * n₁ * n₂) hP' hQ' (by ring)⟩
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
  push_cast; ring

section Entries

variable {R : Type} [CommRing R] {I : AddSubgroup R} {a b : ℕ} {A B A' B' : Matrix (Fin a) (Fin b) R}

theorem entries_of_sub (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, B i j ∈ I) (i : Fin a) (j : Fin b) : A i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, sub_add_cancel] at this

theorem entries_trans (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (B - A') i j ∈ I) (i : Fin a) (j : Fin b) :
    (A - A') i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, Matrix.sub_apply, sub_add_sub_cancel] at this

theorem entries_iff (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (A' - B') i j ∈ I) :
    (∀ i j, (B - B') i j ∈ I) ↔ ∀ i j, (A - A') i j ∈ I := by
  refine forall₂_congr fun i j => ?_
  have h1 := sub_mem (h i j) (h' i j)
  simp only [Matrix.sub_apply] at h1 ⊢
  constructor
  · intro h2
    convert add_mem h1 h2 using 1
    ring
  · intro h2
    convert sub_mem h2 h1 using 1
    ring

end Entries

variable {D : D7} {N N' : ℕ}

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  simp only [pt, embV, tor0, Pi.smul_apply, smul_eq_mul] at h1
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem pt_sub (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - w) = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w := by
  rw [sub_eq_add_neg, pt_add, pt_neg, ← sub_eq_add_neg]

theorem mv_sub (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z - w) = mv g g' z - mv g g' w := by
  rw [sub_eq_add_neg, mv_add, mv_neg, ← sub_eq_add_neg]

theorem pt_mem_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {h : GA D N} {h' : GA D N'}
    {L : Lat D N} {L' : Lat D N'} (hL : Moves D (h : GL (Fin N) (AE D)) L) (hL' : Moves D (h' : GL (Fin N') (AE D)) L')
    (u : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ u ∈ La D (tor0 D cc δ) L L' ↔
      ∀ i j, mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) u i j ∈ IhE D cc := by
  have hD := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hu
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' h h' L L' hL hL' _ hu
    rw [pt_injective cc hδ hz]
    exact hz'
  · exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hD cc δ hcc N N' h h' L L' hL hL' u

theorem move_fwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (((g' * h')⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) *
      ((g' : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) *
      ((g * h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = mv h h' z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
    ← Matrix.mul_assoc ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
    Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]

theorem move_bwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * mv g g' z *
      (h : Matrix (Fin N) (Fin N) (AE D)) = mv (g * h) (g' * h') z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem approx_fwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (z : Matrix (Fin N') (Fin N) D.host.E) (m : ℕ) (hm : 0 < m) :
    ∃ z' : Matrix (Fin N') (Fin N) D.host.E, CloseTo D cc m g g' z z' ∧
      (∀ i j, (mv (g * h) (g' * h') z' - mv h h' z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv (g * k) (g' * k') z' - mv k k' z) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_fwd g h g' h' z, ← move_fwd g k g' k' z]
  exact exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI _ _ _ _ _ m hm

theorem approx_bwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ z : Matrix (Fin N') (Fin N) D.host.E,
      (∀ i j, (mv h h' z - mv (g * h) (g' * h') y) i j ∈ IhE D cc) ∧
      ∀ i j, (mv k k' z - mv (g * k) (g' * k') y) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_bwd g h g' h' y, ← move_bwd g k g' k' y]
  obtain ⟨z, -, hz⟩ := exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI (mv g g' y)
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    ((k'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    (h : Matrix (Fin N) (Fin N) (AE D)) (k : Matrix (Fin N) (Fin N) (AE D)) 1 one_pos
  exact ⟨z, hz⟩

theorem exists_corr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ f : La D (tor0 D cc δ) M₁ M₁' → La D (tor0 D cc δ) M₂ M₂', (∀ x : La D (tor0 D cc δ) M₁ M₁', W.Om g g' (Wd D (tor0 D cc δ) (x : VC D N N') F) = Wd D (tor0 D cc δ) (f x : VC D N N') (W.Om g g' F)) ∧ (∀ x y : La D (tor0 D cc δ) M₁ M₁', (x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₁ L₁' ↔ (f x : VC D N N') - (f y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂') ∧ ∀ y : La D (tor0 D cc δ) M₂ M₂', ∃ x : La D (tor0 D cc δ) M₁ M₁', (f x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  have hcc : cc ≠ ⊥ := hC.1.1
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have step : ∀ z : Matrix (Fin N') (Fin N) D.host.E, ∃ z' : Matrix (Fin N') (Fin N) D.host.E,
      W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) =
        Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om g g' F) ∧
      (∀ i j, (mv ((g * h : GA D N) : GL (Fin N) (AE D)) ((g' * h' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv ((g * k : GA D N) : GL (Fin N) (AE D)) ((g' * k' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (k : GL (Fin N) (AE D)) (k' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc := by
    intro z
    obtain ⟨m, hm, hl⟩ := W.lift g g' z F hF
    obtain ⟨z', hc, h1, h2⟩ := approx_fwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' z m hm
    exact ⟨z', hl z' hc, h1, h2⟩
  choose s hs1 hs2 hs3 using step
  choose r hr1 hr2 using fun x : La D (tor0 D cc δ) M₁ M₁' =>
    GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' k k' M₁ M₁' b1 b1' x x.2
  have hmem : ∀ x, pt D (tor0 D cc δ) δ (s (r x)) ∈ La D (tor0 D cc δ) M₂ M₂' := by
    intro x
    rw [pt_mem_iff hcc hδ b2 b2']
    exact entries_of_sub (hs3 (r x)) (hr2 x)
  refine ⟨fun x => ⟨_, hmem x⟩, fun x => ?_, fun x y => ?_, fun y => ?_⟩
  · have := hs1 (r x)
    rwa [← hr1 x] at this
  · rw [hr1 x, hr1 y]
    dsimp only
    rw [← pt_sub, ← pt_sub, pt_mem_iff hcc hδ a1 a1', pt_mem_iff hcc hδ a2 a2', mv_sub, mv_sub]
    exact entries_iff (hs2 (r x)) (hs2 (r y))
  · obtain ⟨y₀, hy, hy'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' _ _ M₂ M₂' b2 b2' y y.2
    obtain ⟨z, h1, h2⟩ := approx_bwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' y₀
    have hz : pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) M₁ M₁' := by
      rw [pt_mem_iff hcc hδ b1 b1']
      exact entries_of_sub h2 hy'
    refine ⟨⟨_, hz⟩, ?_⟩
    have e : r ⟨_, hz⟩ = z := (pt_injective cc hδ (hr1 ⟨_, hz⟩)).symm
    dsimp only
    rw [e, hy, ← pt_sub, pt_mem_iff hcc hδ a2 a2', mv_sub]
    exact entries_trans (hs2 z) h1

end GlobalTheory.WeilCorr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalRowWeight
section
open GlobalTheory.DualWeyl MvPolynomial NumberField
open Formalism.GradedWeylDivisibility (rowAct rowW rowNu)
open Formalism.REAL (fockF)
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.DualWeylFock

variable {N : ℕ} {la : Fin N → ℕ}

theorem fock_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF (c • f) g = c * fockF f g := by
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

def fockLeft {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' f f' := Formalism.REAL.fischerInner_add_left f f' g
  map_smul' c f := fock_smul_left c f g

theorem extremal_rowWeight (hla : Antitone la) : IsWeightedHomogeneous (rowW N N) (extremal la ℂ) la := by
  have hnu : rowNu (r := N) la = la := by
    funext b
    simp [rowNu]
  have := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl la hla
  rwa [hnu] at this

theorem evalAt_one_of_ne {μ : Fin N → ℕ} (hμ : μ ≠ la) {q : Pol N ℂ} (hq : q ∈ nabla la ℂ)
    (hw : IsWeightedHomogeneous (rowW N N) q μ) : evalAt 1 q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin N → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin N → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have h1 := evalAt_rowAct 1 (Matrix.diagonal t) q
  have h2 := evalAt_colAct 1 (Matrix.diagonal t) q
  rw [Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t μ _ hw, hprod, Matrix.mul_one, map_smul, smul_eq_mul] at h1
  rw [colAct_of_mem hq _ (Matrix.blockTriangular_diagonal t), Matrix.one_mul, map_smul, smul_eq_mul] at h2
  simp only [diagChar, Matrix.diagonal_apply_eq] at h2
  rw [hprod] at h2
  have hne : (2 : ℂ) ^ μ a - 2 ^ la a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ μ a = 2 ^ la a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h')
  have : ((2 : ℂ) ^ μ a - 2 ^ la a) * evalAt 1 q = 0 := by rw [sub_mul, h1, h2, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

theorem fock_extremal (hla : Antitone la) {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) :
    fockF f (extremal la ℂ) = evalAt 1 f * fockF (extremal la ℂ) (extremal la ℂ) := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum := sum_weightedHomogeneousComponent (rowW N N) f
  rw [finsum_eq_sum _ hfin] at hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hsum, Formalism.REAL.fischerInner_sum_left, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N la μ f hf
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW N N) μ f
  by_cases hμ : μ = la
  · subst hμ
    conv_lhs => rw [GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight ℂ N μ hla _ hmem hw']
    rw [fock_smul_left]
  · rw [evalAt_one_of_ne hμ hmem hw', zero_mul]
    exact Formalism.GradedWeylDivisibility.fockWeightOrth _ _ _ μ la _ _ hμ hw' (extremal_rowWeight hla)

theorem exists_form_eq (ψ : Pol N ℂ →ₗ[ℂ] ℂ) : ∃ h ∈ nabla la ℂ, ∀ f ∈ nabla la ℂ, form la f h = ψ f := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  let φ : Space la →ₗ[ℂ] ℂ := ψ ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap
  let v : Space la := (InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap φ)
  refine ⟨((toSpace la).symm v).1, ((toSpace la).symm v).2, fun f hf => ?_⟩
  have h1 : ⟪v, toSpace la ⟨f, hf⟩⟫_ℂ = φ (toSpace la ⟨f, hf⟩) := InnerProductSpace.toDual_symm_apply
  exact h1

theorem form_eq_fock_div (N : ℕ) (la : Fin N → ℕ) (hla : Antitone la) :
    ∀ f ∈ nabla la ℂ, ∀ f' ∈ nabla la ℂ,
      form la f f' = fockF f f' / fockF (extremal la ℂ) (extremal la ℂ) := by
  intro f hf f' hf'
  obtain ⟨hre, him⟩ := Formalism.GradedWeylDivisibility.fockPos _ (extremal la ℂ) extremal_ne_zero
  set c := fockF (extremal la ℂ) (extremal la ℂ) with hc
  have hc0 : c ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hcc : conj c = c := Complex.conj_eq_iff_im.mpr him
  obtain ⟨h, hh, H⟩ := exists_form_eq (la := la) (c⁻¹ • fockLeft f')
  have H' : ∀ g ∈ nabla la ℂ, form la g h = fockF g f' / c := fun g hg => by
    rw [H g hg, div_eq_inv_mul]; rfl
  have hE := extremal_mem (R := ℂ) hla
  have key : h = f' := by
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt_unitary (Submodule.sub_mem _ hh hf') fun u => ?_
    have hst : ∀ (g : Matrix (Fin N) (Fin N) ℂ), ∀ p ∈ nabla la ℂ, rowAct ℂ g p ∈ nabla la ℂ :=
      fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N la g p hp
    have h1 := H' _ (hst (u.1)ᴴ _ hE)
    have h2 : rowAct ℂ u.1 (rowAct ℂ (u.1)ᴴ (extremal la ℂ)) = extremal la ℂ := by
      have h3 : (u.1)ᴴ * u.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp u.2
      rw [← AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowActMul ℂ N N, h3, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
      rfl
    rw [← form_rowAct u, h2, Formalism.GradedWeylDivisibility.fockRowAdj, Matrix.conjTranspose_conjTranspose, ← conj_form,
      (_root_.GlobalTheory.DualWeyl.Repro.extremal_reproducing N la hla).1 _ (hst _ _ hh), Formalism.GradedWeylDivisibility.fockHerm, fock_extremal hla (hst _ _ hf'),
      evalAt_rowAct, evalAt_rowAct, Matrix.mul_one, ← hc, ← starRingEnd_apply, map_mul, hcc,
      mul_div_cancel_right₀ _ hc0] at h1
    rw [map_sub, sub_eq_zero]
    exact (starRingEnd ℂ).injective h1
  rw [← H' f hf, key]

end GlobalTheory.DualWeylFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSqNormEmbT
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.TypeNormProduct

theorem prod_sq_norm_embT : ∀ (D : D7) (y : 𝓞 D.host.E),
    ∏ τ, ‖embT D τ (y : D.host.E)‖ ^ 2 = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
  intro D y
  have hc : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
    fun φ x => D.host.conjE_apply φ x
  have hcc : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x =>
    D.host.φ₀.injective (by rw [hc, hc, Complex.conj_conj])
  set x : D.host.E := (y : D.host.E) with hx
  have ht : D.host.conj (x * D.host.conj x) = x * D.host.conj x := by
    rw [map_mul, hcc, mul_comm]
  have h1 := GlobalTheory.NormSign.prod_embT D (x * D.host.conj x)
  have h2 := congrArg D.host.φ₀ (GlobalTheory.NormSign.norm_eq D.host ht)
  rw [map_pow, ← h1, map_ratCast, map_mul, Algebra.norm_eq_of_algEquiv] at h2
  have h3 : ∏ τ, embT D τ (x * D.host.conj x) = ((∏ τ, ‖embT D τ x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h3] at h2
  have h4 : ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 = (∏ τ, ‖embT D τ x‖ ^ 2) ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, Complex.ofReal_pow, ← h2]
    push_cast
    ring
  have h5 : 0 ≤ ∏ τ, ‖embT D τ x‖ ^ 2 := Finset.prod_nonneg fun _ _ => by positivity
  rw [← sq_abs] at h4
  have h6 := (pow_left_inj₀ (abs_nonneg _) h5 two_ne_zero).1 h4
  rw [← h6, Ideal.absNorm_span_singleton, hx, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.TypeNormProduct
end

