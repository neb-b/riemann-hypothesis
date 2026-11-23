module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CndIff
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem valCast {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ) : (((k : ZMod M)).val : ZMod N) = (k : ZMod N) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast h]

private theorem valDvd {M l n : ℕ} [Fact l.Prime] [NeZero M] (h : l ^ n ∣ M) (k : ℤ) :
    (l : ℤ_[l]) ^ n ∣ (k : ℤ_[l]) - (((k : ZMod M)).val : ℤ_[l]) := by
  have h1 : (M : ℤ) ∣ k - (((k : ZMod M)).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp
  have h2 : ((l ^ n : ℕ) : ℤ) ∣ k - (((k : ZMod M)).val : ℤ) := (Int.natCast_dvd_natCast.2 h).trans h1
  have h3 := map_dvd (Int.castRingHom ℤ_[l]) h2
  simpa only [eq_intCast, Int.cast_natCast, Int.cast_sub, Nat.cast_pow, Int.cast_pow] using h3

private theorem cnd_iff {l N M : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g h : SL(2, ℤ)) (hg : (N : ℤ) ∣ en g 1 0) :
    Cnd l N g ((h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))) ↔ g⁻¹ * h ∈ Gam N l := by
  have hg0 : ((g 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hg
  have dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe; rwa [Matrix.det_fin_two] at this
  have dg' := congrArg (fun z : ℤ => (z : ZMod N)) dg
  have dh' := congrArg (fun z : ℤ => (z : ZMod N)) dh
  have e00 : (g⁻¹ * h) 0 0 = g 1 1 * h 0 0 - g 0 1 * h 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e10 : (g⁻¹ * h) 1 0 = - g 1 0 * h 0 0 + g 0 0 * h 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g⁻¹ * h) 1 1 = - g 1 0 * h 0 1 + g 0 0 * h 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Cnd, Gam, en, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, e00, e10, e11,
    Matrix.map_apply, eq_intCast, valCast hN, valCast hl]
  push_cast at dg' dh' ⊢
  rw [hg0] at dg' ⊢
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [h1, h2]; linear_combination dg'
    · rw [h1, h2] at dh'; linear_combination dh'
    · rw [h1]; ring
    · linear_combination -h3
  · rintro ⟨⟨h1, -, h2⟩, h3⟩
    have h4 : ((h 1 0 : ℤ) : ZMod N) = 0 := by linear_combination (g 1 1 : ZMod N) * h2 - (h 1 0 : ZMod N) * dg'
    refine ⟨h4, ?_, ?_⟩
    · rw [h4] at h1; linear_combination (g 0 0 : ZMod N) * h1 - (h 0 0 : ZMod N) * dg'
    · linear_combination -h3

private theorem term (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (hl : l ^ n ∣ M) (x y : Row M₀) (hxy : Ok x y)
    (a : Fam X M₀) (ha : Eqv X (l ^ n) M₀ a) (h : SL(2, ℤ)) (hh : (N : ℤ) ∣ h 1 0) (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (hm : m = (h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))) :
    CgF X l n (X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) fun u => (u 0) ^ w • clsK X l n (slD X N (a x y : X.K)))
      (fun u => ((((1 : ZMod M).val : ℤ_[l])) * (((m 0 0).val : ℤ_[l]) * u 0 + ((m 0 1).val : ℤ_[l]) * u 1) ^ w) •
        clsK X l n (slD X N (a (x ᵥ* cD N M₀ m) (y ᵥ* cD N M₀ m) : X.K))) := by
  obtain ⟨k, hk⟩ := hh
  have dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe; rwa [Matrix.det_fin_two] at this
  let h' : SL(2, ℤ) := ⟨!![h 0 0, N * h 0 1; k, h 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hk] at dh; linear_combination dh⟩
  have hD : !![(N : ℤ), 0; 0, 1] * (h : Matrix (Fin 2) (Fin 2) ℤ) = (h' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h', Matrix.mul_apply, Fin.sum_univ_two, hk, mul_comm]
  have hc := (sCdFacts N M₀ M hM).2.2.2 _ _ hD
  obtain ⟨-, s2, s3, -⟩ := sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  have hx : x ᵥ* cD N M₀ m = rt x h' := by rw [hm, hc]; rfl
  have hy : y ᵥ* cD N M₀ m = rt y h' := by rw [hm, hc]; rfl
  rw [hx, hy]
  have r1 := c5 (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a x y)))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a (rt x h') (rt y h')))
  have r3 := c4 _ _ _ _ r1 r2 (by
    obtain ⟨t, ht⟩ := (ha x y hxy).2 h'
    refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) t, ?_⟩
    rw [← map_pow, ← map_mul, ← ht]
    apply Units.ext
    have := s2 _ _ (by rw [h.det_coe]; exact one_pos) hD (a x y : X.K)
    rw [s3 h'] at this
    exact this)
  intro u
  have hk : (l : ℤ_[l]) ^ n ∣ ((mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w -
      (((1 : ZMod M).val : ℤ_[l])) * (((m 0 0).val : ℤ_[l]) * u 0 + ((m 0 1).val : ℤ_[l]) * u 1) ^ w := by
    have b1 := valDvd hl 1
    have b2 := valDvd hl (h 0 0)
    have b3 := valDvd hl (h 0 1)
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at b1 b2 b3 ⊢
    rw [Int.cast_one, Int.cast_one] at b1
    simp only [hm, mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, eq_intCast, map_mul, map_pow, map_add (f := _),
      ← b1, ← b2, ← b3, map_one, one_mul]
  have r4 := a5 _ _ (clsK X l n (slD X N (a (rt x h') (rt y h') : X.K))) hk
  have r5 := congrArg (fun z => ((mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w • z) r3
  simp only [smul_zero, ← map_smul] at r5
  have r6 := congrArg₂ (· + ·) r5 r4
  simp only [← map_add (f := _), add_zero, smul_sub] at r6
  show AdicCompletion.eval _ _ _ (X.kmap l _ (_ • _) - _) = 0
  rw [← r6]
  rw [map_smul]
  exact congrArg (AdicCompletion.eval (idl l) (X.Kl l) n) (sub_add_sub_cancel (G := X.Khat l) _ _ _).symm

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sXiOne :
    UpperTheory.V.Z.Kato.Nb.SXiOne := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy a ha
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl : l ∣ M := (dvd_pow_self l (by have := L.pos; omega)).trans hln
  let r : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  have hr : ∀ γ, r (liftSL M γ) = γ := fun γ => Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M γ)
  let φ : SL(2, ZMod M) → GL (Fin 2) (ZMod M) := fun γ => Matrix.SpecialLinearGroup.toGL (r g * γ)
  have hφ : ∀ δ, (φ (r δ) : Matrix (Fin 2) (Fin 2) (ZMod M)) =
      ((g * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) := by
    intro δ
    simp only [φ, ← map_mul r]; rfl
  have hdet : ∀ γ, Matrix.GeneralLinearGroup.det (φ γ) = 1 := fun γ => Units.ext (r g * γ).det_coe
  have hC : ∀ γ ∈ img (Gam N l) M, Cnd l N g (φ γ : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := (Finset.mem_filter.1 hγ).2
    change Cnd l N g (φ (r δ) : Matrix (Fin 2) (Fin 2) (ZMod M))
    rw [hφ, cnd_iff hN hl g _ L.g0]
    simpa using hδ
  let S : GL (Fin 2) (ZMod M) → X.Fn l := fun m u =>
    (((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) *
        ((((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0).val : ℤ_[l]) * u 0 +
          (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1).val : ℤ_[l]) * u 1) ^ w) •
      clsK X l n (slD X N (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
        (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) : X.K))
  have hXi : Xi X l n N M₀ M w g x y (fun z => z = 1) a = ∑ γ ∈ img (Gam N l) M, S (φ γ) := by
    funext u
    rw [Finset.sum_apply]
    unfold Xi
    symm
    refine Finset.sum_bij (fun γ _ => φ γ) ?_ ?_ ?_ ?_
    · intro γ hγ
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hC γ hγ, hdet γ⟩
    · intro γ _ γ' _ e
      exact mul_left_cancel (Matrix.SpecialLinearGroup.toGL_injective e)
    · intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨-, h1, h2⟩ := hm
      let s : SL(2, ZMod M) := ⟨m, congrArg Units.val h2⟩
      have e : φ (r (g⁻¹ * liftSL M s)) = m := by
        apply Units.ext
        simp only [φ, map_mul r, map_inv r, hr, mul_inv_cancel_left]; rfl
      refine ⟨r (g⁻¹ * liftSL M s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨_, ?_, rfl⟩⟩, e⟩
      rw [← e, hφ, mul_inv_cancel_left, cnd_iff hN hl g _ L.g0] at h1
      exact h1
    · intro γ _; rfl
  rw [hXi]
  refine (sApi Ω ε X l n).2.2.2.1 _ _ _ _ fun γ hγ => ?_
  have h1 := hφ (liftSL M γ)
  rw [hr] at h1
  have h2 := (hC γ hγ).1
  rw [h1, Matrix.map_apply, eq_intCast, valCast hN, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have := term Ω ε X l n N M₀ M w L.eq hln x y hxy a ha _ h2 _ h1
  simpa only [S, hdet, inv_one, Units.val_one] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb.InverseLimitApi

private def Fm (R : Type) [CommRing R] (w : ℕ) : Submodule R ((Fin 2 → R) → R) :=
  Submodule.span R {φ | ∃ i j : ℕ, i + j = w ∧ φ = fun u => u 0 ^ i * u 1 ^ j}

private theorem fm_mul {R : Type} [CommRing R] {a b : ℕ} {φ ψ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R a) (hψ : ψ ∈ Fm R b) :
    φ * ψ ∈ Fm R (a + b) := by
  induction hφ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul k x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | mem x hx =>
    induction hψ using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    | mem y hy =>
      obtain ⟨i, j, rfl, rfl⟩ := hx
      obtain ⟨i', j', rfl, rfl⟩ := hy
      refine Submodule.subset_span ⟨i + i', j + j', by omega, ?_⟩
      funext u
      simp only [Pi.mul_apply]
      ring

private theorem fm_pow {R : Type} [CommRing R] {φ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R 1) (k : ℕ) : φ ^ k ∈ Fm R k := by
  induction k with
  | zero => exact Submodule.subset_span ⟨0, 0, rfl, by funext u; simp⟩
  | succ k ih => rw [pow_succ]; exact fm_mul ih hφ

private theorem fm_lin {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (fun u => (m *ᵥ u) i) ∈ Fm R 1 := by
  have h0 : (fun u : Fin 2 → R => u 0 ^ 1 * u 1 ^ 0) ∈ Fm R 1 := Submodule.subset_span ⟨1, 0, rfl, rfl⟩
  have h1 : (fun u : Fin 2 → R => u 0 ^ 0 * u 1 ^ 1) ∈ Fm R 1 := Submodule.subset_span ⟨0, 1, rfl, rfl⟩
  have h := add_mem (Submodule.smul_mem _ (m i 0) h0) (Submodule.smul_mem _ (m i 1) h1)
  convert h using 1
  funext u
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem un_pow (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) (j : ℕ) : f ^ j ∈ X.Un m := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
  induction j with
  | zero => simpa using (h m).1
  | succ j ih => rw [pow_succ]; exact ((h m).2 _ ih _ hf).1

private def Cf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Khat l) where
  carrier := {x | ∃ f ∈ X.Un (l ^ n), Rep X l n f x}
  zero_mem' := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨h1, -, h3, -⟩ := sCls Ω ε X l n
    refine ⟨1, (h _).1, ?_⟩
    simpa using h3 1 _ 0 (h1 1)
  add_mem' := by
    rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨-, h2, -⟩ := sCls Ω ε X l n
    exact ⟨f * g, ((h _).2 f hf g hg).1, (h2 _ _ _ _ ha hb).1⟩
  smul_mem' := by
    rintro k a ⟨f, hf, ha⟩
    obtain ⟨-, -, -, -, -, -, h⟩ := sCls Ω ε X l n
    obtain ⟨j, hj⟩ := h f k a ha
    exact ⟨f ^ j, un_pow X _ f hf j, hj⟩

private def Pm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {t | PolMod X l w n t}
  zero_mem' := ⟨0, fun _ => (Cf X l n).zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c + d, fun i => (Cf X l n).add_mem (hc i) (hd i), fun u => ?_⟩
    simp only [Pi.add_apply, ha u, hb u, smul_add, Finset.sum_add_distrib]
  smul_mem' := by
    rintro k a ⟨c, hc, ha⟩
    refine ⟨k • c, fun i => (Cf X l n).smul_mem k (hc i), fun u => ?_⟩
    simp only [Pi.smul_apply, ha u, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem pm_fm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (c : X.Khat l) (hc : c ∈ Cf X l n)
    (φ : (Fin 2 → ℤ_[l]) → ℤ_[l]) (hφ : φ ∈ Fm ℤ_[l] w) : (fun u => φ u • c) ∈ Pm X l w n := by
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (Pm X l w n).zero_mem using 1
    funext u; simp
  | add x y _ _ hx hy =>
    convert (Pm X l w n).add_mem hx hy using 1
    funext u; simp [add_smul]
  | smul k x _ hx =>
    convert (Pm X l w n).smul_mem k hx using 1
    funext u; simp [mul_smul]
  | mem x hx =>
    obtain ⟨i, j, rfl, rfl⟩ := hx
    refine ⟨Pi.single ⟨i, by omega⟩ c, fun k => ?_, fun u => ?_⟩
    · show Pi.single (M := fun _ => X.Khat l) _ c k ∈ Cf X l n
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
    · rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (i + j + 1))]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, smul_zero]
      · simp

private theorem pm_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (t : X.Fn l)
    (ht : PolMod X l w n t) : PolMod X l w n (X.act l m t) := by
  obtain ⟨c, hc, ht⟩ := ht
  have key : ∀ i : Fin (w + 1), (fun u => (((fun u => (mZl l m *ᵥ u) 0) ^ (i : ℕ) * (fun u => (mZl l m *ᵥ u) 1) ^ (w - (i : ℕ)) :
      (Fin 2 → ℤ_[l]) → ℤ_[l]) u) • X.kmap l (X.sl (toGQ m)).toRingEquiv (c i)) ∈ Pm X l w n := by
    intro i
    apply pm_fm
    · obtain ⟨f, hf, hr⟩ := hc i
      obtain ⟨-, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
      obtain ⟨-, -, -, -, h', -⟩ := sCls Ω ε X l n
      exact ⟨slU X (toGQ m) f, h _ _ f hf, h' (X.sl (toGQ m)).toRingEquiv f _ hr⟩
    · have := fm_mul (fm_pow (fm_lin (mZl l m) 0) i) (fm_pow (fm_lin (mZl l m) 1) (w - i))
      rwa [show (i : ℕ) + (w - i) = w by omega] at this
  have h := (Pm X l w n).sum_mem fun i (_ : i ∈ Finset.univ) => key i
  show X.act l m t ∈ Pm X l w n
  convert h using 1
  funext u
  show X.kmap l (X.sl (toGQ m)).toRingEquiv (t (mZl l m *ᵥ u)) = _
  rw [ht, map_sum (X.kmap l (X.sl (toGQ m)).toRingEquiv), Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

private theorem pm_down (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (t : X.Fn l)
    (ht : PolMod X l w (n + 1) t) : PolMod X l w n t := by
  obtain ⟨c, hc, ht⟩ := ht
  refine ⟨c, fun i => ?_, ht⟩
  obtain ⟨f, hf, hr⟩ := hc i
  obtain ⟨-, -, -, -, -, h, -⟩ := sCls Ω ε X l n
  refine ⟨f, fun W hW => ?_, h _ _ hr⟩
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨g ^ l, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ']
  exact hg

private def Im (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {a | InvM X l N w n a}
  zero_mem' := by
    obtain ⟨he, -⟩ := sApi Ω ε X l n
    refine ⟨⟨0, (Pm X l w n).zero_mem, he.refl _⟩, fun γ _ => ?_, 0, zero_mem _, fun u => by simp⟩
    rw [map_zero]; exact he.refl _
  add_mem' := by
    rintro a b ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩ ⟨⟨s, hs, hbs⟩, hb, y, hy, hyb⟩
    obtain ⟨-, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t + s, (Pm X l w n).add_mem ht hs, (h _ _ _ _ hat hbs).1⟩, fun γ hγ => ?_, x + y, add_mem hx hy, ?_⟩
    · rw [(X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ)).map_add]
      exact (h _ _ _ _ (ha γ hγ) (hb γ hγ)).1
    · have := (h x ((l : ℤ_[l]) ^ cL X l N w • a) y ((l : ℤ_[l]) ^ cL X l N w • b) hxa hyb).1
      rw [← smul_add] at this
      exact this
  smul_mem' := by
    rintro k a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨k • t, (Pm X l w n).smul_mem k ht, h _ _ _ hat⟩, fun γ hγ => ?_, k • x, Submodule.smul_mem _ _ hx, ?_⟩
    · rw [map_smul]; exact h _ _ _ (ha γ hγ)
    · have := h k x ((l : ℤ_[l]) ^ cL X l N w • a) hxa
      rw [smul_comm] at this
      exact this

private theorem main : SInvApi := by
  intro Ω _ _ _ ε X l _ N w n
  refine ⟨(Im X l N w n).zero_mem, fun a b ha hb => ⟨(Im X l N w n).add_mem ha hb, (Im X l N w n).sub_mem ha hb⟩,
    fun k a ha => (Im X l N w n).smul_mem k ha, ?_, fun ι S a h => (Im X l N w n).sum_mem h, ?_, ?_,
    fun m t _ ht => pm_act X l w n m t ht⟩
  · rintro a b hab ⟨⟨t, ht, hbt⟩, hb, x, hx, hxb⟩
    obtain ⟨he, -, hs, -, -, hm, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t, ht, he.trans hab hbt⟩, fun γ hγ => he.trans (hm _ _ _ hab) (he.trans (hb γ hγ) (he.symm hab)), x, hx, ?_⟩
    exact he.trans (x := x) (y := (l : ℤ_[l]) ^ cL X l N w • b) hxb (hs _ _ _ (he.symm hab))
  · rintro a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨t, pm_down X l w n t ht, h _ _ hat⟩, fun γ hγ => h _ _ (ha γ hγ), x, hx,
      h x ((l : ℤ_[l]) ^ cL X l N w • a) hxa⟩
  · intro a
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨0, (Pm X l w 0).zero_mem, h _ _⟩, fun γ _ => h _ _, 0, zero_mem _, h 0 ((l : ℤ_[l]) ^ cL X l N w • a)⟩

end UpperTheory.V.Z.Kato.Nb.InverseLimitApi

theorem UpperTheory.V.Z.Kato.Nb.sInvApi :
    UpperTheory.V.Z.Kato.Nb.SInvApi :=
  UpperTheory.V.Z.Kato.Nb.InverseLimitApi.main

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftPush
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem lsq_eq (l p L : ℕ) (h : Nat.Coprime p l) : lsqInv l p L = inv1 p l ^ (2 * L) := by
  have h1 : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).2 h.symm
  have h2 : IsUnit ((l : ZMod p) ^ (2 * L)) := h1.pow _
  unfold lsqInv inv1
  rw [dite_eq_left h1, dite_eq_left h2, inv_pow]
  congr 1
  ext
  simp

private theorem arg_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) [NeZero M]
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : (repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := sSlD Ω ε X 1 one_pos
  have mul : ∀ a b : Ω ≃ₐ[ℚ] Ω, cycM M (a * b) = cycM M a * cycM M b := fun a b => (hM M a).2.1 b
  have rep : ∀ y : (ZMod M)ˣ, cycM M (repM (Ω := Ω) M y) = y := (hM M s).2.2.1
  let f : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ := MonoidHom.mk' (cycM M) mul
  rw [(hM M _).2.2.2.1]
  have e : f ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    change (cycM M (repM (Ω := Ω) M y))⁻¹ * cycM M s * cycM M (repM (Ω := Ω) M (y * (cycM M s)⁻¹)) = 1
    rw [rep, rep, mul_comm y, ← mul_assoc, mul_inv_cancel_right, inv_mul_cancel]
  exact e

private theorem lift_push {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n c M : ℕ) [NeZero N] [NeZero M] {T ι : Type} [DecidableEq T] [Fintype ι] (π : (ZMod M)ˣ → T)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (h : ∀ σ ∈ fixMu Ω M, LiftB X l N w n c (∑ i, z i σ) (bB σ)) (s : Ω ≃ₐ[ℚ] Ω) (t : T) :
    LiftB X l N w n c (∑ i, GlobalTheory.KA.push π (shB X l M (z i)) s t) (GlobalTheory.KA.push π (shB X l M bB) s t) := by
  obtain ⟨-, -, -, hSum, -, -, hGal, -⟩ := sApi Ω ε X l n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ y : (ZMod M)ˣ, LiftB X l N w n c (∑ i, shB X l M (z i) s y) (shB X l M bB s y) := by
    intro y
    have hy := h _ (arg_mem X M s y)
    refine ⟨(sBStab Ω ε X l N w hN _ hy.1).1 _, ?_⟩
    have hc : CgF X l n (bB ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)))
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := hy.2
    have hg := hGal (repM M y) _ _ hc
    have e : (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y = X.galB l (repM M y)
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [shB, map_smul, map_sum]
    intro u
    have hu := hg u
    rw [← e] at hu
    exact hu
  have hpush : ∀ Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod M)ˣ → X.Fn l,
      GlobalTheory.KA.push π Y s t = ∑ y ∈ Finset.univ.filter (fun y => π y = t), Y s y := fun Y => rfl
  simp only [hpush]
  rw [Finset.sum_comm]
  refine ⟨Submodule.sum_mem _ (fun y _ => (key y).1), ?_⟩
  have hs := hSum _ (Finset.univ.filter (fun y => π y = t)) (fun y => shB X l M bB s y)
    (fun y => (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y) (fun y _ => (key y).2)
  rw [← Finset.smul_sum] at hs
  exact hs

theorem UpperTheory.V.Z.Kato.Nb.sRelT :
    UpperTheory.V.Z.Kato.Nb.SRelT := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he p _ hp c₀ Y hY r n
  obtain ⟨bB, hB, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, hgal, -⟩ := hA
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hB' : ∀ σ ∈ fixMu Ω (lvT l n r N p), LiftB X l N (2 * e - 1) n c₀ (∑ r₀, clsT X l n r N p x c d (2 * e - 1) (gm r₀) σ) (bB σ) := by
    intro σ hσ
    rw [← hw]
    exact hB σ hσ
  refine ⟨fun s y => GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s (y.1 * inv1 p l ^ (2 * (r + n)), y.2), b,
    fun s y => lift_push X l N _ n c₀ _ (rdT l n r N p) _ bB hB' s _, hb, fun s y => ?_⟩
  have key : ∀ t, pr (GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s t) = YfBT X l pr W e ψ n r N p bB s t := by
    intro t
    have hs := map_sum (AddMonoidHom.mk' pr hadd) (shB X l (lvT l n r N p) bB s)
      (Finset.univ.filter fun y' => rdT l n r N p y' = t)
    refine hs.trans (Finset.sum_congr rfl fun y' _ => ?_)
    exact hgal _ _ (hB' _ (arg_mem X _ s y')).1
  have := hC s y
  rw [lsq_eq l p _ hp, ← key] at this
  exact this
end

