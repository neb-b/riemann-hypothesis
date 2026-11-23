module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ClsStep
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.XiAction

private theorem vc {M k : ℕ} [NeZero M] (h : k ∣ M) (a : ZMod M) :
    ((a.val : ℕ) : ZMod k) = ZMod.castHom h (ZMod k) a := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem cnd_iff (l N M : ℕ) [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g δ : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0) (hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod l) = 1)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • m') :
    Cnd l N g m ↔ Cnd l N g m' := by
  have e : ∀ i, m i 0 * (en δ 0 0 : ZMod M) + m i 1 * (en δ 1 0 : ZMod M) = (ν : ZMod M) * m' i 0 := by
    intro i
    have := congrFun (congrFun h i) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, en] using this
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  have uN : (en δ 0 0 : ZMod N) * (en δ 1 1 : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hδN] at this; simpa using this
  have ul : (en δ 0 0 : ZMod l) * (en δ 1 1 : ZMod l) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at this
    rw [hδl] at this; simpa using this
  have eN : ∀ i, ((m i 0).val : ZMod N) = ((m' i 0).val : ZMod N) := by
    intro i
    have := congrArg (ZMod.castHom hN (ZMod N)) (e i)
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, hδN, ← vc hN, ← vc hN, ← vc hN, ← vc hN, h1] at this
    linear_combination (en δ 1 1 : ZMod N) * this - (((m i 0).val : ZMod N) - ((m' i 0).val : ZMod N)) * uN
  have el : ∀ i, ((m i 0).val : ZMod l) * (en δ 0 0 : ZMod l) = ((m' i 0).val : ZMod l) := by
    intro i
    have := congrArg (ZMod.castHom hl (ZMod l)) (e i)
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, hδl, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2] at this
    linear_combination this
  unfold Cnd
  rw [eN 0, eN 1, ← el 0, ← el 1]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h3 => ?_, fun h3 => ?_⟩)
  · linear_combination (en δ 0 0 : ZMod l) * h3
  · linear_combination (en δ 1 1 : ZMod l) * h3 -
      ((en g 1 0 : ZMod l) * ((m 0 0).val : ZMod l) - (en g 0 0 : ZMod l) * ((m 1 0).val : ZMod l)) * ul

private theorem wt_dvd (l n M w : ℕ) [Fact l.Prime] [NeZero M] (hl : l ^ n ∣ M) (δ : Matrix (Fin 2) (Fin 2) ℤ)
    (ν : ZMod M) (h2 : (ν.val : ZMod (l ^ n)) = 1) (d d' : ZMod M) (hd : d' = ν ^ 2 * d)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * δ.map (Int.castRingHom (ZMod M)) = ν • m') (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ (d.val : ℤ_[l]) * (((m 0 0).val : ℤ_[l]) * (mZl l δ *ᵥ u) 0 + ((m 0 1).val : ℤ_[l]) * (mZl l δ *ᵥ u) 1) ^ w -
      (d'.val : ℤ_[l]) * (((m' 0 0).val : ℤ_[l]) * u 0 + ((m' 0 1).val : ℤ_[l]) * u 1) ^ w := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have e : ∀ j, ((m 0 0).val : ZMod (l ^ n)) * (δ 0 j : ZMod (l ^ n)) + ((m 0 1).val : ZMod (l ^ n)) * (δ 1 j : ZMod (l ^ n)) =
      ((m' 0 j).val : ZMod (l ^ n)) := by
    intro j
    have h0 : m 0 0 * (δ 0 j : ZMod M) + m 0 1 * (δ 1 j : ZMod M) = ν * m' 0 j := by
      have := congrFun (congrFun h 0) j
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have := congrArg (ZMod.castHom hl (ZMod (l ^ n))) h0
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2, one_mul] at this
    exact this
  have ed : (d'.val : ZMod (l ^ n)) = (d.val : ZMod (l ^ n)) := by
    rw [vc hl d', hd, map_mul, map_pow, ← vc hl, ← vc hl, h2, one_pow, one_mul]
  have ev : ∀ i, (mZl l δ *ᵥ u) i = (δ i 0 : ℤ_[l]) * u 0 + (δ i 1 : ℤ_[l]) * u 1 := by
    intro i
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ev, ev]
  simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, map_intCast]
  rw [ed, ← e 0, ← e 1, sub_eq_zero]
  congr 2
  ring

private theorem cls_step {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (n N : ℕ) (hN : 0 < N) (δ δ' : SL(2, ℤ))
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (f f' : X.Kˣ) (hf : Cgr (l ^ n) (slU X (ofSL δ') f) f') (k k' : ℤ_[l]) (hk : (l : ℤ_[l]) ^ n ∣ k - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (k • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        k' • clsK X l n (slD X N (f' : X.K))) = 0 := by
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨-, s2, s3, -⟩ := sSlD Ω ε X N hN
  have r1 := c5 (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f')
  have r3 := c4 _ _ _ _ r1 r2 (by
    obtain ⟨h, hh⟩ := hf
    refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩
    rw [← map_pow, ← map_mul, ← hh]
    apply Units.ext
    have := s2 _ _ (by rw [δ.det_coe]; exact one_pos) hc (f : X.K)
    rw [s3 δ'] at this
    exact this)
  have r4 := a5 k k' (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))) hk
  have r5 : AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        clsK X l n (slD X N (f' : X.K))) = 0 := r3
  rw [← sub_add_sub_cancel _ (k' • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))),
    map_add, r4, ← smul_sub, map_smul, r5, smul_zero, add_zero]

private theorem conj_ex (N : ℕ) (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ en δ 1 0) : ∃ δ' : SL(2, ℤ),
    !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨c, hc⟩ := h
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  refine ⟨⟨!![en δ 0 0, N * en δ 0 1; c, en δ 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of, ← hdet, hc]; ring
  · unfold en at hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, en, hc, mul_comm]

private theorem cd_row (N M₀ M : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (δ δ' : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0)
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (ν : ZMod M) (m m' : Matrix (Fin 2) (Fin 2) (ZMod M)) (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0)
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = ν • m') (x : Row M₀) :
    rt (x ᵥ* cD N M₀ m) δ' = ((ν.val : ZMod M₀) • x) ᵥ* cD N M₀ m' := by
  obtain ⟨d1, -, -, d4⟩ := sCdFacts N M₀ M hM
  have hN : N ∣ M := hM ▸ dvd_mul_right N M₀
  have e1 : ν • m' = !![ν, 0; 0, ν] * m' := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : x ᵥ* cD N M₀ (!![ν, 0; 0, ν] : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν.val : ZMod M₀) • x := by
    funext j
    fin_cases j <;> simp [cD, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  unfold rt
  rw [← d4 _ _ hc, Matrix.vecMul_vecMul, ← d1 _ _ hm ?_, h, e1, d1 _ _ ?_ hm', ← Matrix.vecMul_vecMul, e2]
  · simp
  · rw [vc hN, Matrix.map_apply, eq_intCast, map_intCast]; exact hδN

end UpperTheory.V.Z.Kato.Nb.XiAction

open UpperTheory.V.Z.Kato.Nb.XiAction in
theorem UpperTheory.V.Z.Kato.Nb.sXiAct :
    UpperTheory.V.Z.Kato.Nb.SXiAct := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy P a ha δ hδ ν h1 h2 hP u
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl1 : l ∣ l ^ n := dvd_pow_self l (by have := L.pos; omega)
  have hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.1
  have hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.2
  have h2' : ((ν : ZMod M).val : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hl1 (ZMod l)) h2
    rwa [map_natCast, map_one] at this
  obtain ⟨δ', hc⟩ := conj_ex N δ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hδN)
  let D : GL (Fin 2) (ZMod M) := Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ)
  let S : GL (Fin 2) (ZMod M) := Matrix.GeneralLinearGroup.scalar (Fin 2) ν
  let e : GL (Fin 2) (ZMod M) ≃ GL (Fin 2) (ZMod M) := (Equiv.mulRight D).trans (Equiv.mulLeft S⁻¹)
  have he : ∀ m, m * D = S * e m := fun m => by simp [e]
  have hrel : ∀ m : GL (Fin 2) (ZMod M), (m : Matrix (Fin 2) (Fin 2) (ZMod M)) *
      (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • (e m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro m
    have := congrArg (fun z : GL (Fin 2) (ZMod M) => (z : Matrix (Fin 2) (Fin 2) (ZMod M))) (he m)
    simp only [Units.val_mul] at this
    rw [Matrix.smul_eq_diagonal_mul]
    exact this
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det (e m) * ν ^ 2 := by
    intro m
    apply Units.ext
    have := congrArg Matrix.det (hrel m)
    rw [Matrix.det_mul, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, δ.det_coe, map_one, mul_one] at this
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this, mul_comm]; simp
  have hcnd := fun m : GL (Fin 2) (ZMod M) => cnd_iff l N M hN (hl1.trans hln) g δ hδN hδl ν h1 h2' _ _ (hrel m)
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l _ (Xi X l n N M₀ M w g x y P a _) - _) = 0
  unfold Xi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sub, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_equiv e (fun m => ?_) (fun m hm => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcnd m, hdet m, hP]
  · have hm1 := (Finset.mem_filter.1 hm).2.1
    have hm2 := (hcnd m).1 hm1
    rw [← sub_eq_zero, ← map_sub, map_smul]
    refine cls_step X l n N (NeZero.pos N) δ δ' hc _ _ ?_ _ _ ?_
    · rw [← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m), ← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m)]
      exact (ha _ _ ((sCdFacts N M₀ M L.eq).2.2.1 m hm1.1 x y hxy)).2 δ'
    · refine wt_dvd l n M w hln _ ν h2 _ _ ?_ _ _ (hrel m) u
      rw [hdet m, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      congr 1
      rw [mul_inv, mul_comm _ (ν ^ 2)⁻¹, mul_inv_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DetChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem fin_places (S : Finset ℕ) : {v : HeightOneSpectrum (𝓞 ℚ) | normV v ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 ℚ) | Ideal.absNorm I ≤ S.sup id}.Finite := Ideal.finite_setOf_absNorm_le _
  refine (h.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun v hv => ?_
  have : normV v ≤ S.sup id := Finset.le_sup (f := id) hv
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this

private theorem scal_iff {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    (∃ t : K, A = t • 1) ↔ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨A 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

private theorem det_of_quad {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (a c : K)
    (hA : ¬ ∃ t : K, A = t • 1) (h : A ^ 2 - a • A + c • (1 : Matrix (Fin 2) (Fin 2) K) = 0) : A.det = c := by
  rw [scal_iff] at hA
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have ht : A 0 0 + A 1 1 - a = 0 := by
    by_contra hne
    apply hA
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.1 (by linear_combination h01 : A 0 1 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact (mul_eq_zero.1 (by linear_combination h10 : A 1 0 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact sub_eq_zero.1 ((mul_eq_zero.1
        (by linear_combination h00 - h11 : (A 0 0 - A 1 1) * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne)
  rw [Matrix.det_fin_two]
  linear_combination A 0 0 * ht - h00

theorem UpperTheory.V.Z.Kato.Nb.sDetChar :
    UpperTheory.V.Z.Kato.Nb.SDetChar := by
  intro l _ Ω _ _ _ ρ χ hρ hχ ⟨s₀, hs₀⟩ S hF
  have hc : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρ
  have hχ' : Continuous fun s => (χ s : Qbar l) := Units.continuous_val.comp hχ
  have he : ∀ i j, Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i j := fun i j => hc.matrix_elem i j
  have hU : IsOpen {s | ¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1} := by
    simp only [scal_iff]
    exact (((isClosed_eq (he 0 1) continuous_const).inter
      ((isClosed_eq (he 1 0) continuous_const).inter (isClosed_eq (he 0 0) (he 1 1))))).isOpen_compl
  have hC : IsClosed {s | (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s} := isClosed_eq hc.matrix_det hχ'
  have hD := GlobalTheory.frob_dense_off_finite ℚ Ω _ (fin_places S)
  have key : ∀ s, (¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s := by
    intro s hs
    refine hC.closure_subset_iff.2 ?_ (hD.open_subset_closure_inter hU hs)
    rintro σ ⟨hσ, v, hv, B, hB, hf⟩
    obtain ⟨a, ha⟩ := hF v B σ hv hB hf
    exact det_of_quad _ a _ hσ ha
  intro s
  by_cases hs : ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1
  · obtain ⟨t, ht⟩ := hs
    have h0 := key s₀ (fun ⟨u, hu⟩ => hs₀ u hu)
    have h1 := key (s * s₀) (by
      rintro ⟨u, hu⟩
      rw [map_mul, Units.val_mul, ht, smul_mul_assoc, one_mul] at hu
      have t0 : t ≠ 0 := by
        rintro rfl
        exact (ρ s).ne_zero (by simpa using ht)
      exact hs₀ (t⁻¹ * u) (by rw [mul_smul, ← hu, smul_smul, inv_mul_cancel₀ t0, one_smul]))
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, h0] at h1
    exact mul_right_cancel₀ (χ s₀).ne_zero h1
  · exact key s hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

open CongruenceSubgroup

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

private theorem dc_fix (N w : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  unfold Tower.B at hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

private theorem dc_mul (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Tower.act_act Ω ε X l _ _ (by rw [σ.2]; norm_num) (by rw [τ.2]; norm_num),
    Matrix.SpecialLinearGroup.coe_mul]

private theorem dc_en (N : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hτ : τ ∈ Gamma0 N) :
    (en (σ * τ) 1 1 : ZMod N) = (en σ 1 1 : ZMod N) * (en τ 1 1 : ZMod N) := by
  have h0 := Gamma0_mem.1 hσ
  simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [h0]
  ring

private theorem dc_same (N w : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N ⊓ Gamma0 l) (hτ : τ ∈ Gamma0 N ⊓ Gamma0 l)
    (h : (en σ 1 1 : ZMod N) = (en τ 1 1 : ZMod N)) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) b := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = τ * σ⁻¹ := ⟨_, rfl⟩
  have hτ' : τ = ρ * σ := by rw [hρ, inv_mul_cancel_right]
  have hρ0 : ρ ∈ Gamma0 N ⊓ Gamma0 l := by
    rw [hρ]
    exact Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hσ)
  have det1 : ∀ B : SL(2, ℤ), B ∈ Gamma0 N → (en B 0 0 : ZMod N) * (en B 1 1 : ZMod N) = 1 := by
    intro B hB
    have h0 := Gamma0_mem.1 hB
    have hd := congrArg (fun z : ℤ => (z : ZMod N)) B.2
    simp only [Matrix.det_fin_two] at hd
    push_cast at hd
    rw [h0, mul_zero, sub_zero] at hd
    exact hd
  have hσ11 : (en σ⁻¹ 1 1 : ZMod N) = (en σ 0 0 : ZMod N) := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hρ11 : (en ρ 1 1 : ZMod N) = 1 := by
    rw [hρ, dc_en N τ σ⁻¹ hτ.1 (Subgroup.inv_mem _ hσ.1), ← h, hσ11, mul_comm]
    exact det1 σ hσ.1
  have hρ00 : (en ρ 0 0 : ZMod N) = 1 := by
    have := det1 ρ hρ0.1
    rw [hρ11, mul_one] at this
    exact this
  have hρG : ρ ∈ Gam N l := ⟨(Gamma1_mem _ _).2 ⟨hρ00, hρ11, Gamma0_mem.1 hρ0.1⟩, hρ0.2⟩
  rw [hτ', ← dc_mul X l ρ σ b, dc_fix X l N w ρ hρG b hb]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sDiamChar :
    UpperTheory.V.Z.Kato.Nb.SDiamChar := by
  unfold SDiamChar
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN hb
  obtain ⟨-, -, -, -, -, -, -, -, ⟨δ, hδ⟩, -⟩ := hA
  obtain ⟨b0, hb0, hne⟩ := hb
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hdiam : ∀ (q : ℕ) (b : X.Fn l),
      X.diam N l q b = X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b := fun q b => rfl
  have hcop : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → q.Coprime N := fun q hq hd =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hd (Dvd.dvd.mul_left h l))
  have hisD : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → IsDiam N l q (sgD N l q) :=
    fun q hq hd => Betti.isDiam_sgD hN0 hl.ne_zero (hcop q hq hd)
  have hpr : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b ∈ X.B N l (2 * e - 1),
      pr (X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b) = δ q • pr b :=
    fun q hq hd b hb => (hδ q hq hd b hb).2
  have cancel : ∀ a a' : Qbar l, a • pr b0 = a' • pr b0 → a = a' :=
    fun a a' h => smul_left_injective (Qbar l) hne h
  have hQ : ∀ u : (ZMod N)ˣ, ∃ q > l * N, q.Prime ∧ (q : ZMod N) = u :=
    fun u => Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (l * N)
  choose Q hQgt hQp hQu using hQ
  have hQd : ∀ u, ¬ Q u ∣ l * N := fun u h => by
    have h1 := Nat.le_of_dvd (Nat.mul_pos hl.pos hNpos) h
    have h2 := hQgt u
    omega
  have mem : ∀ u, sgD N l (Q u) ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
    fun u => (hisD _ (hQp u) (hQd u)).1
  have en_u : ∀ u, (en (sgD N l (Q u)) 1 1 : ZMod N) = u := fun u => by
    rw [(hisD _ (hQp u) (hQd u)).2, hQu]
  have inB : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l (2 * e - 1) :=
    fun u b hb => (sBStab Ω ε X l N (2 * e - 1) hNpos b hb).2.1 _ (mem u)
  have hΔ : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      pr (X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b) = δ (Q u) • pr b :=
    fun u b hb => hpr _ (hQp u) (hQd u) b hb
  have formula : ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N → (u : ZMod N) = q →
      ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = δ (Q u) • pr b := by
    intro q u hq hd hu b hb
    have e1 : X.diam N l q b = X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b := by
      rw [hdiam]
      exact dc_same X l N (2 * e - 1) _ _ (hisD q hq hd).1 (mem u)
        (by rw [(hisD q hq hd).2, en_u, hu]) b hb
    rw [e1]
    exact hΔ u b hb
  have mul : ∀ u v, δ (Q (u * v)) = δ (Q u) * δ (Q v) := by
    intro u v
    apply cancel
    have e2 : X.act l (((sgD N l (Q u) * sgD N l (Q v) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l (sgD N l (Q (u * v)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (Subgroup.mul_mem _ (mem u) (mem v)) (mem (u * v))
        (by rw [dc_en N _ _ (mem u).1 (mem v).1, en_u, en_u, en_u, Units.val_mul]) b0 hb0
    rw [← hΔ (u * v) b0 hb0, ← e2, ← dc_mul X l, hΔ v _ (inB u b0 hb0), hΔ u b0 hb0, smul_smul, mul_comm]
  have one : δ (Q 1) = 1 := by
    apply cancel
    rw [one_smul, ← hΔ 1 b0 hb0]
    have e3 : X.act l (sgD N l (Q 1) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (mem 1) (Subgroup.one_mem _) (by rw [en_u]; simp [en]) b0 hb0
    rw [e3, dc_fix X l N (2 * e - 1) 1 (Subgroup.one_mem _) b0 hb0]
  have inv : ∀ u : (ZMod N)ˣ, δ (Q u) * δ (Q u⁻¹) = 1 := fun u => by
    rw [← mul, mul_inv_cancel, one]
  refine ⟨MonoidHom.mk' (fun u => Units.mkOfMulEqOne (δ (Q u)) (δ (Q u⁻¹)) (inv u))
    (fun u v => by
      ext
      simp [mul]), ?_⟩
  intro q u hq hd hu b hb
  simp only [MonoidHom.mk'_apply, Units.val_mkOfMulEqOne]
  exact formula q u hq hd hu b hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvMemO
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem inv_mem_O {l : ℕ} [Fact l.Prime] (c : Coef l) {p : ℕ} (hp : Nat.Coprime l p) :
    ((p : Qbar l))⁻¹ ∈ c.O := by
  have hu : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hv
  rw [map_mul, map_natCast, map_one] at h
  rw [← eq_inv_of_mul_eq_one_right h]
  exact c.O.algebraMap_mem v

theorem UpperTheory.V.Z.Kato.Nb.sEulCg :
    UpperTheory.V.Z.Kato.Nb.SEulCg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ _ p n hp hn hd a δ ha hδ
  obtain ⟨k, hk⟩ := hd
  have hpk : p = l ^ n * k + 1 := by have := hp.pos; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcop : Nat.Coprime l p := by
    rw [hpk, pow_succ', mul_assoc]
    simp
  have hq := inv_mem_O cf hcop
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  refine ⟨?_, ?_⟩
  · unfold eul
    rw [← inv_pow, ← inv_pow]
    exact add_mem (sub_mem (one_mem _) (mul_mem ha (pow_mem hq _))) (mul_mem hδ (pow_mem hq _))
  intro σ hψ he htr hdet
  have hc : (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = p := by
    apply Subtype.val_injective
    apply (algebraMap ℚ_[l] (Qbar l)).injective
    have h : eps l σ = algebraMap ℚ_[l] (Qbar l) ((cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) : ℚ_[l]) := rfl
    rw [he] at h
    refine h.symm.trans ?_
    simp
  have hm : ((((cycMod (F := ℚ) (Ω := Ω) l 1 σ : ZMod (l ^ 1))).val : ℕ) : ZMod l) = 1 := by
    have h : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) := rfl
    rw [h, hc, map_natCast, ZMod.val_natCast, pow_one, ZMod.natCast_mod, hpk]
    simp
  have hth : thK l e ψ σ = ((p : Qbar l) ^ e)⁻¹ := by
    unfold thK
    rw [hm, hψ, he, mul_one]
  unfold rhoK at htr hdet
  rw [hth, inv_inv] at htr hdet
  rw [Matrix.trace_smul, Matrix.trace_fin_two, smul_eq_mul] at htr
  rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm e 2, Matrix.det_fin_two] at hdet
  have hdet' := mul_left_cancel₀ (pow_ne_zero _ hp0) hdet
  have hpc : (p : Qbar l) = (l : Qbar l) ^ (m + 1) * k + 1 := by exact_mod_cast hpk
  have ho : (k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p)) ∈ cf.O :=
    mul_mem (natCast_mem _ _) (sub_mem (mul_mem ha (pow_mem hq _))
      (mul_mem (mul_mem hδ (pow_mem hq _)) (add_mem (one_mem _) (natCast_mem _ _))))
  have key : eul l e p a δ - 1 * (mat W σ - 1).det =
      (l : Qbar l) ^ (m + 1) * ((k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p))) := by
    rw [← mul_assoc, ← sub_eq_of_eq_add hpc, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    unfold eul
    rw [← htr, ← hdet']
    simp only [inv_pow]
    field_simp
    ring
  unfold GlobalTheory.Ord2.Cg
  rw [key, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (nle cf ho)
end

