module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootArithVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootArithmeticVariety

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by
    simp [Polynomial.eval₂_sub, h]⟩

theorem isIntegral_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun σ _ => ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => hM (σ i) i) _

theorem isIntegral_onePipe {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, IsIntegral ℤ (Z a b))
    (a : Fin j) (b : Fin (j + m)) : IsIntegral ℤ (onePipe Z a b) := by
  simp only [onePipe, Matrix.of_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) b
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    exact hZ a i

theorem isIntegral_rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id]
  refine isIntegral_onePipe _ (fun a b => ?_) _ _
  obtain ⟨k, hk, h⟩ := hζ p.1 a b
  exact isIntegral_of_pow_eq_one hk h

end RootArithmeticVariety


open RootArithmeticVariety in
theorem RootArithVar.proof (h : CoordConeArithVar.Statement) : RootArithVar.Statement := by
  intro f j m ζ hf hζ
  have hK : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have := h (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) (fun _ => plAnchor j m) 0 Fin.elim0 hK
    (fun k => by simp [rootCoord, anchor_minor]) (algebraicIndependent_empty_type)
    (fun i => Fin.elim0 i) ?_
  · simpa [rootPointIdeal] using this
  · rintro r ⟨p, rfl⟩
    have h1 : IsIntegral ℚ (rootCoord ζ p / rootCoord ζ ⟨p.1, plAnchor j m⟩) := by
      simp only [rootCoord, anchor_minor, div_one]
      exact (isIntegral_rootCoord ζ hζ p).tower_top
    exact (h1.tower_top (A := IntermediateField.adjoin ℚ (Set.range (Fin.elim0 : Fin 0 → ℂ)))).isAlgebraic

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDivSuppEmpty
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootDivisorSupportEmpty

theorem isIntegral_of_pow_eq_one {z : ℂ} {k : ℕ} (hk : 0 < k) (hz : z ^ k = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hz]⟩

theorem isIntegral_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  have : M.det ∈ integralClosure ℤ ℂ := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => h _ _) _
  exact this

theorem isIntegral_rootCoord {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  refine Fin.addCases (fun c => ?_) (fun c => ?_) ((p.2.1.orderEmbOfFin p.2.2) b)
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hz⟩ := hζ p.1 a c
    exact isIntegral_of_pow_eq_one hk hz

end RootDivisorSupportEmpty


open RootDivisorSupportEmpty in
theorem RootDivSuppEmpty.proof : RootDivSuppEmpty.Statement := by
  intro f j m ζ hζ
  ext Q
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hQmin, hrel⟩
  have hQp : Q.IsPrime := hQmin.1.1
  have hle := hQmin.1.2
  have hs : rootAnchorSection f j m ∈ Q := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨τ, -, hτ⟩ := (hQp.prod_mem_iff).1 hs
  obtain ⟨I, hI⟩ := hrel τ
  apply hI
  obtain ⟨p, hpm, hp⟩ := isIntegral_rootCoord hζ ⟨τ, I⟩
  set n := p.natDegree
  set G : MRing (plBlocks f j m) := ∑ k ∈ Finset.range (n + 1),
    C (p.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (n - k) with hGdef
  have hy0 : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchor_minor _ _ _
  have hG : G ∈ rootPointIdeal ζ := by
    rw [rootPointIdeal, mCoordIdeal, RingHom.mem_ker]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hGdef, mConeMap, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      hy0, MvPolynomial.C_1, one_mul]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        algebraMap ℤ (MvPolynomial (Fin f) ℂ) (p.coeff k) * (C (rootCoord ζ ⟨τ, I⟩) * X τ) ^ k *
          (X τ : MvPolynomial (Fin f) ℂ) ^ (n - k) =
        C ((p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k) * X τ ^ n := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [eq_intCast, ← map_intCast (C : ℂ →+* MvPolynomial (Fin f) ℂ), mul_pow, C_mul, C_pow,
        ← Nat.add_sub_cancel' hkn, pow_add, Nat.add_sub_cancel_left]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
    have hsum : ∑ k ∈ Finset.range (n + 1), (p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k = 0 := by
      rw [← hp, Polynomial.eval₂_eq_sum_range]
      simp [n]
    rw [hsum, MvPolynomial.C_0, zero_mul]
  have hGQ : G ∈ Q := hle (Ideal.mem_sup_left hG)
  have h0 : Ideal.Quotient.mk Q (X ⟨τ, plAnchor j m⟩) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hτ
  have hpow : Ideal.Quotient.mk Q (X ⟨τ, I⟩) ^ n = 0 := by
    have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hGQ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hGdef, map_sum, map_mul, map_pow, h0] at h1
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self, pow_zero, mul_one,
      hpm.coeff_natDegree, map_one, map_one, one_mul] at h1
    · exact h1
    · intro k hk
      rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)), mul_zero]
  have := hQp
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_pow_eq_zero hpow)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootHeightNE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

theorem anchor_homog (f j m : ℕ) : IsMultiHomog (rootAnchorSection f j m) (fun _ => 1) := by
  classical
  intro μ hμ k
  have hdeg : rootAnchorSection f j m = monomial (∑ τ : Fin f, Finsupp.single (⟨τ, plAnchor j m⟩ : Σ _ : Fin f, PlIdx j m) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]; rfl
  rw [hdeg] at hμ
  have := MvPolynomial.support_monomial_subset hμ
  rw [Finset.mem_singleton] at this
  subst this
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single (plAnchor j m)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hτ (congrArg Sigma.fst h)
  · simp

theorem RootHeight.proofNE (hA : RootArithVar.Statement) (hD : RootDivSuppEmpty.Statement)
    (hL : RootLogNormBound.Statement) (hF : RootPointsFinite.Statement) (hP : PtsIntegralZeroLowerNE.Statement)
    (hM : MultiHomogMemCoord.Statement) (hS : FsLineSmooth.Statement) : RootHeight.Statement := by
  intro f j m ζ hf hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := hA f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, hM (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := hS _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := hP (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-grassConst f j m)
    hV.2.1.2.1 (hF f j m ζ hζ) ?_ (hL f j m ζ hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, hD f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hpos := (fsMulti (plBlocks f j m)).pos z hz.1
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p) (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointConj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootPointConjugation

theorem aeval_mul_monomial {σ A : Type*} [CommRing A] (s : A) (x : σ → A) (μ : σ →₀ ℕ) (c : ℤ) :
    aeval (fun i => s * x i) (monomial μ c) = s ^ (μ.sum fun _ e => e) * aeval x (monomial μ c) := by
  simp only [aeval_monomial, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

theorem sum_homog {σ A : Type*} [CommRing A] (S : Finset (σ →₀ ℕ)) (N : ℕ)
    (hS : ∀ μ ∈ S, (μ.sum fun _ e => e) ≤ N) (s : A) (g : (σ →₀ ℕ) → A) :
    ∑ μ ∈ S, s ^ (N - μ.sum fun _ e => e) * (s ^ (μ.sum fun _ e => e) * g μ) = s ^ N * ∑ μ ∈ S, g μ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ hμ => by rw [← mul_assoc, pow_sub_mul_pow _ (hS μ hμ)]

theorem homog_vanish {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (z : (Σ _ : Fin f, PlIdx j m) → ℂ) (hz : z ∈ mcPts (rootPointIdeal ζ)) (τ : Fin f)
    (u : PlIdx j m → ℂ) (hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I)
    (Q : MvPolynomial (PlIdx j m) ℤ) (hQ : aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0) :
    z ⟨τ, plAnchor j m⟩ ^ Q.totalDegree * aeval u Q = 0 := by
  classical
  have hS : ∀ μ ∈ Q.support, (μ.sum fun _ e => e) ≤ Q.totalDegree := fun μ hμ => le_totalDegree hμ
  set H : MRing (plBlocks f j m) := ∑ μ ∈ Q.support,
    X ⟨τ, plAnchor j m⟩ ^ (Q.totalDegree - μ.sum fun _ e => e) *
      rename (Sigma.mk τ) (monomial μ (AddMonoidAlgebra.coeff Q μ)) with hH
  have hmem : H ∈ rootPointIdeal ζ := by
    show mConeMap (rootCoord ζ) H = 0
    have hC : ∀ P : MvPolynomial (PlIdx j m) ℤ,
        aeval (fun I => (C (rootCoord ζ ⟨τ, I⟩) : MvPolynomial (Fin f) ℂ)) P =
          C (aeval (fun I => rootCoord ζ ⟨τ, I⟩) P) := by
      intro P
      induction P using MvPolynomial.induction_on <;> simp_all
    have hcomp : (fun p => C (rootCoord ζ p) * (X p.1 : MvPolynomial (Fin f) ℂ)) ∘ Sigma.mk τ =
        fun I => X τ * C (rootCoord ζ ⟨τ, I⟩) := by
      funext I; simp [mul_comm]
    have ha : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchor_minor j m (ζ τ)
    have hsc : ∀ (μ : PlIdx j m →₀ ℕ) (c : ℤ),
        aeval (fun I => X τ * (C (rootCoord ζ ⟨τ, I⟩) : MvPolynomial (Fin f) ℂ)) (monomial μ c) =
          X τ ^ (μ.sum fun _ e => e) * aeval (fun I => C (rootCoord ζ ⟨τ, I⟩)) (monomial μ c) :=
      fun μ c => aeval_mul_monomial _ _ μ c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_rename, hcomp,
      hsc, hC, ha, map_one, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_homog _ _ hS, ← map_sum, ← map_sum, ← as_sum, hQ, map_zero, mul_zero]
  have hE := hz.2 H hmem
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def] at hE
  have hcomp2 : z ∘ Sigma.mk τ = fun I => z ⟨τ, plAnchor j m⟩ * u I := funext hu
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hH, map_sum, map_mul, map_pow, aeval_X, aeval_rename, hcomp2, aeval_mul_monomial] at hE
  rwa [sum_homog _ _ hS, ← map_sum, ← as_sum] at hE

def colAB {j m : ℕ} (a : Fin j) (b : Fin m) (c : Fin j) : Fin (j + m) :=
  if c = a then Fin.natAdd j b else Fin.castAdd m c

theorem colAB_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (colAB a b) := by
  intro c d h
  by_cases hc : c = a <;> by_cases hd : d = a <;>
    simp_all [colAB, Fin.ext_iff] <;> omega

def idxAB {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨colAB a b, colAB_injective a b⟩, by simp⟩

theorem entry_eq_minor {j m : ℕ} (a : Fin j) (b : Fin m) :
    ∃ s : ℤ, ∀ (R : Type) [CommRing R] (Z : Matrix (Fin j) (Fin m) R),
      Z a b = s * (colsOf (onePipe Z) (idxAB a b)).det := by
  classical
  set I := idxAB a b
  have hmem : ∀ c, colAB a b c ∈ I.1 := fun c => by simp [I, idxAB]
  let e' : Fin j → Fin j := fun c => (I.1.orderIsoOfFin I.2).symm ⟨colAB a b c, hmem c⟩
  have he' : ∀ c, I.1.orderEmbOfFin I.2 (e' c) = colAB a b c := fun c => by
    rw [← Finset.coe_orderIsoOfFin_apply]; simp [e']
  have hinj : Function.Injective e' := fun c d h => colAB_injective a b (by rw [← he', ← he', h])
  let e := Equiv.ofBijective e' (Finite.injective_iff_bijective.mp hinj)
  refine ⟨(Equiv.Perm.sign e : ℤ), fun R _ Z => ?_⟩
  have hsub : (colsOf (onePipe Z) I).submatrix id e = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r c
    simp only [submatrix_apply, colsOf, id, e, Equiv.ofBijective_apply, he', updateCol_apply, onePipe,
      of_apply, colAB]
    split_ifs <;> simp [Fin.append_left, Fin.append_right]
  have := Matrix.det_permute' e (colsOf (onePipe Z) I)
  rw [hsub, ← cramer_apply, cramer_one] at this
  exact this

theorem map_minor {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {j m : ℕ}
    (Z : Matrix (Fin j) (Fin m) R) (I : PlIdx j m) :
    φ (colsOf (onePipe Z) I).det = (colsOf (onePipe (Z.map φ)) I).det := by
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, map_apply, colsOf, submatrix_apply, onePipe, of_apply, id]
  generalize I.1.orderEmbOfFin I.2 c = x
  refine Fin.addCases (fun c' => ?_) (fun b => ?_) x
  · simp [Fin.append_left, Matrix.one_apply]
  · simp [Fin.append_right]

end RootPointConjugation


open RootPointConjugation in
theorem RootPointConj.proof (h : RootAnchorNonzero.Statement) : RootPointConj.Statement := by
  intro f j m ζ hζ z hz τ
  classical
  have h0 : z ⟨τ, plAnchor j m⟩ ≠ 0 := h f j m ζ hζ z hz τ
  set u : PlIdx j m → ℂ := fun I => z ⟨τ, I⟩ / z ⟨τ, plAnchor j m⟩
  have hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I := fun I => by simp [u, mul_div_cancel₀ _ h0]
  have hker : ∀ Q : MvPolynomial (PlIdx j m) ℤ,
      aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0 → aeval u Q = 0 := fun Q hQ =>
    (mul_eq_zero.mp (homog_vanish ζ z hz τ u hu Q hQ)).resolve_left (pow_ne_zero _ h0)
  choose s hs using fun a b => entry_eq_minor (j := j) (m := m) a b
  let E : Matrix (Fin j) (Fin m) (MvPolynomial (PlIdx j m) ℤ) :=
    Matrix.of fun a b => C (s a b) * X (idxAB a b)
  have hE : E.map (aeval fun I => rootCoord ζ ⟨τ, I⟩) = ζ τ := by
    ext a b
    simp [E, rootCoord, ← hs a b ℂ (ζ τ)]
  refine ⟨E.map (aeval u), fun a b => ?_, fun I => ?_⟩
  · obtain ⟨k, hk, hk1⟩ := hζ τ a b
    refine ⟨k, hk, ?_⟩
    have hq := hker (E a b ^ k - 1) (by
      rw [map_sub, map_pow, map_one, ← hk1, ← hE]; simp)
    simpa [sub_eq_zero] using hq
  · have hq := hker (X I - (colsOf (onePipe E) I).det) (by
      rw [map_sub, aeval_X]
      have := map_minor (aeval fun I => rootCoord ζ ⟨τ, I⟩).toRingHom E I
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      rw [this, hE]
      exact sub_eq_zero.mpr rfl)
    rw [map_sub, aeval_X, sub_eq_zero] at hq
    have := map_minor (aeval u).toRingHom E I
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [hu I, hq, this]

end

end GroundTheory.Heights₂.Heights
end

