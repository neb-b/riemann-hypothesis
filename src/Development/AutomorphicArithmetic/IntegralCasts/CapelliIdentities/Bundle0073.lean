module

public import Mathlib
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjSqrt
section
theorem UpperTheory.Reformulated.B.Rc9.conj_sqrt :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    (H.conj : H.E → H.E) H.sqd =
      -H.sqd := by
  intro R H
  have h := H.gal_sqd H.conj
  have hc : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
  have h2 : (R.toFrame.cc).1.2 = -1 := rfl
  rw [hc, h2] at h
  simpa using h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfFinitelyGenerated
section
private lemma UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg {R K ι : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Finite ι] (L : Submodule R (ι → K)) (hL : L.FG) :
    ∃ b : R, b ≠ 0 ∧ ∀ y ∈ L, ∀ i : ι, ∃ c : R, algebraMap R K c = algebraMap R K b * y i := by
  obtain ⟨S, rfl⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : S × ι => (p.1 : ι → K) p.2)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro y hy i
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := hb (⟨x, hx⟩, i)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add (f := _), hc, hd, Pi.add_apply, mul_add]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [map_mul, hc, Pi.smul_apply, Algebra.smul_def]; ring⟩

theorem UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator :
    ∀ (I : Formalism.MainNotions.S.AutInst),
      ∃ (b : NumberField.RingOfIntegers I.E),
        b ≠ (0 : NumberField.RingOfIntegers I.E) ∧
          ∀ y ∈ I.L, ∀ (i : Fin I.n), ∃ (c : NumberField.RingOfIntegers I.E), (↑c : I.E) = (↑b : I.E) * y i := by
  intro I
  exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg I.L I.L_fg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorRationalTensor
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh61.VQ :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → GlobalTheory.UPel.HT.Datum p → Type :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) ↦ TensorProduct ℤ ℚ D.La

private theorem UpperTheory.Reformulated.B.Qh61.exists_den {M : Type} [AddCommGroup M] (x : TensorProduct ℤ ℚ M) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : M, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | tmul q m =>
    refine ⟨q.den, q.den_pos, q.num • m, ?_⟩
    have h : q.den • q = q.num • (1 : ℚ) := by
      rw [nsmul_eq_mul, zsmul_eq_mul, mul_one, mul_comm, Rat.mul_den_eq_num]
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨k, hk, a, ha⟩ := hx
    obtain ⟨l, hl, b, hb⟩ := hy
    refine ⟨k * l, Nat.mul_pos hk hl, l • a + k • b, ?_⟩
    have e : ∀ (n : ℕ) (c : M), (1 : ℚ) ⊗ₜ[ℤ] (n • c) = n • ((1 : ℚ) ⊗ₜ[ℤ] c) := fun n c =>
      map_nsmul (TensorProduct.mk ℤ ℚ M 1) n c
    rw [TensorProduct.tmul_add, e, e, ← ha, ← hb, smul_add, smul_smul, smul_smul, mul_comm l k]

private theorem UpperTheory.Reformulated.B.Qh61.exists_denominator_rational_tensor {M : Type} [AddCommGroup M]
    (s : Finset (TensorProduct ℤ ℚ M)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ s, ∃ a : M, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  classical
  choose d hd a ha using fun x : TensorProduct ℤ ℚ M => UpperTheory.Reformulated.B.Qh61.exists_den x
  refine ⟨∏ x ∈ s, d x, Finset.prod_pos fun x _ => hd x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d hx
  refine ⟨c • a x, ?_⟩
  rw [hc, mul_comm, mul_smul, ha]
  exact (map_nsmul (TensorProduct.mk ℤ ℚ M 1) c (a x)).symm

theorem UpperTheory.Reformulated.B.Qh61.exists_den_finset :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) (s : Finset (UpperTheory.Reformulated.B.Qh61.VQ D)),
      ∃ (k : ℕ), (0 : ℕ) < k ∧ ∀ x ∈ s, ∃ (a : D.La), k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D s
  exact UpperTheory.Reformulated.B.Qh61.exists_denominator_rational_tensor s
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPrimeOfDifferentLe
section
attribute [local instance] Subfield.toField._proof_1 SubfieldClass.toField._proof_12 SubringClass.toRing._proof_8

theorem UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥H.F)),
    differentIdeal ℤ (NumberField.RingOfIntegers ↥H.F) ≤ v.asIdeal →
      ∃ (p : ℕ),
        Nat.Prime p ∧
          p ∣ H.QS * H.q * H.d ∧
            (↑p : NumberField.RingOfIntegers ↥H.F) ∈
              v.asIdeal := by
  intro R H v h
  have h1 := h (Ideal.absNorm_mem _)
  rw [NumberField.absNorm_differentIdeal H.F] at h1
  have h0 : (NumberField.discr H.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.F)
  rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Multiset.prod_coe] at h1
  obtain ⟨x, hx, hxv⟩ := (v.isPrime.multiset_prod_mem_iff_exists_mem _).1 h1
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  refine ⟨p, hpp, H.der.discr_primes.1 p hpp ?_, hxv⟩
  rw [H.der.discr_sq]
  exact (Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactorsList hp)).trans (dvd_pow_self _ two_ne_zero)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ModuliIntegralCharts
section
open NumberField

private theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.exists_zsmul_mem {E V : Type} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) {v : V} (hv : v ∈ Submodule.span E (L : Set V)) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : ((M * N : ℤ) : E) • (x + y) = N • ((M : E) • x) + M • ((N : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E N, ← Int.cast_smul_eq_zsmul E M ((N : E) • y), smul_smul,
        smul_smul, smul_add, Int.cast_mul, mul_comm (N : E)]
    rw [h]
    exact L.add_mem (zsmul_mem hx N) (zsmul_mem hy M)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨M, hM, hint⟩ := hc.exists_integral_multiple
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let a : 𝓞 E := ⟨M • c, hint⟩
    have ha : algebraMap (𝓞 E) E a = (M : E) * c := by
      rw [← zsmul_eq_mul]; rfl
    have h : ((M * N : ℤ) : E) • c • x = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, ha, smul_smul, smul_smul, Int.cast_mul, mul_right_comm]
    rw [h]
    exact L.smul_mem a hx

theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem :
    ∀ (I : Formalism.MainNotions.S.AutInst) (i : Fin I.n), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ Pi.single i (↑N : I.E) ∈ I.L := by
  intro I i
  obtain ⟨N, hN, h⟩ := UpperTheory.Reformulated.B.ModuliIntegralCharts.exists_zsmul_mem I.L
    (v := (Pi.single i (1 : I.E) : Fin I.n → I.E)) (by rw [I.L_span]; exact Submodule.mem_top)
  refine ⟨N, hN, ?_⟩
  rwa [← Pi.single_smul', smul_eq_mul, mul_one] at h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionMapComm
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.VA :
    Formalism.MainNotions.S.AutInst → Type :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ Fin I.n → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.sigA :
    (I : Formalism.MainNotions.S.AutInst) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) →+* TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)

noncomputable def UpperTheory.Reformulated.B.Qk24.colM :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} → (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) → Matrix (Fin I.n) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) ↦
      (Matrix.of :
          (Fin I.n → Fin k → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
            Matrix (Fin I.n) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)))
        fun (l : Fin I.n) (i : Fin k) ↦ b i l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.Jf :
    (I : Formalism.MainNotions.S.AutInst) → Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ I.J.map (⇑(Formalism.UG.inclE (Formalism.MainNotions.S.Af I.F)) : I.E → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))

noncomputable def UpperTheory.Reformulated.B.Qk24.rowM :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} → (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) → Matrix (Fin k) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) ↦
      Formalism.UG.cT (UpperTheory.Reformulated.B.Qk24.sigA I) (UpperTheory.Reformulated.B.Qk24.colM I b) * UpperTheory.Reformulated.B.Qk24.Jf I

noncomputable def UpperTheory.Reformulated.B.Qk24.Mk :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} →
        (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) →
          (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) →
            Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
              Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
                Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I)
        (X Y : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) ↦
      (1 : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) +
          UpperTheory.Reformulated.B.Qk24.colM I b * X * UpperTheory.Reformulated.B.Qk24.rowM I d +
        UpperTheory.Reformulated.B.Qk24.colM I d * Y * UpperTheory.Reformulated.B.Qk24.rowM I b

private theorem UpperTheory.Reformulated.B.Qk24.sandwich_mul {R : Type*} [Semiring R] {n k : Type*} [Fintype n] [Fintype k]
    (B C : Matrix n k R) (P Q : Matrix k n R) (X Y : Matrix k k R) :
    B * X * P * (C * Y * Q) = B * (X * (P * C * Y)) * Q := by
  simp only [Matrix.mul_assoc]

private theorem UpperTheory.Reformulated.B.Qk24.block_mul {R : Type*} [Semiring R] {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq n] (B D : Matrix n k R) (P Q : Matrix k n R) (H K : Matrix k k R)
    (h1 : P * B = H) (h2 : P * D = 0) (h3 : Q * B = 0) (h4 : Q * D = K) (X Y X' Y' : Matrix k k R) :
    (1 + B * X * P + D * Y * Q) * (1 + B * X' * P + D * Y' * Q) =
      1 + B * (X + X' + X * (H * X')) * P + D * (Y + Y' + Y * (K * Y')) * Q := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    UpperTheory.Reformulated.B.Qk24.sandwich_mul, h1, h2, h3, h4, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  abel

theorem UpperTheory.Reformulated.B.Qk24.Mk_mul :
    ∀ {I : Formalism.MainNotions.S.AutInst} {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) (η : TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)),
      UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I b =
          η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
        UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I d =
            (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
          UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I b =
              (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
            UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I d =
                (UpperTheory.Reformulated.B.Qk24.sigA I :
                            TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                    η •
                  (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
              ∀ (X Y X' Y' : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))),
                UpperTheory.Reformulated.B.Qk24.Mk I b d X Y * UpperTheory.Reformulated.B.Qk24.Mk I b d X' Y' =
                  UpperTheory.Reformulated.B.Qk24.Mk I b d
                    (X + X' + X * (η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) * X'))
                    (Y + Y' +
                      Y *
                        ((UpperTheory.Reformulated.B.Qk24.sigA I :
                                      TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                              η •
                            (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) *
                          Y')) := by
  intro I k b d η h1 h2 h3 h4 X Y X' Y'
  exact UpperTheory.Reformulated.B.Qk24.block_mul _ _ _ _ _ _ h1 h2 h3 h4 X Y X' Y'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VqInduction
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk61.VQ :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → GlobalTheory.UPel.HT.Datum p → Type :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) ↦ TensorProduct ℤ ℚ D.La

theorem UpperTheory.Reformulated.B.Qk61.vq_induction :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {D : GlobalTheory.UPel.HT.Datum p}
      {P : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D) → Prop},
      P (0 : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)) →
        (∀ (x y : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)), P x → P y → P (x + y)) →
          (∀ (a : GlobalTheory.LKTrip.AfP p) (t : ℚ) (x : D.La), P (a ⊗ₜ[ℚ] (t ⊗ₜ[ℤ] x))) →
            ∀ (v : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)), P v := by
  intro p _ D P h0 hadd htmul v
  induction v using TensorProduct.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero]; exact h0
    | tmul t x => exact htmul a t x
    | add x y hx hy => rw [TensorProduct.tmul_add]; exact hadd _ _ hx hy
end

