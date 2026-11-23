module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquiv
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.Transport

variable {R S : Type} [CommRing R] [CommRing S]

def mapF (φ : R →+* S) (F : ℂ → MvPolynomial (Fin 2) R) : ℂ → MvPolynomial (Fin 2) S :=
  fun z => MvPolynomial.map φ (F z)

theorem map_smul' (φ : R →+* S) (c : R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (c • p) = φ c • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_slP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (slP m p) = slP m (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, Betti.slP_X, MvPolynomial.map_X, map_add (f := _), map_smul', map_intCast]

theorem mapF_add (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F + G) = mapF φ F + mapF φ G := by
  funext z; simp [mapF]

theorem mapF_sub (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F - G) = mapF φ F - mapF φ G := by
  funext z; simp [mapF]

theorem mapF_smul (φ : R →+* S) (c : R) (F : ℂ → MvPolynomial (Fin 2) R) : mapF φ (c • F) = φ c • mapF φ F := by
  funext z; simp [mapF, map_smul']

theorem mapF_sum {ι : Type} (φ : R →+* S) (s : Finset ι) (F : ι → ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (∑ j ∈ s, F j) = ∑ j ∈ s, mapF φ (F j) := by
  funext z; simp [mapF, Finset.sum_apply, map_sum]

theorem mapF_opP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opP R m F) = opP S m (mapF φ F) := by
  funext z; simp [mapF, opP, map_slP]

theorem mapF_opL (φ : R →+* S) (N l : ℕ) (T : Letter) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opL R N l T F) = opL S N l T (mapF φ F) := by
  cases T with
  | T q => simp only [opL, LinearMap.add_apply, LinearMap.sum_apply, mapF_add, mapF_sum, mapF_opP]
  | U => simp only [opL, LinearMap.sum_apply, mapF_sum, mapF_opP]
  | D d => simp only [opL, mapF_opP]

theorem mapF_mem_pot (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Pot R w Γ) : mapF φ F ∈ Pot S w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map φ, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map φ p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, map_slP]; rfl

theorem mapF_mem_triv (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Triv R w Γ) : mapF φ F ∈ Triv S w Γ := by
  obtain ⟨ψ, p, h1, h2⟩ := hF
  refine ⟨mapF φ ψ, MvPolynomial.map φ p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
  · simp only [mapF]; rw [← map_slP, h1 γ hγ z hz]
  · simp only [mapF]; rw [h2 z hz, map_add (f := _)]

theorem exists_preimage (ι : R ≃+* S) (N l : ℕ) (lam : Letter → R) {P : FreeAlgebra S Letter} (hP : P ∈ admissibleLettersSubalgebra S N l) :
    ∃ Q ∈ admissibleLettersSubalgebra R N l, ι (FreeAlgebra.lift R lam Q) = FreeAlgebra.lift S (fun T => ι (lam T)) P ∧
      ∀ F, mapF (ι : R →+* S) (FreeAlgebra.lift R (opL R N l) Q F) =
        FreeAlgebra.lift S (opL S N l) P (mapF (ι : R →+* S) F) := by
  unfold admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact ⟨FreeAlgebra.ι R T, Algebra.subset_adjoin ⟨T, hT, rfl⟩, by simp, fun F => by simp [mapF_opL]⟩
  | algebraMap r =>
    refine ⟨algebraMap R _ (ι.symm r), Subalgebra.algebraMap_mem _ _, by simp, fun F => ?_⟩
    simp [Module.algebraMap_end_apply, mapF_smul]
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q + Q', add_mem hQ hQ', by simp [h1, h1'], fun F => by simp [mapF_add, h2, h2']⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q * Q', mul_mem hQ hQ', by simp [h1, h1'], fun F => by simp [h2, h2']⟩

theorem mapF_symm_mapF (ι : R ≃+* S) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF (ι.symm : S →+* R) (mapF (ι : R →+* S) F) = F := by
  funext z
  simp only [mapF, MvPolynomial.map_map]
  rw [RingEquiv.symm_comp, MvPolynomial.map_id]

end GlobalTheory.KZ.Transport


open GlobalTheory.KZ.Transport in
theorem GlobalTheory.KZ.ssPot_transport : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E),
    SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧
      ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T →
        (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  intro N l w E _ ι lam ⟨P, hP, h1, h2⟩
  obtain ⟨Q, hQ, e1, e2⟩ := exists_preimage ι N l lam hP
  refine ⟨Q, hQ, ι.injective (by rw [e1, h1, map_one]), fun F hF T hT => ?_⟩
  have h := mapF_mem_triv (ι.symm : ℂ →+* E) (h2 _ (mapF_mem_pot (ι : E →+* ℂ) hF) T hT)
  rw [← e2] at h
  rw [← mapF_symm_mapF ι ((opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) Q F))]
  convert h using 2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, mapF_sub, mapF_smul, mapF_opL]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEq
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCong

theorem cong_iff_dg : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ),
    Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  intro N d u hu γ γ'
  have key : (dg u * redGL N γ' = redGL N γ * dg u) ↔
      ((dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) * (redGL N γ' : Matrix (Fin 2) (Fin 2) (ZMod N)) =
        (redGL N γ : Matrix (Fin 2) (Fin 2) (ZMod N)) * (dg u : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
    constructor
    · intro h; rw [← Units.val_mul, h, Units.val_mul]
    · intro h; ext1; simpa using h
  rw [key]
  have hM : ∀ δ : SL(2, ℤ), (redGL N δ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![(en δ 0 0 : ZMod N), en δ 0 1; en δ 1 0, en δ 1 1] := by
    intro δ
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hD : (dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![1, 0; 0, (d : ZMod N)] := by
    show !![1, 0; 0, (u : ZMod N)] = _
    rw [hu]
  rw [hM, hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [Cong, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, one_mul, zero_mul, add_zero,
    zero_add, mul_one, mul_zero]
  have hdu : IsUnit (d : ZMod N) := hu ▸ u.isUnit
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
    · rw [h2, mul_comm]
    · rw [h3]
    · rw [h4, mul_comm]
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · rw [h2, mul_comm]
    · rw [mul_comm] at h4
      exact hdu.mul_right_cancel h4

end GlobalTheory.FNCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEq
section
open GlobalTheory.K5 GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.Glue.DPsi

variable {p : ℕ} [Fact p.Prime]

theorem thL_add (a b : Lau p) : thL (a + b) = thL a + thL b := by
  ext r
  simp [thL, mul_add]

theorem thL_zero : thL (0 : Lau p) = 0 := by
  ext r
  simp [thL]

def sh (N : ℕ) (i : ℤ) (w : ℤ → ℤ_[p]) (b : Lau p) : Lau p where
  coeff r := if (N : ℤ) ∣ r then w r * b.coeff (r + i) else 0
  isPWO_support' := by
    refine (b.isPWO_support.image_of_monotone (f := fun r : ℤ => r - i) (fun x y h => by simpa using h)).mono ?_
    intro r hr
    refine ⟨r + i, ?_, by simp⟩
    intro h
    apply hr
    simp [h]

def dn (N : ℕ) (hN : 0 < N) (B : Lau p) : Lau p where
  coeff j := B.coeff ((N : ℤ) * j)
  isPWO_support' := by
    have hm : StrictMono (fun j : ℤ => (N : ℤ) * j) := fun x y h =>
      mul_lt_mul_of_pos_left h (by exact_mod_cast hN)
    have hwf := B.isPWO_support
    rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt] at hwf ⊢
    intro g hg
    obtain ⟨m, n, hmn, h⟩ := hwf (fun k => (N : ℤ) * g k) hg
    exact ⟨m, n, hmn, hm.le_iff_le.1 h⟩

theorem coeff_natCast_mul (n : ℕ) (X : Lau p) (s : ℤ) : ((n : Lau p) * X).coeff s = (n : ℤ_[p]) * X.coeff s := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ_[p], HahnSeries.coeff_smul, smul_eq_mul]

theorem decomp (N : ℕ) (hN : 0 < N) (b : Lau p) :
    b = ∑ i ∈ Finset.range N, HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b := by
  ext s
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single (s % N).toNat]
  · have h0 : (((s % N).toNat : ℕ) : ℤ) = s % N := Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')
    have h1 : (N : ℤ) ∣ s - s % N := Int.dvd_self_sub_emod
    rw [HahnSeries.coeff_single_mul, h0]
    simp [sh, h1]
  · intro i hi hne
    have h1 : ¬ (N : ℤ) ∣ s - i := by
      intro h
      have h2 : (i : ℤ) % N = s % N := (Int.modEq_iff_dvd).2 h
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.1 hi)] at h2
      apply hne
      rw [← h2]
      simp
    rw [HahnSeries.coeff_single_mul]
    simp [sh, h1]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    have := Int.emod_lt_of_pos s hN'
    have := Int.emod_nonneg s hN'.ne'
    omega

theorem thL_part (N i : ℕ) (b : Lau p) :
    thL (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) =
      (i : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) +
      (N : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun r => ((r / N : ℤ) : ℤ_[p])) b) := by
  ext s : 2
  rw [HahnSeries.coeff_add, coeff_natCast_mul, coeff_natCast_mul]
  change (s : ℤ_[p]) * _ = _
  simp only [HahnSeries.coeff_single_mul, sh, one_mul]
  split_ifs with h
  · have h1 : (s : ℤ_[p]) = i + N * (((s - i) / N : ℤ) : ℤ_[p]) := by
      have h2 : s = i + N * ((s - i) / N) := by rw [Int.mul_ediv_cancel' h]; ring
      exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) h2
    rw [← mul_assoc, ← add_mul, ← h1]
  · simp

theorem part_eq_zero {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] [Module A M]
    (D : Derivation A R M) (q β γ : R) (i N : ℕ) (hβ : D β = 0) (hN : (N : R) • D q = 0) :
    q • D (q ^ i * β) - ((i : R) * (q ^ i * β) + (N : R) * γ) • D q = 0 := by
  rw [Derivation.leibniz, hβ, smul_zero, zero_add, add_smul, mul_comm (N : R), mul_smul γ, hN, smul_zero, add_zero,
    Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_smul, smul_smul, ← sub_smul]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h : q * β * i * q ^ (i - 1) - i * (q ^ i * β) = 0 := by
      conv_lhs => rw [← mul_pow_sub_one hi.ne' q]
      ring
    rw [h, zero_smul]

theorem smul_D_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  intro p hp Ω _ _ T L ψ hψ b x y qL hx hy hq
  have hqi : IsIntegral (O0 p) (T.qq L) :=
    IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hmem : ∀ z, ψ z ∈ integralClosure (O0 p) Ω := fun z => by
    have h1 : ψ z ∈ ψ.range := ⟨z, rfl⟩
    rw [hψ.rng] at h1
    exact adjoin_le_integralClosure hqi h1
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Lau p →+* integralClosure (O0 p) Ω, ∀ c, (Ψ c : Ω) = ψ (algebraMap (Lau p) (O0 p) c) :=
    ⟨(ψ.codRestrict (integralClosure (O0 p) Ω) hmem).comp (algebraMap (Lau p) (O0 p)), fun _ => rfl⟩
  have hx' : x = Ψ b := Subtype.ext (hx.trans (hΨ _).symm)
  have hy' : y = Ψ (thL b) := Subtype.ext (hy.trans (hΨ _).symm)
  rw [hx', hy']
  generalize KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) = D
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hqN : qL ^ p ^ L = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow, hq, Basic.qq_pow]; rfl)
  have hND : ((p ^ L : ℕ) : integralClosure (O0 p) Ω) • D qL = 0 := by
    have h1 : D (qL ^ p ^ L) = 0 := by rw [hqN]; exact D.map_algebraMap _
    rw [Derivation.leibniz_pow] at h1
    have h2 : qL • ((p ^ L) • qL ^ (p ^ L - 1) • D qL) = 0 := by rw [h1, smul_zero]
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), smul_smul, smul_smul, mul_right_comm,
      mul_pow_sub_one hN.ne', hqN, mul_smul] at h2
    have hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p)) := (Basic.isUnit_qO p).map _
    exact hu.smul_left_cancel.1 (h2.trans (smul_zero _).symm)
  have hmono : ∀ i : ℕ, Ψ (HahnSeries.single (i : ℤ) (1 : ℤ_[p])) = qL ^ i := by
    intro i
    have h1 : (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) : Lau p) = (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) ^ i := by
      rw [HahnSeries.single_pow]; simp
    have h2 : Ψ (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) = qL :=
      Subtype.ext (by rw [hΨ, hq]; exact hψ.par)
    rw [h1, map_pow, h2]
  have hsub : ∀ (i : ℤ), D (Ψ (sh (p ^ L) i (fun _ => 1) b)) = 0 := by
    intro i
    have h1 : Ψ (sh (p ^ L) i (fun _ => 1) b) = algebraMap (O0 p) (integralClosure (O0 p) Ω)
        (algebraMap (Lau p) (O0 p) (dn (p ^ L) hN (sh (p ^ L) i (fun _ => 1) b))) := by
      apply Subtype.ext
      rw [hΨ]
      refine hψ.sub _ _ (fun j => ?_) (fun r hr => ?_)
      · simp [dn]
      · have h2 : ¬ ((p ^ L : ℕ) : ℤ) ∣ r := by simpa using hr
        exact if_neg h2
    rw [h1]
    exact D.map_algebraMap _
  let E : Lau p →+ KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω) :=
    { toFun := fun c => qL • D (Ψ c) - Ψ (thL c) • D qL
      map_zero' := by simp [thL_zero]
      map_add' := by
        intro a c
        simp only [thL_add, map_add (f := _), add_smul, smul_add]
        abel }
  have hpart : ∀ i ∈ Finset.range (p ^ L),
      E (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh (p ^ L) i (fun _ => 1) b) = 0 := by
    intro i _
    change qL • D (Ψ _) - Ψ (thL _) • D qL = 0
    rw [thL_part, map_add Ψ, map_mul Ψ (i : Lau p), map_mul Ψ ((p ^ L : ℕ) : Lau p), map_mul Ψ, map_natCast Ψ, map_natCast Ψ, hmono]
    exact part_eq_zero D qL _ _ i (p ^ L) (hsub i) hND
  have hE : E b = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [decomp (p ^ L) hN b, map_sum]
    exact Finset.sum_eq_zero hpart
  exact sub_eq_zero.1 hE

end GlobalTheory.Glue.DPsi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripsExhaustParabolicUnipotentRadical
section
open Filter Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem strip_exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 →
    (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) →
    ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ r t ψ ϖ hψ _ hϖ _ y hy
  have hy' := (GlobalTheory.CuspEntries.mem_unipRad_two_stdSum rfl y).1 hy

  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  have hball : {z : k | valuation k z < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨1, one_ne_zero, fun _ hz => hz⟩
  have P := (triv_ev_props k)
  have hev : ∀ i j : Fin (r + t), ∀ᶠ m : ℕ in atTop,
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    intro i j
    by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [hij, and_self, if_true]
      have hsm : IsSmoothChar (ψ i / ψ j) := by
        have h1 := hψ i
        have h2 := hψ j
        unfold IsSmoothChar at *
        have : (ψ i).ker ⊓ (ψ j).ker ≤ (ψ i / ψ j).ker := by
          intro u hu
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hu
          rw [MonoidHom.mem_ker, MonoidHom.div_apply, hu.1, hu.2, div_one]
        exact Subgroup.isOpen_mono this (by rw [Subgroup.coe_inf]; exact h1.inter h2)
      have hopen := (P.2.2.2.2.2.1 _ hsm).1
      have hT : {z : k | Triv (ψ i / ψ j) z} ∈ 𝓝 (0 : k) := hopen.mem_nhds (P.2.2.1 _)
      have ht : Tendsto (fun m : ℕ => ϖ ^ m * y.val i j) atTop (𝓝 0) := by
        simpa using hpow.mul_const (y.val i j)
      filter_upwards [ht (inter_mem hball hT)] with m hm
      exact ⟨hm.1.le, hm.2⟩
    · simp only [hij, if_false]
      exact Eventually.of_forall fun _ => hy' i j hij
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin (r + t),
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    exact hev i
  obtain ⟨m, hm⟩ := hall.exists
  exact ⟨m, hm⟩

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombinationStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_basis_linear_combination : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (b b' : X.Fn l), b ∈ X.B N l w → b' ∈ X.B N l w → ∀ (c c' : ℤ_[l]) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l n b φ → IsThB X A N l n b' φ' →
    IsThB X A N l n (c • b + c' • b') (((c.appr n : ℕ) : Ω) • φ + ((c'.appr n : ℕ) : Ω) • φ') := by
  intro Ω _ _ _ ε X A N l _ n w b b' _ _ c c' φ φ' h h'
  obtain ⟨f, hfi, hfc, hfd, hfl⟩ := h
  obtain ⟨f', hfi', hfc', hfd', hfl'⟩ := h'
  refine ⟨f ^ (c.appr n) * f' ^ (c'.appr n), ?_, ?_, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact GlobalTheory.ThAdd.inv_mul (GlobalTheory.ThAdd.inv_pow hfi _) (GlobalTheory.ThAdd.inv_pow hfi' _)
  · rw [← GlobalTheory.ThAdd.cls_comb, ← hfc, ← hfc', ← map_smul, ← map_smul, ← map_add (f := _)]
    rfl
  · intro δ hδ hδ'
    obtain ⟨g, hgi, hg⟩ := hfd δ hδ hδ'
    obtain ⟨g', hgi', hg'⟩ := hfd' δ hδ hδ'
    refine ⟨g ^ (c.appr n) * g' ^ (c'.appr n), GlobalTheory.ThAdd.inv_mul (GlobalTheory.ThAdd.inv_pow hgi _) (GlobalTheory.ThAdd.inv_pow hgi' _), ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    calc (f : X.K) ^ (c.appr n) * (f' : X.K) ^ (c'.appr n) *
          (X.sl (ofSL δ) f ^ (c.appr n) * X.sl (ofSL δ) f' ^ (c'.appr n))
        = ((f : X.K) * X.sl (ofSL δ) f) ^ (c.appr n) * ((f' : X.K) * X.sl (ofSL δ) f') ^ (c'.appr n) := by ring
      _ = _ := by rw [hg, hg']; ring
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact GlobalTheory.ThAdd.isDl_mul (GlobalTheory.ThAdd.isDl_pow hfl _) (GlobalTheory.ThAdd.isDl_pow hfl' _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConst
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem theta_coeff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (theta s φ).coeff r = algebraMap ℚ Ω (s * r) * φ.coeff r := rfl

theorem theta_leibniz_add_const :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω),
      theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧
        ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  intro Ω _ _ s P Q
  refine ⟨?_, ?_, ?_⟩
  · ext r
    have h1 : (theta s P).support ⊆ P.support := fun t ht h => ht (by simp [theta_coeff, h])
    have h2 : (theta s Q).support ⊆ Q.support := fun t ht h => ht (by simp [theta_coeff, h])
    rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' P.isPWO_support h1,
      HahnSeries.coeff_mul_right' Q.isPWO_support h2, theta_coeff, HahnSeries.coeff_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have := (Finset.mem_addAntidiagonal.1 hij).2.2
    rw [← this, theta_coeff, theta_coeff, mul_add, map_add (f := _)]; ring
  · ext r; simp [theta_coeff, mul_add]
  · intro c; ext r
    rw [theta_coeff]
    by_cases h : r = 0
    · simp [h]
    · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

end GlobalTheory.Glue
end

