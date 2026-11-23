module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotXPowDvdAdjugateOfFirstOrderKernel
section
open Polynomial Matrix

namespace GlobalTheory
namespace CofactorOrder

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem exists_diag (M : Matrix n n K) :
    ∃ (P Q : Matrix n n K) (D : n → K), P.det = 1 ∧ Q.det = 1 ∧ P * M * Q = diagonal D := by
  obtain ⟨L, L', D, hL⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  have hdet : ∀ T : List (TransvectionStruct n K),
      (T.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro T
    induction T with
    | nil => simp
    | cons t T ih => rw [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det, one_mul]
  exact ⟨_, _, D, hdet L, hdet L', hL⟩

theorem mulVec_eq_zero_of_det {P : Matrix n n K} (hP : P.det = 1) {v : n → K}
    (h : P *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit P := (isUnit_iff_isUnit_det P).mpr (by rw [hP]; exact isUnit_one)
  exact (mulVec_injective_iff_isUnit.mpr hu) (by rw [h, mulVec_zero])

theorem ker_eq_bot_of_det {P : Matrix n n K} (hP : P.det = 1) :
    LinearMap.ker P.mulVecLin = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  rw [mulVecLin_apply] at hv
  exact mulVec_eq_zero_of_det hP hv

theorem card_le_finrank {M P Q : Matrix n n K} {D : n → K} [DecidablePred fun i => D i = 0]
    (hP : P.det = 1) (hQ : Q.det = 1) (h : P * M * Q = diagonal D) :
    Fintype.card {i // D i = 0} ≤ Module.finrank K (LinearMap.ker M.mulVecLin) := by
  set V := LinearMap.ker M.mulVecLin
  have hmem : ∀ i : {i // D i = 0}, Q *ᵥ Pi.single i.1 (1 : K) ∈ V := by
    intro i
    rw [LinearMap.mem_ker, mulVecLin_apply]
    apply mulVec_eq_zero_of_det hP
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]
    funext k
    rw [mulVec_diagonal]
    by_cases hk : k = i.1
    · subst hk; simp [i.2]
    · simp [hk]
  have hsingle : LinearIndependent K (fun i : {i // D i = 0} => (Pi.single i.1 (1 : K) : n → K)) := by
    have := (Pi.basisFun K n).linearIndependent.comp Subtype.val
      (Subtype.val_injective (p := fun i => D i = 0))
    simpa only [Function.comp_def, Pi.basisFun_apply] using this
  have hli : LinearIndependent K (fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) := by
    apply LinearIndependent.of_comp V.subtype
    have hmapped := hsingle.map' Q.mulVecLin (ker_eq_bot_of_det hQ)
    have e : (⇑V.subtype ∘ fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) =
        ⇑Q.mulVecLin ∘ fun i => (Pi.single i.1 (1 : K) : n → K) := by
      funext i
      simp
    rw [e]
    exact hmapped
  exact hli.fintype_card_le_finrank

theorem adjugate_ne_zero [Nonempty n] (M : Matrix n n K)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) ≤ 1) : M.adjugate ≠ 0 := by
  classical
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag M
  have hone := Fintype.card_le_one_iff.mp ((card_le_finrank hP hQ hPQ).trans h)
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, j ≠ i → D j ≠ 0 := by
    by_cases hex : ∃ i, D i = 0
    · obtain ⟨i, hi0⟩ := hex
      exact ⟨i, fun j hj hj0 => hj (congrArg Subtype.val (hone ⟨j, hj0⟩ ⟨i, hi0⟩))⟩
    · push Not at hex
      exact ⟨Classical.arbitrary n, fun j _ => hex j⟩
  intro hM
  have hdiag : (diagonal D).adjugate = 0 := by
    rw [← hPQ, adjugate_mul_distrib, adjugate_mul_distrib, hM, Matrix.zero_mul, Matrix.mul_zero]
  have hii := congrFun (congrFun hdiag i) i
  rw [adjugate_diagonal, diagonal_apply_eq, Matrix.zero_apply] at hii
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => hi j (Finset.ne_of_mem_erase hj)) hii

theorem exists_coeff_adjugate_ne_zero [Nonempty n] (Ψ : Matrix n n K[X])
    (h : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ 1) :
    ∃ b c, ¬ (X : K[X]) ∣ Ψ.adjugate b c := by
  have hmap : (Ψ.map fun p => p.coeff 0) = constantCoeff.mapMatrix Ψ := by
    ext i j
    simp [constantCoeff_apply]
  have hne := adjugate_ne_zero _ h
  rw [hmap, ← RingHom.map_adjugate] at hne
  by_contra hall
  push Not at hall
  apply hne
  ext b c
  rw [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply, constantCoeff_apply]
  exact X_dvd_iff.mp (hall b c)

theorem map_coeff_mul (P Q : Matrix n n K) (Ψ : Matrix n n K[X]) (k : ℕ) :
    ((P.map C * Ψ * Q.map C).map fun p => p.coeff k) = P * (Ψ.map fun p => p.coeff k) * Q := by
  ext i j
  simp only [map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Finset.sum_mul]

theorem diag_case [Nonempty n] (Θ : Matrix n n K[X]) (D : n → K)
    [DecidablePred fun i => D i = 0] (hD : (Θ.map fun p => p.coeff 0) = diagonal D)
    (H : ∀ x0 x1 : Fin (1 + 1) → n → K, (∀ j, (Θ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Θ.map fun p => p.coeff 1).mulVec (x0 j) + (Θ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0) :
    ∃ b c, ¬ (X : K[X]) ^ (Fintype.card {i // D i = 0} + 1) ∣ Θ.adjugate b c := by
  obtain ⟨s, hs⟩ : ∃ s : n → K[X], s = fun i => if D i = 0 then X else 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix n n K[X],
      T = Matrix.of fun i j => if D i = 0 then divX (Θ i j) else Θ i j := ⟨_, rfl⟩
  have h0 : ∀ i j, (Θ i j).coeff 0 = diagonal D i j := fun i j => by
    simpa using congrFun (congrFun hD i) j
  have hfac : Θ = diagonal s * T := by
    refine Matrix.ext fun i j => ?_
    rw [diagonal_mul, hs, hT, of_apply]
    by_cases hi : D i = 0
    · have hc : (Θ i j).coeff 0 = 0 := by
        rw [h0]
        by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [diagonal_apply_ne _ hij]
      have hX := X_mul_divX_add (Θ i j)
      rw [hc, C_0, add_zero] at hX
      simp only [hi, if_true]
      exact hX.symm
    · simp [hi]
  have hadj : ∀ b c, Θ.adjugate b c = T.adjugate b c * ∏ j ∈ Finset.univ.erase c, s j := by
    intro b c
    rw [hfac, adjugate_mul_distrib, adjugate_diagonal, mul_diagonal]
  have hprod : ∀ c, (∏ j ∈ Finset.univ.erase c, s j) ∣ X ^ Fintype.card {i // D i = 0} := by
    intro c
    have hall : ∏ j, s j = X ^ Fintype.card {i // D i = 0} := by
      simp [hs, Finset.prod_ite, Fintype.card_subtype]
    rw [← hall]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)
  have hrow : ∀ (v : n → K) (i : n), ((T.map fun p => p.coeff 0) *ᵥ v) i =
      if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i := by
    intro v i
    by_cases hi : D i = 0
    · simp [Matrix.mulVec, dotProduct, hT, hi, coeff_divX]
    · simp [Matrix.mulVec, dotProduct, hT, hi, h0, diagonal_apply]
  have hker : Module.finrank K (LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    set V := LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin
    have h2 : 1 + 1 ≤ Module.finrank K V := hlt
    have hinj : Function.Injective (Fin.castLE h2) := fun a b hab =>
      Fin.ext (by simpa using congrArg Fin.val hab)
    have hf := (Module.finBasis K V).linearIndependent.comp _ hinj
    have hli := hf.map' V.subtype (Submodule.ker_subtype V)
    refine H (fun j => (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j)
      (fun j i => if D i = 0 then 0 else
        -((Θ.map fun p => p.coeff 1) *ᵥ (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j) i / D i)
      ?_ hli
    intro j
    set v := (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j with hv
    have hvk : (T.map fun p => p.coeff 0) *ᵥ v = 0 := by
      have := (Module.finBasis K V (Fin.castLE h2 j)).2
      rw [LinearMap.mem_ker, mulVecLin_apply] at this
      exact this
    have hvi : ∀ i, (if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i) = 0 := by
      intro i
      rw [← hrow, hvk]
      rfl
    constructor
    · rw [hD]
      funext i
      rw [mulVec_diagonal]
      by_cases hi : D i = 0
      · simp [hi]
      · have := hvi i
        simp only [hi, if_false] at this
        simpa using this
    · rw [hD]
      funext i
      rw [Pi.add_apply, mulVec_diagonal]
      by_cases hi : D i = 0
      · have := hvi i
        simp only [hi, if_true] at this
        simp [hi, this]
      · simp only [hi, if_false]
        rw [Pi.zero_apply, ← mul_div_assoc, mul_div_cancel_left₀ _ hi, add_neg_cancel]
  obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero T hker
  refine ⟨b, c, fun hdvd => hbc ?_⟩
  rw [hadj] at hdvd
  obtain ⟨r, hr⟩ := hprod c
  have h3 := Dvd.dvd.mul_right hdvd r
  rw [mul_assoc, ← hr, pow_succ, mul_comm (X ^ _) X] at h3
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ X_ne_zero)).mp h3

end CofactorOrder


open CofactorOrder in
theorem exists_not_X_pow_dvd_adjugate_of_firstOrderKernel (K : Type) [Field K] (a m : ℕ)
    (Ψ : Matrix (Fin a) (Fin a) (Polynomial K))
    (H : ∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0)
    (hν : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1)
    (ha : a ≠ 0) :
    ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  classical
  have : Nonempty (Fin a) := ⟨⟨0, Nat.pos_of_ne_zero ha⟩⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero Ψ (by simpa using hν)
    exact ⟨b, c, by simpa using hbc⟩
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag (Ψ.map fun p => p.coeff 0)
  have hΘ0 : ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0) = diagonal D := by
    rw [map_coeff_mul]; exact hPQ
  have hz := card_le_finrank hP hQ hPQ
  have HΘ : ∀ x0 x1 : Fin (1 + 1) → Fin a → K,
      (∀ j, ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
        ((P.map C * Ψ * Q.map C).map fun p => p.coeff 1).mulVec (x0 j) +
          ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0 := by
    intro x0 x1 hx hli
    refine H (fun j => Q *ᵥ x0 j) (fun j => Q *ᵥ x1 j) (fun j => ?_)
      (hli.map' Q.mulVecLin (ker_eq_bot_of_det hQ))
    obtain ⟨h0, h1⟩ := hx j
    rw [map_coeff_mul] at h0 h1
    rw [map_coeff_mul] at h1
    constructor
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc] using h0
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc] using h1
  obtain ⟨b, c, hbc⟩ := diag_case _ D hΘ0 HΘ
  by_contra hcon
  push Not at hcon
  apply hbc
  have hle : Fintype.card {i // D i = 0} + 1 ≤ 2 * m + 1 := by omega
  refine (pow_dvd_pow X hle).trans ?_
  rw [adjugate_mul_distrib, adjugate_mul_distrib, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => Dvd.dvd.mul_right
    (Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hcon k l) _) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPartitionOneIntegralAtPlaces
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_partition_one_integral_at_places (L : Type) [Field L] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : S.Nonempty) (Y : S → Finset L)
    (hY : ∀ la, ∀ y ∈ Y la, la.1.valuation L y ≤ 1) :
    ∃ e : S → L, ∑ la, e la = 1 ∧
      ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, la'.valuation L (e la * y) ≤ 1 := by
  classical
  have hb : ∀ (_la : S) (y : L) (la' : HeightOneSpectrum (𝓞 L)),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) * la'.valuation L y ≤ 1 := by
    intro _ y la'
    by_cases hy : la'.valuation L y = 0
    · exact ⟨0, by simp [hy]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = la'.valuation L y := ⟨_, WithZero.exp_log hy⟩
      refine ⟨m.toNat, ?_⟩
      rw [← hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  choose n hn using hb
  let N : ℕ := ∑ la : S, ∑ y ∈ Y la, ∑ la' ∈ S, n la y la'
  have hN : ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, n la y la' ≤ N := by
    intro la y hy la' hla'
    calc n la y la' ≤ ∑ la'' ∈ S, n la y la'' :=
          Finset.single_le_sum (f := fun la'' => n la y la'') (fun _ _ => Nat.zero_le _) hla'
      _ ≤ ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'' :=
          Finset.single_le_sum (f := fun y' => ∑ la'' ∈ S, n la y' la'') (fun _ _ => Nat.zero_le _) hy
      _ ≤ N := Finset.single_le_sum (f := fun la => ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ la)
  let J : S → Ideal (𝓞 L) := fun la => ∏ la' ∈ S.erase la.1, la'.asIdeal ^ N
  have htop : ⨆ la ∈ (Finset.univ : Finset S), J la = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hJM : ∀ la : S, J la ≤ M := fun la =>
      le_trans (le_iSup₂_of_le (f := fun la (_ : la ∈ (Finset.univ : Finset S)) => J la)
        la (Finset.mem_univ _) le_rfl) hle
    obtain ⟨la0, hla0⟩ := hS
    obtain ⟨la1, hla1, h1⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la0, hla0⟩)
    have hle1 : la1.asIdeal ≤ M := hM.isPrime.le_of_pow_le h1
    have heq : la1.asIdeal = M := la1.isMaximal.eq_of_le hM.ne_top hle1
    have hla1S : la1 ∈ S := Finset.mem_of_mem_erase hla1
    obtain ⟨la2, hla2, h2⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la1, hla1S⟩)
    have hle2 : la2.asIdeal ≤ la1.asIdeal := heq ▸ hM.isPrime.le_of_pow_le h2
    have h22 : la2.asIdeal = la1.asIdeal := la2.isMaximal.eq_of_le la1.isPrime.ne_top hle2
    exact (Finset.ne_of_mem_erase hla2) (HeightOneSpectrum.ext h22)
  have h1 : (1 : 𝓞 L) ∈ ⨆ la ∈ (Finset.univ : Finset S), J la := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 h1
  refine ⟨fun la => ((μ la : 𝓞 L) : L), ?_, ?_⟩
  · have := congrArg (fun x : 𝓞 L => (x : L)) hμ
    simpa using this
  · intro la y hy la' hla'
    rw [map_mul]
    by_cases h : la' = la.1
    · subst h
      calc la.1.valuation L ((μ la : 𝓞 L) : L) * la.1.valuation L y ≤ 1 * 1 :=
            mul_le_mul' (HeightOneSpectrum.valuation_le_one _ _) (hY la y hy)
        _ = 1 := one_mul 1
    · have hmem : (μ la : 𝓞 L) ∈ la'.asIdeal ^ N := by
        have hm : (μ la : 𝓞 L) ∈ J la := (μ la).2
        have hs : la' ∈ S.erase la.1 := Finset.mem_erase.2 ⟨h, hla'⟩
        have : J la ≤ la'.asIdeal ^ N := by
          show ∏ la'' ∈ S.erase la.1, la''.asIdeal ^ N ≤ _
          rw [← Finset.mul_prod_erase _ _ hs]
          exact le_trans Ideal.mul_le_inf inf_le_left
        exact this hm
      have hv : la'.valuation L ((μ la : 𝓞 L) : L) ≤ WithZero.exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          Ideal.dvd_span_singleton]
        exact hmem
      calc la'.valuation L ((μ la : 𝓞 L) : L) * la'.valuation L y
          ≤ WithZero.exp (-(N : ℤ)) * la'.valuation L y := mul_le_mul' hv le_rfl
        _ ≤ WithZero.exp (-(n la y la' : ℤ)) * la'.valuation L y := by
            refine mul_le_mul' ?_ le_rfl
            rw [WithZero.exp_le_exp]
            have := hN la y hy la' hla'
            omega
        _ ≤ 1 := hn la y la'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlaceOfEmbedding
section
namespace GlobalTheory.IntegralNormSmallIdeal

open NumberField

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (y : PadicAlgCl l)
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (PadicAlgCl l) NNReal)
  have h2 : IsIntegral (Valued.v : Valuation (PadicAlgCl l) NNReal).integer y :=
    IsIntegral.tower_top hy
  have h3 := hv.isIntegral_iff_v_le_one.mp h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

theorem norm_natCast_prime {l : ℕ} [Fact (Nat.Prime l)] :
    ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h0 := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h0
  rw [h0]
  exact Padic.norm_p_lt_one

theorem norm_map_le_one {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  apply norm_le_one_of_isIntegral
  have h0 := (NumberField.RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  simpa using h0

def smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := map_add (algebraMap (𝓞 E) E) a b
    rw [this, map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have : ((0 : 𝓞 E) : E) = 0 := map_zero (algebraMap (𝓞 E) E)
    rw [this, map_zero, norm_zero]
    exact zero_lt_one
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
    have : ((r * x : 𝓞 E) : E) = (r : E) * (x : E) := map_mul (algebraMap (𝓞 E) E) r x
    rw [this, map_mul, norm_mul]
    calc ‖c (r : E)‖ * ‖c (x : E)‖ ≤ 1 * ‖c (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one c r) (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

theorem mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ smallIdeal c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : (smallIdeal c).IsPrime := by
  refine Ideal.isPrime_iff.2 ⟨?_, fun {x y} hxy => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · rw [mem_smallIdeal, mem_smallIdeal]
    rw [mem_smallIdeal] at hxy
    by_contra hcon
    push_neg at hcon
    have h1 := norm_map_le_one c x
    have h2 := norm_map_le_one c y
    have e : ((x * y : 𝓞 E) : E) = (x : E) * (y : E) := map_mul (algebraMap (𝓞 E) E) x y
    rw [e, map_mul, norm_mul] at hxy
    nlinarith [hcon.1, hcon.2]

theorem natCast_mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ smallIdeal c := by
  rw [mem_smallIdeal]
  have e : (((l : ℕ) : 𝓞 E) : E) = ((l : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) l
  rw [e, map_natCast]
  exact norm_natCast_prime

theorem exists_place_of_embedding {l : ℕ} [inst : Fact (Nat.Prime l)] {E : Type} [inst_1 : Field E]
    [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)),
      (↑l : NumberField.RingOfIntegers E) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ∧
      ∀ (x : NumberField.RingOfIntegers E), x ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ↔
        ‖(c : E → PadicAlgCl l) (↑x : E)‖ < (1 : ℝ) := by
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers E) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨⟨smallIdeal c, smallIdeal_isPrime c, fun h => hl0 ?_⟩, natCast_mem_smallIdeal c, fun x => mem_smallIdeal c x⟩
  have h0 := natCast_mem_smallIdeal (E := E) c
  rw [h] at h0
  exact (Submodule.mem_bot _).1 h0

end GlobalTheory.IntegralNormSmallIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowCardEq
section
namespace GlobalTheory.CardinalPower

open IntermediateField

theorem exists_pow_card_eq {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, (σ : L → L) x = x ^ Fintype.card K ^ i := by
  classical
  let M : IntermediateField K L := adjoin K (X : Set L)
  haveI : FiniteDimensional K M :=
    finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : Finite M := Module.finite_of_finite K
  haveI : Normal K M := inferInstance
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2 (σ.restrictNormal M)
  refine ⟨n.1, fun x hx => ?_⟩
  have hxM : x ∈ M := subset_adjoin K _ hx
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, hxM⟩
  rw [← hn] at h1
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate] at h1
  simpa using h1.symm

end GlobalTheory.CardinalPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuadraticCharOfSplitTwoGroup
section
open scoped commutatorElement Pointwise

namespace GlobalTheory

theorem normal_of_commutator_le {G : Type} [Group G] (M : Subgroup G)
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ M) : M.Normal := by
  constructor
  intro n hn g
  have h1 : ⁅g, n⁆ ∈ M :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have h2 := M.mul_mem h1 hn
  simpa [commutatorElement_def] using h2

end GlobalTheory

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapContinuousOfCompactSpaceOfFinite
section
namespace GlobalTheory

theorem linearMap_continuous_of_compactSpace_of_finite
    {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type}
    [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') : Continuous f := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O M
  have hgc : Continuous g := g.continuous_on_pi
  have hq : Topology.IsQuotientMap g := hgc.isClosedMap.isQuotientMap hgc hg
  have hfg : Continuous (f ∘ g) := (f.comp g).continuous_on_pi
  exact hq.continuous_iff.mpr hfg

end GlobalTheory
end

