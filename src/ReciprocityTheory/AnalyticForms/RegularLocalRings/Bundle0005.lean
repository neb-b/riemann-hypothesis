module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChartA
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {n : ℕ}

def dualEv (p v : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] DualNumber ℂ :=
  aeval fun j => (TrivSqZeroExt.inl (p j) + v j • DualNumber.eps : DualNumber ℂ)

theorem dualEv_fst_snd (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h ∧
      (dualEv p v h).snd = ∑ j, eval p (pderiv j h) * v j := by
  induction h using MvPolynomial.induction_on
  next a =>
    simp [dualEv, TrivSqZeroExt.algebraMap_eq_inl]
  next q r hq hr =>
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h3, h4⟩ := hr
    refine ⟨?_, ?_⟩
    · rw [map_add (f := _), TrivSqZeroExt.fst_add, h1, h3, map_add (f := _)]
    · rw [map_add (f := _), TrivSqZeroExt.snd_add, h2, h4, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add (f := _), map_add (f := _), add_mul]
  next q i hq =>
    obtain ⟨h1, h2⟩ := hq
    have hX : dualEv p v (X i) = TrivSqZeroExt.inl (p i) + v i • DualNumber.eps := by
      simp [dualEv]
    refine ⟨?_, ?_⟩
    · rw [map_mul, TrivSqZeroExt.fst_mul, h1, hX]
      simp
    · rw [map_mul, TrivSqZeroExt.snd_mul, h1, h2, hX]
      simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum,
        DualNumber.snd_eps, DualNumber.fst_eps]
      have e1 : (∑ x, (eval p) (if i = x then q else 0) * v x) = eval p q * v i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      rw [e1, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring

theorem dualEv_fst (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h := (dualEv_fst_snd p v h).1

theorem dualEv_snd (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).snd = ∑ j, eval p (pderiv j h) * v j := (dualEv_fst_snd p v h).2

theorem eval_eq_zero_of_isLocalRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] : ∀ k ∈ K, eval p k = 0 := by
  intro k hk
  by_contra hne
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) k) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) k).2 (fun h => hne (RingHom.mem_ker.1 h))
  have htop : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hk) hu
  have hs : Subsingleton (locRing K p) := Ideal.Quotient.subsingleton_iff.2 htop
  exact not_subsingleton (locRing K p) hs

theorem exists_dualEv_lift (K : Ideal (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ)
    (hK : ∀ k ∈ K, dualEv p v k = 0) :
    ∃ χ : locRing K p →+* DualNumber ℂ,
      ∀ x, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = dualEv p v x := by
  have hunit : ∀ y : (ptIdeal p).primeCompl, IsUnit ((dualEv p v).toRingHom (y : MvPolynomial (Fin n) ℂ)) := by
    intro y
    refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
    have hy : eval p (y : MvPolynomial (Fin n) ℂ) ≠ 0 := fun h => y.2 (RingHom.mem_ker.2 h)
    have := dualEv_fst p v (y : MvPolynomial (Fin n) ℂ)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
    exact hy.isUnit
  let g : locPt p →+* DualNumber ℂ := IsLocalization.lift (M := (ptIdeal p).primeCompl) hunit
  have hg : ∀ x, g (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) x) = dualEv p v x := fun x =>
    IsLocalization.lift_eq hunit x
  have hK' : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro k hk
    rw [Ideal.mem_comap, RingHom.mem_ker, hg]
    exact hK k hk
  refine ⟨Ideal.Quotient.lift _ g (fun a ha => RingHom.mem_ker.1 (hK' ha)), fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) (locPt p) (locRing K p),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk, hg]

theorem map_ptIdeal_eq_zero (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    (χ : locRing K p →+* DualNumber ℂ)
    (hχ : ∀ i, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) = 0) :
    ∀ x ∈ ptIdeal p, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = 0 := by
  intro x hx
  have h1 : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x ∈
      Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) := by
    rw [hr]
    exact Ideal.mem_map_of_mem _ hx
  have h2 : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) ≤
      RingHom.ker χ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hχ i
  exact h2 h1

theorem eq_zero_of_grad (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    [IsLocalRing (locRing K p)] (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hFK : ∀ i, F i ∈ K)
    (hh : MvPolynomial (Fin n) ℂ) (hhp : eval p hh ≠ 0)
    (hcut : ∀ g ∈ K, hh * g ∈ Ideal.span (Set.range F)) (v : Fin n → ℂ)
    (hvr : ∀ i, ∑ j, eval p (pderiv j (r i)) * v j = 0)
    (hvF : ∀ k, ∑ j, eval p (pderiv j (F k)) * v j = 0) : v = 0 := by
  have heval := eval_eq_zero_of_isLocalRing K p
  have hF : ∀ k, dualEv p v (F k) = 0 := fun k => TrivSqZeroExt.ext
    (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval _ (hFK k))
    (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvF k)
  have hspanF : Ideal.span (Set.range F) ≤ RingHom.ker (dualEv p v).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hF k
  have hK : ∀ g ∈ K, dualEv p v g = 0 := by
    intro g hg
    have h1 : dualEv p v (hh * g) = 0 := hspanF (hcut g hg)
    rw [map_mul] at h1
    have hu : IsUnit (dualEv p v hh) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [dualEv_fst]; exact hhp.isUnit)
    exact hu.mul_right_eq_zero.1 h1
  obtain ⟨χ, hχ⟩ := exists_dualEv_lift K p v hK
  obtain ⟨χ0, hχ0⟩ := exists_dualEv_lift K p 0 (fun k hk => TrivSqZeroExt.ext
    (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval k hk)
    (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp))
  have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) ≤ RingHom.ker χ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hχ0]
    exact TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact RingHom.mem_ker.1 hx)
      (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp)
  have hr0 : ∀ i, eval p (r i) = 0 := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) := by
      rw [← hr]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h1 := RingHom.mem_ker.1 (hle hmem)
    rw [hχ0] at h1
    have h2 := congrArg TrivSqZeroExt.fst h1
    rwa [dualEv_fst, TrivSqZeroExt.fst_zero] at h2
  have hall := map_ptIdeal_eq_zero K p r hr χ (fun i => by
    rw [hχ]
    exact TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact hr0 i)
      (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvr i))
  funext j
  have hx : (X j - C (p j) : MvPolynomial (Fin n) ℂ) ∈ ptIdeal p := RingHom.mem_ker.2 (by simp)
  have h1 := hall _ hx
  rw [hχ] at h1
  have h2 := congrArg TrivSqZeroExt.snd h1
  rw [dualEv_snd, TrivSqZeroExt.snd_zero] at h2
  simpa [pderiv_X, Pi.single_apply] using h2

theorem analyticOnNhd_eval_univ (q : MvPolynomial (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun y : Fin n → ℂ => eval y q) Set.univ := by
  exact AnalyticOnNhd.eval_mvPolynomial q

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭

theorem comap_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  let _ : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := MvPolynomial.algebraMvPolynomial
  have hflat : Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
    BaseChangeC.flat_mvPolynomial_rat_complex
  have hQp : Q.IsPrime := hQ.1.1
  have hle : 𝔭 ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hPp : (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have hlo : Q.LiesOver (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))) := ⟨rfl⟩
  obtain ⟨Q', hQ'le, hQ'p, hQ'lo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hle
  have hQ'over : Q'.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := hQ'lo.over.symm
  have hmapQ' : extC 𝔭 ≤ Q' := by
    unfold extC
    rw [Ideal.map_le_iff_le_comap, hQ'over]
  have hEq : Q = Q' := le_antisymm (hQ.2 ⟨hQ'p, hmapQ'⟩ hQ'le) hQ'le
  subst hEq
  exact hQ'over

theorem ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatB
section
namespace ReciprocityTheory.AnForm.R.IntegerToRational

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def eQ (x : PrimeSpectrum (MvPolynomial σ ℤ)) (h : ChZero x.asIdeal) :
    PrimeSpectrum (MvPolynomial σ ℚ) :=
  ⟨Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal, map_isPrime x.asIdeal h⟩

lemma eQ_lt {x y : PrimeSpectrum (MvPolynomial σ ℤ)} (hx : ChZero x.asIdeal)
    (hy : ChZero y.asIdeal) (hxy : x < y) : eQ x hx < eQ y hy := by
  have hle : (eQ x hx).asIdeal ≤ (eQ y hy).asIdeal := by
    show Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal ≤
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal
    exact Ideal.map_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)
  show (eQ x hx).asIdeal < (eQ y hy).asIdeal
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h2 : (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) =
      (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) := congrArg (Ideal.comap _) heq
  rw [comap_map_eq x.asIdeal hx, comap_map_eq y.asIdeal hy] at h2
  exact (show x.asIdeal ≠ y.asIdeal from ne_of_lt hxy) h2

lemma length_le_coheight_eQ (s : LTSeries (PrimeSpectrum (MvPolynomial σ ℤ))) :
    ∀ z, s.head = z → ∀ h0 : ChZero z.asIdeal,
      (s.length : ℕ∞) ≤ Order.coheight (eQ z h0) + 1 := by
  induction s using RelSeries.inductionOn with
  | singleton x => intros; simp
  | cons t x hx ih =>
    intro z hz h0
    rw [RelSeries.head_cons] at hz
    subst hz
    simp only [RelSeries.cons_length, Nat.cast_add, Nat.cast_one]
    by_cases h1 : ChZero t.head.asIdeal
    · have h2 := ih t.head rfl h1
      have h3 := Order.coheight_add_one_le (eQ_lt h0 h1 hx)
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight (eQ t.head h1) + 1 + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h3 1
    · have h2 : (t.length : ℕ∞) ≤ Order.coheight t.head := Order.length_le_coheight_head
      have h3 := dim_le_of_charP x.asIdeal t.head.asIdeal hx.le h0 h1
      rw [ringKrullDim_quotient_eq_coheight,
        ringKrullDim_quotient_eq_coheight (hI := map_isPrime _ h0)] at h3
      have h4 : Order.coheight t.head ≤ Order.coheight (eQ x h0) := WithBot.coe_le_coe.mp h3
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight t.head + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h4 1

private lemma isJacobsonRing_int_regular_local_rings : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ Ideal.le_jacobson
  by_cases hb : P = ⊥
  · subst hb
    intro m hm
    rw [Ideal.mem_jacobson_bot] at hm
    rw [Ideal.mem_bot]
    have h1 := Int.isUnit_iff.mp (hm 1)
    have h2 := Int.isUnit_iff.mp (hm 2)
    omega
  · have hmax : P.IsMaximal := by
      first
        | exact Ideal.IsPrime.isMaximal hP hb
        | exact hP.isMaximal hb
        | exact Ideal.IsPrime.to_maximal_ideal hb
        | exact Ring.DimensionLEOne.maximalOfPrime hb hP
    exact sInf_le ⟨le_rfl, hmax⟩

private lemma not_isMaximal_of_chZero (Q : Ideal (MvPolynomial σ ℤ)) (hQ : ChZero Q) :
    ¬ Q.IsMaximal := by
  intro hmax
  haveI := hmax
  haveI := isJacobsonRing_int_regular_local_rings
  letI : Field (MvPolynomial σ ℤ ⧸ Q) := Ideal.Quotient.field Q
  have hint := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
    (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have hfe : (Ideal.Quotient.mk Q).comp (MvPolynomial.C) =
      algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q) := RingHom.ext_int _ _
  haveI : Algebra.IsIntegral ℤ (MvPolynomial σ ℤ ⧸ Q) := by
    constructor
    intro x
    have hx := hint x
    rw [hfe] at hx
    exact hx
  have hinj : Function.Injective (algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    rw [← hfe, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hm
    exact hQ m hm
  have hF : IsField ℤ := isField_of_isIntegral_of_isField hinj
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hmax)
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
  omega

lemma coheight_eQ_add_one_le (P : PrimeSpectrum (MvPolynomial σ ℤ)) (hP : ChZero P.asIdeal) :
    Order.coheight (eQ P hP) + 1 ≤ Order.coheight P := by
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let g : PrimeSpectrum (MvPolynomial σ ℚ) → PrimeSpectrum (MvPolynomial σ ℤ) :=
    fun Q => ⟨Q.asIdeal.comap φ, inferInstance⟩
  have hg : StrictMono g := by
    intro a b hab
    show a.asIdeal.comap φ < b.asIdeal.comap φ
    exact comap_strictMono (show a.asIdeal < b.asIdeal from hab)
  have hg0 : g (eQ P hP) = P := PrimeSpectrum.ext (comap_map_eq P.asIdeal hP)
  have hup : ∀ L : PrimeSpectrum (MvPolynomial σ ℚ), ∃ M, g L < M := by
    intro L
    have hQ : ChZero (g L).asIdeal := chZero_comap L.asIdeal
    have hnm := not_isMaximal_of_chZero (g L).asIdeal hQ
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (g L).asIdeal (g L).isPrime.ne_top
    refine ⟨⟨M, hM.isPrime⟩, ?_⟩
    show (g L).asIdeal < M
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnm
    rw [heq]
    exact hM
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.coheight (eQ P hP) →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.coheight P := by
    intro n hn
    obtain ⟨p, hph, hpl⟩ := Order.exists_series_of_le_coheight (eQ P hP) hn
    obtain ⟨M, hM⟩ := hup p.last
    have hlast : (p.map g hg).last < M := hM
    let q := (p.map g hg).snoc M hlast
    have hqh : q.head = P := by
      rw [RelSeries.head_snoc]
      show g p.head = P
      rw [hph]
      exact hg0
    have hql : q.length = n + 1 := by
      rw [← hpl]
      rfl
    rw [← hql, ← hqh]
    exact Order.length_le_coheight_head
  rcases eq_or_ne (Order.coheight (eQ P hP)) ⊤ with h | h
  · have htop : Order.coheight P = ⊤ := by
      by_contra hne
      have h1 := key (Order.coheight P).toNat (by rw [h]; exact le_top)
      have h2 : (((Order.coheight P).toNat + 1 : ℕ) : ℕ∞) ≤ ((Order.coheight P).toNat : ℕ∞) := by
        rw [ENat.coe_toNat hne]
        exact h1
      have h3 := (Nat.cast_le (α := ℕ∞)).mp h2
      omega
    rw [htop]
    exact le_top
  · have h1 := key (Order.coheight (eQ P hP)).toNat (by rw [ENat.coe_toNat h])
    rw [← ENat.coe_toNat h]
    exact_mod_cast h1

end ReciprocityTheory.AnForm.R.IntegerToRational
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA
section
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section

variable {n : ℕ}

def ptQ (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ ⧸ K) :=
  (ptIdeal p).map (Ideal.Quotient.mk K)

theorem mk_mem_ptQ {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p)
    (f : MvPolynomial (Fin n) ℂ) : Ideal.Quotient.mk K f ∈ ptQ K p ↔ f ∈ ptIdeal p := by
  exact Ideal.mem_quotient_iff_mem hK

theorem ptQ_isPrime {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p) :
    (ptQ K p).IsPrime := by
  haveI : (ptIdeal p).IsPrime := RingHom.ker_isPrime _
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hK)

theorem algebraMap_quot_mk (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ ⧸ K) (locRing K p) (Ideal.Quotient.mk K f) =
      algebraMap _ (locRing K p) f := by
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem isLocalization_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) :
    letI := ptQ_isPrime hK; IsLocalization.AtPrime (locRing K p) (ptQ K p) := by
  letI := ptQ_isPrime hK
  have hM : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ K) (ptIdeal p).primeCompl =
      (ptQ K p).primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [Ideal.mem_primeCompl_iff, Ideal.Quotient.algebraMap_eq, mk_mem_ptQ hK]
      exact hf
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.mem_primeCompl_iff, mk_mem_ptQ hK] at hx
      exact ⟨f, hx, rfl⟩
  have h := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (ptIdeal p).primeCompl (locPt p) K
  rw [hM] at h
  exact h

theorem isLocalRing_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) : IsLocalRing (locRing K p) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  exact IsLocalization.AtPrime.isLocalRing (locRing K p) (ptQ K p)

theorem maximalIdeal_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) [IsLocalRing (locRing K p)] :
    IsLocalRing.maximalIdeal (locRing K p) = (ptIdeal p).map (algebraMap _ (locRing K p)) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (ptQ K p) (locRing K p), ptQ, Ideal.map_map]
  congr 1

theorem le_ptIdeal_iff' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    K ≤ ptIdeal p ↔ ∀ h ∈ K, eval p h = 0 := by
  simp [ptIdeal, SetLike.le_def, RingHom.mem_ker]

end
end ReciprocityTheory.AnForm.R
end

