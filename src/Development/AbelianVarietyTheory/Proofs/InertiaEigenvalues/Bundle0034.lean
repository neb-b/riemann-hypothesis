module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqZeroOfSubalgebra
section
namespace GlobalTheory.SubalgebraMulVecZero

theorem mulVec_frac_eq_zero {B : Type} [CommRing B] [IsDomain B] {ι κ : Type} [Fintype ι]
    (A : Matrix κ ι B) (hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0)
    (v : ι → FractionRing B)
    (hv : (A.map (algebraMap B (FractionRing B))).mulVec v = 0) : v = 0 := by
  classical
  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) Finset.univ v
  choose u hu using fun i => hb i (Finset.mem_univ i)
  have hAu : A.mulVec u = 0 := by
    funext k
    apply IsFractionRing.injective B (FractionRing B)
    rw [Pi.zero_apply, map_zero]
    have e : algebraMap B (FractionRing B) (A.mulVec u k) =
        (A.map (algebraMap B (FractionRing B))).mulVec (fun i => algebraMap B (FractionRing B) (u i)) k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]
    have e2 : (fun i => algebraMap B (FractionRing B) (u i)) = b • v := funext hu
    rw [e2, Matrix.mulVec_smul, hv, smul_zero]
    rfl
  have hu0 := hA u hAu
  funext i
  have h1 := hu i
  rw [hu0, Pi.zero_apply, map_zero] at h1
  have hb0 : algebraMap B (FractionRing B) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  rw [Algebra.smul_def] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hb0

theorem exists_left_inv {K : Type} [Field K] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι K) (hA : ∀ v : ι → K, A.mulVec v = 0 → v = 0) :
    ∃ N : Matrix ι κ K, N * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hA v hv)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' A) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S]
    [Algebra O S] (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix κ ι S) (hM : ∀ (i : κ) (j : ι), M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → Matrix.mulVec M v = 0 → v = 0)
    (w : ι → S) (hw : Matrix.mulVec M w = 0) : w = 0 := by
  let A : Matrix κ ι B := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let c : B →+* S := B.val.toRingHom
  have hc : Function.Injective c := Subtype.val_injective
  have hAM : A.map c = M := by
    ext i j
    rfl
  have hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0 := by
    intro u hu
    have h1 : M.mulVec (c ∘ u) = 0 := by
      funext i
      rw [← hAM, ← RingHom.map_mulVec, hu]
      simp
    have h2 := hinj (c ∘ u) (fun j => (u j).2) h1
    funext j
    apply hc
    have := congrFun h2 j
    simpa using this
  obtain ⟨N, hN⟩ := exists_left_inv (A.map (algebraMap B (FractionRing B)))
    (mulVec_frac_eq_zero A hA)
  have hL := IsFractionRing.injective S (FractionRing S)
  let g : B →+* FractionRing S := (algebraMap S (FractionRing S)).comp c
  have hg : Function.Injective g := hL.comp hc
  let φ : FractionRing B →+* FractionRing S := IsFractionRing.lift hg
  have hmap : (A.map (algebraMap B (FractionRing B))).map φ
      = M.map (algebraMap S (FractionRing S)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact IsFractionRing.lift_algebraMap hg (A i j)
  have hN' : N.map φ * M.map (algebraMap S (FractionRing S)) = 1 := by
    rw [← hmap, ← Matrix.map_mul, hN]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hw' : (M.map (algebraMap S (FractionRing S))).mulVec
      ((algebraMap S (FractionRing S)) ∘ w) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hw]
    simp
  have h0 : (algebraMap S (FractionRing S)) ∘ w = 0 := by
    rw [← Matrix.one_mulVec ((algebraMap S (FractionRing S)) ∘ w), ← hN',
      ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  funext j
  apply hL
  have := congrFun h0 j
  simpa using this

end GlobalTheory.SubalgebraMulVecZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfProdAddEq
section
namespace GlobalTheory.MultisetOfProduct

open Polynomial

theorem eval_prod_neg (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
  simp [sub_neg_eq_add]

theorem multiset_eq_of_prod_add_eq {m m' : Multiset ℂ}
    (h : ∀ (u : ℂ), Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m)
      = Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m')) : m = m' := by

  have hp : ((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod =
      ((m'.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_neg, eval_prod_neg]
    exact h u
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

end GlobalTheory.MultisetOfProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetManySeparatedPoints
section
open Polynomial
open Classical

namespace GlobalTheory

theorem multiset_many_separated_points : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro K _ s ρ A B hρ hB hAB hball
  set S := s.toFinset.powerset.filter
    (fun Z : Finset K => ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨Z, hZS, hZmax⟩ := Finset.exists_max_image S Finset.card hne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hZS
  obtain ⟨hZsub, hZsep⟩ := hZS
  have hZs : ∀ W ∈ Z, W ∈ s := fun W hW => Multiset.mem_toFinset.mp (hZsub hW)
  have hcov : ∀ z ∈ s, ∃ W ∈ Z, ‖z - W‖ ≤ ρ := by
    intro z hz
    by_contra h
    push_neg at h
    have hzZ : z ∉ Z := by
      intro hzZ
      have := h z hzZ
      simp at this
      linarith
    have hmem : insert z Z ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (Multiset.mem_toFinset.mpr hz) hZsub, ?_⟩
      intro W hW W' hW' hne
      rw [Finset.mem_insert] at hW hW'
      rcases hW with rfl | hW <;> rcases hW' with rfl | hW'
      · exact absurd rfl hne
      · exact h W' hW'
      · rw [norm_sub_rev]; exact h W hW
      · exact hZsep W hW W' hW' hne
    have := hZmax _ hmem
    rw [Finset.card_insert_of_notMem hzZ] at this
    omega
  have hle : s ≤ ∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ) := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum']
    by_cases ha : a ∈ s
    · obtain ⟨W, hW, hd⟩ := hcov a ha
      calc Multiset.count a s = Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
            rw [Multiset.count_filter_of_pos (p := fun z => ‖z - W‖ ≤ ρ) hd]
        _ ≤ _ := Finset.single_le_sum
            (f := fun W => Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)))
            (fun _ _ => Nat.zero_le _) hW
    · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
  have hcard : Multiset.card s ≤ Z.card * B := by
    calc Multiset.card s ≤ Multiset.card (∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ)) :=
          Multiset.card_le_card hle
      _ = ∑ W ∈ Z, Multiset.card (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum]
      _ ≤ ∑ W ∈ Z, B := Finset.sum_le_sum fun W hW => hball W (hZs W hW)
      _ = Z.card * B := by simp
  exact ⟨Z, Nat.le_of_mul_le_mul_right (hAB.trans hcard) hB, hZs, hZsep⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDiffer
section
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory

theorem natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal :
    ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal →
      ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) →
      ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) →
        la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  intro l c K L _ _ _ _ _ la hl hD y hy
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d₀ ∈ differentIdeal (𝓞 K) (𝓞 L), d₀ ∉ la.asIdeal ^ (c + 1) := by
    by_contra h
    push_neg at h
    exact hD (Ideal.dvd_iff_le.mpr h)
  have h1 : la.intValuation ((l : 𝓞 L) ^ c) ≤ WithZero.exp (-(c : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ c).mpr (Ideal.pow_mem_pow hl c)
  have h2 : WithZero.exp (-(c : ℤ)) ≤ la.intValuation d₀ := by
    rw [HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity_le]
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem la,
      HeightOneSpectrum.intValuation_le_exp_iff_le_emultiplicity, not_le] at hd₀
    rw [← ENat.lt_natCast_add_one_iff]
    exact_mod_cast hd₀
  have hyd := hy d₀ hd₀D
  have e1 : la.valuation L (d₀ : L) = la.intValuation d₀ := la.valuation_of_algebraMap (K := L) d₀
  have e2 : la.valuation L ((l : L) ^ c) = la.intValuation ((l : 𝓞 L) ^ c) := by
    rw [← la.valuation_of_algebraMap (K := L)]
    simp
  rw [Valuation.map_mul] at hyd ⊢
  calc la.valuation L ((l : L) ^ c) * la.valuation L y
      ≤ la.valuation L (d₀ : L) * la.valuation L y := by
        gcongr
        rw [e1, e2]
        exact h1.trans h2
    _ = la.valuation L y * la.valuation L (d₀ : L) := mul_comm _ _
    _ ≤ 1 := hyd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeLeAndCoeffProdPow
section
universe u_1 u_2

namespace GlobalTheory.ProductDegreeCoefficient

open Polynomial

theorem natDegree_le_and_coeff_prod_pow {B : Type u_1} [CommRing B] {T : Type u_2}
    (s : Finset T) (p : T → Polynomial B) (e : T → ℕ)
    (h : ∀ t : T, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a ^ e a).natDegree ≤ e a := by
      have := Polynomial.natDegree_pow_le_of_le (e a) (h a)
      simpa using this
    have h2 : (p a ^ e a).coeff (e a) = (p a).coeff 1 ^ e a := by
      have := Polynomial.coeff_pow_of_natDegree_le (m := e a) (h a)
      simpa using this
    refine ⟨Polynomial.natDegree_mul_le_of_le h1 ih1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih1, h2, ih2]

end GlobalTheory.ProductDegreeCoefficient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverEqFinrankOfTrivialFrobenius
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem natCard_le_of_forall_pow_eq_self (F : Type*) [CommRing F] [IsDomain F] [Finite F]
    (q : ℕ) (hq : 1 < q) (h : ∀ x : F, x ^ q = x) : Nat.card F ≤ q := by
  classical
  haveI := Fintype.ofFinite F
  have hne : (X ^ q - X : F[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
    rw [natDegree_X_pow, natDegree_X] at h1
    omega
  have hdeg : (X ^ q - X : F[X]).natDegree ≤ q := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_X_pow, natDegree_X]
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans ?_ hdeg
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro x _
  rw [mem_roots hne]
  simp [h x]

theorem exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) →
        (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧
          ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ _
  have hD : differentIdeal (𝓞 K) (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(fun P : HeightOneSpectrum (𝓞 M) => P.under (𝓞 K)) ''
    {P | P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}, (Ideal.finite_factors hD).image _, ?_⟩
  intro v hv hx
  haveI := v.isPrime
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hf : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.inertiaDeg (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    have hle : Nat.card (𝓞 M ⧸ P) ≤ Ideal.absNorm v.asIdeal := by
      refine natCard_le_of_forall_pow_eq_self _ _ hq fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, Ideal.Quotient.eq]
      exact hx P hP x
    have hN : Ideal.absNorm P = Nat.card (𝓞 M ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal P
    rw [← hN, ← h] at hle
    have hpos : 0 < P.inertiaDeg (𝓞 K) := P.inertiaDeg_pos (𝓞 K)
    have h2 : P.inertiaDeg (𝓞 K) ≤ 1 := by
      rw [← Nat.pow_le_pow_iff_right hq, pow_one]; exact hle
    omega
  have he : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.ramificationIdx (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    have hn : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 M) := by
      intro hd
      refine hv ⟨⟨P, hP.1, hP0⟩, hd, ?_⟩
      ext1
      exact (Ideal.over_def P v.asIdeal).symm
    haveI : Algebra.IsUnramifiedAt (𝓞 K) P := not_dvd_differentIdeal_iff.1 hn
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  refine ⟨?_, fun P hP => ?_⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
    haveI := P.2.1
    haveI := P.2.2
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M)
      Gal(M/K)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 Gal(M/K),
      Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(M/K), he P.1 P.2, hf P.1 P.2,
      IsGalois.card_aut_eq_finrank] at h
    simpa using h
  · haveI := hP.1
    haveI := hP.2
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P, hf P hP, pow_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMul
section
open Polynomial

namespace GlobalTheory

theorem rcout_coeff_succ {K : Type} [NormedField K] (g : K[X]) (a : K) (k : ℕ) :
    ((X - C a) * g).coeff (k + 1) = g.coeff k - a * g.coeff (k + 1) := by
  rw [mul_comm, coeff_mul_X_sub_C]; ring

theorem rcout_coeff_zero {K : Type} [NormedField K] (g : K[X]) (a : K) :
    ((X - C a) * g).coeff 0 = -(a * g.coeff 0) := by
  rw [mul_coeff_zero]; simp

theorem rcout_ultra {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem newton_step_root_outside_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  intro K _ _ g a ρ d hρ ha hle hlt
  set M := ‖g.coeff d‖ * ρ ^ d with hM
  have hMpos : 0 < M := by
    have := hlt (d + 1) (Nat.lt_succ_self d)
    exact lt_of_le_of_lt (by positivity) this
  have hapos : 0 < ‖a‖ := hρ.trans ha

  have hshift : ∀ k, ‖g.coeff k‖ * ρ ^ (k + 1) ≤ ρ * M := by
    intro k
    have := hle k
    calc ‖g.coeff k‖ * ρ ^ (k + 1) = ρ * (‖g.coeff k‖ * ρ ^ k) := by ring
      _ ≤ ρ * M := mul_le_mul_of_nonneg_left this hρ.le
  have hρM : ρ * M < ‖a‖ * M := mul_lt_mul_of_pos_right ha hMpos

  have haterm : ∀ j, ‖a * g.coeff j‖ * ρ ^ j = ‖a‖ * (‖g.coeff j‖ * ρ ^ j) := by
    intro j; rw [norm_mul]; ring

  have hup : ∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖a‖ * M := by
    intro j
    have hpj : 0 ≤ ρ ^ j := by positivity
    cases j with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
      exact mul_le_mul_of_nonneg_left (hle 0) hapos.le
    | succ k =>
      rw [rcout_coeff_succ]
      calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
          ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
        _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
            max_mul_of_nonneg _ _ hpj
        _ ≤ ‖a‖ * M := by
            apply max_le
            · exact (hshift k).trans hρM.le
            · rw [haterm]; exact mul_le_mul_of_nonneg_left (hle (k + 1)) hapos.le

  have hupl : ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖a‖ * M := by
    intro j hj
    have hpj : 0 ≤ ρ ^ j := by positivity
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [rcout_coeff_succ]
    calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hpj
      _ < ‖a‖ * M := by
          apply max_lt
          · exact lt_of_le_of_lt (hshift k) hρM
          · rw [haterm]; exact mul_lt_mul_of_pos_left (hlt (k + 1) hj) hapos

  have hlow : ‖a‖ * M ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
    have hpd : 0 < ρ ^ d := by positivity
    cases d with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
    | succ k =>
      rw [rcout_coeff_succ]
      set c := g.coeff k - a * g.coeff (k + 1)
      have key : a * g.coeff (k + 1) = g.coeff k - c := by simp [c]
      have h1 : ‖a‖ * M = ‖g.coeff k - c‖ * ρ ^ (k + 1) := by
        rw [← key, haterm]
      have h2 : ‖g.coeff k - c‖ * ρ ^ (k + 1) ≤
          max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖c‖ * ρ ^ (k + 1)) := by
        rw [← max_mul_of_nonneg _ _ hpd.le]
        exact mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpd.le
      rcases le_max_iff.mp (h1 ▸ h2 : ‖a‖ * M ≤ _) with h | h
      · exact absurd (lt_of_le_of_lt ((hshift k)) hρM) (not_lt.mpr h)
      · exact h
  exact ⟨fun j => (hup j).trans hlow, fun j hj => (hupl j hj).trans_le hlow⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe
section
namespace GlobalTheory.OneAddPowBound

theorem one_add_pow_le : ∀ {t : ℝ}, (0 : ℝ) ≤ t → ∀ (k : ℕ),
    ((1 : ℝ) + t) ^ k ≤ (2 : ℝ) ^ k * ((1 : ℝ) + t ^ k) := by
  intro t ht k
  have htk : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rcases le_total t 1 with h | h
  · have ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    have hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  · have ha : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    rw [mul_pow] at ha
    have hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith

end GlobalTheory.OneAddPowBound
end

