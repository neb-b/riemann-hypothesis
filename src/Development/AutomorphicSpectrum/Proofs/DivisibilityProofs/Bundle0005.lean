module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycEval_eq_sum {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    (n Z : Ideal (MRing ι R) → ℤ) (T : Finset (Ideal (MRing ι R)))
    (hT : Function.support Z ⊆ (T : Set (Ideal (MRing ι R)))) :
    cycEval n Z = ∑ W ∈ T, Z W * n W := by
  unfold cycEval
  refine finsum_eq_sum_of_support_subset _ ?_
  intro W hW
  apply hT
  intro h0
  apply hW
  simp [h0]

theorem cycEval_comb {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    (n : Ideal (MRing ι R) → ℤ) {α : Type} (s : Finset α) (c : α → ℤ)
    (Z : α → Ideal (MRing ι R) → ℤ) (hZ : ∀ a, (Function.support (Z a)).Finite) :
    cycEval n (fun W => ∑ a ∈ s, c a * Z a W) = ∑ a ∈ s, c a * cycEval n (Z a) := by
  classical
  set T : Finset (Ideal (MRing ι R)) := s.biUnion fun a => (hZ a).toFinset with hTdef
  have hsum : Function.support (fun W => ∑ a ∈ s, c a * Z a W) ⊆
      (T : Set (Ideal (MRing ι R))) := by
    intro W hW
    by_contra hWT
    apply hW
    refine Finset.sum_eq_zero fun a ha => ?_
    have : Z a W = 0 := by
      by_contra hne
      exact hWT (by
        simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
          Set.Finite.coe_toFinset]
        exact ⟨a, ha, hne⟩)
    simp [this]
  have hone : ∀ a ∈ s, cycEval n (Z a) = ∑ W ∈ T, Z a W * n W := by
    intro a ha
    refine cycEval_eq_sum n (Z a) T ?_
    intro W hW
    simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Set.Finite.coe_toFinset]
    exact ⟨a, ha, hW⟩
  have hrhs : ∑ a ∈ s, c a * cycEval n (Z a) = ∑ a ∈ s, c a * ∑ W ∈ T, Z a W * n W :=
    Finset.sum_congr rfl fun a ha => by rw [hone a ha]
  rw [cycEval_eq_sum n _ T hsum, hrhs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem cycNum_int_and_comb : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ (Z : Ideal (MRing ι O) → ℤ), (Function.support Z).Finite → ∀ H : MvPolynomial σ ℤ, cycNum Z cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q = ((cycEval (fun W => classNum cls H Q W) Z : ℤ) : ℝ)) ∧ (∀ (α : Type) (s : Finset α) (c : α → ℤ) (Z : α → Ideal (MRing ι O) → ℤ), (∀ a, (Function.support (Z a)).Finite) → ∀ H : MvPolynomial σ ℝ, cycNum (fun W => ∑ a ∈ s, c a * Z a W) cls H Q = ∑ a ∈ s, (c a : ℝ) * cycNum (Z a) cls H Q) := by
  intro O _ _ _ K _ _ ι _ σ cls Q
  refine ⟨?_, ?_⟩
  · intro Z hZ H
    have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
    have hT : Function.support Z ⊆ (hZ.toFinset : Set (Ideal (MRing ι O))) := by simp
    have key : cycEval (fun W => classNum cls H Q W) Z =
        ∑ μ ∈ H.support, H.coeff μ * cycList Z (classList cls μ ++ Q) := by
      unfold cycList
      rw [cycEval_eq_sum _ Z _ hT]
      simp only [cycEval_eq_sum _ Z _ hT, classNum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    unfold cycNum
    rw [MvPolynomial.support_map_of_injective _ hinj, key]
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.coeff_map]
    simp
  · intro α s c Z hZ H
    unfold cycNum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : cycList (fun W => ∑ a ∈ s, c a * Z a W) (classList cls μ ++ Q) =
        ∑ a ∈ s, c a * cycList (Z a) (classList cls μ ++ Q) :=
      cycEval_comb _ s c Z hZ
    rw [this]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariant
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_perm_of_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → ((K → ℤ) → ℤ)) := by
    constructor
    intro a b g
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring
  unfold intNumL intNum GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

theorem numbers_list_perm : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  refine ⟨fun F _ K _ _ ι _ V l l' h => intNumL_perm_of_perm F K ι V l l' h, ?_⟩
  intro O _ _ _ K _ _ ι _ Z l l' h
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm_of_perm _ K ι (specialIdeal W) l l' h

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsMixedDifferenceExpansion
section
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem exists_monomial_mixExpansion {σ : Type} [Fintype σ] (d : ℕ) :
    ∀ s : σ →₀ ℕ, s.degree = d → ∃ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ,
      mixDiff (monomial s (1 : ℝ)) = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i ∧
      ∀ i, (Gs i).IsHomogeneous (d - 1) ∧ (d = 0 → Gs i = 0) := by
  classical
  induction d with
  | zero =>
    intro s hs
    have hs0 : s = 0 := (Finsupp.degree_eq_zero_iff s).mp hs
    subst hs0
    refine ⟨fun _ => 0, ?_, fun i => ⟨isHomogeneous_zero _ _ _, fun _ => rfl⟩⟩
    simp [mixDiff]
  | succ d ih =>
    intro s hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
      by_contra h
      push_neg at h
      have h0 : s = 0 := Finsupp.ext h
      simp [h0] at hs
    have hle : Finsupp.single i 1 ≤ s := by
      rw [Finsupp.single_le_iff]
      omega
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single i 1 :=
      ⟨s - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩
    have hdeg : s'.degree = d := by
      have e : (s' + Finsupp.single i 1).degree = s'.degree + 1 := by
        rw [Finsupp.degree_eq_weight_one, map_add (f := _)]
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      omega
    obtain ⟨G', hG', hG'h⟩ := ih s' hdeg
    refine ⟨fun j => (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0) + X (Sum.inr i) * G' j,
      ?_, fun j => ⟨?_, fun h => absurd h (Nat.succ_ne_zero d)⟩⟩
    · have key : mixDiff (monomial (s' + Finsupp.single i 1) (1 : ℝ)) =
          (X (Sum.inl i) - X (Sum.inr i)) * rename Sum.inl (monomial s' (1 : ℝ)) +
            X (Sum.inr i) * mixDiff (monomial s' (1 : ℝ)) := by
        simp only [mixDiff]
        rw [monomial_add_single, pow_one, map_mul, map_mul, rename_X, rename_X]
        ring
      rw [key, hG', Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    · have h2 : (X (Sum.inr i) * G' j : MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d := by
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · rw [(hG'h j).2 h0, mul_zero]
          exact isHomogeneous_zero _ _ _
        · have h3 := (isHomogeneous_X ℝ (Sum.inr i : σ ⊕ σ)).mul (hG'h j).1
          rwa [show 1 + (d - 1) = d by omega] at h3
      have h1 : (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0 :
          MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d := by
        split_ifs
        · exact (isHomogeneous_monomial _ hdeg).rename_isHomogeneous
        · exact isHomogeneous_zero _ _ _
      rw [Nat.add_sub_cancel]
      exact h1.add h2

theorem exists_mixExpansion_mixDiff (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ)
    (hF : F.IsHomogeneous n) : ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  classical
  have H := fun s : σ →₀ ℕ => fun h : s.degree = n => exists_monomial_mixExpansion n s h
  choose! G hGeq hGhom using H
  have hdeg : ∀ s ∈ F.support, s.degree = n := fun s hs => by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hs)
  have hlin : mixDiff F = ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ)) := by
    conv_lhs => rw [F.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mixDiff, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show monomial s (F.coeff s) = C (F.coeff s) * monomial s (1 : ℝ) by rw [C_mul_monomial, mul_one],
      map_mul, map_mul, rename_C, rename_C]
    ring
  refine ⟨fun i => ∑ s ∈ F.support, C (F.coeff s) * G s i, ?_⟩
  unfold IsMixExpansion
  refine ⟨?_, fun i => ?_⟩
  · rw [hlin]
    calc ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ))
        = ∑ s ∈ F.support, C (F.coeff s) * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * G s i :=
          Finset.sum_congr rfl fun s hs => by rw [hGeq s (hdeg s hs)]
      _ = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * ∑ s ∈ F.support, C (F.coeff s) * G s i := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  · exact IsHomogeneous.sum _ _ _ fun s hs => ((hGhom s (hdeg s hs) i).1).C_mul _
end

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FibreComponentDivisorProperties
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.FibreComp

theorem mem_minimalPrimes_span_of_mem {T : Type} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    {q : Ideal T} {a b : T} (hq : q ∈ (Ideal.span {a}).minimalPrimes) (hb : b ∈ q) (hb0 : b ≠ 0) :
    q ∈ (Ideal.span {b}).minimalPrimes := by
  have hqp : q.IsPrime := hq.1.1
  refine ⟨⟨hqp, (Ideal.span_singleton_le_iff_mem q).2 hb⟩, ?_⟩
  rintro p ⟨hp, hbp⟩ hpq
  by_contra hne
  have hlt : p < q := lt_of_le_of_ne hpq (fun h => hne (h ▸ le_rfl))
  have hbp' : b ∈ p := (Ideal.span_singleton_le_iff_mem p).1 hbp
  have hbot : (⊥ : Ideal T) < p := by
    refine bot_lt_iff_ne_bot.2 (fun h => hb0 ?_)
    rw [h] at hbp'
    exact (Submodule.mem_bot T).1 hbp'
  haveI : (Ideal.span {a}).IsPrincipal := ⟨⟨a, rfl⟩⟩
  haveI := hqp
  haveI := hp
  have h1 : q.height ≤ ((1 : ℕ) : ℕ∞) := by
    have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) q hq
    exact_mod_cast this
  have hp1 : p.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp h1) p hp hlt
  have hp0 : p.height ≤ ((0 : ℕ) : ℕ∞) := by
    have h' : p.height < 1 := by exact_mod_cast hp1
    rw [Order.lt_one_iff.mp h']
    simp
  have h2 := (Ideal.height_le_iff.mp hp0) ⊥ Ideal.isPrime_bot hbot
  simp at h2

theorem mem_minimalPrimes_sup_of_mem {S : Type} [CommRing S] [IsNoetherianRing S] {P W : Ideal S}
    [P.IsPrime] {f b : S} (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) (hb : b ∈ W) (hbP : b ∉ P) :
    W ∈ (P ⊔ Ideal.span {b}).minimalPrimes := by
  have hπ : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hcomap : ∀ x : S, Ideal.comap (Ideal.Quotient.mk P) (Ideal.span {Ideal.Quotient.mk P x}) =
      P ⊔ Ideal.span {x} := by
    intro x
    have hx : Ideal.span {Ideal.Quotient.mk P x} = Ideal.map (Ideal.Quotient.mk P) (Ideal.span {x}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hx, Ideal.comap_map_of_surjective' _ hπ, Ideal.mk_ker, sup_comm]
  rw [← hcomap f, Ideal.comap_minimalPrimes_eq_of_surjective hπ] at hW
  obtain ⟨W', hW', rfl⟩ := hW
  rw [← hcomap b, Ideal.comap_minimalPrimes_eq_of_surjective hπ]
  refine ⟨W', ?_, rfl⟩
  have hbW' : Ideal.Quotient.mk P b ∈ W' := hb
  have hb0 : Ideal.Quotient.mk P b ≠ 0 := fun h => hbP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact mem_minimalPrimes_span_of_mem hW' hbW' hb0

theorem length_toNat_ne_zero {S : Type} [CommRing S] [IsNoetherianRing S] {J W : Ideal S}
    [hWp : W.IsPrime] (hW : W ∈ J.minimalPrimes) :
    (Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J))).toNat ≠ 0 := by
  classical
  haveI : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  rw [Ne, ENat.toNat_eq_zero, not_or]
  refine ⟨?_, ?_⟩
  · rw [Module.length_eq_zero_iff]
    intro hsub
    have h10 : (LocalizedModule.mk (1 : S ⧸ J) (1 : W.primeCompl) :
        LocalizedModule W.primeCompl (S ⧸ J)) = LocalizedModule.mk 0 1 := Subsingleton.elim _ _
    rw [LocalizedModule.mk_eq] at h10
    obtain ⟨u, hu⟩ := h10
    simp only [one_smul, smul_zero] at hu
    have hu' : (u : S) ∈ J := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] at hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp hu
    exact u.2 (hW.1.2 hu')
  · set JA : Ideal (Localization.AtPrime W) := J.map (algebraMap S (Localization.AtPrime W)) with hJA
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈ JA.minimalPrimes := by
      rw [hJA, IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hW
    haveI : Ring.KrullDimLE 0 (Localization.AtPrime W ⧸ JA) := by
      rw [Ring.krullDimLE_zero_iff]
      intro I hI
      have hQ : (I.comap (Ideal.Quotient.mk JA)).IsPrime := Ideal.comap_isPrime _ I
      have hJQ : JA ≤ I.comap (Ideal.Quotient.mk JA) := by
        intro x hx
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact I.zero_mem
      have hQm : I.comap (Ideal.Quotient.mk JA) ≤ IsLocalRing.maximalIdeal _ :=
        IsLocalRing.le_maximalIdeal hQ.ne_top
      have hmQ := hm.2 ⟨hQ, hJQ⟩ hQm
      have hIeq : I = Ideal.map (Ideal.Quotient.mk JA) (IsLocalRing.maximalIdeal _) := by
        rw [← le_antisymm hQm hmQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk JA)
          Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime W))
          with h | h
      · exact absurd (hIeq.trans h) hI.ne_top
      · rw [hIeq]
        exact h
    haveI : IsArtinianRing (Localization.AtPrime W ⧸ JA) :=
      IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    have hlenQ : Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ JA) ≠ ⊤ := by
      rw [Module.length_eq_of_surjective (S := Localization.AtPrime W)
        (R := Localization.AtPrime W ⧸ JA) (M := Localization.AtPrime W ⧸ JA)
        (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
      exact Module.length_ne_top
    let x : LocalizedModule W.primeCompl (S ⧸ J) := LocalizedModule.mk 1 1
    let g : Localization.AtPrime W →ₗ[Localization.AtPrime W] LocalizedModule W.primeCompl (S ⧸ J) :=
      LinearMap.toSpanSingleton _ _ x
    have hker : JA ≤ LinearMap.ker g := by
      rw [hJA, Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, LinearMap.mem_ker]
      show (algebraMap S (Localization.AtPrime W) j) • x = 0
      rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hj, LocalizedModule.zero_mk]
    have hsurj : Function.Surjective (JA.liftQ g hker) := by
      intro y
      refine LocalizedModule.induction_on (fun m s => ?_) y
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective m
      refine ⟨Submodule.Quotient.mk (Localization.mk t s), ?_⟩
      rw [Submodule.liftQ_apply]
      show Localization.mk t s • x = _
      rw [LocalizedModule.mk_smul_mk, Algebra.smul_def, mul_one, mul_one, Ideal.Quotient.algebraMap_eq]
    exact ne_top_of_le_ne_top hlenQ (Module.length_le_of_surjective _ hsurj)

theorem facts_of_divCycle_ne_zero {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    {P W : Ideal (MRing ι R)} {f : MRing ι R} (h : divCycle P f W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  by_contra hc
  apply h
  unfold divCycle
  rw [dite_eq_right hc]

theorem fibre_comp : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → (∀ W, IsFibreComp P W ↔ divCycle P (C ϖ) W ≠ 0) ∧ (∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W → IsFibreComp P W) ∧ ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g → ∀ W, ratDiv P f g W ≠ 0 → IsFibreComp P W := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  classical
  haveI : IsNoetherianRing (MRing ι O) :=
    (inferInstance : IsNoetherianRing (MvPolynomial ((k : K) × ι k) O))
  obtain ⟨⟨hPprime, -, -⟩, hnt, -⟩ := hP
  haveI := hPprime
  have hmax : Ideal.map (C : O →+* MRing ι O) (IsLocalRing.maximalIdeal O) =
      Ideal.span {(C ϖ : MRing ι O)} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h2 : ϖ ∈ Ideal.comap (C : O →+* MRing ι O) P := Ideal.mem_comap.mpr h
    rw [hnt] at h2
    exact hϖ.ne_zero ((Submodule.mem_bot O).1 h2)
  have key : ∀ f : MRing ι O, f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W →
      IsFibreComp P W := by
    intro f _ W hW hϖW
    obtain ⟨hWmin, hWrel⟩ := facts_of_divCycle_ne_zero hW
    unfold IsFibreComp
    rw [hmax]
    exact ⟨mem_minimalPrimes_sup_of_mem hWmin hϖW hϖP, hWrel⟩
  refine ⟨?_, fun a f _ hf W hW hϖW => key f hf W hW hϖW, ?_⟩
  · intro W
    constructor
    · intro hF
      unfold IsFibreComp at hF
      rw [hmax] at hF
      obtain ⟨hWmin, hWrel⟩ := hF
      haveI : W.IsPrime := hWmin.1.1
      unfold divCycle
      rw [dite_eq_left ⟨hWmin, hWrel⟩]
      exact Nat.cast_ne_zero.mpr (length_toNat_ne_zero hWmin)
    · intro hW
      obtain ⟨hWmin, hWrel⟩ := facts_of_divCycle_ne_zero hW
      unfold IsFibreComp
      rw [hmax]
      exact ⟨hWmin, hWrel⟩
  · intro b f g hV W hW
    obtain ⟨-, hfP, hgP, hvert, -⟩ := hV
    have hϖW : (C ϖ : MRing ι O) ∈ W := hvert W hW
    by_cases hfW : divCycle P f W = 0
    · have hgW : divCycle P g W ≠ 0 := by
        intro hg
        apply hW
        unfold ratDiv
        rw [hfW, hg, sub_zero]
      exact key g hgP W hgW hϖW
    · exact key f hfP W hfW hϖW

end GlobalTheory.CompanionTheory.Ar.Num.FibreComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalPowerSum
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem sh_tot_pk_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ σ : Ψ) (k : ℕ) (Q : RP Ψ N), 1 ≤ k → Sh j σ (pk τ k * Q) = (if σ = τ then k * degFl (pkLow j τ (k - 1) * Q) else 0) ∧ Tot σ (pk τ k * Q) = (if σ = τ ∧ k = 1 then N * degFl Q else 0) :=
  RootFieldNumerics.shift_power_sum_mul

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairSplitSum
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.CkAppend

theorem classList_mapDomain_eq {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename_eq {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain_eq]

theorem psumExpansion_rename (N k : ℕ) (i : Fin N) :
    psumExpansion N k i =
      rename (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) (psumExpansion 1 k 0) := by
  simp [psumExpansion]

theorem pairNum_psumExpansion {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {N : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin N → K → ℤ)
    (f g : Fin N → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (psumExpansion N k) Q =
      ∑ i, pairNum P (fun _ : Fin 1 => x i) (fun _ => x' i) (fun _ => f i) (fun _ => g i)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_one]
  have he : Function.Injective (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) :=
    Sum.map_injective.mpr ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  have hc : Sum.elim x x' ∘ Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i) =
      Sum.elim (fun _ : Fin 1 => x i) (fun _ : Fin 1 => x' i) := by
    funext s
    rcases s with s | s <;> rfl
  simp only [psumExpansion_rename N k i, classNum_rename_eq _ _ he, hc]

theorem ck_append : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (j j' : ℕ) (T : LocPair ι O (Fin (j + j')))
    (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)),
    T.ck P k Q = (T.comp (Fin.castAdd j')).ck P k Q + (T.comp (Fin.natAdd j)).ck P k Q := by
  intro O _ _ _ K _ _ ι _ j j' T P k Q
  unfold LocPair.ck
  rw [pairNum_psumExpansion, pairNum_psumExpansion, pairNum_psumExpansion, Fin.sum_univ_add]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.CkAppend
end

