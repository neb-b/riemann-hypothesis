module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.GwCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.greenberg_wiles_count_mod_l :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (K : Subgroup (G F Ω)) (r : ℕ) (c : InfinitePlace F → G F Ω), l ≠ 2 → ContainsAbove S l → ContAction ρ → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → (∀ w, w.IsReal → IsCCAt w (c w)) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * archH0Card S ρ c ≤ Nat.card M ^ (r + 2 + S.card + Module.finrank ℚ F) := by
  intro P F Ω _ _ _ _ _ l hp M _ _ _ _ _ S ρ K r c hl hS hρ hN hK hρK hKc hX hc
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  choose Av hA using fun v : S => (exists_isPlaceOver Ω v.1 : ∃ A : ValuationSubring Ω, IsPlaceOver A v.1)
  have e := P.gw F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc (fun _ => ⊤)
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hp.out⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  have hf1 : Finite (H1 ρ) := (P.gf F Ω l 1 M S ρ one_pos hS hρ).2.1
  obtain ⟨hZ, eZ⟩ := cocycle_card_euler_formula _ _ M ρ hρ hf1
  refine ⟨hZ, ?_⟩
  have hM : 0 < Nat.card M := Nat.card_pos
  have hD : Nat.card (TDual (ZMod (l ^ 1)) M) = Nat.card M := by
    show Nat.card (Module.Dual (ZMod (l ^ 1)) M) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)) (V := Module.Dual (ZMod (l ^ 1)) M),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
  have hsha := (tate_shafarevich_card_mod_l F Ω l (TDual (ZMod (l ^ 1)) M) S (twDual μ ρ) Av K r hA hN hK (fun g hg y => by
    refine DFunLike.ext _ _ fun m => ?_
    have h1 : μ (toGS Ω _ g) = 1 := by
      have := hKc hg
      rw [← hμ] at this
      exact this
    rw [twDual_apply, h1, ← map_inv, hρK _ (K.inv_mem hg), Units.val_one, one_mul]) hX).2
  rw [hD, ← dualSelmer_orthogonalComplement_conditions P.loc.lt F Ω l M S ρ hρ μ Av hμ hA] at hsha
  have hsel : Sel ρ (locFam S Av) (continuous_locFam S Av) (fun _ => ⊤) = ⊤ :=
    eq_top_iff.2 fun x _ => (mem_Sel _ _ _ _ _).2 fun _ => trivial
  have htop : ∀ (N : Type) [AddCommGroup N] [Module (ZMod (l ^ 1)) N],
      Nat.card (⊤ : Submodule (ZMod (l ^ 1)) N) = Nat.card N :=
    fun N _ _ => Nat.card_congr Submodule.topEquiv.toEquiv
  rw [hsel, htop] at e
  simp only [htop] at e
  have hloc : (∏ v : S, Nat.card (H1 (ρ.comp (locFam S Av v)))) ≤
      (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) * Nat.card M ^ (S.card + Module.finrank ℚ F) := by
    refine (Finset.prod_le_prod' fun v _ => (local_h1_finite_mod_l P.loc.lf P.loc.lt P.loc.le F Ω l M (Av v) v.1
      (ρ.comp (locFam S Av v)) (hA v) (hρ.comp' (continuous_locFam S Av v))).2).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe,
      Finset.sum_coe_sort S (fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0)]
    exact Nat.add_le_add_left (sum_local_degree_above_l_le_finrank F l S) _
  have p1 : 0 < Nat.card (H0 ρ) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have key := e.le.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ hsha) hloc)
  generalize (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) = q at p3 key
  generalize Nat.card (H0 (twDual μ ρ)) = b at p2 key
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos p1 p3)
  calc _ = (Nat.card (Z1 ρ) * Nat.card (H0 ρ)) * 1 * q * archH0Card S ρ c := by ring
    _ ≤ (Nat.card (Z1 ρ) * Nat.card (H0 ρ)) * b * q * archH0Card S ρ c := by gcongr; exact p2
    _ = Nat.card M * (Nat.card (H1 ρ) * b * q * archH0Card S ρ c) := by rw [eZ]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ key
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PlacesBd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_eq (F : Type) [Field F] (N : ℕ) (hN : N ≠ 0) :
    plDvd F N = ⋃ p ∈ N.primeFactors, plDvd F p := by
  ext v
  simp only [plDvd, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · have key : ∀ M : ℕ, M ≠ 0 → ((M : 𝓞 F) ∈ v.asIdeal) →
        ∃ p ∈ M.primeFactors, (p : 𝓞 F) ∈ v.asIdeal := by
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro hM hv
        by_cases h1 : M = 1
        · subst h1
          rw [Nat.cast_one] at hv
          exact (v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hv)).elim
        · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
          rw [Nat.cast_mul] at hv
          rcases v.isPrime.mem_or_mem hv with h | h
          · exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p m, hM⟩, h⟩
          · have hm0 : m ≠ 0 := by
              rintro rfl
              simp at hM
            have hlt : m < p * m := by
              have := hp.two_le
              have := Nat.pos_of_ne_zero hm0
              nlinarith
            obtain ⟨q, hq, hqv⟩ := ih m hlt hm0 h
            have hq' := Nat.mem_primeFactors.1 hq
            exact ⟨q, Nat.mem_primeFactors.2 ⟨hq'.1, hq'.2.1.mul_left p, hM⟩, hqv⟩
    exact key N hN
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨m, hm⟩ := (Nat.mem_primeFactors.1 hp).2.1
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv

theorem UpperTheory.V.Ws.exists_uniform_bound_ncard_placesDividing :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (N : ℕ), U.Normal → IsOpen (U : Set (G ℚ Ω)) → N ≠ 0 → ∃ g : ℕ, ∀ (F : IntermediateField ℚ Ω) [NumberField F], cycU l U ≤ F.fixingSubgroup → (plDvd F N).ncard ≤ g := by
  intro Ω _ _ _ l _ U N hUn hUo hN
  haveI := hUn
  haveI : (cycU l U).Normal := by
    unfold cycU
    infer_instance
  have hUi : U.index ≠ 0 := by
    haveI := Subgroup.quotient_finite_of_isOpen U hUo
    exact Subgroup.index_ne_zero_of_finite
  have hUle : ∀ {X : Type} (s : Finset ℕ) (f : ℕ → Set X),
      (⋃ p ∈ s, f p).ncard ≤ ∑ p ∈ s, (f p).ncard := by
    intro X s f
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hb : ∀ p : ℕ, ∃ n, p.Prime → OrbLe (cycU l U) p n := by
    intro p
    by_cases hA : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
    · obtain ⟨A₀, hA₀⟩ := hA
      refine ⟨(cycU l U ⊔ Dec A₀).index, fun hp => ?_⟩
      have hK := index_cyclotomicKer_sup_decompositionGroup_ne_zero Ω l p A₀ hp hA₀
      have hs := supIndex (G ℚ Ω) (cycZ ℚ Ω l).ker U (Dec A₀) hUi hK
      exact orbIndex Ω p (cycU l U) A₀ hp hA₀ hs.1
    · exact ⟨0, fun _ => ⟨∅, by simp, by simp, fun A hA' => (hA ⟨A, hA'⟩).elim⟩⟩
  choose nf hnf using hb
  refine ⟨∑ p ∈ N.primeFactors, nf p, fun F _ hF => ?_⟩
  rw [plDvd_eq F N hN]
  refine (hUle _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpp := (Nat.mem_primeFactors.1 hp).1
  exact ncard_placesDividing_le_of_orbitBound Ω F (cycU l U) p (nf p) hpp.ne_zero hF (hnf p hpp)
end

