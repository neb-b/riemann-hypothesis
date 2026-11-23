module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagDegreeZero.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      ∃ f₃ g₃ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ (zetaFirst a₀ - zetaSecond a₀') f₃ g₃ ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) f₃ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₃ ∧
        (0 < k → f₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧ g₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          aeval (flagClosurePt y w e φ φ' t k) f₃ = aeval (flagClosurePt y w e φ φ' t k) g₃)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def flagFurtherTerm_independent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) → ∀ l : Fin r,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
                                  (Fin.append (Fin.append φ₁.deg y) (Fin.append φ₁.deg' y'))
                                  (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                                    (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
            (Fin.append (Fin.append φ₂.deg y) (Fin.append φ₂.deg' y'))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpFibreDegree.proof (ha : HomLocRingLocal.Statement.{u}) (hb : DivCycleHomLoc.Statement.{u})
    (hc : FiniteBirationalLength.Statement.{u}) (hd : BlowUpFibreSemilocal.Statement.{u}) :
    BlowUpFibreDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv
  have hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hdiv (by unfold divCycle; rw [dite_eq_right h])
  have hWp : W.IsPrime := hsupp.1.1.1
  have := hP.multiProj.isPrime
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hsupp.2 c
  have hg : IsMultiHomog (powMonomial c i : MRing ι O) c := isMultiHomog_powMonomial c i
  have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
        (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W :=
    Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩
  obtain ⟨hloc, hnoeth, hdim⟩ := ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2
  have := hloc
  have := hnoeth
  obtain ⟨B, _, _, _, hfin, hinj, hrank, e, he⟩ :=
    hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz
  have hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun w : homLocRing P W => (w : FractionRing (MRing ι O ⧸ P))) h0
    simp only [ZeroMemClass.coe_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))
    · exact hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))))
  obtain ⟨hfinite, hlen⟩ := hc (homLocRing P W) B hdim hinj hrank _ hz0
  have hmult := hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz
  have hdivW : divCycle P x W = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ) := by
    unfold divCycle
    rw [dite_eq_left hsupp]
  have := Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}

  have hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
      (have := 𝔫.2.isPrime;
       Module.length (Localization.AtPrime 𝔫.1)
         (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
           (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) =
        (((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat * specialRelDeg (e 𝔫).1 : ℕ) : ℕ∞) := by
    intro 𝔫
    rw [(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum] at hlen
  rw [hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]

  classical
  let p : Ideal (MRing (extIdx ι J) O) → Prop := fun W' =>
    W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
  have hite : ∀ W' : Ideal (MRing (extIdx ι J) O),
      (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
        divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) =
      ∑ᶠ (_ : p W'), divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) := by
    intro W'
    rw [finsum_eq_if]
    by_cases hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
    · by_cases hp : p W'
      · rw [if_pos hc', if_pos hp]
      · rw [if_pos hc', if_neg hp]
        have h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0 := by
          unfold divCycle
          rw [dite_eq_right]
          exact fun h => hp ⟨h.1, h.2, hc'⟩
        rw [h0, zero_mul]
    · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
  rw [finsum_congr hite, ← finsum_subtype_eq_finsum_cond p,
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have h0 : 0 ≤ divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1 := by
    unfold divCycle
    split_ifs <;> positivity
  rw [Nat.cast_mul, Int.toNat_of_nonneg h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalChartLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section ChartLength

theorem chartLength_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem chartLength_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  let _ := RingHomInvPair.of_ringEquiv τ
  let _ := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

theorem chartLength_quotient_self {A : Type*} [CommRing A] (I : Ideal A) :
    Module.length A (A ⧸ I) = Module.length (A ⧸ I) (A ⧸ I) :=
  Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem exists_aeval_chartSubst_eq_C_pow_mul (a : J → MRing ι R) (j₀ : J) (h : Polynomial (MRing ι R)) :
    ∃ (d : ℕ) (H : MRing (extIdx ι J) R),
      aeval (chartSubst a) H = Polynomial.C (a j₀ ^ d) * h := by
  refine ⟨h.natDegree, ∑ k ∈ Finset.range (h.natDegree + 1),
    liftForm (h.coeff k * a j₀ ^ (h.natDegree - k)) * newVar j₀ ^ k, ?_⟩
  have hs : Polynomial.C (a j₀ ^ h.natDegree) * h = ∑ k ∈ Finset.range (h.natDegree + 1),
      Polynomial.C (a j₀ ^ h.natDegree) * (Polynomial.C (h.coeff k) * Polynomial.X ^ k) := by
    rw [← Finset.mul_sum, ← h.as_sum_range_C_mul_X_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ h.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e : a j₀ ^ h.natDegree = a j₀ ^ (h.natDegree - k) * a j₀ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [map_mul, map_pow, aeval_chartSubst_liftForm, e]
  simp only [newVar, aeval_X, chartSubst, map_mul, map_pow]
  ring

end ChartLength

theorem BlowUpHorizontalChartLength.full : BlowUpHorizontalChartLength.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨-, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  set 𝔮 := W₀.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with h𝔮
  set Jx := (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with hJx
  set I := blowUpOf P u ⊔ Ideal.span {liftForm x} with hI
  let φ : MRing (extIdx ι J) O →+* Polynomial (MRing ι O) := (aeval (R := O) (chartSubst a)).toRingHom
  have hφ : ∀ F, φ F = aeval (chartSubst a) F := fun _ => rfl
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hW𝔮 : W = 𝔮.comap φ := by
    refine le_antisymm ?_ ?_
    · refine hmin.2 ⟨Ideal.comap_isPrime _ _, sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩
        (fun G hG => ?_)
      · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
      · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
        exact Ideal.mem_map_of_mem _ hxW
      · exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
    · intro G hG
      exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hlfa : ∀ m : ℕ, liftForm (a j₀ ^ m) ∉ W := fun m h =>
    ha₀ (hW₀p.mem_of_pow_mem m (show a j₀ ^ m ∈ W₀ from h))
  have hCa : ∀ e : ℕ, Polynomial.C (a j₀ ^ e) ∉ 𝔮 := by
    intro e h
    have h1 := Ideal.mem_map_C_iff.mp h 0
    rw [Polynomial.coeff_C_zero] at h1
    exact ha₀ (hW₀p.mem_of_pow_mem _ h1)
  have hq : 𝔮.IsPrime := inferInstance

  have hlift : ∀ t, t ∉ 𝔮 → ∃ (e : ℕ) (T : MRing (extIdx ι J) O),
      φ T = Polynomial.C (a j₀ ^ e) * t ∧ T ∉ W := by
    intro t ht
    obtain ⟨e, T, hT⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ t
    refine ⟨e, T, hT, fun hTW => ?_⟩
    have h1 : φ T ∈ 𝔮 := by rw [hW𝔮] at hTW; exact hTW
    rw [hφ, hT] at h1
    exact (hq.mem_or_mem h1).elim (hCa e) ht

  have hIJ : I ≤ Jx.comap φ := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono le_sup_left (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  have memI : ∀ G, φ G ∈ Jx → ∃ m : ℕ, liftForm (a j₀ ^ m) * G ∈ I := by
    intro G hG
    rw [hJx, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at hG
    obtain ⟨y, hy, z, hz, hyz⟩ := hG
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    have h1 : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) ∈
        Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P := by
      have e : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) =
          Polynomial.C (a j₀ ^ d) * y := by
        rw [map_sub, map_mul, map_mul, aeval_chartSubst_liftForm, aeval_chartSubst_liftForm, hH, ← hφ G,
          ← hyz]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hy
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem (P := P) (u := u) j₀ hrelB h1
    have hPB : Ideal.map (liftForm (J := J) : MRing ι O →ₐ[O] MRing (extIdx ι J) O) P ≤ blowUpOf P u :=
      Ideal.map_le_iff_le_comap.mpr fun p hp => liftForm_mem_blowUpOf hp
    have hm' := sup_le le_rfl hPB hm
    refine ⟨m + d, ?_⟩
    have e : liftForm (a j₀ ^ (m + d)) * G =
        liftForm (a j₀ ^ m) * (liftForm (a j₀ ^ d) * G - H * liftForm x) +
          (liftForm (a j₀ ^ m) * H) * liftForm x := by
      rw [pow_add, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hm')
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

  let Φ := Localization.localRingHom W 𝔮 φ hW𝔮
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨h, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    obtain ⟨e, T, hT, hTW⟩ := hlift t t.2
    have hs : T * liftForm (a j₀ ^ d) ∈ W.primeCompl := W.primeCompl.mul_mem hTW (hlfa d)
    refine ⟨IsLocalization.mk' _ (H * liftForm (a j₀ ^ e)) ⟨_, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    change (t : Polynomial (MRing ι O)) * φ (H * liftForm (a j₀ ^ e)) = φ (T * liftForm (a j₀ ^ d)) * h
    rw [map_mul, map_mul, hT]
    simp only [hφ, aeval_chartSubst_liftForm, hH]
    ring
  have hker : I.map (algebraMap _ (Localization.AtPrime W)) =
      (Jx.map (algebraMap _ (Localization.AtPrime 𝔮))).comap Φ := by
    ext z
    obtain ⟨⟨F, T⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [Ideal.mem_comap, Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨s, hs, hsF⟩
      refine ⟨φ s, fun h => hs (by rw [hW𝔮]; exact h), ?_⟩
      rw [← map_mul]
      exact hIJ hsF
    · rintro ⟨t, ht, htF⟩
      obtain ⟨e, T', hT', hT'W⟩ := hlift t ht
      obtain ⟨m, hm⟩ := memI (T' * F) (by
        rw [map_mul, hT', mul_assoc]
        exact Ideal.mul_mem_left _ _ htF)
      exact ⟨liftForm (a j₀ ^ m) * T', W.primeCompl.mul_mem (hlfa m) hT'W, by rw [mul_assoc]; exact hm⟩
  have hsurj' : Function.Surjective
      ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) :=
    Ideal.Quotient.mk_surjective.comp hsurj
  have hker' : I.map (algebraMap _ (Localization.AtPrime W)) =
      RingHom.ker ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact hker
  let τ := (Ideal.quotEquivOfEq hker').trans (RingHom.quotientKerEquivOfSurjective hsurj')
  unfold multAt
  rw [chartLength_localizedModule_quotient, chartLength_localizedModule_quotient,
    chartLength_quotient_self, chartLength_quotient_self]
  exact chartLength_self_eq_of_ringEquiv τ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpHorizontalMult.proof (hmin : BlowUpHorizontalMinimal.Statement.{u})
    (hchart : BlowUpHorizontalChartLength.Statement.{u}) : BlowUpHorizontalMult.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  have hm := hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW
  obtain ⟨hWp, hBW, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  obtain ⟨-, -, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hrel
  have hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    unfold divCycle at hW
    rw [dite_eq_right h] at hW
    exact hW rfl
  have hch := hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  have := hWp
  have hp := PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})
  unfold divCycle
  rw [dite_eq_left ⟨hm, hrel₀⟩, dite_eq_left hcond]
  congr 2
  exact (hp.symm.trans hch.symm : _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

