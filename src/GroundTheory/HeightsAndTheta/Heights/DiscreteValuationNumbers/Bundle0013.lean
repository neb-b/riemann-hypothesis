module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFibreVarieties
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

private theorem withBot_eq_of_add_one_eq (a : WithBot ℕ∞) (m : ℕ)
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m : WithBot ℕ∞) + 1) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    rw [Nat.cast_add, Nat.cast_one, e] at h
    exact WithBot.bot_ne_coe h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) = (m + 1 : ℕ) := by
        apply WithBot.coe_injective
        simpa using h
      exact ENat.top_ne_natCast (m + 1) h'
    | coe a =>
      have h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]; push_cast; rfl
      have : a + 1 = m + 1 := by exact_mod_cast h'
      have ham : a = m := by omega
      subst ham
      rfl

theorem FibreVarieties.proof
    (hGen : GenericFibProps.Statement.{u}) (hBound : GenericDimBound.Statement.{u})
    (hGe : GenericDimGe.Statement.{u}) (hCorr : SpecialIdealCorresp.Statement.{u})
    (hSpecHomog : SpecialIdealMultiHomog.Statement.{u}) (hSup : SupSpanMultiHomog.Statement.{u})
    (hMin : MinimalPrimeMultiHomog.Statement.{u}) (hQuot : SpecialQuotDim.Statement.{u})
    (hComp : ComponentDim.Statement.{u}) : FibreVarieties.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  obtain ⟨hprime, hhomog, hforms⟩ := hGen O K ι P hP.multiProj hP.noTorsion
  have hcast : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
      ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    congr 1; omega
  refine ⟨⟨⟨hprime, hhomog, ?_⟩, ?_⟩, ?_⟩
  ·
    intro k
    obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    obtain ⟨-, h⟩ := hforms _ _ (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, i⟩) hi
    exact ⟨i, by simpa [MvPolynomial.map_X] using h⟩
  ·
    have h1 := hBound O K ι P hP.multiProj hP.noTorsion
    have h2 := hGe O K ι P hP.multiProj.isPrime hP.noTorsion
    rw [hP.dim, hcast] at h1 h2
    exact withBot_eq_of_add_one_eq _ _ (le_antisymm h1 h2)
  ·
    intro W hW
    have hW0 := hW
    unfold divCycle at hW
    split_ifs at hW with h
    · obtain ⟨hWmin, hWrel⟩ := h
      have hWp : W.IsPrime := hWmin.1.1
      have hϖW : (C ϖ : MRing ι O) ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      obtain ⟨hsp, -, hrel, -⟩ := hCorr O ϖ hϖ K ι P W hWp hϖW
      have hJ : IsMultiHomogIdeal (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
        hSup O K ι P (C ϖ) 0 hP.multiProj.multiHomog (isWeightedHomogeneous_C _ _)
      have hWh : IsMultiHomogIdeal W := hMin O K ι _ W hJ hWmin
      have hϖP : (C ϖ : MRing ι O) ∉ P := by
        intro hmem
        have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
        rw [hP.noTorsion, Ideal.mem_bot] at this
        exact hϖ.ne_zero this
      refine ⟨⟨hsp, hSpecHomog O K ι W hWh, hrel.mp hWrel⟩, ?_⟩
      rw [hQuot O ϖ hϖ K ι W hϖW]
      exact hComp O ϖ hϖ K ι P d hP 0 (C ϖ) (isWeightedHomogeneous_C _ _) hϖP W hW0 hϖW
    · exact absurd rfl hW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericDimBound.proof (hmax : MaximalIdealHeightFG.Statement.{u}) :
    GenericDimBound.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hT
  classical
  let KO := FractionRing O
  let S := MRing ι O
  let MainNotions := MRing ι KO
  let φ : S →+* MainNotions := algebraMap S MainNotions
  let M : Submonoid S := (nonZeroDivisors O).map (C : O →+* S)
  have : IsLocalization M MainNotions := MvPolynomial.isLocalization (nonZeroDivisors O) KO

  have hPker : ∀ f ∈ P, constantCoeff f = 0 := by
    intro f hf
    have h0 := hP.multiHomog f hf 0
    rw [weightedHomogeneousComponent_zero] at h0
    · have : AddMonoidAlgebra.coeff f 0 ∈ P.comap (C : O →+* S) := h0
      rw [hT, Ideal.mem_bot] at this
      rw [constantCoeff_eq]
      exact this
    · intro v h
      have := congrFun h v.1
      simp [blockWeight] at this

  have hdisj : Disjoint (M : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* S) := hmem
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  have hPK : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj

  let N : Ideal MainNotions := RingHom.ker (constantCoeff : MainNotions →+* KO)
  have hNmax : N.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩
  have hPN : genFib P ≤ N := by
    rw [genFib, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]
  let A := MainNotions ⧸ genFib P
  let mk : MainNotions →+* A := Ideal.Quotient.mk (genFib P)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomapN : (N.map mk).comap mk = N := by
    rw [Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]
  let m : Ideal A := N.map mk
  have hm : m.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h
    · exfalso
      have : N = ⊤ := by rw [← hcomapN, h, Ideal.comap_top]
      exact hNmax.ne_top this
    · exact h
  have : Algebra.FiniteType KO A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P))
      (Ideal.Quotient.mkₐ_surjective KO _)
  have hht : (m.height : WithBot ℕ∞) = ringKrullDim A := hmax KO A m hm

  let g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R := S) (P : Set S) := fun x =>
    ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show mk (φ f) ∈ x.asIdeal
      have h0 : mk (φ f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)
      rw [h0]
      exact x.asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro x y hxy
    have h1 : x.asIdeal.comap mk < y.asIdeal.comap mk :=
      lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h =>
        hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))
    exact (IsLocalization.orderEmbedding M MainNotions).strictMono h1

  have hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0 := by
    intro f
    rw [hcomapN, Ideal.mem_comap, RingHom.mem_ker]
    show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _
    rw [constantCoeff_map]
    exact ⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M1 : Ideal S := (IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)
  let top : PrimeSpectrum.zeroLocus (R := S) (P : Set S) :=
    ⟨⟨M1, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [hPker f hf]
      exact Ideal.zero_mem _⟩
  have htop : g ⟨m, hm.isPrime⟩ < top := by
    show (m.comap mk).comap φ < M1
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => ?_
    · show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [(hlastN f).mp hf]
      exact Ideal.zero_mem _
    · have hC : (C ϖ : S) ∈ M1 := by
        show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O
        rw [constantCoeff_C]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
      rw [← h, hlastN, constantCoeff_C] at hC
      exact hϖ.ne_zero hC

  have key : ∀ n : ℕ, (n : ℕ∞) ≤ m.height →
      ((n + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) := by
    intro n hn
    rw [show m.height = Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩] at hn
    obtain ⟨p, hplast, hplen⟩ :=
      Order.exists_series_of_le_height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) hn
    have hlt : (p.map g hg).last < top := by
      rw [LTSeries.last_map, hplast]
      exact htop
    have := Order.LTSeries.length_le_krullDim ((p.map g hg).snoc top hlt)
    simpa [hplen] using this

  rw [← hht, ringKrullDim_quotient P]
  have h1 := key 0 (by simp)
  have hne : Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) ≠ ⊥ := fun h => by
    rw [h] at h1; simp at h1
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at key ⊢
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
  refine ENat.forall_natCast_le_iff_le.mp fun a ha => ?_
  rcases a with _ | k
  · simp
  · have hk : (k : ℕ∞) ≤ m.height := by
      have : (k : ℕ∞) + 1 ≤ m.height + 1 := by exact_mod_cast ha
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
    have := key k hk
    exact_mod_cast this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_map {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibProps.proof : GenericFibProps.Statement := by
  intro O _ _ _ K _ _ ι _ P hP hT
  set φ := algebraMap O (FractionRing O) with hφ
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ := rfl
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P := rfl
  have hprime : (genFib P).IsPrime :=
    hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj
  have hunder : (genFib P).comap (MvPolynomial.map φ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj
  refine ⟨hprime, ?_, ?_⟩
  · intro x hx b
    rw [hgen, IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := hx
    simp only [hmap, map_C] at h
    have hm0 : φ m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p := by
      rw [← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))
  · intro s c hs hsP
    refine ⟨?_, ?_⟩
    · intro d hd
      apply hs
      intro h0
      rw [coeff_map, h0, map_zero] at hd
      exact hd rfl
    · intro h
      apply hsP
      rw [← hunder]
      exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAddFirstField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GroundTheory.Heights₂.Heights.FieldNumbers

universe u

private lemma mixedDiff_eventually_zero {K : Type*} (h : (K → ℤ) → ℤ)
    (hh : ∀ᶠ m in Filter.atTop, h m = 0) {n : ℕ} (bs : Fin n → K → ℤ) :
    ∀ᶠ m in Filter.atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction (List.ofFn bs) with
  | nil => simpa using hh
  | cons b l ih =>
    have hs : Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-b) Filter.tendsto_id
    filter_upwards [ih, hs.eventually ih] with m h1 h2
    simp [List.foldr, diffStep, h1, h2]

private lemma eventualValue_of_eventually_zero {K : Type*} (f : (K → ℤ) → ℤ)
    (hf : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  classical
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨0, hf⟩
  rw [eventualValue, dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

theorem IntNumAddFirst.proof (h1 : FieldNumbers.IntNumAdd.Statement.{u})
    (h2 : FieldNumbers.IntNumZeroSlot.Statement.{u})
    (h3 : FieldNumbers.HilbDegreeBound.Statement.{u}) : IntNumAddFirst.Statement.{u} := by
  intro F _ K _ _ ι _ n G hG hGh hdim b₁ b₂ L
  have hupd : ∀ b : K → ℤ,
      Matrix.vecCons b L = Function.update (Matrix.vecCons (0 : K → ℤ) L) 0 b := fun b => by
    simp [Matrix.vecCons, Fin.update_cons_zero]
  by_cases hrel : IsRelevant G
  ·
    have hle : relDim G = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) ∨
        relDim G < ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      have hc : ((n + 1 : ℕ) : WithBot (WithTop ℤ)) = (((n + 1 : ℕ) : ℤ) : WithTop ℤ) := by
        rfl
      unfold relDim
      generalize ringKrullDim (MRing ι F ⧸ G) = x at hdim ⊢
      induction x using WithBot.recBotCoe with
      | bot => exact Or.inr (WithBot.bot_lt_coe _)
      | coe d =>
        induction d using ENat.recTopCoe with
        | top => exfalso; exact absurd hdim (by simp)
        | coe e =>
          have he : e < n + 2 + Fintype.card K := by
            rw [← WithBot.coe_natCast] at hdim
            exact_mod_cast WithBot.coe_lt_coe.1 hdim
          simp only [WithBot.map_coe]
          rw [hc]
          show ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = _ ∨
            ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < _
          rcases (show (e : ℤ) - Fintype.card K ≤ ((n + 1 : ℕ) : ℤ) by omega).lt_or_eq with h | h
          · exact Or.inr (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 h))
          · exact Or.inl (by rw [h])
    rcases hle with heq | hlt
    · rw [hupd (b₁ + b₂), hupd b₁, hupd b₂]
      exact h1 F K ι G hGh hrel (n + 1) heq (Matrix.vecCons 0 L) 0 b₁ b₂
    · simp only [(h2 F K ι G).2 hGh (n + 1) _ hlt, add_zero]
  · have hz := (h3 F K ι G hGh).2 hrel
    simp only [intNum, eventualValue_of_eventually_zero _ (mixedDiff_eventually_zero _ hz _),
      add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

section Regrading

variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']

theorem weight_comp_addMonoidHom (φ : M →+ M') (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun v => φ (w v)) d = φ (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, map_finsuppSum, map_nsmul]

theorem weightedHomogeneousComponent_comp_addMonoidHom (φ : M →+ M') (hφ : Function.Injective φ)
    (w : σ → M) (b : M) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun v => φ (w v)) (φ b) f = weightedHomogeneousComponent w b f := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    weight_comp_addMonoidHom, hφ.eq_iff]

end Regrading

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]

def lexRelabel (e : K ≃ Fin (Fintype.card K)) : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun j => b (e.symm j))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lexRelabel_surjective (e : K ≃ Fin (Fintype.card K)) : Function.Surjective (lexRelabel e) :=
  fun i => ⟨fun k => ofLex i (e k), by
    change toLex (fun j => ofLex i (e (e.symm j))) = i
    simp only [Equiv.apply_symm_apply]
    rfl⟩

theorem lexRelabel_injective (e : K ≃ Fin (Fintype.card K)) : Function.Injective (lexRelabel e) := by
  intro a b h
  have h' : (fun j => a (e.symm j)) = fun j => b (e.symm j) := toLex.injective h
  funext k
  simpa using congrFun h' (e k)

variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]

theorem isHomogeneous_lex_of_isMultiHomogIdeal (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v));
    I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro i r hr
  change ((weightedDecomposition R (fun v => lexRelabel e (blockWeight ι v))).decompose' r i :
    MRing ι R) ∈ I
  rw [weightedDecomposition.decompose'_apply]
  obtain ⟨b, rfl⟩ := lexRelabel_surjective e i
  rw [weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact hI r hr b

theorem isMultiHomogIdeal_of_isHomogeneous_lex (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)}
    (hI : letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v));
      I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))) :
    IsMultiHomogIdeal I := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro f hf b
  rw [← weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact weightedHomogeneousComponent_mem_of_mem R _ hI hf _

end Lex

theorem MinimalPrimeMultiHomog.proof : MinimalPrimeMultiHomog.Statement := by
  intro R _ K _ _ ι J W hJ hW
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal.IsPrime := hWp.homogeneousCore
  have hJle : J ≤ (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) hW.1.2
  have hle : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal ≤ W := Ideal.toIdeal_homogeneousCore_le (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) W
  have heq : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal = W := le_antisymm hle (hW.2 ⟨hcore, hJle⟩ hle)
  apply isMultiHomogIdeal_of_isHomogeneous_lex e
  rw [← heq]
  exact (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).isHomogeneous

end GroundTheory.Heights₂.Heights.NumbersDVR
end

