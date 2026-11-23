module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_avoid_primes (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ W ∈ S, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W) (e₀ : K → ℕ) :
    ∃ (e : K → ℕ) (h : MRing ι R), IsMultiHomog h e ∧ e₀ ≤ e ∧ ∀ W ∈ S, h ∉ W := by
  classical
  set T := S.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := (S.finite_toSet).exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hW'.prop, fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hsep : ∀ W ∈ T, ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ W ∧
      ∀ W' ∈ T.erase W, a ∈ W' := by
    intro W hW
    have := (hS W (hTS W hW)).1
    refine exists_form_separator (T.erase W) fun W' hW' => ⟨(hS W' (hTS W' (Finset.mem_of_mem_erase hW'))).2.1,
      fun hle' => Finset.ne_of_mem_erase hW' ?_⟩
    exact (hTmax W' (Finset.mem_of_mem_erase hW') W (hTS W hW) hle').symm
  choose! a A haH haW haMem using hsep
  set e : K → ℕ := e₀ + ∑ W ∈ T, A W with he
  have hAe : ∀ W ∈ T, A W ≤ e := fun W hW =>
    le_add_left (Finset.single_le_sum (f := A) (fun _ _ => fun _ => Nat.zero_le _) hW)
  have hmon : ∀ W ∈ T, ∃ m : MRing ι R, IsMultiHomog m (e - A W) ∧ m ∉ W := by
    intro W hW
    have := (hS W (hTS W hW)).1
    exact exists_form_not_mem_of_isRelevant (hS W (hTS W hW)).2.2 _
  choose! m hmH hmW using hmon
  refine ⟨e, ∑ W ∈ T, a W * m W, ?_, le_self_add, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun W hW => ?_
    have := (haH W hW).mul (hmH W hW)
    rwa [add_tsub_cancel_of_le (hAe W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ hmem
      have hp := (hS W₀ (hTS W₀ hW₀)).1
      rw [← Finset.add_sum_erase _ _ hW₀] at hmem
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _ (haMem W (Finset.mem_of_mem_erase hW) W₀
          (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hW).symm, hW₀⟩))
      rcases hp.mem_or_mem ((Ideal.add_mem_iff_left _ hrest).mp hmem) with h2 | h2
      · exact haW W₀ hW₀ h2
      · exact hmW W₀ hW₀ h2
    intro W hW hmem
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' hmem)

end Avoid

theorem mem_minimalPrimes_sup_span_of_mem {A : Type*} [CommRing A] [IsNoetherianRing A] {P H : Ideal A}
    [hP : P.IsPrime] {x y : A} (hH : H ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hy : y ∉ P)
    (hyH : y ∈ H) : H ∈ (P ⊔ Ideal.span {y}).minimalPrimes := by
  have : H.IsPrime := hH.1.1
  have hPH : P ≤ H := le_sup_left.trans hH.1.2
  obtain ⟨Q, hQ, hQH⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPH ((Ideal.span_singleton_le_iff_mem _).mpr hyH))
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hyQ : y ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  suffices hQH' : Q = H by rw [← hQH']; exact hQ
  by_contra hne
  have hlt : Q < H := lt_of_le_of_ne hQH hne
  let φ := Ideal.Quotient.mk P
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hHm : (H.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hQm : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hcomap : ∀ I : Ideal A, P ≤ I → (I.map φ).comap φ = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]
  have h_lt : Q.map φ < H.map φ := (Ideal.map_mono hlt.le).lt_of_not_ge fun h => hlt.not_ge (by
    simpa only [hcomap Q hPQ, hcomap H hPH] using Ideal.comap_mono (f := φ) h)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hH
  have : (H.map φ).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h0' : Q.map φ ∈ (⊥ : Ideal (A ⧸ P)).minimalPrimes := h0
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h0'
  have : φ y ∈ Q.map φ := Ideal.mem_map_of_mem φ hyQ
  rw [show Q.map φ = ⊥ from h0', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact hy this

theorem relevant_minimal_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : divCycle P x W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

theorem AvoidingFormExists.proof : AvoidingFormExists.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD e₀
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hD1 := hD.1
  obtain ⟨bf, bg, hf, hg, -⟩ := hD1.degrees

  have hfin : ∀ x : MRing ι O, {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W}.Finite :=
    fun x => (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun W hW => hW.1
  have hmin : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c →
      ∀ W ∈ {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W},
        W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W := fun x c hx W hW =>
    ⟨hW.1.1.1, MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hx) hW.1, hW.2⟩
  obtain ⟨e, h, hh, he, hS⟩ := exists_form_avoid_primes
    (insert P ((hfin f).toFinset ∪ (hfin g).toFinset)) (by
      intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hPp, hP.multiProj.multiHomog, hP.multiProj.relevant⟩
      rcases Finset.mem_union.mp hW with hW | hW
      · exact hmin f bf hf W ((hfin f).mem_toFinset.mp hW)
      · exact hmin g bg hg W ((hfin g).mem_toFinset.mp hW)) e₀
  have hhP : h ∉ P := hS P (Finset.mem_insert_self _ _)
  have hhf : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hfin f).mem_toFinset.mpr ⟨hW, hr⟩)))
  have hhg : ∀ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hfin g).mem_toFinset.mpr ⟨hW, hr⟩)))

  have hG : ∀ G, ratDiv P f g G ≠ 0 → divCycle P h G = 0 := by
    intro G hG
    by_contra hhG
    have hhG' : h ∈ G := (relevant_minimal_of_divCycle_ne_zero hhG).1.1.2
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    by_cases hfG : divCycle P f G = 0
    · have hgG : divCycle P g G ≠ 0 := fun h0 => hG (by unfold ratDiv; rw [hfG, h0, sub_zero])
      obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hgG
      exact hhg G hm hr hhG'
    · obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hfG
      exact hhf G hm hr hhG'
  have hterm : ∀ s : MRing ι O, ∀ G, ratDiv P f g G ≠ 0 →
      divCycle P (s * h) G = divCycle P s G ∨ s ∈ P := by
    intro s G hr
    by_cases hsP : s ∈ P
    · exact Or.inr hsP
    · left
      rw [DivCycleMul.proof O K ι P s h hPp hsP hhP, Pi.add_apply, hG G hr, add_zero]
  refine ⟨e, h, hh, hhP, he, ?_, fun G _ hr => hG G hr, ?_, ?_⟩
  ·
    intro H hH _
    obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hH
    have : H.IsPrime := hm.1.1
    have hPH : P ≤ H := le_sup_left.trans hm.1.2
    have hhH : h ∈ H := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    refine IsVerticalDivisor.of_unit_off_special hD1.degrees
      (fun hfH => hhf H (mem_minimalPrimes_sup_span_of_mem hm hD1.num_not_mem hfH) hr hhH)
      (fun hgH => hhg H (mem_minimalPrimes_sup_span_of_mem hm hD1.den_not_mem hgH) hr hhH) (by
        intro W hW hHW hrW hϖW
        obtain ⟨u, v, hu, hv, huv⟩ := hD1.unit_off_special W hW (hPH.trans hHW) hrW hϖW
        exact ⟨u, v, hu, hv, hPH huv⟩)
  ·
    refine Nat.le_zero.mp (ciSup_le' fun G => ?_)
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · simp [hG G.1 hr]
  ·
    intro s hsP
    unfold commonExcess
    congr 1
    funext G
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · rcases hterm s G.1 hr with h1 | h1
      · rw [h1]
      · exact absurd h1 hsP

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u

section Statements

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable (Ω : Type*) [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def Ba.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' E'' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x E' E'' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E'' k L Q = ck O x d N E E' k L Q + ck O x d N E' E'' k L Q ∧
        ck O x d N E' E k L Q = -ck O x d N E E' k L Q

def Bb.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N N₁ N₂ : ℕ) (V V₁ V₂ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]
    (E E' : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsSubQuot O x E i p E₁ E₂ →
    IsSubQuot O x E' i p E₁' E₂' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q + ck O x d N₂ E₂ E₂' k L Q

def Bd.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (g : O), g ≠ 0 →
    IsModelOver O (mcIdeal O x) d →
    (∀ s, mseg x s ≠ 0 → ∀ v, v ∈ E'.lat s ↔ ∃ e ∈ E.lat s, v = algebraMap O Ω g • e) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g ∧
        ∀ (m n : ℕ) (h w : O), IsUnit w → 1 ≤ m → g ^ m = w * h ^ n →
          (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g =
            (n : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q h

end Statements

section FieldStatements

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def SegreFlagIndep.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric → ∀ (c n : ℕ) (Y : Fin n → K → ℤ),
      G.IsHomogeneous c → c + n = e →
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j))

end FieldStatements

section Inhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem sameGeneric_symm {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') : SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleSectionDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open Classical in
def FlagBundleSectionDiv.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N, 1 ≤ (i : ℕ) →
    ∀ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
      IsMultiHomog f bf → IsMultiHomog g bg →
      (fun o => (bf o : ℤ) - bg o) = zetaDeg + liftDeg (b i - a) →
      g ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) →
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g →
      ∀ W : Ideal (MRing (bundleIdx ι M) F),
        ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
          if W = projIdeal F y w φ (truncCoord t i) then 1 else 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagLineSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ h0 : 0 < N,
      ∃ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
        IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
        f ∉ projIdeal F y w φ (truncCoord t 1) ∧ g ∉ projIdeal F y w φ (truncCoord t 1) ∧
        (fun o => (bf o : ℤ) - bg o) = zetaDeg - liftDeg (a - b ⟨0, h0⟩) ∧
        ratDiv (projIdeal F y w φ (truncCoord t 1)) f g = 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHsymmShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def HsymmShift.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
    ∀ d : ℕ, FieldNumbers.relDim W = (d : WithBot (WithTop ℤ)) →
    ∀ (N : ℕ), 0 < N → ∀ (x : Fin N → K → ℤ) (s : K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
      r + Y.length = d →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (fun i => x i + s) α ++ Y) =
        ∑ k ∈ Finset.range (r + 1), ((N - 1 + r).choose k : ℤ) *
          ∑ α ∈ Finset.Nat.antidiagonalTuple N (r - k),
            intNumL F W (rootList x α ++ List.replicate k s ++ Y)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinPointIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointIdeal.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal R (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))) =
      (pointIdeal R y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def pairProjCoord (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ
  | ⟨none, l⟩ => ∑ i, t i * algebraMap Ω Φ (φ' l (e i))
  | ⟨some o, j⟩ => projCoord y e φ t ⟨o, j⟩

def zetaFirst (a : K → ℤ) : Option (Option K) → ℤ
  | none => 0
  | some none => 1
  | some (some k) => -a k

def zetaSecond (a : K → ℤ) : Option (Option K) → ℤ
  | none => 1
  | some none => 0
  | some (some k) => -a k

def liftPairDeg (L : K → ℤ) : Option (Option K) → ℤ
  | some (some k) => L k
  | _ => 0

def liftPairForm {R : Type*} [CommRing R] (M M' : ℕ) (f : MRing ι R) :
    MRing (bundleIdx (bundleIdx ι M) M') R :=
  rename (fun p : Σ k, ι k => (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)) f

end Objects

def zetaPowTimes (n m : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (1 + n)) ℤ :=
  X (Fin.castAdd n 0) ^ m * rename (Fin.natAdd 1) R

def GenericProjClosureModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ ∧ IsTwistedDualGens y B' a₀' φ' ∧
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) ∧
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

