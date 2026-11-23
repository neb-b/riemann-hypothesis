module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


variable (ι) in
abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)

def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a

def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)



end Objects

def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)

section Inhabitants

abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n

abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩

theorem isArithVar_bot (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [Nat.card_eq_fintype_card]
    exact add_comm _ _

theorem isMultiHomog_Xb (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by
  intro m hm k
  rw [support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def locRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    v ∉ W ∧ IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

def locIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)) : Ideal (locRing P W) :=
  Ideal.span {z | (z : FractionRing (MRing ι ⧸ P)) = y}

theorem locIdeal_eq_span {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) :
    locIdeal P W y = Ideal.span {(⟨y, hy⟩ : locRing P W)} := by
  unfold locIdeal
  congr 1
  ext z
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsSemiPosHerm (M : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ v : (Σ k, ι k) → ℂ,
    0 ≤ Δ (fun t : ℂ => Real.log (M.h (z + t • v))) 0

def De (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι) : ℝ :=
  ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s)) -
    ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s'))

theorem De_swap (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by
  unfold De
  ring

end Objects

def DeSlotAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (j : Fin n) (M N A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ i, IsSmoothHerm (L i)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P (Function.update L j (M.tensor N)) A A' s s' =
      De P (Function.update L j M) A A' s s' + De P (Function.update L j N) A A' s s'

def SemiPosTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (M : HermLine ι),
    IsSmoothHerm M → ∃ T : HermLine ι, IsSmoothHerm T ∧ IsSemiPosHerm T ∧ IsSemiPosHerm (M.tensor T)

def DeLeSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSemiPosHerm (L j)) →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P L A A' s s' ≤ 0

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace ThmIMultilin

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_update {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ i, IsSmoothHerm (L i)) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : ∀ i, IsSmoothHerm (Function.update L j X i) := by
  intro i
  by_cases h : i = j
  · subst h
    simpa using hX
  · simpa [Function.update_of_ne h] using hL i


omit [∀ k, Fintype (ι k)] in
theorem update_comp_swap {m : ℕ} (L : Fin (m + 1) → HermLine ι) (j : Fin (m + 1)) (X : HermLine ι) :
    Function.update L j X ∘ Equiv.swap j (Fin.last m) =
      Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · have hne : Equiv.swap j (Fin.last m) i.castSucc ≠ j := by
      intro h
      have h' : Equiv.swap j (Fin.last m) i.castSucc = Equiv.swap j (Fin.last m) (Fin.last m) := by
        rw [h, Equiv.swap_apply_right]
      exact Fin.castSucc_ne_last i ((Equiv.swap j (Fin.last m)).injective h')
    simp [Function.update_of_ne hne]

end ThmIMultilin

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PWellDefined
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem divSupp_disjoint_of_not_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {u a : MRing ι} (h : ∀ W ∈ divSupp P u, a ∉ W) :
    ∀ W, W ∈ divSupp P u → W ∉ divSupp P a :=
  fun W hW hW' => h W hW (hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem isMultiProjPrime_of_mem_divSupp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) {u : MRing ι} {b : K → ℕ} (hu : IsMultiHomog u b)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P u) : IsMultiProjPrime W :=
  ⟨hW.1.isPrime, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hu hW.1, hW.2⟩

theorem WellDefined.proof (h₁ : Swap.Statement) (h₂ : RPositionAdd.Statement) :
    WellDefined.Statement := by
  intro K _ ι _ I P n L B s t hR hA hP hL hB hs ht
  classical
  obtain ⟨bs, hbs, hsH, hsP⟩ := hs
  obtain ⟨bt, hbt, htH, htP⟩ := ht
  have hPm : IsMultiProjPrime P := hP.2.1
  set S : Set (Ideal (MRing ι)) := divSupp P s ∪ divSupp P t ∪ {P} with hSdef
  have hSf : S.Finite :=
    ((divSupp_finite P s).union (divSupp_finite P t)).union (Set.finite_singleton P)
  have hS' : ∀ W ∈ S, IsMultiProjPrime W := by
    rintro W ((hW | hW) | hW)
    · exact isMultiProjPrime_of_mem_divSupp hPm hsH hW
    · exact isMultiProjPrime_of_mem_divSupp hPm htH hW
    · rw [Set.mem_singleton_iff.mp hW]
      exact hPm
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSf hS'
  set M := L (Fin.last n) with hM
  set k : ℕ := ∑ l, (d₀ l + (M.a l).natAbs) with hkdef
  have hk1 : ∀ l, d₀ l + (M.a l).natAbs ≤ k := fun l =>
    Finset.single_le_sum (f := fun l => d₀ l + (M.a l).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l)
  set b : K → ℕ := fun l => (M.a l + k).toNat with hbdef
  have hb : ∀ l, (b l : ℤ) = M.a l + k := fun l =>
    Int.toNat_of_nonneg (by have := hk1 l; omega)
  have hbd : d₀ ≤ b := fun l => by
    have h1 := hk1 l
    have h2 := hb l
    show d₀ l ≤ b l
    omega
  have hkd : d₀ ≤ fun _ => k := fun l => by
    have := hk1 l
    show d₀ l ≤ k
    omega
  obtain ⟨a1, ha1H, ha1S⟩ := hd₀ b hbd
  obtain ⟨a2, ha2H, ha2S⟩ := hd₀ _ hkd
  set H : HermLine ι := HermLine.sqMetric (fun _ => k) with hH
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric _
  have hMs : IsSmoothHerm M := hL _
  have hA1s : IsSmoothHerm (M.tensor H) := isSmoothHerm_tensor hMs hHs
  have hL' : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
  have hPS : P ∈ S := Or.inr rfl
  have hsec1 : IsSectionOn P (M.tensor H) a1 :=
    ⟨b, fun l => by rw [hb l]; rfl, ha1H, ha1S P hPS⟩
  have hsec2 : IsSectionOn P H a2 := ⟨fun _ => k, fun l => rfl, ha2H, ha2S P hPS⟩
  have hsecs : IsSectionOn P B s := ⟨bs, hbs, hsH, hsP⟩
  have hsect : IsSectionOn P B t := ⟨bt, hbt, htH, htP⟩
  have d1s := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inl hW))
  have d1t := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inr hW))
  have d2s := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inl hW))
  have d2t := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inr hW))
  have e1s := h₁ K ι I P n (Fin.init L) B (M.tensor H) s a1 hR hP hL' hB hA1s hsecs hsec1 d1s
  have e1t := h₁ K ι I P n (Fin.init L) B (M.tensor H) t a1 hR hP hL' hB hA1s hsect hsec1 d1t
  have e2s := h₁ K ι I P n (Fin.init L) B H s a2 hR hP hL' hB hHs hsecs hsec2 d2s
  have e2t := h₁ K ι I P n (Fin.init L) B H t a2 hR hP hL' hB hHs hsect hsec2 d2t
  have fs := h₂ K ι I P n (Fin.init L) M H B s hA hP hL' hMs hHs hB hsecs
  have ft := h₂ K ι I P n (Fin.init L) M H B t hA hP hL' hMs hHs hB hsect
  have hLeq : L = Fin.snoc (Fin.init L) M := (Fin.snoc_init_self L).symm
  rw [hLeq]
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
end

