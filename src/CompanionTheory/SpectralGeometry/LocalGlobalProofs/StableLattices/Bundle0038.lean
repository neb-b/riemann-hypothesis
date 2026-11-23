module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantOfKHighest
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg

open Finset
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

lemma kRel_of_glRel {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) : CompanionTheory.D.DSIC.KRel ε E :=
  fun a b c d _ _ => hE a b c d

lemma kUnit_of_isUnitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) : CompanionTheory.D.DSIC.KUnit ε E := by
  intro a b he x y
  rw [hU a b x y]
  simp [Formalism.REAL.sgn, he]

lemma dominant_of_kHighest {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hF : CompanionTheory.D.DSIC.KRel ε E) (hU : CompanionTheory.D.DSIC.KUnit ε E)
    {μ : Fin n → ℝ} {u : V} (hu : u ≠ 0) (hh : KHighest ε E μ u) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    μ b ≤ μ a := by
  have h := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity hF hU he hh.1
  rw [hh.2 a b hab he, norm_zero] at h
  have hp : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu; positivity
  by_contra hc
  push Not at hc
  have : 0 < (μ b - μ a) * ‖u‖ ^ 2 := mul_pos (by linarith) hp
  have := sq_nonneg ‖E b a u‖
  nlinarith

lemma two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, ((2 : ℝ) • rhoC ε) a = m := by
  refine ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  simp only [Pi.smul_apply, rhoC, smul_eq_mul]
  push_cast
  ring

lemma vNormSq_nat (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : ∀ a, ∃ m : ℤ, μ a = m) :
    ∃ k : ℕ, vNormSq ε μ = k := by
  choose m hm using hμ
  choose r hr using two_rhoC_int ε
  refine ⟨∑ a, ((m a + r a) ^ 2).toNat, ?_⟩
  have h : ∀ a, (((m a + r a) ^ 2).toNat : ℝ) = (μ a + ((2 : ℝ) • rhoC ε) a) ^ 2 := by
    intro a
    have h0 : (((m a + r a) ^ 2).toNat : ℤ) = (m a + r a) ^ 2 := Int.toNat_of_nonneg (sq_nonneg _)
    have h1 : (((m a + r a) ^ 2).toNat : ℝ) = (((m a + r a) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1, hm a, hr a]
    push_cast
    ring
  rw [Nat.cast_sum]
  simp only [vNormSq, PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [h a, sq]

theorem lktExists : LKTExists := by
  classical
  intro n ε V _ _ E hE hV hU hfin hint
  have hF : CompanionTheory.D.DSIC.KRel ε E := kRel_of_glRel hE
  have hK : CompanionTheory.D.DSIC.KUnit ε E := kUnit_of_isUnitary hU
  have hintK : ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → ∀ a, ∃ m : ℤ, μ a = m :=
    fun μ x hx hh => hint μ x hx hh.1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨S, hfd, hS, hxS⟩ := hfin x
  obtain ⟨y, -, hy0, ν, hy⟩ := Formalism.REAL.highestWeightExists_holds V n ε E S hfd hF hK hS
    (fun h => hx (by simpa [h] using hxS))
  have hex : ∃ k : ℕ, ∃ (μ : Fin n → ℝ) (w : V), w ≠ 0 ∧ KHighest ε E μ w ∧ vNormSq ε μ = k := by
    obtain ⟨k, hk⟩ := vNormSq_nat ε (hintK ν y hy0 hy)
    exact ⟨k, ν, y, hy0, hy, hk⟩
  obtain ⟨γ, u, hu, hγ, hk⟩ := Nat.find_spec hex
  refine ⟨γ, u, hu, hγ, ?_, hintK γ u hu hγ, fun a b hab he => dominant_of_kHighest hF hK hu hγ hab he⟩
  intro μ w hw hμ
  obtain ⟨k, hk'⟩ := vNormSq_nat ε (hintK μ w hw hμ)
  rw [hk, hk']
  exact_mod_cast Nat.find_min' hex ⟨μ, w, hw, hμ, hk'⟩

end GlobalTheory.CompanionTheory.RgExhFarReg
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationList
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgClusterOrder

def rootHt {n : ℕ} (i : Pos n) : ℕ := (i.1.2 : ℕ) - (i.1.1 : ℕ)

theorem exists_sorted_list {α : Type} (S : Finset α) (h : α → ℕ) :
    ∃ l : List α, l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ S) ∧ l.Pairwise (fun a b => h a ≤ h b) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S h hne
      obtain ⟨l, hnd, hmem, hs⟩ := ih (S.erase m) (Finset.erase_ssubset hm)
      refine ⟨m :: l, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, hnd⟩
        intro hml
        exact (Finset.mem_erase.1 ((hmem m).1 hml)).1 rfl
      · intro i
        rw [List.mem_cons, hmem, Finset.mem_erase]
        constructor
        · rintro (rfl | hi)
          · exact hm
          · exact hi.2
        · intro hi
          by_cases him : i = m
          · exact Or.inl him
          · exact Or.inr ⟨him, hi⟩
      · refine List.pairwise_cons.2 ⟨?_, hs⟩
        intro b hb
        exact hmin b (Finset.mem_of_mem_erase ((hmem b).1 hb))

theorem adC_ne_zero_cases {n : ℕ} {p q : Fin n} {i k : Pos n} (h : adC p q i k ≠ 0) :
    (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
  by_contra hc
  rw [not_or] at hc
  exact h (by simp only [adC, if_neg hc.1, if_neg hc.2, sub_self])

theorem mem_inside_iff {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} (hlev : Monotone lev) (i : Pos n) :
    i ∈ om ε ∧ i ∉ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 = lev i.1.2 := by
  have hle : lev i.1.1 ≤ lev i.1.2 := hlev (le_of_lt i.2)
  simp only [CompanionTheory.D.LK.om, omU, Finset.mem_filter, Finset.mem_univ, true_and, cpt, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_antisymm hle (not_lt.1 (h2 h1))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => by omega⟩

theorem exists_inside_order : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  intro n ε lev hlev
  classical
  obtain ⟨l, hnd, hmem, hs⟩ := exists_sorted_list ((om ε).filter (· ∉ omU ε lev)) (rootHt (n := n))
  have hmem' : ∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev := fun i => by
    rw [hmem, Finset.mem_filter]
  refine ⟨l, hnd, hmem', ?_⟩
  intro pre f post hl e he k hk
  have hfl : f ∈ l := by simp [hl]
  obtain ⟨he1, he2⟩ := (mem_inside_iff hlev e).1 ((hmem' e).1 he)
  obtain ⟨hf1, hf2⟩ := (mem_inside_iff hlev f).1 ((hmem' f).1 hfl)
  have he0 : (e.1.1 : ℕ) < e.1.2 := e.2
  have hf0 : (f.1.1 : ℕ) < f.1.2 := f.2

  have hkey : (ε k.1.1 = ε k.1.2 ∧ lev k.1.1 = lev k.1.2) ∧ rootHt f < rootHt k := by
    rcases adC_ne_zero_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [← h1] at hf1 hf2 ⊢
        exact he1.trans hf1
      · simp only [← h1] at hf1 hf2 ⊢
        exact he2.trans hf2
      · have : (e.1.2 : ℕ) = f.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [h1] at hf1 hf2 ⊢
        exact hf1.trans he1
      · simp only [h1] at hf1 hf2 ⊢
        exact hf2.trans he2
      · have : (f.1.2 : ℕ) = e.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
  have hkl : k ∈ l := (hmem' k).2 ((mem_inside_iff hlev k).2 hkey.1)
  rw [hl] at hkl hs
  rcases List.mem_append.1 hkl with hpre | hrest
  · have := (List.pairwise_append.1 hs).2.2 k hpre f (by simp)
    omega
  · rcases List.mem_cons.1 hrest with rfl | hpost
    · exact absurd hkey.2 (lt_irrefl _)
    · exact hpost

end GlobalTheory.CompanionTheory.RgClusterOrder
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimInvariantSubspaceAdjointPair
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FarReg

theorem highest_preimage_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (T : Submodule ℂ E) (a b : ι → Module.End ℂ E) (D : Module.End ℂ E) (y : E)
    (hT : FiniteDimensional ℂ T)
    (hadj : ∀ i x z, ⟪a i x, z⟫_ℂ = ⟪x, b i z⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) :
    ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  classical
  let S : Submodule ℂ E := Submodule.span ℂ {z | ∃ i, ∃ t ∈ T, z = b i t}
  have hST : S ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, t, ht, rfl⟩
    exact hbT i t ht
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hST
  obtain ⟨u, huS, w, hw, hyuw⟩ := S.exists_add_mem_mem_orthogonal y
  have hbS : ∀ i, ∀ t ∈ T, b i t ∈ S := fun i t ht => Submodule.subset_span ⟨i, t, ht, rfl⟩
  have huT : u ∈ T := hST huS
  have hwT : w ∈ T := by
    have : w = y - u := by rw [hyuw]; abel
    rw [this]
    exact T.sub_mem hy huT
  have haw : ∀ i, a i w = 0 := by
    intro i
    have h0 : ⟪a i w, a i w⟫_ℂ = 0 := by
      rw [hadj]
      exact (Submodule.mem_orthogonal' S w).1 hw _ (hbS i _ (haT i w hwT))
    exact inner_self_eq_zero.1 h0
  have har : ∀ i, a i (D u) = 0 := by
    intro i
    have h1 : a i (D y) = a i (D u) + D (a i w) := by
      rw [← haD i w hwT, ← map_add (f := _), ← map_add (f := _), hyuw]
    rw [hDy i, haw i, map_zero, add_zero] at h1
    exact h1.symm
  have hperp : ∀ z ∈ S, ⟪D u, D z⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, t, ht, rfl⟩ := hz
      rw [← hbD i t ht, ← hadj, har i, inner_zero_left]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add (f := _), inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [map_smul, inner_smul_right, hx, mul_zero]
  have hDu : D u = 0 := inner_self_eq_zero.1 (hperp u huS)
  exact ⟨w, hwT, haw, by rw [hyuw, map_add (f := _), hDu, zero_add]⟩

theorem highest_preimage_of_stable : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ι : Type) (T : Submodule ℂ (Cn n V))
    (a b : ι → Module.End ℂ (Cn n V)) (D : Module.End ℂ (Cn n V)) (y : Cn n V), FiniteDimensional ℂ T →
    (∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ) →
    (∀ i, ∀ t ∈ T, a i t ∈ T) → (∀ i, ∀ t ∈ T, b i t ∈ T) →
    (∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) → (∀ i, ∀ t ∈ T, b i (D t) = D (b i t)) →
    y ∈ T → (∀ i, a i (D y) = 0) → ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  intro n V _ _ ι T a b D y hT hadj haT hbT haD hbD hy hDy
  let e : Cn n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Pos n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Pos n) → V)).symm
  let c : Module.End ℂ (Cn n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Pos n) => V)) := fun f =>
    (e : Cn n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cn n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

end GlobalTheory.CompanionTheory.FarReg
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightVectorKilledByRaising
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExh

theorem adC_mem_omU {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hε : ε p = ε q)
    (hl : lev p = lev q) {i k : Pos n} (hc : adC p q i k ≠ 0) (hi : i ∈ omU ε lev) :
    k ∈ omU ε lev ∧ k ≠ i := by
  have hcase : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adC, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := (mem_filter.1 hi).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε p = ε i.1.2; rw [hε, e1, h1]
    · rw [e2]; show lev p < lev i.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε i.1.1 = ε q; rw [h1, e1, hε]
    · rw [e2]; show lev i.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem lF_single_omU : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), KHighest ε E γ u →
    ∀ p q : Fin n, p < q → ε p = ε q → lev p = lev q →
      lF E p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
  intro n ε lev V _ _ E γ u hu p q hpq hε hl
  have hE : E p q u = 0 := hu.2 p q hpq hε
  have h1 : lift n (E p q) (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    funext A
    rw [CompanionTheory.D.LK.lift_apply]
    by_cases e : A = omU ε lev
    · subst e
      rw [Pi.single_eq_same]
      exact hE
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adL p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hc : adC p q i k = 0
    · rw [hc, zero_smul]
    suffices h : cre k (ann i (Pi.single (omU ε lev) u : Cn n V)) = 0 by rw [h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := CompanionTheory.D.LK.cre_ne h
    obtain ⟨-, h4⟩ := CompanionTheory.D.LK.ann_ne h3
    have e : insert i (B.erase k) = omU ε lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hi : i ∈ omU ε lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hki⟩ := adC_mem_omU hpq hε hl hc hi
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hki h5
    · exact notMem_erase _ _ h5
  show lift n (E p q) _ + adL p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.RgExh
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLevi
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.FarReg.BdProd

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_sq (k : Pos n) : (cre k * cre k : Module.End ℂ (Cn n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply, CompanionTheory.D.LK.Car.cre_apply]
  by_cases h : k ∈ A <;> simp [h]

theorem cre_anti (i j : Pos n) : (cre i * cre j : Module.End ℂ (Cn n V)) = -(cre j * cre i) :=
  eq_neg_of_add_eq_zero_left (CompanionTheory.D.LK.Car.cre_cre i j)

theorem cre_mul_prod_of_mem {k : Pos n} {l : List (Pos n)} (h : k ∈ l) :
    (cre k * (l.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
  induction l with
  | nil => simp at h
  | cons g t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hk : k = g
    · subst hk
      rw [← mul_assoc, cre_sq, zero_mul]
    · have h1 := ih ((List.mem_cons.1 h).resolve_left hk)
      rw [← mul_assoc, cre_anti, neg_mul, mul_assoc, h1, mul_zero, neg_zero]

theorem term_comm (k i g : Pos n) :
    (cre k * ann i * cre g - cre g * (cre k * ann i) : Module.End ℂ (Cn n V)) = if i = g then cre k else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) i g
  rw [mul_assoc, eq_sub_of_add_eq h1, mul_sub, ← mul_assoc (cre k) (cre g), cre_anti k g, neg_mul, mul_assoc (cre g),
    sub_neg_eq_add, add_sub_cancel_right]
  split_ifs <;> simp

theorem adL_cre (p q : Fin n) (g : Pos n) :
    (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) = ∑ k : Pos n, adC p q g k • cre k := by
  have h : (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (cre k * ann i * cre g - cre g * (cre k * ann i)) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm]
  rw [Finset.sum_eq_single g]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem lF_cre (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (g : Pos n) :
    (lF E p q * cre g : Module.End ℂ (Cn n V)) = cre g * lF E p q + ∑ k : Pos n, adC p q g k • cre k := by
  have h1 : (lift n (E p q) * cre g : Module.End ℂ (Cn n V)) = cre g * lift n (E p q) :=
    LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre (E p q) g x
  rw [← adL_cre, lF, add_mul, mul_add, h1]
  abel

theorem lF_prod (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : List (Pos n))
    (h : ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ k : Pos n,
      adC p q f k ≠ 0 → k ∈ post) :
    (lF E p q * (l.map cre).prod : Module.End ℂ (Cn n V)) = (l.map cre).prod * lF E p q := by
  induction l with
  | nil => simp
  | cons g t ih =>
    have ht := ih fun pre f post e k hk => h (g :: pre) f post (by rw [e]; rfl) k hk
    have hz : ((∑ k : Pos n, adC p q g k • cre k) * (t.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : adC p q g k = 0
      · rw [hk, zero_smul, zero_mul]
      · rw [smul_mul_assoc, cre_mul_prod_of_mem (h [] g t rfl k hk), smul_zero]
    rw [List.map_cons, List.prod_cons, ← mul_assoc, lF_cre, add_mul, hz, add_zero, mul_assoc, ht, mul_assoc]

theorem bd_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  intro n V _ _ E hC l x
  induction l with
  | nil => intro _ _; simp
  | cons f t ih =>
    intro hcl hx
    have ih' := ih (fun pre g post e a ha k hk =>
      hcl (f :: pre) g post (by rw [e]; rfl) a (List.mem_cons_of_mem _ ha) k hk)
      (fun e he => hx e (List.mem_cons_of_mem _ he))
    have hf : lF E f.1.1 f.1.2 (((t.map cre).prod : Module.End ℂ (Cn n V)) x) = 0 := by
      have h1 := lF_prod E f.1.1 f.1.2 t (fun pre g post e k hk =>
        hcl (f :: pre) g post (by rw [e]; rfl) f List.mem_cons_self k hk)
      have h2 := LinearMap.congr_fun h1 x
      simp only [Module.End.mul_apply] at h2
      rw [h2, hx f List.mem_cons_self, map_zero]
    have h3 := LinearMap.congr_fun (hC f) (((t.map cre).prod : Module.End ℂ (Cn n V)) x)
    simp only [LinearMap.add_apply, Module.End.mul_apply, hf, ih'] at h3
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, map_smul]
    rw [eq_neg_of_add_eq_zero_left h3, mul_neg_one, neg_smul, map_smul]

end GlobalTheory.CompanionTheory.FarReg.BdProd
end
end

