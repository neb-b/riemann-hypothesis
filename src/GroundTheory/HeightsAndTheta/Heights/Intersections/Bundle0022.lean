module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalClosedPoints.proof (hE : regularityEmbedding_holds.Statement) (hV : VerticalEmbedding.Statement) : VerticalClosedPoints.Statement := by
  intro K _ ι _ P f g a R hP hf hg hfP hgP hR hRu
  have : P.IsPrime := hP.2.1.1
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hf hg hgP
  obtain ⟨e, he⟩ := hE K ι P R hP hR hRu
  rw [hV K ι P f g a x hP hf hg hfP hgP hx]
  have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) g :=
    ⟨a, fun _ => rfl, hg, hgP⟩
  have key : ∀ t : R, Real.log ‖e t x‖ =
      Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖) := by
    intro t
    have hg0 := eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)
    rw [← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ /
    ‖eval t (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalEmbedding.proof (hD : regularityDehomogenization_holds.Statement) (hC : regularityLocalCardinality_holds.Statement) (hL : RegularityLocalProduct.Statement) :
    VerticalEmbedding.Statement := by
  classical
  intro K _ ι _ P f g a x hP hf hg hfP hgP hx
  have : P.IsPrime := hP.2.1.1

  let t : Ideal (MRing ι) → MRing ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1
  have ht : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → IsMultiHomog (t W) a ∧ t W ∉ W := by
    intro W hWp hW
    simp only [t, dif_pos hW]
    refine ⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩
    obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp hmem
    exact (hW k).choose_spec (hWp.mem_of_pow_mem _ hk)
  have hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0 := by
    intro W hPW htW h0
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact htW (hPW h0)

  let y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P) := fun s W =>
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) /
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))
  have hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧
      ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s') := by
    intro s W hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    obtain ⟨h1, h2⟩ := ht W hW.1.1.1 hW.2
    exact ⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩

  have term : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
          (if IsHorizontal W then 0 else
            (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → HermLine ι) j).a) : ℝ) * Real.log (charOf W)) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP W hW
    have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) s :=
      ⟨a, fun _ => rfl, hs, hsP⟩
    rw [if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]
    obtain ⟨-, -, hta, htW, hy⟩ := hdata s W hW
    obtain ⟨hyW, hm⟩ := hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)
    have hy0 : y s W ≠ 0 := by
      intro h0
      have h1 := hy s
      rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact hsP h1
    rw [hm]
    exact hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0
  have hvert : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P →
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s =
        ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP
    unfold vertR
    exact finsum_mem_congr rfl fun W hW => term s hs hsP W hW
  rw [hvert f hf hfP, hvert g hg hgP]
  refine hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_
  obtain ⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by
    rcases hW with hW | hW
    · exact hdata f W hW
    · exact hdata g W hW
  exact ⟨hta, htW, hy f, hy g⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherBis
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def IntersectionWithSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsSectionOn (imageZ v P') A s →
    ptsIntegral P' (pot L') (logNorm A' (rename v s)) =
      (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ptsIntegral (imageZ v P') (pot L) (logNorm A s)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℤ) (y : funField P),
    IsArithVar P 1 → Prime p →
    (∀ W, IsClosedPt W → P ≤ W → C p ∈ W → (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    ∃ n : ℤ, ¬ p ∣ n ∧ (n : funField P) * y ∈ regRing P

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : regRing P),
    IsArithVar P 1 → b ≠ 0 →
    {W | IsClosedPt W ∧ P ≤ W ∧
        Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P))) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P)))) =
        Real.log (Nat.card (regRing P ⧸ Ideal.span {b}))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSurjective.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ m : Ideal (regRing P), m.IsMaximal →
    ∃ W : Ideal (MRing ι), IsClosedPt W ∧ P ≤ W ∧ ∀ x ∈ m, ∀ z ∈ locRing P W,
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z ≠ 1

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSpectrum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ e : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} ≃ MaximalSpectrum (regRing P),
      ∀ (W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}) (y : FractionRing (MRing ι ⧸ P)),
        y ∈ locRing P W.1 ↔ ∃ x s : regRing P, s ∉ (e W).asIdeal ∧
          y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ x : regRing P, IsIntegral ℤ ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PushforwardArithIntersection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1


open Classical in
theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp


omit [Fintype K] in
open Classical in
theorem sum_single_eq_extend {K₀ : Type} [Fintype K₀] (κ : K₀ → K) (hκ : Function.Injective κ) (α : K₀ → ℕ) :
    (∑ k, α k • (Pi.single (κ k) 1 : K → ℕ)) = Function.extend κ α 0 := by
  funext k'
  rw [Finset.sum_apply]
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hκ.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hκ.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : k' ≠ κ k := fun e => h ⟨k, e.symm⟩
    simp [hk]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem wh_prod_X_pow {K₀ : Type} [Fintype K₀] (q : K₀ → Σ k, ι k) (α : K₀ → ℕ) :
    IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X (q k) : MRing ι) ^ α k) (∑ k, α k • blkW (q k)) :=
  IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ (q k)).pow (α k)

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h := wh_prod_X_pow (ι := ι) (fun k => ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h


omit [∀ k, Fintype (ι k)] in
theorem isMultiHomog_rename_coordPow {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)) (Function.extend κ α 0) := by
  have h := wh_prod_X_pow (ι := ι') (fun k => v ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι') (v ⟨k, i k⟩)) = Function.extend κ α 0 := by
    simp only [blkW, hv.2.2.1]
    exact sum_single_eq_extend κ hv.1 α
  rw [e] at h
  simp only [map_prod, map_pow, rename_X]
  exact isMultiHomog_of_wh h


omit [∀ k, Fintype (ι k)] in
theorem coordPow_not_mem {V : Ideal (MRing ι)} (hV : V.IsPrime) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ V) (α : K → ℕ) : (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hi k (hV.mem_of_pow_mem _ hk)

theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem genDegAt_zero (h0 : ArithVarZeroStatement) (I : AllFam) : GenDegAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' _ hP'
  exact absurd hP' (h0 K' ι' P')

theorem genDegAt_succ (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement)
    (I : AllFam) (hI : I.IsFamily) (n : ℕ) (ih : GenDegAt I n) : GenDegAt I (n + 1) := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' hv hP' hP hJ hL hLL'
  have hrel := hP.2.1.2.2
  choose i hi using hrel
  have hPp : (imageZ v P').IsPrime := hP.2.1.1
  let α : K → ℕ := fun k => ((L (Fin.last n)).a k).toNat
  let β : K → ℕ := fun k => (-(L (Fin.last n)).a k).toNat
  have hfP := coordPow_not_mem hPp i hi α
  have hgP := coordPow_not_mem hPp i hi β
  have hfP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ P' := fun h => hfP (Ideal.mem_comap.mpr h)
  have hgP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) ∉ P' := fun h => hgP (Ideal.mem_comap.mpr h)
  have hsec : IsRatSectionOn (imageZ v P') (L (Fin.last n)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) :=
    ⟨α, β, isMultiHomog_coordPow i α, isMultiHomog_coordPow i β, hfP, hgP,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hsec' : IsRatSectionOn P' (L' (Fin.last n)) (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k))
      (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k)) := by
    refine ⟨_, _, isMultiHomog_rename_coordPow hv i α, isMultiHomog_rename_coordPow hv i β, hfP', hgP',
      fun k' => ?_⟩
    rw [(hLL' (Fin.last n)).1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply]
      exact Int.toNat_sub_toNat_neg _
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have e1 := hRat K' ι' (I K' ι') (hI K' ι') P' n (Fin.init L') (L' (Fin.last n)) _ _ hP'
    (fun j => hL' _) (hL' _) hsec'
  have e2 := hRat K ι (I K ι) (hI K ι) (imageZ v P') n (Fin.init L) (L (Fin.last n)) _ _ hP
    (fun j => hL _) (hL _) hsec
  rw [Fin.snoc_init_self] at e1 e2
  rw [e1, e2, recRRat, recRRat,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ α hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i α) hfP,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ β hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i β) hgP,
    hInt K ι K' ι' κ v P' n G J (Fin.init L) (Fin.init L') (L (Fin.last n)) (L' (Fin.last n)) _ _ hv hP' hP
      hJ (fun j => hL _) (fun j => hLL' _) (hL _) (hLL' _) hsec]
  ring

end PushforwardArithIntersection

theorem PushforwardArithIntersection.proof (h0 : ArithVarZeroStatement) (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement)
    (hInt : ArithmeticIntersectionIntegral.Statement) : PushforwardArithIntersection.Statement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  have key : ∀ n, GenDegAt I n := fun n =>
    Nat.rec (PushforwardArithIntersection.genDegAt_zero h0 I) (fun n ih => PushforwardArithIntersection.genDegAt_succ hRat hCyc hInt I hI n ih) n
  exact key d K ι K' ι' κ v P' G J L L' hv hP' hP hJ hL hLL'

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagArith
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Flag

variable {K : Type} {ι : K → Type}

end Flag

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

