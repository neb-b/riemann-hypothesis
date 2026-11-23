module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLinearQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityPointsSum_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    ∃ R : Finset ((Σ k, ι k) → ℂ), (∀ t ∈ R, t ∈ mcPts P) ∧
      (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) ∧
      ∀ h : ((Σ k, ι k) → ℂ) → ℝ,
        (∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') →
        ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h = ∑ t ∈ R, h t

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHomogeneousOfIsMultiHomogOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section Helpers

variable {F : Type} [Field F]

theorem linearForm_fin_one_eq {g : MvPolynomial (Fin 1) F} (hg : g.IsHomogeneous 1) :
    g = C (AddMonoidAlgebra.coeff g (Finsupp.single 0 1)) * X 0 := by
  ext d
  rw [coeff_C_mul, coeff_X]
  by_cases h : Finsupp.single 0 1 = d
  · subst h
    simp
  · rw [if_neg h, mul_zero]
    by_contra hne
    apply h
    have hw := hg hne
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Finsupp.weight_apply, Finsupp.sum_fintype] at hw ⊢
    omega

theorem isHomogeneous_of_isMultiHomog_one {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type}
    [∀ k, Fintype (ι₀ k)] (hK : Fintype.card K₀ = 1) {f : MRingOver F ι₀}
    (hf : IsMultiHomog f fun _ => 1) : f.IsHomogeneous 1 := by
  intro d hd
  have h := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  simp [h, hK]

end Helpers

theorem LineFibreBlocks.proof (hLin : LinearQuotient.Statement) : LineFibreBlocks.Statement := by
  intro F _ K₀ _ ι₀ _ k₀ Q J hk hQ ⟨S, hS, hQS⟩ hJ m
  classical
  have hK : Fintype.card K₀ = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hk⟩
  have hQp : Q.IsPrime := hQ.1.1
  obtain ⟨i₀, hi₀⟩ := hQ.1.2.2 k₀
  set ℓ : MRingOver F ι₀ := X ⟨k₀, i₀⟩ with hℓdef
  obtain ⟨r, φ, hφs, hφk, hφX⟩ := hLin F (Σ k, ι₀ k) (insert ℓ S) (by
    rintro f (rfl | hf)
    · exact isHomogeneous_X F _
    · exact isHomogeneous_of_isMultiHomog_one hK (hS f hf))
  set W : Ideal (MRingOver F ι₀) := RingHom.ker φ with hWdef
  have hQW : Q ⊔ Ideal.span {ℓ} = W := by
    rw [hφk, Ideal.span_insert, hQS, sup_comm]
  have hWp : W.IsPrime := RingHom.ker_isPrime φ
  have hWmin : W ∈ (Q ⊔ Ideal.span {ℓ}).minimalPrimes := by
    rw [hQW, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have hdim := cyc_dim_quot_minimal_add_one hi₀ hWmin (fun h => by
    rw [hQ.2] at h
    exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  have hdimW : ringKrullDim (MRingOver F ι₀ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) :=
    cyc_withBot_eq_of_add_one (by rw [hdim, hQ.2, hK])
  rw [hWdef, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hφs).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at hdimW
  have hr : r = 1 := by
    have h : ENat.card (Fin r) = (1 : ℕ∞) := WithBot.coe_injective hdimW
    rw [ENat.card_eq_coe_natCard] at h
    have h2 : Nat.card (Fin r) = 1 := by exact_mod_cast h
    simpa using h2
  subst hr

  have hex : ∃ s, (X s : MRingOver F ι₀) ∉ W := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    have hφ0 : φ = (Algebra.ofId F _).comp (aeval fun _ => (0 : F)) := by
      apply MvPolynomial.algHom_ext
      intro s
      have h0 := hno s
      rw [hWdef, RingHom.mem_ker] at h0
      simp [h0]
    obtain ⟨f, hf⟩ := hφs (X 0)
    rw [hφ0] at hf
    have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single 0 1)) hf
    simp [Algebra.ofId_apply, coeff_X, algebraMap_eq, coeff_C] at this
    rw [if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm] at this
    exact zero_ne_one this
  obtain ⟨s₁, hs₁⟩ := hex
  have hWrel : IsRelevant W := fun k => by
    obtain rfl : k = s₁.1 := (hk k).trans (hk s₁.1).symm
    exact ⟨s₁.2, hs₁⟩

  have hdivℓ : divCycle Q ℓ = Finsupp.single W 1 := inh_divCycle_prime Q ℓ W hQW hWrel
  have hℓpow : ∀ n : ℕ, ℓ ^ n ∉ Q := fun n h => hi₀ (hQp.mem_of_pow_mem n h)
  have hdivpow : ∀ n : ℕ, divCycle Q (ℓ ^ n) = Finsupp.single W n := by
    intro n
    induction n with
    | zero => simp [divCycle_one]
    | succ n ih =>
      rw [pow_succ, divCycle_mul hQp (hℓpow n) hi₀, ih, hdivℓ, ← Finsupp.single_add]

  have hWpv : IsProjVarF W 0 :=
    isProjVarF_of_mem_divSupp (n := 0) hQ (isMultiHomog_X k₀ i₀) hi₀ ⟨hWmin, hWrel⟩
  set j : ∀ k, ι₀ k := fun k => (hWrel k).choose with hjdef
  have hj : IsChart W j := fun k => (hWrel k).choose_spec
  set p₁ : Σ k, ι₀ k := ⟨k₀, j k₀⟩ with hp₁
  set a : (Σ k, ι₀ k) → F := fun s => AddMonoidAlgebra.coeff (φ (X s)) (Finsupp.single 0 1) with hadef
  have hφXs : ∀ s, φ (X s) = C (a s) * X 0 := fun s => linearForm_fin_one_eq (hφX s)
  have ha1 : a p₁ ≠ 0 := by
    intro h0
    apply hj k₀
    rw [hWdef, RingHom.mem_ker, hφXs, h0, C_0, zero_mul]
  set c : (Σ k, ι₀ k) → F := fun s => a s / a p₁ with hcdef
  have hev : aeval c = (aeval fun _ : Fin 1 => (a p₁)⁻¹).comp φ := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [hφXs, hcdef, div_eq_mul_inv]
  have hpt : ∀ L : Fin 0 → K₀ → ℤ, J W 0 L = 1 := by
    intro L
    rw [hJ.1 W L j hWpv hj]
    unfold ptDeg chartIdeal
    rw [inh_finrank_quot _ c]
    · rfl
    · apply sup_le
      · intro f hf
        rw [RingHom.mem_ker, ← coe_aeval_eq_eval, hev]
        rw [hWdef, RingHom.mem_ker] at hf
        simp [hf]
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        obtain rfl : k = k₀ := hk k
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        exact sub_eq_zero.mpr (div_self ha1)
    · intro s
      have h1 : X s - C (c s) * X p₁ ∈ W := by
        rw [hWdef, RingHom.mem_ker, map_sub, map_mul, algHom_C, hφXs, hφXs, ← mul_assoc,
          algebraMap_eq, ← C_mul, hcdef, div_mul_cancel₀ _ ha1, sub_self]
      have h2 : C (c s) * (X p₁ - 1) ∈
          Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver F ι₀) - 1) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k₀, rfl⟩)
      have e : X s - C (c s) = (X s - C (c s) * X p₁) + C (c s) * (X p₁ - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)

  have e1 : (![m] : Fin 1 → K₀ → ℤ) = Fin.snoc (α := fun _ => K₀ → ℤ) Fin.elim0 m := by
    funext i
    fin_cases i
    rfl
  have hmk : ∀ k, m k = m k₀ := fun k => by rw [hk k]
  have hhomℓ : ∀ n : ℕ, IsMultiHomog (ℓ ^ n) (fun _ => n) := fun n => by
    have := isMultiHomog_pow (isMultiHomog_X (F := F) (ι := ι₀) k₀ i₀) n
    convert this using 1
    funext k
    rw [hk k]
    simp
  have h1Q : (1 : MRingOver F ι₀) ∉ Q := fun h => hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  rw [e1]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (m k₀)
  · rw [hJ.2 Q 0 Fin.elim0 m (ℓ ^ n) 1 hQ ⟨fun _ => n, 0, hhomℓ n, isMultiHomog_one, hℓpow n, h1Q,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp [inh_cycEval_single, hpt, hn]
  · rw [hJ.2 Q 0 Fin.elim0 m 1 (ℓ ^ n) hQ ⟨0, fun _ => n, isMultiHomog_one, hhomℓ n, h1Q, hℓpow n,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, zero_sub]
    rw [← Finsupp.single_neg, inh_cycEval_single, hpt, hn]
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogTwoXc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def RegularityProductFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    vertR P (Fin.elim0 : Fin 0 → HermLine ι) f - vertR P (Fin.elim0 : Fin 0 → HermLine ι) g =
      ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
        (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartScalingIndep

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isHomogeneous_mw {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hV
  refine Ideal.homogeneous_span _ S fun f hf => ?_
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, mem_weighted_of_isMultiHomog ha⟩

theorem coeff_eq_zero (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k) (hx : ∀ k, x ⟨k, i k⟩ ≠ 0)
    (hV : IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)))
    (s : Finset (K →₀ ℕ)) (g : (K →₀ ℕ) → MRingOver F ι)
    (hs : ∑ α ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0) :
    ∀ β ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g β) = 0 := by
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  have hxy : x = fun q => x ⟨q.1, i q.1⟩ * y q := by
    funext q
    show x q = x ⟨q.1, i q.1⟩ * (x q / x ⟨q.1, i q.1⟩)
    rw [mul_div_cancel₀ _ (hx q.1)]

  choose e₀ he₀ using fun α => exists_homog_chart (⊥ : Ideal (MRingOver F ι)) i (g α)
  set M : K → ℕ := s.sup e₀ with hM
  have hGex : ∀ α, ∃ G : MRingOver F ι, α ∈ s →
      G ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) M ∧
        Ideal.Quotient.mk (chartIdeal ⊥ i) G = Ideal.Quotient.mk (chartIdeal ⊥ i) (g α) := by
    intro α
    by_cases hα : α ∈ s
    · obtain ⟨G, h1, h2⟩ := he₀ α M (Finset.le_sup (f := e₀) hα)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hα⟩
  choose G hG using hGex
  have hker : chartIdeal (⊥ : Ideal (MRingOver F ι)) i ≤
      RingHom.ker (aeval y : MRingOver F ι →ₐ[F] Ω) := by
    unfold chartIdeal
    refine sup_le bot_le (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_X, map_one]
    show x ⟨k, i k⟩ / x ⟨k, i k⟩ - 1 = 0
    rw [div_self (hx k), sub_self]
  have hGx : ∀ α ∈ s, aeval x (G α) = (∏ k, x ⟨k, i k⟩ ^ M k) * aeval y (g α) := by
    intro α hα
    have h0 := hker (Ideal.Quotient.eq.mp (hG α hα).2)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h0
    rw [← h0]
    have h := aeval_blockScale (isMultiHomog_of_mem_weighted (hG α hα).1) (fun k => x ⟨k, i k⟩) y
    exact (congrArg (fun z => aeval z (G α)) hxy).trans h
  have hxc : ∀ α : K →₀ ℕ,
      aeval x (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) = ∏ k, x ⟨k, i k⟩ ^ α k := by
    intro α
    simp [map_prod]
  have hcM : (∏ k, x ⟨k, i k⟩ ^ M k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)

  have hH : (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) ∈
      RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sum]
    calc ∑ α ∈ s, aeval x (G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k)
        = ∑ α ∈ s, (∏ k, x ⟨k, i k⟩ ^ M k) *
            (aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k) :=
          Finset.sum_congr rfl fun α hα => by rw [map_mul, hGx α hα, hxc, mul_assoc]
      _ = 0 := by rw [← Finset.mul_sum, hs, mul_zero]
  have hmem : ∀ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k ∈
      weightedHomogeneousSubmodule F (mw (ι := ι)) (M + ⇑α) := fun α hα =>
    SetLike.mul_mem_graded (hG α hα).1 (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i ⇑α))
  intro β hβ

  have hcomp : weightedHomogeneousComponent (mw (ι := ι)) (M + ⇑β)
      (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) =
        G β * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ β k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single β]
    · rw [weightedHomogeneousComponent_of_mem (hmem β hβ), if_pos rfl]
    · intro α hα hne
      rw [weightedHomogeneousComponent_of_mem (hmem α hα), if_neg]
      intro h
      exact hne (DFunLike.coe_injective (add_left_cancel h)).symm
    · intro h
      exact absurd hβ h
  have hβV := weightedHomogeneousComponent_mem_of_mem F (mw (ι := ι)) (isHomogeneous_mw hV) hH (M + ⇑β)
  rw [hcomp, RingHom.mem_ker, map_mul, hGx β hβ, hxc] at hβV
  have hcβ : (∏ k, x ⟨k, i k⟩ ^ β k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hβV).resolve_right hcβ)).resolve_left hcM

end ChartScalingIndep

theorem ChartScalingIndep.proof : ChartScalingIndep.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ x i hx hV
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ α, ∃ a b : MRingOver F ι, aeval y b ≠ 0 ∧
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * aeval y b = aeval y a := by
    intro α
    obtain ⟨r, hr, t, ht, he⟩ := IntermediateField.mem_adjoin_iff_div.mp (p.coeff α).2
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨a, rfl⟩ := hr
    obtain ⟨b, rfl⟩ := ht
    change ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) = aeval y a / aeval y b at he
    by_cases hb : aeval y b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [he, hb, div_zero]
      simp
    · exact ⟨a, b, hb, by rw [he, div_mul_cancel₀ _ hb]⟩
  choose a b hb hab using hq
  set D : MRingOver F ι := ∏ α ∈ p.support, b α with hD
  have hD0 : aeval y D ≠ 0 := by
    rw [hD, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun α _ => hb α
  set g : (K →₀ ℕ) → MRingOver F ι := fun α => a α * ∏ β ∈ p.support.erase α, b β with hg
  have hgD : ∀ α ∈ p.support,
      aeval y (g α) = aeval y D * ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) := by
    intro α hα
    rw [hg, hD, map_mul, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hα, ← hab α]
    ring
  have h1 : aeval (fun k => x ⟨k, i k⟩) p = ∑ α ∈ p.support,
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * ∏ k, x ⟨k, i k⟩ ^ α k := by
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun k => pow_zero _)]
    rfl
  have hsum : ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0 := by
    calc ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k
        = aeval y D * aeval (fun k => x ⟨k, i k⟩) p := by
          rw [h1, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α hα => by rw [hgD α hα, mul_assoc]
      _ = 0 := by rw [hp, mul_zero]
  have h0 := ChartScalingIndep.coeff_eq_zero x i hx hV p.support g hsum
  refine MvPolynomial.ext _ _ fun α => ?_
  change p.coeff α = 0
  by_cases hα : α ∈ p.support
  · have h2 := h0 α hα
    rw [hgD α hα] at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left hD0
    exact_mod_cast h3
  · exact notMem_support_iff.mp hα

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFnDegAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FnDegAdjoin

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}

def quotEquiv (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) :
    (MvPolynomial σ F ⧸ I) ≃ₐ[F] Algebra.adjoin F (Set.range g) :=
  let e1 := Ideal.quotientEquivAlgOfEq F h
  let e2 := Ideal.quotientKerEquivRange (aeval g : MvPolynomial σ F →ₐ[F] Ω)
  let e3 := Subalgebra.equivOfEq _ _ (aeval_range (R := F) g)
  (e1.trans e2).trans e3

theorem quotEquiv_mk (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) (p : MvPolynomial σ F) :
    (quotEquiv g I h (Ideal.Quotient.mk I p) : Ω) = aeval g p :=
  rfl

theorem incl_apply {S T : Subalgebra F Ω} (h : S ≤ T) (x : S) :
    ((Subalgebra.inclusion h).toRingHom x : Ω) = x :=
  rfl

theorem toRingHom_apply {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (a : A) :
    f.toRingHom a = f a :=
  rfl

end FnDegAdjoin

theorem FnDegAdjoin.proof : FnDegAdjoin.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ K' _ ι' _ v x' i' hx hV
  have hker : chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
      RingHom.ker (aeval (fun q => x' q / x' ⟨q.1, i' q.1⟩) : MRingOver F ι' →ₐ[F] Ω) :=
    ChartRankAdjoin.chartIdeal_eq_ker hx hV
  have hcomap : (chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').comap
      (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom =
      RingHom.ker (aeval ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v) : MRingOver F ι →ₐ[F] Ω) := by
    rw [hker]
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]
  let _ := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
  unfold fnDeg
  let _ := (chartMap v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').toAlgebra
  have key := Algebra.finrank_eq_of_equiv_equiv (FnDegAdjoin.quotEquiv _ _ hcomap).toRingEquiv
    (FnDegAdjoin.quotEquiv _ _ hker).toRingEquiv
  refine key ?_
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Subtype.ext
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, chartMap, Ideal.quotientMap_mk]
  rw [FnDegAdjoin.incl_apply, FnDegAdjoin.toRingHom_apply, FnDegAdjoin.quotEquiv_mk, FnDegAdjoin.quotEquiv_mk,
    aeval_rename]

end GroundTheory.Heights₂.Heights.Inter
end
end

