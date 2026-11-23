module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleChartSectionTools
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

section PolynomialHeights

variable {σ : Type*} [Finite σ]

theorem ringKrullDim_mvPolynomial_dvr (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] :
    ringKrullDim (MvPolynomial σ O) = ((Nat.card σ + 1 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [ENat.card_eq_coe_natCard]
  push_cast
  ring

theorem height_mvPolynomial_field_of_isMaximal {k : Type*} [Field k]
    (M : Ideal (MvPolynomial σ k)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = (Nat.card σ : WithBot ℕ∞) := by
  have h := DimF.height_eq_ringKrullDim_of_forall
    (DimF.height_eq_of_isMaximal_of_field (k := k)) M hM
  rw [h, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp [ENat.card_eq_coe_natCard]

theorem le_height_of_isMaximal_of_uniformiser_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (m : Ideal (MvPolynomial σ O))
    (hm : m.IsMaximal) (hϖm : (C ϖ : MvPolynomial σ O) ∈ m) :
    ((Nat.card σ + 1 : ℕ) : ℕ∞) ≤ m.height := by
  set p0 : Ideal (MvPolynomial σ O) := Ideal.map C (IsLocalRing.maximalIdeal O) with hp0def
  have hp0 : p0 = Ideal.span {C ϖ} := by
    rw [hp0def, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let e : (MvPolynomial σ O ⧸ p0) ≃+* MvPolynomial σ (IsLocalRing.ResidueField O) :=
    (MvPolynomial.quotientEquivQuotientMvPolynomial (IsLocalRing.maximalIdeal O)).symm.toRingEquiv
  have hdom : IsDomain (MvPolynomial σ O ⧸ p0) := Function.Injective.isDomain e.toRingHom (by exact e.injective)
  have hp0p : p0.IsPrime := (Ideal.Quotient.isDomain_iff_prime p0).mp hdom
  have hle : p0 ≤ m := by
    rw [hp0]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hϖm)
  have hmb : (m.map (Ideal.Quotient.mk p0)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hle)
  have h1 : (m.map (Ideal.Quotient.mk p0)).height = Nat.card σ := by
    rw [← e.height_map]
    have := height_mvPolynomial_field_of_isMaximal (k := IsLocalRing.ResidueField O) _
      (Ideal.map_isMaximal_of_equiv e (p := m.map (Ideal.Quotient.mk p0)))
    exact_mod_cast this
  have h0 : 1 ≤ p0.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, hp0,
      Ideal.span_singleton_eq_bot, C_eq_zero]
    exact hϖ.ne_zero
  have hfin : FiniteRingKrullDim (MvPolynomial σ O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, ringKrullDim_mvPolynomial_dvr]
    exact ⟨by simp, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have h2 := DimF.height_add_height_map_le (q := p0) (M := m) hle
  rw [h1] at h2
  calc ((Nat.card σ + 1 : ℕ) : ℕ∞) = 1 + (Nat.card σ : ℕ∞) := by push_cast; ring
    _ ≤ p0.height + (Nat.card σ : ℕ∞) := add_le_add h0 le_rfl
    _ ≤ m.height := h2

theorem ringKrullDim_quotient_le_sub_height {A : Type*} [CommRing A] [IsNoetherianRing A]
    [FiniteRingKrullDim A] (P : Ideal A) [P.IsPrime] (N h : ℕ)
    (hmax : ∀ m : Ideal A, m.IsMaximal → m.height ≤ N) (hP : P.height = h) :
    ringKrullDim (A ⧸ P) ≤ ((N - h : ℕ) : WithBot ℕ∞) := by
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun M hM => ?_
  have hc : (M.comap (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have : (M.comap (Ideal.Quotient.mk P)).IsPrime := hc.isPrime
  have hPle : P ≤ M.comap (Ideal.Quotient.mk P) := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M.zero_mem
  have e : (M.comap (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk P) = M :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M
  have h2 := DimF.height_add_height_map_le (q := P) (M := M.comap (Ideal.Quotient.mk P)) hPle
  rw [e, hP] at h2
  have h3 := DimF.le_natSub_of_add_le (h2.trans (hmax _ hc))
  calc (M.height : WithBot ℕ∞) ≤ (((N - h : ℕ) : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr h3
    _ = ((N - h : ℕ) : WithBot ℕ∞) := WithBot.coe_natCast _

theorem withBot_eq_of_le_of_add_one_le {x : WithBot ℕ∞} {c : ℕ} (h1 : (c : WithBot ℕ∞) ≤ x)
    (h2 : x + 1 ≤ ((c + 1 : ℕ) : WithBot ℕ∞)) : x = c :=
  _root_.UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le h1 h2

end PolynomialHeights

theorem ComponentDim.proof : ComponentDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hfa hfP W hW hϖW
  have hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))

  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm⟩ := Ideal.exists_le_maximal W hWp.ne_top
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm (hWm hϖW)
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hP.dim] at hPdim
  have hPdim' : d + 1 + Fintype.card K ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : d + Fintype.card K ≤ b0 := by omega
  have hlow' : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hP.dim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' (by rw [show d + Fintype.card K + 1 = d + 1 + Fintype.card K by ring]; exact hup)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Module IsLocalRing

noncomputable section

universe u

namespace FiniteBirationalLength

theorem length_quot_maximal_eq_inertiaDeg {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.length A (B ⧸ 𝔫) = (𝔫.inertiaDeg A : ℕ∞) := by
  have hmax : (𝔫.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫
  have hm : 𝔫.under A = maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have : 𝔫.LiesOver (maximalIdeal A) := ⟨hm.symm⟩
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ 𝔫) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) 𝔫,
    Module.length_eq_of_surjective (R := A ⧸ maximalIdeal A) (S := A) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

theorem full : FiniteBirationalLength.Statement.{u} := by
  intro A B _ _ _ _ _ _ _ _ hdim hinj hrank z hz
  classical
  have hfinMS := Vertical.LengthDecomp.finite_maximalSpectrum (R := A) (B := B)
  have hfin : Finite {𝔫 : Ideal B // 𝔫.IsMaximal} :=
    Finite.of_injective
      (fun 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal} => (⟨𝔫.1, 𝔫.2⟩ : MaximalSpectrum B))
      (fun a b h => Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
  refine ⟨hfin, ?_⟩
  let : Fintype {𝔫 : Ideal B // 𝔫.IsMaximal} := Fintype.ofFinite _
  have : Module.IsTorsionFree A B := isTorsionFree_iff_algebraMap_injective.mpr hinj
  have h1 := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A B z hdim hz
  rw [hrank, Nat.cast_one, one_mul, Ring.ord] at h1
  let hP : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal}, 𝔫.1.IsPrime := fun 𝔫 => 𝔫.2.isPrime
  have h2 := FieldNumbers.FiniteAlgebraLengthSum.proof A B {𝔫 : Ideal B // 𝔫.IsMaximal}
    (fun 𝔫 => 𝔫.1) (fun 𝔫 => 𝔫.2) Subtype.val_injective (fun M hM => ⟨⟨M, hM⟩, rfl⟩)
    (fun 𝔫 => Localization.AtPrime 𝔫.1) (fun 𝔫 => inferInstance) z
  rw [← h1, h2, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have := 𝔫.2
  rw [length_quot_maximal_eq_inertiaDeg, Ring.ord]

end FiniteBirationalLength

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleChartSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open FlagBundleSectionForms (chartPow chartMono liftNat) in
open FlagBundleChartSection in
theorem FlagBundleChartSection.proof : FlagBundleChartSection.Statement := by
  intro F _ Ω _ _ K _ _ ι y N E _ _ B w b hfl M a φ hφ Φ _ _ t ht i c hsc
  classical
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hsc) k (Finset.mem_univ _)
  have hcpb : chartPow y c (b i) ≠ 0 := chartPow_ne_zero hY _
  obtain ⟨dl, β, f, hfh, hdeg, hfv⟩ := exists_section_form (M := M) y B w b hfl a φ hφ t i c hsc

  obtain ⟨vi, hviL, hviT, hviD⟩ : ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
      w.repr v i = chartPow y c (b i) := by
    have h := hfl.graded c hsc i
    rw [Set.ext_iff] at h
    exact (h (chartPow y c (b i))).2 ⟨1, one_mem _, (one_mul _).symm⟩

  have hr : ∀ l, ∃ r ∈ chartRing F (segreVec y) c, φ l vi = r * chartPow y c a :=
    fun l => hφ.sections c hsc l vi hviL
  choose r hrA hrv using hr
  obtain ⟨n₂, R, hRh, hRe⟩ := chartRing_forms_fin (M := M) y w φ (truncCoord t ((i : ℕ) + 1)) c hsc hrA

  let γ₁ : K → ℕ := fun k => (b i k - a k).toNat
  let γ₂ : K → ℕ := fun k => (a k - b i k).toNat
  let δ : K → ℕ := β + fun k => n₂ + γ₁ k
  let u : MRing (bundleIdx ι M) F := chartMono M c δ
  let Y : Fin M → MRing (bundleIdx ι M) F := fun l => u * X ⟨none, l⟩ - R l * chartMono M c γ₂ * f
  let g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F := fun v =>
    match v with
    | ⟨none, l⟩ => Y l
    | ⟨some k, p⟩ => X ⟨some k, p⟩
  let e : Option K → ℕ := fun o => liftNat δ o + Option.elim o 1 (fun _ => 0)
  have hYh : ∀ l, IsMultiHomog (Y l) e := by
    intro l
    refine isMultiHomog_sub ?_ ?_
    · have h := (chartMono_homog (F := F) M c δ).mul
        (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
      have he : e = liftNat δ + blockWeight (bundleIdx ι M) ⟨none, l⟩ := by
        funext o
        cases o <;> simp [e, liftNat, blockWeight]
      rw [he]
      exact h
    · have h := ((hRh l).mul (chartMono_homog (F := F) M c γ₂)).mul hfh
      have he : e = (liftNat fun _ => n₂) + liftNat γ₂ + dl := by
        funext o
        cases o with
        | none =>
          have h0 := congrFun hdeg none
          simp [liftNat, zetaDeg, liftDeg] at h0
          simp [e, liftNat]
          omega
        | some k =>
          have h0 := congrFun hdeg (some k)
          simp [liftNat, zetaDeg, liftDeg] at h0
          simp [e, liftNat, δ, γ₁, γ₂]
          omega
      rw [he]
      exact h
  have hid : (∏ k, y ⟨k, c k⟩ ^ δ k) * chartPow y c a =
      (∏ k, y ⟨k, c k⟩ ^ β k) * segreVec y c ^ n₂ * (∏ k, y ⟨k, c k⟩ ^ γ₂ k) * chartPow y c (b i) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_natCast]
    simp only [← chartPow_add hY]
    congr 1
    funext k
    simp only [Pi.add_apply, Nat.cast_add, δ, γ₁, γ₂]
    omega
  have hevY : ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (Y l) =
      algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ -
        algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * (t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹) *
          algebraMap Ω Φ (φ l vi) := by
    intro l
    have hΩ : r l * segreVec y c ^ n₂ * (∏ k, y ⟨k, c k⟩ ^ γ₂ k) * (∏ k, y ⟨k, c k⟩ ^ β k) =
        (∏ k, y ⟨k, c k⟩ ^ δ k) * (chartPow y c (b i))⁻¹ * (r l * chartPow y c a) := by
      rw [show (∏ k, y ⟨k, c k⟩ ^ δ k) * (chartPow y c (b i))⁻¹ * (r l * chartPow y c a) =
        r l * ((∏ k, y ⟨k, c k⟩ ^ δ k) * chartPow y c a) * (chartPow y c (b i))⁻¹ by ring, hid]
      field_simp
    have h2 := congrArg (algebraMap Ω Φ) hΩ
    simp only [Y, u, eval₂_sub, eval₂_mul, eval₂_X, hRe, eval_chartMono, hfv, hrv]
    simp only [map_mul, map_inv₀] at h2 ⊢
    linear_combination (-(t i)) * h2

  have hgev : (fun v => eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (g v)) =
      projCoord y w φ (truncCoord (fun j => algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) *
        (t j - t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ * algebraMap Ω Φ (w.repr vi j))) i) := by
    funext v
    rcases v with ⟨_ | k, p⟩
    · show eval₂ _ _ (Y p) = _
      have hφv : algebraMap Ω Φ (φ p vi) =
          ∑ j, algebraMap Ω Φ (w.repr vi j) * algebraMap Ω Φ (φ p (w j)) := by
        conv_lhs => rw [← w.sum_repr vi]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, smul_eq_mul, map_mul]
      rw [hevY p, hφv]
      simp only [projCoord]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [truncCoord]
      rcases lt_trichotomy j i with h | h | h
      · have h1 : (j : ℕ) < i := h
        have h2 : (j : ℕ) < (i : ℕ) + 1 := by omega
        simp only [h1, h2, if_true]
        ring
      · subst h
        have h1 : ¬ (j : ℕ) < j := lt_irrefl _
        have h2 : (j : ℕ) < (j : ℕ) + 1 := Nat.lt_succ_self _
        have hσ : t j * algebraMap Ω Φ (chartPow y c (b j))⁻¹ * algebraMap Ω Φ (chartPow y c (b j)) = t j := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hcpb, map_one, mul_one]
        simp only [h1, h2, if_true, if_false, hviD]
        linear_combination (-(algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * algebraMap Ω Φ (φ p (w j)))) * hσ
      · have h1 : ¬ (j : ℕ) < i := by
          have : (i : ℕ) < j := h
          omega
        have h2 : ¬ (j : ℕ) < (i : ℕ) + 1 := by
          have : (i : ℕ) < j := h
          omega
        simp only [h1, h2, if_false, hviT j h, map_zero]
        ring
    · rw [eval₂_X]
      rfl

  have hform : ∀ (d : Option K → ℕ) (q : MRing (bundleIdx ι M) F), IsMultiHomog q d →
      q ∈ projIdeal F y w φ (truncCoord t i) →
      u ^ d none * q ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} := by
    intro d q hq hqI
    have h1 : bind₁ g q ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      rw [ProjIdealFormValue.proof F Ω K ι y N E w M φ Φ _ _ _
        (bind₁_isMultiHomog g e (fun _ _ => rfl) hYh hq)]
      rw [← coe_eval₂Hom, eval₂Hom_bind₁, coe_eval₂Hom]
      simp only [coe_eval₂Hom]
      rw [hgev]
      exact eval_trunc_eq_zero y w φ ht i hqI _
    have h2 : u ^ d none * q - bind₁ g q ∈ Ideal.span {f} := by
      rw [← bind₁_scale u hq]
      refine bind₁_sub_mem _ g _ (fun v => ?_) q
      rcases v with ⟨_ | k, p⟩
      · have h3 : u ^ blockWeight (bundleIdx ι M) ⟨none, p⟩ none * X ⟨none, p⟩ - g ⟨none, p⟩ =
            R p * chartMono M c γ₂ * f := by
          simp [g, Y, blockWeight]
        rw [h3]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)
      · have h3 : u ^ blockWeight (bundleIdx ι M) ⟨some k, p⟩ none * X ⟨some k, p⟩ - g ⟨some k, p⟩ = 0 := by
          simp [g, blockWeight]
        rw [h3]
        exact zero_mem _
    have h3 : bind₁ g q + (u ^ d none * q - bind₁ g q) ∈
        projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} :=
      Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    rwa [add_sub_cancel] at h3
  refine ⟨dl, liftNat β, f, chartMono M c β, β, rfl, hfh, chartMono_homog M c β, hdeg, hfv, ?_⟩
  intro q hq

  have hsat : ∀ d, ∃ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n *
      weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈
      projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} := by
    intro d
    have hqd := hform d _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (component_mem_projIdeal y w φ _ hq d)
    obtain ⟨r', hr'⟩ := chartMono_pow_dvd (F := F) (M := M) c δ (d none)
    refine ⟨d none * ∑ k, δ k, ?_⟩
    rw [hr', mul_comm (chartMono M c δ ^ d none) r', mul_assoc]
    exact Ideal.mul_mem_left _ _ hqd
  choose nn hnn using hsat
  obtain ⟨S, hS⟩ : ∃ S : Finset (Option K → ℕ),
      q = ∑ d ∈ S, weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q := by
    have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight (bundleIdx ι M)) q
    refine ⟨hfin.toFinset, ?_⟩
    conv_lhs => rw [← sum_weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) q]
    exact finsum_eq_sum _ hfin
  refine ⟨∑ d ∈ S, nn d, ?_⟩
  rw [hS, Finset.mul_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [← Nat.sub_add_cancel (Finset.single_le_sum (f := nn) (fun _ _ => Nat.zero_le _) hd), pow_add,
    mul_assoc]
  exact Ideal.mul_mem_left _ _ (hnn d)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelValueIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace FlagModelValueIndependence

theorem fieldNum_isFieldIntersection (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type)
    [∀ k, Fintype (κ k)] : IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem pullDeg_sub {K K' : Type} (a b : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (a - b) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') a - IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') b := by
  funext k
  cases k <;> simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]

theorem proof (hOne : FlagPairValueIndependence.Statement) (hCommon : FlagModelCommonModel.Statement) :
    FlagModelValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂ I₁ I₂ hI₁ hI₂ G hG r y y' f g hv c Q hc hGc hQ
  obtain ⟨K'', _, ι'', _, z, EB, E'B, φ₁, φ₂, hZ, -, -, -, hS, hpull, hval⟩ :=
    hCommon O Ω K ι x d N V E E' hW hE F₁ F₂
  have hI := fieldNum_isFieldIntersection (IsLocalRing.ResidueField O) (Sum.elim ι ι'')
  obtain ⟨h₁, h₂⟩ := hval _ I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hGc hQ
  rw [h₁, h₂]
  refine hOne O Ω (K ⊕ K'') (Sum.elim ι ι'') (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) d N V EB E'B hZ hS
    φ₁ φ₂ _ hI G hG r (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y l))
    (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y' l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l)) (fun l => ?_) c Q hc hGc hQ
  rw [← pullDeg_sub]
  exact hpull _ _ _ (hv l)

end FlagModelValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end

