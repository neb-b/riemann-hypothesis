module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtPosOfMemDivSupp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem multAt_pos_of_mem_divSupp {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalDivisor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]


open Classical in
theorem divCycle_eq_ite {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by
  by_cases hW : W ∈ divSupp P (s * u)
  · rw [if_pos hW]
    by_cases hWs : W ∈ divSupp P s
    · exact divCycle_of_mem hWs
    rw [divCycle_of_not_mem hWs]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hsW : s ∈ W
    · exfalso
      refine hWs ⟨⟨⟨hWp, sup_le (le_sup_left.trans hW.1.1.2)
        ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, ?_⟩ hQW⟩, hW.2⟩
      exact (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self s))) P).trans hQ.2
    · have hnle : ¬ P ⊔ Ideal.span {s} ≤ W := fun h => hsW (h (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      unfold multAt
      rw [dite_eq_left hWp, Module.length_eq_zero_iff.mpr
        (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W hnle)]
      rfl
  · rw [if_neg hW]
    refine divCycle_of_not_mem fun hWs => hW ⟨?_, hWs.2⟩
    exact NumbersDVR.mem_minimalPrimes_sup_span_mul hu hWs.1

end DiagonalDivisor


end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrder

section Orders

variable {K : Type} {ι : K → Type}

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem multAt_sup_span_eq {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by
  have := hW
  have hlen : ∀ {s w : MRing ι}, w ∉ W →
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {w * s}))) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {s}))) := by
    intro s w hw
    rw [NumbersDVR.length_localizedQuot_sup_span_mul P W s (fun h' => hw (hPW h')),
      Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W
        (fun hle => hw (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))), add_zero]
  have heq : P ⊔ Ideal.span {u * g} = P ⊔ Ideal.span {v * h} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : u * g = (u * g - v * h) + v * h := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hm)
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW, ← hlen (s := g) hu, heq, hlen hv]

end Orders

section Diagonal

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]



end Diagonal

end DiagonalOrder


end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HorizNotMem.ringKrullDim_quotient_add_one_le {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩
  rw [← Order.krullDim_withBot]
  let f : WithBot (PrimeSpectrum.zeroLocus (R := R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ :=
    fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x
  refine Order.krullDim_le_of_strictMono f ?_
  intro a b hab
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (lt_irrefl _)
    | coe q =>
      change (⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
        (hlt.trans_le (fun _ h => q.2 h)))
  | coe p =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (WithBot.not_lt_bot _)
    | coe q =>
      change (⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))

theorem HorizNotMem.proof : HorizNotMem.Statement := by
  intro K _ ι _ P d s s' W hP hsP hs'P hnc hW hWh hs'W
  have : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hle : P ⊔ Ideal.span {s'} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hs'W)
  obtain ⟨W₀, hW₀, hW₀W⟩ := Ideal.exists_minimalPrimes_le hle
  have : W₀.IsPrime := hW₀.1.1
  have h1 := dim_quot_minimal_add_one P W s hsP hW.1
  have h2 := dim_quot_minimal_add_one P W₀ s' hs'P hW₀
  have heq : W₀ = W := by
    by_contra hne
    have hstep := HorizNotMem.ringKrullDim_quotient_add_one_le (lt_of_le_of_ne hW₀W hne)
    have h3 := add_le_add hstep (le_refl (1 : WithBot ℕ∞))
    rw [h1, h2, hP.2.2.2] at h3
    have h4 : ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h5
    omega
  exact hnc W hW ⟨heq ▸ hW₀, hW.2⟩ hWh

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingFrac

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

end LocRingFrac

theorem LocRingFrac.proof : LocRingFrac.Statement := by
  intro K _ ι _ P W _ hW _ y hy
  have h1 : (1 : MRing ι) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hy using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
    exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
  | zero => exact ⟨0, 1, 0, isMultiHomog_zero 0, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | one => exact ⟨1, 1, 0, AvoidRing.isMultiHomog_one, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * v' + u' * v, v * v', a + a',
      isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
        (by rw [add_comm]; exact AvoidRing.isMultiHomog_mul hu' hv),
      AvoidRing.isMultiHomog_mul hv hv', fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    simp only [RingHom.map_mul, RingHom.map_add]
    rw [← e, ← e']
    ring
  | neg x _ hx =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    exact ⟨-u, v, a, isMultiHomog_neg hu, hv, hvW, by
      simp only [RingHom.map_neg]
      rw [← e]
      ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * u', v * v', a + a', AvoidRing.isMultiHomog_mul hu hu', AvoidRing.isMultiHomog_mul hv hv',
      fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingLocal

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

end LocRingLocal

theorem LocRingLocal.proof (hF : LocRingFrac.Statement) : LocRingLocal.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP
  set F := FractionRing (MRing ι ⧸ P)
  have hnzd : ∀ w : MRing ι, w ∉ W → Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P) := fun w hw =>
    mem_nonZeroDivisors_of_ne_zero fun h => hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hne : ∀ w : MRing ι, w ∉ W → algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P w) ≠ 0 := fun w hw =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hnzd w hw)
  have key : ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (y : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P u) →
      (IsUnit y ↔ u ∉ W) := by
    intro y u v a hu hv hvW hy
    constructor
    · rintro hunit huW
      obtain ⟨y', hyy'⟩ := hunit.exists_right_inv
      obtain ⟨u', v', a', -, -, hv'W, hy'⟩ := hF K ι P W hP hW hPW y' y'.2
      have h1 : ((y * y' : locRing P W) : F) = 1 := by rw [hyy']; rfl
      have h2 : algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * u')) := by
        rw [map_mul, map_mul, map_mul, map_mul, ← hy, ← hy']
        rw [Subring.coe_mul] at h1
        linear_combination (-(algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) *
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v'))) * h1
      have h3 := Ideal.Quotient.eq.mp (IsFractionRing.injective (MRing ι ⧸ P) F h2)
      have h4 : v * v' ∈ W := by
        have := W.add_mem (hPW h3) (W.mul_mem_right u' huW)
        simpa using this
      rcases hW.mem_or_mem h4 with h | h
      · exact hvW h
      · exact hv'W h
    · intro huW
      have hz : IsLocalization.mk' F (Ideal.Quotient.mk P v) (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P)) ∈
          locRing P W := Subring.subset_closure ⟨v, u, a, hnzd u huW, huW, hv, hu, rfl⟩
      refine IsUnit.of_mul_eq_one (a := y) ⟨_, hz⟩ (Subtype.ext ?_)
      have hspec := IsLocalization.mk'_spec F (Ideal.Quotient.mk P v)
        (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P))
      simp only [Subring.coe_mul, Subring.coe_one]
      apply mul_right_cancel₀ (hne u huW)
      rw [one_mul, mul_assoc, hspec, hy]
  refine ⟨?_, key⟩
  refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hxe⟩ := hF K ι P W hP hW hPW x x.2
  obtain ⟨u', v', a', hu', hv', hv'W, hye⟩ := hF K ι P W hP hW hPW y y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((key x u v a hu hv hvW hxe).mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((key y u' v' a' hu' hv' hv'W hye).mpr h)
  have hvv' : v * v' ∉ W := fun h => (hW.mem_or_mem h).elim hvW hv'W
  have hsum : ((x + y : locRing P W) : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
      algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * v' + u' * v)) := by
    simp only [Subring.coe_add, map_mul, (algebraMap (MRing ι ⧸ P) F).map_add,
      (Ideal.Quotient.mk P).map_add]
    rw [← hxe, ← hye]
    ring
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') :=
    LocRingLocal.isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
      (add_comm a' a ▸ AvoidRing.isMultiHomog_mul hu' hv)
  intro hunit
  exact (key (x + y) _ _ (a + a') hnum (AvoidRing.isMultiHomog_mul hv hv') hvv' hsum).mp hunit
    (W.add_mem (W.mul_mem_right v' huW) (W.mul_mem_right v hu'W))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]



def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s



end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingChartLoc
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def LocRingChartLoc.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) [P.IsPrime],
    W.IsPrime → P ≤ W → IsRelevant W →
    ∃ T : Finset (FractionRing (MRing ι ⧸ P)),
      Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))) ≤ locRing P W ∧
      ∀ z ∈ locRing P W, ∃ b ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))),
        ∃ c ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))), c ≠ 0 ∧ c⁻¹ ∈ locRing P W ∧ z * c = b

end GroundTheory.Heights₂.Heights.Inter
end
end

