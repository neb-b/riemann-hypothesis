module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreTranscendenceDegreeAlt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    ∀ G' : GenFibre v W',
      Algebra.trdeg G'.Φ (IntermediateField.adjoin G'.Φ
        (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G'.x' ⟨q.1.1, q.2⟩)) = Fintype.card (FibreBlock κ)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMore
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenericPointsCount.proof (hGood : GenericPointsAvoidBadLocus.Statement) : GenericPointsCount.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n G i Ψ hv hP' hP hΨ hi
  obtain ⟨D, a, hDa, hDP, hcount⟩ := hGood K ι K' ι' κ v P' n G i hv hP' hP hi
  have hJ : IsMultiHomogIdeal (Ideal.span {D}) :=
    ⟨{D}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hDa⟩, rfl⟩
  have hJP : ¬ Ideal.span {D} ≤ imageZ v P' := fun hle => hDP (hle (Ideal.subset_span rfl))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (projB_null Ψ hP hΨ hJ hJP)] with y hy
  rintro w ⟨z, hz, rfl, hΨz⟩
  have hD : eval z (map (Int.castRingHom ℂ) D) ≠ 0 := by
    intro h0
    refine hy ⟨z, hz, ⟨hz.1, fun f hf => ?_⟩, hΨz⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero]
  have hΨ0 : Ψ (segre z) 0 = 1 := by
    have := congrFun hΨz 0
    simpa using this
  rw [← hcount z hz hD]
  congr 1
  ext O
  constructor
  · rintro ⟨z', hz', rfl, hw⟩
    refine ⟨z', hz', rfl, ?_⟩
    have hμ : Ψ (segre fun p => z' (v p)) 0 ≠ 0 := by
      intro h0
      rw [h0, inv_zero, zero_smul] at hw
      rw [← hw, map_zero] at hΨ0
      exact zero_ne_one hΨ0
    refine sameOrbit_of_segre hz.1 (Ψ (segre fun p => z' (v p)) 0) hμ ?_
    rw [← hw, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · rintro ⟨z', hz', rfl, hs⟩
    refine ⟨z', hz', rfl, ?_⟩
    obtain ⟨c, hc, hcz⟩ := hs
    have hμ : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    rw [hcz, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, hΨ0, mul_one, smul_smul, inv_mul_cancel₀ hμ,
      one_smul]

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreLast
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionFibreMultiHomogeneous.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) →
    ∀ G' : GenFibre v W', IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G')

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VerticalDegree.proof (h₁ : FibreDimensionZero.Statement) (h₂ : ChartRankAdjoin.Statement)
    (h₃ : VerticalDegreeAfterAdjoining.Statement) : VerticalDegree.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW hV hch G' J' hJ
  have hfib := h₁ K ι K' ι' κ v p W' n hv hp hW hV G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hch k.1
    have hX : (X ⟨k.1, i' k.1⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h0
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  have hj : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, h₃ K ι K' ι' κ v p W' n i' hv hp hW hV hch G']
  congr 1
  exact (h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩) (fun k => i' k.1) hz
    hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrderOne

section Length

variable {A : Type*} [CommRing A]

theorem length_eq_one_of_sat (J W : Ideal A) [W.IsPrime] (hJ : J ≤ W) (hs : ∀ d ∈ W, ∃ u ∉ W, u * d ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) = 1 := by
  have hz : ∀ (r : A) (s : W.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk J r) s = 0 ↔ r ∈ W := by
    intro r s
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    constructor
    · rintro ⟨u, hu⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
      rcases ‹W.IsPrime›.mem_or_mem (hJ hu) with h | h
      · exact absurd h u.2
      rcases ‹W.IsPrime›.mem_or_mem h with h | h
      · exact absurd h s.2
      · exact h
    · intro hr
      obtain ⟨u, hu, hud⟩ := hs r hr
      refine ⟨⟨u, hu⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : u * ((s : A) * r) = u * r * s := by ring
      rw [show ((⟨u, hu⟩ : W.primeCompl) : A) = u from rfl, e]
      exact J.mul_mem_right _ hud
  have hgen : ∀ (q : A) (t : W.primeCompl) (r : A) (s : W.primeCompl) (hr : r ∉ W),
      LocalizedModule.mk (Ideal.Quotient.mk J q) t =
        Localization.mk (q * s) (t * ⟨r, hr⟩) • LocalizedModule.mk (Ideal.Quotient.mk J r) s := by
    intro q t r s hr
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul]
    congr 1
    ring
  have h1 : LocalizedModule.mk (Ideal.Quotient.mk J 1) (1 : W.primeCompl) ≠ 0 :=
    fun h => ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).2 ((hz 1 1).1 h))
  have : Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := ⟨⟨_, 0, h1⟩⟩
  rw [Module.length_eq_one_iff, isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hnN, hn0⟩ := (Submodule.ne_bot_iff N).1 hN
  induction n using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hr : r ∉ W := fun h => hn0 ((hz r s).2 h)
    rw [eq_top_iff]
    intro y _
    induction y using LocalizedModule.induction_on with
    | h m' t =>
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [hgen q t r s hr]
      exact N.smul_mem _ hnN

end Length

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

end Graded

end DiagonalOrderOne


end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingDimOne.proof (hF : LocRingFrac.Statement) (hN : LocRingNoeth.Statement)
    (hL : LocRingLocal.Statement) (hPow : LocRingPow.Statement) : LocRingDimOne.Statement := by
  classical
  intro K _ ι _ P s a W hP hs hsP hW
  obtain ⟨hPp, hPh, -⟩ := hP
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hNoeth := hN K ι P W hPp hWp hPW hW.2
  refine ⟨hNoeth, hloc, ?_⟩

  choose c hc using hW.2
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) c a
  have htW := AvoidRing.coordProd_not_mem hWp c hc a
  set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
  have htP : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set x : FractionRing (MRing ι ⧸ P) := IsLocalization.mk' _ (Ideal.Quotient.mk P s) ⟨_, htP⟩
  have hxA : x ∈ locRing P W := Subring.subset_closure ⟨s, t, a, htP, htW, hs, ht, rfl⟩
  have hx : x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x' : locRing P W := ⟨x, hxA⟩
  have hxu : ¬ IsUnit x' := fun h => (hunit x' s t a hs ht htW hx).mp h hsW
  have hx0 : x' ≠ 0 := by
    intro h
    have h0 : x = 0 := congrArg Subtype.val h
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hsP hx

  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x'}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun Q hQ _ y hy => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyn⟩ :=
      hPow K ι P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hyuv
    have hyn' : y ^ n = x' * ⟨z, hz⟩ := Subtype.ext (by simpa using hyn)
    have hyQ : y ^ n ∈ Q := hyn' ▸ Ideal.mul_mem_right _ _ (hQ.2 (Ideal.mem_span_singleton_self x'))
    exact hQ.1.mem_of_pow_mem n hyQ
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : IsLocalRing.maximalIdeal (locRing P W) ≠ ⊥ := fun h =>
    hx0 (by simpa [h] using (IsLocalRing.mem_maximalIdeal x').mpr hxu)
  have h1 : (IsLocalRing.maximalIdeal (locRing P W)).height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)))
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingIntClosure
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter


open Classical in
theorem subfield_closure_coords_eq_top {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι')) [P'.IsPrime] :
    Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
        Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι' ⧸ P') x
  have h : ∀ f : MRing ι', algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' f) ∈
      Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
        algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
          Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eq_intCast C r, map_intCast, map_intCast]; exact intCast_mem _ r
    | add f g hf hg =>
      rw [(Ideal.Quotient.mk P').map_add, (algebraMap _ _).map_add]
      exact add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact mul_mem hf (Subfield.subset_closure (by simp))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact div_mem (h f) (h g)

theorem LocRingIntClosureFinite.proof (h₁ : LocRingChartLoc.Statement) (h₂ : IntClosureLocFinite.Statement) :
    LocRingIntClosureFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W _hv hP' _hQ _hs _hsQ hW
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  obtain ⟨T, hTA, hloc⟩ := h₁ K ι (imageZ v P') W hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
  obtain ⟨t, ht⟩ := h₂ _ _ (fracMapZ v P') _ (subfield_closure_coords_eq_top P') _ T hTA hloc
  exact ⟨t, fun x _ hx => ht x hx⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem semiLocRing_le_empty {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (𝒲 : Set (Ideal (MRing ι))) : semiLocRing P 𝒲 ≤ semiLocRing P ∅ := by
  unfold semiLocRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, fun _ h => h.elim, hu, hwa, rfl⟩

theorem SemilocFinite.proof (h₁ : SemilocIntegral.Statement) (h₂ : LocRingIntClosureFinite.Statement)
    (h₃ : LocRingDimOne.Statement) : SemilocFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  have := hP'.2.1.1
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hN : IsNoetherianRing (locRing (imageZ v P') W) := (h₃ K ι (imageZ v P') s α W hQ.2.1 hs hsQ hW).1
  have hint := h₁ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
  refine ⟨?_, ?_⟩
  · let _ := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    let _ : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    obtain ⟨t, ht⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
    let g : semiLocRing P' (fibreOver v P' W) →ₗ[locRing (imageZ v P') W] FractionRing (MRing ι' ⧸ P') :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : ∀ b, g b ∈ Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P'))) :=
      fun b => ht _ (semiLocRing_le_empty P' _ b.2)
        ((hint.isIntegral b).map_of_comp_eq (RingHom.id (locRing (imageZ v P') W)) (semiLocRing P' (fibreOver v P' W)).subtype
          (RingHom.ext fun _ => rfl))
    have : IsNoetherian (locRing (imageZ v P') W)
        (Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P')))) :=
      isNoetherian_span_of_finite _ t.finite_toSet
    exact Module.Finite.of_injective (g.codRestrict _ hg)
      fun b c hbc => by
        have h := congrArg Subtype.val hbc
        exact Subtype.ext h
  · have := imageZ_isPrime_of_prime v P'
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.val_injective ((fracMapZ v P').injective (congrArg Subtype.val hab))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def ptsOverChart (P' : Ideal (MRing ι')) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k'))
    (j : ∀ k : FibreBlock κ, ι' k.1) (z : (Σ k, ι k) → ℂ) : Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z ∧
    ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0}

end Over

def GenericPointsInAffineChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverChart P' κ v j z).Finite ∧
        (ptsOverChart P' κ v j z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) ∧
        ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) z → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) →
          ∀ q : Σ k : FibreBlock κ, ι' k.1, G.x' ⟨q.1.1, q.2⟩ ≠ 0 → z' ⟨q.1.1, q.2⟩ ≠ 0

end GroundTheory.Heights₂.Heights.Inter
end
end

