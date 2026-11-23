module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOrderLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem subring_map_maximal_cases {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by
  by_cases h : m ≤ (IsLocalRing.maximalIdeal D).comap C.subtype
  · right
    rw [hm.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal D).ne_top) h]
    exact hC
  · left
    obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp h
    have hu : IsUnit (C.subtype c) := by
      by_contra hnu
      exact hc (IsLocalRing.mem_maximalIdeal _ |>.mpr hnu)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hcm) hu

theorem length_quot_le_of_subring (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  let _ : Algebra A C := f.toAlgebra
  have s3 := h₃ A C hdim hfinj
    (fun c => by
      obtain ⟨b, hb, hbc⟩ := hfrac c
      exact ⟨b, hb, by rw [Algebra.smul_def]; exact hbc⟩) a ha
  have s2 : Module.length C (C ⧸ Ideal.span {algebraMap A C a}) ≤
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) := by
    have h := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at h
  have s1 := h₂ C D C.subtype (subring_map_maximal_cases C hmax) (Ideal.span {algebraMap A C a})
  rw [Ideal.map_span, Set.image_singleton] at s1
  exact s1.trans (s2.trans s3)

theorem BlowUpOrderLe.proof (h₁ : LocalizedQuotLength.Statement.{u})
    (h₂ : LengthMapIdealLe.Statement.{u}) (h₃ : IntermediateRingQuotLength.Statement.{u})
    (h₄ : BlowUpLocalChart.Statement.{u}) : BlowUpOrderLe.Statement.{u} := by
  intro R _ _ K _ ι _ J _ P hP u G' y hy hG' hrel x hx hG z hz
  have hGp : G'.IsPrime := hG'.1.1
  obtain ⟨G₀, W₀, hG₀p, hW₀p, hG₀, hW₀⟩ := BlowUpLocalChart.exists_quotient_primes hGp
    (le_sup_left.trans hG'.1.2) (le_sup_left.trans hG.1.2)
  have hRHS0 : (0 : ℤ) ≤ divCycle P z (G'.comap (liftForm (J := J))) := by
    unfold divCycle
    split_ifs <;> positivity
  by_cases hL : G' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm z}).minimalPrimes ∧ IsRelevant G'
  swap
  · have h0 : divCycle (blowUpOf P u) (liftForm z) G' = 0 := by
      unfold divCycle
      rw [dite_eq_right hL]
    rw [h0]
    exact hRHS0
  have hzG : z ∈ G'.comap (liftForm (J := J)) :=
    hL.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcp : (G'.comap (liftForm (J := J))).IsPrime := hG.1.1
  have hRmin : G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {z}).minimalPrimes := by
    have h := mem_minimalPrimes_sup_span_mul (P := P) (W := G'.comap (liftForm (J := J))) hz hG
    refine ⟨⟨hcp, sup_le (le_sup_left.trans hG.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hzG)⟩, ?_⟩
    intro q hq hqG
    refine h.2 ⟨hq.1, sup_le (le_sup_left.trans hq.2) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hqG
    exact q.mul_mem_left x (hq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z)))
  have hRrel : IsRelevant (G'.comap (liftForm (J := J))) := by
    intro k
    obtain ⟨i, hi⟩ := hL.2 (some k)
    refine ⟨i, fun hmem => hi ?_⟩
    rw [Ideal.mem_comap] at hmem
    simpa [liftForm, rename_X] using hmem
  have hfin := length_localizedQuot_ne_top (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) hRmin
  unfold divCycle
  rw [dite_eq_left hL, dite_eq_left ⟨hRmin, hRrel⟩]
  suffices key : multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) G' ≤
      multAt (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) by
    exact_mod_cast ENat.toNat_le_toNat key hfin

  obtain ⟨C, f, hfinj, hfrac, hfcompat, hmax⟩ := h₄ R K ι J P hP u G' y hy hG' hrel x hx hG G₀ hG₀ W₀ hW₀
  have hQp : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hSn : IsNoetherianRing (MRing ι R ⧸ P) := inferInstance
  have hAn : IsNoetherianRing (Localization.AtPrime G₀) :=
    IsLocalization.isNoetherianRing G₀.primeCompl _ hSn
  have hAinj : Function.Injective (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀)) :=
    IsLocalization.injective (Localization.AtPrime G₀) (Ideal.primeCompl_le_nonZeroDivisors G₀)
  have hdim : ringKrullDim (Localization.AtPrime G₀) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height G₀ (Localization.AtPrime G₀)]
    have hmap : (G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P) = G₀ := by
      rw [← hG₀, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hle : G₀.height ≤ 1 := hmap ▸ Ideal.map_height_le_one_of_mem_minimalPrimes hG
    have hne : G₀.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      have hxG : Ideal.Quotient.mk P x ∈ G₀ := by
        rw [← Ideal.mem_comap, hG₀]
        exact hG.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hxG
      exact hx hxG
    have h1 : G₀.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
    rw [h1]
    rfl
  set a : Localization.AtPrime G₀ :=
    algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P z) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    rw [ha_def, ← map_zero (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀))] at h0
    exact hz (Ideal.Quotient.eq_zero_iff_mem.mp (hAinj h0))
  have hDom : IsDomain (Localization.AtPrime W₀) := inferInstance
  have hchain := length_quot_le_of_subring h₂ h₃ hdim C f hfinj hfrac hmax a ha
  rw [ha_def, hfcompat z] at hchain
  have e₁ := h₁ (MRing (extIdx ι J) R) (blowUpOf P u) W₀ (liftForm z)
  have e₂ := h₁ (MRing ι R) P G₀ z
  have key : ∀ (H : Ideal (MRing (extIdx ι J) R)) [H.IsPrime] (G : Ideal (MRing ι R)) [G.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = H → G₀.comap (Ideal.Quotient.mk P) = G →
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) H ≤ multAt (P ⊔ Ideal.span {z}) G := by
    intro H _ G _ hH hGG
    subst hH
    subst hGG
    unfold multAt
    exact e₁.le.trans (hchain.trans e₂.ge)
  exact key _ _ hW₀ hG₀

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimTwoSumReading
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing

noncomputable section

namespace DimTwoSumReading

variable {A : Type*} [CommRing A]

theorem length_loc_eq_ordLoc (W : Ideal A) [hW : W.IsPrime] (a : A) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc ⟨W, hW⟩ a := by
  have h := length_localizedModule_quot_eq (T := Localization.AtPrime W) W.primeCompl ⊥ a
    (fun s hs => IsLocalization.map_units _ (⟨s, hs⟩ : W.primeCompl))
    (fun y => by
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj W.primeCompl y
      exact ⟨r, s, s.2, hy.symm⟩)
    (fun r hr => by
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff W.primeCompl _ r).mp hr
      exact ⟨s, s.2, (Ideal.mem_bot).mpr hs⟩)
    (fun v hv => by rw [(Ideal.mem_bot).mp hv, map_zero])
  rw [bot_sup_eq] at h
  exact h

theorem length_max_eq_ordMod [IsLocalRing A] (W : Ideal A) [hW : W.IsPrime] (b : A) :
    Module.length (Localization.AtPrime (maximalIdeal A))
        (LocalizedModule (maximalIdeal A).primeCompl (A ⧸ (W ⊔ Ideal.span {b}))) =
      ordMod ⟨W, hW⟩ b := by
  have h := length_localizedModule_quot_eq (T := A ⧸ W) (maximalIdeal A).primeCompl W b
    (fun s hs => (notMem_maximalIdeal.mp hs).map _)
    (fun y => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨r, 1, (maximalIdeal A).primeCompl.one_mem, by simp⟩)
    (fun r hr => ⟨1, (maximalIdeal A).primeCompl.one_mem, by
      rw [one_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mp hr⟩)
    (fun v hv => Ideal.Quotient.eq_zero_iff_mem.mpr hv)
  rw [h, ordMod, Ring.ord, Ideal.Quotient.algebraMap_eq]

variable [IsDomain A] [IsNoetherianRing A]

theorem mem_minimalPrimes_iff {a : A} (ha : a ≠ 0) (W : Ideal A) [W.IsPrime] :
    W ∈ (Ideal.span {a}).minimalPrimes ↔ W.height = 1 ∧ a ∈ W := by
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  constructor
  · intro hW
    have haW : a ∈ W := hW.1.2 (Ideal.subset_span rfl)
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) W hW
    have h0 : W.height ≠ 0 := fun h => ha ((Ideal.mem_bot).mp (Ideal.height_eq_zero_iff_eq_bot.mp h ▸ haW))
    exact ⟨le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), haW⟩
  · rintro ⟨h1, haW⟩
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := W)
      ((Ideal.span_singleton_le_iff_mem W).mpr haW)
    rcases hQW.lt_or_eq with hlt | rfl
    · have := hQ.1.1
      have haQ : a ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
      have hbQ : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun h => ha ((Ideal.mem_bot).mp (h ▸ haQ))
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbQ
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at e1
      rw [h1] at e2
      have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add e1 le_rfl) e2
      exact absurd this (by decide)
    · exact hQ


omit [IsDomain A] [IsNoetherianRing A] in
theorem max_mem_minimalPrimes [IsLocalRing A] (h2 : ringKrullDim A = 2) (W : Ideal A) [hW : W.IsPrime]
    (h1 : W.height = 1) {b : A} (hbW : b ∉ W) (hbm : b ∈ maximalIdeal A) :
    maximalIdeal A ∈ (W ⊔ Ideal.span {b}).minimalPrimes := by
  have hle : W ⊔ Ideal.span {b} ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hW.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  refine ⟨⟨(maximalIdeal.isMaximal A).isPrime, hle⟩, fun Q hQ hQm => ?_⟩
  have := hQ.1
  by_contra hne
  have hlt : Q < maximalIdeal A := lt_of_le_of_ne hQm fun h => hne (h ▸ le_rfl)
  have hWQ : W < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
    hbW (h ▸ hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hWQ
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [h2, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hm
  rw [WithBot.coe_injective hm] at e2
  rw [h1] at e1
  have : (1 : ℕ∞) + 1 + 1 ≤ 2 := le_trans (add_le_add e1 le_rfl) e2
  exact absurd this (by decide)

end DimTwoSumReading


open DimTwoSumReading in
theorem DimTwoSumReading.proof : DimTwoSumReading.Statement := by
  intro A _ _ _ _ h2 a b ha hab
  classical
  have hT : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)).subset
      (fun p hp => (mem_minimalPrimes_iff ha p.asIdeal).mpr hp)
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal →
      (locCycle (Ideal.span {a}) p.asIdeal = ((ordLoc p a).toNat : ℤ) ∧ ordLoc p a ≠ ⊤) ∧
      (locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = ((ordMod p b).toNat : ℤ) ∧
        ordMod p b ≠ ⊤) := by
    intro p hp
    have hmin := (mem_minimalPrimes_iff ha p.asIdeal).mpr hp
    have hlA := length_loc_eq_ordLoc p.asIdeal a
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold locCycle; rw [dite_eq_left hmin]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlA
    · rw [← hlA]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmin
    by_cases hbm : b ∈ maximalIdeal A
    · have hmm := max_mem_minimalPrimes h2 p.asIdeal hp.1 (hab _ p.isPrime hp.1 hp.2) hbm
      have hlB := length_max_eq_ordMod p.asIdeal b
      refine ⟨?_, ?_⟩
      · unfold locCycle; rw [dite_eq_left hmm]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlB
      · rw [← hlB]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmm
    · have h0 : ordMod p b = 0 := Ring.ord_of_isUnit ((notMem_maximalIdeal.mp hbm).map _)
      have hnm : maximalIdeal A ∉ (p.asIdeal ⊔ Ideal.span {b}).minimalPrimes := fun h =>
        hbm (h.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      rw [h0]
      refine ⟨?_, ENat.zero_ne_top⟩
      unfold locCycle; rw [dite_eq_right hnm]; rfl
  have hsupp : Function.support (fun W : Ideal A => locCycle (Ideal.span {a}) W *
      locCycle (W ⊔ Ideal.span {b}) (maximalIdeal A)) ⊆
      (hT.toFinset.map ⟨PrimeSpectrum.asIdeal, by intro p q h; exact PrimeSpectrum.ext h⟩ : Finset (Ideal A)) := by
    intro W hW
    have hne : locCycle (Ideal.span {a}) W ≠ 0 := left_ne_zero_of_mul hW
    have hmin : W ∈ (Ideal.span {a}).minimalPrimes := by
      by_contra h
      exact hne (by unfold locCycle; rw [dite_eq_right h])
    have := hmin.1.1
    rw [Finset.coe_map, Set.Finite.coe_toFinset]
    exact ⟨⟨W, hmin.1.1⟩, (mem_minimalPrimes_iff ha W).mp hmin, rfl⟩
  refine ⟨∑ p ∈ hT.toFinset, (ordLoc p a).toNat * (ordMod p b).toNat, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    show locCycle (Ideal.span {a}) p.asIdeal * locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = _
    rw [hk.1.1, hk.2.1]
  · refine (finsum_mem_eq_finite_toFinset_sum (fun p => ordLoc p a * ordMod p b) hT).trans ?_
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    rw [ENat.natCast_toNat hk.1.2, ENat.natCast_toNat hk.2.2]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntermediateRingQuotLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Module Submodule
open scoped Pointwise

namespace IntermediateRingQuotLength

theorem smul_top_eq_span {A : Type*} [CommRing A] (a : A) :
    (a • ⊤ : Submodule A A) = Ideal.span {a} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

theorem length_quot_smul_le {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {M : Type*} [AddCommGroup M] [Module A M] (φ : A →ₗ[A] M)
    (hφ : Function.Injective φ) (htor : ∀ x : M, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range φ)
    {a : A} (ha : a ≠ 0) (hreg : Function.Injective fun x : M => a • x) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  rw [← smul_top_eq_span]
  have hLtop : Module.length A (A ⧸ (a • ⊤ : Submodule A A)) ≠ ⊤ := by
    rw [smul_top_eq_span]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
  let T : Submodule A M := a • ⊤
  have hfg : ∀ N : Submodule A M, N.FG → LinearMap.range φ ≤ N →
      Module.length A (N.map T.mkQ) ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := by
    intro N hN hφN
    have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
    let φN : A →ₗ[A] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hregN : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (hreg (congrArg Subtype.val h))
    have hfin : IsFiniteLength A (N ⧸ LinearMap.range φN) := by
      refine GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.isFiniteLength_of_torsion _
        fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule A N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule A N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.length_quot_smul_eq φN hφN'
      hregN hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)
  let S : Set ℕ := {n | ∃ N : Submodule A M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length A (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length A (A ⧸ (a • ⊤ : Submodule A A))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length A ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span A {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span A {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span A {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length A (N₀.map T.mkQ) < Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length A (M ⧸ T) = Module.length A (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := hfg N₀ hN₀ hφN₀

end IntermediateRingQuotLength

theorem IntermediateRingQuotLength.proof : IntermediateRingQuotLength.Statement.{u} := by
  intro A C _ _ _ _ _ _ hdim hinj hfrac a ha
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  have hI : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      mem_smul_pointwise_iff_exists, mem_top, true_and, Algebra.smul_def, mul_comm]
  have hreg : Function.Injective fun x : C => a • x := fun x y h => by
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using (map_ne_zero_iff _ hinj).mpr ha) h
  have htor : ∀ x : C, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range (Algebra.linearMap A C) := by
    intro x
    obtain ⟨c, hc, y, hy⟩ := hfrac x
    exact ⟨c, hc, y, by simpa using hy⟩
  rw [← (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})).length_eq, hI]
  exact IntermediateRingQuotLength.length_quot_smul_le (Algebra.linearMap A C) hinj htor ha hreg

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCyclePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem localizedModule_quot_nontrivial {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk (1 : R ⧸ J) 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨v, hv⟩ := h
  have hv' : ((v : R) : R ⧸ J) = 0 := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hv
  exact v.2 (hJW (Ideal.Quotient.eq_zero_iff_mem.mp hv'))

theorem LocCyclePos.proof : LocCyclePos.Statement := by
  intro R _ _ J W hW
  have : W.IsPrime := hW.1.1
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW
  unfold ReciprocityTheory.ChartRestriction.G.AI.locLen at hfin
  have := localizedModule_quot_nontrivial J W hW.1.2
  have hpos : 0 < Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.length_pos
  unfold locCycle
  rw [dite_eq_left hW]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only at hn
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_natCast, Nat.cast_pos]
  exact_mod_cast hpos

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

