module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkEquivOfFromSpecStalk
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncMeet

open IsLocalRing

theorem exists_stalk_equiv_of_fromSpecStalk (X : Scheme.{0}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ (h : X.fromSpecStalk x p ⤳ x)
      (e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal),
      ∀ g, e ((X.presheaf.stalkSpecializes h).hom g) = algebraMap _ _ g := by
  obtain ⟨e, he⟩ := GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x p.asIdeal
  have hs : X.fromSpecStalk x p ⤳ x := by
    have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hs, e, ?_⟩
  have hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    change e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) =
      algebraMap _ (Localization.AtPrime p.asIdeal) ((X.presheaf.germ U _ hxU).hom s)
    rw [h3]
    exact he U _ hxU s
  intro g
  exact congrArg (fun f => f.hom g) hcomp

theorem mem_asIdeal_iff (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) (y : X)
    (hy : y ⤳ x) (hp : X.fromSpecStalk x p = y) (g : X.presheaf.stalk x) :
    g ∈ p.asIdeal ↔ (X.presheaf.stalkSpecializes hy).hom g ∈ maximalIdeal (X.presheaf.stalk y) := by
  subst hp
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 : g ∈ p.asIdeal ↔ algebraMap _ (Localization.AtPrime p.asIdeal) g ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal) p.asIdeal g).symm
  rw [h1, ← he g, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MulEquiv.isUnit_map]

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_algebraMap_of_isUnit (x : X) (g : X.presheaf.stalk x) (hg : IsUnit g) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg.ne_zero
    rw [Scheme.ord_eq_iff hx hne]
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change Ring.ordFrac _ _ = _
    rw [Ring.ordFrac_of_isUnit hg]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

theorem ord_algebraMap_ne_zero (x : X) (hx : Order.coheight x = 1) (g : X.presheaf.stalk x)
    (hg0 : g ≠ 0) (hg : g ∈ maximalIdeal (X.presheaf.stalk x)) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x ≠ 0 := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg0
  intro h0
  rw [Scheme.ord_eq_iff hx hne] at h0
  change Ring.ordFrac _ _ = _ at h0
  rw [Ring.ordFrac_eq_ord _] at h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0))
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hg0) hm.symm] at h0
  have hm0 : m = 0 := by
    have h4 : (m : ℤ) = 0 := Multiplicative.ofAdd.injective (WithZero.coe_injective h0)
    exact_mod_cast h4
  subst hm0
  have h2 : Ring.ord (X.presheaf.stalk x) g = 0 := by rw [← hm]; rfl
  rw [Ring.ord] at h2
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h2
  exact (mem_maximalIdeal g).1 hg h2


open IsLocalRing in
theorem exists_meet_point : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ v σ w : Y, v ∈ B → σ ∈ B → Order.coheight v = 1 → Order.coheight σ = 1 → v ≠ σ → v ⤳ w → σ ⤳ w → ∃ (w' : Y) (t u : Y.presheaf.stalk w'), w' ⤳ w ∧ v ⤳ w' ∧ σ ⤳ w' ∧ ringKrullDim (Y.presheaf.stalk w') = 2 ∧ Ideal.span {t, u} = IsLocalRing.maximalIdeal (Y.presheaf.stalk w') ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField t) σ = 1 ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField u) v = 1 ∧ ∀ v' ∈ B, Order.coheight v' = 1 → v' ⤳ w' → v' = v ∨ v' = σ := by
  classical
  intro Y _ _ q n _ B hB v σ w hvB hσB hv hσ hvσ hvw hσw
  obtain ⟨U, hwU, z, J, wf, uf, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB w
  obtain ⟨j', hj'J, rfl⟩ := (hc.mem v hvw hv).1 hvB
  obtain ⟨j, hjJ, rfl⟩ := (hc.mem σ hσw hσ).1 hσB
  have hjj : j ≠ j' := fun h => hvσ (by rw [h])
  haveI : IsRegularLocalRing (Y.presheaf.stalk w) := (hB w).1
  have hUmem : ∀ y : Y, y ⤳ w → y ∈ U := fun y hy => hy.mem_open U.isOpen hwU
  have hgerm : ∀ (y : Y) (hy : y ⤳ w) (i : Fin n),
      (Y.presheaf.stalkSpecializes hy).hom (Y.presheaf.germ U w hwU (z i)) =
        Y.presheaf.germ U y (hUmem y hy) (z i) := fun y hy i => by
    rw [← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hwU hy]; rfl
  have hfn : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J →
      algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hy (z i)) =
        (uf i : Y.functionField) := fun y hy i hi => by
    rw [GlobalTheory.Cartier.algebraMap_germ hy, hc.val i hi]
  have hgne : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J → Y.presheaf.germ U y hy (z i) ≠ 0 :=
    fun y hy i hi h0 => (uf i).ne_zero (by rw [← hfn y hy i hi, h0, map_zero])
  have hmy : ∀ i (hi : i ∈ J), Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i) ∈
      maximalIdeal (Y.presheaf.stalk (wf i)) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have h1 := GlobalTheory.SncMeet.ord_algebraMap_of_isUnit _ _ hu
    rw [hfn _ _ i hi, hc.ord_self i hi] at h1
    exact one_ne_zero h1
  have hm : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ maximalIdeal (Y.presheaf.stalk w) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U w hwU (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have hu' := hu.map (Y.presheaf.stalkSpecializes (hc.spec i hi)).hom
    rw [hgerm] at hu'
    exact (mem_maximalIdeal _).1 (hmy i hi) hu'
  have hli := _root_.GlobalTheory.CotIndep.linearIndependent_cotangent_of_isFrame Y q n U z hc.frame w hwU J (fun i => hm i.1 i.2)

  have hi2 : Function.Injective (![⟨j, hjJ⟩, ⟨j', hj'J⟩] : Fin 2 → J) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hjj (by simpa using congrArg Subtype.val hkl)).elim
    · exact (hjj (by simpa using (congrArg Subtype.val hkl).symm)).elim
    · rfl
  have hli2 := hli.comp _ hi2
  obtain ⟨hPp, hPh⟩ := _root_.GlobalTheory.PointSep.span_pair_isPrime_and_height_eq_two (Y.presheaf.stalk w) (Y.presheaf.germ U w hwU (z j))
    (Y.presheaf.germ U w hwU (z j')) (hm j hjJ) (hm j' hj'J) (by
      convert hli2 using 1
      funext k; fin_cases k <;> rfl)
  let pt : PrimeSpectrum (Y.presheaf.stalk w) :=
    ⟨Ideal.span {Y.presheaf.germ U w hwU (z j), Y.presheaf.germ U w hwU (z j')}, hPp⟩
  obtain ⟨hw', e, he⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pt
  have K1 : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal →
      wf i ⤳ Y.fromSpecStalk w pt := by
    intro i hi hiP
    obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem _).2 hiP)
    have hQp : Q.IsPrime := hQmin.1.1
    have hbQ : Y.presheaf.germ U w hwU (z i) ∈ Q := hQmin.1.2 (Ideal.mem_span_singleton_self _)
    have hQh1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin
    have hQ0 : Q ≠ ⊥ := fun h => hgne w hwU i hi (by rw [h] at hbQ; exact Ideal.mem_bot.1 hbQ)
    have hQh : Q.height = 1 := by
      refine le_antisymm hQh1 ?_
      rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hQ0
    let pQ : PrimeSpectrum (Y.presheaf.stalk w) := ⟨Q, hQp⟩
    obtain ⟨hQw, -, -⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pQ
    have hcoh : Order.coheight (Y.fromSpecStalk w pQ) = 1 := by
      rw [GlobalTheory.SncMeet.coheight_fromSpecStalk]; exact_mod_cast hQh
    have hsp : Y.fromSpecStalk w pQ ⤳ Y.fromSpecStalk w pt :=
      ((PrimeSpectrum.le_iff_specializes pQ pt).1 hQle).map (Y.fromSpecStalk w).continuous
    have hmem : Y.presheaf.germ U _ (hUmem _ hQw) (z i) ∈
        maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk w pQ)) := by
      rw [← hgerm _ hQw i]; exact (GlobalTheory.SncMeet.mem_asIdeal_iff Y w pQ _ hQw rfl _).1 hbQ
    have hord := GlobalTheory.SncMeet.ord_algebraMap_ne_zero _ hcoh _ (hgne _ _ i hi) hmem
    rw [hfn _ _ i hi] at hord
    have heq : Y.fromSpecStalk w pQ = wf i := by
      by_contra hne; exact hord (hc.ord_other i hi _ hQw hne)
    rw [← heq]; exact hsp
  have hPh' : pt.asIdeal.height = 2 := hPh
  have ht : ∀ g, (Y.presheaf.stalkSpecializes hw').hom g =
      e.symm (algebraMap _ (Localization.AtPrime pt.asIdeal) g) := fun g => by
    rw [← he g, RingEquiv.symm_apply_apply]
  refine ⟨Y.fromSpecStalk w pt, (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
    (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j')), hw',
    K1 j' hj'J (Ideal.subset_span (by simp)), K1 j hjJ (Ideal.subset_span (by simp)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height pt.asIdeal, hPh']
    rfl
  · have h1 : Ideal.span {(Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
        (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j'))} =
        Ideal.map e.symm (Ideal.map (algebraMap _ (Localization.AtPrime pt.asIdeal)) pt.asIdeal) := by
      rw [ht, ht]
      show _ = Ideal.map e.symm (Ideal.map _ (Ideal.span _))
      simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [h1, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.symm)
  · rw [hgerm _ hw' j, hfn _ _ j hjJ]; exact hc.ord_self j hjJ
  · rw [hgerm _ hw' j', hfn _ _ j' hj'J]; exact hc.ord_self j' hj'J
  · intro v' hv'B hv'1 hv'w'
    have hv'w := hv'w'.trans hw'
    obtain ⟨i, hi, rfl⟩ := (hc.mem v' hv'w hv'1).1 hv'B
    by_contra hcon
    rw [not_or] at hcon
    have hij' : i ≠ j' := fun h => hcon.1 (by rw [h])
    have hij : i ≠ j := fun h => hcon.2 (by rw [h])
    obtain ⟨pi, hpi⟩ : wf i ∈ Set.range (Y.fromSpecStalk w) := by
      rw [Scheme.range_fromSpecStalk]; exact hv'w
    have hle : pi.asIdeal ≤ pt.asIdeal := by
      have h1 : Y.fromSpecStalk w pi ⤳ Y.fromSpecStalk w pt := hpi ▸ hv'w'
      exact (PrimeSpectrum.le_iff_specializes pi pt).2
        ((IsPreimmersion.isEmbedding (Y.fromSpecStalk w)).specializes_iff.1 h1)
    have hciP : Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal := by
      apply hle
      rw [GlobalTheory.SncMeet.mem_asIdeal_iff Y w pi (wf i) (hc.spec i hi) hpi, hgerm]
      exact hmy i hi
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hciP
    refine hli.notMem_span_image (s := {⟨j, hjJ⟩, ⟨j', hj'J⟩}) (x := ⟨i, hi⟩) ?_ ?_
    · simp [Subtype.ext_iff, hij, hij']
    · have hsum : (⟨Y.presheaf.germ U w hwU (z i), hm i hi⟩ : maximalIdeal (Y.presheaf.stalk w)) =
          r • ⟨Y.presheaf.germ U w hwU (z j), hm j hjJ⟩ +
            s • ⟨Y.presheaf.germ U w hwU (z j'), hm j' hj'J⟩ := by
        ext; simp [← hrs, smul_eq_mul]
      show (maximalIdeal _).toCotangent ⟨_, _⟩ ∈ _
      rw [hsum, map_add (f := _), map_smul, map_smul]
      exact Submodule.add_mem _
        (Submodule.smul_of_tower_mem _ r (Submodule.subset_span ⟨⟨j, hjJ⟩, by simp, rfl⟩))
        (Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨⟨j', hj'J⟩, by simp, rfl⟩))

end GlobalTheory.SncMeet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.LamBridge

section Charts

variable {X X' Y : Scheme.{0}}

def cpTrans {A'' A' A : LB Y} (c₁ : ChartPull A'' A' (𝟙 Y)) (c₂ : ChartPull A' A (𝟙 Y)) : ChartPull A'' A (𝟙 Y) where
  idx i := c₂.idx (c₁.idx i)
  le i _ hy := c₂.le _ (c₁.le i hy)
  g y i j hi hj := (c₁.g y i j hi hj).trans (c₂.g y _ _ (c₁.le i hi) (c₁.le j hj))

def cpDiv {A' A B' B : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull B' B (𝟙 Y)) :
    ChartPull (LB.div B' A') (LB.div B A) (𝟙 Y) where
  idx p := (b.idx p.1, a.idx p.2)
  le p _ hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := (gm_div A' B' (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans (by rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1])
    (gm_div A B (𝟙 Y) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
      ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, ⟨b.le _ hq.1, a.le _ hq.2⟩⟩).symm)

def cpEquiv (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (E : K' ≃ K) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hφ : ∀ k, φ' k = φ (E k)) (hε : ∀ k, ε' k = ε (E k)) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) (𝟙 Y) :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart L φ (fun k => j (E.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have h := Set.mem_iInter.1 hy (E.symm k)
      rw [hφ, E.apply_symm_apply] at h
      exact h
  { idx := fun j k => j (E.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Fintype.prod_equiv E _ _ fun k => ?_
      rw [E.symm_apply_apply, hφ, hε] }

def cpFlat (L : LB X) {I K : Type} [Fintype I] [Fintype K] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) : ChartPull (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb (LB.LinComb L ψ δ) σ e) (𝟙 Y) :=
  have le : ∀ j : I × K → L.ι, LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) j ≤
      (𝟙 Y) ⁻¹ᵁ LB.wchart (LB.LinComb L ψ δ) σ (fun i k => j (i, k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { idx := fun j i k => j (i, k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L ψ δ) σ e (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i)
        (gm_linComb L ψ δ (𝟙 Y ≫ σ i) y (fun k => j (i, k)) (fun k => j' (i, k))
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul, mul_comm (δ k), Category.assoc] }

end Charts

def e4 : Fin 4 ≃ ULift.{0} (Finset (Fin 2)) where
  toFun k := ⟨(![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k⟩
  invFun I := if I.down = {0, 1} then 0 else if I.down = {0} then 1 else if I.down = {1} then 2 else 3
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro I; revert I; decide

theorem finFourEquivSubsetsFinTwo_down_eq (k : Fin 4) : (e4 k).down = (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k := rfl

theorem mumfordSign_finFourEquivSubsetsFinTwo (k : Fin 4) : Oε k = (-1) ^ (2 - (e4 k).down.card) := by
  fin_cases k <;> decide

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem lift_psum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (I : Finset (Fin 2)) :
    (lift u v).left ≫ (psum B (x2 B) I).left = (psum B ![u, v] I).left := by
  rw [← Over.comp_left, comp_psum]
  congr 2
  funext k
  fin_cases k <;> simp [x2]

theorem mumfordBundleFourPoints_eq_lift_comp_partialSum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (k : Fin 4) :
    lamPts u v k = (lift u v).left ≫ (psum B (x2 B) (e4 k).down).left := by
  rw [lift_psum]
  fin_cases k
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_01 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_0 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_1 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_e B u v).symm

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem finFourEquivSubsetsFinTwo_symm_apply (I : ULift.{0} (Finset (Fin 2))) :
    (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) (e4.symm I) = I.down := by
  rw [← finFourEquivSubsetsFinTwo_down_eq, Equiv.apply_symm_apply]

theorem exists_iso_tens : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  intro S₀ S B₀ _ _ B _ _ L₀ M hL₀ hM β₂ wR hw r W Y x φ ε hφ hε
  let σ : Fin r × Fin r → (Y.left ⟶ (G2 B₀).left) := fun ab => (lift (x ab.1) (x ab.2)).left
  let e : Fin r × Fin r → ℤ := fun ab => W ab.1 ab.2
  let v₁ := transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) wR σ e
  have hv₁ : v₁.IsGen := isGen_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) hw σ e
  let cA : ChartPull (LB.LinComb L₀ (tensφ x) (tensε W)) (LB.LinComb (abelian₂ B₀ L₀) σ e) (𝟙 Y.left) :=
    cpTrans (cpEquiv L₀ (Equiv.prodCongr (Equiv.refl _) e4)
      (fun p : (Fin r × Fin r) × ULift.{0} (Finset (Fin 2)) => σ p.1 ≫ (psum B₀ (x2 B₀) p.2.down).left)
      (fun p => e p.1 * (-1) ^ (2 - p.2.down.card)) _ _
      (fun k => mumfordBundleFourPoints_eq_lift_comp_partialSum (x k.1.1) (x k.1.2) k.2)
      (fun k => by
        show W k.1.1 k.1.2 * Oε k.2 = W k.1.1 k.1.2 * (-1) ^ (2 - (e4 k.2).down.card)
        rw [mumfordSign_finFourEquivSubsetsFinTwo]))
      (cpFlat L₀ (fun I : ULift.{0} (Finset (Fin 2)) => (psum B₀ (x2 B₀) I.down).left)
        (fun I => (-1) ^ (2 - I.down.card)) σ e)
  let cB : ChartPull ((LB.LinComb M φ ε).pull (𝟙 Y.left))
      (LB.LinComb (abelian₂ B M) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)) (𝟙 Y.left) :=
    cpTrans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (LB.LinComb M φ ε) (𝟙 Y.left) (𝟙 Y.left) rfl)
      (cpTrans (cpEquiv M (Equiv.prodCongr (Equiv.prodPUnit _).symm e4)
        (fun q : ((Fin r × Fin r) × PUnit) × ULift.{0} (Finset (Fin 2)) =>
          (σ q.1.1 ≫ β₂) ≫ (psum B (x2 B) q.2.down).left)
        (fun q => (e q.1.1 * 1) * (-1) ^ (2 - q.2.down.card)) φ ε
        (fun k => by rw [hφ k]; exact (Category.assoc _ _ _).symm)
        (fun k => by
          show ε k = (W k.1.1 k.1.2 * 1) * (-1) ^ (2 - (e4 k.2).down.card)
          rw [hε k, mumfordSign_finFourEquivSubsetsFinTwo, _root_.mul_one]))
        (cpFlat M (fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left)
          (fun I => (-1) ^ (2 - I.down.card)) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)))
  let c := cpDiv cA cB
  refine ⟨cGen c v₁, cGen_isGen c hv₁, fun Z q z J J₀ hJ hJ₀ => ?_⟩
  have hm : q z ∈ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y.left)) (LB.LinComb L₀ (tensφ x) (tensε W))).U
      (fun _ k => J (q ≫ 𝟙 Y.left ≫ φ k), fun k => J₀ (q ≫ tensφ x k)) :=
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (q ≫ 𝟙 Y.left ≫ φ k),
      Set.mem_iInter.2 fun k => hJ₀ (q ≫ tensφ x k)⟩
  refine (gm_res q z _ hm _).trans ((gm_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1)
    wR σ e q z (c.idx _) (c.le _ hm)).trans ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => congrArg (· ^ W a b) ?_
  unfold GlobalTheory.PolDeg.lamVal
  have key : ∀ P P', P = P' → gm (q ≫ σ (a, b)) z _ (wR.s P) = gm (q ≫ σ (a, b)) z _ (wR.s P') := by
    rintro _ _ rfl; rfl
  refine key _ _ (Prod.ext (funext fun _ => funext fun I => ?_) (funext fun I => ?_))
  · show J _ = J _
    congr 1
    show q ≫ 𝟙 Y.left ≫ φ ((a, b), e4.symm I) = _
    rw [hφ]
    simp only [finFourEquivSubsetsFinTwo_symm_apply, Category.assoc, Category.id_comp]
  · show J₀ _ = J₀ _
    congr 1
    show q ≫ lamPts (x a) (x b) (e4.symm I) = _
    rw [mumfordBundleFourPoints_eq_lift_comp_partialSum, e4.apply_symm_apply, Category.assoc]

end GlobalTheory.Mum.LamBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.ToricLabel

theorem exists_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi lam
  have hj : IsLocalHom j := GlobalTheory.UPoinc.ClosedPt.isLocalHom_of_isCpl hCpl
  have hk0 : S.r * S.N ≠ 0 := Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)
  haveI : NeZero (S.r * S.N) := ⟨hk0⟩
  set ζR : R := j ((M.stalkEquiv x).symm (algebraMap o' (M.O x) S.ζ)) with hζR
  have hζpow : ζR ^ ((S.r * S.N) ^ 2) = 1 := by
    rw [hζR, ← map_pow, ← map_pow, ← map_pow, S.prim.pow_eq_one, map_one, map_one, map_one]
  let u0 : Rˣ := Units.ofPowEqOne ζR ((S.r * S.N) ^ 2) hζpow (pow_ne_zero 2 hk0)
  have hu0 : ((u0 : Rˣ) : R) = ζR := Units.val_ofPowEqOne _ _ _ _
  let w : Rˣ := u0 ^ (S.r * S.N)
  have hw : w ^ (S.r * S.N) = 1 := by
    rw [← pow_mul, ← sq]; ext; rw [Units.val_pow_eq_pow_val, hu0, hζpow, Units.val_one]
  let τ : Multiplicative D.toPre.X →* Rˣ :=
    { toFun := fun χ => w ^ (lam (Multiplicative.toAdd χ)).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [toAdd_mul, map_add (f := _), ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add] }
  have hτ : τ ^ (S.r * S.N) = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show (w ^ (lam (Multiplicative.toAdd χ)).val) ^ (S.r * S.N) = 1
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hpb (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  obtain ⟨s, hs, hspec⟩ := GlobalTheory.ToricTorsionSpec.main R hBase G hsemi D A U (S.r * S.N) (Nat.one_le_iff_ne_zero.2 hk0) τ hτ
  obtain ⟨b, hb⟩ := GlobalTheory.Poinc.LabIndex.torsion_section_label o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi s hs
  refine ⟨b, ?_⟩
  intro p _ y ev hCen hy y₀ hAt u ε hBC τ' hτ' q x' hq hTor hQk
  obtain ⟨ev₀, hloc, hD, bc, hmon, hpull, hxe, hev, t, ht1, ht2⟩ := hBC
  haveI : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hring : (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp ((algebraMap u.V (FractionRing u.V)).comp ev₀) =
      (OO p).subtype.comp ev := RingHom.ext hev
  have hζ : ((ev ζR : OO p) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) := by
    rw [hζR, GlobalTheory.Poinc.TestAtPt.val_gPt_of_stalk o' Ω M x R j hj p y ev hy, hAt]
    rfl
  have hchar : ∀ χ', ((τ' χ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) = algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R))) := by
    intro χ'
    obtain ⟨χ, hχ⟩ := ε.surjective (Multiplicative.toAdd χ')
    have e1 : χ' = Multiplicative.ofAdd (ε χ) := by rw [hχ]; rfl
    subst e1
    rw [hτ' χ, hev]
    simp only [toAdd_ofAdd, hxe]
    show _ = ((ev (((w ^ (lam χ).val : Rˣ) : R)) : OO p) : PadicAlgCl p)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu0, map_pow, map_pow, SubmonoidClass.coe_pow,
      SubmonoidClass.coe_pow, hζ, ← pow_mul]
  have key := hspec u.V u.complete ev₀ hloc u.G bc hmon u.D u.A hD u.U hpull (PadicAlgCl p) τ' hchar q x' hq hTor hQk
  have h2 := hb p y ev hCen hy y₀ hAt (x'.left ≫ t) (by
    rw [Category.assoc, ht2, ← hring]
    simpa only [Category.assoc] using congrArg (· ≫ gm) key)
  rw [Category.assoc, ht1] at h2
  exact h2

end GlobalTheory.Poinc.ToricLabel
end
end

