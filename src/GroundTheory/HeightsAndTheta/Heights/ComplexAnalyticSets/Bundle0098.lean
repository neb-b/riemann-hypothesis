module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMGeneralPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets IsLocalRing

theorem isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by
  set S := Localization.AtPrime W
  set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)
  have hJm : J ≤ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hW.1.2
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro K hK
    have : K.IsPrime := hK.1.1
    have hKm : K ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal hK.1.1.ne_top
    have hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      Ideal.map_le_iff_le_comap.mp hK.1.2
    have hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W := by
      have h := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm
      rwa [show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from
        Localization.AtPrime.under_maximalIdeal] at h
    have hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW
    have hmK : maximalIdeal S ≤ K := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_le_iff_le_comap.mpr hWK
    rw [le_antisymm hKm hmK]
    exact maximalIdeal.isMaximal S
  have h0 : ringKrullDim (S ⧸ J) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim
  exact
    { exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }

theorem CMGeneralPoint.proof (hOpen : CMLocusOpen.Statement) : CMGeneralPoint.Statement := by
  intro n I W hW
  have : W.IsPrime := hW.1.1
  obtain ⟨g, hgW, hg⟩ :=
    hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)
  have hfin : (I.minimalPrimes \ {W}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset
  have hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W := by
    rintro W' ⟨hW', hne⟩
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc (hW.2 hW'.1 hc))
  choose! h hh using hsel
  refine ⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1
    · exact hgW h1
    · obtain ⟨W', hW', h2⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hh W' (hfin.mem_toFinset.mp hW')).2 h2
  · intro q hq hf
    rw [map_mul, map_prod] at hf
    have hg0 : eval q g ≠ 0 := left_ne_zero_of_mul hf
    have hp0 := right_ne_zero_of_mul hf
    refine ⟨fun W' hW' hqW' => ?_, ?_⟩
    · by_contra hne
      have hmem : W' ∈ I.minimalPrimes \ {W} := ⟨hW', hne⟩
      exact hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))
    · have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
        fun x hx => RingHom.mem_ker.mpr (hq x hx)
      exact hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightOneGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem isCohenMacaulayLocalRing_of_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hgW : g ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W := by rwa [Ideal.mk_ker]
  set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'
  have : W'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : W'.comap (Ideal.Quotient.mk J) = W := by
    rw [hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W := fun a => by
    rw [← Ideal.mem_comap, hcomap]
  have hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      obtain ⟨b, hb, hba⟩ := Submonoid.mem_map.mp hx
      change Ideal.Quotient.mk J a ∉ W'
      rw [← hba, hmem]
      exact hb
    · intro ha
      exact Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      W' := by
    have h := Vertical.SpecChart.isLocalization_quot W J
    rw [hsub] at h
    exact h
  have : IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.AtPrime.isLocalRing _ W'
  have : IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors W')
  set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
    (Ideal.Quotient.mk J g) with hx
  have hg0 : Ideal.Quotient.mk J g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx0 : x ≠ 0 := by
    intro h
    apply hg0
    have h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0 := by
      rw [map_zero]
      exact h
    exact IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0
  have hxm : x ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W']
    exact Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)
  have hheight : W'.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    apply hg0
    rw [← Ideal.mem_bot, ← h]
    exact (hmem g).mpr hgW
  refine { exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hxm
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b hab
    simp only [smul_eq_mul] at hab
    exact mul_left_cancel₀ hx0 hab
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]
    simp

theorem CMHeightOneGeneral.proof (hopen : CMLocusOpen.Statement) : CMHeightOneGeneral.Statement := by
  intro n J W g hJ hg hW
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  obtain ⟨f, hfW, hf⟩ := hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := fun p hp =>
    RingHom.mem_ker.mpr (hq p hp)
  exact hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMProjDimCriterion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

theorem exists_nat_eq_of_ne_bot_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe y =>
    have hy : y ≤ (d : ℕ∞) := by exact_mod_cast hle
    have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy
    exact ⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩

theorem quotient_mk_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]
  have h2 : (1 : S) ∈ maximalIdeal S := by
    have := sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

theorem mem_maximalIdeal_of_quotient_mk {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] {r : S} (hr : Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J)) : r ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  exact fun hu => hr (hu.map _)

theorem isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨rs0, hrs0, hofl, hlen0⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)
  have hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S := fun r hr => hofl ▸ Ideal.subset_span hr
  set d := rs0.length with hd_def
  have hcmS : IsCohenMacaulayLocalRing S :=
    { exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }
  have hsum := hcm S J hJ
  rw [← hlen0] at hsum
  obtain ⟨e, he⟩ := exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d)
    (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)
  have hht : J.height ≠ ⊤ := by
    intro h
    rw [h, he] at hsum
    have h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d := by exact_mod_cast hsum
    simp at h2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, J.height = h := ⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩
  have hhe : h + e = d := by
    rw [hh, he] at hsum; exact_mod_cast hsum
  have hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d :=
    GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)
  constructor
  · intro hCM
    obtain ⟨as, has_m, has_reg, has_len⟩ := hCM.exists_isWeaklyRegular
    obtain ⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as :=
      ⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by
        rw [List.map_map]; conv_rhs => rw [← List.map_id as]
        exact List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩
    have hmsreg : IsWeaklyRegular (S ⧸ J) ms := by
      rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]; exact has_reg
    have hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S := fun r hr =>
      mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))
    have hmslen : ms.length = e := by
      have : (as.length : WithBot ℕ∞) = e := has_len.symm.trans he
      rw [← hms, List.length_map] at this; exact_mod_cast this
    have hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d :=
      fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this
    refine ⟨d - e, ?_, ?_⟩
    · have := hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg
      rwa [hmslen] at this
    · rw [hh]; exact_mod_cast (by omega : d - e ≤ h)
  · rintro ⟨ℓ, hpd, hℓ⟩
    obtain ⟨ms, hmsm, hmsreg, hmslen⟩ := hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular
    have hℓh : ℓ ≤ h := by rw [hh] at hℓ; exact_mod_cast hℓ
    have hle : e ≤ ms.length := by rw [hmslen]; omega
    have hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e) := by
      have := hmsreg; rw [← List.take_append_drop e ms] at this
      exact ((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1
    refine { exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))
    · exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'
    · rw [he, List.length_map, List.length_take, min_eq_left hle]

theorem CMProjDimCriterion.proof (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by
  intro n I Q _ hIQ
  have : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q
  refine isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hIQ

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveRegularOffCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffCentre.proof (hG : CurveGermComponents.Statement) (hR : CurveRegularOffFinite.Statement)
    (hF : CurveProperClosedFinite.Statement) : CurveRegularOffCentre.Statement := by
  classical
  intro n I q hdim
  obtain ⟨N, hN, hcomp⟩ := hG n I q hdim
  have hZc : ∀ J : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet J) := fun J ↦ by
    have : zeroSet J = ⋂ p ∈ J, {x : Fin n → ℂ | eval x p = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ ↦ isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hM : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  set S := {W | W ∈ I.minimalPrimes ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1}
  have hS : S.Finite := hM.subset fun W hW ↦ hW.1
  choose! F hFfin hFchart using fun W (hW : W ∈ S) ↦ hR n W hW.1.1.1 hW.2
  have hnle : ∀ W ∈ S, ∀ W' ∈ I.minimalPrimes \ {W}, ¬ W' ≤ W := fun W hW W' hW' hle ↦
    hW'.2 (le_antisymm hle (hW.1.2 hW'.1.1 hle))
  set Bad := (⋃ W ∈ S, F W) ∪ ⋃ W ∈ S, ⋃ W' ∈ I.minimalPrimes \ {W}, zeroSet W ∩ zeroSet W'
  have hBad : Bad.Finite := (hS.biUnion hFfin).union (hS.biUnion fun W hW ↦
    hM.sdiff.biUnion fun W' hW' ↦ hF n W W' hW.1.1.1 hW.2 (hnle W hW W' hW'))
  have hN'o : IsOpen (interior N \ (Bad \ {q})) := isOpen_interior.sdiff hBad.sdiff.isClosed
  refine ⟨_, hN'o.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hN, fun h ↦ h.2 rfl⟩, ?_⟩
  rintro x ⟨hxI, hxN, hxB⟩ hxq
  have hxBad : x ∉ Bad := fun h ↦ hxB ⟨h, hxq⟩
  obtain ⟨W, hWm, hWd, -, hxW⟩ := hcomp x ⟨hxI, interior_subset hxN⟩
  have hWS : W ∈ S := ⟨hWm, hWd⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hWV⟩ :=
    hFchart W hWS x hxW fun h ↦ hxBad (Or.inl (Set.mem_biUnion hWS h))
  set V' := V ∩ interior N ∩ ⋂ W' ∈ I.minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hV' : IsOpen V' := (hV.inter isOpen_interior).inter
    (hM.sdiff.isOpen_biInter fun W' _ ↦ (hZc W').isOpen_compl)
  have hIV' : zeroSet I ∩ V' = zeroSet W ∩ V' := by
    ext z
    refine ⟨fun ⟨hzI, hzV⟩ ↦ ⟨?_, hzV⟩, fun ⟨hzW, hzV⟩ ↦ ⟨fun p hp ↦ hzW p (hWm.1.2 hp), hzV⟩⟩
    obtain ⟨W'', hW''m, -, -, hzW''⟩ := hcomp z ⟨hzI, interior_subset hzV.1.2⟩
    by_cases h : W'' = W
    · exact h ▸ hzW''
    · exact absurd hzW'' (Set.mem_iInter₂.1 hzV.2 W'' ⟨hW''m, h⟩)
  refine ⟨A, O ∩ g ⁻¹' V', V', g, hg.continuousOn.isOpen_inter_preimage hO hV', hV',
    ⟨⟨hxV, hxN⟩, Set.mem_iInter₂.2 fun W' hW' hxW' ↦ hxBad (Or.inr (Set.mem_biUnion hWS
      (Set.mem_biUnion hW' ⟨hxW, hxW'⟩)))⟩, hg.mono Set.inter_subset_left,
    fun y hy ↦ hAg y hy.1, ?_⟩
  rw [hIV', Set.image_inter_preimage, ← hWV]
  ext z
  exact ⟨fun ⟨hzW, hzV⟩ ↦ ⟨⟨hzW, hzV.1.1⟩, hzV⟩, fun ⟨⟨hzW, _⟩, hzV⟩ ↦ ⟨hzW, hzV⟩⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveResidueDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem CurveResidueDegree.proof : CurveResidueDegree.Statement := by
  intro n I q _ hdim P
  have := P.isMaximal
  let _ : Field (curveNormalisation I q ⧸ P.asIdeal) := Ideal.Quotient.field _

  have hO : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)

  have hIq : ∀ g ∈ I, eval q g = 0 := by
    intro g hg
    by_contra hgq
    have hu := isUnit_algebraMap_curveLocalRing I q g hgq
    have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
    rw [h0] at hu
    exact not_isUnit_zero hu

  let evL : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+* ℂ :=
    IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl) (g := eval q)
      (fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 (RingHom.mem_ker.2 h))
  have hJ : ∀ a ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))), evL a = 0 := by
    intro a ha
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))) ≤ RingHom.ker evL := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp [evL, IsLocalization.lift_eq, hIq g hg]
    exact hle ha
  let ε : curveLocalRing I q →+* ℂ := Ideal.Quotient.lift _ evL hJ
  let K := curveNormalisation I q ⧸ P.asIdeal
  let π : curveLocalRing I q →+* K := algebraMap (curveLocalRing I q) K
  let ι : ℂ →+* K := π.comp ((algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)).comp C)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  have hmax : (P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
  have hmax' := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))))
    Ideal.Quotient.mk_surjective (K := P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)))
    (H := hmax)
  have hloc := IsLocalRing.eq_maximalIdeal hmax'
  have hker : ∀ a ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ),
      π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) a) = 0 := by
    intro a ha
    rw [← Localization.AtPrime.under_maximalIdeal (I := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)),
      Ideal.under, Ideal.mem_comap, ← hloc] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hcomp : π = ι.comp ε := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl ?_
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = c := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (C c)) = c
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      rfl
    · have h1 : (X i - C (q i) : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker (eval q) := by simp
      have h2 := hker _ h1
      rw [map_sub, map_sub, sub_eq_zero] at h2
      show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = q i := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (X i)) = q i
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      exact h2

  have hint : ι.IsIntegral := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : IsIntegral (curveLocalRing I q) b := Algebra.IsIntegral.isIntegral b
    obtain ⟨p, hp, he⟩ := hb.map (Ideal.Quotient.mkₐ (curveLocalRing I q) P.asIdeal)
    refine ⟨p.map ε, hp.map ε, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp]
    exact he
  have hsurj : Function.Surjective ι := (IsAlgClosed.ringHom_bijective_of_isIntegral ι hint).2
  have hπ : Function.Surjective π := fun y ↦ by
    obtain ⟨c, hc⟩ := hsurj y
    exact ⟨_, hc⟩

  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx y ↦ ?_⟩
  obtain ⟨r, hr⟩ := hπ (y * x⁻¹)
  refine ⟨r, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  change π r * x = y
  rw [hr, mul_assoc, inv_mul_cancel₀ hx, mul_one]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRingUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def CMRingUnmixed.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsCohenMacaulayLocalRing A],
    ∀ p ∈ associatedPrimes A A, p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A

end GroundTheory.Heights₂.Heights
end

