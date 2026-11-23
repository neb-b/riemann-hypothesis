module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleLocalQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem length_self_eq_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

private theorem length_localizedModule_quot {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem LocCycleLocalQuot.proof (h₂ : LocalQuotPrimes.Statement.{u}) : LocCycleLocalQuot.Statement.{u} := by
  intro R _ P U _ J W hPJ hW hPW hWU
  obtain ⟨hup, hdown⟩ := h₂ R P U (hPW.trans hWU)
  obtain ⟨hpW, hcW⟩ := hup W hW hPW hWU

  have hmin : W ∈ J.minimalPrimes ↔ W.map (localQuotMap P U) ∈ (J.map (localQuotMap P U)).minimalPrimes := by
    constructor
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hpW, Ideal.map_mono hJW⟩, fun q hq hqW => ?_⟩
      have := hq.1
      obtain ⟨hPq, hqU, hqe⟩ := hdown q hq.1
      have h := hm ⟨Ideal.comap_isPrime _ q, Ideal.le_comap_map.trans (Ideal.comap_mono hq.2)⟩
        ((Ideal.comap_mono hqW).trans hcW.le)
      rw [← hqe]
      exact Ideal.map_mono h
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hW, Ideal.le_comap_map.trans ((Ideal.comap_mono hJW).trans hcW.le)⟩, fun Q hQ hQW => ?_⟩
      obtain ⟨hQp, hQc⟩ := hup Q hQ.1 (hPJ.trans hQ.2) (hQW.trans hWU)
      have h := hm ⟨hQp, Ideal.map_mono hQ.2⟩ (Ideal.map_mono hQW)
      rw [← hcW, ← hQc]
      exact Ideal.comap_mono h
  unfold locCycle
  by_cases h : W ∈ J.minimalPrimes
  swap
  · rw [dite_eq_right h, dite_eq_right (mt hmin.2 h)]
  rw [dite_eq_left h, dite_eq_left (hmin.1 h)]
  have := hW
  have := hpW
  set φ := localQuotMap P U with hφ
  obtain ⟨p, hp⟩ : ∃ p, W.map φ = p := ⟨_, rfl⟩
  rw [hp] at hpW hcW
  have := hpW
  have hφp : ∀ x : R, φ x ∈ p ↔ x ∈ W := fun x => by rw [← Ideal.mem_comap, hcW]

  have hrep : ∀ a : localQuot P U, ∃ r u : R, u ∉ U ∧ a * φ u = φ r := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b
    refine ⟨r, u, u.2, ?_⟩
    simp only [hφ, localQuotMap, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hnum : ∀ (t : localQuot P U) (r' u' : R), t ∉ p → u' ∉ U → t * φ u' = φ r' → r' ∉ W := by
    intro t r' u' ht hu' hr' hmem
    rw [← hφp, ← hr'] at hmem
    rcases hpW.mem_or_mem hmem with h | h
    · exact ht h
    · exact hu' (hWU ((hφp u').1 h))
  let ψ : (Localization.AtPrime W) →+* (Localization.AtPrime p) := Localization.localRingHom W p φ hcW.symm
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨r, u, hu, hr⟩ := hrep a
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hs : r' * u ∈ W.primeCompl :=
      W.primeCompl.mul_mem (hnum t r' u' t.2 hu' hr') fun h => hu (hWU h)
    refine ⟨IsLocalization.mk' _ (r * u') ⟨r' * u, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    linear_combination (φ r) * hr' - (φ r') * hr

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap R (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hr'W := hnum t r' u' ht hu' hr'
    have h0 : φ (r' * r) = 0 := by
      rw [map_mul, ← hr', mul_right_comm, htr, zero_mul]
    rw [hφ, localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      IsLocalization.mem_map_algebraMap_iff U.primeCompl] at h0
    obtain ⟨⟨⟨i, hi⟩, v⟩, hv⟩ := h0
    rw [← map_mul, IsLocalization.eq_iff_exists U.primeCompl] at hv
    obtain ⟨c, hc⟩ := hv
    have hcW : (c : R) * r' * v ∈ W.primeCompl :=
      W.primeCompl.mul_mem (W.primeCompl.mul_mem (fun h => c.2 (hWU h)) hr'W) fun h => v.2 (hWU h)
    have hmemP : (c : R) * r' * v * r ∈ P := by
      have : (c : R) * (r' * r * v) = c * r' * v * r := by ring
      rw [← this, hc]
      exact P.mul_mem_left _ hi
    have hrJ : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, hcW⟩), ← map_mul]
      exact Ideal.mem_map_of_mem _ (hPJ hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  let : CommRing (Localization.AtPrime p) := inferInstance
  have hcomp : ψ.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (localQuot P U) (Localization.AtPrime p)).comp φ :=
    RingHom.ext fun x => Localization.localRingHom_to_map W p φ hcW.symm x
  have hI : (J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)) = (J.map (algebraMap R (Localization.AtPrime W))).map ψ := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  let g := (Ideal.Quotient.mk ((J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)))).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [← length_localizedModule_quot, ← length_localizedModule_quot] at key
  subst hp
  exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem mem_minimalPrimes_of_locCycle_ne_zero {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dite_eq_right hc])

theorem LocalCoeffRing.proof (h₁ : LocalQuotRing.Statement.{u}) (h₂ : LocalQuotPrimes.Statement.{u})
    (h₃ : LocCycleLocalQuot.Statement.{u}) (h₄ : LocalQuotColon.Statement.{u})
    (h₅ : LocalQuotFinsum.Statement.{u}) (h₆ : LocalCoeffLocal.Statement.{u}) :
    LocalCoeffRing.Statement.{u} := by
  intro R _ _ P U hP hU hPU hchain f g s u v hf hg hs hu huv hno
  have := hU
  obtain ⟨hdom, hloc, hunit, hker⟩ := h₁ R P U hP hPU
  have := hdom
  have := hloc
  obtain ⟨hup, hdown⟩ := h₂ R P U hPU
  have hmin := fun {J W : Ideal R} (h : locCycle J W ≠ 0) => mem_minimalPrimes_of_locCycle_ne_zero h
  have hmin' := fun {J W : Ideal (localQuot P U)} (h : locCycle J W ≠ 0) =>
    mem_minimalPrimes_of_locCycle_ne_zero h

  have hm : IsLocalRing.maximalIdeal (localQuot P U) = U.map (localQuotMap P U) := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not]
  have hUc : (U.map (localQuotMap P U)).comap (localQuotMap P U) = U := (hup U hU hPU le_rfl).2
  have hPbot : P.map (localQuotMap P U) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr fun y hy => RingHom.mem_ker.mpr ((hker y).2 hy)
  have hmapx : ∀ x : R, (P ⊔ Ideal.span {x}).map (localQuotMap P U) =
      Ideal.span {localQuotMap P U x} := by
    intro x
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hPbot, bot_sup_eq]

  have hchain' : ∀ Q₁ Q₂ : Ideal (localQuot P U), Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ →
      Q₂ < IsLocalRing.maximalIdeal (localQuot P U) → False := by
    intro Q₁ Q₂ hQ₁ hQ₂ h0 h12 h2m
    obtain ⟨hP1, -, he1⟩ := hdown Q₁ hQ₁
    obtain ⟨-, hU2, he2⟩ := hdown Q₂ hQ₂
    exact hchain _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _)
      (lt_of_le_of_ne hP1 fun h => h0.ne (by rw [← he1, ← h, hPbot]))
      (lt_of_le_of_ne (Ideal.comap_mono h12.le) fun h => h12.ne (by rw [← he1, ← he2, h]))
      (lt_of_le_of_ne hU2 fun h => h2m.ne (by rw [← he2, h, hm]))
  have hne : ∀ x : R, x ∉ P → localQuotMap P U x ≠ 0 := fun x hx h => hx ((hker x).1 h)
  have hloc' := h₆ (localQuot P U) hchain' (localQuotMap P U f) (localQuotMap P U g)
    (localQuotMap P U s) (localQuotMap P U u) (localQuotMap P U v) (hne f hf) (hne g hg) (hne s hs)
    ((hunit _).2 fun h => hu (hUc ▸ Ideal.mem_comap.mpr h))
    (by rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]; exact (hker _).2 huv) ?_
  swap
  ·
    intro W hW
    have hWm := hmin' hW
    have := hWm.1.1
    obtain ⟨hPW, hWU, hWe⟩ := hdown W hWm.1.1
    have h := hno (W.comap (localQuotMap P U)) hWU
    rw [h₃ R P U _ _ le_sup_left inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {f}) _ le_sup_left
      inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {g}) _ le_sup_left inferInstance hPW hWU,
      hmapx, hmapx, hmapx, hWe] at h
    exact h hW
  rw [hm] at hloc'
  convert hloc' using 1
  ·
    apply h₅ R P U hPU
    · intro G hG
      have hGU : G ≤ U := le_sup_left.trans (hmin (right_ne_zero_of_mul hG)).1.2
      have h2 := left_ne_zero_of_mul hG
      by_cases h : locCycle (P ⊔ Ideal.span {f}) G = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact ⟨(hmin h2).1.1, le_sup_left.trans (hmin h2).1.2, hGU⟩
      · exact ⟨(hmin h).1.1, le_sup_left.trans (hmin h).1.2, hGU⟩
    · intro p hp
      have h2 := left_ne_zero_of_mul hp
      by_cases h : locCycle (Ideal.span {localQuotMap P U f}) p = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact (hmin' h2).1.1
      · exact (hmin' h).1.1
    · intro G hG hPG hGU
      rw [h₃ R P U _ G le_sup_left hG hPG hGU, h₃ R P U (P ⊔ Ideal.span {g}) G le_sup_left hG hPG hGU,
        h₃ R P U (G ⊔ Ideal.span {s}) U (le_sup_of_le_left hPG) hU hPU le_rfl, hmapx, hmapx,
        Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ·
    apply h₅ R P U hPU
    · intro W hW
      have h1 := hmin (left_ne_zero_of_mul hW)
      have h2 := hmin (right_ne_zero_of_mul hW)
      exact ⟨h1.1.1, le_sup_left.trans h1.1.2, le_sup_left.trans h2.1.2⟩
    · intro p hp
      exact (hmin' (left_ne_zero_of_mul hp)).1.1
    · intro W hW hPW hWU
      rw [h₃ R P U _ W le_sup_left hW hPW hWU, h₃ R P U (W ⊔ _) U (le_sup_of_le_left hPW) hU hPU le_rfl,
        hmapx, Ideal.map_sup, h₄ R P U f g]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotColon
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotColon.proof : LocalQuotColon.Statement.{u} := by
  intro R _ P U _ f g
  set S := Localization.AtPrime U
  set I := P.map (algebraMap R S)
  have hφ : ∀ x : R, localQuotMap P U x = Ideal.Quotient.mk I (algebraMap R S x) := fun _ => rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hp0 : localQuotMap P U p = 0 := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hp
    refine Ideal.mem_span_singleton'.mpr ⟨localQuotMap P U a, ?_⟩
    rw [← map_mul, ← map_mul, ← hpz, map_add (f := _), hp0, zero_add, map_mul]
  · intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl y0
    obtain ⟨⟨r', t'⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b0
    simp only [hφ] at hb
    have hI := Ideal.Quotient.eq.mp hb
    have e1 := IsLocalization.mk'_spec S r t
    have e2 := IsLocalization.mk'_spec S r' t'
    have hw : algebraMap R S ((t : R) * r' * f - (t' : R) * r * g) ∈ I := by
      have := I.mul_mem_left (algebraMap R S ((t : R) * t')) hI
      convert this using 1
      simp only [map_mul, map_sub]
      linear_combination (algebraMap R S t' * algebraMap R S g) * e1 -
        (algebraMap R S t * algebraMap R S f) * e2
    obtain ⟨⟨p, s⟩, hps⟩ := (IsLocalization.mem_map_algebraMap_iff U.primeCompl S).mp hw
    rw [← map_mul] at hps
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists U.primeCompl S).mp hps
    have hx : (c : R) * s * t' * r ∈ (P ⊔ Ideal.span {f}).colon {g} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      refine Submodule.mem_sup.mpr ⟨-((c : R) * p), P.neg_mem (P.mul_mem_left _ p.2),
        (c : R) * s * t * r' * f, Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩, ?_⟩
      linear_combination hc
    have hy' : Ideal.Quotient.mk I (IsLocalization.mk' S r t) =
        localQuotMap P U ((c : R) * s * t' * r) *
          Ideal.Quotient.mk I (IsLocalization.mk' S (1 : R) (c * s * t' * t)) := by
      rw [hφ, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
      congr 1
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      push_cast
      ring
    rw [hy']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotPrimes
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotPrimes.proof : LocalQuotPrimes.Statement.{u} := by
  intro R _ P U _ hPU
  let S := Localization.AtPrime U
  let PS : Ideal S := P.map (algebraMap R S)
  have hsurj : Function.Surjective (Ideal.Quotient.mk PS) := Ideal.Quotient.mk_surjective
  have hmap : ∀ I : Ideal R,
      I.map (localQuotMap P U) = (I.map (algebraMap R S)).map (Ideal.Quotient.mk PS) := by
    intro I
    rw [Ideal.map_map]
    rfl
  have hcomap : ∀ J : Ideal (localQuot P U),
      J.comap (localQuotMap P U) = (J.comap (Ideal.Quotient.mk PS)).comap (algebraMap R S) := by
    intro J
    rw [Ideal.comap_comap]
    rfl
  refine ⟨fun W hW hPW hWU => ?_, fun p hp => ?_⟩
  · have hdisj : Disjoint (U.primeCompl : Set R) W := by
      rw [Set.disjoint_left]
      intro x hx hxW
      exact hx (hWU hxW)
    have hWS : (W.map (algebraMap R S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl S W hW hdisj
    have hWSc : (W.map (algebraMap R S)).comap (algebraMap R S) = W :=
      IsLocalization.under_map_of_isPrime_disjoint U.primeCompl S hW hdisj
    have hker : RingHom.ker (Ideal.Quotient.mk PS) ≤ W.map (algebraMap R S) := by
      rw [Ideal.mk_ker]
      exact Ideal.map_mono hPW
    refine ⟨?_, ?_⟩
    · rw [hmap]
      exact Ideal.map_isPrime_of_surjective hsurj hker
    · rw [hmap, hcomap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker, hWSc]
  · let q : Ideal S := p.comap (Ideal.Quotient.mk PS)
    have hq : q.IsPrime := Ideal.comap_isPrime _ p
    have hq' := (IsLocalization.isPrime_iff_isPrime_disjoint U.primeCompl S q).mp hq
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Ideal.mem_comap]
      have h0 : localQuotMap P U x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
      rw [h0]
      exact p.zero_mem
    · intro x hx
      by_contra hxU
      rw [hcomap] at hx
      exact Set.disjoint_left.mp hq'.2 (show x ∈ U.primeCompl from hxU) hx
    · rw [hmap, hcomap]
      have hloc : (q.comap (algebraMap R S)).map (algebraMap R S) = q :=
        IsLocalization.map_under U.primeCompl S q
      rw [hloc]
      exact Ideal.map_comap_of_surjective _ hsurj p

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem PairConeLinesIndep.formMatrix_isUnit {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {N : ℕ}
    (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E) (hψ : LinearIndependent Ω ψ) :
    IsUnit (Matrix.of fun i j => ψ i (e j)) := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have h := hψ.map' e.dualBasis.equivFun.toLinearMap e.dualBasis.equivFun.ker
  have hrows : (Matrix.of fun i j => ψ i (e j)).row = ⇑e.dualBasis.equivFun ∘ ψ := by
    funext i
    funext j
    simp [Matrix.row, Module.Basis.equivFun_apply]
  rw [hrows]
  exact h

theorem PairConeLinesIndep.linearChange_indep {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {N : ℕ}
    (P : Matrix (Fin N) (Fin N) Ω) (hP : IsUnit P) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (P i j)) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  let f : Fin N → MvPolynomial (Fin N) Ω := fun i => ∑ j, X j * C (P i j)
  let g : Fin N → MvPolynomial (Fin N) Ω := fun j => ∑ k, X k * C (P⁻¹ j k)
  have hgf : (fun i => aeval g (f i)) = X := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, g, map_sum, map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq]
    calc ∑ j, (∑ k, X k * C (P⁻¹ j k)) * C (P i j)
        = ∑ k, X k * C ((P * P⁻¹) i k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp_rw [Finset.sum_mul, Matrix.mul_apply, map_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]
          ring
      _ = X i := by
          rw [Matrix.mul_nonsing_inv _ hdet]
          simp [Matrix.one_apply]
  have hf : AlgebraicIndependent Ω f := by
    apply AlgebraicIndependent.of_aeval (x := g)
    rw [hgf]
    exact algebraicIndependent_X _ _
  have h := ht.aeval_of_algebraicIndependent hf
  convert h using 1
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [f, map_sum, aeval_X]

theorem PairConeLinesIndep.proof : PairConeLinesIndep.Statement := by
  intro Ω _ Φ _ _ K N E _ _ e ψ hψ t ht g hg
  have hw : AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (ψ i (e j))) :=
    PairConeLinesIndep.linearChange_indep (Matrix.of fun i j => ψ i (e j))
      (PairConeLinesIndep.formMatrix_isUnit e ψ hψ) t ht
  let T : K → MvPolynomial (Option (Option K)) Φ := fun k => X (some (some k))
  let idx : Unit ⊕ K → Option (Option K) := Sum.elim (fun _ => none) (fun k => some (some k))
  have hidx : Function.Injective idx := by
    rintro (_ | a) (_ | b) h <;> simp_all [idx]
  have hvars : AlgebraicIndependent Φ (X ∘ idx : Unit ⊕ K → MvPolynomial (Option (Option K)) Φ) :=
    (algebraicIndependent_X _ _).comp idx hidx
  have hA := AlgebraicIndependent.sumElim_comp hw hvars
  have hB : AlgebraicIndependent Ω
      (Sum.elim (Sum.elim (fun i => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))))
        (fun _ : Unit => (X none : MvPolynomial (Option (Option K)) Φ))) T) := by
    have h := hA.comp ((Equiv.sumAssoc _ _ _).trans (Equiv.sumComm _ _)) (Equiv.injective _)
    convert h using 1
    funext x
    rcases x with ((i | u) | k) <;> simp [idx, T, MvPolynomial.algebraMap_eq]
  have hC := (AlgebraicIndependent.sumElim_iff.mp hB).2
  let σ : MvPolynomial (Option (Option K)) Φ →ₐ[Φ] MvPolynomial (Option (Option K)) Φ :=
    aeval fun o => Option.elim o (C g⁻¹ * X none) (fun o' => Option.elim o' 1 (fun k => X (some (some k))))
  have hfix : Algebra.adjoin Ω (Set.range T) ≤ AlgHom.equalizer (σ.restrictScalars Ω) (AlgHom.id Ω _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩
    simp [σ, T]
  let f : MvPolynomial (Option (Option K)) Φ →ₐ[Algebra.adjoin Ω (Set.range T)]
      MvPolynomial (Option (Option K)) Φ :=
    { σ.toRingHom with commutes' := fun r => hfix r.2 }
  apply AlgebraicIndependent.of_comp f
  convert hC using 1
  funext x
  rcases x with i | u
  · simp [f, σ]
  · change σ (C g * X none) = X none
    simp only [σ, map_mul, aeval_C, aeval_X, Option.elim, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, one_mul]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

