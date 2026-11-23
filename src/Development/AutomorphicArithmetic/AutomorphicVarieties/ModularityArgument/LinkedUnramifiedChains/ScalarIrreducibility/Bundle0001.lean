module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0106
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CmOfRegularLocal
section
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

open GroundTheory.Heights₂.Heights in
private theorem cm_of_regular_local (A : Type) [CommRing A] [IsRegularLocalRing A] :
    IsCohenMacaulayLocalRing A := by
  haveI hL : IsLocalRing A := IsRegularLocalRing.toIsLocalRing
  haveI hN : IsNoetherian A A := IsRegularLocalRing.toIsNoetherian
  obtain ⟨rs, hreg, hmax, hlen⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := A)
  refine @IsCohenMacaulayLocalRing.mk A _ hL hN ⟨rs, fun r hr => ?_, hreg.toIsWeaklyRegular, hlen.symm⟩
  rw [← hmax]
  exact Ideal.subset_span hr


open GroundTheory.Heights₂.Heights in
private theorem ass_min_of_surj {A B : Type} [CommRing A] [IsCohenMacaulayLocalRing A] [CommRing B]
    [Nontrivial B] (φ : A →+* B) (hφ : Function.Surjective φ) {k : ℕ} (x : Fin k → A)
    (hx : ∀ i, x i ∈ maximalIdeal A) (hk : RingHom.ker φ = Ideal.span (Set.range x))
    (hd : ringKrullDim B + (k : WithBot ℕ∞) ≤ ringKrullDim A) {P : Ideal B}
    (hP : P ∈ associatedPrimes B B) : P ∈ minimalPrimes B := by
  classical
  set I : Ideal A := Ideal.span (Set.range x) with hI
  let e : A ⧸ I ≃+* B := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have hdimB : ringKrullDim B = ringKrullDim (A ⧸ I) := (ringKrullDim_eq_of_ringEquiv e).symm
  have hs : ((Finset.univ.image x : Finset A) : Set A) = Set.range x := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcard : (Finset.univ.image x).card ≤ k :=
    Finset.card_image_le.trans (Finset.card_fin k).le
  have hle : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) := by
    have h0 := ringKrullDim_le_ringKrullDim_quotient_add_card (R := A) (Finset.univ.image x) (by
      rw [hs, IsLocalRing.ringJacobson_eq_maximalIdeal]
      rintro _ ⟨i, rfl⟩
      exact hx i)
    rw [hs] at h0
    refine h0.trans ?_
    gcongr
  have heq : ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) = ringKrullDim A :=
    le_antisymm (hdimB ▸ hd) hle
  have hCM : IsCohenMacaulayLocalRing (A ⧸ I) :=
    CMParameterQuotient.proof CMRegularElement.proof A k x hx heq
  have : IsCohenMacaulayLocalRing B := IsCohenMacaulayLocalRing.of_ringEquiv e
  exact mem_minimalPrimes_of_mem_associatedPrimes hP

private theorem min_of_localized {R : Type} [CommRing R] (Q : Ideal R) [Q.IsPrime] {P : Ideal R}
    (hP : P ∈ associatedPrimes R R) (hPQ : P ≤ Q)
    (h : ∀ P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q),
      P' ∈ minimalPrimes (Localization.AtPrime Q)) : P ∈ minimalPrimes R := by
  have hPprime : P.IsPrime := hP.1
  have hdis : Disjoint (Q.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    intro a ha haP
    exact ha (hPQ haP)
  set P' : Ideal (Localization.AtPrime Q) := P.map (algebraMap R (Localization.AtPrime Q)) with hP'
  have hcomap : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hPprime hdis
  have hass : P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q) := by
    refine Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      Q.primeCompl (Algebra.linearMap R (Localization.AtPrime Q)) P' ?_
    rw [hcomap]
    exact hP
  have hmin : P' ∈ (Ideal.map (algebraMap R (Localization.AtPrime Q)) (⊥ : Ideal R)).minimalPrimes := by
    rw [Ideal.map_bot]
    exact h P' hass
  rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q) (⊥ : Ideal R)] at hmin
  have key : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' ∈ (⊥ : Ideal R).minimalPrimes := hmin
  rw [hcomap] at key
  exact key

theorem UpperTheory.V.J.unmix :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (N N' : ℕ) (R : Type) [CommRing R]
        (p : MvPowerSeries (Fin N) O →+* R) (f : Fin N' → MvPowerSeries (Fin N) O), Function.Surjective p → RingHom.ker p = Ideal.span (Set.range f) →
        ∀ Q : Ideal R, Q.IsPrime → Q.height + N' ≤ (Q.comap p).height → ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R := by
  intro O _ _ _ _ N N' R _ p f hp hker Q hQ hht P hP hPQ
  set q : Ideal (MvPowerSeries (Fin N) O) := Q.comap p with hq
  haveI : IsRegularLocalRing (MvPowerSeries (Fin N) O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin N)
  haveI : IsRegularLocalRing (Localization.AtPrime q) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime q
  haveI : GroundTheory.Heights₂.Heights.IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
    cm_of_regular_local _
  let φ : Localization.AtPrime q →+* Localization.AtPrime Q := Localization.localRingHom q Q p rfl
  have hφ : Function.Surjective φ := RingHom.surjective_localRingHom_of_surjective p hp Q
  have hkerφ : RingHom.ker φ = (RingHom.ker p).map (algebraMap _ (Localization.AtPrime q)) :=
    IsLocalization.ker_map (M := q.primeCompl) (S := Localization.AtPrime q)
      (Localization.AtPrime Q) p (Submonoid.map_comap_eq_of_surjective hp Q.primeCompl)
  have hkx : RingHom.ker φ = Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (f i))) := by
    rw [hkerφ, hker, Ideal.map_span, ← Set.range_comp]
    rfl
  have hx : ∀ i, algebraMap _ (Localization.AtPrime q) (f i) ∈ maximalIdeal (Localization.AtPrime q) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
    have hfi : f i ∈ RingHom.ker p := by
      rw [hker]
      exact Ideal.subset_span ⟨i, rfl⟩
    show p (f i) ∈ Q
    rw [RingHom.mem_ker.mp hfi]
    exact Q.zero_mem
  have hd : ringKrullDim (Localization.AtPrime Q) + (N' : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
    exact_mod_cast hht
  refine min_of_localized Q hP hPQ ?_
  intro P' hP'
  exact ass_min_of_surj φ hφ _ hx hkx hd hP'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DenseOf
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private lemma dim_succ_le {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime] (h : P < Q) :
    ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨r, hrQ, hrP⟩ := SetLike.exists_of_lt h
  have hne : Ideal.Quotient.mk P r ≠ 0 := fun h0 => hrP (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hnzd : Ideal.Quotient.mk P r ∈ nonZeroDivisors (A ⧸ P) := mem_nonZeroDivisors_of_ne_zero hne
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk P r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have : Ideal.Quotient.factor h.le (Ideal.Quotient.mk P r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hrQ
    rw [map_mul, this, mul_zero]
  have hs : Function.Surjective
      (Ideal.Quotient.lift (Ideal.span {Ideal.Quotient.mk P r}) (Ideal.Quotient.factor h.le) hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective h.le)
  have h2 := ringKrullDim_le_of_surjective _ hs
  exact (add_le_add_left h2 1).trans h1

private lemma exists_sep {A : Type} [CommRing A] [IsNoetherianRing A] {J Z₀ : Ideal A}
    (h₀ : Z₀ ∈ J.minimalPrimes) :
    ∃ e, e ∉ Z₀ ∧ ∀ Z₁ ∈ J.minimalPrimes, Z₁ ≠ Z₀ → e ∈ Z₁ := by
  classical
  have hfin := J.finite_minimalPrimes_of_isNoetherianRing A
  set s := hfin.toFinset.erase Z₀ with hs
  have hp : Z₀.IsPrime := h₀.1.1
  have hnot : ¬ s.inf id ≤ Z₀ := by
    intro hle
    obtain ⟨W, hW, hWle⟩ := (Ideal.IsPrime.inf_le' hp).mp hle
    have hW' := Finset.mem_erase.mp hW
    have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW'.2
    exact hW'.1 (le_antisymm hWle (h₀.2 hWm.1 hWle) |>.symm ▸ rfl)
  obtain ⟨e, he, heZ⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨e, heZ, fun Z₁ h₁ hne => ?_⟩
  have : Z₁ ∈ s := Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr h₁⟩
  exact (Finset.inf_le (f := id) this) he

theorem UpperTheory.V.J.denseOf :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (B₀ B : Type) [CommRing B₀] [IsNoetherianRing B₀] [Algebra c.O B₀] [CommRing B] [Algebra c.O B]
        (φ : B₀ →ₐ[c.O] B) (J : Ideal B₀) (D : ℕ) (Gd : (B₀ →ₐ[c.O] Qbar l) → Prop), Function.Surjective φ →
        (∀ Z ∈ J.minimalPrimes, ringKrullDim (B₀ ⧸ Z) = (D : WithBot ℕ∞)) →
        (∀ b : B₀, (∀ x : B₀ →ₐ[c.O] Qbar l, J ≤ RingHom.ker x → Gd x → x b = 0) → b ∈ J) →
        ∀ Z : Ideal B, Z.IsPrime → J.map φ ≤ Z → ringKrullDim (B ⧸ Z) ≤ (D : WithBot ℕ∞) ∧
          (ringKrullDim (B ⧸ Z) = (D : WithBot ℕ∞) → ∀ b ∉ Z, ∃ y : B →ₐ[c.O] Qbar l, Z ≤ RingHom.ker y ∧ Gd (y.comp φ) ∧ y b ≠ 0) := by
  intro l _ c B₀ B _ _ _ _ _ φ J D Gd hφ hdim hdense Z hZ hJZ
  have hJZ' : J ≤ Z.comap φ := Ideal.map_le_iff_le_comap.mp hJZ
  haveI hZ' : (Z.comap φ).IsPrime := Ideal.comap_isPrime φ Z
  obtain ⟨Z₀, hZ₀, hZ₀le⟩ := Ideal.exists_minimalPrimes_le hJZ'
  haveI hp₀ : Z₀.IsPrime := hZ₀.1.1
  have hψ : Function.Surjective ((Ideal.Quotient.mk Z).comp (φ : B₀ →+* B)) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk Z).comp (φ : B₀ →+* B)) = Z.comap φ := by
    ext a
    exact RingHom.mem_ker.trans Ideal.Quotient.eq_zero_iff_mem
  have hde : ringKrullDim (B ⧸ Z) = ringKrullDim (B₀ ⧸ Z.comap φ) := by
    rw [← hker]
    exact (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)).symm
  have hle : ringKrullDim (B ⧸ Z) ≤ (D : WithBot ℕ∞) := by
    rw [hde, ← hdim Z₀ hZ₀]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ₀le) (Ideal.Quotient.factor_surjective hZ₀le)
  refine ⟨hle, fun hD b hb => ?_⟩
  have hZeq : Z₀ = Z.comap φ := by
    by_contra hne
    have hlt : Z₀ < Z.comap φ := lt_of_le_of_ne hZ₀le hne
    have h1 := dim_succ_le hlt
    rw [← hde, hD, hdim Z₀ hZ₀] at h1
    have h2 : ((D : WithBot ℕ∞) + 1) = ((D + 1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    rw [h2] at h1
    have h3 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ (D : WithBot ℕ∞) := h1
    have h4 : D + 1 ≤ D := by exact_mod_cast h3
    omega
  obtain ⟨b', rfl⟩ := hφ b
  have hb' : b' ∉ Z₀ := by rw [hZeq]; exact hb
  obtain ⟨e, he, hesep⟩ := exists_sep hZ₀
  have hbe : b' * e ∉ J := fun hm =>
    (hp₀.mem_or_mem (hZ₀.1.2 hm)).elim hb' he
  have hx : ∃ x : B₀ →ₐ[c.O] Qbar l, J ≤ RingHom.ker x ∧ Gd x ∧ x (b' * e) ≠ 0 := by
    by_contra hno
    refine hbe (hdense _ fun x h1 h2 => ?_)
    by_contra h3
    exact hno ⟨x, h1, h2, h3⟩
  obtain ⟨x, hJx, hGx, hxbe⟩ := hx
  have hxb : x b' ≠ 0 := fun h0 => hxbe (by rw [map_mul, h0, zero_mul])
  have hxe : x e ≠ 0 := fun h0 => hxbe (by rw [map_mul, h0, mul_zero])
  haveI hkp : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Z₁, hZ₁, hZ₁le⟩ := Ideal.exists_minimalPrimes_le hJx
  have hZ₁eq : Z₁ = Z₀ := by
    by_contra hne
    exact hxe (hZ₁le (hesep Z₁ hZ₁ hne))
  have hZx : Z.comap φ ≤ RingHom.ker x := by rw [← hZeq, ← hZ₁eq]; exact hZ₁le
  have hkφ : RingHom.ker φ ≤ RingHom.ker x := fun a ha =>
    hZx (by
      have : φ a = 0 := ha
      show φ a ∈ Z
      rw [this]; exact Z.zero_mem)
  let y : B →ₐ[c.O] Qbar l := (Ideal.Quotient.liftₐ (RingHom.ker φ) x (fun a ha => hkφ ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom
  have hy : ∀ a, y (φ a) = x a := by
    intro a
    have e1 : (Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a) = Ideal.Quotient.mk _ a :=
      (AlgEquiv.symm_apply_eq _).2 (Ideal.quotientKerAlgEquivOfSurjective_mk hφ a).symm
    show Ideal.Quotient.liftₐ (RingHom.ker φ) x (fun a ha => hkφ ha) ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a)) = x a
    rw [e1]
    rfl
  refine ⟨y, fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hφ z
    show y (φ a) = 0
    rw [hy]
    exact hZx hz
  · have : y.comp φ = x := AlgHom.ext hy
    rwa [this]
  · rw [hy]; exact hxb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DomMin
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.domMin :
    ∀ (A : Type) [CommRing A] (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q) → ∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
  intro A _ q _ hD P hP hPq a ha
  letI : Nontrivial (Localization.AtPrime q) := hD.toNontrivial
  letI : NoZeroDivisors (Localization.AtPrime q) :=
    isCancelMulZero_iff_noZeroDivisors.mp hD.toIsCancelMulZero
  have hK : (RingHom.ker (algebraMap A (Localization.AtPrime q))).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (algebraMap A (Localization.AtPrime q)) ≤ P := by
    intro x hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).1 hx
    have h0 : (m : A) * x ∈ P := by rw [hm]; exact P.zero_mem
    exact (hP.1.1.mem_or_mem h0).resolve_left (fun h => m.2 (hPq h))
  have hge : P ≤ RingHom.ker (algebraMap A (Localization.AtPrime q)) := hP.2 ⟨hK, bot_le⟩ hle
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) a).1 (hge ha)
  exact ⟨m, fun h => m.2 (hPq h), hm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExtIntegral
section
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.ChevalleyRestriction

private theorem main_fin (A : Type) [CommRing A] [IsDomain A] (s : Finset A) :
    ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B A],
      Algebra.adjoin B (s : Set A) = ⊤ → Function.Injective (algebraMap B A) →
      ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
        y b ≠ 0 → ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra5.main_fin A s

end UpperTheory.V.J.ChevalleyRestriction

theorem UpperTheory.V.J.chev :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
        ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
          ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  intro B A _ _ _ _ _ hft hinj a ha
  obtain ⟨s, hs⟩ := hft.out
  exact UpperTheory.V.J.ChevalleyRestriction.main_fin A s B hs hinj a ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatAss
section
private theorem flatAss_ann {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) (r : R) (h : a • r = 0) :
    r ∈ P.map (algebraMap A R) := by
  have h1 : ∑ _i : Fin 1, a • r = 0 := by
    rw [Fin.sum_univ_one]
    exact h
  obtain ⟨l, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Fin 1 => a)
      (x := fun _ : Fin 1 => r) h1
  have hr : r = ∑ j, c 0 j • y j := hy 0
  rw [hr]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem _).2 ?_))
  have h2 := hc j
  rw [Fin.sum_univ_one] at h2
  rw [mul_comm]
  exact h2

private theorem flatAss_annih {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) :
    Module.annihilator R (Ideal.span {algebraMap A R a} : Ideal R) = P.map (algebraMap A R) := by
  apply le_antisymm
  · intro r hr
    have h0 : r * algebraMap A R a = 0 :=
      congrArg Subtype.val (Module.mem_annihilator.1 hr
        ⟨algebraMap A R a, Ideal.mem_span_singleton_self _⟩)
    refine flatAss_ann P a hmem r ?_
    rw [Algebra.smul_def, mul_comm]
    exact h0
  · refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
    rw [Ideal.mem_comap, Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hn
    apply Subtype.ext
    change algebraMap A R b * (c * algebraMap A R a) = 0
    rw [mul_left_comm, ← map_mul, (hmem b).1 hb, map_zero, mul_zero]

private theorem flatAss_alg {A R : Type} [CommRing A] [CommRing R] [IsNoetherianRing A]
    [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (Q : Ideal R) (hQ : Q.IsPrime)
    (hmin : ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R)
    (P : Ideal A) (hP : P ∈ associatedPrimes A A) (hPQ : P ≤ Q.comap (algebraMap A R)) :
    P ∈ minimalPrimes A := by
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  obtain ⟨hPp, a, hPa⟩ := isAssociatedPrime_iff.1 hP
  have hmem : ∀ b, b ∈ P ↔ b * a = 0 := fun b => by
    rw [hPa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  have hmapQ : P.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.2 hPQ
  haveI := hQ
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hmapQ
  have hQ'ass : Q' ∈ associatedPrimes R R := by
    have h1 := hQ'min
    rw [← flatAss_annih P a hmem] at h1
    exact associatedPrimes.subset_of_injective (Submodule.injective_subtype _)
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ h1)
  have hQ'm := hmin Q' hQ'ass hQ'Q
  haveI hQ'p : Q'.IsPrime := hQ'min.1.1
  refine ⟨⟨hPp, bot_le⟩, fun p hp hpP => ?_⟩
  haveI := hp.1
  have hPc : P ≤ Q'.comap (algebraMap A R) := Ideal.map_le_iff_le_comap.1 hQ'min.1.2
  haveI : Q'.LiesOver (Q'.comap (algebraMap A R)) := ⟨rfl⟩
  obtain ⟨Q'', hle, hQ''p, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le Q' (hpP.trans hPc)
  have hge := hQ'm.2 ⟨hQ''p, bot_le⟩ hle
  have heq : Q'' = Q' := le_antisymm hle hge
  rw [hlies.over, heq]
  exact hPc

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatAss :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ Q : Ideal R, Q.IsPrime →
        (∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R) → ∀ P ∈ associatedPrimes A A, P ≤ Q.comap ι → P ∈ minimalPrimes A :=
  fun A R _ _ _ _ ι hι Q hQ hmin P hP hPQ =>
    @flatAss_alg A R _ _ _ _ ι.toAlgebra hι Q hQ hmin P hP hPQ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatHt
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatHt :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ (q : Ideal A) (Q : Ideal R),
        Q.IsPrime → Q.comap ι = q → Q ∈ (q.map ι).minimalPrimes → Q.height = q.height := by
  intro A R _ _ _ _ ι hι q Q hQ hcomap hmin
  letI : Algebra A R := ι.toAlgebra
  haveI : Module.Flat A R := hι
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q
  haveI : Q.LiesOver q := ⟨hcomap.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]
  suffices h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by
    rw [h0, add_zero]
  have hJQ : q.map (algebraMap A R) ≤ Q := hmin.1.2
  have hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro K ⟨hK, -⟩ hKQ
  have hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)
    have hd : y - x ∈ q.map (algebraMap A R) := Ideal.Quotient.eq.mp hxy
    have hx' : x = y - (y - x) := by ring
    rw [hx']
    exact Q.sub_mem hy (hJQ hd)
  have hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle
    intro x hx
    have hx2 : x ∈ q.map (algebraMap A R) := hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]
    exact K.zero_mem
  exact Ideal.map_le_iff_le_comap.mpr hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HeightLeOfDim
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem height_le_of_dim {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) [hQ : Q.IsPrime]
    (h1 : ringKrullDim (R ⧸ Q) = 1) (N : ℕ)
    (h : ∀ P : Ideal R, P.IsPrime → P ≤ Q → ringKrullDim (R ⧸ P) ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) :
    Q.height ≤ (N : ℕ∞) := by
  have e : Q.height = Order.height (⟨Q, hQ⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.height_eq_orderHeight (⟨Q, hQ⟩ : PrimeSpectrum R)
  rw [e, Order.height_le_iff]
  intro p hp
  have hQm : Q < maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) ?_
    intro hEq
    haveI : Q.IsMaximal := hEq ▸ IsLocalRing.maximalIdeal.isMaximal R
    letI := Ideal.Quotient.field Q
    rw [ringKrullDim_eq_zero_of_field] at h1
    exact absurd h1 (by decide)
  have hlt : p.last < (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) :=
    lt_of_le_of_lt hp hQm
  let s : LTSeries (PrimeSpectrum R) := p.snoc _ hlt
  set P := p.head.asIdeal with hPdef
  have hPp : P.IsPrime := p.head.isPrime
  have hPQ : P ≤ Q := (LTSeries.monotone p (Fin.zero_le (Fin.last _))).trans hp
  have hmem : ∀ i, s i ∈ PrimeSpectrum.zeroLocus (P : Set R) := by
    intro i
    have h0 := LTSeries.monotone s (Fin.zero_le i)
    rw [show s 0 = p.head from RelSeries.head_snoc _ _ _] at h0
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => h0 ha
  let t : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) :=
    ⟨s.length, fun i => ⟨s i, hmem i⟩, fun i => s.step i⟩
  have ht : ((s.length : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := by
    rw [ringKrullDim_quotient]
    exact Order.le_krullDim_iff.2 ⟨t, rfl⟩
  have hb := ht.trans (h P hPp hPQ)
  have hsl : s.length = p.length + 1 := RelSeries.snoc_length _ _ _
  rw [hsl] at hb
  have hb' : p.length + 1 ≤ N + 1 := by exact_mod_cast hb
  exact_mod_cast (by omega : p.length ≤ N)

theorem UpperTheory.V.J.htUp :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (M : Ideal S.B), AllGood S M → (∀ Z : Ideal S.B, Z.IsPrime → M ≤ Z → ringKrullDim (S.B ⧸ Z) ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞)) →
          ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q → S.u.TI q → Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) := by
  intro l _ c _ F C₀ n hF hn S M hM hZ q x L Q hO hT
  obtain ⟨hQp, him, -, hdim⟩ := hO
  refine height_le_of_dim Q hdim (n * F.d + 1) ?_
  intro P hP hPQ
  have hPq : L.im P ≤ q := him ▸ Ideal.comap_mono hPQ
  have hTP : S.u.TI (L.im P) :=
    ⟨⟨fun h => hT.1.1 (h.trans hPq), fun h => hT.1.2 (h.trans hPq)⟩,
      fun h3 h => hT.2 h3 (h.trans hPq)⟩
  have hprime : (L.im P).IsPrime := Ideal.comap_isPrime _ _
  have htd : S.td (L.im P) ≤ ((1 : ℕ) : Cardinal) := by
    rw [Nat.cast_one]
    exact Fr.fibre hF hn S _ hprime hTP.1
  have h1 := (Fr.loc_dim hF hn S x L).1 P hP 1 htd
  have hπ : (L.π P).IsPrime := Ideal.comap_isPrime _ _
  have h2 := hZ (L.π P) hπ (hM _ hprime hTP)
  calc ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (S.B ⧸ L.π P) + ((1 : ℕ) : WithBot ℕ∞) := h1
    _ ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by gcongr
    _ = ((n * F.d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← Nat.cast_add]
      congr 1
      omega
end

