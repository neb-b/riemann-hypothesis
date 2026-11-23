module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalFlat
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeLocalLength.proof (h₁ : LocalizedQuotientLength.Statement.{u, u})
    (h₂ : ConeLocalFlat.Statement.{u}) : ConeLocalLength.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW c a h _ _ hhW α hα
  have := hP.isPrime
  have := hW.isPrime
  obtain ⟨_, _, _, hmax⟩ := h₂ F K ι P hP W hW hPW
  have : IsLocalHom (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) :=
    ((local_hom_tfae _).out 3 1).mp hmax.le
  have hu : IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h)) :=
    IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, ⟨h, hhW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hne : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P h) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hhW (hPW h')
  have ha : algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a) =
      algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) α *
        algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hα, div_mul_cancel₀ _ hne]
  have hspan : Ideal.span {algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a)} =
      (Ideal.span {α}).map (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, ha, Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A R : Type u) [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
      [Algebra A R] [IsLocalHom (algebraMap A R)] [Module.Flat A R],
      (maximalIdeal A).map (algebraMap A R) = maximalIdeal R → ∀ x : A,
        Module.length R (R ⧸ (Ideal.span {x}).map (algebraMap A R)) = Ring.ord A x := by
    intro A R _ _ _ _ _ _ _ hm x
    have hs : Module.length R (R ⧸ maximalIdeal R) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hs, mul_one]
    rfl
  unfold multAt
  rw [h₁ _ P W a (coneLocal P W hPW) inferInstance, hspan]
  exact key (degZeroLoc P {W}) (coneLocal P W hPW) hmax α

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DivCycleMinimal.ringKrullDim_eq {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type u} [Field F] (Q : Ideal (MRing ι F)) (m : ℕ)
    (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MRing ι F ⧸ Q) = d := by
    have h2 := PFContracted.ringKrullDim_lt_top Q
    cases hc : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [relDim, hc] at h
      exact absurd h (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [hc] at h2
        exact absurd h2 (by simp)
      | coe d => exact ⟨d, rfl⟩
  rw [PFContracted.relDim_eq_int hd, PFContracted.natCast_withBot_withTop] at h
  have h' : (d : ℤ) - Fintype.card K = m := by
    have := WithBot.coe_injective h
    exact_mod_cast WithTop.coe_injective this
  rw [hd]
  congr 1
  omega

theorem DivCycleMinimal.proof : DivCycleMinimal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hPn a ha W hW hWn hle
  have hmin : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hW, hle⟩, fun Q hQ hQW => ?_⟩
    obtain ⟨hQp, hJQ⟩ := hQ
    by_contra hWQ
    obtain ⟨f, hfW, hfQ⟩ := Set.not_subset.mp hWQ
    have h1 := PFContracted.ringKrullDim_add_one_le (P := Q) (Q := W) hQW hfQ hfW
    have h2 := PFContracted.ringKrullDim_add_one_le (P := P) (Q := Q) (le_sup_left.trans hJQ) ha
      (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
    have h3 := (add_le_add h1 (le_refl 1)).trans h2
    rw [DivCycleMinimal.ringKrullDim_eq W n hWn, DivCycleMinimal.ringKrullDim_eq P (n + 1) hPn] at h3
    have h4 : (((n + Fintype.card K + 1 + 1 : ℕ)) : WithBot ℕ∞) ≤ ((n + 1 + Fintype.card K : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 := ENat.natCast_le_natCast.mp h5
    omega
  exact ⟨hmin, length_localizedQuot_ne_top _ _ hmin⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u}
    [Field F] {W : Ideal (MRing ι F)} (hW : IsMultiProjPrime W) (c : K → ℕ) :
    ∃ h : MRing ι F, IsMultiHomog h c ∧ h ∉ W := by
  choose v hv using hW.relevant
  have := hW.isPrime
  refine ⟨∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (c k))
    have hc : (∑ k, c k • blockWeight ι ⟨k, v k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem this _ hk)

theorem DivPushForwardLocal.proof (h1 : DivCycleMinimal.Statement.{u})
    (h2 : ConeLocalLength.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : SemilocalFiniteRank.Statement.{u}) (h5 : SemilocalLength.Statement.{u}) :
    DivPushForwardLocal.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hdim hdimP c a ha haP W hW hWd M hM1 hM0
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  by_cases hPW : contractPrime j P' ⊔ Ideal.span {a} ≤ W
  · have := hW.isPrime
    have hPle : contractPrime j P' ≤ W := le_trans le_sup_left hPW
    obtain ⟨h, hh, hhW⟩ := exists_form_not_mem hW c
    let α : degZeroLoc (contractPrime j P') {W} := ⟨_, div_mem_degZeroLoc _ _ ha hh
      (fun hm => hhW (hPle hm)) (fun W₁ h₁ => (Set.mem_singleton_iff.mp h₁) ▸ hhW)⟩
    have hα0 : α ≠ 0 := by
      intro h0
      have h0' := congrArg Subtype.val h0
      rcases div_eq_zero_iff.mp h0' with h' | h' <;>
        rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
      · exact haP h'
      · exact hhW (hPle h')
    obtain ⟨⟨hNo, hLo⟩, hdA⟩ := h3 F K _ _ hP W hW hPle
    obtain ⟨hfin, htf, hrk⟩ := h4 F K K' j ι' P' hP' n hdim hdimP W hW hWd hPle
    have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (degZeroLoc P' (fibrePrimes j P' W)) α
      (hdA n hdimP hWd) hα0
    obtain ⟨N, hN, hMN⟩ := h5 F K K' j ι' P' hP' n hdim hdimP c a h ha hh haP W hW hWd hPle hhW
      M hM1 hM0 α rfl
    obtain ⟨hmin, hfinm⟩ := h1 F K _ _ hP.isPrime n hdimP a haP W hW.isPrime hWd hPW
    have hcone := h2 F K _ _ hP W hW hPle c a h ha hh hhW α rfl
    have hdc : divCycle (contractPrime j P') a W =
        ((multAt (contractPrime j P' ⊔ Ideal.span {a}) W).toNat : ℤ) := by
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hW.relevant⟩]
    rw [hMN, hdc]
    rw [hN, hrk, ← hcone] at key
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinm
    rw [← hm] at key ⊢
    have hNm : N = relDeg j P' * m := by exact_mod_cast key
    rw [hNm, ENat.toNat_natCast]
    push_cast
    rfl
  · have hR : divCycle (contractPrime j P') a W = 0 := by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, -⟩
      exact hPW h.1.2
    rw [hR, mul_zero]
    unfold cycEval
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    by_cases hD : divCycle P' (rename (blockIncl j ι') a) W' = 0
    · rw [hD, zero_mul]
    · refine mul_eq_zero_of_right _ (hM0 W' fun hc => hPW ?_)
      unfold divCycle at hD
      split_ifs at hD with hm
      · rw [← hc]
        refine sup_le (Ideal.comap_mono (le_trans le_sup_left hm.1.1.2)) ?_
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hm.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      · exact absurd rfl hD

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConePolyLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

theorem isPrime_map_C_mvPolynomial {A : Type*} [CommRing A] (σ : Type*) (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

section Cone

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def coneVarMap (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (v : ∀ k, ι k) :
    MvPolynomial K (degZeroLoc P {W}) →ₐ[degZeroLoc P {W}] coneLocal P W hPW :=
  aeval fun k => algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩))

end Cone

def ConePolyLocalization.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})),
      letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
      haveI := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
      IsLocalization.AtPrime (coneLocal P W hPW)
        ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocFrac.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W) →
    haveI := hP.isPrime
    ∀ x ∈ homFracDegZero P, ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocLocal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    IsLocalRing (degZeroLoc P {W})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocNoetherian.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    IsNoetherianRing (degZeroLoc P {W})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocQuot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))), (∀ W ∈ 𝒲, W.IsPrime) →
    ∀ x ∈ degZeroLoc P 𝒲, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
      x = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocSeparate.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, ¬ W₁ ≤ W₂ →
      ∃ x ∈ degZeroLoc P 𝒲, (¬ ∃ y ∈ degZeroLoc P {W₁}, x * y = 1) ∧
        ∃ y ∈ degZeroLoc P {W₂}, x * y = 1

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → (fibrePrimes j P' W).Finite

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

