module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreFinite.proof : FibreFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _
  have := hP'.isPrime
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (P' ⊔ W.map (rename (blockIncl j ι')))).subset ?_
  rintro W' ⟨hW', hPW', hc⟩
  have := hW'.isPrime
  obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW' (Ideal.map_le_iff_le_comap.mpr hc.ge))
  have := hQ.1.1
  have hP'Q : P' ≤ Q := le_sup_left.trans hQ.1.2
  suffices Q = W' by rwa [← this]
  by_contra hne
  have hQc : contractPrime j Q = W := le_antisymm (hc ▸ Ideal.comap_mono hQW')
    (Ideal.le_comap_map.trans (Ideal.comap_mono (le_sup_right.trans hQ.1.2)))
  have hne' : P' ≠ Q := by
    rintro rfl
    rw [hQc, hWn] at hPn
    simp only [natCast_withBot_withTop] at hPn
    have := WithTop.coe_inj.mp (WithBot.coe_inj.mp hPn)
    omega
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hP'Q hne')
  obtain ⟨g, hgW, hgQ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQW' hne)
  have h1 := ringKrullDim_add_one_le hP'Q hfP hfQ
  have h2 := ringKrullDim_add_one_le hQW' hgQ hgW
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
  obtain ⟨E, -, hE⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hW'.multiHomog T hq) hW'.relevant
  have h3 := ContractRelDimLe.proof F K K' j ι' W' hW'
  rw [hc, hWn, relDim_eq_int hE, natCast_withBot_withTop] at h3
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hP'n
  have h4 : ((E + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ D := by
    rw [← hD]
    rw [hE] at h2
    push_cast
    exact le_trans (by gcongr) h1
  have h3' : (n : ℤ) ≤ E - Fintype.card K' := by exact_mod_cast h3
  have hP'n' : (D : ℤ) - Fintype.card K' = (n + 1 : ℕ) := by exact_mod_cast hP'n
  have h4' : E + 1 + 1 ≤ D := by exact_mod_cast h4
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreRelDim.proof : FibreRelDim.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _ W' hW'
  obtain ⟨hW'm, hPW', hcW'⟩ := hW'
  have := hP'.isPrime
  have := hW'm.isPrime

  have hge : ((n : ℕ) : WithBot (WithTop ℤ)) ≤ relDim W' := by
    rw [← hWn, ← hcW']
    exact ContractRelDimLe.proof F K K' j ι' W' hW'm

  have hne : ¬ W' ≤ P' := by
    intro hle
    have heq : W' = P' := le_antisymm hle hPW'
    rw [heq] at hcW'
    rw [hcW', hWn] at hPn
    have := congrArg (fun x : WithBot (WithTop ℤ) => x) hPn
    rw [natCast_withBot_withTop, natCast_withBot_withTop] at this
    have h2 := WithTop.coe_injective (WithBot.coe_injective this)
    omega
  obtain ⟨f, hfW', hfP'⟩ := Set.not_subset.mp hne
  have hstab : ∀ {Q : Ideal (MRing ι' F)}, IsMultiProjPrime Q →
      ∀ (T : Finset K') (q : MRing ι' F), q ∈ Q → killBlocks T q ∈ Q :=
    fun hQ T _ hq => killBlocks_mem_of_isMultiHomogIdeal hQ.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq (hstab hP') hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (hstab hW'm) hW'm.relevant
  have hstep := ringKrullDim_add_one_le hPW' hfP' hfW'
  rw [hD, hD'] at hstep
  have hlt : D + 1 ≤ D' := by exact_mod_cast hstep
  rw [relDim_eq_int hD', natCast_withBot_withTop] at hP'n
  have hP'z := WithTop.coe_injective (WithBot.coe_injective hP'n)
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hge ⊢
  have hgez : (n : ℤ) ≤ (D : ℤ) - Fintype.card K' :=
    WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hge)
  congr 2
  push_cast at hP'z
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Rank

variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]

theorem isFractionRing_of_div {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    (inj : Function.Injective (algebraMap A K))
    (surj : ∀ z : K, ∃ x y : A, z = algebraMap A K x / algebraMap A K y) : IsFractionRing A K :=
  haveI := (faithfulSMul_iff_algebraMap_injective A K).mpr inj
  IsFractionRing.of_field A K surj

theorem finrank_eq_relfinrank_of_div (φ : L₀ →ₐ[F] L) {K₀ : IntermediateField F L₀}
    {E : IntermediateField F L} (hKE : K₀.map φ ≤ E) {A : Subalgebra F L₀} {B : Subalgebra F L}
    [Algebra A B] (hφ : ∀ a : A, ((algebraMap A B a : B) : L) = φ a) (hA : ∀ a ∈ A, a ∈ K₀)
    (hB : ∀ b ∈ B, b ∈ E) (fracA : ∀ x ∈ K₀, ∃ y ∈ A, ∃ z ∈ A, z ≠ 0 ∧ x = y / z)
    (fracB : ∀ x ∈ E, ∃ y ∈ B, ∃ z ∈ B, z ≠ 0 ∧ x = y / z) :
    Module.finrank A B = IntermediateField.relfinrank (K₀.map φ) E := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hKE]
  set K := K₀.map φ
  set Lf := IntermediateField.extendScalars hKE
  let _ : Algebra A K := (((φ.comp A.val).toRingHom).codRestrict K
    (fun a => show φ a ∈ K from ⟨a, hA a a.2, rfl⟩)).toAlgebra
  let _ : Algebra B Lf := ((B.val.toRingHom).codRestrict Lf (fun b => hB b b.2)).toAlgebra
  let _ : Algebra A Lf := ((algebraMap B Lf).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B Lf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : IsScalarTower A K Lf := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (hφ a))
  have _ : IsFractionRing A K := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (φ.injective ?_)) ?_
    · exact congrArg Subtype.val h
    · rintro ⟨_, x, hx, rfl⟩
      obtain ⟨y, hy, z, hz, -, rfl⟩ := fracA x hx
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext (map_div₀ φ y z)⟩
  have _ : IsFractionRing B Lf := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (congrArg Subtype.val h :)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, -, rfl⟩ := fracB x hx
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext rfl⟩
  exact (IsFractionRing.finrank_eq A K B Lf).symm

end Rank

theorem mem_homFracDegZero_of_mem_degZeroLoc {K : Type*} [DecidableEq K] {ι : K → Type*}
    {F : Type*} [Field F] (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    ∀ x ∈ degZeroLoc P 𝒲, x ∈ homFracDegZero P := by
  intro x hx
  refine (Algebra.adjoin_le (S := (homFracDegZero P).toSubalgebra) ?_) hx
  rintro _ ⟨b, f, g, hf, hg, hgP, -, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgP, rfl⟩

theorem SemilocalFiniteRank.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFinite.Statement.{u}) (h3 : DegZeroLocFrac.Statement.{u}) :
    SemilocalFiniteRank.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  have inj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro a b hab
    apply Subtype.ext
    apply (contractFracMap j P').toRingHom.injective
    have := congrArg Subtype.val hab
    rwa [degZeroLoc.algebraMap_contract_coe, degZeroLoc.algebraMap_contract_coe] at this
  refine ⟨h2 F K K' j ι' P' hP' n hd' hd W hW hdW hle, ⟨fun r hr x y hxy => ?_⟩, ?_⟩
  · have hr0 : algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W)) r ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W))), inj.eq_iff]
      exact hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
  · refine finrank_eq_relfinrank_of_div (contractFracMap j P') (map_homFracDegZero_le j ι' P')
      (degZeroLoc.algebraMap_contract_coe j P' W)
      (mem_homFracDegZero_of_mem_degZeroLoc _ _) (mem_homFracDegZero_of_mem_degZeroLoc _ _) ?_ ?_
    · intro x hx
      refine h3 F K (fun k => ι' (j k)) (contractPrime j P')
        (isMultiProjPrime_contractPrime _ _ hP') {W} (Set.finite_singleton W) ?_ x hx
      intro W₁ hW₁
      rw [Set.mem_singleton_iff.mp hW₁]
      exact hW
    · exact h3 F K' ι' P' hP' (fibrePrimes j P' W) hfin (fun W' hW' => hW'.1)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


open Classical in
set_option synthInstance.maxHeartbeats 400000 in
theorem SemilocalLength.proof (h1 : SemilocalLengthSum.Statement.{u})
    (h2 : FibreRelDim.Statement.{u}) (h3 : DivCycleMinimal.Statement.{u})
    (h4 : ConeLocalLength.Statement.{u}) : SemilocalLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW M hM1 hM0 α hα
  have := hP'.isPrime
  obtain ⟨d, hd⟩ := exists_relDegFn (F := F) j (ι' := ι')
  obtain ⟨β, hβ⟩ := exists_fibreLift j P' W α
  obtain ⟨hfin, hlen⟩ := h1 F K K' j ι' P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d
    (fun W' hW' _ => hd W' hW') α hα β hβ
  have key : ∀ W' ∈ hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W'), ∃ hW' : IsMultiProjPrime W',
      haveI := hW'.isPrime
      Ring.ord (degZeroLoc P' {W'}) (β W') = multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W' ∧
        multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W' ≠ ⊤ ∧
        divCycle P' (rename (blockIncl j ι') a) W' = ((multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W').toNat : ℤ) ∧ M W' = d W' := by
    intro W' hT
    obtain ⟨hWf, haW'⟩ := Finset.mem_filter.mp hT
    have hWf' := hfin.mem_toFinset.mp hWf
    obtain ⟨hW'p, hPW', hcW'⟩ := id hWf'
    have := hW'p.isPrime
    have hmin := h3 F K' ι' P' hP'.isPrime n hP'n (rename (blockIncl j ι') a) haP W' hW'p.isPrime
      (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W' hWf')
      (sup_le hPW' ((Ideal.span_singleton_le_iff_mem _).mpr haW'))
    have hcone := h4 F K' ι' P' hP' W' hW'p hPW' (Function.extend j c 0) (rename (blockIncl j ι') a)
      (rename (blockIncl j ι') h) (isMultiHomog_rename j ι' ha) (isMultiHomog_rename j ι' hh)
      (fun hm => hhW (by rw [← hcW']; exact hm)) (β W')
      (by rw [hβ W' hWf', hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap])
    refine ⟨hW'p, hcone.symm, hmin.2, ?_, by rw [hM1 W' hW'p hcW', hd W' hW'p]⟩
    unfold divCycle
    rw [dite_eq_left ⟨hmin.1, hW'p.relevant⟩]
  refine ⟨∑ W' ∈ hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W'),
    (Ring.ord (degZeroLoc P' {W'}) (β W')).toNat * d W', ?_, ?_⟩
  · rw [hlen, Nat.cast_sum]
    refine Finset.sum_congr rfl fun W' hT => ?_
    obtain ⟨hW'p, hord, hfin', -, -⟩ := key W' hT
    rw [Nat.cast_mul, ENat.natCast_toNat (hord ▸ hfin')]
  · unfold cycEval
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W')) _ ?_,
      Nat.cast_sum]
    · refine Finset.sum_congr rfl fun W' hT => ?_
      obtain ⟨hW'p, hord, -, hdiv, hMd⟩ := key W' hT
      rw [hdiv, hMd, hord]
      push_cast
      ring
    · intro W' hW'
      have hdc : divCycle P' (rename (blockIncl j ι') a) W' ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hW')
      have hMW : M W' ≠ 0 := right_ne_zero_of_mul (Function.mem_support.mp hW')
      obtain ⟨hWp, -⟩ := DivCycleSupport.proof F K' ι' P' hP' n hP'n (Function.extend j c 0) (rename (blockIncl j ι') a)
        (isMultiHomog_rename j ι' ha) haP W' hdc
      have hmin : W' ∈ (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}).minimalPrimes := by
        by_contra hn
        exact hdc (by unfold divCycle; rw [dite_eq_right (fun hc => hn hc.1)])
      have hc : contractPrime j W' = W := by
        by_contra hne
        exact hMW (hM0 W' hne)
      exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ⟨hWp, le_sup_left.trans hmin.1.2, hc⟩,
        hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarInj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    Function.Injective (coneVarMap P W hPW v)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarNumerator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarNumerator.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ p : MvPolynomial K (degZeroLoc P {W}),
      ∃ (b : K → ℕ) (g : MRing ι F) (h : (K →₀ ℕ) → MRing ι F),
        IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (h d) b) ∧
        (∀ d, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (h d)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)) ∧
        ((coneVarMap P W hPW v p : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
              (Ideal.Quotient.mk P (∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarSurj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarSurj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ z : coneLocal P W hPW, ∃ (p q : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ),
      IsUnit (q.coeff e) ∧ z * coneVarMap P W hPW v q = coneVarMap P W hPW v p

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarUnit.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ (p : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ), IsUnit (p.coeff e) →
      IsUnit (coneVarMap P W hPW v p)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocalize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocLocalize.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W ∈ 𝒲, ∀ y ∈ degZeroLoc P {W}, ∃ b ∈ degZeroLoc P 𝒲, ∃ s ∈ degZeroLoc P 𝒲,
      (∃ t ∈ degZeroLoc P {W}, s * t = 1) ∧ y * s = b

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocUnits
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocUnits.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Nonempty → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ x ∈ degZeroLoc P 𝒲,
      (∃ y ∈ degZeroLoc P 𝒲, x * y = 1) ↔ ∀ W ∈ 𝒲, ∃ y ∈ degZeroLoc P {W}, x * y = 1

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

