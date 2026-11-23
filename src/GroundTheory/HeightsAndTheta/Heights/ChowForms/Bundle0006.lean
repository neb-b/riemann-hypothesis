module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormBirational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem pderiv_aeval_eq_sum {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add (f := _), add_mul,
      Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · refine Finset.sum_congr rfl fun b _ => by ring

theorem pderiv_genSubst {K : Type*} [CommRing K] {n k : ℕ} (ζ c : Fin n → K) (i : Fin k) (m : Fin n)
    (j : Fin k × Fin n) :
    pderiv (i, m) (genSubst ζ c j) =
      (if j = (i, m) then 1 else 0) - (if j.1 = i then C (ζ m) * C (c j.2) else 0) := by
  classical
  obtain ⟨j₁, j₂⟩ := j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [genSubst, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
    map_sum, pderiv_X, Pi.single_apply, mul_zero]
  by_cases h : j₁ = i
  · subst h
    simp [Prod.ext_iff, eq_comm, mul_comm]
  · simp [Prod.ext_iff, h]

theorem not_dvd_pderiv_of_degreeOf_pos {F σ : Type*} [Field F] [CharZero F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hi : 0 < degreeOf i g) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hne : pderiv i g ≠ 0 := by
    obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup g.support (support_nonempty.2 hg) (fun m => m i)
    rw [← degreeOf_eq_sup] at hsd
    have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single i 1)) h0
    simp only [coeff_pderiv, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at this
    have hcs : AddMonoidAlgebra.coeff g s ≠ 0 := mem_support_iff.1 hs
    have hsi : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : F) + 1 ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero hcs hsi this
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem ChowFormBirational.proof (h₁ : IncidenceGeneric.Statement)
    (h₂ : ChowFormMultiHomog.Statement) : ChowFormBirational.Statement := by
  intro F _ _ n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (k + 1) P g hP hg
  obtain ⟨s, hs⟩ := support_nonempty.2 hg.1
  obtain ⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by
    by_contra hcon
    push Not at hcon
    have hw := congrFun (hhom (mem_support_iff.1 hs)) 0
    have : (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      obtain ⟨x₁, x₂⟩ := x
      by_cases hx : x₁ = 0
      · subst hx; simp [Nat.le_zero.1 (hcon x₂)]
      · simp [groupWeight, hx]
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩
  have hdeg : 0 < degreeOf (0, l) g := lt_of_lt_of_le hl (monomial_le_degreeOf _ hs)
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_degreeOf_pos hg.1 hdeg
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem constantCoeff_eq_zero_of_isProjPrime {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) {f : MvPolynomial (Fin n) F}
    (hf : f ∈ P) : constantCoeff f = 0 := by
  by_contra h
  have h0 : homogeneousComponent 0 f ∈ P := hP.isHomog f hf 0
  rw [homogeneousComponent_zero] at h0
  apply hP.isPrime.ne_top
  refine Ideal.eq_top_of_isUnit_mem _ h0 ?_
  have hc : AddMonoidAlgebra.coeff f 0 ≠ 0 := by simpa [constantCoeff] using h
  exact hc.isUnit.map C

theorem one_le_of_isProjPrime {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    (hk : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exfalso
    have := hP.isPrime
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := by
      rw [ringKrullDimZero_iff_ringKrullDim_eq_zero]
      simpa using hk
    have hmax : P.IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
    have hle : P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F) :=
      fun f hf => constantCoeff_eq_zero_of_isProjPrime hP hf
    have heq := hmax.eq_of_le (RingHom.ker_ne_top _) hle
    obtain ⟨j, hj⟩ := hP.isRelevant
    rw [heq] at hj
    exact hj (by simp [RingHom.mem_ker])
  · exact h

theorem ChowFormExists.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ChowFormExists.Statement := by
  intro F _ n k P hP hdim
  have hk : 1 ≤ k := one_le_of_isProjPrime hP hdim
  obtain ⟨j, -⟩ := hP.isRelevant
  have hn : 0 < n := j.pos
  have hQ : (incIdeal P k).IsPrime := h₂ F n k P hP.isPrime hP.isRelevant
  have hdimQ := h₁ F n k (k - 1) P hP (by rw [Nat.sub_add_cancel hk]; exact hdim)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  letI : (incIdeal P k).IsPrime := hQ
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (incIdeal P k)
  rw [hdimQ, hS] at hsum
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  obtain ⟨m, hm1, hm2⟩ : ∃ m, k * n - k + min k (k - 1) = m ∧ m + 1 = k * n :=
    ⟨_, rfl, by generalize k * n = N at hkn ⊢; omega⟩
  rw [hm1, ← hm2] at hsum
  have hht : (incIdeal P k).height = 1 := by
    generalize (incIdeal P k).height = h at hsum
    have h' : (h + m : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := by
      have : ((h + m : ℕ∞) : WithBot ℕ∞) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast at hsum ⊢
        exact hsum
      exact_mod_cast this
    induction h using ENat.recTopCoe with
    | top => exact (ENat.natCast_ne_top (m + 1) h'.symm).elim
    | coe a =>
      norm_cast at h' ⊢
      omega
  have hne : incIdeal P k ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hht
  obtain ⟨g, hgmem, hgp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ hne
  have hspan := Ideal.eq_span_singleton_of_height_eq_one hht hgmem hgp
  refine ⟨g, hgp.ne_zero, fun f => ?_⟩
  rw [← Ideal.mem_span_singleton, ← hspan]
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IsChowForm.incIdeal_eq_span {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm P k f) : incIdeal P k = Ideal.span {f} := by
  ext g
  rw [Ideal.mem_span_singleton, ← hf.2 g]
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem constantCoeff_eq_zero_of_isHomogIdeal {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsHomogIdeal P) (htop : P ≠ ⊤)
    {g : MvPolynomial (Fin n) F} (hg : g ∈ P) : constantCoeff g = 0 := by
  by_contra h
  have h0 := hP g hg 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact htop (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem IsProjPrime.not_isField_quotient {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) :
    ¬ IsField (MvPolynomial (Fin n) F ⧸ P) := by
  intro hfield
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at hy
  have := constantCoeff_eq_zero_of_isHomogIdeal hP.isHomog hP.isPrime.ne_top hy
  simp at this

theorem ConeDimOfChowForm.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ConeDimOfChowForm.Statement := by
  intro F _ n k P f hP hf
  have hspan := hf.incIdeal_eq_span
  have hprime : (Ideal.span {f}).IsPrime := hspan ▸ h₂ F n k P hP.isPrime hP.isRelevant
  have hnu : ¬ IsUnit f := fun hu => hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu)
  have hht : (Ideal.span {f}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf.1) hnu
  have hdimS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) (Ideal.span {f})
  rw [hht, hdimS] at hform
  have := hP.isPrime
  obtain ⟨m, hm, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MvPolynomial (Fin n) F ⧸ P)
  cases m with
  | zero =>
    exfalso
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := Ring.krullDimLE_iff.mpr (by rw [hm])
    exact hP.not_isField_quotient Ring.KrullDimLE.isField_of_isDomain
  | succ d =>
    have h := h₁ F n k d P hP hm
    rw [hspan] at h
    rw [h] at hform
    have h3 : ((1 + (k * n - k + min k d) : ℕ) : WithBot ℕ∞) = ((k * n : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
      convert hform using 2
    replace h3 := Nat.cast_injective h3
    rw [hm]
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      omega
    · have hkn := Nat.le_mul_of_pos_right k hn
      generalize k * n = N at h3 hkn
      omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PEmultiplicityOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem EmultiplicityOrd.proof (h₁ : LocalizationPrimeDVR.Statement) : EmultiplicityOrd.Statement := by
  intro R _ _ _ _ q x p _ hq hp hx
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₁ R q p hq hp
  set O := Localization.AtPrime p
  have hfin : FiniteMultiplicity q x := FiniteMultiplicity.of_prime_left hq hx
  obtain ⟨y, hxy, hy⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]

  have hyu : IsUnit (algebraMap R O y) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O p y]
    change y ∉ p
    rw [hp, Ideal.mem_span_singleton]
    exact hy

  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R O q) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hnz : algebraMap R O q ∈ nonZeroDivisors O :=
    mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz,
    Ring.ord_of_irreducible hirr]
  simp

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealBelow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

private def shiftGroup {e n : ℕ} (ij : Fin e × Fin n) : Fin (e + 1) × Fin n := (ij.1.succ, ij.2)

private theorem shiftGroup_injective {e n : ℕ} : Function.Injective (shiftGroup (e := e) (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftGroup, Prod.mk.injEq, Fin.succ_inj] at h
  rw [h.1, h.2]

private def killFirst {F : Type*} [Field F] {e n : ℕ} (ij : Fin (e + 1) × Fin n) :
    MvPolynomial (Fin (e + 1) × Fin n) F :=
  if ij.1 = 0 then 0 else X ij

private theorem aeval_killFirst_eq_zero {F : Type*} [Field F] {e n δ : ℕ} (hδ : 1 ≤ δ)
    {f : MvPolynomial (Fin (e + 1) × Fin n) F} (hf : IsMultiHomog δ f) :
    aeval (killFirst (F := F)) f = 0 := by
  classical
  rw [aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := congrFun (hf (mem_support_iff.mp hd)) 0
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
  have hne : (∑ c ∈ d.support, (d c • groupWeight (e + 1) n c) 0) ≠ 0 := by rw [hw]; omega
  obtain ⟨ij, hij, hij0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 : ij.1 = 0 := by
    by_contra h
    apply hij0
    simp [groupWeight, Ne.symm h]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hij ?_)
  rw [killFirst, if_pos h1]
  exact zero_pow (Finsupp.mem_support_iff.mp hij)

theorem IncIdealBelow.proof (h₁ : ChowFormMultiHomog.Statement) : IncIdealBelow.Statement := by
  intro F _ n e I f hI hf
  classical
  obtain ⟨δ, hδ, hmh⟩ := h₁ F n (e + 1) I f hI hf
  rw [eq_bot_iff]
  intro g hg
  rw [Ideal.mem_bot]
  set g' : MvPolynomial (Fin (e + 1) × Fin n) F := rename shiftGroup g with hg'
  have hvan : ∀ v ∈ incidence I (e + 1), aeval v g' = 0 := by
    rintro v ⟨x, hx0, hxI, hxv⟩
    rw [hg', aeval_rename]
    exact (mem_incIdeal_iff.mp hg) (v ∘ shiftGroup) ⟨x, hx0, hxI, fun i => hxv i.succ⟩
  obtain ⟨h, hh⟩ := (hf.2 g').mp hvan
  have hfix : aeval (killFirst (F := F)) g' = g' := by
    rw [hg', aeval_rename]
    conv_rhs => rw [← aeval_X_left_apply (rename shiftGroup g), aeval_rename]
    congr 1
  have hzero : g' = 0 := by
    rw [← hfix, hh, map_mul, aeval_killFirst_eq_zero hδ hmh, zero_mul]
  exact rename_injective _ shiftGroup_injective (by rw [← hg', hzero, map_zero])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLocalizationPrimeDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem LocalizationPrimeDVR.proof : LocalizationPrimeDVR.Statement := by
  intro R _ _ _ _ q p _ hq hp
  set O := Localization.AtPrime p
  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O,
      congrArg (Ideal.map (algebraMap R O)) hp, Ideal.map_span, Set.image_singleton]
  have hprin : (maximalIdeal O).IsPrincipal := ⟨⟨algebraMap R O q, hmax⟩⟩
  have hPID : IsPrincipalIdealRing O :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain O).out 5 1).mp hprin
  have hq0 : algebraMap R O q ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap R O) :=
      IsLocalization.injective O (p.primeCompl_le_nonZeroDivisors)
    exact hq.ne_zero (hinj (by rw [h, map_zero]))
  have hne : maximalIdeal O ≠ ⊥ := by
    rw [hmax, Ne, Ideal.span_singleton_eq_bot]
    exact hq0
  exact { hPID with not_a_field' := hne }

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PSpecFirstMemIncIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SpecFirstMemIncIdeal.proof : SpecFirstMemIncIdeal.Statement := by
  intro F _ n e I W f t hf hIW ht
  rw [mem_incIdeal_iff]
  rintro v ⟨x, hx0, hxW, hv⟩
  let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
    Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F (AlgebraicClosure F) (t ij.2))
      (fun i => v (i, ij.2)) ij.1
  have hw : w ∈ incidence I (e + 1) := by
    refine ⟨x, hx0, fun g hg => hxW g (hIW hg), fun i => ?_⟩
    induction i using Fin.cases with
    | zero =>
      have h := hxW _ ht
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [w, linForm, map_sum, aeval_X, aeval_C] using h
    | succ i => simpa [w] using hv i
  have hfw : aeval w f = 0 := (hf.2 f).mpr dvd_rfl w hw
  have hev : aeval v (specFirst f t) = aeval w f := by
    rw [specFirst, aeval_bind₁]
    congr 2
    funext ij
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [specFirstVar, w]
    | succ i => simp [specFirstVar, w]
  rw [hev, hfw]

end GroundTheory.Heights₂.Heights
end

