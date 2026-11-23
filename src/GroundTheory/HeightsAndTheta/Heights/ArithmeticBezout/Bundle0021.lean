module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjDegreeChow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ProjDegreeChow.proof (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by
  intro n e δ W f A hW hf hδ hA
  rw [h₁ n e W A]
  obtain ⟨hdom, hfin⟩ := h₂ n e W A hW.isPrime hA
  have hc := h₃ n e W f A hW hf hA
  have hsep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
      (Vertical.SecAlg
        (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
        (projPar A)) :=
    ⟨fun x => PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  refine le_antisymm (h₄ ℂ _ n e δ W f (projPar A) hW hf hδ hfin hdom hsep fun h => hc ?_)
    (h₅ ℂ _ n e δ W f (projPar A) hW hf hδ hc).2
  rw [h, map_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjSecDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjSecDomain

abbrev Kf (e : ℕ) : Type := FractionRing (MvPolynomial (Fin (e + 1)) ℂ)

variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)

abbrev S : Type :=
  Vertical.SecAlg (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)

theorem map_linPoly (k : Fin (e + 1)) :
    MvPolynomial.map (algebraMap ℂ (Kf e)) (ComplexSets.linPoly A k) =
      linForm fun j => algebraMap ℂ (Kf e) (A k j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ComplexSets.linPoly, linForm, map_sum]

theorem projVar_ne_zero (k : Fin (e + 1)) : projVar e k ≠ 0 := by
  rw [projVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact X_ne_zero k

theorem chartForm_eq : Vertical.chartForm (projPar A) =
    C (projVar e 0)⁻¹ * linForm fun j => algebraMap ℂ (Kf e) (A 0 j) := by
  simp [Vertical.chartForm, linForm, projPar, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm]

theorem secForm_eq (i : Fin e) : Vertical.secForm (projPar A) i =
    C (projVar e i.succ) * (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) -
      C (projVar e 0) * linForm fun j => algebraMap ℂ (Kf e) (A i.succ j) := by
  simp [Vertical.secForm, linForm, projPar, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]

variable {W A}

theorem mk_row (k : Fin (e + 1)) :
    Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
        (linForm fun j => algebraMap ℂ (Kf e) (A k j)) =
      algebraMap (Kf e) (S W A) (projVar e k) := by
  set q := Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
  have hC : ∀ c, q (C c) = algebraMap (Kf e) (S W A) c := fun _ => rfl
  have hu : q (C (projVar e 0)) * q (C ((projVar e 0)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero 0), map_one, map_one]
  have hch : q (Vertical.chartForm (projPar A) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [map_sub, map_one, chartForm_eq, map_mul] at hch
  have ha0 : q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) = q (C (projVar e 0)) := by
    linear_combination q (C (projVar e 0)) * hch - q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) * hu
  induction k using Fin.cases with
  | zero => rw [ha0, hC]
  | succ i =>
    have hs : q (Vertical.secForm (projPar A) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_eq, map_sub, map_mul, map_mul, ha0] at hs
    rw [← hC]
    linear_combination (-q (C ((projVar e 0)⁻¹))) * hs +
      (q (C (projVar e i.succ)) - q (linForm fun j => algebraMap ℂ (Kf e) (A i.succ j))) * hu

variable (W A)

def psi : MvPolynomial (Fin n) ℂ ⧸ W →+* S W A :=
  Ideal.Quotient.lift W
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap ℂ (Kf e))))
    fun _ hf => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)))

def M : Submonoid (MvPolynomial (Fin n) ℂ ⧸ W) :=
  (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)).map (ComplexSets.projHom W A)

abbrev T : Type := Localization (M W A)

def kappa : Kf e →+* T W A :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) (S := Kf e) (P := T W A)
    (g := (algebraMap _ (T W A)).comp (ComplexSets.projHom W A).toRingHom)
    fun y => IsLocalization.map_units (T W A) (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : M W A)

def phi : MvPolynomial (Fin n) (Kf e) →+* T W A :=
  eval₂Hom (kappa W A) fun j => algebraMap _ (T W A) (Ideal.Quotient.mk W (X j))

variable {W A}

theorem psi_mk (f : MvPolynomial (Fin n) ℂ) : psi W A (Ideal.Quotient.mk W f) =
    Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℂ (Kf e)) f) := rfl

theorem projHom_X (k : Fin (e + 1)) :
    ComplexSets.projHom W A (X k) = Ideal.Quotient.mk W (ComplexSets.linPoly A k) := by
  rw [ComplexSets.projHom, AlgHom.comp_apply, ComplexSets.pullback, aeval_X]; rfl

theorem psi_comp_projHom :
    (psi W A).comp (ComplexSets.projHom W A).toRingHom =
      (algebraMap (Kf e) (S W A)).comp (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · have h1 : algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e) (C r) = algebraMap ℂ (Kf e) r :=
      (IsScalarTower.algebraMap_apply ℂ _ (Kf e) r).symm
    have h2 : ComplexSets.projHom W A (C r) = Ideal.Quotient.mk W (C r) := (ComplexSets.projHom W A).commutes r
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, psi_mk,
      map_C]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projHom_X,
      psi_mk, map_linPoly, mk_row]
    rfl

theorem kappa_alg (p : MvPolynomial (Fin (e + 1)) ℂ) :
    kappa W A (algebraMap _ (Kf e) p) = algebraMap _ (T W A) (ComplexSets.projHom W A p) := by
  unfold kappa; exact IsLocalization.lift_eq _ p

theorem phi_C (c : Kf e) : phi W A (C c) = kappa W A c := eval₂Hom_C _ _ _

theorem phi_map (f : MvPolynomial (Fin n) ℂ) :
    phi W A (MvPolynomial.map (algebraMap ℂ (Kf e)) f) = algebraMap _ (T W A) (Ideal.Quotient.mk W f) := by
  have : (phi W A).comp (MvPolynomial.map (algebraMap ℂ (Kf e))) =
      (algebraMap _ (T W A)).comp (Ideal.Quotient.mk W) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_C, phi_C,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Kf e), kappa_alg, AlgHom.commutes]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_X, phi, eval₂Hom_X']
  exact RingHom.congr_fun this f

theorem phi_row (k : Fin (e + 1)) :
    phi W A (linForm fun j => algebraMap ℂ (Kf e) (A k j)) = kappa W A (projVar e k) := by
  rw [← map_linPoly, phi_map, projVar, kappa_alg, projHom_X]

theorem secIdeal_le_ker :
    Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A) ≤
      RingHom.ker (phi W A) := by
  have hu : kappa W A (projVar e 0)⁻¹ * kappa W A (projVar e 0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (projVar_ne_zero 0), map_one]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]; intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, phi_map, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm_eq, map_sub, map_mul, map_mul, phi_C, phi_C, phi_row,
      phi_row]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      chartForm_eq, map_mul, phi_C, phi_row, hu, sub_self]

variable (W A)

def g : S W A →+* T W A := Ideal.Quotient.lift _ (phi W A) fun _ hf => RingHom.mem_ker.1 (secIdeal_le_ker hf)

theorem psi_unit (y : M W A) : IsUnit (psi W A y) := by
  obtain ⟨_, p, hp, rfl⟩ := y
  have h := RingHom.congr_fun (psi_comp_projHom (W := W) (A := A)) p
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  exact (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map _

def chi : T W A →+* S W A :=
  IsLocalization.lift (M := M W A) (S := T W A) (P := S W A) (g := psi W A) (psi_unit W A)

variable {W A}

theorem chi_kappa : (chi W A).comp (kappa W A) = algebraMap (Kf e) (S W A) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) ?_
  rw [RingHom.comp_assoc, kappa, IsLocalization.lift_comp, ← RingHom.comp_assoc, chi,
    IsLocalization.lift_comp, psi_comp_projHom]

theorem chi_g (s : S W A) : chi W A (g W A s) = s := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  have : (chi W A).comp (phi W A) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, phi_C, ← RingHom.comp_apply, chi_kappa]; rfl
    · rw [RingHom.comp_apply, phi, eval₂Hom_X', chi, IsLocalization.lift_eq, psi_mk, map_X]
  show chi W A (phi W A f) = _
  exact RingHom.congr_fun this f

theorem proof : ProjSecDomain.Statement := by
  intro n e W A hW hA
  have hM : M W A ≤ nonZeroDivisors _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero hp (hA.injective (by rw [map_zero]; exact h))
  have : IsDomain (T W A) := IsLocalization.isDomain_localization hM
  refine ⟨Function.Injective.isDomain (g W A) (Function.LeftInverse.injective chi_g), ?_⟩
  let _ : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have hint (j : Fin n) : IsIntegral (Kf e) (Ideal.Quotient.mk
      (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)) (X j)) := by
    have := IsIntegral.map_of_comp_eq (algebraMap _ (Kf e)) (psi W A) psi_comp_projHom.symm
      (hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j)))
    rwa [psi_mk, map_X] at this
  have : Algebra.IsIntegral (Kf e) (S W A) := ⟨fun s => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p j hp => rw [map_mul]; exact hp.mul (hint j)⟩
  have : Algebra.FiniteType (Kf e) (S W A) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (Kf e) _)
      (Ideal.Quotient.mkₐ_surjective _ _)
  exact Algebra.IsIntegral.finite

end ProjSecDomain

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProperSymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Ideal

theorem localMult_ne_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by
  have hPp : P.IsPrime := hP.1.1
  unfold localMult
  rw [dite_eq_left hPp]
  let R := Localization.AtPrime P
  let I : Ideal R := J.map (algebraMap A R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hP
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherian R (R ⧸ I) := isNoetherian_quotient I
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ne, ENat.toNat_eq_zero, not_or]
  exact ⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem map_specFirst {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {k n : ℕ}
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial.map φ (specFirst f u) = specFirst (MvPolynomial.map φ f) (fun j => φ (u j)) := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar]
  | succ i => simp [specFirstVar]

theorem ChowHeightRecursion.proof (hV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) :
    ChowHeightRecursion.Statement := by
  intro K _ _ n e δ H I f u hI hf hδ hu
  set u' : Fin n → K := fun j => (u j : K) with hu'
  set g := specFirst f u' with hg

  have hfin_f := log_gaussNorm_support_finite (K := K) hf.1
  have hfin_g : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v g)).Finite := by
    by_cases hg0 : g = 0
    · have : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => Real.log (gaussNorm v g)) = 0 := by
        funext v
        rw [hg0]
        simp [gaussNorm]
        exact Or.inl rfl
      rw [this, Function.support_zero]
      exact Set.finite_empty
    · exact log_gaussNorm_support_finite hg0
  have hfinsum : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g)) + vertTerm I (e + 1) u := by
    unfold vertTerm
    rw [← finsum_add_distrib hfin_g]
    · refine finsum_congr fun v => ?_
      rw [← hV K n e I f u hI hf hu v]
      ring
    · refine Set.Finite.subset (hfin_f.union hfin_g) fun v hv => ?_
      rw [Function.mem_support, ← hV K n e I f u hI hf hu v] at hv
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
      exact hv (by rw [hcon.1, hcon.2, sub_zero])

  have harch : ∀ σ : K →+* ℂ, mahler (H.normAt σ) (e + 1) (f.map σ) =
      mahler (H.normAt σ) e (g.map σ) - δ * (harmonic (n - 1) : ℝ) / 2 -
        cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    intro σ
    obtain ⟨hprime, hcyc⟩ := hB K n (e + 1) I f σ hI hf
    have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
      (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
    have h := hA n e δ (H.normAt σ) _ _ (fun j => σ (u j)) hprime hcyc hδσ
      (fun W hW => hAv K n I u' σ hI hu W hW)
    rw [hg, map_specFirst, h]
    ring
  unfold chowHt
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) (e + 1) (f.map σ) +
        ((e + 1 : ℕ) : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) e (g.map σ) + (e : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) -
        ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [harch σ]
    push_cast
    ring
  rw [hfinsum, hs]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionOrderAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrderAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoiceAlgClosed.Statement) (h₄ : Vertical.SpecFirstNeField.Statement)
    (h₅ : LocalizationPrimeDVR.Statement) (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement)
    (h₈ : ChartLocDomain.Statement) (h₉ : ChartNormAlgClosed.Statement)
    (h₁₀ : ChartLengthAlgClosed.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrderAlgClosed.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

section Objects

variable {n : ℕ}



def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1


end Objects


end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

end
end

