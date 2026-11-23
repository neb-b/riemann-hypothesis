module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FGNullstellensatz.full : FGNullstellensatz.Statement :=
  FGNullstellensatz.proof

theorem ProjNullstellensatz.full : ProjNullstellensatz.Statement :=
  ProjNullstellensatz.proof FGNullstellensatz.full

theorem IncidenceGeneric.full : IncidenceGeneric.Statement :=
  IncidenceGeneric.proof FGNullstellensatz.full

theorem IncIdealPrime.full : IncIdealPrime.Statement :=
  IncIdealPrime.proof IncidenceGeneric.full

theorem ChowFormMultiHomog.full : ChowFormMultiHomog.Statement :=
  ChowFormMultiHomog.proof ProjNullstellensatz.full

theorem GenericLinearTrdeg.full : GenericLinearTrdeg.Statement :=
  GenericLinearTrdeg.proof

theorem MinimalPrimeHomog.full : MinimalPrimeHomog.Statement :=
  MinimalPrimeHomog.proof

theorem ConeDimComponent.full : ConeDimComponent.Statement :=
  ConeDimComponent.proof MinimalPrimeHomog.full

theorem LengthQuotientDet.full : LengthQuotientDet.Statement :=
  LengthQuotientDet.proof

theorem OrdPolynomialLocalization.full : OrdPolynomialLocalization.Statement :=
  OrdPolynomialLocalization.proof

theorem ChowFormBirational.full : ChowFormBirational.Statement :=
  ChowFormBirational.proof IncidenceGeneric.full ChowFormMultiHomog.full

theorem IncIdealDim.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    IncIdealDim.Statement :=
  IncIdealDim.proof IncidenceGeneric.full GenericLinearTrdeg.full hA

theorem ConeDimOfChowForm.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ConeDimOfChowForm.Statement :=
  ConeDimOfChowForm.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

theorem ChowFormExists.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ChowFormExists.Statement :=
  ChowFormExists.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartFirstGroupDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartFirstGroupDvd

theorem dvd_sub_aeval {R : Type*} [CommRing R] {n : ℕ} (a : MvPolynomial (Fin n) R)
    (σ : Fin n → MvPolynomial (Fin n) R) (hσ : ∀ m, a ∣ σ m - X m) (P : MvPolynomial (Fin n) R) :
    a ∣ P - aeval σ P := by
  set π := Ideal.Quotient.mk (Ideal.span {a})
  have h : π.comp (aeval σ).toRingHom = π := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π]
    · intro m
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, π]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hσ m
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  exact (RingHom.congr_fun h P).symm

variable {F : Type} [Field F] {n : ℕ}

theorem exists_injective (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (t : Fin n → F) (e : ℕ)
    (hI : IsProjPrime I) (ht : linForm t ∉ I) :
    ∃ φ : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)),
      Function.Injective φ ∧
      (∀ g, φ (chartX I t e g) = C (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) g)) ∧
      ∀ im, φ (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im)) =
        genSubst ((aeval (genPt I) (linForm t))⁻¹ • genPt I)
          (fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m)) im := by
  set K := FractionRing (MvPolynomial (Fin n) F ⧸ I)
  set η : Fin n → K := (aeval (genPt I) (linForm t))⁻¹ • genPt I with hη
  set ψ : MvPolynomial (Fin n) F →+* K := (aeval η).toRingHom with hψ
  have hJeq : RingHom.ker ψ = I ⊔ Ideal.span {linForm t - 1} := by
    rw [← ChartIncDomain.ker_aeval_eta I t hI ht]
    rfl
  set J := RingHom.ker ψ with hJ

  set q : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F ⧸ J := Ideal.Quotient.mk J with hq
  set ζ : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (X m) with hζ
  set c : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (C (t m)) with hc'
  have hc : ∑ l, c l * ζ l = 1 := by
    have h1 : q (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one q, ← map_sub, hq, Ideal.Quotient.eq_zero_iff_mem, hJeq]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, linForm, map_sum]
    simp only [map_mul, hζ, hc']

  set γ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    eval₂Hom (C.comp (q.comp C)) (Sum.elim (fun m => C (ζ m)) (genSubst ζ c)) with hγ
  have hγX : ∀ g, γ (rename Sum.inl g) = C (q g) := by
    intro g
    have : γ.comp (rename Sum.inl).toRingHom = C.comp q := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [hγ]
      · intro m; simp [hγ, hζ]
    exact RingHom.congr_fun this g
  have hker : chartIncIdeal I t e ≤ RingHom.ker γ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hγX, hq, (Ideal.Quotient.eq_zero_iff_mem).mpr (hJeq ▸ hg),
        map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← C_1, ← hc, map_sum]
        simp only [C_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hγ, coe_eval₂Hom, eval₂_X, Sum.elim_inl, Sum.elim_inr]
      simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
        sub_self]
  set γbar : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    Ideal.Quotient.lift (chartIncIdeal I t e) γ (fun a ha => RingHom.mem_ker.mp (hker ha)) with hγbar
  set χ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom with hχ
  have hJX : ∀ a ∈ J, χ a = 0 := by
    intro a ha
    rw [hJeq] at ha
    rw [hχ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

  set β : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) →+*
      MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    eval₂Hom (Ideal.Quotient.lift J χ hJX)
      (fun im => Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr im))) with hβ
  have hβγ : β.comp γ = Ideal.Quotient.mk (chartIncIdeal I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hβ, hγ, hq, hχ]
    · rintro (m | im)
      · simp [hβ, hγ, hζ, hq, hχ]
      · have h0 : Ideal.Quotient.mk (chartIncIdeal I t e)
            (∑ l, X (Sum.inr (im.1, l)) * X (Sum.inl l)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.subset_span ⟨im.1, rfl⟩)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul] at h0
        simp [hβ, hγ, hζ, hc', hq, hχ, genSubst]
        rw [h0, zero_mul]
  have hleft : ∀ x : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e, β (γbar x) = x := by
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x
    rw [hγbar, Ideal.Quotient.lift_mk]
    exact RingHom.congr_fun hβγ g
  have hinj : Function.Injective γbar := Function.LeftInverse.injective hleft

  have hjinj : Function.Injective (RingHom.kerLift ψ) := RingHom.kerLift_injective ψ
  refine ⟨(MvPolynomial.map (RingHom.kerLift ψ)).comp γbar, (map_injective _ hjinj).comp hinj, ?_, ?_⟩
  · intro g
    have h' : γbar (Ideal.Quotient.mk _ (rename Sum.inl g)) = C (q g) := by
      rw [hγbar, Ideal.Quotient.lift_mk]
      exact hγX g
    change MvPolynomial.map (RingHom.kerLift ψ) (γbar (Ideal.Quotient.mk _ (rename Sum.inl g))) = _
    rw [h', map_C, hq, RingHom.kerLift_mk]
    rfl
  · intro im
    have h' : γbar (Ideal.Quotient.mk _ (rename Sum.inr (X im))) = genSubst ζ c im := by
      rw [hγbar, Ideal.Quotient.lift_mk, rename_X]
      simp [hγ]
    change MvPolynomial.map (RingHom.kerLift ψ) (γbar (Ideal.Quotient.mk _ (rename Sum.inr (X im)))) = _
    rw [h', IncidenceGeneric.map_genSubst]
    congr 1
    · funext m
      change RingHom.kerLift ψ (Ideal.Quotient.mk _ (X m)) = _
      rw [RingHom.kerLift_mk, hψ]
      simp [η]
    · funext m
      change RingHom.kerLift ψ (Ideal.Quotient.mk _ (C (t m))) = _
      rw [RingHom.kerLift_mk, hψ]
      simp
      rfl

theorem proof (h₁ : IncidenceGeneric.Statement) : ChartFirstGroupDvd.Statement := by
  intro F _ n e I f t hI hf ht
  have := hI.isPrime
  obtain ⟨φ, hφinj, hφX, hφU⟩ := exists_injective I t e hI ht
  set τ : (FractionRing (MvPolynomial (Fin n) F ⧸ I)) := aeval (genPt I) (linForm t) with hτdef
  have hτ : τ ≠ 0 := by
    rw [hτdef, ChartIncDomain.aeval_genPt, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ht
  have hτsum : τ = ∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t l) * genPt I l := by
    simp [hτdef, linForm]
  set cK : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ I)) := fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m) / τ with hcK
  have homogComponent_comm_first_action : ∑ j, cK j * genPt I j = 1 := by
    simp only [hcK, div_mul_eq_mul_div, ← Finset.sum_div, ← hτsum]
    exact div_self hτ
  have hcKm : ∀ m, cK m = τ⁻¹ * algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m) := fun m => by
    simp only [hcK]
    ring
  have hfI : f ∈ incIdeal I (e + 1) := mem_incIdeal_iff.mpr ((hf.2 f).mpr dvd_rfl)
  have hgen : aeval (genSubst (genPt I) cK) f = 0 := (h₁ F n (e + 1) I cK homogComponent_comm_first_action f).mp hfI
  set θ : MvPolynomial (Fin n) (ChartInc I t e) := ∑ m, X m * C (chartX I t e (X m)) with hθ
  set σ : Fin n → MvPolynomial (Fin n) (ChartInc I t e) :=
    fun m => X m - θ * C (chartX I t e (C (t m))) with hσ
  have hdvd := dvd_sub_aeval θ σ (fun m => ⟨-C (chartX I t e (C (t m))), by simp only [hσ]; ring⟩)
    (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f))
  suffices h0 : aeval σ (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)) = 0 by
    rw [h0, sub_zero] at hdvd
    exact hdvd
  apply map_injective φ hφinj
  rw [map_zero]
  set ρ : MvPolynomial (Fin (e + 1) × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)) →+* MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))) :=
    eval₂Hom (C.comp C) (fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) with hρ
  have key : (MvPolynomial.map φ).comp ((aeval σ).toRingHom.comp
      ((MvPolynomial.map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e))).comp
        (aeval (fun ij : Fin (e + 1) × Fin n =>
          Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
            (X ij.2) (fun i => C (X (i, ij.2))) ij.1)).toRingHom)) =
      ρ.comp (aeval (genSubst (genPt I) cK) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin (e + 1) × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).toRingHom := by
    have hρ0 : ∀ m, ρ (X (0, m)) = X m := fun m => by simp [hρ]
    have hρs : ∀ (i : Fin e) m, ρ (X (i.succ, m)) = C (X (i, m)) := fun i m => by simp [hρ]
    have hρC : ∀ k, ρ (C k) = C (C k) := fun k => by simp [hρ]
    apply MvPolynomial.ringHom_ext
    · intro a
      have hCa : algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) = chartX I t e (C a) := by
        change Ideal.Quotient.mk _ (rename Sum.inr (C a)) = Ideal.Quotient.mk _ (rename Sum.inl (C a))
        rw [rename_C, rename_C]
      simp [hρC, hCa, hφX]
    · rintro ⟨i, m⟩
      cases i using Fin.cases with
      | zero =>
        simp [hρ0, hσ, hθ, hφX, hρC, genSubst]
        rw [hcKm]
        simp only [map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      | succ i =>
        simp [hρs, hρC, hφU, genSubst]
        rw [hcKm]
        simp only [map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hgen, map_zero] at this
  exact this

end ChartFirstGroupDvd

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Chart

variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem chartLoc_algebraMap_tower (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem chartX_C (c : F) :
    chartX I t e (C c) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C c) := by
  show Ideal.Quotient.mk _ (rename Sum.inl (C c)) = Ideal.Quotient.mk _ (rename Sum.inr (C c))
  simp only [rename_C]

theorem algebraMap_localization_C (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p),
    MvPolynomial.algebraMap_eq]

theorem chartLin_eq_sum (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, chartLoc_algebraMap_tower, chartX_C]

theorem chartLin_self : chartLin I t e t = 1 := by
  have h : chartX I t e (linForm t - 1) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

theorem chartLoc_adjoin_eq_top :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by
  set A := Algebra.adjoin (Localization.AtPrime p)
    (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))
  have hS : ∀ x : MvPolynomial (Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) ∈ A := by
    intro x
    rw [← chartLoc_algebraMap_tower]
    exact Subalgebra.algebraMap_mem A _
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hSig : ∀ y : MvPolynomial (Fin n ⊕ Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) ∈ A := by
    intro y
    induction y using MvPolynomial.induction_on with
    | C a =>
      have h : π (C a) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) := by
        show _ = Ideal.Quotient.mk _ (rename Sum.inr (C a))
        rw [rename_C]
        rfl
      rw [h]
      exact hS _
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb
    | mul_X a v ha =>
      rw [map_mul, map_mul]
      refine mul_mem ha ?_
      rcases v with m | im
      · refine Algebra.subset_adjoin ⟨m, ?_⟩
        show algebraMap (ChartInc I t e) (ChartLoc I t e p)
          ((Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) : ChartInc I t e)) = _
        rw [rename_X]
        rfl
      · have h : π (X (Sum.inr im)) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im) := by
          show _ = Ideal.Quotient.mk _ (rename Sum.inr (X im))
          rw [rename_X]
          rfl
        rw [h]
        exact hS _
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z
  obtain ⟨s₀, hs₀, hs⟩ := s.2
  obtain ⟨y, rfl⟩ : ∃ y, π y = x := Ideal.Quotient.mk_surjective x
  set w := algebraMap (Localization.AtPrime p) (ChartLoc I t e p)
    (IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin e × Fin n) F) ⟨s₀, hs₀⟩)
  have hw : algebraMap (ChartInc I t e) (ChartLoc I t e p) (s : ChartInc I t e) * w = 1 := by
    rw [← hs, ← chartLoc_algebraMap_tower, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one,
      IsLocalization.mk'_self, map_one]
  have hz : IsLocalization.mk' (ChartLoc I t e p) (π y) s =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) * w := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, mul_comm w, hw, mul_one]
  show IsLocalization.mk' (ChartLoc I t e p) (π y) s ∈ A
  rw [hz]
  exact mul_mem (hSig y) (Subalgebra.algebraMap_mem A _)

end Chart

theorem eval_map_firstGroup {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by
  rw [eval_map]
  simp only [firstGroup, specFirst]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, bind₁_C_right, MvPolynomial.algebraMap_apply, eval₂_C, MvPolynomial.algebraMap_eq]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), eval₂_add, ha, hb, map_add (f := _)]
  | mul_X a ij ha =>
    rw [map_mul, map_mul, eval₂_mul, ha, map_mul, aeval_X, bind₁_X_right]
    congr 1
    obtain ⟨i, m⟩ := ij
    cases i using Fin.cases with
    | zero => simp [specFirstVar, algebraMap_localization_C]
    | succ i => simp [specFirstVar]

theorem ChartNorm.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : LocalizationPrimeDVR.Statement) (h₄ : ChartFinite.Statement) (h₅ : ChartLocDomain.Statement)
    (h₆ : ChartFirstGroupPrime.Statement) (h₇ : ChartFirstGroupDvd.Statement)
    (h₈ : NormOfDividedForm.Statement) : ChartNorm.Statement := by
  intro F _ _ n e I f t p _ hI hf hp hft u
  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact hft (hmem ▸ p.zero_mem)
  obtain ⟨hdom, hinj, -⟩ := h₅ F n e I f t p hI hf htI
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₄ F n e I f t p hI hf hft
  have : IsPrincipalIdealRing (Localization.AtPrime p) := by
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · have hfield : IsField (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) := by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
          Ideal.map_bot]
      let := hfield.toField
      infer_instance
    · have := h₃ _ q _ hq rfl
      infer_instance
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) := Module.free_of_finite_type_torsion_free'
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (algebraMap F (Localization.AtPrime p)).injective
  have hsum : ∑ m, algebraMap F (Localization.AtPrime p) (t m) •
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) = 1 := by
    rw [← chartLin_eq_sum, chartLin_self, map_one]
  have hcomp : (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    RingHom.ext fun x => (chartLoc_algebraMap_tower I t p x).symm
  have hdvd := map_dvd (MvPolynomial.map (algebraMap (ChartInc I t e) (ChartLoc I t e p)))
    (h₇ F n e I f t hI hf htI)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_X, map_C, map_map, hcomp] at hdvd
  rw [← map_map] at hdvd
  have key := h₈ (Localization.AtPrime p) (ChartLoc I t e p) n _ _ _ (chartLoc_adjoin_eq_top I t p) hsum
    (h₆ F n e I f p hI hf) hdvd (fun m => algebraMap F (Localization.AtPrime p) (u m))
  rw [eval_map_firstGroup, eval_map_firstGroup, ← chartLin_eq_sum] at key
  exact key

end

end GroundTheory.Heights₂.Heights
end

