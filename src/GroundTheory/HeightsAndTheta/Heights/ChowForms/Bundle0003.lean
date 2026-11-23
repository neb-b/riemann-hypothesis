module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericLinearTrdeg.Statement : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (N k d : ℕ) (η : Fin N → E),
    Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = d →
      Algebra.trdeg F (Algebra.adjoin F
        (Set.range (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E)) ∪
          Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m)))) = ((k * N + min k d : ℕ) : Cardinal)

def IncIdealDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal P k) =
        ((k * n - k + min k d : ℕ) : WithBot ℕ∞)

def ChowFormBirational.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def AffineChartTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (j : Fin n), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) → X j ∉ P →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) =
        ((d : ℕ) : Cardinal)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

theorem mem_incIdeal_iff {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v g = 0 := by
  simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

theorem isChowForm_iff {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [mem_incIdeal_iff, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← mem_incIdeal_iff, h, Ideal.mem_span_singleton]

theorem dvd_of_forall_emultiplicity_le {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p, Irreducible p → emultiplicity p a ≤ emultiplicity p b) : a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime generalizing b with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact hx.dvd
  | h₃ a p ha' hp ih =>
    have hpp : emultiplicity p p = 1 :=
      (FiniteMultiplicity.of_not_isUnit hp.not_isUnit hp.ne_zero).emultiplicity_self
    have hpb : p ∣ b := by
      apply dvd_of_emultiplicity_pos
      have := h p hp.irreducible
      rw [emultiplicity_mul hp, hpp] at this
      exact lt_of_lt_of_le (by simp) this
    obtain ⟨b', rfl⟩ := hpb
    have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
    refine mul_dvd_mul_left p (ih ha' hb' fun q hq => ?_)
    have hqp : Prime q := hq.prime
    have hfin : emultiplicity q p ≠ ⊤ := by
      rw [Ne, emultiplicity_eq_top, not_not]
      exact FiniteMultiplicity.of_not_isUnit hqp.not_isUnit hp.ne_zero
    have := h q hq
    rw [emultiplicity_mul hqp, emultiplicity_mul hqp] at this
    exact (WithTop.add_le_add_iff_left hfin).mp this

theorem ChowFormSection.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncIdealPrime.Statement) (h₅ : SectionOrder.Statement) :
    ChowFormSection.Statement := by
  intro F _ _ n e I f u hI hf hu
  classical
  obtain ⟨hh0, hord⟩ := h₅ F n e I f u hI hf hu
  have hdim := h₁ F n (e + 1) I f hI hf
  have hcomp : ∀ W ∈ (divCycle I u).support, W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    by_contra h
    exact hW (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
  have hW1 : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := fun W hW =>
    h₂ F n e I W u hI hdim hu (hcomp W hW)
  have hex : ∀ W ∈ (divCycle I u).support, ∃ g, IsChowForm W e g := fun W hW =>
    h₃ F n e W (hW1 W hW).1 (hW1 W hW).2
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F :=
    fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1
  have hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W) := fun W hW => by
    simp only [g, dif_pos (hex W hW)]
    exact (hex W hW).choose_spec
  have hspan : ∀ W ∈ (divCycle I u).support, incIdeal W e = Ideal.span {g W} := fun W hW =>
    (isChowForm_iff.mp (hg W hW)).2
  have hgprime : ∀ W ∈ (divCycle I u).support, Prime (g W) := by
    intro W hW
    have hp := h₄ F n e W (hW1 W hW).1.isPrime (hW1 W hW).1.isRelevant
    rw [hspan W hW] at hp
    exact (Ideal.span_singleton_prime (isChowForm_iff.mp (hg W hW)).1).mp hp
  set Pr := ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W with hPr
  have hPr0 : Pr ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hgprime W hW).ne_zero
  have hmult : ∀ q, Irreducible q → emultiplicity q Pr = emultiplicity q (specFirst f u) := by
    intro q hq
    have hqp : Prime q := hq.prime
    rw [hord q hq, hPr, Finset.emultiplicity_prod hqp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [emultiplicity_pow hqp]
    split_ifs with hs
    · have hass : Associated q (g W) := by
        rw [← Ideal.span_singleton_eq_span_singleton, hs, hspan W hW]
      rw [← emultiplicity_eq_of_associated_left hass,
        (FiniteMultiplicity.of_not_isUnit (hgprime W hW).not_isUnit (hgprime W hW).ne_zero).emultiplicity_self,
        mul_one]
    · have : emultiplicity q (g W) = 0 := by
        rw [emultiplicity_eq_zero]
        intro hdvd
        apply hs
        rw [hspan W hW, Ideal.span_singleton_eq_span_singleton]
        exact hq.associated_of_dvd (hgprime W hW).irreducible hdvd
      rw [this, mul_zero]
  have hass : Associated Pr (specFirst f u) :=
    associated_of_dvd_dvd
      (dvd_of_forall_emultiplicity_le hPr0 hh0 fun q hq => (hmult q hq).le)
      (dvd_of_forall_emultiplicity_le hh0 hPr0 fun q hq => (hmult q hq).ge)
  obtain ⟨v, hv⟩ := hass
  obtain ⟨c, hc, hvc⟩ := (isUnit_iff_eq_C_of_isReduced (P := (v : MvPolynomial (Fin e × Fin n) F))).mp
    v.isUnit
  refine ⟨c, hc.ne_zero, g, hg, ?_⟩
  rw [← hv, hvc, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FGNullstellensatz.proof : FGNullstellensatz.Statement := by
  intro F _ D _ _ _ _ r hr
  have hJ : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := F)
  have hmem : r ∈ (⊥ : Ideal D).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    let _ : Field (D ⧸ m) := Ideal.Quotient.field m
    have : Algebra.FiniteType F (D ⧸ m) := inferInstance
    have : Module.Finite F (D ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (D ⧸ m)
    have : Algebra.IsAlgebraic F (D ⧸ m) := inferInstance
    let ψ : (D ⧸ m) →ₐ[F] AlgebraicClosure F := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h0 : ψ (Ideal.Quotient.mkₐ F m r) = 0 := hr (ψ.comp (Ideal.Quotient.mkₐ F m))
    have h1 : Ideal.Quotient.mkₐ F m r = 0 := (map_eq_zero_iff ψ ψ.toRingHom.injective).mp h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  rw [← Ideal.radical_eq_jacobson] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact IsReduced.eq_zero r ⟨k, by simpa using hk⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealPrime.proof (h₁ : IncidenceGeneric.Statement) : IncIdealPrime.Statement := by
  intro F _ n k P hP hrel
  have := hP
  obtain ⟨j, hj⟩ := hrel
  have hξ : genPt P j ≠ 0 := by
    unfold genPt
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) := Pi.single j (genPt P j)⁻¹ with hc
  have hsum : ∑ l, c l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [hc, inv_mul_cancel₀ hξ]
    · intro b _ hb
      simp [hc, Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hker : incIdeal P k =
      RingHom.ker (aeval (genSubst (k := k) (genPt P) c) :
        MvPolynomial (Fin k × Fin n) F →ₐ[F]
          MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) := by
    ext g
    rw [RingHom.mem_ker]
    exact h₁ F n k P c hsum g
  rw [hker]
  exact RingHom.ker_isPrime _

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncidenceGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace IncidenceGeneric

theorem hom_aeval {F σ R T : Type*} [Field F] [CommRing R] [CommRing T] [Algebra F R] [Algebra F T]
    (Φ : R →+* T) (hΦ : ∀ r : F, Φ (algebraMap F R r) = algebraMap F T r) (y : σ → R)
    (g : MvPolynomial σ F) : Φ (aeval y g) = aeval (fun s => Φ (y s)) g := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  ext r
  exact hΦ r

theorem map_genSubst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n k : ℕ}
    (ζ c : Fin n → R) (ij : Fin k × Fin n) :
    map φ (genSubst ζ c ij) = genSubst (fun l => φ (ζ l)) (fun l => φ (c l)) ij := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genSubst, map_sum]

theorem aeval_genSubst_genSubst {R : Type*} [CommRing R] {n k : ℕ} (ζ c c' : Fin n → R)
    (hc : ∑ l, c l * ζ l = 1) (ij : Fin k × Fin n) :
    aeval (genSubst ζ c) (genSubst ζ c' ij) = genSubst ζ c ij := by
  have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin k × Fin n) R) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← C_1, ← hc, map_sum]
    simp only [C_mul]
  have h0 : ∑ l, genSubst ζ c (ij.1, l) * C (ζ l) = 0 := by
    simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
      sub_self]
  rw [show genSubst ζ c' ij = X ij - (∑ l, X (ij.1, l) * C (ζ l)) * C (c' ij.2) from rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_mul, map_sum, aeval_X, aeval_C, algebraMap_eq, h0, zero_mul, sub_zero]

theorem aeval_genSubst_eq_zero_of {F R : Type*} [Field F] [CommRing R] [Algebra F R] {n k : ℕ}
    (ζ c c' : Fin n → R) (hc : ∑ l, c l * ζ l = 1) (g : MvPolynomial (Fin k × Fin n) F)
    (h : aeval (genSubst ζ c') g = 0) : aeval (genSubst ζ c) g = 0 := by
  have := hom_aeval (F := F) (aeval (genSubst ζ c) : MvPolynomial (Fin k × Fin n) R →ₐ[R] _).toRingHom
    (fun r => by simp [MvPolynomial.algebraMap_apply]) (genSubst ζ c') g
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_genSubst_genSubst ζ c c' hc, h,
    map_zero] at this
  exact this.symm

theorem mem_incIdeal_of_aeval_eq_zero {F : Type*} [Field F] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)))
    (g : MvPolynomial (Fin k × Fin n) F) (h : aeval (genSubst (genPt P) c) g = 0) :
    g ∈ incIdeal P k := by
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  intro v hv
  obtain ⟨x, hx0, hxP, hvx⟩ := hv
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx0
  set a : (MvPolynomial (Fin n) F ⧸ P) := Ideal.Quotient.mk P (X j) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    apply hj
    simpa using hxP _ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hξj : genPt P j ≠ 0 := by
    show algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P)) a ≠ 0
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]

  obtain ⟨c', hc'_def⟩ : ∃ c' : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)), c' = Pi.single j (genPt P j)⁻¹ := ⟨_, rfl⟩
  have hc' : ∑ l, c' l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [hc'_def, Pi.single_eq_of_ne hl, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), hc'_def, Pi.single_eq_same, inv_mul_cancel₀ hξj]
  have h' : aeval (genSubst (genPt P) c') g = 0 := aeval_genSubst_eq_zero_of _ c' c hc' g h

  let L := Localization.Away a
  have hθu : IsUnit (algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P)) a) := isUnit_iff_ne_zero.mpr hξj
  let θ : L →+* (FractionRing (MvPolynomial (Fin n) F ⧸ P)) := IsLocalization.Away.lift a hθu
  have hθinj : Function.Injective θ := by
    unfold θ IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro y z
    rw [(IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff,
      (IsFractionRing.injective (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).eq_iff]
  let ev : (MvPolynomial (Fin n) F ⧸ P) →+* AlgebraicClosure F :=
    Ideal.Quotient.lift P (aeval x).toRingHom (fun p hp => hxP p hp)
  have hev : ∀ p, ev (Ideal.Quotient.mk P p) = aeval x p := fun p => rfl
  have hψu : IsUnit (ev a) := isUnit_iff_ne_zero.mpr (by rw [ha_def, hev, aeval_X]; exact hj)
  let ψ : L →+* AlgebraicClosure F := IsLocalization.Away.lift a hψu
  let ξL : Fin n → L := fun l => algebraMap (MvPolynomial (Fin n) F ⧸ P) L (Ideal.Quotient.mk P (X l))
  let cL : Fin n → L := Pi.single j (IsLocalization.Away.invSelf a)
  have hθξ : ∀ l, θ (ξL l) = genPt P l := fun l => IsLocalization.Away.lift_eq a hθu _
  have hθinv : θ (IsLocalization.Away.invSelf a) = (genPt P j)⁻¹ := by
    have := congrArg θ (IsLocalization.Away.mul_invSelf (S := L) a)
    rw [map_mul, map_one, show θ (algebraMap (MvPolynomial (Fin n) F ⧸ P) L a) = genPt P j from hθξ j] at this
    exact eq_inv_of_mul_eq_one_right this
  have hθc : ∀ l, θ (cL l) = c' l := by
    intro l
    by_cases hl : l = j
    · subst hl; simp [cL, hc'_def, hθinv]
    · simp [cL, hc'_def, Pi.single_eq_of_ne hl]
  have hψξ : ∀ l, ψ (ξL l) = x l := fun l => by
    rw [IsLocalization.Away.lift_eq, hev, aeval_X]

  let f₀ : F →+* MvPolynomial (Fin k × Fin n) L :=
    C.comp ((algebraMap (MvPolynomial (Fin n) F ⧸ P) L).comp (algebraMap F (MvPolynomial (Fin n) F ⧸ P)))
  let Q := eval₂ f₀ (genSubst ξL cL) g
  have hQ : map θ Q = aeval (genSubst (genPt P) c') g := by
    rw [eval₂_comp_left, aeval_def]
    congr 1
    · ext r
      simp [f₀, θ, MvPolynomial.algebraMap_apply, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))]
    · funext ij
      simp only [Function.comp_apply, map_genSubst, hθξ, hθc]
  have hQ0 : Q = 0 := by
    apply map_injective θ hθinj
    rw [hQ, h', map_zero]
  have hvQ : eval₂Hom ψ v Q = aeval v g := by
    rw [eval₂_comp_left, aeval_def]
    congr 1
    · ext r
      simp only [f₀, RingHom.coe_comp, Function.comp_apply, eval₂Hom_C]
      rw [IsLocalization.Away.lift_eq, ← Ideal.Quotient.mk_algebraMap, hev, AlgHom.commutes]
    · funext ij
      simp [genSubst, hψξ, hvx ij.1]
  rw [← hvQ, hQ0, map_zero]

theorem aeval_eq_zero_of_mem_incIdeal (h₁ : FGNullstellensatz.Statement) {F : Type} [Field F]
    {n k : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)) (hc : ∑ j, c j * genPt P j = 1)
    (g : MvPolynomial (Fin k × Fin n) F) (hg : g ∈ incIdeal P k) :
    aeval (genSubst (genPt P) c) g = 0 := by
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker] at hg

  let e : MvPolynomial (Fin n ⊕ Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ P) :=
    aeval (Sum.elim (genPt P) c)
  let D := e.range
  have : Algebra.FiniteType F D :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have : Algebra.FiniteType F (MvPolynomial (Fin k × Fin n) D) :=
    Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  let ξD : Fin n → D := fun l => ⟨genPt P l, X (Sum.inl l), by simp [e]⟩
  let cD : Fin n → D := fun l => ⟨c l, X (Sum.inr l), by simp [e]⟩
  have hD : ∑ l, cD l * ξD l = 1 := Subtype.ext (by simpa [ξD, cD] using hc)
  let r : MvPolynomial (Fin k × Fin n) D := aeval (genSubst ξD cD) g
  have hr : map D.val.toRingHom r = aeval (genSubst (genPt P) c) g := by
    show map D.val.toRingHom (aeval (genSubst ξD cD) g) = _
    rw [hom_aeval (F := F) (R := MvPolynomial (Fin k × Fin n) D)
      (T := MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) (map D.val.toRingHom) (fun s => by simp [MvPolynomial.algebraMap_apply])]
    rw [show (fun s => map D.val.toRingHom (genSubst ξD cD s)) = genSubst (genPt P) c from
      funext fun ij => by rw [map_genSubst]; rfl]
  rw [← hr]
  suffices r = 0 by rw [this, map_zero]
  refine h₁ F (MvPolynomial (Fin k × Fin n) D) r fun φ => ?_

  let x : Fin n → AlgebraicClosure F := fun l => φ (C (ξD l))
  let cx : Fin n → AlgebraicClosure F := fun l => φ (C (cD l))
  let w : Fin k × Fin n → AlgebraicClosure F := fun ij => φ (X ij)
  let v : Fin k × Fin n → AlgebraicClosure F :=
    fun ij => w ij - (∑ l, w (ij.1, l) * x l) * cx ij.2
  have hφC : ∀ s : F, φ (C (algebraMap F D s)) = algebraMap F (AlgebraicClosure F) s := fun s => by
    rw [← MvPolynomial.algebraMap_apply, AlgHom.commutes]
  set_option synthInstance.maxHeartbeats 200000 in
  have key : ∑ l, cx l * x l = 1 := by
    calc
      ∑ l, cx l * x l = φ (C (∑ l, cD l * ξD l)) := by
        rw [map_sum (C : D →+* MvPolynomial (Fin k × Fin n) D), map_sum φ]
        simp only [map_mul (C : D →+* MvPolynomial (Fin k × Fin n) D), map_mul φ, cx, x]
      _ = 1 := by rw [hD, map_one, map_one]
  have hφr : φ r = aeval v g := by
    rw [show φ r = φ.toRingHom r from rfl,
      hom_aeval (F := F) φ.toRingHom (fun s => φ.commutes s)]
    rw [show (fun s => φ.toRingHom (genSubst ξD cD s)) = v from funext fun ij => by
      simp [genSubst, v, w, x, cx]]
  have hvI : v ∈ incidence P k := by
    refine ⟨x, fun hx => ?_, fun p hp => ?_, fun i => ?_⟩
    · rw [hx] at key
      simp at key
    · have hpD : aeval ξD p = 0 := by
        apply Subtype.ext
        have h1 := hom_aeval (F := F) D.val.toRingHom (fun s => D.val.commutes s) ξD p
        have h2 := hom_aeval (F := F)
          ((algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp
            (Ideal.Quotient.mk P)) (fun s => by
              rw [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]) X p
        simp only [aeval_X_left_apply, RingHom.coe_comp, Function.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero] at h2
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val] at h1
        rw [h1]
        exact h2.symm
      have h3 := hom_aeval (F := F) (φ.toRingHom.comp C) hφC ξD p
      simp only [hpD, map_zero, RingHom.coe_comp, Function.comp_apply] at h3
      exact h3.symm
    · simp only [v, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, key, mul_one,
        sub_self]
  rw [hφr]
  exact hg v hvI

theorem proof (h₁ : FGNullstellensatz.Statement) : IncidenceGeneric.Statement := by
  intro F _ n k P _ c hc g
  exact ⟨aeval_eq_zero_of_mem_incIdeal h₁ P c hc g, mem_incIdeal_of_aeval_eq_zero P c g⟩

end IncidenceGeneric

end

end GroundTheory.Heights₂.Heights
end

