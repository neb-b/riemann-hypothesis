module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartIncDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      IsDomain (ChartInc I t e) ∧ RingHom.ker (chartX I t e) = I ⊔ Ideal.span {linForm t - 1}

def ChartKernel.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = incIdeal I e

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace AffineChartTrdeg

variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]


omit [P.IsPrime] in
theorem aeval_genPt (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = algebraMap (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  rfl


omit [P.IsPrime] in
theorem aeval_genPt_eq_zero_iff (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem exists_isHomogeneous (j : Fin n) (hj : genPt P j ≠ 0)
    {a : FractionRing (MvPolynomial (Fin n) F ⧸ P)}
    (ha : a ∈ Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) :
    ∃ D : ℕ, ∀ D' ≥ D, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous D' ∧ aeval (genPt P) h = a * genPt P j ^ D' := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    refine ⟨1, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = 1 + e := ⟨D' - 1, by omega⟩
    refine ⟨X m * X j ^ e, (isHomogeneous_X F m).mul (isHomogeneous_X_pow j e), ?_⟩
    simp only [map_mul, map_pow, aeval_X]
    rw [pow_add, pow_one]
    field_simp
  | algebraMap r =>
    exact ⟨0, fun D' _ => ⟨C r * X j ^ D', isHomogeneous_C_mul_X_pow r j D', by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨max D₁ D₂, fun D' hD' => ?_⟩
    obtain ⟨f, hf, ef⟩ := h₁ D' (le_of_max_le_left hD')
    obtain ⟨g, hg, eg⟩ := h₂ D' (le_of_max_le_right hD')
    exact ⟨f + g, hf.add hg, by rw [map_add (f := _), ef, eg, add_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨D₁ + D₂, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = D₁ + e := ⟨D' - D₁, by omega⟩
    obtain ⟨f, hf, ef⟩ := h₁ D₁ le_rfl
    obtain ⟨g, hg, eg⟩ := h₂ e (by omega)
    exact ⟨f * g, hf.mul hg, by rw [map_mul, ef, eg, pow_add]; ring⟩

theorem transcendental (hP : IsHomogIdeal P) (j : Fin n) (hj : X j ∉ P) :
    Transcendental (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹))
      (genPt P j) := by
  classical
  set A' := Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)
  set ξ := genPt P
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))
  rintro ⟨p, hp, hpe⟩
  set N := p.natDegree + 1
  choose D hD using fun e => exists_isHomogeneous P j hξ (p.coeff e).2
  set M := (Finset.range N).sup D
  have hh : ∀ e, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous M ∧ aeval ξ h = (p.coeff e : _) * ξ j ^ M := by
    intro e
    by_cases he : e < N
    · exact hD e M (Finset.le_sup (Finset.mem_range.2 he))
    · refine ⟨0, isHomogeneous_zero _ _ _, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  choose h hhom heval using hh
  set G := ∑ e ∈ Finset.range N, h e * X j ^ e
  have hG : G ∈ P := by
    rw [← aeval_genPt_eq_zero_iff]
    have h0 : Polynomial.aeval (ξ j) p = ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
      rw [Polynomial.aeval_eq_sum_range]
      rfl
    calc aeval ξ G = ξ j ^ M * ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [G, map_sum, map_mul, map_pow, aeval_X, heval, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by rw [← h0, hpe, mul_zero]
  have hcoeff : ∀ e < N, p.coeff e = 0 := by
    intro e he
    have hcomp : homogeneousComponent (M + e) G = h e * X j ^ e := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [G, map_sum]
      rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self ((hhom e).mul (isHomogeneous_X_pow j e))
      · intro b _ hb
        rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
          ((hhom b).mul (isHomogeneous_X_pow j b))), if_neg (by omega)]
      · intro hne
        exact absurd (Finset.mem_range.2 he) hne
    have hmem : h e * X j ^ e ∈ P := hcomp ▸ hP G hG (M + e)
    have hhe : h e ∈ P := by
      rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h1 | h1
      · exact h1
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹_› e h1) hj
    have h2 := heval e
    rw [(aeval_genPt_eq_zero_iff P _).2 hhe, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd (pow_eq_zero_iff'.1 h2).1 hξ
  refine hp (Polynomial.ext fun e => ?_)
  by_cases he : e < N
  · simpa using hcoeff e he
  · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)

theorem proof : AffineChartTrdeg.Statement := by
  intro F _ n d P _ j hP hdim hj
  set R := MvPolynomial (Fin n) F ⧸ P
  set K := FractionRing R
  set ξ := genPt P
  set A' := Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹)
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))

  have hK : Algebra.trdeg F K = ((d + 1 : ℕ) : Cardinal) := by
    have : Algebra.FiniteType F R :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P)
        (Ideal.Quotient.mkₐ_surjective F P)
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) K]
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    have h2 : (Algebra.trdeg F R).toENat = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdim
    exact Cardinal.toENat_eq_natCast.mp h2

  set S := Algebra.adjoin A' (Set.range fun _ : Unit => ξ j)
  have hξS : ∀ m, ξ m ∈ S := by
    intro m
    have hr : ξ m * (ξ j)⁻¹ ∈ A' := Algebra.subset_adjoin ⟨m, rfl⟩
    have : ξ m = ξ m * (ξ j)⁻¹ * ξ j := by field_simp
    rw [this]
    exact S.mul_mem (S.algebraMap_mem (⟨_, hr⟩ : A')) (Algebra.subset_adjoin ⟨(), rfl⟩)
  have hRS : ∀ r : R, algebraMap R K r ∈ S := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← aeval_genPt]
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [aeval_C, IsScalarTower.algebraMap_apply F A' K]
      exact S.algebraMap_mem _
    | add f g hf hg => rw [map_add (f := _)]; exact S.add_mem hf hg
    | mul_X f i hf => rw [map_mul, aeval_X]; exact S.mul_mem hf (hξS i)

  letI : CommRing A' := Subalgebra.toCommRing A'
  letI : CommRing S := Subalgebra.toCommRing S
  have halg : Algebra.IsAlgebraic S K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨Polynomial.C (⟨_, hRS b⟩ : S) * Polynomial.X - Polynomial.C (⟨_, hRS a⟩ : S), fun h => hb0 ?_, ?_⟩
    · have := congrArg (AddMonoidAlgebra.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
        one_ne_zero, Polynomial.coeff_zero] at this
      have h' := congrArg Subtype.val this
      simp only [Subalgebra.coe_sub, Subalgebra.coe_zero, sub_zero] at h'
      exact h'
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show algebraMap R K b * (algebraMap R K a / algebraMap R K b) - algebraMap R K a = 0
      rw [mul_comm, div_mul_cancel₀ _ hb0, sub_self]

  have h1 : Algebra.trdeg A' K = 1 := by
    have hind : AlgebraicIndependent A' (fun _ : Unit => ξ j) :=
      algebraicIndependent_unique_type_iff.mpr (transcendental P hP.isHomog j hj)
    have hb : IsTranscendenceBasis A' (fun _ : Unit => ξ j) :=
      hind.isTranscendenceBasis_iff_isAlgebraic.mpr halg
    rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one]

  have : FaithfulSMul A' K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A').injective
  have hadd := trdeg_add_eq F A' (A := K)
  rw [h1, hK] at hadd
  have hfin : Algebra.trdeg F A' < Cardinal.aleph0 :=
    lt_of_le_of_lt le_self_add (by rw [hadd]; exact Cardinal.natCast_lt_aleph0)
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hk] at hadd ⊢
  norm_cast at hadd ⊢
  omega

end AffineChartTrdeg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartChoice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoice

variable {F : Type} [Field F] {n e : ℕ}

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by
  classical
  unfold specFirst
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [bind₁_monomial]
  obtain ⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by
    by_contra hno
    push Not at hno
    have hw := congrFun (hf (mem_support_iff.mp hs)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
    have : ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      simp [groupWeight, Ne.symm (hno c hc)]
    omega
  rw [Finset.prod_eq_zero hi, mul_zero]
  obtain ⟨a, m⟩ := i
  simp only at h0
  subst h0
  simp [specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]

theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar]
  exact RingHom.congr_fun h f

end ChartChoice


open ChartChoice in
theorem ChartChoice.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoice.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this
  have : CharZero (MvPolynomial (Fin e × Fin n) F ⧸ J) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => (k : MvPolynomial (Fin e × Fin n) F ⧸ J)))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((k m : ℕ) : F)) := by
      funext m
      rw [← hk m]
      simp
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem finsum_maximalSpectrum_ord_eq_sum {O B ι : Type*} [CommRing O] [CommRing B] [Algebra O B] (θ : B)
    (S : Finset ι) (c : ι → Ideal B) (hc : Set.BijOn c ↑S {P | P.IsMaximal ∧ θ ∈ P}) (m : ι → ℕ∞)
    (hm : ∀ i ∈ S, ∀ _ : (c i).IsPrime,
      Ring.ord (Localization.AtPrime (c i)) (algebraMap B _ θ) * Module.length O (B ⧸ c i) = m i) :
    ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal) =
      ∑ i ∈ S, m i := by
  classical
  let ψ : Ideal B → ℕ∞ := fun P => if h : P.IsMaximal then
    (haveI := h.isPrime
     Ring.ord (Localization.AtPrime P) (algebraMap B (Localization.AtPrime P) θ) * Module.length O (B ⧸ P))
    else 0
  calc ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)
      = ∑ᶠ 𝔓 ∈ {𝔓 : MaximalSpectrum B | θ ∈ 𝔓.asIdeal},
          Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) *
            Module.length O (B ⧸ 𝔓.asIdeal) := by
        refine finsum_congr fun 𝔓 => ?_
        rw [finsum_eq_if]
        split_ifs with h
        · rfl
        · have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔓.asIdeal) θ) :=
            IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) (Localization.AtPrime 𝔓.asIdeal) ⟨θ, h⟩
          rw [Ring.ord_of_isUnit hu, zero_mul]
    _ = ∑ᶠ P ∈ {P : Ideal B | P.IsMaximal ∧ θ ∈ P}, ψ P :=
        finsum_mem_eq_of_bijOn MaximalSpectrum.asIdeal
          ⟨fun 𝔓 h => ⟨𝔓.isMaximal, h⟩, fun a _ b _ h => MaximalSpectrum.ext h,
            fun P hP => ⟨⟨P, hP.1⟩, hP.2, rfl⟩⟩
          (fun 𝔓 _ => by simp only [ψ, dif_pos 𝔓.isMaximal])
    _ = ∑ᶠ i ∈ (S : Set ι), ψ (c i) := (finsum_mem_eq_of_bijOn c hc fun _ _ => rfl).symm
    _ = ∑ i ∈ S, ψ (c i) := finsum_mem_coe_finset _ _
    _ = ∑ i ∈ S, m i := Finset.sum_congr rfl fun i hi => by
        have hmax : (c i).IsMaximal := (hc.mapsTo (Finset.mem_coe.mpr hi)).1
        simp only [ψ, dif_pos hmax]
        exact hm i hi hmax.isPrime

theorem ChartLength.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegree.Statement) : ChartLength.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

end

end GroundTheory.Heights₂.Heights
end

