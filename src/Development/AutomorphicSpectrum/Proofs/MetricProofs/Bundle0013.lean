module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSucc
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def baseD (p : ℕ) (W : Ideal (MRing ι)) : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Ideal.Quotient.lift W ((Ideal.Quotient.mk (twist p W)).comp inc) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

def baseP (p : ℕ) (W : Ideal (MRing ι)) :
    Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Polynomial.eval₂RingHom (baseD p W) (Ideal.Quotient.mk (twist p W) yN)

def quadP (p : ℕ) (W : Ideal (MRing ι)) : Polynomial (Polynomial (MRing ι ⧸ W)) :=
  Polynomial.X ^ 2 + Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)

theorem quadraticPolynomial_monic (p : ℕ) (W : Ideal (MRing ι)) : (quadP p W).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

theorem quadraticPolynomial_natDegree (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] : (quadP p W).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_add_C

def coordA (p : ℕ) (W : Ideal (MRing ι)) : (Σ o, Tb ι o) → AdjoinRoot (quadP p W)
  | ⟨none, j⟩ => (![AdjoinRoot.root _, AdjoinRoot.of _ Polynomial.X] : Fin 2 → _) j
  | ⟨some k, i⟩ => AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩)))

def toA (p : ℕ) (W : Ideal (MRing ι)) : MRing (Tb ι) →+* AdjoinRoot (quadP p W) :=
  (aeval (coordA p W) : MRing (Tb ι) →ₐ[ℤ] AdjoinRoot (quadP p W)).toRingHom

theorem toA_inc (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    toA p W (inc f) = AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W f)) := by
  have h : (toA p W).comp inc =
      (AdjoinRoot.of (quadP p W)).comp (Polynomial.C.comp (Ideal.Quotient.mk W)) := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · intro i
      simp only [RingHom.comp_apply, toA, inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        aeval_X]
      rfl
  exact RingHom.congr_fun h f

theorem toA_xN (p : ℕ) (W : Ideal (MRing ι)) : toA p W xN = AdjoinRoot.root _ := by
  simp only [toA, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_yN (p : ℕ) (W : Ideal (MRing ι)) : toA p W yN = AdjoinRoot.of _ Polynomial.X := by
  simp only [toA, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_quad (p : ℕ) (W : Ideal (MRing ι)) : toA p W (quad p) = 0 := by
  have h : AdjoinRoot.mk (quadP p W) (Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)) = 0 :=
    AdjoinRoot.mk_self
  set_option synthInstance.maxHeartbeats 200000 in
  simp only [map_add (f := _), map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_intCast,
    Int.cast_natCast, map_natCast] at h
  have hC : toA p W (MvPolynomial.C (p : ℤ)) = (p : AdjoinRoot (quadP p W)) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quad, map_add (f := toA p W), map_mul, map_pow, toA_xN, toA_yN, hC]
  linear_combination h

theorem twist_le_ker_toA (p : ℕ) (W : Ideal (MRing ι)) : twist p W ≤ RingHom.ker (toA p W) := by
  unfold twist
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, toA_inc, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero,
      map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 (toA_quad p W)

def quotA (p : ℕ) (W : Ideal (MRing ι)) : (MRing (Tb ι) ⧸ twist p W) →+* AdjoinRoot (quadP p W) :=
  Ideal.Quotient.lift _ (toA p W) fun _ ha => twist_le_ker_toA p W ha

theorem quotA_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing (Tb ι)) :
    quotA p W (Ideal.Quotient.mk _ f) = toA p W f := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseD_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    baseD p W (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (inc f) := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseP_C (p : ℕ) (W : Ideal (MRing ι)) (a : MRing ι ⧸ W) :
    baseP p W (Polynomial.C a) = baseD p W a := by
  simp [baseP]

theorem baseP_X (p : ℕ) (W : Ideal (MRing ι)) :
    baseP p W Polynomial.X = Ideal.Quotient.mk _ yN := by
  simp [baseP]

theorem quotA_baseP (p : ℕ) (W : Ideal (MRing ι)) (g : Polynomial (MRing ι ⧸ W)) :
    quotA p W (baseP p W g) = AdjoinRoot.of _ g := by
  have h : (quotA p W).comp (baseP p W) = AdjoinRoot.of (quadP p W) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [RingHom.comp_apply, baseP_C, baseD_mk, quotA_mk, toA_inc]
    · rw [RingHom.comp_apply, baseP_X, quotA_mk, toA_yN]
  exact RingHom.congr_fun h g

theorem baseMap_injective (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] :
    Function.Injective (baseP p W) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro g hg
  have h0 : AdjoinRoot.of (quadP p W) g = 0 := by
    rw [← quotA_baseP, hg, map_zero]
  rw [← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at h0
  obtain ⟨q, hq⟩ := h0
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, Polynomial.C_eq_zero] at hq
    exact hq
  · have h1 := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_C, (quadraticPolynomial_monic p W).natDegree_mul' hq0, quadraticPolynomial_natDegree] at h1
    omega

theorem mk_quad_eq_zero (p : ℕ) (W : Ideal (MRing ι)) :
    Ideal.Quotient.mk (twist p W) (quad p) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem baseMap_isIntegralElem_xN (p : ℕ) (W : Ideal (MRing ι)) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) xN) := by
  refine ⟨quadP p W, quadraticPolynomial_monic p W, ?_⟩
  rw [← mk_quad_eq_zero p W]
  have hp : (Ideal.Quotient.mk (twist p W)) (MvPolynomial.C (p : ℤ)) =
      (p : MRing (Tb ι) ⧸ twist p W) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quadP, quad, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_add, baseP_X, map_intCast,
    Int.cast_natCast, hp, map_natCast, Polynomial.eval₂_natCast]

theorem baseMap_isIntegralElem_X (p : ℕ) (W : Ideal (MRing ι)) (q : Σ o, Tb ι o) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) (X q)) := by
  obtain ⟨o, j⟩ := q
  cases o with
  | none =>
    revert j
    change ∀ j : Fin 2, _
    intro j
    fin_cases j
    · exact baseMap_isIntegralElem_xN p W
    · have h := RingHom.isIntegralElem_map (baseP p W) (x := Polynomial.X)
      rw [baseP_X] at h
      exact h
  | some k =>
    have h : Ideal.Quotient.mk (twist p W) (X ⟨some k, j⟩ : MRing (Tb ι)) =
        baseP p W (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, j⟩))) := by
      rw [baseP_C, baseD_mk]
      simp [inc, oldIdx]
    rw [h]
    exact RingHom.isIntegralElem_map _

theorem baseMap_isIntegral (p : ℕ) (W : Ideal (MRing ι)) (b : MRing (Tb ι) ⧸ twist p W) :
    (baseP p W).IsIntegralElem b := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction f using MvPolynomial.induction_on
  · rw [eq_intCast MvPolynomial.C, map_intCast, ← map_intCast (baseP p W)]
    exact RingHom.isIntegralElem_map _
  · rw [map_add (f := _)]
    exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  · rw [map_mul]
    exact RingHom.IsIntegralElem.mul _ ‹_› (baseMap_isIntegralElem_X p W _)

theorem ringKrullDim_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  haveI : W.IsPrime := hW
  haveI : Nontrivial (MRing ι ⧸ W) := inferInstance
  haveI : IsNoetherianRing (MRing ι) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial ((k : K) × ι k) ℤ))
  letI : Algebra (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) := (baseP p W).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) :=
    ⟨fun b => baseMap_isIntegral p W b⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (baseMap_injective p W),
    Polynomial.ringKrullDim_of_isNoetherianRing]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlue
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conj_contDiff {T : Type} [Fintype T] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : T → ℂ => fun q => starRingEnd ℂ (z q)) :=
  contDiff_pi.2 fun q => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) q)

theorem oldPart_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (basePart₂ : ((Σ o, Tb ι o) → ℂ) → (Σ k, ι k) → ℂ) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ (fun _ => ℂ) _

theorem chi_contDiffOn (p : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi (ι := ι) p) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (0 : Fin 2)⟩) := contDiff_apply ℝ (fun _ => ℂ) _
  have hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (1 : Fin 2)⟩) := contDiff_apply ℝ (fun _ => ℂ) _
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im) :=
    Complex.imCLM.contDiff.comp (hx.mul (Complex.conjCLE.contDiff.comp hy))
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2) :=
    (hx.norm_sq ℝ).add (hy.norm_sq ℝ)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im /
        (‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
    refine hnum.contDiffOn.div hden.contDiffOn fun u hu => ?_
    have h0 : 0 ≤ ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 := by positivity
    have h1 : 0 ≤ ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 := by positivity
    have key : ∀ j : Fin 2, u ⟨none, j⟩ ≠ 0 →
        ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 ≠ 0 := by
      intro j hj
      have hpos : 0 < ‖u ⟨none, j⟩‖ ^ 2 := by positivity
      have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases hj2 with rfl | rfl <;> exact ne_of_gt (by linarith)
    obtain ⟨i, hi⟩ := hu none
    exact key i hi
  exact (contDiffOn_const.add (contDiffOn_const.mul hq))

theorem chi_conj (p : ℕ) (u : (Σ o, Tb ι o) → ℂ) :
    chi p (fun q => starRingEnd ℂ (u q)) = 1 - chi p u := by
  have him : ((starRingEnd ℂ) (u ⟨none, (0 : Fin 2)⟩) *
      (starRingEnd ℂ) ((starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩))).im =
      -(u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im := by
    rw [Complex.conj_conj, ← Complex.conj_im, map_mul, Complex.conj_conj]
  simp only [chi, RCLike.norm_conj, him]
  ring

theorem chi_vPlus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vPlus p)) = 1 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vPlus p) ⟨none, (0 : Fin 2)⟩ = cRoot p := rfl
  have e1 : glue z (vPlus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, hn, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem chi_vMinus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vMinus p)) = 0 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vMinus p) ⟨none, (0 : Fin 2)⟩ = -cRoot p := rfl
  have e1 : glue z (vMinus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, norm_neg, hn, Complex.neg_im, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem conj_ne {T : Type} {B : T → Type} {u : (Σ o, B o) → ℂ} {o : T} (h : ∃ i, u ⟨o, i⟩ ≠ 0) :
    ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa using hi⟩

theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  exact hA'.comp (s := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (conj_contDiff (T := Σ k, ι k)).contDiffOn fun z hz k => conj_ne (hz k)

theorem twLine_smooth (p : ℕ) (A : HermLine ι) (hA : IsSmoothHerm A) :
    IsSmoothHerm (twLine p A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h (basePart₂ u)) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA' oldPart_contDiff.contDiffOn
      fun _ hu k => oldPart_ne hu k
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h fun q => starRingEnd ℂ (basePart₂ u q))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA'
      (conj_contDiff.comp oldPart_contDiff).contDiffOn
      fun _ hu k => conj_ne (oldPart_ne hu k)
  have l1 := h1.log fun u hu => (A.pos _ (oldPart_ne hu)).ne'
  have l2 := h2.log fun u hu => (A.pos _ fun k => conj_ne (oldPart_ne hu k)).ne'
  have hc := chi_contDiffOn (ι := ι) p
  have hE := (((hc.mul l1).add (((contDiffOn_const (c := (1 : ℝ))).sub hc).mul l2))).exp
  refine ContDiffOn.congr hE fun u hu => ?_
  change twH p A u = _
  have hu' : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 := hu
  rw [twH, if_pos hu']

theorem twLine_conj (p : ℕ) (A : HermLine ι) : IsConjInvariantH (twLine p A) := by
  intro u
  change twH p A (fun q => starRingEnd ℂ (u q)) = twH p A u
  have hsame : (∀ o, ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0) ↔ ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 :=
    forall_congr' fun o => exists_congr fun i => by simp
  by_cases hu : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0
  · rw [twH, twH, if_pos (hsame.mpr hu), if_pos hu, chi_conj]
    have e1 : basePart₂ (fun q => starRingEnd ℂ (u q)) = fun q => starRingEnd ℂ (basePart₂ u q) := rfl
    have e2 : (fun q => starRingEnd ℂ (basePart₂ (fun q => starRingEnd ℂ (u q)) q)) = basePart₂ u := by
      funext q; simp [basePart₂]
    rw [e2, e1]
    congr 1
    ring
  · rw [twH, twH, if_neg (fun h => hu (hsame.mp h)), if_neg hu]

theorem glue_block {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {v : Fin 2 → ℂ}
    (hv : v 1 ≠ 0) : ∀ o, ∃ i, glue z v ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact ⟨(1 : Fin 2), hv⟩
  | some k => exact hz k

theorem twLine_vPlus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vPlus p)) = A.h z := by
  change twH p A _ = _
  have hv : vPlus p 1 ≠ 0 := by simp [vPlus]
  have ho : basePart₂ (glue z (vPlus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vPlus p hp, ho]
  simp only [one_mul, sub_self, zero_mul, add_zero]
  exact Real.exp_log (A.pos z hz)

theorem twLine_vMinus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z := by
  change twH p A _ = A.h fun q => starRingEnd ℂ (z q)
  have hv : vMinus p 1 ≠ 0 := by simp [vMinus]
  have ho : basePart₂ (glue z (vMinus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vMinus p hp, ho]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  exact Real.exp_log (A.pos _ fun k => conj_ne (hz k))

theorem twLine_main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) :=
  fun _ _ _ _ p A hp => ⟨twLine_smooth p A, conjLine_smooth A, twLine_conj p A,
    twLine_vPlus p hp A, twLine_vMinus p hp A⟩

end GlobalTheory.CompanionTheory.Ar.Tw.Lines
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdeal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨k, i⟩

theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

