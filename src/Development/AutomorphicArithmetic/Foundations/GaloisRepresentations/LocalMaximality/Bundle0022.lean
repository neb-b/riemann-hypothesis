module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRYBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

private lemma int_range {L A : Type} [Field L] [Algebra ℂ L] [CommRing A] [Algebra ℂ A] [Algebra A L]
    [IsScalarTower ℂ A L] (hA : ∀ a : A, a ∈ (algebraMap ℂ A).range) {y : L} (h : IsIntegral A y) :
    y ∈ (algebraMap ℂ L).range := by
  haveI : Algebra.IsIntegral ℂ A := ⟨fun a => by
    obtain ⟨c, rfl⟩ := hA a
    exact isIntegral_algebraMap⟩
  have hy : IsIntegral ℂ y := isIntegral_trans y h
  exact minpoly.mem_range_of_degree_eq_one ℂ y
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hy))

private lemma int_mono {E L : Type} [CommRing E] [Algebra ℂ E] [CommRing L] [Algebra E L]
    {A B : Subalgebra ℂ E} (h : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hp, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact he

private lemma int_scale {L : Type} [Field L] [Algebra ℂ L] (A A' : Subalgebra ℂ L) (s : L) (hs : s ∈ A)
    (hc : ∀ c ∈ A', ∃ N : ℕ, s ^ N * c ∈ A) {y : L} (hy : IsIntegral A' y) :
    ∃ N : ℕ, IsIntegral A (y * s ^ N) := by
  obtain ⟨p, hp, he⟩ := hy
  set q : Polynomial L := p.map (algebraMap A' L) with hq
  have hqm : q.Monic := hp.map _
  have hqe : q.eval₂ (RingHom.id L) y = 0 := by
    rw [hq, Polynomial.eval₂_map]
    simpa using he
  have hcoef : ∀ i, q.coeff i ∈ A' := fun i => by
    rw [hq, Polynomial.coeff_map]
    exact (p.coeff i).2
  have hM : ∀ t : Finset ℕ, ∃ M : ℕ, ∀ i ∈ t, s ^ M * q.coeff i ∈ A := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a t _ ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨N, hN⟩ := hc _ (hcoef a)
      refine ⟨M + N, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) hN
      · rw [add_comm, pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) (hM i hi)
  obtain ⟨M, hM⟩ := hM (Finset.range (q.natDegree + 1))
  refine ⟨M, ?_⟩
  have hrm : (Polynomial.scaleRoots q (s ^ M)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hqm
  have hre : (Polynomial.scaleRoots q (s ^ M)).eval₂ (RingHom.id L) (y * s ^ M) = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id L) y (s ^ M)
    rw [hqe, mul_zero] at this
    rw [mul_comm]
    exact this
  have hA : ∀ i, (Polynomial.scaleRoots q (s ^ M)).coeff i ∈ A := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1 := ⟨q.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, mul_comm, mul_assoc]
      refine A.mul_mem (A.pow_mem (A.pow_mem hs _) _) ?_
      rw [mul_comm]
      exact mul_comm (s ^ M) (q.coeff i) ▸ hM i (Finset.mem_range.2 (by omega))
    · subst hi
      simp [hqm.coeff_natDegree, A.one_mem]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact A.zero_mem
  have hlift : Polynomial.scaleRoots q (s ^ M) ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hA i⟩, rfl⟩
  obtain ⟨r, hr, -, hrm'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hrm
  refine ⟨r, hrm', ?_⟩
  rw [← hr, Polynomial.eval₂_map] at hre
  simpa using hre

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩

private lemma omB_stab {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro r hr m hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, by simp [mul_smul]⟩
  | zero => simp
  | add a c _ _ ha hc =>
    rw [map_add (f := _)]
    exact add_mem ha hc
  | smul t a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K')

private lemma rA_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rA ℂ x I ≤ rA ℂ x I' :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

private lemma rB_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rB ℂ K x I ≤ rB ℂ K x I' :=
  fun _ hy => int_mono (rA_mono' x h) hy

private lemma integralClosure_mono_subset {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') : R2 x j2 J ≤ R2 x j2 J' :=
  fun _ hy => int_mono (Subalgebra.map_mono (rB_mono' x h)) hy

private lemma ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    x a / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private lemma rA_mem_rB {I : Finset (Fin (d + 1))} {f : F} (hf : f ∈ rA ℂ x I) :
    algebraMap F K f ∈ rB ℂ K x I :=
  show IsIntegral (rA ℂ x I) (algebraMap F K f) from
    isIntegral_algebraMap (R := rA ℂ x I) (A := K) (x := ⟨f, hf⟩)

private lemma rB_empty {b : K} (hb : b ∈ rB ℂ K x ∅) : b ∈ (algebraMap ℂ K).range := by
  refine int_range (A := rA ℂ x ∅) (fun a => ?_) hb
  have h0 : rA ℂ x ∅ = ⊥ := by simp [rA]
  have ha : (a : F) ∈ (⊥ : Subalgebra ℂ F) := h0 ▸ a.2
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 ha
  exact ⟨c, Subtype.ext hc⟩

private lemma integralClosure_empty_const {y : K'} (hy : y ∈ R2 x j2 ∅) : y ∈ (algebraMap ℂ K').range := by
  refine int_range (A := (rB ℂ K x ∅).map j2) (fun a => ?_) hy
  obtain ⟨b, hb, hba⟩ := a.2
  obtain ⟨c, rfl⟩ := rB_empty x hb
  exact ⟨c, Subtype.ext (by rw [← hba]; simp)⟩

private lemma j2_mem_R2_of_mem_rB {J : Finset (Fin (d + 1))} {b : K} (hb : b ∈ rB ℂ K x J) : j2 b ∈ R2 x j2 J :=
  show IsIntegral ((rB ℂ K x J).map j2) (j2 b) from
    isIntegral_algebraMap (R := (rB ℂ K x J).map j2) (A := K') (x := ⟨j2 b, b, hb, rfl⟩)

private lemma rB_shift (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {b : K}
    (hb : b ∈ rB ℂ K x (insert j' J)) : ∃ N : ℕ, algebraMap F K (x j' / x j) ^ N * b ∈ rB ℂ K x J := by
  by_cases hj' : j' ∈ J
  · refine ⟨0, ?_⟩
    rw [Finset.insert_eq_of_mem hj'] at hb
    simpa using hb
  · obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h (insert j' J) j (Finset.mem_insert_of_mem hj)).2 b).1 hb
    refine ⟨N, ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h J j hj).2 _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj', map_mul, mul_pow] at hN
    convert hN using 1
    ring

private lemma integralClosure_shift_power (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {y : K'}
    (hy : y ∈ R2 x j2 (insert j' J)) : ∃ N : ℕ, y * j2 (algebraMap F K (x j' / x j)) ^ N ∈ R2 x j2 J := by
  have hs : j2 (algebraMap F K (x j' / x j)) ∈ (rB ℂ K x J).map j2 :=
    ⟨_, rA_mem_rB x (ratio_mem x hj j'), rfl⟩
  obtain ⟨N, hN⟩ := int_scale ((rB ℂ K x J).map j2) ((rB ℂ K x (insert j' J)).map j2) _ hs (by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨N, hN⟩ := rB_shift x h hj hb
    exact ⟨N, ⟨_, hN, by simp⟩⟩) hy
  exact ⟨N, hN⟩

end

theorem UpperTheory.Gal.productCup_of_system.rYBasic_of :
    RYBasic := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  have hpull : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I := by
    intro I b hb
    have hb' : IsIntegral (rA ℂ (xv x) I) b := hb
    exact (IsIntegral.algebraMap hb' : IsIntegral (rA ℂ (xv x) I) (algebraMap K K' b))
  have hmono : ∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J' :=
    fun I I' J J' hI hJ => sup_le_sup (rB_mono' (xv x) hI) (integralClosure_mono_subset (xv x) j2 hJ)
  refine ⟨fun I => ?_, fun a => ?_, hmono, fun I b hb => ⟨hpull I b hb, j2_mem_R2_of_mem_rB (xv x) j2 hb⟩, ?_⟩
  · refine sup_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := integralClosure_empty_const (xv x) j2 hy
    exact (rB ℂ K' (xv x) I).algebraMap_mem c
  · refine ⟨fun I I' J J' _ _ hI hJ => hmono I I' J J' hI hJ,
      fun I I' J J' _ _ hI hJ => omB_mono' (hmono I I' J J' hI hJ) a,
      fun I J _ _ => omB_stab _ a, fun I J _ i hi b => ?_, fun I J _ j hj b => ?_⟩
    · have e : (((sysY x j2 a).X b * ((sysY x j2 a).X i)⁻¹ : K'ˣ) : K') = algebraMap F K' (xv x b / xv x i) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rA_mem_rB (xv x) (ratio_mem (xv x) hi b))
    · have e : (((sysY x j2 a).Y b * ((sysY x j2 a).Y j)⁻¹ : K'ˣ) : K') = j2 (algebraMap F K (xv x b / xv x j)) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J)
        (j2_mem_R2_of_mem_rB (xv x) j2 (rA_mem_rB (xv x) (ratio_mem (xv x) hj b)))
  · intro J j hj j' y hy
    exact integralClosure_shift_power (xv x) j2 hY.covZ hj hy
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrVal
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system.PartialTraceValue

private theorem nakGen {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map (algebraMap A B) = ⊤) : ∃ r : A, r - 1 ∈ I ∧ algebraMap A B r ∈ 𝔟 := by
  let N : Submodule A B := 𝔟.restrictScalars A
  have key : ∀ j ∈ I.map (algebraMap A B), ∀ b : B,
      (Submodule.Quotient.mk (j * b) : B ⧸ N) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
    intro j hj
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hj
    · rintro _ ⟨i, hi, rfl⟩ b
      rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · intro b
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv b
      rw [add_mul, Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (hu b) (hv b)
    · intro c u _ hu b
      rw [smul_eq_mul, show c * u * b = u * (c * b) by ring]
      exact hu _
  have hin : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
    rintro q -
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.1 (hb ▸ Submodule.mem_top : (1 : B) ∈ 𝔟 ⊔ I.map (algebraMap A B))
    have : (Submodule.Quotient.mk b : B ⧸ N) = Submodule.Quotient.mk (j * b) := by
      rw [Submodule.Quotient.eq]
      have : b - j * b = a * b := by
        linear_combination (-b) * haj
      rw [this]
      exact 𝔟.mul_mem_right b ha
    rw [this]
    exact key j hj b
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (⊤ : Submodule A (B ⧸ N)) Module.Finite.fg_top hin
  refine ⟨r, hr1, ?_⟩
  have h0 := hr (Submodule.Quotient.mk 1) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_one] at h0
  exact h0

private theorem nakHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (φ : A →ₐ[ℂ] B) (hint : ∀ b : B, φ.toRingHom.IsIntegralElem b) (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map φ.toRingHom = ⊤) : ∃ r : A, r - 1 ∈ I ∧ φ r ∈ 𝔟 := by
  letI alg : Algebra A B := φ.toRingHom.toAlgebra
  haveI tow : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI int : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  haveI fin : Module.Finite A B := Algebra.IsIntegral.finite
  exact nakGen I 𝔟 hb

variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L]
  {d : ℕ} (x : Fin (d + 1) → F)

private def tA (j : Fin d) : rA ℂ x {0} :=
  ⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩

private def IA : Ideal (rA ℂ x {0}) := Ideal.span (Set.range (tA x))

private theorem val_one (φ : rA ℂ x {0} →ₐ[ℂ] ℂ) (hφ : ∀ j, φ (tA x j) = 0) {r : rA ℂ x {0}}
    (hr : r - 1 ∈ IA x) : φ r = 1 := by
  have hle : IA x ≤ RingHom.ker φ := by
    rw [IA, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hφ j
  have := hle hr
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this

private theorem nak (h : IsFinCover ℂ L x) (𝔟 : Ideal (rB ℂ L x {0}))
    (hb : 𝔟 ⊔ FibFin.coordIdeal ℂ L x = ⊤) :
    ∃ r : rA ℂ x {0}, r - 1 ∈ IA x ∧ FibFin.incl ℂ L x r ∈ 𝔟 := by
  haveI := h.smooth 0
  have hcomp : (rB ℂ L x {0}).val.toRingHom.comp (FibFin.incl ℂ L x).toRingHom =
      algebraMap (rA ℂ x {0}) L := RingHom.ext fun a => rfl
  have hint : ∀ b : rB ℂ L x {0}, (FibFin.incl ℂ L x).toRingHom.IsIntegralElem b := fun b => by
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA ℂ x {0}) (b : L) := b.2
    refine ⟨p, hpm, ?_⟩
    apply Subtype.ext
    change (rB ℂ L x {0}).val.toRingHom (Polynomial.eval₂ (FibFin.incl ℂ L x).toRingHom b p) = (0 : L)
    rw [Polynomial.hom_eval₂, hcomp]
    exact hp
  have hJ : FibFin.coordIdeal ℂ L x ≤ (IA x).map (FibFin.incl ℂ L x).toRingHom := by
    rw [FibFin.coordIdeal, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    change (FibFin.incl ℂ L x).toRingHom (tA x l) ∈ _
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self l))
  exact nakHom (FibFin.incl ℂ L x) hint (IA x) 𝔟 (top_le_iff.1 (hb ▸ sup_le_sup_left hJ 𝔟))

private theorem fib_nonempty (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) : Nonempty (fib ℂ L x) := by
  by_contra hne
  have hall := (FibFin.fib_finite_and_sep ℂ L x h hred).2 1 (fun e => (hne ⟨e⟩).elim)
  have ht : FibFin.coordIdeal ℂ L x = ⊤ := (Ideal.eq_top_iff_one _).2 hall
  obtain ⟨r, hr1, hr⟩ := nak x h ⊥ (by rw [ht]; simp)
  have hr0 : r = 0 := by
    have h0 : algebraMap F L (r : F) = 0 := congrArg Subtype.val ((Ideal.mem_bot).1 hr)
    exact Subtype.ext ((map_eq_zero _).1 h0)
  obtain ⟨e, he⟩ := rA_single_polyEquiv ℂ F d x h.pd 0
  have hε : ((MvPolynomial.aeval (0 : Fin d → ℂ)).comp e.symm.toAlgHom) r = 1 := by
    refine val_one x _ (fun j => ?_) hr1
    have htj : tA x j = e (MvPolynomial.X j) := Subtype.ext (by rw [he j, Fin.succAbove_zero]; rfl)
    rw [htj]
    simp
  rw [hr0, map_zero] at hε
  exact zero_ne_one hε

private theorem comax (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (𝔞 : Ideal (rB ℂ L x {0})) (h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0) :
    𝔞 ⊔ FibFin.coordIdeal ℂ L x = ⊤ := by
  obtain ⟨hfin, hsep⟩ := FibFin.fib_finite_and_sep ℂ L x h hred
  haveI := Fintype.ofFinite (fib ℂ L x)
  classical
  choose b hb hb0 using h𝔞
  choose c hc using fun e0 : fib ℂ L x => hCRT (fun e => if e = e0 then (e0.1 (b e0))⁻¹ else 0)
  have hs : (∑ e0, c e0 * b e0) ∈ 𝔞 := Ideal.sum_mem _ fun e0 _ => 𝔞.mul_mem_left _ (hb e0)
  have hval : ∀ e : fib ℂ L x, e.1 (∑ e0, c e0 * b e0) = 1 := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single e (fun e0 _ hne => by rw [map_mul, hc, if_neg (Ne.symm hne), zero_mul])
      (fun hn => (hn (Finset.mem_univ e)).elim), map_mul, hc, if_pos rfl]
    exact inv_mul_cancel₀ (hb0 e)
  have h1 := hsep (1 - ∑ e0, c e0 * b e0) (fun e => by rw [map_sub, map_one, hval, sub_self])
  rw [Ideal.eq_top_iff_one]
  exact Submodule.mem_sup.2 ⟨_, hs, _, h1, by ring⟩

private theorem partialTrace_valuation_sum (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) (ρ : F →ₗ[ℂ] ℂ)
    (hRT : ∀ b : rB ℂ L x {0}, ρ (Algebra.trace F L b) = ∑ᶠ e : fib ℂ L x, e.1 b)
    (hRes : ∀ e : fib ℂ L x, ∀ f ∈ rA ℂ x {0}, Val (rB ℂ L x {0}) e.1 (algebraMap F L f) (ρ f))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (g : L) (γ : fib ℂ L x → ℂ) (hg : ∀ e : fib ℂ L x, Val (rB ℂ L x {0}) e.1 g (γ e))
    (ht : Algebra.trace F L g ∈ rA ℂ x {0}) :
    ρ (Algebra.trace F L g) = ∑ᶠ e, γ e := by
  let 𝔞 : Ideal (rB ℂ L x {0}) :=
    { carrier := {b | (b : L) * g ∈ rB ℂ L x {0}}
      add_mem' := by
        intro a b ha hb
        have := (rB ℂ L x {0}).add_mem ha hb
        simpa [add_mul] using this
      zero_mem' := by simpa using (rB ℂ L x {0}).zero_mem
      smul_mem' := by
        intro c b hb
        have := (rB ℂ L x {0}).mul_mem c.2 hb
        simpa [mul_assoc] using this }
  have h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0 := fun e => by
    obtain ⟨b, hb, hbv, hne, -⟩ := hg e
    exact ⟨⟨b, hb⟩, hbv, hne⟩
  obtain ⟨s, hs1, hs⟩ := nak x h 𝔞 (comax x h hred hCRT 𝔞 h𝔞)
  have hs' : algebraMap F L (s : F) * g ∈ rB ℂ L x {0} := hs
  have hone : ∀ e : fib ℂ L x, e.1 (FibFin.incl ℂ L x s) = 1 := fun e =>
    val_one x (e.1.comp (FibFin.incl ℂ L x)) (fun j => e.2 j) hs1
  have hval : ∀ e : fib ℂ L x, e.1 ⟨_, hs'⟩ = γ e := by
    intro e
    obtain ⟨b, hb, hbv, hne, heq⟩ := hg e
    have h1 : (⟨b, hb⟩ : rB ℂ L x {0}) * ⟨_, hs'⟩ = FibFin.incl ℂ L x s * ⟨b * g, hbv⟩ := by
      apply Subtype.ext
      change b * (algebraMap F L (s : F) * g) = algebraMap F L (s : F) * (b * g)
      ring
    have h2 := congrArg e.1 h1
    rw [map_mul, map_mul, hone, one_mul, heq] at h2
    exact mul_left_cancel₀ hne h2
  obtain ⟨e0⟩ := fib_nonempty x h hred
  have hev : ∀ f : rA ℂ x {0}, e0.1 (FibFin.incl ℂ L x f) = ρ f := by
    intro f
    obtain ⟨b, hb, hbv, hne, heq⟩ := hRes e0 f f.2
    have h1 : (⟨b * algebraMap F L f, hbv⟩ : rB ℂ L x {0}) = ⟨b, hb⟩ * FibFin.incl ℂ L x f := rfl
    rw [h1, map_mul] at heq
    exact mul_left_cancel₀ hne heq
  have htr : Algebra.trace F L (algebraMap F L (s : F) * g) = (s : F) * Algebra.trace F L g := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h3 : ρ ((s : F) * Algebra.trace F L g) = ρ (Algebra.trace F L g) := by
    have h4 := hev (s * ⟨_, ht⟩)
    rw [map_mul, map_mul, hone e0, one_mul, hev] at h4
    exact h4.symm
  rw [← h3, ← htr]
  exact (hRT ⟨_, hs'⟩).trans (finsum_congr hval)

end UpperTheory.Gal.productCup_of_system.PartialTraceValue

end

theorem UpperTheory.Gal.productCup_of_system.trVal_of :
    ResidueOfTraceIsFiberSum → ResVal → CRT → ValBasic → TrVal := by
  intro hRT hRes hCRT _ F L _ _ _ _ _ _ d x hc hred ρ hρ g γ hg ht
  exact PartialTraceValue.partialTrace_valuation_sum (xv x) hc hred ρ (hRT F L d x hc hred ρ hρ)
    (fun e f hf => hRes F L d x hc ρ hρ e f hf) (hCRT F L d x hc).2 g γ hg ht
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceEqZeroOfBot
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem omB_eq_bot {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (a : ℕ)
    (hv : ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], y = 0) : omB ℂ K B a = ⊥ := by
  unfold omB
  rw [Submodule.span_eq_bot]
  rintro y ⟨b, -, v, -, rfl⟩
  rw [hv _ (ExteriorAlgebra.ιMulti_range K a ⟨_, rfl⟩), smul_zero]

private theorem trace_eq_zero_of_bot {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (G : Finset ι → Submodule ℂ E) (hG : ∀ I, G I = ⊥) (p : ℤ)
    (f : (cech G).H p →ₗ[ℂ] (cech G).H p) : LinearMap.trace ℂ _ f = 0 := by
  have hZ : ∀ z ∈ (cech G).Z p, z = 0 := by
    intro z hz
    have hC : z ∈ cechC G p := (Submodule.mem_inf.1 hz).1
    rw [cechC, Submodule.mem_pi] at hC
    funext s
    have h1 := hC s (Set.mem_univ s)
    split_ifs at h1 <;> simpa [hG] using h1
  haveI : Subsingleton ((cech G).Z p) :=
    ⟨fun a b => Subtype.ext ((hZ a a.2).trans (hZ b b.2).symm)⟩
  haveI : Subsingleton ((cech G).H p) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  rw [Subsingleton.elim f 0, map_zero]

private theorem coeff_det_eq_zero {d a : ℕ} (hlt : d < a) (B : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)).coeff a = 0 := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_eq_empty.2 (by simpa using hlt), Finset.sum_empty]

private theorem val_div {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    (c g : L) (hc : c ∈ B) (hg : g ∈ B) (hne : e ⟨c, hc⟩ ≠ 0) (t : ℂ)
    (h : e ⟨g, hg⟩ = e ⟨c, hc⟩ * t) (hc0 : c ≠ 0) : Val B e (g / c) t := by
  have hcg : c * (g / c) = g := by
    rw [mul_comm]
    exact div_mul_cancel₀ g hc0
  have hmem : c * (g / c) ∈ B := by
    rw [hcg]
    exact hg
  refine ⟨c, hc, hmem, hne, ?_⟩
  have hsub : (⟨c * (g / c), hmem⟩ : B) = ⟨g, hg⟩ := Subtype.ext hcg
  rw [hsub, h]

theorem UpperTheory.Gal.productCup_of_system.field0_of :
    FieldLe → ValBasic → Field0 := by
  intro hLe _
  intro d a F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ x j2 hK hK' hred hnf hz hfix Fx hFx hgen A hA hdet u hu hfd
  by_cases had : a ≤ d
  · have hne : ∀ i, x i ≠ 0 := hK.pd.ne
    let xu : Fin (d + 1) → Fˣ := fun i => Units.mk0 (x i) (hne i)
    have hY : Y1 xu j2 Fx A :=
      { covZ := hK
        covY := hK'
        cov := by
          intro i e
          obtain ⟨j, hj⟩ := hred i e
          refine ⟨j, fun v hv => ?_⟩
          obtain ⟨b, hb, he, hbv⟩ := hj v hv
          exact ⟨⟨b, hb⟩, he, hbv⟩
        red := hnf
        off := hz
        orig := hfix
        fx := hFx
        tan := by
          intro e he m
          obtain ⟨c, hc, g, hg, hec, hsum, hgl⟩ := hA e he m
          have hc0 : c ≠ 0 := by
            rintro rfl
            apply hec
            have h0 : (⟨0, hc⟩ : rB ℂ K' x {0}) = 0 := rfl
            rw [h0, map_zero]
          refine ⟨fun l => g l / c, fun l => val_div _ _ c (g l) hc (hg l) hec _ (hgl l) hc0, ?_⟩
          show j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l / c * algebraMap F K' (x l.succ / x 0)
          apply mul_left_cancel₀ hc0
          rw [hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mul_assoc, mul_comm c, div_mul_cancel₀ _ hc0]
        det := hdet }
    exact hLe F K K' d xu j2 Fx A hY a had u hu
  · push_neg at had
    have hv := (GlobalTheory.T.dlog_basis_and_vanishing_above_dimension ℂ F K d x hK).2 a had
    refine (Finset.sum_eq_zero fun p _ => ?_).trans (Finset.sum_eq_zero fun e _ => ?_).symm
    · rw [trace_eq_zero_of_bot _ (fun I => omB_eq_bot _ a hv) _ (u p), mul_zero]
    · rw [coeff_det_eq_zero had, zero_div]
end

