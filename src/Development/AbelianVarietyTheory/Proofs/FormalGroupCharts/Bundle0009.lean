module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSeriesSubstPointsStandardThree
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsActionGauge
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeOfLog
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_of_log : LogSt → CanonGaugeSt := fun hlog =>
  have hcob := FormalCocycle.exists_coboundary_of_symm_cocycle hlog ChartInv.exists_isInvPair
  have huniq := AdditiveSeries.eq_zero_of_additive_of_pderiv
  canonGauge_of_steps exists_formalBiext_map exists_regauge
    (GaugeFirstLaw.exists_gauge_first_law hcob huniq)
    (SecondLawGauge.exists_gauge_second_law hcob huniq)
    (ActionGauge.exists_action_gauge
      (derivation_inner_of_reduced_order SepIdem.exists_separability_element))
    SymGauge.exists_gauge_of_symmetry

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NonemptyTensorQuotientEquiv
section
open IsLocalRing TensorProduct

namespace GlobalTheory.QuotientBaseChange

open MvPowerSeries

open IsLocalRing TensorProduct in
open MvPowerSeries in
private theorem monomial_one_mem_span_X_pow_degree {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    MvPowerSeries.monomial α (1 : R) ∈
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ (Finsupp.degree α) := by
  induction α using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [← one_mul (1 : R), ← MvPowerSeries.monomial_mul_monomial, map_add (f := _), Finsupp.degree_single,
      pow_add, ← MvPowerSeries.X_pow_eq]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self a)) b) ih


open IsLocalRing TensorProduct in
open MvPowerSeries in
theorem _root_.GlobalTheory.QuotientBaseChange.nonempty_tensor_quotient_equiv : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal T), I.FG → IsAdicComplete (I.map (algebraMap T O)) O → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ T) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : T →+* MvPowerSeries σ T) I → Module.Free T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → Nonempty ((O ⊗[T] (MvPowerSeries σ T ⧸ Ideal.span (Set.range f))) ≃ₐ[O] (MvPowerSeries σ O ⧸ Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j)))) := by
  intro T O _ _ _ I hI hO σ ι hσ hι f M hM hfree hfin
  classical
  haveI := hfree
  haveI := hfin
  haveI := hO
  let J : Ideal O := I.map (algebraMap T O)
  let A := MvPowerSeries σ T ⧸ Ideal.span (Set.range f)
  let f' : ι → MvPowerSeries σ O := fun j => MvPowerSeries.map (algebraMap T O) (f j)
  let Q := MvPowerSeries σ O ⧸ Ideal.span (Set.range f')
  let S := O ⊗[T] A
  let μ : MvPowerSeries σ T →ₐ[T] MvPowerSeries σ O := MvPowerSeries.mapAlgHom (Algebra.ofId T O)
  have hker : Ideal.span (Set.range f) ≤ RingHom.ker ((Ideal.Quotient.mkₐ T (Ideal.span (Set.range f'))).comp μ) :=
    Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact (RingHom.mem_ker).mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)))
  let g : A →ₐ[T] Q := Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ T _).comp μ) (fun a ha => hker ha)
  let φ : S →ₐ[O] Q := Algebra.TensorProduct.lift (Algebra.ofId O Q) g (fun _ _ => Commute.all _ _)
  have hφ1 : ∀ p : MvPowerSeries σ T,
      φ ((1 : O) ⊗ₜ Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (μ p) := fun p => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  let b := Algebra.TensorProduct.basis O (Module.Free.chooseBasis T A)
  haveI h1 : IsAdicComplete J S := _root_.GlobalTheory.FlatComplete.isAdicComplete_of_finite_basis b J
  let K : Ideal S := J.map (algebraMap O S)
  haveI h2 : IsAdicComplete K S := (IsAdicComplete.map_algebraMap_iff J S).mpr h1
  let h : MvPowerSeries σ T →ₐ[T] S :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ T (Ideal.span (Set.range f)))
  let hR : MvPowerSeries σ T →+* S := h
  have hf0 : ∀ j, h (f j) = 0 := fun j => by
    show Algebra.TensorProduct.includeRight (Ideal.Quotient.mk _ (f j)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), map_zero]
  let L : Ideal S := Ideal.map hR (Ideal.span (Set.range MvPowerSeries.X))
  have hLK : L ^ M ≤ K := by
    rw [← Ideal.map_pow]
    refine (Ideal.map_mono hM).trans ?_
    rw [Ideal.map_sup]
    refine sup_le ?_ ?_
    · rw [Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      show h (f j) ∈ K
      rw [hf0 j]
      exact K.zero_mem
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have e : (MvPowerSeries.C a : MvPowerSeries σ T) = algebraMap T _ a := by
        simp [MvPowerSeries.algebraMap_apply]
      show h (MvPowerSeries.C a) ∈ K
      rw [e, h.commutes, IsScalarTower.algebraMap_apply T O S]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
  let J' : Ideal S := K ⊔ L
  haveI : IsAdicComplete J' S :=
    _root_.GlobalTheory.isAdicComplete_of_pow_le_of_pow_le S K J' 1 (1 + M) (by rw [pow_one]; exact le_sup_left)
      (Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le (pow_one K).le hLK)) h2
  let x : σ → S := fun i => h (MvPowerSeries.X i)
  have hx : ∀ i, x i ∈ J' := fun i =>
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
  let ψ0 : MvPowerSeries σ O →ₐ[O] S := _root_.GlobalTheory.mvEvalAdic O J' x hx
  have hX : ∀ i, ((ψ0.restrictScalars T).comp μ) (MvPowerSeries.X i) = x i := fun i => by
    show ψ0 (MvPowerSeries.map (algebraMap T O) (MvPowerSeries.X i)) = x i
    rw [MvPowerSeries.map_X]
    exact _root_.GlobalTheory.mvEvalAdic_X J' x hx i
  have hcomp : (ψ0.restrictScalars T).comp μ = h :=
    _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff J' (fun i => (hX i).symm ▸ hx i) hX
  have hψ0 : ∀ j, ψ0 (f' j) = 0 := fun j => by
    calc ψ0 (f' j) = ((ψ0.restrictScalars T).comp μ) (f j) := rfl
      _ = h (f j) := by rw [hcomp]
      _ = 0 := hf0 j
  have hker' : Ideal.span (Set.range f') ≤ RingHom.ker ψ0 :=
    Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact (RingHom.mem_ker).mpr (hψ0 j))
  let ψ : Q →ₐ[O] S := Ideal.Quotient.liftₐ _ ψ0 (fun a ha => hker' ha)
  have hψφ : ψ.comp φ = AlgHom.id O S := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AlgHom.ext
      intro q
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      show ψ (φ ((1 : O) ⊗ₜ Ideal.Quotient.mk _ p)) = (1 : O) ⊗ₜ Ideal.Quotient.mk _ p
      rw [hφ1]
      exact DFunLike.congr_fun hcomp p
  have hCmap : (MvPowerSeries.map (algebraMap T O)).comp (MvPowerSeries.C : T →+* MvPowerSeries σ T) =
      (MvPowerSeries.C : O →+* MvPowerSeries σ O).comp (algebraMap T O) :=
    RingHom.ext fun a => by simp
  have hmono : ∀ α : σ →₀ ℕ, Finsupp.degree α = M →
      MvPowerSeries.monomial α (1 : O) ∈ Ideal.span (Set.range f') ⊔ Ideal.map MvPowerSeries.C J := by
    intro α hα
    have hT := hM (hα ▸ monomial_one_mem_span_X_pow_degree (R := T) α)
    have hm := Ideal.mem_map_of_mem (MvPowerSeries.map (algebraMap T O)) hT
    rw [MvPowerSeries.map_monomial, map_one, Ideal.map_sup, Ideal.map_span, ← Set.range_comp,
      Ideal.map_map, hCmap, ← Ideal.map_map] at hm
    exact hm
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨g0, rfl⟩ := Ideal.Quotient.mk_surjective q
    letI := Fintype.ofFinite ι
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.CompleteBaseChange.exists_polynomial_sub_mem (hI.map (algebraMap T O)) f' M hmono g0
    refine ⟨MvPolynomial.aeval x p, ?_⟩
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hφx : (fun i => φ (x i)) = fun i => Ideal.Quotient.mkₐ O (Ideal.span (Set.range f')) (MvPowerSeries.X i) := by
      funext i
      show φ ((1 : O) ⊗ₜ Ideal.Quotient.mk _ (MvPowerSeries.X i)) = _
      rw [hφ1]
      show Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap T O) (MvPowerSeries.X i)) = _
      rw [MvPowerSeries.map_X]
      rfl
    rw [hφx, ← _root_.GlobalTheory.algHom_coe_mvPolynomial]
    exact (Ideal.Quotient.eq.mpr hp).symm
  have hinj : Function.Injective φ :=
    Function.LeftInverse.injective (g := ψ) (fun s => DFunLike.congr_fun hψφ s)
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

end GlobalTheory.QuotientBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondOrderMonomial
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.HalfIdentity

variable {k : Type} [CommRing k] {d : ℕ}

section

variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

theorem T_replicate (n : ℕ) (l : ι) (f : PS k 1 d) :
    G2.T F u (List.replicate n l) f = (Dof F (u l))^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, G2.T_cons, ih, Function.iterate_succ_apply']

theorem foldr_eq_T_word (L : List ι) (m : ι →₀ ℕ) (f : PS k 1 d) :
    L.foldr (fun l g => (Dof F (u l))^[m l] g) f = G2.T F u (G2.word L m) f := by
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, ih, G2.word_cons, G2.T_append, T_replicate]

variable [Fintype ι]

theorem dmonOf_eq_T_word (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f = G2.T F u (G2.word (Finset.univ : Finset ι).toList m) f :=
  foldr_eq_T_word F u _ m f

theorem dpolyOf_monomial (m : ι →₀ ℕ) (a : k) (f : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial m a) f = C a * DmonOf F u m f := by
  classical
  rw [GE.dpolyOf_eq_sum_of_subset F u _ {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem secondOrder_add (c : ι → ι → k) (P Q : MvPolynomial ι k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by
  simp only [secondOrder, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem secondOrder_monomial (c : ι → ι → k) (m : ι →₀ ℕ) (a : k) :
    secondOrder k c (MvPolynomial.monomial m a) =
      ∑ x, ∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
        (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k))) := by
  unfold secondOrder
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial]
  congr 1
  push_cast
  ring

end

theorem halfSt : GE.HalfSt := by
  intro k _ _ d F ι _ u c q hc hq0 hq1 hq2 P A
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [secondOrder_add, GE.dpolyOf_add_P, GE.dpolyOf_add_P, map_add (f := _), map_add (f := _), hP, hQ, mul_add]
  | monomial m a =>
    have h2 : algebraMap ℚ k (1 / 2) * 2 = 1 := by
      rw [show (2 : k) = algebraMap ℚ k 2 from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    have key := G2.sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) m
      (fun w => constantCoeff (G2.T F u w A))
    simp only [Finset.sum_map_toList] at key
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dpolyOf_monomial, dmonOf_eq_T_word, map_mul, constantCoeff_C,
      G2.cc_T_mul_q c F u q hq0 hq1 hq2, secondOrder_monomial, GE.dpolyOf_sum_P, map_sum]
    have hR : ∑ x, constantCoeff (DpolyOf F u
        (∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
          (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k)))) A) =
        a * ∑ x, ∑ y, c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          constantCoeff (G2.T F u (G2.word (Finset.univ : Finset ι).toList
            (m - Finsupp.single y 1 - Finsupp.single x 1)) A) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GE.dpolyOf_sum_P, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [dpolyOf_monomial, dmonOf_eq_T_word, map_mul, constantCoeff_C, mul_assoc]
    rw [hR, ← key]
    linear_combination (-(a * ((G2.splits (G2.word (Finset.univ : Finset ι).toList m)).map
      (fun p => constantCoeff (G2.T F u p.1 A) * G2.ev2 c p.2)).sum)) * h2

end GlobalTheory.HalfIdentity
end
end

