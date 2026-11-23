module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ExistsGroupRingSurj
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem grEx_gen {σ : Type} [Fintype σ] [DecidableEq σ] (n : σ → ℕ) [∀ s, NeZero (n s)]
    (S : Submonoid (∀ s, Multiplicative (ZMod (n s))))
    (h : ∀ s : σ, (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ∈ S)
    (g : ∀ s, Multiplicative (ZMod (n s))) : g ∈ S := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Submonoid.prod_mem _ fun s _ => ?_
  have hs : Pi.mulSingle s (g s) =
      (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ^
        (Multiplicative.toAdd (g s)).val := by
    rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rfl
  rw [hs]
  exact Submonoid.pow_mem _ (h s) _

theorem UpperTheory.V.AlgebraTools.exists_groupRing_surj :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ),
      ∃ φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) ∧ Function.Surjective φ ∧
        IsLocalRing (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) ∧
        (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ Λ))).map φ =
          RingHom.ker (MonoidAlgebra.lift Λ Λ (∀ s, Multiplicative (ZMod (l ^ e s))) 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e
  haveI : Fact l.Prime := ⟨hl⟩
  haveI hNZ : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  have hpg : IsPGroup l (∀ s, Multiplicative (ZMod (l ^ e s))) := by
    apply IsPGroup.of_card (n := ∑ s, e s)
    rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨hloc, hmax, -, -⟩ := UpperTheory.V.CF.grLocal l Λ (∀ s, Multiplicative (ZMod (l ^ e s))) hlm hpg
  haveI := hloc
  haveI hCOΛ : UpperTheory.V.Alg.IsCO Λ Λ := inferInstance
  haveI hCO : UpperTheory.V.Alg.IsCO Λ (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) := by
    apply UpperTheory.V.Alg.co_finite Λ Λ
    intro x
    refine ⟨UpperTheory.V.CF.aug Λ _ x, ?_⟩
    rw [hmax, Ideal.mem_comap, map_sub, AlgHom.commutes]
    simp
  set gen : σ → MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) := fun s =>
    MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s)))
      (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s)))) with hgen
  have haug_of : ∀ g, UpperTheory.V.CF.aug Λ (∀ s, Multiplicative (ZMod (l ^ e s)))
      (MonoidAlgebra.of Λ _ g) = 1 := by
    intro g
    simp [UpperTheory.V.CF.aug]
  have hamem : ∀ s, gen s - 1 ∈ IsLocalRing.maximalIdeal (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) := by
    intro s
    rw [hmax, Ideal.mem_comap, map_sub, map_one, hgen, haug_of, sub_self]
    exact Ideal.zero_mem _
  obtain ⟨φ, ⟨hφC, hφX⟩, -⟩ := UpperTheory.V.Alg.co_ev Λ Λ
    (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) σ
    (Algebra.ofId Λ _) (fun s => gen s - 1) hamem
  have hφ1 : ∀ s, φ (1 + MvPowerSeries.X s) = gen s := by
    intro s
    rw [map_add (f := _), map_one, hφX]
    ring
  have hofrange : ∀ g, MonoidAlgebra.of Λ _ g ∈ φ.range := by
    intro g
    let S : Submonoid (∀ s, Multiplicative (ZMod (l ^ e s))) :=
      { carrier := {g | MonoidAlgebra.of Λ _ g ∈ φ.range}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          exact Subalgebra.mul_mem _ ha hb
        one_mem' := by
          simp only [Set.mem_setOf_eq, map_one]
          exact Subalgebra.one_mem _ }
    exact grEx_gen (fun s => l ^ e s) S (fun s => ⟨1 + MvPowerSeries.X s, hφ1 s⟩) g
  have hsurj : Function.Surjective φ := by
    intro y
    suffices y ∈ φ.range by simpa using this
    induction y using MonoidAlgebra.induction_on with
    | of g => exact hofrange g
    | add f g hf hg => exact Subalgebra.add_mem _ hf hg
    | smul r f hf => exact Subalgebra.smul_mem _ hf r
  refine ⟨φ, hφ1, hsurj, hloc, ?_⟩
  have hker := (UpperTheory.V.CF.augKer Λ (∀ s, Multiplicative (ZMod (l ^ e s)))).1
  change _ = RingHom.ker (UpperTheory.V.CF.aug Λ _)
  rw [hker, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    apply Ideal.subset_span
    exact ⟨Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))), (hφX s).symm⟩
  · rw [UpperTheory.V.CF.augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    set J := Ideal.span (Set.range (⇑φ ∘ MvPowerSeries.X))
    let S : Submonoid (∀ s, Multiplicative (ZMod (l ^ e s))) :=
      { carrier := {g | MonoidAlgebra.of Λ _ g - 1 ∈ J}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          have : MonoidAlgebra.of Λ _ a * MonoidAlgebra.of Λ _ b - 1 =
              (MonoidAlgebra.of Λ _ a - 1) * MonoidAlgebra.of Λ _ b + (MonoidAlgebra.of Λ _ b - 1) := by ring
          rw [this]
          exact J.add_mem (J.mul_mem_right _ ha) hb
        one_mem' := by
          simp only [Set.mem_setOf_eq, map_one, sub_self]
          exact J.zero_mem }
    refine grEx_gen (fun s => l ^ e s) S (fun s => ?_) g
    show gen s - 1 ∈ J
    rw [← hφX]
    exact Ideal.subset_span ⟨s, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqInj
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

section

open GlobalTheory.IwahoriInj GlobalTheory.IwahoriTraceProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem jqInj_compact (C : Subgroup 𝓀[k]ˣ) : IsCompact (iwC k n C : Set (GL (Fin n) k)) := by
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho)
    fun g hg => iwahori_le_KO k _ (((memIwC k n C).1 g).1 hg).1

private theorem jqInj_dom {x : kˣ} (hx : valuation k (x : k) = uniformizer k) (m : ℕ) :
    Dom fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))) := by
  intro i j hij
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
  refine zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le ?_
  have : ((i : ℕ) : ℤ) ≤ (j : ℕ) := by exact_mod_cast Fin.le_def.1 hij
  nlinarith

private theorem jqInj_ev {x : kˣ} (hx : valuation k (x : k) = uniformizer k) {u : GL (Fin n) k}
    (hu : u ∈ unipB k (Fin n)) : ∀ᶠ m : ℕ in Filter.atTop,
      diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹ ∈ unipO k n := by
  have key : ∀ u ∈ unipB k (Fin n), ∀ᶠ m : ℕ in Filter.atTop, GlobalTheory.StepData.IntM
      (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹).val := by
    intro u hu
    simp only [GlobalTheory.StepData.IntM, Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      rw [← map_inv, diag_mul_mul_diag]
      have h1 : Deep (-((m : ℤ) * (i : ℕ)) + (m : ℤ) * (j : ℕ))
          ((x ^ (-((m : ℤ) * (i : ℕ))) * (x ^ (-((m : ℤ) * (j : ℕ))))⁻¹ : kˣ) : k) := by
        rw [← _root_.zpow_neg, neg_neg, ← _root_.zpow_add, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
      have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast Fin.lt_def.1 h
      exact deep_zero_iff.1 ((h1.mul hm).mono (by nlinarith))
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).2 i]
      exact one_mem _
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).1 i j h]
      exact zero_mem _
  filter_upwards [key u hu, key _ (inv_mem hu)] with m h1 h2
  refine ⟨conj_mem_unipB _ hu, GlobalTheory.StepData.mem_KO.2 ⟨h1, ?_⟩⟩
  convert h2 using 2
  group

end

theorem UpperTheory.V.AlgebraTools.jqInj :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v : fixd π (iwC k n C), (Submodule.Quotient.mk (v : V) : Jacquet π (unipB k (Fin n))) = 0 → v = 0 := by
  intro k _ _ _ _ n C V _ _ π hπ v hv
  have h1 : (v : V) ∈ twKer π (unipB k (Fin n)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hc
    exact GlobalTheory.IwahoriInj.unif_pos.ne hc
  have hx : valuation k ((Units.mk0 c hc0 : kˣ) : k) = uniformizer k := hc
  generalize Units.mk0 c hc0 = x at hx
  have hle : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  have h2 : ∀ w ∈ twKer π (unipB k (Fin n)) 1, ∀ᶠ m : ℕ in Filter.atTop,
      π (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w ∈ twKer π (iwC k n C) 1 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, w, rfl⟩ := hy
      filter_upwards [jqInj_ev hx u.2] with m hm
      have := GlobalTheory.IwahoriInj.sub_mem_twKer (π := π) (hle hm)
        (π (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, ← map_sub] at this
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using this
    | zero => simp
    | add a b _ _ ha hb =>
      filter_upwards [ha, hb] with m h1 h2
      rw [map_add (f := _)]
      exact add_mem h1 h2
    | smul a y _ hy =>
      filter_upwards [hy] with m h1
      rw [map_smul]
      exact Submodule.smul_mem _ a h1
  obtain ⟨m, hm⟩ := (h2 _ h1).exists
  have hd := jqInj_dom (n := n) hx m
  obtain ⟨s, hs, -, hsum⟩ := domSum k n _ hd
  have hq : IsUnit (resCard k : ℂ) := by
    refine Ne.isUnit (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  have hu := (domMul k n C ℂ V π).2.1 hq _ hd
  have h0 : hk π (iwC k n C) (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) v = 0 := by
    refine Subtype.ext (GlobalTheory.IwahoriInj.eq_zero_of_fixed hπ (jqInj_compact C)
      (GlobalTheory.IwahoriInj.mem_fixed.2 (hk π (iwC k n C) _ v).2) ?_)
    rw [hsum]
    refine Submodule.sum_mem _ fun u hu => ?_
    rw [map_mul, Module.End.mul_apply]
    exact GlobalTheory.IwahoriInj.apply_mem_twKer (hle (hs u hu)) hm
  exact ((Module.End.isUnit_iff _).1 hu).1 (h0.trans (map_zero _).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqRec
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.AlgebraTools.jqRec :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A) (rc : IrrGL (k := w.adicCompletion E) → WD h), Laws a ha ε rc → ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient π.ρ (prinSeries ψ) → ∀ σ : Weil h, (rc (cls π)).charPol σ = ∏ i, (X - C ((ψ i (a σ) : ℂˣ) : ℂ)) := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc L n π ψ hψ hs σ
  have H := GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (k := w.adicCompletion E) ⟨π.V, π.ρ, π.smooth, π.irr⟩ hψ hs
  have H1 := (hasSupport_of_isCuspSupport H).of_equiv (equivRep π)
  have H2 := L.supp (cls π) _ H1 σ
  rw [H2, Multiset.map_map, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  show (rc (IrrGL.ofChar (ψ i) (hψ i))).charPol σ = _
  rw [L.one]
  rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwTamePair
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

private theorem tamePair_aeval_comm {K A : Type} [CommRing K] [Ring A] [Algebra K A]
    (P X Y : A) (h : P * X = Y * P) (p : Polynomial K) :
    P * Polynomial.aeval X p = Polynomial.aeval Y p * P := by
  have hp : ∀ k : ℕ, P * X ^ k = Y ^ k * P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, pow_succ, mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, add_mul, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hp]

private theorem tamePair_inj {K : Type} [Field K] {n : ℕ} (c : K) (hc : c ≠ 0)
    (P : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    (ha : ∀ i j, a i ≠ c * a j) (Y : Matrix (Fin n) (Fin n) K) (hY : P * Y = Y * (c • P)) :
    Y = 0 := by
  have h1 := tamePair_aeval_comm (K := K) Y (c • P) P hY.symm P.charpoly
  rw [Matrix.aeval_self_charpoly, zero_mul, hP] at h1
  have hu : ∀ i, IsUnit (Polynomial.aeval (c • P) (Polynomial.X - Polynomial.C (a i))) := by
    intro i
    have e : Polynomial.aeval (c • P) (Polynomial.X - Polynomial.C (a i)) =
        (-c) • (Matrix.scalar (Fin n) (a i / c) - P) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      ext k l
      by_cases hkl : k = l
      · subst hkl
        simp [Matrix.algebraMap_matrix_apply]
        field_simp
        ring
      · simp [Matrix.algebraMap_matrix_apply, hkl]
    rw [e, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, ← Matrix.eval_charpoly, hP,
      Polynomial.eval_prod, isUnit_iff_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hc)) (Finset.prod_ne_zero_iff.mpr ?_)
    intro j _ h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    apply ha i j
    rw [sub_eq_zero, div_eq_iff hc] at h
    rw [h, mul_comm]
  have hs : ∀ s : Finset (Fin n),
      IsUnit (Polynomial.aeval (c • P) (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i)))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, map_mul]; exact (hu i).mul ih
  exact (hs Finset.univ).mul_left_eq_zero.mp h1

private theorem tamePair_binom {K : Type} [CommRing K] (q : ℕ) :
    ∃ r : Polynomial K, (1 + Polynomial.X) ^ q =
      1 + (q : Polynomial K) * Polynomial.X + Polynomial.X ^ 2 * r := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨(q : Polynomial K) + r + Polynomial.X * r, ?_⟩
    rw [pow_succ, hr]; push_cast; ring

private theorem tamePair_nil {K A : Type} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] (q : ℕ) (P Q X : A) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hinj : ∀ Y : A, P * Y = Y * ((q : K) • P) → Y = 0)
    (hX : IsNilpotent X) (h : P * (1 + X) = (1 + X) ^ q * P) : X = 0 := by
  obtain ⟨r, hr⟩ := tamePair_binom (K := K) q
  set g : Polynomial K := (q : Polynomial K) * Polynomial.X + Polynomial.X ^ 2 * r with hg
  have h1 : P * X = Polynomial.aeval X g * P := by
    have := congrArg (Polynomial.aeval X) hr
    rw [map_pow, map_add (f := _), map_one, Polynomial.aeval_X, add_assoc, map_add (f := _), map_one, ← hg] at this
    rw [this, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  have h2 : ∀ p : Polynomial K, P * Polynomial.aeval X p * Q = Polynomial.aeval X (p.comp g) := by
    intro p
    rw [tamePair_aeval_comm P X _ h1, mul_assoc, hPQ, mul_one, Polynomial.aeval_comp]
  let ψ : A →ₗ[K] A := (LinearMap.mulRight K Q).comp (LinearMap.mulLeft K P) - (q : K) • LinearMap.id
  have hψ : ∀ Y, ψ Y = P * Y * Q - (q : K) • Y := fun _ => rfl
  have hψa : ∀ p : Polynomial K, ψ (Polynomial.aeval X p) =
      Polynomial.aeval X (p.comp g - (q : Polynomial K) * p) := by
    intro p
    rw [hψ, h2, map_sub, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hψi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Y hY
    apply hinj
    rw [hψ, sub_eq_zero] at hY
    rw [mul_smul_comm, ← smul_mul_assoc, ← hY, mul_assoc, hQP, mul_one]
  let L : Polynomial K →ₗ[K] A :=
    (Polynomial.aeval X).toLinearMap.comp (LinearMap.mulLeft K (Polynomial.X ^ 2))
  have hL : ∀ p, L p = Polynomial.aeval X (Polynomial.X ^ 2 * p) := fun _ => rfl
  have hW : ∀ Y ∈ LinearMap.range L, ψ Y ∈ LinearMap.range L := by
    rintro _ ⟨p, rfl⟩
    refine ⟨((q : Polynomial K) + Polynomial.X * r) ^ 2 * p.comp g - (q : Polynomial K) * p, ?_⟩
    rw [hL, hL, hψa]
    congr 1
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
    generalize p.comp g = t
    rw [hg]; ring
  have hsurj : Function.Surjective (ψ.restrict hW) := by
    apply LinearMap.injective_iff_surjective.mp
    intro x y hxy
    exact Subtype.ext (hψi (congrArg Subtype.val hxy))
  have hXW : ψ X ∈ LinearMap.range L := by
    refine ⟨r, ?_⟩
    have := hψa Polynomial.X
    rw [Polynomial.aeval_X] at this
    rw [this, hL, Polynomial.X_comp]
    congr 1
    rw [hg]; ring
  obtain ⟨⟨_, p, rfl⟩, hw⟩ := hsurj ⟨_, hXW⟩
  have h3 : L p = X := hψi (congrArg Subtype.val hw)
  rw [hL, map_mul, map_pow, Polynomial.aeval_X] at h3
  have hc : Commute X (Polynomial.aeval X p) := tamePair_aeval_comm X X X rfl p
  have hn : IsNilpotent (X * Polynomial.aeval X p) := hc.isNilpotent_mul_right hX
  have h4 : X * (1 - X * Polynomial.aeval X p) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, h3, sub_self]
  exact hn.isUnit_one_sub.mul_left_eq_zero.mp h4

theorem UpperTheory.V.AlgebraTools.tamePair :
    ∀ (K : Type) [Field K] [CharZero K] (n q : ℕ) (P T : GL (Fin n) K) (a : Fin n → K), 2 ≤ q → P * T * P⁻¹ = T ^ q → (P : Matrix (Fin n) (Fin n) K).charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)) → (∀ i j, a i ≠ (q : K) * a j) → IsNilpotent (((T ^ (q - 1) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) → T ^ (q - 1) = 1 ∧ P * T = T * P := by
  intro K _ _ n q P T a hq hPT hP ha hN
  have hq0 : (q : K) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : P * T ^ (q - 1) = (T ^ (q - 1)) ^ q * P := by
    rw [← pow_mul, mul_comm (q - 1) q, pow_mul, ← hPT, conj_pow, inv_mul_cancel_right]
  have h2 := tamePair_nil (K := K) q (P : Matrix (Fin n) (Fin n) K)
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) _ (Units.mul_inv P) (Units.inv_mul P)
    (tamePair_inj (q : K) hq0 _ a hP ha) hN (by
      rw [add_sub_cancel, ← Units.val_mul, h1, Units.val_mul, Units.val_pow_eq_pow_val _ q])
  have h3 : T ^ (q - 1) = 1 := Units.ext (sub_eq_zero.mp h2)
  refine ⟨h3, ?_⟩
  have h4 : T ^ q = T := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h3
    rw [pow_succ, h3, one_mul]
  rw [h4] at hPT
  exact mul_inv_eq_iff_eq_mul.mp hPT
end

