module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0309
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEtStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  first | (exact @GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt) | (exact GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt) | (intros; apply GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

abbrev upPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2

theorem relIndex_unipLat {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c C : Fin n → Fin n → ℤ}
    (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) = q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - c p.1 p.2).toNat := by
  rw [Cayley.relIndex_unipLat L ϖ σ q n h c C hc hC hI]
  have h1 := relIndex_upLat_eq_sq L ϖ σ q n h c C hc.1 hC.1 hI.1
  rw [UpLatIndex.relIndex_upLat L ϖ σ q n h c C hI.1, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm, pow_mul] at h1
  exact (Nat.pow_left_injective two_ne_zero h1).symm

theorem v_eq_exp {x : L} (hx : x ≠ 0) : Valued.v x = WithZero.exp (-ordL x) := by
  rw [ordL_eq, neg_neg, WithZero.exp_log (by simpa using hx)]

theorem exists_idealWeight {c : Fin n → Fin n → ℤ} :
    ∃ C : Fin n → Fin n → ℤ, IsWeight C ∧ IsIdealWeight c C ∧ IsIdealWeight (fun _ _ => 0) C := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i j, |c i j| ≤ M := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun p : Fin n × Fin n => (c p.1 p.2).natAbs).bddAbove
    exact ⟨M, fun i j => by
      have : (c i j).natAbs ≤ M := hM ⟨(i, j), rfl⟩
      rw [← Int.natCast_natAbs]; exact_mod_cast this⟩
  have key : ∀ d : Fin n → Fin n → ℤ, (∀ i j, |d i j| ≤ M) →
      IsIdealWeight d fun i j => (M : ℤ) * (n + i.val - j.val) := by
    intro d hd
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    refine ⟨fun i j _ => ?_, fun i j k h1 _ => ?_, fun i j k _ h2 => ?_⟩
    · have h1 : (1 : ℤ) ≤ n + i.val - j.val := by have := j.2; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ j.val - i.val := by have := Fin.lt_def.1 h1; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ k.val - j.val := by have := Fin.lt_def.1 h2; omega
      nlinarith [abs_le.1 (hd j k)]
  refine ⟨_, ⟨fun i j => ?_, fun i j k _ _ => ?_⟩, key c hM, key _ fun _ _ => by simp⟩
  · have := i.2
    have := j.2
    simp only [Fin.val_rev]
    congr 1
    omega
  · have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    have h1 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith

theorem sum_upPairs (a : Fin n → ℤ) :
    ∑ p ∈ upPairs n, (a p.1 - a p.2) = ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ p ∈ upPairs n, a p.1 = ∑ i, a i * ((n : ℤ) - 1 - i.val) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul, mul_comm]
    congr 1
    have := i.2
    omega
  have h2 : ∑ p ∈ upPairs n, a p.2 = ∑ i, a i * (i.val : ℤ) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_half (a : Fin n → ℤ) (ha : ∀ i, a i.rev = -a i) :
    ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) =
      2 * ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) =
      ∑ i : Fin n, if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => Fin.castLE (Nat.div_le_self n 2) i) (fun i _ => by simp)
      (fun i _ j _ e => Fin.castLE_injective _ e) (fun j hj => ⟨⟨j.val, by simpa using hj⟩, by simp, rfl⟩)
      fun i _ => rfl
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n => if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0),
    h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  have hr : ((i.rev.val : ℕ) : ℤ) = n - 1 - i.val := by rw [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, ha, hr]
  split_ifs with h1 h2 h2
  · omega
  · ring
  · ring
  · have : (n : ℤ) - 1 - 2 * i.val = 0 := by omega
    simp [this]

theorem zpow_finset_sum {ι : Type} {z : ℂ} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFirst.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFirst.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFirst.main ..)

end GlobalTheory.BorelUMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMatrixForDepth
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory

noncomputable section

variable {C : Type} [Field C]

theorem powRow_nonneg_of_nsmul {a : WithTop ℝ} {N : ℕ} (hN : N ≠ 0) (h : 0 ≤ N • a) : 0 ≤ a := by
  cases a with
  | top => exact le_top
  | coe r =>
    have e : ((N • r : ℝ) : WithTop ℝ) = N • (r : WithTop ℝ) := WithTop.coe_nsmul _ _
    rw [← e] at h
    have h' : (0 : ℝ) ≤ N • r := by exact_mod_cast h
    rw [nsmul_eq_mul] at h'
    have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have : 0 ≤ r := by
      by_contra hr
      push Not at hr
      nlinarith
    exact_mod_cast this

theorem powRow_int_root [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {N : ℕ} (hN : 0 < N)
    (y : C) (hy : IsIntV v y) : ∃ x, x ^ N = y ∧ IsIntV v x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hN
  refine ⟨x, hx, powRow_nonneg_of_nsmul hN.ne' ?_⟩
  rw [← AddValuation.map_pow, hx]
  exact hy

theorem powRow_int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  unfold IsIntV
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := (v.ne_top_iff).2 hb
  cases hvb : v b with
  | top => exact absurd hvb hb'
  | coe r =>
    rw [hvb] at h
    cases hva : v a with
    | top => exact le_top
    | coe s =>
      rw [hva] at h
      have h2 : r ≤ s + r := by exact_mod_cast h
      exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

theorem powRow_v_neg_one_pow (v : AddValuation C (WithTop ℝ)) (k : ℕ) : v ((-1 : C) ^ k) = 0 := by
  rw [AddValuation.map_pow, AddValuation.map_neg, AddValuation.map_one, smul_zero]

theorem powRow_exists [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {V : Type} [AddCommGroup V]
    [Module C V] (N : ℕ) (hN : 0 < N) (j : ℕ) : ∀ (m : ℕ) (z : Fin m → V),
    Module.finrank C (Submodule.span C (Set.range z)) ≤ j →
    ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧
      ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro m
  induction m with
  | zero =>
    intro z _
    exact ⟨1, fun w => w.elim0, by simp, fun w => w.elim0⟩
  | succ m ih =>
    intro z hz
    by_cases hli : LinearIndependent C z
    · have hmj : m + 1 ≤ j := by
        have := finrank_span_eq_card hli
        simp only [Fintype.card_fin] at this
        omega
      refine ⟨1, ?_, by simp [AddValuation.map_one], fun w hw => absurd hw (by omega)⟩
      intro w u
      unfold IsIntV
      rw [Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
      obtain ⟨u0, -, hu0⟩ := Finset.exists_min_image Finset.univ (fun u => v (g u))
        ⟨i, Finset.mem_univ _⟩
      have hg0 : g u0 ≠ 0 := by
        intro h0
        apply hi
        have := hu0 i (Finset.mem_univ _)
        rw [h0, AddValuation.map_zero] at this
        exact (v.top_iff).1 (top_le_iff.1 this)
      set c : Fin (m + 1) → C := fun u => g u / g u0 with hc
      have hc0 : c u0 = 1 := div_self hg0
      have hcint : ∀ u, IsIntV v (c u) := by
        intro u
        apply powRow_int_of_le v hg0
        have : c u * g u0 = g u := div_mul_cancel₀ _ hg0
        rw [this]
        exact hu0 u (Finset.mem_univ _)
      have hcz : ∑ u, c u • z u = 0 := by
        have : ∑ u, c u • z u = (g u0)⁻¹ • ∑ u, g u • z u := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [smul_smul, hc]
          simp only [div_eq_mul_inv, mul_comm]
        rw [this, hg, smul_zero]
      choose r hr hrint using fun u => powRow_int_root v hN (c u) (hcint u)
      set r' : Fin (m + 1) → C := Function.update r u0 1 with hr'
      have hr'N : ∀ u, r' u ^ N = c u := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self, one_pow, hc0]
        · rw [hr', Function.update_of_ne hu, hr]
      have hr'int : ∀ u, IsIntV v (r' u) := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self]; unfold IsIntV; rw [AddValuation.map_one]
        · rw [hr', Function.update_of_ne hu]; exact hrint u
      have hz' : Module.finrank C (Submodule.span C (Set.range (z ∘ u0.succAbove))) ≤ j := by
        have : Module.Finite C (Submodule.span C (Set.range z)) :=
          Module.Finite.span_of_finite C (Set.finite_range z)
        refine le_trans (Submodule.finrank_mono (Submodule.span_mono ?_)) hz
        rintro _ ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      obtain ⟨x', hx'int, hx'det, hx'k⟩ := ih (z ∘ u0.succAbove) hz'
      let A : Matrix (Fin (m + 1)) (Fin (m + 1)) C :=
        Matrix.of (Fin.snoc (fun w' => Fin.insertNth (α := fun _ => C) u0 0 (x' w')) r')
      have hAlast : ∀ u, A (Fin.last m) u = r' u := by
        intro u; simp [A, Fin.snoc_last]
      have hAcs : ∀ w' u, A w'.castSucc u = Fin.insertNth (α := fun _ => C) u0 0 (x' w') u := by
        intro w' u; simp [A, Fin.snoc_castSucc]
      refine ⟨A, ?_, ?_, ?_⟩
      · intro w u
        induction w using Fin.lastCases with
        | last => rw [hAlast]; exact hr'int u
        | cast w' =>
          rw [hAcs]
          induction u using Fin.succAboveCases u0 with
          | x =>
            rw [Fin.insertNth_apply_same]; unfold IsIntV; rw [AddValuation.map_zero]; exact le_top
          | p k => rw [Fin.insertNth_apply_succAbove]; exact hx'int w' k
      · rw [Matrix.det_succ_column A u0]
        rw [Fintype.sum_eq_single (Fin.last m)]
        · have hsub : A.submatrix (Fin.last m).succAbove u0.succAbove = x' := by
            ext w' k
            simp only [Matrix.submatrix_apply, Fin.succAbove_last]
            rw [hAcs, Fin.insertNth_apply_succAbove]
          rw [hsub, hAlast]
          rw [AddValuation.map_mul, AddValuation.map_mul, powRow_v_neg_one_pow, hx'det]
          have : r' u0 = 1 := by rw [hr', Function.update_self]
          rw [this, AddValuation.map_one]
          simp
        · intro w hw
          induction w using Fin.lastCases with
          | last => exact absurd rfl hw
          | cast w' => rw [hAcs, Fin.insertNth_apply_same]; simp
      · intro w hw
        induction w using Fin.lastCases with
        | last =>
          simp only [hAlast, hr'N]
          exact hcz
        | cast w' =>
          simp only [hAcs]
          rw [Fin.sum_univ_succAbove _ u0, Fin.insertNth_apply_same, zero_pow hN.ne', zero_smul,
            zero_add]
          simp only [Fin.insertNth_apply_succAbove]
          exact hx'k w' (by simpa using hw)

theorem powRow_matrix : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro C _ _ v V _ _ N hN j m z hz
  exact powRow_exists v N hN j m z hz

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFlip_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor) := by
  first | exact @GlobalTheory.EtC.Pair.exists_isFlip | exact GlobalTheory.EtC.Pair.exists_isFlip | (intros; apply GlobalTheory.EtC.Pair.exists_isFlip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRingHomModXPowSuccLift
section
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem ringHom_lift_sqZero {B A O R' : Type} [CommRing B] [CommRing A] [CommRing O] [CommRing R'] (α : B →+* A)
    (hα : α.FormallySmooth) (π : R' →+* O) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (β' : B →+* R') (χ : A →+* O) (hc : χ.comp α = π.comp β') :
    ∃ χ' : A →+* R', π.comp χ' = χ ∧ χ'.comp α = β' := by
  letI := α.toAlgebra
  letI := β'.toAlgebra
  letI := (π.comp β').toAlgebra
  haveI : Algebra.FormallySmooth B A := hα
  let π₁ : R' →ₐ[B] O := { π with commutes' := fun _ => rfl }
  let χ₁ : A →ₐ[B] O := { χ with commutes' := fun b => RingHom.congr_fun hc b }
  have hn : IsNilpotent (RingHom.ker (π₁ : R' →+* O)) := ⟨2, hk⟩
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn : A →+* R'), RingHom.ext fun a => ?_,
    RingHom.ext fun b => (Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn).commutes b⟩
  exact Algebra.FormallySmooth.liftOfSurjective_apply χ₁ π₁ hs hn a

theorem mk_eq_iff_X_pow_dvd {R : Type} [CommRing R] (k : ℕ) (x y : PowerSeries R) :
    Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ k}) x =
      Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ k}) y ↔ (X : PowerSeries R) ^ k ∣ x - y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

noncomputable def quotRingHom {A B R : Type} [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R) (n : ℕ)
    (φ : A → PowerSeries R) (hφ : IsRingHomMod π β n φ) :
    A →+* PowerSeries R ⧸ Ideal.span {(X : PowerSeries R) ^ n} where
  toFun f := Ideal.Quotient.mk _ (φ f)
  map_one' := by rw [← map_one (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd]; exact hφ.2.2.1
  map_mul' f g := by rw [← map_mul, mk_eq_iff_X_pow_dvd]; exact hφ.1 f g
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd]
    have := hφ.2.1 0 0
    simp only [add_zero] at this
    simpa using this
  map_add' f g := by rw [← map_add (f := _), mk_eq_iff_X_pow_dvd]; exact hφ.2.1 f g

theorem ker_factor_sq {R : Type} [CommRing R] (n : ℕ) (hn : 1 ≤ n)
    (hle : Ideal.span {(X : PowerSeries R) ^ (n + 1)} ≤ Ideal.span {(X : PowerSeries R) ^ n}) :
    RingHom.ker (Ideal.Quotient.factor hle) ^ 2 = ⊥ := by
  have hker : ∀ z ∈ RingHom.ker (Ideal.Quotient.factor hle), ∃ x, (X : PowerSeries R) ^ n ∣ x ∧
      Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ (n + 1)}) x = z := by
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨x, ?_, rfl⟩
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, ← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd,
      sub_zero] at hz
    exact hz
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := hker a ha
  obtain ⟨y, hy, rfl⟩ := hker b hb
  rw [Ideal.mem_bot, ← map_mul, ← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd, sub_zero]
  have h2 : (X : PowerSeries R) ^ (n + n) ∣ x * y := by rw [pow_add]; exact mul_dvd_mul hx hy
  exact (pow_dvd_pow _ (by omega : n + 1 ≤ n + n)).trans h2

theorem exists_lift_succ : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R), π.FormallySmooth → ∀ n : ℕ, 1 ≤ n → ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β n φ → ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f := by
  intro A B R _ _ _ π β hπ n hn φ hφ
  have hle : Ideal.span {(X : PowerSeries R) ^ (n + 1)} ≤ Ideal.span {(X : PowerSeries R) ^ n} := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
    exact pow_dvd_pow _ (Nat.le_succ n)
  have hs : Function.Surjective (Ideal.Quotient.factor hle) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, Ideal.Quotient.factor_mk hle x⟩
  have hc : (quotRingHom π β n φ hφ).comp π =
      (Ideal.Quotient.factor hle).comp ((Ideal.Quotient.mk _).comp ((C : R →+* PowerSeries R).comp β)) := by
    ext b
    change Ideal.Quotient.mk _ (φ (π b)) = Ideal.Quotient.factor hle (Ideal.Quotient.mk _ (C (β b)))
    rw [Ideal.Quotient.factor_mk, mk_eq_iff_X_pow_dvd]
    exact hφ.2.2.2 b
  obtain ⟨χ', h₁, h₂⟩ := ringHom_lift_sqZero π hπ _ hs (ker_factor_sq n hn hle) _ _ hc
  choose ψ hψ using fun f => Ideal.Quotient.mk_surjective (χ' f)
  refine ⟨ψ, ⟨fun f g => ?_, fun f g => ?_, ?_, fun b => ?_⟩, fun f => ?_⟩
  · rw [← mk_eq_iff_X_pow_dvd, map_mul, hψ, hψ, hψ, map_mul]
  · rw [← mk_eq_iff_X_pow_dvd, map_add (f := _), hψ, hψ, hψ, map_add (f := _)]
  · rw [← mk_eq_iff_X_pow_dvd, map_one, hψ, map_one]
  · rw [← mk_eq_iff_X_pow_dvd, hψ, ← RingHom.comp_apply χ' π, h₂]; rfl
  · rw [← mk_eq_iff_X_pow_dvd, ← Ideal.Quotient.factor_mk hle, hψ, ← RingHom.comp_apply, h₁]; rfl

end GlobalTheory.Nef.PathJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslationStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jet_morphism_extending_translation : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {l : Λ} {k k' : K.K} (e : K.le l k' k), ∃ χ : K.jet k ⟶ K.jet k', χ.deg = l ∧ jet0 k ≫ χ = ptHom (K.triv k') e ≫ jet0 k' ∧ jet1 k ≫ χ = ptHom (K.triv k') e ≫ jet1 k' ∧ ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), (TrivSqZeroExt.fst (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) = sh e x.fst) ∧ ∀ a, TrivSqZeroExt.snd (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) a = sh e (x.snd a) := by
  first | exact @GlobalTheory.AnPer.Charts.jet_sh | exact GlobalTheory.AnPer.Charts.jet_sh | (intros; apply GlobalTheory.AnPer.Charts.jet_sh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycleStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_agree_of_cocycle_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  first | exact @GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle | exact GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle | (intros; apply GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowFibreRankEqPDivGroupStatement
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulPow_fibreRank_eq_pDivGroup :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ),
      ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)),
        Function.Surjective r ∧
        RingHom.ker r = torsionIdeal (R := O) (A := G.A (k + m)) (p ^ k) ∧
        (∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a) ∧
        ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  exact @GlobalTheory.PDivGroup.exists_mulPow_fibreRank_eq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableNormalisationReducedFibresStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_normalization_reduced_fibers : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], ¬ IsField A → ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧ ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  first | (exact @GlobalTheory.exists_separable_normalisation_reduced_fibres) | (exact GlobalTheory.exists_separable_normalisation_reduced_fibres) | (intros; apply GlobalTheory.exists_separable_normalisation_reduced_fibres  <;> assumption)
end

