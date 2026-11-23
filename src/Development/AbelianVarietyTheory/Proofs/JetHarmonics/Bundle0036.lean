module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThirdPointDerivativeAtZeroSeriesMemIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DmonOfMulCongrOfCongr
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGerms
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem nabVal_character_columns_of_canonGauge : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) :=
  GlobalTheory.nabVal_character_columns (GlobalTheory.exists_integral_germ_nabVal_congr
    GlobalTheory.canonGauge_dmonOf_hL_natCast_mul GlobalTheory.dmonOf_mul_congr_of_congr)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovectorMultiplierShift
section
open Formalism.REAL Finset

namespace GlobalTheory


open Finset in
theorem _root_.GlobalTheory.covector_multiplier_shift : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), _root_.Formalism.REAL.qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b - if a = j then x b else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), _root_.Formalism.REAL.qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t - if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  obtain ⟨hF, hqF⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  obtain ⟨hF', hqF'⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ W) n E' hE'
  have hιF : ∀ (a b : Fin n) (w : W), ι ((-E' b a) w) = (-E b a) (ι w) := by
    intro a b w
    simp only [LinearMap.neg_apply, map_neg, hι]
  have hνF : Function.Injective (fun s : Fin n => (1 : ℂ) - n - ν s) := by
    intro s t h
    apply hν
    have h' : (1 - n - ν s : ℂ) = 1 - n - ν t := h
    linear_combination -h'
  have hqE' : ∀ (u : ℂ) (w : W), (_root_.Formalism.REAL.qdet (fun a b => -E' b a) u) w
      = (∏ s, (u + (1 - n - ν s))) • w := by
    intro u w
    rw [hqF', LinearMap.smul_apply, hq, smul_smul]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hxF : ∀ (a b k : Fin n), (-E b a) * x k = x k * (-E b a) + if b = k then x a else 0 := by
    intro a b k
    rw [neg_mul, mul_neg, hx b a k]
    abel
  obtain ⟨v, hv1, hv2⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W n (fun a b => -E b a)
    (fun a b => -E' b a) ι x (fun s => 1 - n - ν s) hF hF' hιF hνF hqE' hxF j w
  · refine ⟨v, hv1, fun s u => ?_⟩
    have h := hv2 s ((n : ℂ) - 1 - u)
    rw [hqF, show (n : ℂ) - 1 - ((n : ℂ) - 1 - u) = u by ring, LinearMap.smul_apply] at h
    have h2 := congrArg (((-1 : ℂ) ^ n) • ·) h
    simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at h2
    rw [h2]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    split_ifs <;> ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DomSubsetClosureIsGenFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Cardinal Topology

namespace GlobalTheory.GenFrame

theorem subset_closure_forall_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {J : Type*} [Countable J] (f : J → E → ℂ) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hne : ∀ j, ∃ x ∈ U, f j x ≠ 0) : U ⊆ closure {x | x ∈ U ∧ ∀ j, f j x ≠ 0} := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set W : J → Set E := fun j => (U ∩ f j ⁻¹' {0}ᶜ) ∪ (closure U)ᶜ with hW
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    ((hf j).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hWd : ∀ j, Dense (W j) := by
    intro j
    rw [dense_iff_inter_open]
    intro O hO hOne
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hnot : ∀ y ∈ O, y ∉ W j := fun y hy hyW => by
      have : y ∈ O ∩ W j := ⟨hy, hyW⟩
      rw [hemp] at this
      exact this
    obtain ⟨y, hy⟩ := hOne
    have hyc : y ∈ closure U := by
      by_contra h
      exact hnot y hy (Or.inr h)
    obtain ⟨z, hzO, hzU⟩ := mem_closure_iff.mp hyc O hO hy
    have hz := GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) hU hc (hf j)
      (differentiableOn_const 0) (hO.inter hU) ⟨z, hzO, hzU⟩ Set.inter_subset_right
      (fun w hw => by
        by_contra h
        exact hnot w hw.1 (Or.inl ⟨hw.2, h⟩))
    obtain ⟨x, hx, hx0⟩ := hne j
    exact hx0 (hz hx)
  have hD := dense_iInter_of_isOpen hWo hWd
  refine (hD.open_subset_closure_inter hU).trans (closure_mono ?_)
  rintro x ⟨hxU, hx⟩
  refine ⟨hxU, fun j => ?_⟩
  rcases Set.mem_iInter.mp hx j with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory.GenFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane

namespace GlobalTheory.MomOne

theorem model_norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  let S : Subring ℂ_[q] := (NormedField.valuation (K := ℂ_[q])).integer
  have hS := Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))
  have h1 : IsIntegral S x := hx.tower_top
  have h2 := hS.mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem model_isIntegral_j {d : ℕ} (hd : d ≠ 0) {L : PeriodPair} (hL : IsOK d L) :
    IsIntegral ℤ (GlobalTheory.latticeCurve L).j := by
  have hw : ((GlobalTheory.halfOneAddSqrtNeg d hd : ℍ) : ℂ) = wK d := by
    change (1 + √d * Complex.I) / 2 = _
    rw [wK]; ring
  rw [GlobalTheory.latticeCurve_j (a := 1) (τ := GlobalTheory.halfOneAddSqrtNeg d hd) one_ne_zero]
  · exact GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg d hd
  · intro x
    rw [hL x, hw]
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨v, u, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩

theorem exists_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  intro d q _ ι L hd _ hL
  obtain ⟨E, h₁, h₂, h₃, h₄, h₆, hΔ, hc⟩ :=
    GlobalTheory.CMCurves.exists_integral_curve (model_isIntegral_j hd.ne_zero hL)
  have hE : E.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj : (GlobalTheory.latticeCurve L).j = E.j := by
    rw [← hc, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ]
    simp
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have e4 : E.c₄ / 12 = L.g₂ / (C.u : ℂ) ^ 4 := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, GlobalTheory.latticeCurve_c₄, Units.val_inv_eq_inv_val]
    field_simp
  have e6 : E.c₆ / 216 = L.g₃ / (C.u : ℂ) ^ 6 := by
    have : (GlobalTheory.latticeCurve L).c₆ = 216 * L.g₃ := by
      simp only [GlobalTheory.latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
      ring
    rw [← hC, WeierstrassCurve.variableChange_c₆, this, Units.val_inv_eq_inv_val]
    field_simp
  have hi : ∀ {x : ℂ}, IsIntegral ℤ x → IsIntegral ℤ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    hx.map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[q]) (RingHom.ext_int _ _)
  have ha : ∀ {x : ℂ}, IsIntegral ℤ x → IsAlgebraic ℚ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    (IsIntegral.tower_top (A := ℚ) (hi hx)).isAlgebraic
  refine ⟨⟨ι, L, C.u, E.map (ι : ℂ →+* ℂ_[q])⟩, rfl, rfl,
    ⟨hu, model_norm_le_one_of_isIntegral (hi h₁), model_norm_le_one_of_isIntegral (hi h₂),
      model_norm_le_one_of_isIntegral (hi h₃), model_norm_le_one_of_isIntegral (hi h₄),
      model_norm_le_one_of_isIntegral (hi h₆), ?_, ?_, ?_⟩, ha h₁, ha h₂, ha h₃, ha h₄, ha h₆⟩
  · simp [WeierstrassCurve.map_Δ, hΔ]
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₄ / 12 = ι (L.g₂ / (C.u : ℂ) ^ 4)
    rw [← e4, WeierstrassCurve.map_c₄, map_div₀, map_ofNat]
    rfl
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₆ / 216 = ι (L.g₃ / (C.u : ℂ) ^ 6)
    rw [← e6, WeierstrassCurve.map_c₆, map_div₀, map_ofNat]
    rfl

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolynomialTorsionCharacterLevelStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_polynomial_torsion_character_level : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ∀ (n : ℕ) (ζ : K), ζ ^ (p ^ n) = 1 → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  first | exact @GlobalTheory.ConvSer.exists_intg_polynomial_level | exact GlobalTheory.ConvSer.exists_intg_polynomial_level | (intros; apply GlobalTheory.ConvSer.exists_intg_polynomial_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevel
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_sum_sq_le_fin_mul {M : Type} [NormedAddCommGroup M] {n : ℕ} (s : Finset (Fin n)) (v : Fin n → M) :
    ‖∑ c ∈ s, v c‖ ^ 2 ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have h1 : ‖∑ c ∈ s, v c‖ ≤ ∑ c ∈ s, ‖v c‖ := norm_sum_le _ _
  have h2 : (∑ c ∈ s, ‖v c‖) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (s.card : ℝ) ≤ n := by
    have := card_le_univ s
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h4 : 0 ≤ ∑ c ∈ s, ‖v c‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ c ∈ s, v c‖ ^ 2 ≤ (∑ c ∈ s, ‖v c‖) ^ 2 := by gcongr
    _ ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := h2
    _ ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h4

theorem offDiagPart_sq_le_of_lev : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M),
    IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) →
      ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hsh hj hlev

  have step1 : ∀ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤
      (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 :=
    fun b => norm_sum_sq_le_fin_mul _ _
  have swap : ∑ b, ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 =
      ∑ c, ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 :=
    Finset.sum_comm' (fun b c => by
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ne_comm)
  have step2 : ∀ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 ≤
      (bv / 16) ^ 2 * ‖x c‖ ^ 2 := by
    intro c
    refine le_trans ?_ (lev_offDiag_normSq_le M n ε E μ kk j bv (x c) hmod hsh hj (hlev c))
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    calc ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2
        ≤ ∑ b ∈ univ.erase c, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 := by
          refine sum_le_sum fun b hb => ?_
          have hcb : c ∈ univ.erase b :=
            mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 h.symm, mem_univ _⟩
          exact single_le_sum (f := fun b' => ‖E b b' (x c)‖ ^ 2) (fun _ _ => sq_nonneg _) hcb
      _ ≤ ∑ b, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2
      ≤ ∑ b, (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 := sum_le_sum fun b _ => step1 b
    _ = ∑ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 := by
      rw [← mul_sum, swap, mul_sum]
    _ ≤ ∑ c, (bv / 16) ^ 2 * ‖x c‖ ^ 2 := sum_le_sum fun c _ => step2 c
    _ = (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by rw [mul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLe
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_gl_size : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M),
    IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
    ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv b w hM hS hb hj hL
  have hj' : j ≤ 4 * n ^ 2 + 2 := by omega
  obtain ⟨hbv, hpos, -⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj'
  have hoff := _root_.GlobalTheory.lev_offDiag_normSq_le M n ε E μ kk j bv w hM hS hj' hL
  have hdiag := (_root_.GlobalTheory.wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) w hM.2.1 hL.2).2.2
  have hd : ∀ a, ‖E a a w‖ ^ 2 ≤ (3 * bv) ^ 2 * ‖w‖ ^ 2 := by
    intro a
    refine hdiag a (3 * bv) ?_
    intro ω hω
    obtain ⟨h1, h2⟩ := hpos ω hω a
    rw [abs_le]
    by_cases h : a.val + 1 < kk
    · obtain ⟨h3, h4⟩ := h1 h
      constructor <;> linarith
    · obtain ⟨h3, h4⟩ := h2 (by omega)
      constructor <;> linarith
  have hn : (1 : ℝ) ≤ n := by
    have := hS.1
    have := hS.2.1
    exact_mod_cast (by omega : 1 ≤ n)
  have hbig : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv := hS.2.2.2.2.2
  have hsplit : ∑ a, ∑ c, ‖E a c w‖ ^ 2
      = ∑ a, ‖E a a w‖ ^ 2 + ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.add_sum_erase univ (fun c => ‖E a c w‖ ^ 2) (Finset.mem_univ a)).symm
  have hsum : ∑ a, ‖E a a w‖ ^ 2 ≤ n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by
    calc ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ _a : Fin n, (3 * bv) ^ 2 * ‖w‖ ^ 2 := Finset.sum_le_sum fun a _ => hd a
      _ = n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by simp
  have hO : 0 ≤ ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have hO' : ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 :=
    le_trans (le_mul_of_one_le_left hO hn) hoff
  have hn7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn (by norm_num)
  have hb1 : 10 ^ 6 * (n : ℝ) ≤ bv := by linarith
  have hb2 : 9 * (n : ℝ) + 1 ≤ bv ^ 2 := by nlinarith
  have hb4 : bv ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hbv.le hb 4
  have hc : (n : ℝ) * (3 * bv) ^ 2 + (bv / 16) ^ 2 ≤ b ^ 4 := by
    have h1 : (9 * (n : ℝ) + 1) * bv ^ 2 ≤ bv ^ 2 * bv ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)
    nlinarith [sq_nonneg bv]
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖w‖)
  rw [hsplit]
  nlinarith

end GlobalTheory
end

