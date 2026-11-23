module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPoint
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TotalDegreeEqOfMemHarmA
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMul
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.AtAdd

variable {q : ℕ} [Fact q.Prime]


open Classical in
theorem sub_mem_of_uw (M : Mdl q) (hM : M.Ok) (s t : ℂ) (ht : t ∉ M.L.lattice) (hy : M.y t ≠ 0)
    (hu : M.u s = M.u t) (hw : M.w s = M.w t) : s - t ∈ M.L.lattice := by
  have hwt : M.w t = -1 / M.y t := by simp [Mdl.w, ht]
  have hwt0 : M.w t ≠ 0 := by rw [hwt]; exact div_ne_zero (by norm_num) hy
  have hs : s ∉ M.L.lattice := by
    intro hs
    apply hwt0
    rw [← hw]; simp [Mdl.w, hs]
  have hws : M.w s = -1 / M.y s := by simp [Mdl.w, hs]
  have hys : M.y s ≠ 0 := by
    intro h
    apply hwt0
    rw [← hw, hws, h, div_zero]
  have hyy : M.y s = M.y t := by
    rw [hws, hwt, div_eq_div_iff hys hy] at hw
    linear_combination hw
  have hxx : M.x s = M.x t := by
    have h1 : M.u s = -M.x s / M.y s := by simp [Mdl.u, hs]
    have h2 : M.u t = -M.x t / M.y t := by simp [Mdl.u, ht]
    rw [h1, h2, hyy, div_left_inj' hy] at hu
    exact neg_injective hu
  obtain ⟨φ, -, hk, hφ⟩ := Mdl.exists_pointHom q M hM
  obtain ⟨h1, e1⟩ := hφ s hs
  obtain ⟨h2, e2⟩ := hφ t ht
  rw [← hk, map_sub, e1, e2, sub_eq_zero]
  congr 1 <;> simp [hxx, hyy]

theorem sub_mem_of_germ (M : Mdl q) (hM : M.Ok) (α s t : ℂ) (hα : α ≠ 0) (ht : M.Small t)
    (hu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u (α * z + s) = M.u (α * z + t))
    (hw : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.w (α * z + s) = M.w (α * z + t)) : s - t ∈ M.L.lattice := by
  have hg := ((uw_elliptic_flow q M hM).2.2.2.2.2.2.2.2 t ht).2.2.2.2.1
  have htend : Filter.Tendsto (fun z : ℂ => α * z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous (fun z : ℂ => α * z + t) := by fun_prop
      simpa using hc.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hα] using hz
  obtain ⟨z, h1, h2, h3⟩ := ((htend.eventually hg).and (hu.and hw)).exists
  have := sub_mem_of_uw M hM _ _ h1.1 h1.2.1 h2 h3
  simpa using this

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  simp [logS, ← coeff_zero_eq_constantCoeff_apply]

theorem bd_w (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (h : M.Chart ℓ) : Bd 1 (hat M.ι ℓ M.w) := by
  obtain ⟨-, v, xs, ys, -, -, hys, -, -, hc, -, hw, -⟩ := _root_.GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ h
  apply (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 hys hc
  rw [pow_zero, one_mul, mul_comm, hw]
  intro n
  rw [map_neg, norm_neg, coeff_X_pow]
  split_ifs <;> simp

theorem germ_add (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (ζ ζ' : ℂ_[q]) (p p' t : ℂ) (h : M.At ω ζ p) (h' : M.At ω ζ' p') (ht : M.At ω (ζ * ζ') t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (1 * z + (p + p')) = F (1 * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hEp : Ell M.L (fun z => F (z + p)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (x + p)).comp_analyticAt (f := F) (g := fun z => z + p) (by fun_prop)
    · show F (z + l + p) = F (z + p)
      rw [add_right_comm, hE.2 l hl]
  have hBp : Bdd (hat M.ι (C ω * logS) (fun z => F (z + p))) := by
    rw [hT ζ p h]
    exact ⟨1, (Shift.shift_laws q ζ h.2.1).1 _ _ hB⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := _root_.GlobalTheory.MomOne.Transfer.shift_eq_hat_translate q M ω ζ' p' _ hM h' hEp (han p h.1) hBp
  rw [hT ζ p h, (_root_.GlobalTheory.MomOne.ShiftComp.main q).1 ζ' ζ _ h'.2.1 h.2.1 ⟨1, hB⟩, mul_comm ζ' ζ, ← hT _ t ht] at hψ
  have h1 := (_root_.GlobalTheory.MomOne.ChartXY.chart_xy q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa (han t ht.1)).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [one_mul, ← e2, e1]
  congr 1; ring

theorem germ_mul (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p t : ℂ)
    (hL : ∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) (hα : M.ι α = zc a)
    (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hζ : ζ ^ (q ^ n) = 1)
    (h : M.At ω ζ p) (ht : M.At ω (ζ ^ k) t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z + α * p) = F (α * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hF0 : AnalyticAt ℂ F 0 := hA 0 (Or.inl (zero_mem _))
  have hmul : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → AnalyticAt ℂ (fun z => G (α * z)) 0 := fun G hG =>
    AnalyticAt.comp_of_eq (g := G) (f := fun z => α * z) hG (by fun_prop) (by simp)
  have hEα : Ell M.L (fun z => F (α * z)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (α * x)).comp_analyticAt (f := F) (g := fun z => α * z) (by fun_prop)
    · show F (α * (z + l)) = F (α * z)
      rw [mul_add, hE.2 _ (hL l hl)]
  have hsub := (_root_.GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω F hF0).2.2.1 α a hα
  have hm := (MulSeries.mulS_laws q).1 a
  have hBα : Bdd (hat M.ι (C ω * logS) (fun z => F (α * z))) := by
    rw [hsub]
    exact ⟨1, (sup_norm_laws q).2.1 _ _ _ hB hm.1 hm.2.1⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := _root_.GlobalTheory.MomOne.Transfer.shift_eq_hat_translate q M ω ζ p _ hM h hEα (hmul F hF0) hBα
  rw [hsub, ((_root_.GlobalTheory.MomOne.ShiftComp.main q).2 ζ n k a _ hζ hk ⟨1, hB⟩).2, ← hT _ t ht,
    ← (_root_.GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω _ (han t ht.1)).2.2.1 α a hα] at hψ
  have h1 := (_root_.GlobalTheory.MomOne.ChartXY.chart_xy q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa
    (hmul _ (han t ht.1))).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [← mul_add, ← e1, e2]

theorem norm_mul_sub_one_lt {ζ ξ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (h' : ‖ξ - 1‖ < 1) : ‖ζ * ξ - 1‖ < 1 := by
  have e : ζ * ξ - 1 = (ζ - 1) * (ξ - 1) + ((ζ - 1) + (ξ - 1)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h h'.le
  · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h h')

theorem norm_pow_sub_one_lt {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (k : ℕ) : ‖ζ ^ k - 1‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih h

theorem at_add_and_mul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  intro q _ M ω hM
  have hOk : M.Ok := hM.1
  obtain ⟨hex, -, -, hiff, h10⟩ := _root_.GlobalTheory.MomOne.SmallPt.at_exists_unique q M ω hM
  obtain ⟨hEu, hEw, -, -, -, -, -, -, hS⟩ := uw_elliptic_flow q M hOk
  have hBu : Bd 1 (hat M.ι (C ω * logS) M.u) := hM.2.2.1
  have hBw := bd_w M _ hM
  have hTu := fun ζ p h => (_root_.GlobalTheory.MomOne.SmallTranslate.shift_eq_translate q M ω ζ p hM h).1
  have hTw := fun ζ p h => (_root_.GlobalTheory.MomOne.SmallTranslate.shift_eq_translate q M ω ζ p hM h).2
  refine ⟨fun ζ ζ' p p' h h' => ?_, fun α a n k ζ p hL hα hk hζ h => ?_⟩
  · obtain ⟨t, ht⟩ := hex _ (norm_mul_sub_one_lt h.2.1 h'.2.1)
    have := sub_mem_of_germ M hOk 1 (p + p') t one_ne_zero ht.1
      (germ_add M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu ζ ζ' p p' t h h' ht)
      (germ_add M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw ζ ζ' p p' t h h' ht)
    refine (hiff _ t _ ht).2 ?_
    simpa using neg_mem this
  · by_cases h0 : α = 0
    · subst h0
      have ha : a = 0 := by
        have := (MulSeries.mulS_laws q).2.2.2.2.2 a
        rw [← hα, map_zero, norm_zero] at this
        exact norm_eq_zero.1 this.symm
      subst ha
      rw [zero_sub, norm_neg] at hk
      have hd : ((q : ℤ) ^ n) ∣ (k : ℤ) := by
        rw [← PadicInt.norm_int_le_pow_iff_dvd]
        simpa using hk
      have hd' : q ^ n ∣ k := by exact_mod_cast hd
      obtain ⟨m, rfl⟩ := hd'
      rw [pow_mul, hζ, one_pow, zero_mul]
      exact h10
    · obtain ⟨t, ht⟩ := hex _ (norm_pow_sub_one_lt h.2.1 k)
      have := sub_mem_of_germ M hOk α (α * p) t h0 ht.1
        (germ_mul M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu α a n k ζ p t hL hα hk hζ h ht)
        (germ_mul M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw α a n k ζ p t hL hα hk hζ h ht)
      refine (hiff _ t _ ht).2 ?_
      simpa using neg_mem this

end GlobalTheory.MomOne.AtAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.XLaterHarmonicNotMemSpan
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NabUniqCompare

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem pderiv_swap {σ R : Type} [CommRing R] (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hp, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem isHarmonic_iff_cmType {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) :
    IsHarmonic c P ↔ P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by
  have e : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ↔
      ∀ τ : E →+* ℂ, InPsi H τ → ∀ (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap,
      LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  rw [e]
  refine ⟨fun h τ _ => h τ, fun h τ => ?_⟩
  by_cases hτ : InPsi H τ
  · exact h τ hτ
  · have key : ∀ σ : E →+* ℂ, σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) →
        ∀ (i : Fin (Dw.mult σ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨σ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
      rintro σ rfl i i'
      rw [← h _ ((GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff τ).2 hτ) i' i]
      exact Finset.sum_congr rfl fun b _ => pderiv_swap _ _ _
    exact key τ (by ext x; simp)

def IsTopHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
    ∃ a : (E →+* ℂ) × ℕ → ℕ, RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P

theorem mem_harmA_iff {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) :
    P ∈ harmA c a n ↔ IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
      RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P ∧ ∀ m, IsIntegral ℤ (P.coeff m) := by
  rw [isHarmonic_iff_cmType]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

def colSumL {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S) :
    MvPolynomial (LtN Dw n) c.F →ₗ[c.F] S :=
  (MvPolynomial.basisMonomials (LtN Dw n) c.F).constr c.F fun m => ∏ b : Fin n, v b (colOf m b)

theorem colSumL_apply {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : colSumL c v P = colSum c v P := by
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, colSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (MvPolynomial.monomial m (P.coeff m) : MvPolynomial (LtN Dw n) c.F) =
      P.coeff m • MvPolynomial.basisMonomials (LtN Dw n) c.F m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, colSumL, Module.Basis.constr_basis, Algebra.smul_def]

def UniqueOn (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F), Q n P →
        sysVal Xo c nab y k F P = sysVal Xo c nab' y k F P

theorem UniqueOn.mono {Q Q' : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop} (h : UniqueOn Xo c Q)
    (hQ : ∀ n P, Q' n P → Q n P) : UniqueOn Xo c Q' :=
  fun nab nab' h1 h2 S _ _ y k n F P hP => h nab nab' h1 h2 S y k n F P (hQ n P hP)

theorem uniqueOn_span_iff (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) :
    (UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' | Q n P'}) ↔ UniqueOn Xo c Q := by
  refine ⟨fun h => h.mono Xo c fun n P hP => Submodule.subset_span hP, ?_⟩
  intro h _ nab nab' h1 h2 S _ _ y k n F P hP
  unfold sysVal
  rw [← colSumL_apply, ← colSumL_apply]
  refine LinearMap.eqOn_span ?_ hP
  intro P' hP'
  rw [colSumL_apply, colSumL_apply]
  exact h nab nab' h1 h2 S y k n F P' hP'

theorem span_harmA_eq (n : ℕ) :
    Submodule.span c.F {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n} =
      Submodule.span c.F {P | IsTopHarmonic c P} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro P ⟨a, ha⟩
    rw [mem_harmA_iff] at ha
    exact ⟨ha.1, ha.2.1, a, ha.2.2.1⟩
  · refine Submodule.span_le.2 ?_
    rintro P ⟨h1, h2, a, h3⟩
    obtain ⟨N, hN, hP, -⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P
      ⟨(isHarmonic_iff_cmType c P).1 h1, h2, h3⟩
    have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have := Submodule.smul_mem _ (N : c.F)⁻¹ (Submodule.subset_span
      (s := {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n}) ⟨a, hP⟩)
    rwa [inv_smul_smul₀ hN'] at this

theorem thExprUniqSt_iff_harmA : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun n P => ∃ a, P ∈ harmA c a n := by
  constructor
  · rintro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ y k n F P ⟨a, ha⟩
    letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F a P ha
  · intro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ _ y k n F a P ha
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F P ⟨a, ha⟩

theorem thExprUniqSt_iff_span : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l),
      UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' : MvPolynomial (LtN Dw n) c.F | IsTopHarmonic c P'} := by
  rw [thExprUniqSt_iff_harmA]
  refine forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => ?_
  rw [← uniqueOn_span_iff]
  simp only [span_harmA_eq]

theorem thExprUniqSt_iff_top : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun _ P => IsTopHarmonic c P := by
  rw [thExprUniqSt_iff_span]
  exact forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => uniqueOn_span_iff Xo c _

section Reframe




end Reframe

end GlobalTheory.NabUniqCompare
end
end

