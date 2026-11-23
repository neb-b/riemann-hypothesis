module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedBasisIntegralPartOfLinearIndependen
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomials
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.HarmBasis

open MvPolynomial

theorem mem_HHa_of_mem_span {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {S : Set (MvPolynomial (Letter T r n) k)} (hS : S ⊆ HHa r n k cc isX a)
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k S) : P ∈ HHa r n k cc isX a := by
  classical
  induction hP using Submodule.span_induction with
  | mem y hy => exact hS hy
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add y z _ _ hy hz =>
    refine ⟨add_mem hy.1 hz.1, fun σ i i' h t => ?_, fun m hm => ?_⟩
    · rw [map_add (f := _), hy.2.1 σ i i' h t, hz.2.1 σ i i' h t]
    · rcases Finset.mem_union.1 (support_add hm) with h | h
      exacts [hy.2.2 m h, hz.2.2 m h]
  | smul q y _ hy =>
    refine ⟨Submodule.smul_mem _ _ hy.1, fun σ i i' h t => ?_, fun m hm => hy.2.2 m (support_smul hm)⟩
    rw [map_smul, hy.2.1 σ i i' h t]

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ σ, ∑ i : Fin (r σ), a σ i := by
  classical
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

theorem l1At_eq_l1Norm_map {K ι : Type} [Field K] (σ : K →+* ℂ) (P : MvPolynomial ι K) :
    l1At σ P = MvPoly.l1Norm (map σ P) := by
  rw [MvPoly.l1Norm_eq_sum_of_subset (support_map_subset σ P), l1At]
  simp only [coeff_map]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mult_add_mult_conjugate (Dw : Datum H) (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  have h2 := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hne : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    rw [h0] at h2
    have : (H.d : ℂ) = 0 := by simpa using h2.symm
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp [pow_two] at him hre
    have h0 : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [h0]
  have hs : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]
    simpa using h
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h
  · rw [if_pos h, if_neg (by rw [h, hc]; exact hne.symm)]
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos (by rw [h, map_neg, hc, neg_neg]), add_comm]

theorem card_LtN (Dw : Datum H) (n : ℕ) :
    Fintype.card (LtN Dw n) = FD.fdeg E * (Dw.p + Dw.q) * n := by
  have h1 := (ComplexEmbedding.involutive_conjugate E).bijective.sum_comp Dw.mult
  have h2 : ∑ τ, (Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ)) =
      Module.finrank ℚ E * (Dw.p + Dw.q) := by
    simp only [mult_add_mult_conjugate]
    rw [Finset.sum_const, Finset.card_univ, Embeddings.card E ℂ, smul_eq_mul]
  rw [Finset.sum_add_distrib, h1] at h2
  have h3 : Module.finrank ℚ E = 2 * FD.fdeg E := by
    rw [FD.fdeg, IsTotallyComplex.finrank E]
    omega
  have h4 : ∑ τ, Dw.mult τ = FD.fdeg E * (Dw.p + Dw.q) := by
    rw [h3, mul_assoc] at h2
    omega
  rw [Fintype.card_sigma, ← h4, Finset.sum_mul]
  simp only [Fintype.card_prod, Fintype.card_fin]

theorem bound_le_exp {R d D N : ℕ} {L x Δ : ℝ} (hR : 1 ≤ R) (hd : 1 ≤ d) (hΔ : 0 < Δ)
    (hle : R ≤ d * (1 + D) ^ N) (hL : Real.log (1 + D) ≤ 2 * L) :
    (1 + D : ℝ) ^ ((N : ℝ) / 2) * (√((R + 3) / 4) * √d * ((d : ℝ) ^ 3 * Δ ^ (1 / (d : ℝ))) * Real.exp x) ≤
      Real.exp (x + 2 * N * L + 4 * Real.log d + Real.log Δ / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 + D : ℝ) ^ ((N : ℝ) / 2) ≤ Real.exp (N * L) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)
    linarith
  have h2 : √((R + 3) / 4) ≤ √d * Real.exp (N * L) := by
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hle' : (R : ℝ) ≤ d * (1 + D) ^ N := by exact_mod_cast hle
    refine (Real.sqrt_le_sqrt (show ((R : ℝ) + 3) / 4 ≤ d * (1 + D) ^ N by linarith)).trans ?_
    rw [Real.sqrt_mul hd0.le]
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) h1) (Real.sqrt_nonneg _)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have h3 : Real.exp (4 * Real.log d) = √d * √d * (d : ℝ) ^ 3 := by
    rw [Real.mul_self_sqrt hd0.le, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hd0]
    ring
  have h4 : Real.exp (Real.log Δ / d) = Δ ^ (1 / (d : ℝ)) := by
    rw [Real.rpow_def_of_pos hΔ, mul_one_div]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, h3, h4,
    show 2 * (N : ℝ) * L = N * L + N * L by ring, Real.exp_add]
  calc _ ≤ Real.exp (N * L) * (√d * Real.exp (N * L) * √d * ((d : ℝ) ^ 3 * Δ ^ (1 / (d : ℝ))) * Real.exp x) := by
        gcongr
    _ = _ := by ring

theorem exists_reduced_basis_harmA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ (R : ℕ) (b : Fin R → MvPolynomial (LtN Dw n) c.F), (∀ i, b i ∈ harmA (Dw := Dw) c a n) ∧ (∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) ∧ R ≤ Module.finrank ℚ c.F * (1 + DF Dw a) ^ (FD.fdeg E * (Dw.p + Dw.q) * n) ∧ ∀ i (σ : c.F →+* ℂ), l1At σ (b i) ≤ Real.exp (140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a + 2 * FD.fdeg E * (Dw.p + Dw.q : ℕ) * n * L + 4 * Real.log (Module.finrank ℚ c.F) + Real.log |((NumberField.discr c.F : ℤ) : ℝ)| / Module.finrank ℚ c.F) := by
  intro E _ _ _ H Dw l c n hn a L hL h1 h2 h3 h4
  classical
  have hsp := (GlobalTheory.StdHarm.harmA_mem_span_short E H Dw l c n).2 hn a L hL h1 h2 h3 h4
  set x : ℝ := 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a with hx
  set S : Set (MvPolynomial (LtN Dw n) c.F) := {Q | Q ∈ harmA c a n ∧
    ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ x} with hS
  have hW : ∀ P ∈ Submodule.span c.F S, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
      fun τ i => a (τ, i) := fun P hP => mem_HHa_of_mem_span (S := S) (fun Q hQ => hQ.1.1) hP
  have hI : ∀ P, P ∈ MvPoly.integralPart (Submodule.span c.F S) ↔ P ∈ harmA (Dw := Dw) c a n := fun P =>
    ⟨fun h => ⟨hW P h.1, h.2⟩, fun h => ⟨hsp P h, h.2⟩⟩
  obtain ⟨ω, hω, hA⟩ := GlobalTheory.exists_short_independent_integers c.F
  obtain ⟨hR, b, -, hb, -⟩ := MvPoly.exists_reduced_basis_integralPart (Submodule.span c.F S) (D := DF Dw a)
    (fun P hP => totalDegree_le_of_rowDeg (hW P hP).2.2) S (fun P hP => (hI P).2 hP.1) rfl
    (B := Real.exp x) (fun P hP s => by
      rw [← l1At_eq_l1Norm_map]
      exact Real.le_exp_of_log_le (hP.2 s))
    ω (hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)) hA rfl
  rw [card_LtN] at hR hb
  refine ⟨_, fun i => b i, fun i => (hI _).1 (b i).2, fun P hP => ?_, hR, fun i σ => ?_⟩
  · refine ⟨b.repr ⟨P, (hI P).2 hP⟩, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨P, (hI P).2 hP⟩)
    simp only [Int.cast_smul_eq_zsmul]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    exact h.symm
  · rw [l1At_eq_l1Norm_map]
    refine (hb i σ).trans ((bound_le_exp (L := L) i.pos Module.finrank_pos
      (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero c.F)) hR h3).trans (le_of_eq ?_))
    congr 1
    push_cast
    ring

end GlobalTheory.HarmBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrConjugateUnit
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem inPsi_or_conjugate_unit {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  first
  | exact @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | (apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate ..)

theorem gaStar_conj_eq_letAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (ga : Matrix (Fin n) (Fin n) E) (h : IsUnit ga.det), ga.conjTranspose * ga = 1 → gaStar (Dw := Dw) c (ga.map (IsCMField.complexConj E)) = letAct Dw pl c.F (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) := by
  intro E _ _ _ H Dw n Ix _ pl hpl _ l c ga h hU
  have hval : ((Matrix.nonsingInvUnit ga h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ga := rfl
  have hinv : (((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
      = ga.conjTranspose := by
    rw [Matrix.coe_units_inv, hval]
    exact Matrix.inv_eq_left_inv hU
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, b⟩
  simp only [Formalism.L2.Pj.gaStar, letAct, aeval_X, letB]
  split_ifs with h1 h2
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h1.choose :
        Matrix (Fin n) (Fin n) c.F) j b = embF c (pl h1.choose)
          ((((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b j) := rfl
    rw [e, hinv, h1.choose_spec]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h2.choose)⁻¹ : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F) b j = embF c (pl h2.choose) (ga j b) := rfl
    rw [e]
    apply Subtype.ext
    change τ (IsCMField.complexConj E (ga j b)) = pl h2.choose (ga j b)
    have hs := h2.choose_spec
    generalize h2.choose = t at hs ⊢
    subst hs
    rw [IsCMField.complexEmbedding_complexConj]
    simp
  · exfalso
    rcases inPsi_or_conjugate_unit H τ with h3 | h3
    · exact h1 ((hpl.2 τ).1 h3)
    · obtain ⟨t, ht⟩ := (hpl.2 _).1 h3
      exact h2 ⟨t, by rw [ht]; ext x; simp⟩

end GlobalTheory.FrameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsNabTwist
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem isNab_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → IsNab Xo c (fun {S} _ _ y k F α => (nab (twPt h y) k F α).val) := by
  intro E _ _ _ H Dw l Xo c ta h _ nab hn
  refine ⟨hn.1, fun S _ _ iQ y => ?_⟩
  letI : Algebra ℚ (Tw ta S) := iQ
  obtain ⟨C, h1, h2⟩ := hn.2 (Tw ta S) (twPt h y)
  exact ⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩,
    ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩

end GlobalTheory.GalTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneous
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

section

open GlobalTheory.LevelPairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_zetaM_pow (c : Coeff l) (ta : c.F ≃+* c.F) :
    ∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M] := by
  have h3 := l.three_le
  haveI : NeZero l.M := ⟨by omega⟩
  have hp := zetaM_prim c
  have hp' : IsPrimitiveRoot (ta (zetaM c)) l.M := hp.map_of_injective ta.injective
  obtain ⟨a, -, ha⟩ := hp.eq_pow_of_pow_eq_one hp'.pow_eq_one
  have hco : a.Coprime l.M := (hp.pow_iff_coprime (by omega) a).1 (ha ▸ hp')
  obtain ⟨a', -, h⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
  refine ⟨a, a', ha.symm, ?_⟩
  unfold Nat.ModEq
  rw [h, Nat.mod_eq_of_lt (by omega)]

theorem mk_qRep {K : Submodule (𝓞 E) Dw.La} (x : Dw.La ⧸ K) : (Submodule.Quotient.mk (qRep x) : Dw.La ⧸ K) = x :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ x)

theorem level_nsmul (x : LevQc Dw l) : l.M • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    rw [Mfr, l.prod]; exact Ideal.mem_span_singleton_self _
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Submodule.mem_inf.1 (Ideal.mul_le_inf h)).2 Submodule.mem_top

theorem nsmul_nsmul_of_modEq {n a a' : ℕ} (h : a * a' ≡ 1 [MOD l.M]) (x : Fin n → LevQc Dw l) :
    a • a' • x = x := by
  have h3 := l.three_le
  have hM : l.M • x = 0 := funext fun b => level_nsmul (x b)
  have e : a * a' = l.M * (a * a' / l.M) + 1 := by
    have := Nat.div_add_mod (a * a') l.M
    rw [h, Nat.mod_eq_of_lt (show 1 < l.M by omega)] at this
    exact this.symm
  rw [← mul_smul, e, add_smul, one_smul, mul_comm, mul_smul, hM, smul_zero, zero_add]

theorem pairL_nsmul {n : ℕ} (a : ℕ) (x : Fin n → LevQc Dw l) (y : Fin n → Dw.La) :
    (l.M : ℤ) ∣ (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y -
      pairL (l := l) (fun b => qRep ((a • x) b)) y := by
  have e : (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y = pairL (l := l) (fun b => a • qRep (x b)) y := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  rw [e]
  refine pairL_congr _ _ _ _ (fun b => ?_) (fun b => by simp)
  rw [← Submodule.Quotient.eq, mk_qRep, ← Nat.cast_smul_eq_nsmul (𝓞 E), Submodule.Quotient.mk_smul, mk_qRep,
    Nat.cast_smul_eq_nsmul]
  rfl

theorem map_phiHat (c : Coeff l) {n : ℕ} (ta : c.F ≃+* c.F) {a a' : ℕ} (ha : ta (zetaM c) = zetaM c ^ a)
    (h : a * a' ≡ 1 [MOD l.M]) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q := by
  have h' : a' * a ≡ 1 [MOD l.M] := mul_comm a a' ▸ h
  let e : (Fin n → LevQc Dw l) ≃ (Fin n → LevQc Dw l) :=
    ⟨fun x => a • x, fun x => a' • x, nsmul_nsmul_of_modEq h', nsmul_nsmul_of_modEq h⟩
  unfold phiHat
  refine (ta.toAddEquiv.map_finsum _).trans (Eq.trans (finsum_congr fun x => ?_) (finsum_comp_equiv e))
  change ta _ = ta (φ (a' • a • x)) * zetaM c ^ pairL (l := l) (fun b => qRep ((a • x) b)) _
  rw [nsmul_nsmul_of_modEq h', map_mul, map_zpow₀, ha, ← zpow_natCast, ← zpow_mul,
    zpow_congr c (pairL_nsmul a x _)]

theorem phiHat_mul (c : Coeff l) {n : ℕ} (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    phiHat c (fun x => u * φ x) q = u * phiHat c φ q := by
  unfold phiHat
  rw [← smul_eq_mul u, smul_finsum]
  refine finsum_congr fun x => ?_
  rw [smul_eq_mul, mul_assoc]

theorem shortValAt_mul {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (nab : NabV Xo c)
    (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (h : ShortValAt Xo c nab w Λ b N P y v) :
    ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, h7, AlgHom.commutes, mul_left_comm]
  congr 1
  rw [← Algebra.smul_def, smul_finsum]
  refine finsum_congr fun q => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc]

end

theorem phiHat_aut_and_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  intro E _ _ _ H Dw l Xo c n
  exact ⟨fun ta => ⟨exists_zetaM_pow c ta, fun _ _ ha h φ q => map_phiHat c ta ha h φ q⟩,
    fun u φ q => phiHat_mul c u φ q,
    fun nab w Λ b u N P S _ _ y v h => shortValAt_mul nab w Λ b u N P S y v h⟩

end GlobalTheory.GalTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_shift_halfTorsion_root : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0))) (t u z : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), t ^ (N ^ 2) = 1 → u ^ (N ^ 2) = 1 → z ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) t u 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) u z e → ∀ F F', IsUUOver Xo.univ.t.G Xo.univ.t.PP N s z (t * u) F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (u * z) t F' → ∃ r : B, (toΓ B r) ^ 2 = (e : Γ((ptO Xo x0).left, ⊤)) ∧ r ^ (N ^ 2) = 1 ∧ ∀ j, F.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x0) (toΓ B r) * F'.f j := by
  first | exact @GlobalTheory.isUUOver_shift | exact GlobalTheory.isUUOver_shift | (intros; apply GlobalTheory.isUUOver_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem thExpr_tmul_lemma (hL : Laws) (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [StarRing (𝓞 E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n)
    {S1 : Type} [CommRing S1] [Algebra c.F S1] [Algebra S S1] (φ1 : S →ₐ[c.F] S1)
    (hφ1 : ∀ s, φ1 s = algebraMap S S1 s) (y1 : FrPt Xo c S1)
    (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x)))
    (h1 : FrMap φ1 y y1)
    (hF1 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s
      (levPt Xo y1.x (x b)) (F1 b))
    {S2 : Type} [CommRing S2] [Algebra c.F S2] [Algebra S S2] (φ2 : S →ₐ[c.F] S2)
    (hφ2 : ∀ s, φ2 s = algebraMap S S2 s) (y2 : FrPt Xo c S2)
    (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x)))
    (h2 : FrMap φ2 y y2)
    (hF2 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s
      (levPt Xo y2.x (x b)) (F2 b)) :
    TensorProduct.tmul S (thExpr Xo c nab y1 P F1) (1 : S2) =
      TensorProduct.tmul S (1 : S1) (thExpr Xo c nab y2 P F2) := by
  letI : Algebra c.F (TensorProduct S S1 S2) :=
    ((algebraMap S (TensorProduct S S1 S2)).comp (algebraMap c.F S)).toAlgebra
  let χ1 : S1 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeLeft
  let χ2 : S2 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeRight

  let ψ1 : S1 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ1.toRingHom with
      commutes' := fun r => by
        show χ1 (algebraMap c.F S1 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ1.commutes r, hφ1]
        exact χ1.commutes _ }
  let ψ2 : S2 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ2.toRingHom with
      commutes' := fun r => by
        show χ2 (algebraMap c.F S2 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ2.commutes r, hφ2]
        exact χ2.commutes _ }
  have hcomp : ψ1.comp φ1 = ψ2.comp φ2 := by
    ext s
    show χ1 (φ1 s) = χ2 (φ2 s)
    rw [hφ1, hφ2, χ1.commutes, χ2.commutes]
  exact _root_.GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y a n x P hP S1 φ1 y1 F1 S2 φ2 y2 F2 h1 hF1 h2 hF2
    (TensorProduct S S1 S2) ψ1 ψ2 hcomp

theorem thValTot_of_chartIndep : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP

  obtain ⟨S', _, _, φ, y', F, hff, hy', hF⟩ := _root_.GlobalTheory.exists_faithfullyFlat_isVtOver hL E H Dw l Xo c S y n x
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := hff
  have hφ : ∀ s, φ s = algebraMap S S' s := fun _ => rfl

  have htmul := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ hφ y' F hy' hF
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' (thExpr Xo c nab y' P F)).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, htmul, sub_self])
  refine ⟨v, ⟨S', inferInstance, inferInstance, φ, y', F, hff, hy', hF, hv⟩, ?_⟩

  rintro w ⟨S2, _, _, φ2, y2, F2, hff2, hy2, hF2, hw⟩
  letI : Algebra S S2 := φ2.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S2 := hff2
  have h12 := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ2 (fun _ => rfl) y2 F2 hy2 hF2
  have hv' : φ v = thExpr Xo c nab y' P F := hv
  rw [← hv', ← hw, hφ, Algebra.TensorProduct.tmul_one_eq_one_tmul] at h12
  have h3 : algebraMap S S2 v = algebraMap S S2 w :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := S') S2 h12
  exact (FaithfulSMul.algebraMap_injective S S2 h3).symm

end GlobalTheory
end

