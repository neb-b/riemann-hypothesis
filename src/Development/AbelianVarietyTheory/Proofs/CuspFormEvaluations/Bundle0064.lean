module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

noncomputable section

namespace GlobalTheory.Shares.WtDic

variable {D : D7}

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_conjEmb {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun x => by simp [conjEmb]

theorem tauEmb_ne_conj (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_tau {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj, this]
  · simp

theorem wtA_conj {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [(tauEmb_ne_conj _ _).symm]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h => ht' (tauEmb_inj (by
      have := congrArg conjEmb h
      rwa [conjEmb_conjEmb, conjEmb_conjEmb] at this)).symm
    simp [(tauEmb_ne_conj _ _).symm, this]
  · simp

theorem matrixExtendByZero_mul {p : ℕ} (c : ℕ) (f : Fin p → ℕ) (i : ℕ) : ext0 (fun k => c * f k) i = c * ext0 f i := by
  unfold ext0; split_ifs <;> rfl

theorem wtA_wsmul {j : ℕ} (c : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (wsmul c w) x = c * wtA w x := by
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((wsmul c w).aP t) x.2 = c * ext0 (w.aP t) x.2 := matrixExtendByZero_mul _ _ _
  have h2 : ext0 ((wsmul c w).aM t) x.2 = c * ext0 (w.aM t) x.2 := matrixExtendByZero_mul _ _ _
  rw [h1, h2]
  split_ifs <;> ring

theorem wtA_wscalar (j n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp only [wtA]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h1 : ext0 ((wscalar D j n hn).aP t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  have h2 : ext0 ((wscalar D j n hn).aM t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  rw [h1, h2]
  simp

theorem laR_wadd (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (u u' : WeightFamilies.Wt D j) :
    laR T j (wadd u u') k = laR T j u k + laR T j u' k := by
  funext τ a
  have hn : (wadd u u').n / 2 = u.n / 2 + u'.n / 2 := by
    have h1 := u.n_even
    have h2 := u'.n_even
    rw [n_wadd]
    rw [Nat.even_iff] at h1 h2
    omega
  simp only [laR, laU, Pi.add_apply, wtA_wadd, hn]
  split_ifs <;> push_cast <;> ring

theorem laR_wsmul (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (m : ℕ) (u : WeightFamilies.Wt D j) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  funext τ a
  have hn : (wsmul m u).n / 2 = m * (u.n / 2) := by
    obtain ⟨s, hs⟩ := u.n_even
    show m * u.n / 2 = _
    rw [hs, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  simp only [laR, laU, Pi.smul_apply, wtA_wsmul, hn, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem card_lower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem choose_split (p q : ℕ) : (p + q) * (p + q - 1) / 2 = p * q + p * (p - 1) / 2 + q * (q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem weights_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  intro D T h j hj k
  obtain ⟨hr, hk, -⟩ := h.unf j hj T.σ₀ T.good_σ₀
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  have hc : Fintype.card ((T.U j T.σ₀).X k).Ψ = D.R.f := by
    have h1 := GlobalTheory.RunIn.WtSize.two_mul_card_cm ((T.U j T.σ₀).X k)
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq D] at h1
    omega
  refine ⟨laR_wadd T j k, laR_wsmul T j k, fun u v m => ?_, fun i => ?_, ?_, hp0.trans hq, ?_, ?_⟩
  · rw [addL, laR_wadd, laR_wsmul]
  · funext τ a
    have hn : (etWt D j i).n / 2 = i * (g0 D / 2) := by
      show g0 D * i / 2 = _
      unfold g0
      rw [mul_assoc 2, mul_assoc 2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, mul_comm]
    have hw : ∀ x, wtA (etWt D j i) x = 0 := wtA_wscalar _ _ _
    simp only [laR, laU, Pi.smul_apply, hw, hn, nsmul_eq_mul, de2W]
    split_ifs <;> simp
  · rw [nd, Fintype.card_prod, hc, card_lower, WeightFamilies.dimY, ← choose_split, hr, hp, hq]
  · rw [← hc, Fintype.card_coe]
  · let f : D.what₂.Tau → ((T.U j T.σ₀).X k).Ψ := fun t => ⟨DV.tauEmb D t, (hΨ _).2 (h.pins.1.2.2.2 t)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun t t' e => tauEmb_inj (congrArg Subtype.val e), fun τ => ?_⟩
      obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 τ.1 ((hΨ _).1 τ.2)
      exact ⟨t, Subtype.ext ht.symm⟩
    have hinv : ∀ τ, Function.invFun (relab T.Q.c T.σ₀) τ = τ := fun τ =>
      Function.leftInverse_invFun (GlobalTheory.RunIn.WtSize.relab_bijective T.Q.c T.σ₀).1 τ
    refine ⟨(Equiv.ofBijective f hf).symm, fun u τ a => ?_⟩
    obtain ⟨t, rfl⟩ := (Equiv.ofBijective f hf).surjective τ
    rw [Equiv.symm_apply_apply]
    have e : ((Equiv.ofBijective f hf) t).1 = DV.tauEmb D t := rfl
    simp only [laR, laU, hinv, e, wtA_tau, wtA_conj]

end GlobalTheory.Shares.WtDic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjHalfIntegralGenerator
section
namespace GlobalTheory.CMConjugationOfSquareRoot

open NumberField Complex
open scoped ComplexConjugate

theorem conj_eq_neg_of_sq_eq_neg {z : ℂ} {d : ℝ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    conj z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h0 | h0
    · exact h0
    · rw [h0] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre0]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem complexConj_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E ((H.rt : 𝓞 E) : E) = -((H.rt : 𝓞 E) : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq_eq_neg (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
  simpa using h

theorem conj_halfIntegralGenerator (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc ((H.w0 : 𝓞 E) : E) = (1 : E) - ((H.w0 : 𝓞 E) : E) := by
  have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    push_cast at this
    exact this
  have h3 : (2 : E) * IsCMField.complexConj E (H.w0 : E) = 1 - (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add (f := _), map_one, complexConj_rt] at this
    have h22 : IsCMField.complexConj E (2 : E) = 2 := map_ofNat _ 2
    rw [h22] at this
    rw [this]; ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.cc
  apply mul_left_cancel₀ (two_ne_zero : (2 : E) ≠ 0)
  rw [h3, mul_sub, h2]; ring

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ReciprocityTheory.ChartRestriction.G.FD.cc (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) = (1 : E) - (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) := fun H => conj_halfIntegralGenerator H

end GlobalTheory.CMConjugationOfSquareRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
open MeasureTheory

namespace GlobalTheory.GenericFlat

theorem ae_cast {a b n m : ℕ} (hab : a = b) (hnm : n = m) (P : (Fin (a + 1) × Fin n → ℂ) → Prop)
    (hP : ∀ᵐ t : Fin (a + 1) × Fin n → ℂ, P t) :
    ∀ᵐ t : Fin (b + 1) × Fin m → ℂ,
      P fun p => t (Fin.cast (congrArg (· + 1) hab) p.1, Fin.cast hnm p.2) := by
  subst hab hnm
  simpa using hP

theorem exists_generic_flatAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  intro D T h j _hj N wL wF w Tn c1 A
  have hC : Countable T.Q.c.F := (Module.finBasis ℚ T.Q.c.F).equivFun.injective.countable

  have hk : ∀ k : (T.U j T.σ₀).Comp, ∀ᵐ t : Fin (WeightFamilies.dimY D j + 1) × Fin N → ℂ,
      ∃ Fl : FlatM ((T.U j T.σ₀).X k) (A.Xa k),
        (∀ x, Fl.w0 x = ∑ i, t (0, i) * rdR h j (w i) k x) ∧
        ∀ a x, Fl.s a x = ∑ i, t ((Fin.cast (A.dim k) a).succ, i) * rdR h j (w i) k x := by
    intro k
    have H := _root_.GlobalTheory.GenericFlat.ae_exists_flat _ _ ((T.U j T.σ₀).X k) (A.Xa k) T.Q.c.F T.σ₀ (A.rel k)
    refine (ae_cast (A.dim k) (A.hN k) _ H).mono ?_
    rintro t ⟨Fl, h0, hs⟩
    refine ⟨Fl, fun x => ?_, fun a x => ?_⟩
    · rw [h0]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2
    · rw [hs]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2

  have hall := (ae_all_iff.2 hk).and
    (GlobalTheory.ae_eval₂_ne_zero_of_countable T.Q.c.F T.σ₀ (Fin (WeightFamilies.dimY D j + 1) × Fin N))
  obtain ⟨t, ht, hg⟩ := hall.exists
  choose Fl h0 hs using ht
  exact ⟨t, hg, ⟨⟨Fl, h0, hs⟩⟩⟩

end GlobalTheory.GenericFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAuxiliaryWeightsAtRunWeights
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.AuxiliaryWeightsExistence

theorem antitone_nonneg_of_gaps {p : ℕ} (g : Fin p → ℤ)
    (hg : ∀ (i : Fin p) (h : i.1 + 1 < p), g ⟨i.1 + 1, h⟩ ≤ g i)
    (hl : ∀ i : Fin p, i.1 + 1 = p → 0 ≤ g i) : Antitone g ∧ ∀ i, 0 ≤ g i := by

  have walk : ∀ k : ℕ, ∀ i j : Fin p, j.1 = i.1 + k → g j ≤ g i := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : j = i := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro i j hij
      have hm : i.1 + k < p := by have := j.2; omega
      have hstep := hg ⟨i.1 + k, hm⟩ (by have := j.2; simp only; omega)
      have hj : (⟨i.1 + k + 1, by have := j.2; omega⟩ : Fin p) = j := Fin.ext (by simp only; omega)
      rw [hj] at hstep
      exact le_trans hstep (ih i ⟨i.1 + k, hm⟩ rfl)
  refine ⟨fun i j hij => walk (j.1 - i.1) i j (by have : i.1 ≤ j.1 := hij; omega), fun i => ?_⟩
  have hp : p - 1 < p := by have := i.2; omega
  exact le_trans (hl ⟨p - 1, hp⟩ (by simp only; have := i.2; omega))
    (walk (p - 1 - i.1) i ⟨p - 1, hp⟩ (by simp only; have := i.2; omega))

theorem gap_key (c cL T' r : ℤ) (hT : 0 < T') (hr : 0 ≤ r) (hc : T' * (T' + 2 * r) ≤ c + 2)
    (hL : cL = Int.fdiv (c + 2) T') : c ≤ (T' + 2) * cL := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT.le] at hL
  have hdm := Int.mul_ediv_add_emod (c + 2) T'
  have hlt := Int.emod_lt_of_pos (c + 2) hT
  have hge := Int.emod_nonneg (c + 2) hT.ne'
  rw [← hL] at hdm

  have hq : T' + 2 * r ≤ cL := by
    by_contra hcon
    rw [not_le] at hcon
    have : T' * (cL + 1) ≤ T' * (T' + 2 * r) := by
      apply mul_le_mul_of_nonneg_left _ hT.le; omega
    nlinarith
  nlinarith

theorem exists_block {p : ℕ} (a l f : Fin p → ℕ) (T Dm r T' : ℕ) (hT' : T' = T + Dm + 2)
    (hf : ∀ i, (f i : ℤ) = a i - T * l i)
    (hgap : ∀ i : Fin p, i.1 + 1 < p → ((T' * (T' + 2 * r) : ℕ) : ℤ) ≤ gapZ a i + 2)
    (hL : ∀ i : Fin p, i.1 + 1 < p → gapZ l i = Int.fdiv (gapZ a i + 2) T')
    (hlast : ∀ i : Fin p, i.1 + 1 = p → (a i : ℤ) ≤ ((T : ℤ) + Dm + 4) * l i) :
    ∃ w : Fin p → ℕ, Antitone w ∧ ∀ i, w i + f i = (Dm + 4) * l i := by

  have hT'z : (T' : ℤ) = T + Dm + 2 := by rw [hT']; push_cast; ring
  have hg := antitone_nonneg_of_gaps (fun i => ((T : ℤ) + Dm + 4) * l i - a i) ?_ ?_
  · refine ⟨fun i => (((T : ℤ) + Dm + 4) * l i - a i).toNat,
      fun i j hij => Int.toNat_le_toNat (hg.1 hij), fun i => ?_⟩
    have h0 := hg.2 i
    have hfi := hf i
    dsimp only at h0 ⊢
    zify
    rw [Int.toNat_of_nonneg h0]
    linarith
  · intro i h
    have hk := gap_key (gapZ a i) (gapZ l i) T' r (by omega) (by positivity)
      (by exact_mod_cast hgap i h) (hL i h)
    unfold gapZ at hk
    rw [dite_eq_left h, dite_eq_left h, hT'z] at hk
    nlinarith
  · intro i h
    have := hlast i h
    linarith

private theorem le_mul_fdiv_sub_of_sq_le (a c T Dm : ℤ) (hD : 0 ≤ Dm) (h40 : 40 * (Dm + 2) ≤ T)
    (hc : c ≤ T) (ha : 2 * T ^ 2 ≤ a) :
    a ≤ (T + Dm + 4) * Int.fdiv (a - c) (T + Dm + 2) := by
  have hT : 0 < T + Dm + 2 := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT.le]
  have hdm := Int.mul_ediv_add_emod (a - c) (T + Dm + 2)
  have hlt := Int.emod_lt_of_pos (a - c) hT
  have hge := Int.emod_nonneg (a - c) hT.ne'
  set q := (a - c) / (T + Dm + 2) with hq
  set m := (a - c) % (T + Dm + 2) with hm

  have h2q : c + T + Dm + 2 ≤ 2 * q := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (T + Dm + 2) * (2 * q) ≤ (T + Dm + 2) * (2 * T + Dm + 1) := by
      apply mul_le_mul_of_nonneg_left _ hT.le
      omega
    have hT0 : (0 : ℤ) ≤ T := by omega
    nlinarith [mul_le_mul_of_nonneg_right h40 hT0, mul_le_mul_of_nonneg_right h40 hD,
      mul_nonneg hD hT0, mul_nonneg hD hD]
  nlinarith

theorem exists_auxiliaryWeights_at_runWeights : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 →
      (∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2) ∧ ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, hgP, hgM, hh0, -, hlP, hlM, -, hnP, -, hPW, -, -, -, hL, hF, -, -, -, h40, hcT, h40W,
    -, -, -, -⟩ := hS
  obtain ⟨hLn, hLP, hLM⟩ := hL
  obtain ⟨hFn, hFP, hFM⟩ := hF
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = Tn + WeightFamilies.dimY D j + 2 := by unfold Tp; push_cast; ring
  have h40z : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40

  have hbigP : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      2 * (Tn : ℤ) ^ 2 ≤ ka.aP τ i := by
    intro τ i hi
    have h1 := hlP τ i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ ka.aP τ i := by linarith
    exact_mod_cast h2
  have hbigM : ∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
      2 * (Tn : ℤ) ^ 2 ≤ ka.aM τ i := by
    intro τ i hi
    have h1 := hlM τ i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ ka.aM τ i := by linarith
    exact_mod_cast h2

  have blockP : ∀ τ, ∃ w : Fin (D.R.sigW j).1 → ℕ, Antitone w ∧
      ∀ i, w i + wF.aP τ i = (WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ
    refine exists_block (ka.aP τ) (wL.aP τ) (wF.aP τ) Tn (WeightFamilies.dimY D j) D.R.r (Tp D j Tn) rfl
      (hFP τ) (hgP τ) ?_ ?_
    · intro i hi
      have hl := hLP τ i
      rw [if_pos hi] at hl
      exact hl
    · intro i hi
      have hn : ¬ (i.1 + 1 < (D.R.sigW j).1) := by omega
      have hl := hLP τ i
      rw [if_neg hn] at hl
      unfold gapZ at hl
      rw [dite_eq_right hn] at hl
      have hk := le_mul_fdiv_sub_of_sq_le (ka.aP τ i) (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) Tn
        (WeightFamilies.dimY D j) (by positivity) h40z (by exact_mod_cast hcT) (hbigP τ i hi)
      have e : (ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r =
          ka.aP τ i - (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) := by ring
      rw [hl, e, hTp]
      exact hk
  have blockM : ∀ τ, ∃ w : Fin (D.R.sigW j).2 → ℕ, Antitone w ∧
      ∀ i, w i + wF.aM τ i = (WeightFamilies.dimY D j + 4) * wL.aM τ i := by
    intro τ
    refine exists_block (ka.aM τ) (wL.aM τ) (wF.aM τ) Tn (WeightFamilies.dimY D j) D.R.r (Tp D j Tn) rfl
      (hFM τ) (hgM τ) ?_ ?_
    · intro i hi
      have hl := hLM τ i
      rw [if_pos hi] at hl
      exact hl
    · intro i hi
      have hn : ¬ (i.1 + 1 < (D.R.sigW j).2) := by omega
      have hl := hLM τ i
      rw [if_neg hn] at hl
      unfold gapZ at hl
      rw [dite_eq_right hn] at hl
      have hk := le_mul_fdiv_sub_of_sq_le (ka.aM τ i) 0 Tn (WeightFamilies.dimY D j) (by positivity) h40z
        (by positivity) (hbigM τ i hi)
      rw [sub_zero] at hk
      rw [hl, hTp]
      exact hk
  choose bP hbPa hbPs using blockP
  choose bM hbMa hbMs using blockM
  have hnW : Even nW := hLn ▸ wL.n_even
  have hle : nP ≤ (WeightFamilies.dimY D j + 4) * nW := le_trans hPW (by nlinarith)
  have hn2 : Even ((WeightFamilies.dimY D j + 4) * nW - nP) :=
    (Nat.even_sub hle).2 ⟨fun _ => hnP, fun _ => hnW.mul_left _⟩
  have hP2 : ∀ τ, Antitone (fun i => 2 * wL.aP τ i) := fun τ a b h => by
    have := wL.aPlus_antitone τ h
    dsimp only
    omega
  have hM2 : ∀ τ, Antitone (fun i => 2 * wL.aM τ i) := fun τ a b h => by
    have := wL.aM_anti τ h
    dsimp only
    omega
  have hn1 : Even (2 * nW - 2) := ⟨nW - 1, by omega⟩
  refine ⟨⟨(⟨bP, bM, hbPa, hbMa, (WeightFamilies.dimY D j + 4) * nW - nP, hn2⟩ : WeightFamilies.Wt D j), ?_, hbPs, hbMs⟩,
    ⟨(⟨fun τ i => 2 * wL.aP τ i, fun τ i => 2 * wL.aM τ i, hP2, hM2, 2 * nW - 2, hn1⟩ : WeightFamilies.Wt D j),
      ?_, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · show (WeightFamilies.dimY D j + 4) * nW - nP + wF.n = (WeightFamilies.dimY D j + 4) * wL.n
    rw [hFn, hLn]
    exact Nat.sub_add_cancel hle
  · show 2 * nW - 2 + 2 = 2 * nW
    omega

end GlobalTheory.AuxiliaryWeightsExistence
end
end

