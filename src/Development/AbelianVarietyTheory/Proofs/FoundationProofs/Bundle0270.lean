module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.MovedIdx

theorem common_denom {A ι : Type} [CommRing A] [Fintype ι] (S : Subring A) (f : ι → A) (P : ℕ → Prop) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (h : ∀ i, ∃ n : ℕ, P n ∧ (n : A) * f i ∈ S) :
    ∃ n : ℕ, P n ∧ ∀ i, (n : A) * f i ∈ S := by
  choose n hn hf using h
  refine ⟨∏ i, n i, Finset.prod_induction _ P hm h1 fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_comm (n i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem S c) (hf i)

theorem dvd_of_dvd_idx {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (A B : Submodule R X) (n q : ℕ)
    (hq : q.Prime) (h0 : idx A B ≠ 0) (hn : ∀ x ∈ B, n • x ∈ A) (hd : q ∣ idx A B) : q ∣ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) q hd
  rw [← hx, addOrderOf_dvd_iff_nsmul_eq_zero]
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hn y.1 y.2

theorem denom_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ∃ n : ℕ, n.Coprime q ∧ (n : AE D) * (y * x) ∈ OhE D := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, -, hmq, s, hs, h⟩ := hx a
  refine ⟨m * n', Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, ?_⟩
  convert mul_mem hs hy using 1
  push_cast
  linear_combination (n' : AE D) * y * h

theorem one_entry_mem (D : D7) {N : ℕ} (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem denom_triv (D : D7) {q N : ℕ} {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * (g : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2)
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (by
      rintro ⟨i, j⟩
      obtain ⟨m, -, hm, s, hs, e⟩ := hg i j 0
      refine ⟨m, hm, ?_⟩
      convert add_mem hs (mul_mem (natCast_mem _ m) (one_entry_mem D i j)) using 1
      linear_combination e)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem denom_triv_inv (D : D7) {q N : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N × Fin N =>
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2.1 *
      ((g : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2))
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (fun p => denom_mul D hq (hg _ _) _)
  refine ⟨n, hn, fun i j => ?_⟩
  have e : ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      1 - ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * ((g : Matrix (Fin N) (Fin N) (AE D)) - 1) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, sub_sub_cancel]
  rw [e, Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum]
  exact sub_mem (mul_mem (natCast_mem _ n) (one_entry_mem D i j)) (sum_mem fun l _ => h (i, l, j))

theorem denom_mat (D : D7) {N : ℕ} (M : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : AE D) * M i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => M p.1 p.2)
    (fun n => 0 < n) one_pos (fun a b => Nat.mul_pos) (fun p => GlobalTheory.HeckeVal.exists_denom D _)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem nsmul_mem_latA (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (g : GA D N) (g' : GA D N') {n n' : ℕ}
    (h : ∀ i j, (n : AE D) * (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (h' : ∀ i j, (n' : AE D) * ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D) :
    ∀ ζ ∈ (latA D cc N N').map (actA D N N' (g, g')), (n * n') • ζ ∈ latA D cc N N' := by
  rintro _ ⟨ζ, hζ, rfl⟩ i j
  rw [actA_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  convert ihE_mul D cc (mul_mem (h l j) (h' i k)) (hζ k l) using 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.FinWeil.MovedIdx


open GlobalTheory.FinWeil.MovedIdx in
theorem GlobalTheory.FinWeil.idx_map_actA : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  intro D hD cc δ hC N N' g g'
  have h0 : idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 := by
    obtain ⟨n, hn, h⟩ := denom_mat D (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    obtain ⟨n', hn', h'⟩ := denom_mat D ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    exact _root_.GlobalTheory.FinWeil.idx_latA_ne_zero D hD cc δ hC N N' _ (Nat.mul_pos hn hn') _ (nsmul_mem_latA D cc g g' h h')
  refine ⟨h0, fun q hq hg hg' hd => ?_, fun hg hg' ζ hζ => ?_⟩
  · obtain ⟨n, hn, h⟩ := denom_triv_inv D hq hg
    obtain ⟨n', hn', h'⟩ := denom_triv D hg'
    exact (Nat.Prime.coprime_iff_not_dvd hq).1 (Nat.Coprime.mul_left hn hn').symm
      (dvd_of_dvd_idx _ _ _ q hq h0 (nsmul_mem_latA D cc g g' h h') hd)
  · have := nsmul_mem_latA D cc g g' (n := 1) (n' := 1) (fun i j => by simpa using (hg i j).2)
      (fun i j => by simpa using (hg' i j).1) ζ hζ
    simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitaryPos
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_gaussian_unitary_pos : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, 0 < κ ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos, fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => _root_.GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTriple

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem theta_cocycle_eq_exp_hermitian (T : Tor D) (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T (w0 D • x) y).im : ℂ)) := by
  have h : Hf D T (w0 D • x) y = w0 D * Hf D T x y := by
    rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  rw [bc, h, Complex.mul_im, h1, h2]
  congr 1
  push_cast
  ring

theorem nice_of_klat (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    Nice D (tor0 D cc δ) A := by
  obtain ⟨-, h0, h1, h2, -, -, -⟩ :=
    GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have hw := GlobalTheory.ThetaInter.klat_smul_mem hA a hx
    rw [ha] at hw
    obtain ⟨m, hm⟩ := h1 _ hw y hy
    rw [theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  · have h := hx y hy
    rw [bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination -hn
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h3

theorem index_ne_zero (hc : Crv D cc δ) {A₁ A₂ : AddSubgroup (VC D N N')} (h₁ : KLat D (tor0 D cc δ) A₁)
    (h₂ : KLat D (tor0 D cc δ) A₂) : (A₁.addSubgroupOf A₂).index ≠ 0 := by
  haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂
    (GlobalTheory.ThetaInter.klat_facts hc h₂).1
  exact AddSubgroup.index_ne_zero_of_finite

theorem iop_self {T : Tor D} {A : AddSubgroup (VC D N N')} (hA : Nice D T A) {e : VC D N N' → ℂ}
    (he : e ∈ ThSp D T A) : Iop D T A A e = e := by
  rw [hA.Iop_eq]
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1 := hi
  obtain ⟨hs, ⟨q₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hc
  rw [finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi,
    ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]
  simp

theorem klat_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  intro D cc δ hc N N'
  refine ⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂,
    fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he
  exact ⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂,
    index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩

end GlobalTheory.ThetaTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeDualSumWeylLatticesLe
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

private theorem selfDual_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  letI := hM.1
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨s, hs⟩ := hM.1.fg
  obtain ⟨d, hd, hden⟩ := GlobalTheory.DualLat.exists_den_finset
    (s.image (fun y => star y ⬝ᵥ (G *ᵥ x)))
  have hdx : d • x ∈ M := by
    rw [← hM.2]
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [Matrix.mulVec_smul, dotProduct_smul]
      exact hden _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz =>
      simpa [star_add, add_dotProduct] using add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨b, hb⟩ := Submodule.mem_one.mp (GlobalTheory.DualLat.star_mem_one
        (Submodule.mem_one.mpr ⟨a, rfl⟩ : (algebraMap (𝓞 K) K a) ∈ (1 : Submodule (𝓞 K) K)))
      have heq : star (a • y) = (algebraMap (𝓞 K) K b) • star y := by
        ext i
        change star (algebraMap (𝓞 K) K a * y i) = algebraMap (𝓞 K) K b * star (y i)
        rw [star_mul, hb, mul_comm]
      rw [heq, smul_dotProduct]
      exact Submodule.smul_mem (1 : Submodule (𝓞 K) K) b hy
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := fun h =>
    hd ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
  have hx := (Submodule.span K (M : Set (Fin n → K))).smul_mem
    (algebraMap (𝓞 K) K d)⁻¹ (Submodule.subset_span hdx)
  rwa [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hdK, one_smul] at hx

private theorem sumLat_full {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} [Fintype C]
    (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam)
    (T : C → Submodule (𝓞 K) (VV K lam))
    (hT : ∀ c, Submodule.IsFullLattice K (T c))
    (hL : Submodule.IsLattice K (sumLat lam e T)) :
    Submodule.IsFullLattice K (sumLat lam e T) := by
  classical
  letI := hL
  refine ⟨?_⟩
  let f := SumLat.valEquiv (K := K) lam e
  let g : C → VV K lam →ₗ[K] (Fin N → K) := fun c =>
    f.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : C => VV K lam) c
  have hval : ∀ c c' t, valAt lam e c' (g c t) = (Pi.single c t : C → VV K lam) c' := by
    intro c c' t
    exact congrFun (f.apply_symm_apply (Pi.single c t : C → VV K lam)) c'
  have hmem : ∀ c t, t ∈ T c → g c t ∈ sumLat lam e T := by
    intro c t ht
    rw [Model.mem_sumLat]
    intro c'
    rw [hval]
    by_cases hc : c' = c
    · subst hc; simpa using ht
    · simp [hc]
  have key : ∀ c t, t ∈ Submodule.span K (T c : Set (VV K lam)) →
      g c t ∈ Submodule.span K (sumLat lam e T : Set (Fin N → K)) := by
    intro c t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span (hmem c t ht)
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
  apply eq_top_iff.mpr
  intro u _
  have hsum : ∑ c, g c (valAt lam e c u) = u := by
    apply f.injective
    rw [map_sum]
    have h : ∀ c, f (g c (valAt lam e c u)) =
        Pi.single c (valAt lam e c u) := fun c => f.apply_symm_apply _
    simp only [h]
    exact Finset.univ_sum_single (fun c => valAt lam e c u)
  rw [← hsum]
  apply Submodule.sum_mem
  intro c _
  apply key
  rw [(hT c).span_eq_top]
  trivial

theorem testLatticeCondition_dualFr_sumLat_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  have hGh : ∀ τ, (G τ)ᴴ = G τ := fun τ => (hG τ).1
  have hMfull : ∀ c τ, Submodule.IsFullLattice K (M c τ) := fun c τ => selfDual_full _ _ (hM c τ)
  have hdel : ∀ c, Submodule.IsFullLattice K (delK lam (M c)) := fun c =>
    (_root_.GlobalTheory.TransLattice.nabDelLattice K ι n lam (M c) (hMfull c)).2
  obtain ⟨hlat, hN, hdual⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e (fun c => delK lam (M c)) (fun c => (hdel c).toIsLattice)
  haveI : Finite C := by
    let i₀ : VVIdx lam := (e ⟨0, hN⟩).2
    refine Finite.of_injective (fun c : C => e.symm (c, i₀)) ?_
    intro a b hab
    exact (Prod.ext_iff.1 (e.symm.injective hab)).1
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨hval, hH, hHi, hGu⟩ := _root_.GlobalTheory.TestLat.sumGram_spec K ι n lam G hG C N e
  have hHu : IsUnit (sumGram lam e G).det := by
    have h1 := (hH.2.2 v₀.embedding).isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    have h2 : ((sumGram lam e G).map v₀.embedding).det = v₀.embedding (sumGram lam e G).det :=
      (RingHom.map_det v₀.embedding (sumGram lam e G)).symm
    rw [h2] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  have hnab : hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c))
      = sumLat lam e fun c => nabK lam (M c) := by
    rw [hdual G hGh]
    congr 1
    funext c
    rw [(_root_.GlobalTheory.TransDual.nabDelDual K ι n lam G (M c) hGh hGu (hMfull c)).2]
    congr 1
    funext τ
    exact (hM c τ).2
  obtain ⟨s, hs, hse, hsb⟩ := _root_.GlobalTheory.extNorm_eq_nat_log_le_bound K ι n lam R hR hsp
  have hint : ∀ x ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
      ∀ y ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
        (s : K) * (star x ⬝ᵥ sumGram lam e G *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx y hy
    rw [hnab] at hx hy
    rw [hval, Finset.mul_sum]
    refine Subring.sum_mem _ fun c _ => ?_
    rw [← hse]
    exact _root_.GlobalTheory.PairInt.extNorm_mul_pairK_integral K ι n lam G (M c) hGh hGu (hM c) _
      ((Submodule.mem_iInf _).1 hx c) _ ((Submodule.mem_iInf _).1 hy c)
  have hint' := dualForm_integral_on_dualFr K N (sumGram lam e G) hH.1 hHu _ s hint
  have hD := (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K N (sumGram lam e G) _ hHu (sumLat_full lam e _ hdel hlat)).1
  have hne : dualFr (sumLat lam e fun c => delK lam (M c)) ≠ ⊥ := by
    classical
    let i : Fin N := ⟨0, hN⟩
    obtain ⟨S, hS⟩ := hlat.fg
    obtain ⟨⟨d, hd⟩, hden⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 K)) (S.image (fun x => x i))
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hm : (Pi.single i (algebraMap (𝓞 K) K d) : Fin N → K) ∈
        dualFr (sumLat lam e fun c => delK lam (M c)) := by
      intro x hx
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        rw [single_dotProduct]
        exact Submodule.mem_one.2 (hden _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      | zero => simp
      | add x y _ _ hx hy => simpa [dotProduct_add] using add_mem hx hy
      | smul c x _ hx => simpa [dotProduct_smul] using Submodule.smul_mem (1 : Submodule (𝓞 K) K) c hx
    intro h0
    rw [h0, Submodule.mem_bot] at hm
    have := congrFun hm i
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hd0 (RingOfIntegers.coe_injective (by simpa using this))
  refine ⟨hD.fg, hne, fun v => (hX v).1, le_trans ?_ hsb⟩
  exact _root_.GlobalTheory.muMaxDef_le_log_of_integral K v₀ hv N _ X ⟨hHi.2.1, hX⟩ s hs _ hD.fg hne hint'

end GlobalTheory.TestLat
end

