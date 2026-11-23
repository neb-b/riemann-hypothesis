module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdOfMemSupport
section
noncomputable section

namespace GlobalTheory.KerRescale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

theorem card_eq_sum_colLen (μ : YoungDiagram) : μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have hmap : ∀ c ∈ μ.cells, c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (0, c.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl h1
    exact YoungDiagram.mem_iff_lt_rowLen.1 h2
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun c hc => hmap c hc),
    Fin.sum_univ_eq_sum_range (fun c => μ.colLen c)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

section Hom

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) {K : Type} [CommMonoid K] (a : Lt → K)

def wt : KM.XZ Lt N0 N1 → Additive K := Sum.elim (fun _ => 0) (fun z => Additive.ofMul (a z.1))

theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.minorXZ N0 N1 s p I) (p • Additive.ofMul (a s)) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (KM.XZ Lt N0 N1) ℤ) (Additive.ofMul (a s)) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold KM.minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => Additive.ofMul (a s))
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem Gxz_hom (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.Gxz N0 N1 nu I) (∑ s, (nu s).card • Additive.ofMul (a s)) := by
  unfold KM.Gxz
  refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun s _ => ?_
  rw [card_eq_sum_colLen, Finset.sum_smul]
  exact MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun c _ => minorXZ_hom N0 N1 a s _ (I s c)

theorem prod_of_mem_support (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) (μ : KM.XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (KM.Gxz N0 N1 nu I).support) :
    ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun z n => a z.1 ^ n) = ∏ s, a s ^ (nu s).card := by
  have h := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hμ' : μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
    ext x; cases x <;> simp
  rw [hμ', Finsupp.weight_apply, Finsupp.sum_sumElim] at h
  generalize Finsupp.sumFinsuppEquivProdFinsupp μ = p at h ⊢
  have h2 := congrArg Additive.toMul h
  unfold Finsupp.sum at h2
  simp only [Function.comp_apply, wt, Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero, zero_add, toMul_sum,
    toMul_nsmul, toMul_ofMul] at h2
  exact h2

end Hom

theorem applyAt0_rescale {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime] (a : Lt → ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    KM.applyAt0 N0 N1 l (MvPowerSeries.rescale (fun z => a z.1) Th) (KM.Gxz N0 N1 nu I) =
      (∏ s, a s ^ (nu s).card) • KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I) := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [MvPowerSeries.coeff_rescale, prod_of_mem_support N0 N1 a nu I μ hμ, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem rescale_atLin {σ κ : Type} [Finite σ] [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (a : κ → ℂ_[p])
    (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.rescale a (atLin c (fun j => MvPowerSeries.X j) F) =
      atLin (fun k j => a j * c k j) (fun j => MvPowerSeries.X j) F := by
  unfold atLin
  have hs : MvPowerSeries.HasSubst (fun k : σ => ∑ j : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k j) * MvPowerSeries.X j) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hs (MvPowerSeries.HasSubst.smul_X a)]
  congr 1
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.rescale_eq_subst, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← MvPowerSeries.rescaleAlgHom_apply, map_smul, MvPowerSeries.rescaleAlgHom_apply,
    MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_X (MvPowerSeries.HasSubst.smul_X a)]
  show c k j • (a j • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])) = (a j * c k j) • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])
  rw [mul_comm, mul_smul]

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D}
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem tauEmb_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (x : D.host.E) : ∃ y : D.what₂.LL, tauEmb D (P.lam w) τ x = P.iL w y := by
  have e : D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) = embT D τ x := RingHom.congr_fun D.embE_φ₀ _
  refine ⟨D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x), ?_⟩
  rw [P.iL_lam, e]
  rfl

def adUnit (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) : Cw D w :=
  if AdPl D w then (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ else 1

theorem norm_adUnit (hU : DgenUnitAd P O) (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) :
    ‖adUnit P O w u μ τ‖ = 1 := by
  unfold adUnit
  split_ifs with hw
  · rw [norm_inv, hU w hw u μ τ, inv_one]
  · exact norm_one

end GlobalTheory.KerRescale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.SobHS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_orthonormal_expansion {ι : Type} [Fintype ι] (f : ι → H) :
    ∃ (m : ℕ) (h : Fin m → H) (φ : ι → Fin m → ℂ), Orthonormal ℂ h ∧ (∀ j, f j = ∑ p, φ j p • h p) ∧
      ∀ j, ∑ p, ‖φ j p‖ ^ 2 = ‖f j‖ ^ 2 := by
  let U : Submodule ℂ H := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  let b := stdOrthonormalBasis ℂ U
  let u : ι → U := fun j => ⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨_, fun p => (b p : H), fun j p => ⟪b p, u j⟫_ℂ, b.orthonormal.comp_linearIsometry U.subtypeₗᵢ,
    fun j => ?_, fun j => b.sum_sq_norm_inner_right (u j)⟩
  have := congrArg Subtype.val (b.sum_repr' (u j))
  simpa using this.symm

theorem integral_sq_sum {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {μ : Measure (UJ ε)} {d : ℝ}
    (hd : IsFdeg μ σ d) {m : ℕ} {h : Fin m → H} (hh : Orthonormal ℂ h) (y : Fin m → H) :
    Integrable (fun g : UJ ε => ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2) μ ∧
      ∫ g : UJ ε, ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 ∂μ = (∑ p, ‖y p‖ ^ 2) / d := by
  have e : ∀ g : UJ ε, ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ∑ p, ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g) := by
    intro g
    rw [← Finset.sum_mul_sum, ← star_sum, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  have i1 : ∀ p, Integrable (fun g : UJ ε => ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g)) μ :=
    fun p => integrable_finsetSum _ fun q _ => (hd.2 _ _ _ _).1
  have i2 : Integrable (fun g : UJ ε => ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) μ := by
    simp only [e]
    exact integrable_finsetSum _ fun p _ => i1 p
  refine ⟨by simpa only [RCLike.re_to_complex, Complex.ofReal_re] using i2.re, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [e]
  rw [integral_finsetSum _ fun p _ => i1 p]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (hd.2 _ _ _ _).1]
  simp only [(hd.2 _ _ _ _).2, orthonormal_iff_ite.1 hh]
  rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
  simp [inner_self_eq_norm_sq_to_K]

theorem sobolev_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨S, C, hS, hC, H1⟩ := _root_.GlobalTheory.SobolevHaar.sobolev_at_one n ε
  obtain ⟨d, hd⟩ := hσ.2.2.2.1
  have hd0 := hd.1
  refine ⟨S, C * S.length / d, hS, by positivity, fun ι _ f x A hA hx hb => ?_⟩
  obtain ⟨m, h, φ, hh, hf, hφ⟩ := exists_orthonormal_expansion f
  let F : List (Mx n) → Mx n → ℂ := fun l g => ∑ j, ⟪f j, σ g (Dw σ l (x j))⟫_ℂ
  have eF : ∀ l g, F l g = ∑ p, ⟪h p, σ g (∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j))⟫_ℂ := by
    intro l g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_smul, inner_sum, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j, sum_inner]
    simp only [inner_smul_left]
  have hI := fun l => integral_sq_sum hd hh fun p => ∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j)
  simp only [← eF] at hI
  have key := H1 F (fun l _ => continuousOn_finsetSum _ fun j _ =>
      (innerSL ℂ (f j)).continuous.comp_continuousOn (hσ.1.2.2 _)) ?_ fun l _ => (hI l).1
  · have e1 : F [] 1 = ∑ j, ⟪f j, x j⟫_ℂ := by simp only [F, sigma_one hσ.1]; rfl
    rw [e1] at key
    refine key.trans ?_
    have h2 : (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum ≤
        (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).length • ((A * ∑ j, ‖f j‖ ^ 2) / d) := by
      refine List.sum_le_card_nsmul _ _ fun r hr => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      rw [(hI l).2]
      refine div_le_div_of_nonneg_right ?_ hd0.le
      refine (Finset.sum_le_sum fun p _ => hb l hl _).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [RCLike.norm_conj, hφ]
    rw [List.length_map, nsmul_eq_mul] at h2
    refine (mul_le_mul_of_nonneg_left h2 hC).trans (le_of_eq ?_)
    ring
  · intro l hl X hX g hg
    have e : ∀ t : ℝ, F l (g * NormedSpace.exp (t • X)) =
        ∑ j, ⟪f j, σ g (σ (NormedSpace.exp (t • X)) (Dw σ l (x j)))⟫_ℂ := fun t => by
      simp only [F, sigma_mul hσ.1 hg (exp_mem_UJ hX t)]
    simp only [e]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_orbit hσ.1 ((hx j).word hσ.1 hl) hX 0
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ.1] at h1
    exact (((innerSL ℂ (f j)).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1

end GlobalTheory.TypeSum.SobHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


variable (E) in
abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

theorem conjSrc_conjSrc_cm (v : HeightOneSpectrum (𝓞 E)) : conjSrc (conjE E) (conjSrc (conjE E) v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (conjE E) v ((conjE E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjPl_self_conjSrc (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ConjPl (conjE E) w (conjSrc (conjE E) w) := by
  have h := conjPl_conjSrc (conjE E) (conjSrc (conjE E) w)
  rwa [conjSrc_conjSrc_cm] at h

theorem over_split {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    conjSrc (conjE E) w ≠ w ∧
      (conjSrc (conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) →
        u = w ∨ u = conjSrc (conjE E) w := by
  have key := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w
  have h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE E) w u → u = conjSrc (conjE E) w := fun u h => by
    rw [eq_conjSrc h, conjSrc_conjSrc_cm]
  obtain ⟨u, hu, hu'⟩ := hw
  refine ⟨?_, (key _).2 (Or.inr (conjPl_self_conjSrc w)), fun u' h => ((key u').1 h).imp_right (h2 u')⟩
  rcases (key u).1 hu' with h | h
  · exact absurd h hu
  · rw [← h2 u h]; exact hu

theorem comp_eq (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ * (cLoc u x).val = 1 := by
  have h : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 := congrArg (RingHom.mapMatrix ((pLoc E u).comp (pFin E))) h
  rw [map_one, map_mul] at h2
  exact h2

theorem eq_one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (z : locU n w) (h1 : cLoc w z.1 = 1) :
    z = 1 := by
  obtain ⟨-, -, hover⟩ := over_split hw
  have hw1 : ∀ v, v = w → cLoc v z.1 = 1 := by
    rintro v rfl
    exact h1
  have hall : ∀ u, cLoc u z.1 = 1 := by
    intro u
    by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · rcases hover u hu with rfl | rfl
      · exact h1
      · have hce := comp_eq z.1 (conjSrc (conjE E) w)
        rw [hw1 _ (conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one, Matrix.one_mul] at hce
        exact Units.ext hce
    · have hz := (Subgroup.mem_inf.1 z.2).2
      exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hz u) hu)
  have hinf : cInf z.1 = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 z.2).1
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

def psi (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E :=
  (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose

theorem psi_spec (w : HeightOneSpectrum (𝓞 E)) : Continuous (psi w) ∧
    ∀ k : E, psi w (algebraMap E _ k) = algebraMap E _ (conjE E k) :=
  ⟨(GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.1,
    (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.2.1⟩

theorem conjLoc_psi (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) : conjLoc (conjE E) w (psi w y) = y := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) w).equalizer
    ((conjLoc_spec (conjE E) w).1.comp (psi_spec w).1) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem conjLoc_pLoc (w : HeightOneSpectrum (𝓞 E)) (a : Af E) :
    conjLoc (conjE E) (conjSrc (conjE E) w) (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w)) a) = psi w (pLoc E w a) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w)
      (f : v.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = psi w (pLoc E w a) := by
    rintro v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf (psi_spec v).1
      (funext fun k => (h k).trans ((psi_spec v).2 k).symm)) _
  exact key _ (conjSrc_conjSrc_cm w) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem invT_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (invT n R g) = invT n S (GeneralLinearGroup.map f g) := by
  apply Units.ext
  change ((g⁻¹ : GL (Fin n) R).val)ᵀ.map f = ((GeneralLinearGroup.map f g)⁻¹).valᵀ
  rw [← map_inv]
  rfl

def finPt (w : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (w.adicCompletion E)) : GL (Fin n) (Af E) :=
  locGL E n w h * locGL E n (conjSrc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))

theorem finPt_w {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E w) (finPt w h) = h := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]

theorem finPt_w' {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) w)) (finPt w h) =
      invT n _ (GeneralLinearGroup.map (psi w) h) := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]

theorem finPt_other {w u : HeightOneSpectrum (𝓞 E)} (h1 : u ≠ w) (h2 : u ≠ conjSrc (conjE E) w)
    (h : GL (Fin n) (w.adicCompletion E)) : GeneralLinearGroup.map (pLoc E u) (finPt w h) = 1 := by
  rw [finPt, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]

omit [IsCMField E] in
theorem matAf_ext {M N : Matrix (Fin n) (Fin n) (Af E)}
    (h : ∀ u, RingHom.mapMatrix (pLoc E u) M = RingHom.mapMatrix (pLoc E u) N) : M = N :=
  Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => congrFun (congrFun (h u) i) j

theorem matAd_ext {M N : Matrix (Fin n) (Fin n) (Ad E)} (h1 : RingHom.mapMatrix (pInf E) M = RingHom.mapMatrix (pInf E) N)
    (h2 : RingHom.mapMatrix (pFin E) M = RingHom.mapMatrix (pFin E) N) : M = N :=
  Matrix.ext fun i j => ad_ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem finGL_mem_UA (k : GL (Fin n) (Af E))
    (hk : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) k).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1) : finGL E n k ∈ UA E n := by
  show cT (conjAd E) (finGL E n k).val * 1 * (finGL E n k).val = 1
  rw [Matrix.mul_one]
  have hinf : (finGL E n k).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL k)
  have hfin : (finGL E n k).val.map (pFin E) = k.val := congrArg Units.val (pFin_finGL k)
  refine matAd_ext ?_ ?_
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pInf E) (cT (conjAd E) (finGL E n k).val) = 1 := by
      refine Matrix.ext fun i j => ?_
      have hji := congrFun (congrFun hinf j) i
      change pInf E (conjAd E ((finGL E n k).val j i)) = _
      rw [show pInf E (conjAd E ((finGL E n k).val j i)) = starRingEnd (Cinf E) (pInf E ((finGL E n k).val j i)) from
        (infEq E).symm_apply_apply _]
      change starRingEnd (Cinf E) (((finGL E n k).val.map (pInf E)) j i) = _
      rw [hinf]
      simp [Matrix.one_apply, eq_comm]
    rw [e, one_mul]
    exact hinf
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) = cT (conjFin (conjE E)) k.val := by
      rw [← hfin]; rfl
    change RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) * (finGL E n k).val.map (pFin E) = 1
    rw [e, hfin]
    refine matAf_ext fun u => ?_
    rw [map_mul, map_one]
    exact hk u

theorem finPt_cond {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E))
    (u : HeightOneSpectrum (𝓞 E)) :
    ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) (finPt w h)).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) (finPt w h)).val = 1 := by
  obtain ⟨hne, -, -⟩ := over_split hw
  by_cases h1 : u = w
  · rw [h1, finPt_w' hne, finPt_w hne]
    change ((GeneralLinearGroup.map (conjLoc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))).val)ᵀ * h.val = 1
    rw [invT_map, show GeneralLinearGroup.map (conjLoc (conjE E) w) (GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _)]
    change (((h⁻¹ : GL (Fin n) _).val)ᵀ)ᵀ * h.val = 1
    rw [Matrix.transpose_transpose, Units.inv_mul]
  · by_cases h2 : u = conjSrc (conjE E) w
    · rw [h2, finPt_w' hne]
      have e : (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w))) (finPt w h)).val.map
          (conjLoc (conjE E) (conjSrc (conjE E) w)) = (GeneralLinearGroup.map (psi w) h).val := by
        refine Matrix.ext fun i j => ?_
        refine (conjLoc_pLoc w _).trans ?_
        have := congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) (finPt_w hne h)
        exact congrArg (psi w) this
      rw [e]
      change (GeneralLinearGroup.map (psi w) h).valᵀ * ((GeneralLinearGroup.map (psi w) h)⁻¹).valᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    · have h3 : conjSrc (conjE E) u ≠ w := fun e => h2 (by rw [← e, conjSrc_conjSrc_cm])
      have h4 : conjSrc (conjE E) u ≠ conjSrc (conjE E) w := fun e => h1 (conjSrc_injective _ e)
      rw [finPt_other h3 h4, finPt_other h1 h2]
      simp

theorem cLoc_finGL (u : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) (hk : finGL E n k ∈ UA E n) :
    cLoc u (⟨finGL E n k, hk⟩ : UA E n) = GeneralLinearGroup.map (pLoc E u) k := by
  change GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
  have e : ∀ g : GA E n, GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) g) := fun g => Units.ext rfl
  rw [e, pFin_finGL]

def locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) : locU n w :=
  ⟨⟨finGL E n (finPt w h), finGL_mem_UA _ (finPt_cond hw h)⟩, by
    obtain ⟨-, hw', -⟩ := over_split hw
    refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
    rw [cLoc_finGL]
    exact finPt_other (fun e => hu (by rw [e])) (fun e => hu (by rw [e, hw'])) h⟩

theorem cLoc_locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) :
    cLoc w (locPt hw h).1 = h :=
  (cLoc_finGL w _ _).trans (finPt_w (over_split hw).1 h)

theorem continuous_invT (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invT n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end GlobalTheory.SplitPts


open GlobalTheory.SplitPts in
theorem GlobalTheory.locU_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
      ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  intro E _ _ _ n w hw
  have inj : ∀ a b : locU n w, cLoc w a.1 = cLoc w b.1 → a = b := fun a b hab => by
    have := eq_one_of_cLoc hw (a * b⁻¹)
      (by rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hfin : Continuous (finGL E n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  refine ⟨{ toFun := fun x => cLoc w x.1
            invFun := locPt hw
            left_inv := fun x => inj _ _ (cLoc_locPt hw _)
            right_inv := fun h => cLoc_locPt hw h
            map_mul' := fun x y => map_mul (cLoc w) x.1 y.1
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · exact (Continuous.units_map _ (continuous_id.matrix_map
      ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · refine Continuous.subtype_mk (Continuous.subtype_mk (hfin.comp ?_) _) _
    exact (CuspSub.continuous_locGL w).mul ((CuspSub.continuous_locGL _).comp ((continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))))
end
end

