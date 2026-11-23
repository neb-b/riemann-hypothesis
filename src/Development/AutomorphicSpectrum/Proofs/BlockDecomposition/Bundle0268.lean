module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatible
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem existsUnique_limit_of_dvd {R : Type*} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (z : ℕ → R)
    (hz : ∀ m, t ^ (m + 1) ∣ z (m + 1) - z m) :
    ∃! x : R, ∀ m, t ^ (m + 1) ∣ x - z m := by
  have hmem : ∀ (n : ℕ) (a : R), a ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule R R) ↔ t ^ n ∣ a := by
    intro n a
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hchain : ∀ {m n : ℕ}, m ≤ n → t ^ m ∣ z n - z m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : t ^ m ∣ z (n + 1) - z n := (pow_dvd_pow t (by omega)).trans (hz n)
      have h2 := dvd_add h1 ih
      simpa using h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) z (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, hmem]
    exact hchain hmn)
  refine ⟨L, fun m => ?_, fun x hx => ?_⟩
  · have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
      have := hL (m + 1)
      rw [SModEq.comm, SModEq.sub_mem, hmem] at this
      exact this
    have h2 := dvd_add h1 (hz m)
    simpa using h2
  · have hLd : ∀ m, t ^ (m + 1) ∣ L - z m := by
      intro m
      have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
        have := hL (m + 1)
        rw [SModEq.comm, SModEq.sub_mem, hmem] at this
        exact this
      have h2 := dvd_add h1 (hz m)
      simpa using h2
    refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)
    rw [SModEq.zero, hmem]
    have h3 := dvd_sub (hx n) (hLd n)
    have h4 : t ^ (n + 1) ∣ x - L := by simpa using h3
    exact (pow_dvd_pow t (Nat.le_succ n)).trans h4

theorem isAdicComplete_span_tBdR (l : ℕ) [Fact l.Prime] :
    IsAdicComplete (Ideal.span {tBdR l}) (BdRp l) := by
  rw [← maximalIdeal_eq_span_tBdR]
  exact IsPerfectoidField.instIsAdicCompleteMaximalIdealBdR

theorem pInv_rangeRestrict (l : ℕ) [Fact l.Prime] (b : BdRp l) :
    pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b) = b :=
  RingEquiv.symm_apply_apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩) b

theorem pInv_injective (l : ℕ) [Fact l.Prime] : Function.Injective (pInv l) :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.injective

theorem existsUnique_bdRp_of_compatible (l : ℕ) [Fact l.Prime]
    (y : ∀ m : ℕ, Bk l (m + 1)) (hy : ∀ m, dk l (m + 1) (y (m + 1)) = y m) :
    ∃! x : BdRp l, ∀ m, pk l (m + 1) x = y m := by
  haveI := isAdicComplete_span_tBdR l
  choose z hz using fun m => Ideal.Quotient.mk_surjective (y m)
  have key : ∀ (m : ℕ) (x : BdRp l), pk l (m + 1) x = y m ↔ tBdR l ^ (m + 1) ∣ x - z m := by
    intro m x
    rw [← hz m, pk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hstep : ∀ m, tBdR l ^ (m + 1) ∣ z (m + 1) - z m := by
    intro m
    rw [← key m]
    have := hy m
    rw [← hz (m + 1)] at this
    exact this
  obtain ⟨x, hx, hu⟩ := existsUnique_limit_of_dvd (tBdR l) z hstep
  exact ⟨x, fun m => (key m x).2 (hx m), fun x' hx' => hu x' fun m => (key m x').1 (hx' m)⟩

theorem levSys_existsUnique {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    {M : ℕ} (h : LevHyp l K M) :
    ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) →
      ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  intro y hy
  obtain ⟨b, hb, hu⟩ := existsUnique_bdRp_of_compatible l y hy
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict b, fun m => ?_, fun x' hx' => ?_⟩
  · change pk l (m + 1) (pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b)) = y m
    rw [pInv_rangeRestrict]
    exact hb m
  · refine pInv_injective l ?_
    rw [pInv_rangeRestrict]
    exact hu _ hx'

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSub
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

theorem map_mem_sub_of_mul {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (g : B →+* B) (s : W → W) (hs : ∀ w, g (f w) = f (s w)) (u : W) (hu : s ξ = u * ξ) :
    ∀ x ∈ sub f ξ l M, g x ∈ sub f ξ l M := by
  have hle : sub f ξ l M ≤ (sub f ξ l M).comap g := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · show g (f w) ∈ sub f ξ l M
      rw [hs]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    · show g (dpE f ξ l M i) ∈ sub f ξ l M
      have hη : g (η f ξ l M) = f u * η f ξ l M := by
        rw [η, map_rat_smul, hs, hu, map_mul, mul_smul_comm]
      have hd : g (dpE f ξ l M i) = f u ^ i * dpE f ξ l M i := by
        rw [dpE, map_rat_smul, map_pow, hη, mul_pow, mul_smul_comm]
      rw [hd]
      have h1 : f u ∈ sub f ξ l M := Subring.subset_closure (Or.inl ⟨u, rfl⟩)
      have h2 : dpE f ξ l M i ∈ sub f ξ l M := Subring.subset_closure (Or.inr ⟨i, rfl⟩)
      exact (sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem h1 i) h2
  exact fun x hx => hle hx

theorem gal_mem_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ)
    (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)),
    ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M,
      Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K M k g hT
  have hmem : toBot g.1 • xi0 l ∈ RingHom.ker (theta0 l) :=
    gal_smul_mem_ker_fontaineTheta (toBot g.1) (by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _)
  rw [ker_theta0, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine map_mem_sub_of_mul (fk l k) (xi0 l) l M _ (fun w => toBot g.1 • w) (fun w => ?_) u hu.symm
  show Ideal.quotientMap _ (gP l g) hT (Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l w)) =
    Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l (toBot g.1 • w))
  rw [Ideal.quotientMap_mk, ← gal_smul_wittToBDeRhamPlus]
  rfl

end GlobalTheory.CompanionTheory.LatGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
section
set_option autoImplicit false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

private theorem galBdRHom_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : BDeRhamPlus (normInteger ℂ_[p]) p)
    (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)) :
    galBdRHom σ x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have h1 : galBdRHom σ⁻¹ (galBdRHom σ x) = x := by
    rw [← RingHom.comp_apply, ← galBdRHom_mul, inv_mul_cancel, galBdRHom_one, RingHom.id_apply]
  rw [← h1]
  exact hu.map _

theorem span_tBdR_pow_le_comap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (k : ℕ) (g : K.fixingSubgroup) :
    Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  have ht : Lat.gP l g (tBdR l) ∈ Ideal.span {tBdR l} := by
    rw [← maximalIdeal_eq_span_tBdR]
    exact galBdRHom_mem_maximalIdeal _ _ (by rw [maximalIdeal_eq_span_tBdR]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ht
  rw [← hc, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.LatGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureLocalBall
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi.BallVol

theorem measure_translate_ballV : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  intro F _ _ v lam hlam k a
  obtain ⟨hHaar, h1⟩ := hlam
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : lam.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam
  have htr : (fun z => z - a) ⁻¹' ballV v k = (fun z => z + -a) ⁻¹' ballV v k := by
    simp only [sub_eq_add_neg]
  rw [htr, measure_preimage_add_right]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  let ϖ : Fv F v := ((π : v.adicCompletion F) : Fv F v)
  have hvϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hvϖ
    exact WithZero.exp_ne_zero hvϖ.symm
  open Pointwise in
  have hball : ballV v k = (ϖ ^ k) • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero k hϖ0)]
    simp only [ballV, Set.mem_ofPred_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      smul_eq_mul, map_mul, map_inv₀, map_pow, hvϖ]
    have hk : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by
      rw [← WithZero.exp_nsmul]; simp
    rw [hk, inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
  rw [hball]
  have hu : IsUnit (ϖ ^ k) := (pow_ne_zero k hϖ0).isUnit
  open Pointwise in
  have key := distribHaarChar_mul lam hu.unit (v.adicCompletionIntegers F : Set (Fv F v))
  rw [Units.smul_def, IsUnit.unit_spec, h1, mul_one] at key
  rw [← key]
  open scoped Pointwise in
  have card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
    obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
    have ha1 : a ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
    have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
      (by simpa using ha)
    have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
      ext y
      rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
        (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
      change _ ↔ _ ≤ Valued.v a
      rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
      exact Valuation.mem_maximalIdeal_iff _ _
    rw [pow_one, ← e] at h
    exact h
  open scoped Pointwise ENNReal NNReal in
  have modu_finite (x : Fv F v)
      (hx : x ≠ 0) : (distribHaarChar (Fv F v) hx.isUnit.unit : ℝ) = ‖x‖ := by
    have hu : IsUnit x := hx.isUnit
    have hv : Valued.v x ≠ 0 := by simpa using hx
    let μ : Measure (Fv F v) := Measure.addHaar
    have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
      (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
      ext y
      rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
      rfl
    have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
      rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
    have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
        WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
        HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
        Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
      simp
    have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
        v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext y
      simp
    rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
      Fintype.card_unit, pow_one] at h
    have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
    rw [h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
    push_cast
    congr 1
  have hm := modu_finite (ϖ ^ k) (pow_ne_zero k hϖ0)
  have hn : ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
    rw [NumberField.FinitePlace.norm_def, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π, hπ,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-1 : ℤ) : NNReal) : ℝ) = _
    rw [zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
  rw [norm_pow, hn, inv_pow] at hm
  rw [← hm, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.Equi.BallVol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltration
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.Tower

variable {R : Type} [CommRing R] {N : ℕ}

theorem sub_tail_mem (I : Ideal R) (e : ℕ) (G : ℕ → MvPolynomial (Fin (N + 1)) R)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) (m k : ℕ) :
    G m - G (m + k) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : G (m + k) - G (m + k + 1) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hd (m + k))
    have h3 : G m - G (m + (k + 1)) = (G m - G (m + k)) + (G (m + k) - G (m + k + 1)) := by
      rw [show m + (k + 1) = m + k + 1 from rfl]
      ring
    rw [h3]
    exact add_mem ih h2

theorem exists_limit_form (I : Ideal R) [IsPrecomplete I R] (n e : ℕ)
    (G : ℕ → MvPolynomial (Fin (N + 1)) R) (hom : ∀ i, (G i).IsHomogeneous n)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ g : MvPolynomial (Fin (N + 1)) R, g.IsHomogeneous n ∧
      ∀ i, G i - g ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have htop : ∀ k, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcoef : ∀ d i k, AddMonoidAlgebra.coeff (G i) d - AddMonoidAlgebra.coeff (G (i + k)) d ∈ I ^ (e + i + 1) := by
    intro d i k
    have h := (mem_map_C_iff.1 (sub_tail_mem I e G hd i k)) d
    rwa [coeff_sub] at h
  have hL : ∀ d, ∃ Ld : R, ∀ i, AddMonoidAlgebra.coeff (G i) d - Ld ∈ I ^ (e + i + 1) := by
    intro d
    obtain ⟨Ld, hLd⟩ := IsPrecomplete.prec' (I := I) (fun i => AddMonoidAlgebra.coeff (G i) d) (by
      intro m n hmn
      rw [SModEq.sub_mem, htop]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Ideal.pow_le_pow_right (by omega) (hcoef d m k))
    refine ⟨Ld, fun i => ?_⟩
    have h1 := hcoef d i (e + 1)
    have h2 := hLd (i + (e + 1))
    rw [SModEq.sub_mem, htop] at h2
    have h3 : AddMonoidAlgebra.coeff (G i) d - Ld =
        (AddMonoidAlgebra.coeff (G i) d - AddMonoidAlgebra.coeff (G (i + (e + 1))) d) + (AddMonoidAlgebra.coeff (G (i + (e + 1))) d - Ld) := by ring
    rw [h3]
    exact add_mem h1 (Ideal.pow_le_pow_right (by omega) h2)
  choose Lf hLf using hL
  refine ⟨∑ d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n, monomial d (Lf d), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ (fun d hd => isHomogeneous_monomial _ ?_)
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [Finsupp.degree_eq_sum]
    exact hd.1
  · intro i
    rw [mem_map_C_iff]
    intro d
    rw [coeff_sub, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hdS : d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n
    · rw [if_pos hdS]
      exact hLf d i
    · rw [if_neg hdS, sub_zero]
      have h0 : AddMonoidAlgebra.coeff (G i) d = 0 := by
        by_contra hne
        apply hdS
        have hw := hom i hne
        rw [Finset.mem_finsuppAntidiag]
        refine ⟨?_, Finset.subset_univ _⟩
        rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
        exact hw
      rw [h0]
      exact zero_mem _

theorem exists_form_in_all (I : Ideal R) [IsPrecomplete I R]
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hanti : ∀ e, L (e + 1) ≤ L e) (n₀ : ℕ)
    (hlift : ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (e n : ℕ) (hn : n₀ ≤ n) (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ L e)
    (hgn : g.IsHomogeneous n) :
    ∃ g' : MvPolynomial (Fin (N + 1)) R, g'.IsHomogeneous n ∧ (∀ j, g' ∈ L j) ∧
      g - g' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have hL : Antitone L := antitone_nat_of_succ_le hanti
  let lift' : ℕ → MvPolynomial (Fin (N + 1)) R → MvPolynomial (Fin (N + 1)) R := fun j f =>
    if h : ∃ f' ∈ L (j + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (j + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) then h.choose else f
  let s : ℕ → MvPolynomial (Fin (N + 1)) R := fun i =>
    Nat.rec (motive := fun _ => MvPolynomial (Fin (N + 1)) R) g (fun k f => lift' (e + k) f) i
  have hsS : ∀ i, s (i + 1) = lift' (e + i) (s i) := fun i => rfl
  have hstep : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n →
      s (i + 1) ∈ L (e + i + 1) ∧ (s (i + 1)).IsHomogeneous n ∧
        s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    rintro i ⟨h1, h2⟩
    have hex := hlift (e + i) n hn (s i) h1 h2
    rw [hsS]
    simp only [lift']
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have hinv : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n := by
    intro i
    induction i with
    | zero => exact ⟨hg, hgn⟩
    | succ i ih => exact ⟨(hstep i ih).1, (hstep i ih).2.1⟩
  have hd : ∀ i, s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
    fun i => (hstep i (hinv i)).2.2
  obtain ⟨g', hg'n, hg'⟩ := exists_limit_form I n e s (fun i => (hinv i).2) hd
  refine ⟨g', hg'n, fun j => ?_, hg' 0⟩
  have h1 : s j ∈ L j := hL (by omega : j ≤ e + j) (hinv j).1
  have h2 : s j - g' ∈ L j := hL (by omega : j ≤ e + j) (hbase (e + j) (hg' j))
  have h3 : g' = s j - (s j - g') := by ring
  rw [h3]
  exact sub_mem h1 h2


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem exists_limit_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ I hI N L hhom hbase hanti n₀ hlift
  have : IsPrecomplete I R := hI.toIsPrecomplete
  classical
  let S : Set (MvPolynomial (Fin (N + 1)) R) := {g | ∃ n, n₀ ≤ n ∧ g.IsHomogeneous n ∧ ∀ j, g ∈ L j}
  refine ⟨Ideal.span S, ?_, fun e => ⟨?_, ?_⟩⟩
  · intro d f hf
    have hH : (Ideal.span S).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) :=
      Ideal.homogeneous_span _ _ (fun x hx => by
        obtain ⟨n, _, hn, _⟩ := hx
        exact ⟨n, (mem_homogeneousSubmodule n x).2 hn⟩)
    have h := (Ideal.IsHomogeneous.mem_iff _ hH).1 hf d
    have e1 : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) f d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d f := decomposition.decompose'_apply f d
    rwa [e1] at h
  · rw [Ideal.span_le]
    rintro g ⟨n, _, _, hall⟩
    exact hall e
  · intro f hf k
    refine ⟨n₀, ?_⟩
    rw [← sum_homogeneousComponent f, Finset.mul_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hmem : X k ^ n₀ * homogeneousComponent d f ∈ L e := Ideal.mul_mem_left _ _ (hhom e d f hf)
    have hh : (X k ^ n₀ * homogeneousComponent d f).IsHomogeneous (n₀ + d) :=
      (isHomogeneous_X_pow k n₀).mul (homogeneousComponent_isHomogeneous d f)
    obtain ⟨g', hg'n, hall, hdiff⟩ :=
      exists_form_in_all I L hbase hanti n₀ hlift e (n₀ + d) (Nat.le_add_right _ _) _ hmem hh
    have h3 : X k ^ n₀ * homogeneousComponent d f = g' + (X k ^ n₀ * homogeneousComponent d f - g') := by
      ring
    rw [h3]
    exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨n₀ + d, Nat.le_add_right _ _, hg'n, hall⟩))
      (Ideal.mem_sup_right hdiff)

end GlobalTheory.CompanionTheory.GE.Tower
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegers
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem iota_algebraMap_OK : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  intro l _ K M h k a
  rfl

end GlobalTheory.CompanionTheory.LatC
end

