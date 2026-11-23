module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0122
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFinite
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory

theorem finite_latticeCurve_torsion (L : PeriodPair) {n : ℕ} (hn : n ≠ 0) :
    {P : (latticeCurve L).toAffine.Point | n • P = 0}.Finite := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hz : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine (((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image
    (fun p : ℤ × ℤ => latticePoint L ((p.1 * L.ω₁ + p.2 * L.ω₂) / n))).subset ?_
  intro P hP
  obtain ⟨z, rfl⟩ := latticePoint_surjective L P
  have h1 : latticePoint L (n • z) = 0 := by
    rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
  rw [latticePoint_eq_zero_iff] at h1
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩,
    ⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩⟩, ?_⟩
  dsimp only
  rw [latticePoint_eq_iff, PeriodPair.mem_lattice]
  refine ⟨-(a / n), -(b / n), ?_⟩
  have ea : (a : ℂ) = ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a n).symm
  have eb : (b : ℂ) = ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b n).symm
  rw [nsmul_eq_mul] at hab
  rw [Int.cast_neg, Int.cast_neg]
  generalize ((a % n : ℤ) : ℂ) = a₁, ((a / n : ℤ) : ℂ) = a₂, ((b % n : ℤ) : ℂ) = b₁,
    ((b / n : ℤ) : ℂ) = b₂ at ea eb ⊢
  rw [ea, eb] at hab
  field_simp
  linear_combination -hab

theorem finite_complex_torsion_points (W : WeierstrassCurve ℂ) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.toAffine.Point | n • P = 0}.Finite := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  refine ((finite_latticeCurve_torsion L hn).image e).subset ?_
  intro P hP
  refine ⟨e.symm P, ?_, e.apply_symm_apply P⟩
  have hP' : n • P = 0 := hP
  show n • e.symm P = 0
  rw [← map_nsmul, hP', map_zero]

theorem finite_torsionCoords :
    ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  intro W _ n hn
  have h := finite_complex_torsion_points W hn
  let fx : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some x _ _ => x
  let fy : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some _ y _ => y
  refine ((h.image fx).union (h.image fy)).subset ?_
  rintro z ⟨x, y, hxy, h0, rfl | rfl⟩
  · exact Or.inl ⟨_, h0, rfl⟩
  · exact Or.inr ⟨_, h0, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem fdegOf_eq_of_isFdeg {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ)
    (h : IsFdeg μ σ d) (w : H) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, h⟩ := h
  have h2 := (h w w w w).2
  have e1 : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂μ = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    push_cast
    simp only [RCLike.ofReal, Complex.coe_algebraMap]
    ring
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegOf
  rw [h3]
  field_simp

theorem exists_isDS_isFdeg_trueDsig : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  intro hE hF cd R P
  have hpar := (_root_.GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos R P).1
  have key : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
    intro H _ _ σ d hσ hd
    have : Nontrivial H := hσ.2.1
    obtain ⟨w, hw⟩ := exists_ne (0 : H)
    rw [← fdegOf_eq_of_isFdeg _ σ d hd w hw]
    exact hF cd (trueScale cd) (_root_.GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale cd) _ (epsSH R) (lamSH R P) hpar H σ w hσ hw
  refine ⟨?_, key⟩
  obtain ⟨H, i1, i2, σ, hσ⟩ := hE _ (epsSH R) (lamSH R P) hpar
  obtain ⟨d, hd⟩ := exists_isFdeg_smul_of_isDS _ (epsSH R) (lamSH R P) H σ hσ _ (trueScale_pos cd _ (epsSH R))
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key H σ d hσ hd]
  exact hd

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorPowPrimeOneModModulus
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem exists_unif_one_mod {R : Type} [CommRing R] [IsDedekindDomain R] (𝔮 : Ideal R) (h𝔮 : 𝔮 ≠ ⊥)
    (v : HeightOneSpectrum R) : ∃ c : R, c ∈ v.asIdeal ∧ c ∉ v.asIdeal ^ 2 ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.asIdeal ∣ 𝔮 → c - 1 ∈ w.asIdeal := by
  classical
  have hfin := Ideal.finite_factors h𝔮
  let S : Finset (HeightOneSpectrum R) := hfin.toFinset.erase v
  have hcop : IsCoprime (v.asIdeal ^ 2) (∏ w ∈ S, w.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun w hw => ?_)
    have hne : v.asIdeal ≠ w.asIdeal := fun h => (Finset.ne_of_mem_erase hw) (HeightOneSpectrum.ext h).symm
    exact Ideal.isCoprime_iff_sup_eq.2 (v.isMaximal.coprime_of_ne w.isMaximal hne)
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  rw [pow_one] at hπ1
  refine ⟨π * b + a, ?_, ?_, fun w hw hd => ?_⟩
  · exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ hπ1) (Ideal.pow_le_self two_ne_zero ha)
  · intro hc
    apply hπ2
    have : π = (π * b + a) + a * (π - 1) := by linear_combination (-π) * hab
    rw [this]
    exact Ideal.add_mem _ hc (Ideal.mul_mem_right _ _ ha)
  · have hS : w ∈ S := Finset.mem_erase.2 ⟨hw, hfin.mem_toFinset.2 hd⟩
    have hb' : b ∈ w.asIdeal := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hS) hb
    have : π * b + a - 1 = b * (π - 1) := by linear_combination hab
    rw [this]
    exact Ideal.mul_mem_right _ _ hb'

theorem exists_gen_pow_prime_one_mod (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ) (h𝔮 : 𝔮 ≠ ⊥)
    (H : ∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α})
    (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ,
      FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_unif_one_mod 𝔮 h𝔮 v
  have hc0 : c ≠ 0 := by rintro rfl; exact hc2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc1)
  have hcJ : c ∈ v.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self c
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hcJ
    exact hc0 hcJ
  have hcop : IsCoprime J 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm0 : m ≠ ⊥ := fun h0 => h𝔮 (le_bot_iff.1 (h0 ▸ le_sup_right.trans hle))
    let w : HeightOneSpectrum (𝓞 L) := ⟨m, hm.isPrime, hm0⟩
    have hJm : J ≤ m := le_sup_left.trans hle
    by_cases hw : w = v
    · apply hc2
      have : v.asIdeal = m := hw ▸ rfl
      rw [sq]
      exact Ideal.mul_mono_right (this ▸ hJm) hcJ
    · have h1 : c - 1 ∈ m := hc3 w hw (Ideal.dvd_iff_le.2 (le_sup_right.trans hle))
      have h2 : c ∈ m := hJm (Ideal.le_of_dvd (dvd_mul_left J v.asIdeal) hcJ)
      exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h2 h1))
  obtain ⟨α, β, ⟨hα0, hβ0, hα, -, hαβ, -⟩, hE⟩ := H J hJ0 hcop
  have hαL : algebraMap (𝓞 L) L α ≠ 0 := by simpa using hα0
  have hβL : algebraMap (𝓞 L) L β ≠ 0 := by simpa using hβ0
  have hcL : algebraMap (𝓞 L) L c ≠ 0 := by simpa using hc0
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L (c ^ h * β) / algebraMap (𝓞 L) L α)
    (div_ne_zero (by rw [map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hcL) hβL) hαL), ?_, fun w hw hd => ?_⟩
  · have hI : Ideal.span {c ^ h * β} = v.asIdeal ^ h * Ideal.span {α} := by
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hJ, mul_pow, mul_assoc, hE]
    have hne : FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L α) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.2 hαL
    apply mul_right_cancel₀ hne
    rw [Units.val_mk0, FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hαL,
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, hI,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  · have hle : 𝔮 ≤ w.asIdeal := Ideal.le_of_dvd hd
    have hαw : α ∉ w.asIdeal := fun hm => w.isPrime.ne_top (top_le_iff.1 (by
      rw [← Ideal.isCoprime_iff_sup_eq.1 hα]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hm) hle))
    have hp : c ^ h - 1 ∈ w.asIdeal := by
      have := sub_dvd_pow_sub_pow c 1 h
      rw [one_pow] at this
      obtain ⟨t, ht⟩ := this
      rw [ht]
      exact Ideal.mul_mem_right _ _ (hc3 w hw hd)
    have hm : c ^ h * β - α ∈ w.asIdeal := by
      have : c ^ h * β - α = (c ^ h - 1) * β - (α - β) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hp) (hle hαβ)
    rw [Units.val_mk0, div_sub_one hαL, ← map_sub, map_div₀,
      (w.valuation_eq_one_iff_notMem (K := L)).2 hαw, div_one]
    exact (w.valuation_lt_one_iff_mem (K := L) _).2 hm

end GlobalTheory.Mem.FieldsEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHFrameDtPackPre
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Pre

variable (B : Pre)

theorem splitsC_level {p : ℕ} (hp : p ∈ B.host.levelPrimes) : SplitsC B.host.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem splitsC_g (k : Fin 2) : SplitsC B.host.E (B.host.g k) := B.splitsC_level (B.host.g_level k)

theorem splitsC_pde : SplitsC B.host.E B.host.pde := B.splitsC_level B.host.pde_level.1

theorem splitsC_pde' : SplitsC B.host.E B.host.pde' := B.splitsC_level B.host.pde_level.2

def EvenExp : Prop := ∀ j, UpperTheory.MUQ (Formalism.L2.Host.embPsi B.host) (fun τ : B.R.Psi => (B.hc τ).e j)

theorem nonempty_hframe (h : B.EvenExp) : Nonempty (HFrame B.host fun j τ => (B.hc τ).e j) :=
  _root_.GlobalTheory.nonempty_hFrame B.R B.host _ B.splitsC_g B.splitsC_pde B.splitsC_pde' (fun j τ => (B.hc τ).e_int j) h

end GlobalTheory.Mem.Pre

namespace GlobalTheory.Mem.Chr

end GlobalTheory.Mem.Chr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity
section
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf_of_density {p q : ℕ} (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) (c : ℝ≥0∞)
    (h0 : c ≠ 0) (ht : c ≠ ⊤) (hc : OmegaDensity μ c) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  haveI : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
  have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
  have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
  lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc
  refine ⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩
  have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
  rwa [htc, ENNReal.div_mul_cancel h0 ht] at h

theorem exists_isMinf_of_cd (h : Nonempty CDHaar) (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  obtain ⟨cd⟩ := h
  obtain ⟨c, h0, ht, hc, -⟩ := cd.trick p q
  exact exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc

end GlobalTheory.MinfMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobenius
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : R, x ^ q = x) : Nat.card R ≤ q := by
  classical
  have := Fintype.ofFinite R
  have hd : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), Polynomial.natDegree_X_pow]
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) hd.le
  intro x _
  rw [Polynomial.mem_roots hne]
  simp [h x]

theorem exists_two_primes_of_isFrob_one (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (σ : F ≃ₐ[K] F) (hσ : σ ≠ 1) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 →
      ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧
        Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  let e : 𝓞 F ≃ₐ[𝓞 K] 𝓞 F := RingOfIntegers.mapAlgEquiv σ
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓞 F, e θ - θ ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hσ
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have h : ∀ a : 𝓞 F, σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F a := fun a =>
      congrArg (algebraMap (𝓞 F) F) (sub_eq_zero.1 (hc a))
    simp only [map_div₀, h, AlgEquiv.one_apply]
  have hfin : {P : HeightOneSpectrum (𝓞 F) | P.asIdeal ∣ Ideal.span {e θ - θ}}.Finite :=
    Ideal.finite_factors (by simpa using hθ)
  refine ⟨{v | ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ Ideal.span {e θ - θ} ∧
    P.asIdeal.under (𝓞 K) = v.asIdeal}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      ((hfin.image (fun P => P.asIdeal.under (𝓞 K))).subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨v, ⟨P, hP, hv⟩, rfl⟩
    exact ⟨P, hP, hv⟩
  rintro v hv ⟨P, hP, hPo, hx⟩
  have hvp := v.isPrime
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hfP : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Finite.one_lt_card
  have hle : Nat.card (𝓞 F ⧸ P) ≤ Nat.card (𝓞 K ⧸ v.asIdeal) := by
    have h0 : Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [← h0]
    refine card_le_of_pow_eq_self hq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := hx x
    rw [one_smul] at this
    rw [← map_pow]
    exact (Ideal.Quotient.eq.2 this).symm
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  have hbij : Function.Bijective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) :=
    hinj.bijective_of_nat_card_le hle
  have hN : Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_eq_of_bijective _ hbij).symm
  have hQo : (P.comap e).LiesOver v.asIdeal := inferInstance
  have hQ : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  have hQne : P.comap e ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  refine ⟨⟨P, hP, hne⟩, ⟨P.comap e, hQ, hQne⟩, ?_, hPo, hQo, hN, ?_⟩
  · intro h
    have h' : P = P.comap e := congrArg HeightOneSpectrum.asIdeal h
    apply hv
    refine ⟨⟨P, hP, hne⟩, ?_, hPo.over.symm⟩
    rw [Ideal.dvd_span_singleton]
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk P θ)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h1 : algebraMap (𝓞 K) (𝓞 F) a - θ ∈ P := Ideal.Quotient.eq.1 ha
    have h2 : e (algebraMap (𝓞 K) (𝓞 F) a - θ) ∈ P := by
      have := h' ▸ h1
      exact this
    rw [map_sub, AlgEquiv.commutes] at h2
    have := P.sub_mem h1 h2
    show e θ - θ ∈ P
    convert this using 1
    ring
  · show Ideal.absNorm (P.comap e) = _
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    refine Nat.card_congr (Ideal.quotientEquiv (P.comap e) P e.toRingEquiv ?_).toEquiv
    exact (Ideal.map_comap_of_surjective (e.toRingEquiv : 𝓞 F →+* 𝓞 F) e.surjective P).symm

end GlobalTheory.Mem.Fld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMulInv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.DualPairCheck
open scoped TensorProduct

namespace GlobalTheory.OrientedAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  exact (cA_incA _).trans (congrArg (incA D) (gram_star V j i))

section Generic
variable {A : Type} [CommRing A] {m n : ℕ}

theorem inv_conj (σ : A →+* A) (P Pi : Matrix (Fin n) (Fin n) A) (h : P * Pi = 1) (hP : (P.map σ)ᵀ = P) :
    (Pi.map σ)ᵀ = Pi := by
  have h' : Pi * P = 1 := mul_eq_one_comm.1 h
  have h2 : P * (Pi.map σ)ᵀ = 1 := by
    rw [← hP, ← Matrix.transpose_mul, ← Matrix.map_mul, h',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc _ = (Pi * P) * (Pi.map σ)ᵀ := by rw [h', Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

end Generic

end GlobalTheory.OrientedAdjoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_complexForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  first | exact @GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | exact GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | (intros; apply GlobalTheory.Mem.Col2.DiaStab.lawDiaStable <;> assumption)
end

