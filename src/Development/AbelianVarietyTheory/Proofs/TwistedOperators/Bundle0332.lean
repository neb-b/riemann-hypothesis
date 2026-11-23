module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0059
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinZeta.SplitNorm

theorem natCast_mem_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | (apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm ..)

theorem conj_smul_ne_of_isSplit (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) : D.host.conj • w.asIdeal ≠ w.asIdeal := by
  intro hfix
  set c := GlobalTheory.Member.cF D
  have hcc : ∀ x : D.host.E, c x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hself : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    conv_rhs => rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w := fun u hu =>
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl c D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w u).1 (hu.trans hw.symm)).elim id
      fun h => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h hself
  obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := GlobalTheory.LFun.isSplit_iff.1 hv
  exact hne ((key w₁ h₁).trans (key w₂ h₂).symm)

theorem lam_qV_pow (D : D7) (lam : ℕ →* ℂ)
    (hlam : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w.under (𝓞 D.host.F) = v)
    (hv : IsSplit (E := D.host.E) v) (m : ℕ) :
    lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  apply hlam
  · exact pow_ne_zero _ fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · intro q hq hi hd
    have hmem := natCast_mem_of_dvd_absNorm w hq (hq.dvd_of_dvd_pow hd)
    refine conj_smul_ne_of_isSplit D v w hw hv (hi w.asIdeal w.isPrime w.ne_bot hmem)

end GlobalTheory.FinZeta.SplitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

variable {D : D7}

theorem exists_F_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∉ P.asIdeal := by
  classical
  choose! x hx hxP using hP
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ v ∈ S, x v) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hv := hS Q hJ
    have hxv : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hv
    rw [map_prod, ← Finset.prod_erase_mul _ _ hv]
    exact Ideal.mul_mem_left J _ hxv
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ v ∈ S, x v) ^ K, by rwa [map_pow], fun h => ?_⟩
  rw [map_pow] at h
  have h1 := P.isPrime.mem_of_pow_mem K h
  rw [map_prod] at h1
  obtain ⟨v, hv, h2⟩ := (P.isPrime.prod_mem_iff).1 h1
  exact hxP v hv _ rfl h2

theorem oToS_smul_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    oToS F E a • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Subring.smul_def, oToS_coe]
    simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx

end GlobalTheory.CongMember

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_sub_one {R : Type} [CommRing R] (u : R) (hu : u * u = u) (A B K : Matrix (Fin n) (Fin n) R)
    (hA : u • (A - 1) = A - 1) (hB : (1 - u) • (B - 1) = B - 1) (hK : K = A * B ∨ K = B * A) : A - 1 = u • (K - 1) := by
  have e1 : u • B = u • 1 := by
    rw [← sub_eq_zero, ← smul_sub, ← hB, smul_smul, mul_sub, mul_one, hu, sub_self, zero_smul]
  have e2 : u • K = u • A := by
    rcases hK with rfl | rfl
    · rw [← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]
    · rw [← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]
  rw [smul_sub, e2, ← smul_sub, hA]

theorem cong_of_eq (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    (u : Formalism.L2.Herm.intAf F E) (A K : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (e : A - 1 = ((u * oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • (K - 1))
    (hK : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, K *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, A *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  intro y hy
  have e1 : A *ᵥ y - y = (A - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e2 : K *ᵥ y - y = (K - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e' : A *ᵥ y - y = (u * oToS F E a) • (K *ᵥ y - y) := by
    rw [e1, e2, e, Matrix.smul_mulVec, Subring.smul_def]
  rw [e', mul_smul]
  exact Submodule.smul_mem _ u (oToS_smul_mem_hatL Λ ha (Submodule.sub_mem _ (hK y hy) hy))

theorem hatL_smul_le (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) :
    Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) ≤ Formalism.L2.Herm.hatL (F := F) Λ :=
  Submodule.span_mono (Set.image_mono Submodule.smul_le_right)

theorem mem_congLev_of [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hU : x ∈ UA hc J)
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ))
    (h2 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    x ∈ congLev hc J Λ 𝔪 := by
  refine ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, h1⟩
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h1 y hy)) hy
    rwa [sub_add_cancel] at this
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h2 _ hy)) hy
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec, sub_add_cancel] at this

theorem stab_of_mem_congLev [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {𝔪 : Ideal (𝓞 E)} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ congLev hc J Λ 𝔪) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  ⟨fun y hy => (hx.2.1 y).1 hy, fun y hy => ((Subgroup.inv_mem _ hx).2.1 y).1 hy⟩

end General

variable {D : D7}

theorem exists_idem_eq {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) {e f : Formalism.L2.Theta.AE D} (hi : IsPrimeIdem P e f) :
    ∃ a ∈ 𝔪, ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      ((u * oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = GlobalTheory.LevSplit.finSw D f := by
  obtain ⟨X, hX𝔪, hXP⟩ := exists_F_mem h𝔪 hS hP
  obtain ⟨u, hu⟩ := GlobalTheory.LevSplit.idem_div_int hi _ _ ((D.sp.cm.fixed _).2 ⟨(X : D.host.F), rfl⟩).symm hXP hXP
  exact ⟨_, hX𝔪, u, hu⟩

end GlobalTheory.CongMember
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharTraceSingleRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.PhaseReal.psi_trace_single : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (t : AE D),
  finPart D t = 0 → (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) →
  ψ (Algebra.trace (AF D.host.F) (AE D) t) = Complex.exp (Complex.I * (((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re : ℂ)) := by
  intro D ψ hψ θ hθ τ t hfin hsupp
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ T = psiInf D.host.F ψ (fstA D.host.F T) := by
    unfold psiInf
    congr 1
  have h2 := hψ.2.2 θ hθ (fstA D.host.F T)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) :=
    fun ρ => GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
  have h4 : ∑ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ τ (infPart D t)).re : ℝ) : ℂ) := by
    simp only [h3]
    refine Finset.sum_eq_single τ (fun ρ _ hρ => ?_) (fun h => absurd (Finset.mem_univ τ) h)
    rw [hsupp ρ hρ]
    simp
  rw [h1, h2, h4]
  congr 1
  have h5 : ((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re = -(4 * Real.pi) * (θ τ (infPart D t)).re := by
    have : (-(4 * Real.pi : ℂ)) = ((-(4 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [h5]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisJointEigen

theorem coeff_zero_of_separated {ι V : Type*} [AddCommGroup V] [Module ℂ V] [DecidableEq ι] (v : ι → V) :
    ∀ R : Finset ι, (∀ z ∈ R, v z ≠ 0) →
      (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ R, A (v z) = χ z • v z) ∧ χ y ≠ χ y') →
      ∀ c : ι → ℂ, ∑ z ∈ R, c z • v z = 0 → ∀ z ∈ R, c z = 0 := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _ _ c _ z hz; simp at hz
  | insert a s ha ih =>
    intro hv hsep c hsum
    have hv' : ∀ z ∈ s, v z ≠ 0 := fun z hz => hv z (Finset.mem_insert_of_mem hz)
    have hsep' : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' →
        ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ s, A (v z) = χ z • v z) ∧ χ y ≠ χ y' := by
      intro y hy y' hy' hne
      obtain ⟨A, χ, hA, hχ⟩ := hsep y (Finset.mem_insert_of_mem hy) y' (Finset.mem_insert_of_mem hy') hne
      exact ⟨A, χ, fun z hz => hA z (Finset.mem_insert_of_mem hz), hχ⟩
    rw [Finset.sum_insert ha] at hsum
    have hs0 : ∀ b ∈ s, c b = 0 := by
      intro b hb
      have hab : b ≠ a := fun h => ha (h ▸ hb)
      obtain ⟨A, χ, hA, hχ⟩ := hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s) hab
      have key : ∑ z ∈ s, (c z * (χ z - χ a)) • v z =
          A (c a • v a + ∑ z ∈ s, c z • v z) - χ a • (c a • v a + ∑ z ∈ s, c z • v z) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, map_smul, hA a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum,
          add_sub_add_comm, smul_comm (χ a) (c a), sub_self, zero_add, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [map_smul, hA z (Finset.mem_insert_of_mem hz), smul_smul, smul_smul, ← sub_smul]
        congr 1
        ring
      rw [hsum, map_zero, smul_zero, sub_zero] at key
      have h := ih hv' hsep' (fun z => c z * (χ z - χ a)) key b hb
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hχ
    have hsum0 : ∑ z ∈ s, c z • v z = 0 := Finset.sum_eq_zero fun z hz => by rw [hs0 z hz, zero_smul]
    rw [hsum0, add_zero] at hsum
    have hca : c a = 0 := (smul_eq_zero.1 hsum).resolve_right (hv a (Finset.mem_insert_self a s))
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hca
    · exact hs0 z hz

theorem sum_heisO_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  intro D ψ S T ΛS ΛT P e he R hsep g hg hg0 c hc hsum
  obtain ⟨z0, hz0, hcz⟩ := hc
  apply hcz
  classical
  refine coeff_zero_of_separated (fun z => heisO ψ S T z g) R ?_ ?_ c hsum z0 hz0
  · intro z _ h
    apply hg0
    funext w
    have h1 := congrFun h (w - z)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (Formalism.IndefR.Fin.psi_ne_zero ψ _)
    · exact h2
  · intro y hy y' hy' hne
    obtain ⟨u, hu, hhalf, hψ⟩ := hsep y hy y' hy' hne
    have hfix : heisO ψ S T u g = g :=
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he u hu (Or.inl hhalf)
    refine ⟨Formalism.IndefR.Fin.heisL ψ S T u, fun z => ψ (symplO S T u z), fun z _ => ?_, hψ⟩
    have h1 := congrArg (fun L => L g) (Formalism.IndefR.Fin.heisL_comm ψ S T u z)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Formalism.IndefR.Fin.heisL_apply] at h1
    rw [hfix] at h1
    rw [Formalism.IndefR.Fin.heisL_apply]
    exact h1

end GlobalTheory.HeisJointEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
section
noncomputable section

namespace GlobalTheory.PolKer

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ T : Finset (Pl F), X.T ⊆ T ∧ ∃ (m : ℕ) (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) = 0

theorem sum_pure_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (h i).1, (h i).2.1, ?_, rfl⟩
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact (h i).2.2 v hv

theorem algD_of_polZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (h : PolZero B G X R Rf Φ) : Φ ∈ GlobalTheory.SquareAgree.algD G.M B.ψ B.emb := by
  obtain ⟨T, -, m, f, φ, hf, rfl, -⟩ := h
  exact sum_pure_mem_algD G.M B.ψ B.emb T f φ hf

end GlobalTheory.PolKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

variable {D : D7}

theorem symplO_smul_half (S T : HSp D) (e : AE D) (u y : WO S T) (hy : IsHalf (cA D e) y) :
    symplO S T (e • u) y = symplO S T u y := by
  have hc : ∀ c b, cA D (y c b) = e * cA D (y c b) := fun c b => by
    conv_lhs => rw [← hy c b]
    rw [map_mul, GlobalTheory.LatVac.cA_cA]
  unfold symplO
  congr 2
  unfold hO
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl
    (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [Matrix.smul_apply, smul_eq_mul]
  conv_rhs => rw [hc c b]
  ring

theorem half_actO (S T : HSp D) (c : AE D) (h : GA D T) (Y : WO S T) (hY : IsHalf c Y) :
    IsHalf c (actO S T 1 h Y) := by
  have hYe : c • Y = Y := by
    ext a b
    exact hY a b
  have hm : c • actO S T 1 h Y = actO S T 1 h Y := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hYe]
  intro a b
  exact congrFun (congrFun hm a) b

theorem actO_add (S T : HSp D) (h : GA D T) (Y Y' : WO S T) :
    actO S T 1 h (Y + Y') = actO S T 1 h Y + actO S T 1 h Y' := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_inv (S T : HSp D) (h : GA D T) (y : WO S T) :
    actO S T 1 h (actO S T 1 h⁻¹ y) = y := by
  have h1 : Formalism.L2.Theta.mt T h * Formalism.L2.Theta.mt T h⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    first
      | rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
      | simp
  unfold actO
  simp [← Matrix.mul_assoc, h1]

end GlobalTheory.CosDual
end
end

