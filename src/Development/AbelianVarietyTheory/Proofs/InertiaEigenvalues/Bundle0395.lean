module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrameStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := by
  first | (exact @GlobalTheory.BcrisInv.invariant_unit) | (exact GlobalTheory.BcrisInv.invariant_unit) | (intros; apply GlobalTheory.BcrisInv.invariant_unit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

section Reg

variable {H : Type} [Group H] [Fintype H]

theorem sum_irr_coeff (h : H) :
    ∑ σ ∈ (irr_finite_and_finsum_zOf_eq_one H).1.toFinset, (zOf σ).coeff h = if h = 1 then 1 else 0 := by
  obtain ⟨hfin, hsum⟩ := irr_finite_and_finsum_zOf_eq_one H
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have e := congrArg (fun z : MonoidAlgebra ℂ H => z.coeff h) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at e
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hh : h = 1
  · simp [hh]
  · simp [hh, Ne.symm hh]

theorem exists_irr_sum_ne_zero (F : H → ℂ) (hF : F 1 ≠ 0) :
    ∃ σ : H → ℂ, IsIrr σ ∧ ∑ h, F h * σ h⁻¹ ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hF
  set s := (irr_finite_and_finsum_zOf_eq_one H).1.toFinset with hs
  have h0 : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [hc σ (by simpa [hs] using hσ), mul_zero]
  rw [← h0]
  have e : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ =
      ∑ h, F h * ∑ σ ∈ s, (zOf σ).coeff h := by
    simp_rw [Finset.mul_sum, ZSumOne.zOf_coeff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e, hs]
  simp_rw [sum_irr_coeff]
  simp

end Reg

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isIrr {n : ℕ} {ψ : Gn g n → ℂ} (hψ : IsIrr ψ) : IsClass ψ := by
  obtain ⟨V, _, hV⟩ := hψ
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_hc_eq_left (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ h : Gn g a, (∑ y : Gn g b, res a b χ h y * β y⁻¹) * α h⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem ip_hc_eq_right (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ y : Gn g b, (∑ h : Gn g a, res a b χ h y * α h⁻¹) * β y⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem thetaInv_det_inv (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ) = ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  simp [map_inv]

end GlobalTheory.GLq.HCFrobWeight

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

theorem exists_irr_hc_thetaInv : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  intro g _ n ψ hψ θ
  have hcl := isClass_of_isIrr hψ
  constructor
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun h : Gn g n => ∑ y : Gn g 1, res n 1 ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_left n 1 (n + 1) rfl ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun y : Gn g n => ∑ h : Gn g 1, res 1 n ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det h⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_right 1 n (n + 1) (by omega) ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne

end GlobalTheory.GLq.HCFrobWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLambdaAlgebraHomEvaluation
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LamHom

def chr {B ι : Type} [CommRing B] [Fintype ι] {n : ℕ} [NeZero n] (u : ι → B) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* B := GlobalTheory.RootCharacter.rootChar u hu

theorem chr_single {B ι : Type} [CommRing B] [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (hn : 1 < n) (u : ι → B)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : chr u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  haveI : Fact (1 < n) := ⟨hn⟩
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem exists_lamHom : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (B : Type) [CommRing B] [Algebra (X.O0 i) B] (ξ : ι → B), 0 < nu X i → nu X i + 1 ≤ M → Kills i B → (∀ q, ξ q ^ X.l i ^ (M - nu X i - 1) = 0) → ∃ φ : abelian₂ X i M ι →ₐ[X.O0 i] B, (∀ F, φ (toLam X i M ι F) = MvPolynomial.aeval ξ F) ∧ ∀ d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))), ∃ κ : GE N →* Bˣ, (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) ∧ IsChar i κ ξ d := by
  intro D N X i M ι _ B _ _ ξ _ hM hK hξ
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hm : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have h4 : ((X.l i : ℕ) : B) ^ (nu X i + 1) = 0 := by
    have h := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm)
    rw [map_mul, map_pow, map_natCast] at h
    rw [pow_succ]
    exact h
  have hn : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + ξ q) ^ (X.l i ^ M) = 1 := fun q =>
    KStar.Tree.one_add_pow_prime_pow_eq_one hp h4 hM (hξ q)
  let φ : abelian₂ X i M ι →ₐ[X.O0 i] B := MonoidAlgebra.lift (X.O0 i) B (Del X i M ι) (chr (fun q => 1 + ξ q) hu)
  have hφ : ∀ x, φ (MonoidAlgebra.of (X.O0 i) (Del X i M ι) x) = chr (fun q => 1 + ξ q) hu x := fun x =>
    MonoidAlgebra.lift_of _ x
  refine ⟨φ, fun F => ?_, fun d => ⟨(Units.map (φ : abelian₂ X i M ι →* B)).comp (delInv i M d), fun g => rfl, fun g => ?_⟩⟩
  · have : φ.comp (toLam X i M ι) = MvPolynomial.aeval ξ := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sub, map_one, hφ]
      have := chr_single hn (fun q => 1 + ξ q) hu q
      rw [sub_eq_iff_eq_add']
      convert this
    exact DFunLike.congr_fun this F
  · have h1 : ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) *
        MonoidAlgebra.of (X.O0 i) (Del X i M ι) (delAll X i M d g) = 1 :=
      Units.inv_mul ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits (delAll X i M d g))
    have h2 := congrArg φ h1
    rw [map_mul, map_one, hφ] at h2
    exact h2

end GlobalTheory.NewPrime.LamHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  first | (exact @GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (exact GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (intros; apply GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroSmulMemOfSpanEqTop
section
namespace GlobalTheory.QuotientLatticeTorsion

theorem exists_ne_zero_smul_mem_of_span_eq_top
    {O K V : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (N : Submodule O V) (hN : Submodule.span K (N : Set V) = ⊤) (v : V) :
    ∃ b : O, b ≠ 0 ∧ b • v ∈ N := by
  have hv : v ∈ Submodule.span K (N : Set V) := hN ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hax
    · rw [mul_smul]
      exact N.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨s.1 * a, mul_ne_zero (nonZeroDivisors.ne_zero s.2) ha, ?_⟩
    have key : (s.1 * a) • c • x = r • a • x := by
      rw [← algebraMap_smul K (s.1 * a), ← algebraMap_smul K r, ← algebraMap_smul K a x,
        smul_smul, smul_smul, ← hrs, map_mul]
      congr 1
      ring
    rw [key]
    exact N.smul_mem r hax

theorem quotient_lattice_torsion
    {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {LL : Type} [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsDomain O]
    [IsFractionRing O LL] (T : Formalism.BasicNotions.LocLat G Qp LL O)
    (w : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) :
    ∃ (b : O), b ≠ (0 : O) ∧
      b • w = (0 : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨b, hb, hbv⟩ :=
    exists_ne_zero_smul_mem_of_span_eq_top (K := LL) T.L.T T.L.span v
  refine ⟨b, hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hbv

end GlobalTheory.QuotientLatticeTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

theorem sh_le_sh_nsmul {l : ℕ} [Fact l.Prime] (y : Formalism.Per.Fl l) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖sh y‖ ≤ ‖sh (n • y)‖ := by
  have hn0 : (n : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set m := ((n : ZMod l)⁻¹).val with hm
  have hmnZ : ((m * n : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast
    rw [hm, ZMod.natCast_zmod_val, inv_mul_cancel₀ hn0]
  have hmn : ((m * n : ℕ) : Formalism.Per.Fl l) = 1 := by
    rw [← Nat.cast_one, CharP.natCast_eq_natCast (Formalism.Per.Fl l) l]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hmnZ
  have hy : y = (m : Formalism.Per.Fl l) * (n • y) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hmn, one_mul]
  have hmul : ∀ a b : Formalism.Per.Fl l, sh (a * b) = sh a * sh b := by
    intro a b; simp [sh, map_mul]
  have hle : ∀ x : Formalism.Per.Fl l, ‖sh x‖ ≤ 1 := fun x => (GlobalTheory.RingBasics.mem_OC _).1 (PreTilt.untilt x).2
  calc ‖sh y‖ = ‖sh (m : Formalism.Per.Fl l)‖ * ‖sh (n • y)‖ := by
        conv_lhs => rw [hy]
        rw [hmul, norm_mul]
    _ ≤ 1 * ‖sh (n • y)‖ := mul_le_mul_of_nonneg_right (hle _) (norm_nonneg _)
    _ = ‖sh (n • y)‖ := one_mul _

theorem ev_algebraMap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (q : ℚ_[l]) :
    ev P m (algebraMap ℚ_[l] P.R.B q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [ev, ← AlgHom.coe_pow, AlgHom.commutes, AlgHom.commutes]

end GlobalTheory.PMonII

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

theorem exII : ExII := by
  intro l _ P AI T h hh lam hlam hind
  obtain ⟨S, θ, hS, hker, hQ, hser⟩ := _root_.GlobalTheory.PSer.series_residues l P AI T
  obtain ⟨-, hPev, hPring, hPq, -, -⟩ := GlobalTheory.PMon.CrisPlus.plus_props l P AI T
  have hθq : ∀ (c : ℚ_[l]) (hm : algebraMap ℚ_[l] P.R.BdR c ∈ S),
      θ ⟨_, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c := by
    intro c hm; obtain ⟨_, h'⟩ := hQ c; exact h'
  have hqS : ∀ c : ℚ_[l], algebraMap ℚ_[l] P.R.BdR c ∈ S := fun c => (hS _).2 (q_mem_Fil P c)
  have hlS : ∀ j, lam j ∈ S := fun j => (hS _).2 (hlam j)
  let μ : Fin h → ℂ_[l] := fun j => θ ⟨lam j, hlS j⟩
  have hμind : ∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0 := by
    intro c hc
    apply hind c
    have hm : ∑ j, c j • lam j ∈ S := S.sum_mem fun j _ => by
      rw [Algebra.smul_def]; exact S.mul_mem (hqS _) (hlS j)
    have he : (⟨_, hm⟩ : S) = ∑ j, (⟨_, hqS (c j)⟩ : S) * ⟨lam j, hlS j⟩ := by
      apply Subtype.ext; simp [Algebra.smul_def]
    have h0 : θ ⟨_, hm⟩ = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [he, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hθq]
    exact (hker ⟨_, hm⟩).1 h0
  obtain ⟨Pm, μ', hdet, hμ', hnorm, hanti, hlt, horth⟩ := _root_.GlobalTheory.PMonE.OrthBasis.exists_orthBasis l h μ hμind
  obtain ⟨y, j0, r, R, hr0, hr1, hR1, hyR, hyr, hy0, hzero⟩ :=
    _root_.GlobalTheory.CoreOrth.residue_zeros l h μ' hh hnorm hanti hlt horth
  have hb : ∀ k : Fin h, ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
      ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j (y k) :=
    fun k => hser h R (y k) hh hR1 (hyR k)
  choose b hbP hbφ hbθ using hb
  choose hbm hθb using hbθ

  have hbne : b j0 ≠ 0 := by
    intro h0
    have hc := _root_.GlobalTheory.PSer.Lam_indep_of_first_terms l h 1 r (fun _ => y j0) hh hr0 hr1 (fun _ k => hyr k) ?_ (fun _ => 1) ?_
    · exact one_ne_zero (congrFun hc 0)
    · intro n hn a
      by_contra hd
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      have hle := sh_le_sh_nsmul (y j0 0) (n 0) hd
      simp only [Finset.univ_unique, Finset.sum_singleton] at hn
      have : (default : Fin 1) = 0 := rfl
      rw [this] at hn
      linarith
    · intro j _
      have e : (⟨ev P j (b j0), hbm j0 j⟩ : S) = 0 := Subtype.ext (by
        simp only [h0, ZeroMemClass.coe_zero, ← evHom_apply, map_zero])
      have hL : abelian₂ h j (y j0) = 0 := by rw [← hθb j0 j, e, map_zero]
      simp [hL]
  let a : Fin h → P.R.B := fun j => ∑ k, algebraMap ℚ_[l] P.R.B (Pm k j) * b k
  have hplus0 : Plus T (0 : P.R.B) := by simpa using hPq 0
  have hev : ∀ (i : ℕ) (j : Fin h), ev P i (a j) = ∑ k, algebraMap ℚ_[l] P.R.BdR (Pm k j) * ev P i (b k) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [a, ← evHom_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evHom_apply, evHom_apply, ev_algebraMap]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  ·
    intro ha
    apply hbne
    have hinv : Pm * Pm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    have key : ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0) * a j = b j0 := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0 * Pm k j) * b k =
          algebraMap ℚ_[l] P.R.B ((Pm * Pm⁻¹) k j0) * b k := by
        intro k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
        simp only [mul_comm]
      simp only [this, hinv, Matrix.one_apply]
      simp
    rw [← key]
    simp [ha]
  · intro j
    refine Finset.sum_induction _ (Plus T) (fun x y hx hy => (hPring x y hx hy).1) hplus0 fun k _ => ?_
    exact (hPring _ _ (hPq _) (hbP k)).2
  · intro j
    simp only [a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← AlgHom.coe_pow, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, AlgHom.coe_pow, hbφ k]
    ring
  · intro i
    have hX : ∑ j, lam j * ev P i (a j) ∈ S := S.sum_mem fun j _ => S.mul_mem (hlS j) (by
      rw [hev]; exact S.sum_mem fun k _ => S.mul_mem (hqS _) (hbm k i))
    apply (hker ⟨_, hX⟩).1
    have he : (⟨_, hX⟩ : S) = ∑ j, ∑ k, (⟨lam j, hlS j⟩ : S) * ((⟨_, hqS (Pm k j)⟩ : S) * ⟨_, hbm k i⟩) := by
      apply Subtype.ext
      simp only [hev, Finset.mul_sum]
      simp
    rw [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hθq, hθb]
    rw [Finset.sum_comm]
    rw [← hzero i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hμ' k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [μ]
    ring

end GlobalTheory.PMonII
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmuller_log_unit_bcris : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  first | (exact @GlobalTheory.LogU.exists_log_unit) | (exact GlobalTheory.LogU.exists_log_unit) | (intros; apply GlobalTheory.LogU.exists_log_unit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentFreeModuleCocycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithfullyFlat_descent_free_module_cocycle : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (d : ℕ) (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)), IsUnit ε → ε.map (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) * ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) = ε.map (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)) → ∀ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i) → Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  first | exact @GlobalTheory.CocycleDescent.descent | exact GlobalTheory.CocycleDescent.descent | (intros; apply GlobalTheory.CocycleDescent.descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1ReductionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_reduction : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  first | exact @GlobalTheory.CocycleModPow.finite_H1Q_lpow | exact GlobalTheory.CocycleModPow.finite_H1Q_lpow | (intros; apply GlobalTheory.CocycleModPow.finite_H1Q_lpow <;> assumption)
end

