module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReduction
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD

theorem pure_step {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) :
    ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
      (y : MvPolynomial (Fin N × Fin N) O) = evalPol O N Φ (x τ : MvPolynomial (Fin N × Fin N) O) ∧
      evalE O N lam P (FreeAlgebra.lift O Fab Φ) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro x
    refine ⟨r • x τ, ?_, ?_⟩
    · rw [AlgHom.commutes, Module.algebraMap_end_apply]; rfl
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, MultilinearMap.map_update_smul,
        Function.update_eq_self]
      rfl
  | grade1 p =>
    intro x
    obtain ⟨y, hy, he⟩ := hF p x
    refine ⟨y, ?_, ?_⟩
    · rw [hy]; simp [evalPol]
    · rw [FreeAlgebra.lift_ι_apply]; exact he
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ (Function.update x τ y₂)
    refine ⟨y₁, ?_, ?_⟩
    · rw [hy₁, Function.update_self, hy₂, map_mul, Module.End.mul_apply]
    · rw [map_mul, map_mul, Module.End.mul_apply, he₂, he₁, Function.update_idem]
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [Submodule.coe_add, hy₁, hy₂, map_add (f := _), LinearMap.add_apply]
    · rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, he₁, he₂, MultilinearMap.map_update_add]

theorem scalar_of {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) (c : O)
    (hΦ : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), evalPol O N Φ f = c • f) :
    evalE O N lam P (FreeAlgebra.lift O Fab Φ) = c • (1 : Module.End O (NablaT O N lam)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  obtain ⟨y, hy, he⟩ := pure_step τ lam P Fab hF Φ x
  have hyc : y = c • x τ := Subtype.ext (by rw [hy, hΦ _ (x τ).2]; rfl)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, he, hyc,
    MultilinearMap.map_update_smul, Function.update_eq_self]
  simp

def evalA (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] alg O N lam :=
  FreeAlgebra.lift O (Sum.elim (grpA O N lam) fun p =>
    ⟨P p.1 p.2, Algebra.subset_adjoin (Or.inr ⟨p.1, p.2, hP p.1 p.2⟩)⟩)

theorem evalA_coe (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ((evalA O N lam P hP Φ : alg O N lam) : Module.End O (NablaT O N lam)) = evalE O N lam P Φ := by
  have h : (alg O N lam).val.comp (evalA O N lam P hP) = evalE O N lam P := by
    apply FreeAlgebra.hom_ext
    funext p
    rcases p with g | p
    · simp [evalA, evalE, grpA]
    · simp [evalA, evalE]
  exact DFunLike.congr_fun h Φ

theorem compat {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam mu : ι → ℕ → ℕ} {ϖ : O}
    {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Q : ι → (Fin N → ℕ) → Module.End O (NablaT O N mu)) (hQ : ∀ σ w, IsProj O N mu σ w (Q σ w))
    (ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))))
    (h2 : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z)
    (h3 : ∀ g z y, ψ z = Submodule.Quotient.mk y →
      ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y))
    (h4 : ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a →
      IsProj O N mu τ w a' → ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ∀ z y, ψ z = Submodule.Quotient.mk y →
      ψ (evalA O N lam P hP Φ • z) = Submodule.Quotient.mk (evalE O N mu Q Φ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro z y h
    rw [AlgHom.commutes, AlgHom.commutes, h2, h, Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
  | grade1 p =>
    intro z y h
    rcases p with g | ⟨σ, w⟩
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inl]; exact h3 g z y h
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      exact h4 σ w _ (Q σ w) (hP σ w) (hQ σ w) z y h
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_mul, map_mul, mul_smul, Module.End.mul_apply]
    exact h₁ _ _ (h₂ z y h)
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_add (f := _), map_add (f := _), add_smul, map_add (f := _), LinearMap.add_apply, h₁ z y h, h₂ z y h, Submodule.Quotient.mk_add]

theorem dvd_of_smul_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type}
    [AddCommGroup V] [Module O V] {ϖ : O} (hϖ : Irreducible ϖ) (d : O) (y : V)
    (hne : (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) ≠ 0)
    (h0 : d • (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) = 0) : ϖ ∣ d := by
  by_contra hd
  have hu : IsUnit d := by
    by_contra hnu
    have hm : d ∈ IsLocalRing.maximalIdeal O := hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
    exact hd hm
  obtain ⟨u, rfl⟩ := hu
  apply hne
  have h1 := congrArg (fun q => (↑u⁻¹ : O) • q) h0
  simpa [smul_smul] using h1

theorem int_dvd_of {O : Type} [CommRing O] {ϖ : O} (hϖ : ¬ IsUnit ϖ) {l : ℕ} (hl : l.Prime)
    (hϖl : ϖ ∣ (l : O)) (d : ℤ) (hd : ϖ ∣ (d : O)) : (l : ℤ) ∣ d := by
  by_contra h
  have hc : IsCoprime (l : ℤ) d := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h' : Nat.Coprime l d.natAbs := (Nat.Prime.coprime_iff_not_dvd hl).2 (fun h' => h (Int.natCast_dvd.2 h'))
    simpa [Int.gcd] using h'
  obtain ⟨u, v, huv⟩ := hc
  have h1 : ϖ ∣ ((u * l + v * d : ℤ) : O) := by
    push_cast
    exact dvd_add (dvd_mul_of_dvd_right hϖl _) (dvd_mul_of_dvd_right hd _)
  rw [huv, Int.cast_one] at h1
  exact hϖ (isUnit_of_dvd_one h1)


set_option synthInstance.maxHeartbeats 400000 in
theorem linkage : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ →
    ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) →
    ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm →
    Embeds O N lam mu ϖ Gm → ∀ τ,
    (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
      ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  intro O _ _ _ _ N ι _ _ lam mu l ϖ hl hϖ hϖl hlam hmu Gm _ _ _ hSub hEmb τ
  obtain ⟨U, π, hπ, -⟩ := hSub
  obtain ⟨ψ, hψ, h2, h3, h4⟩ := hEmb
  choose P hP _ using fun σ w => _root_.GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam σ w
  choose Q hQ _ using fun σ w => _root_.GlobalTheory.ExpFrame.exists_unique_isProj O N ι mu σ w
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ c : Fin N, lam τ c + ∑ c : Fin N, mu τ c := ⟨_, rfl⟩
  choose Fab hFab using fun p : Fin N × Fin N => _root_.GlobalTheory.PolarFormula.polar_formula O N ι τ M p.1 p.2
  obtain ⟨Fk, hFk⟩ := _root_.GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl O N
  have hscal : ∀ (nu : ι → ℕ → ℕ) (R : ι → (Fin N → ℕ) → Module.End O (NablaT O N nu)),
      (∀ σ, Antitone (res N (nu σ))) → (∀ σ w, IsProj O N nu σ w (R σ w)) → ∑ c : Fin N, nu τ c ≤ M → ∀ k,
      evalE O N nu R (FreeAlgebra.lift O Fab (Fk k)) =
        (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • 1 := by
    intro nu R hnu hR hb k
    apply scalar_of τ nu R Fab (fun p x => hFab p nu R hnu hR hb x)
    intro f hf
    exact hFk (res N (nu τ)) (hnu τ) f hf k
  obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
  obtain ⟨u, rfl⟩ := hπ z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (ψ (π u))
  have hne : (Submodule.Quotient.mk y : NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))) ≠ 0 := by
    rw [hy]; intro h; apply hz; apply hψ; rw [h, map_zero]
  have key : ∀ k, ϖ ∣ ((((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k -
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ)) : O) := by
    intro k
    apply dvd_of_smul_eq_zero hϖ _ y hne
    have hL := hscal lam P hlam hP (by omega) k
    have hMu := hscal mu Q hmu hQ (by omega) k
    have hc := compat P hP Q hQ ψ h2 h3 h4 (FreeAlgebra.lift O Fab (Fk k)) (π u) y hy.symm
    have hA : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • π u =
        algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • π u := by
      have hu' : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • u =
          algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • u := by
        apply Subtype.ext
        change ((evalA O N lam P hP _ : alg O N lam) : Module.End O _) (u : NablaT O N lam) =
          ((algebraMap O (alg O N lam) _ : alg O N lam) : Module.End O _) (u : NablaT O N lam)
        rw [evalA_coe, hL, LinearMap.smul_apply, Module.End.one_apply, Subalgebra.coe_algebraMap,
          Module.algebraMap_end_apply]
      rw [← π.map_smul, hu', π.map_smul]
    rw [hA, h2, hMu, ← hy] at hc
    rw [Int.cast_sub, sub_smul, sub_eq_zero, hc]
    simp [Submodule.Quotient.mk_smul]
  have hmap : ∀ nu : ι → ℕ → ℕ,
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
        (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).map (Int.castRingHom (ZMod l)) := by
    intro nu; simp [Polynomial.map_prod]
  rw [hmap lam, hmap mu]
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_map, eq_intCast, eq_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub]
  exact dvd_neg.2 (int_dvd_of hϖ.not_isUnit hl hϖl _ (key k))

end GlobalTheory.CapelliLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberIntegralFrameEq
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdReadFrame

theorem row_mul {R : Type} [CommRing R] {P Q : R → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → Q y → P (x * y)) {b a : ℕ} {Y : Matrix (Fin b) (Fin a) R} {K : Matrix (Fin a) (Fin a) R}
    (hK : ∀ i j, Q (K i j)) {i : Fin b} (h : ∀ j, P (Y i j)) (j : Fin a) : P ((Y * K) i j) := by
  rw [Matrix.mul_apply]
  exact Finset.sum_induction _ P hadd h0 fun l _ => hmul _ _ (h l) (hK l j)

theorem row_mul_iff {R : Type} [CommRing R] {P Q : R → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → Q y → P (x * y)) {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) {β : GL (Fin a) R}
    (hK : ∀ i j, Q (β.val i j)) (hK' : ∀ i j, Q ((β⁻¹).val i j)) (i : Fin b) :
    (∀ j, P ((Y * β.val) i j)) ↔ ∀ j, P (Y i j) := by
  refine ⟨fun h j => ?_, fun h j => row_mul h0 hadd hmul hK h j⟩
  have h1 := row_mul h0 hadd hmul hK' h j
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1

theorem topL_mul {R : Type} [CommRing R] {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) (K : Matrix (Fin a) (Fin a) R) :
    topL a (Y * K) = topL a Y * K := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : i.val < b
  · simp [topL, h, Matrix.mul_apply]
  · simp [topL, h]

theorem one_inv_mul {R : Type} [CommRing R] {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) :
    ((1 : GL (Fin b) R)⁻¹).val * Y = Y := by
  rw [inv_one, Units.val_one, Matrix.one_mul]

variable {D : D7}

theorem inId_zero (I : Ideal (𝓞 D.host.E)) : InId (D := D) I 0 := ⟨zero_mem _, Ideal.zero_mem _⟩

theorem inId_add {I : Ideal (𝓞 D.host.E)} (x y : EAf D) (hx : InId I x) (hy : InId I y) : InId I (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩

theorem inId_mul {I : Ideal (𝓞 D.host.E)} (x y : EAf D) (hx : InId I x)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : InId I (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  exact ⟨mul_mem h1 hy, Ideal.mul_mem_right (⟨y, hy⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _ h2⟩

theorem frMapO_one (S T : HSp D) (β : GL (Fin S.rank) (EAf D)) (t : WO S T) :
    frMapO S T β 1 t = HMul.hMul (Matrix.of fun i j => toEAf D (t i j) : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) β.val := by
  unfold frMapO
  rw [one_inv_mul]
  rfl

theorem stdFst_frame : ∀ {D : D7} (S T : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) (β : GL (Fin S.rank) (EAf D)),
  IsIntM β.val → IsIntM (β⁻¹).val → ∀ t : WO S T, stdFst ν e 𝔪 S T β 1 t =
    if IsHalf e t ∧ (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
        ∀ i j, S.rank ≤ i.1 → InId 𝔪 (toEAf D (t i j)) then
      unitChar ν e (HMul.hMul (topL S.rank (Matrix.of fun i j => toEAf D (t i j))) β.val) else 0 := by
  intro D S T ν e 𝔪 β hβ hβ' t
  unfold stdFst
  rw [frMapO_one, topL_mul]
  refine if_congr (and_congr_right fun _ => and_congr ?_ ?_) rfl rfl
  · exact forall_congr' fun i => row_mul_iff (P := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (Q := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (zero_mem _) (fun _ _ => add_mem) (fun _ _ => mul_mem)
      (Matrix.of fun i j => toEAf D (t i j)) hβ hβ' i
  · refine forall_congr' fun i => ?_
    have h := row_mul_iff (P := InId (D := D) 𝔪) (Q := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (inId_zero 𝔪) inId_add inId_mul (Matrix.of fun i j => toEAf D (t i j)) hβ hβ' i
    exact ⟨fun H j hi => h.1 (fun l => H l hi) j, fun H j hi => h.2 (fun l => H l hi) j⟩

end GlobalTheory.StdReadFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCharacterRationalValues
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.LevVal

theorem envV_chi_mem {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.Char F)
    (j : Fin D.R.m) (t : T0) (k : (GlobalTheory.TraceIncl.envV R j t).J) :
    ∃ a : D.what₂.LL, D.what₂.embLL a = (((GlobalTheory.TraceIncl.envV R j t).χ k : ℂˣ) : ℂ) := by
  obtain ⟨a, ha⟩ := hχ_of R j t
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.ConjForms.chi_mem R h.grp.chiW j PP hP u; ⟨a, ha.symm⟩)
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.PinsOverField.xiR_mem R h.lev h.fam t PP hP u; ⟨a, ha.symm⟩) k
  exact ⟨a, ha.symm⟩

end GlobalTheory.BigOn.LevVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.ClassScalarIntegral


set_option maxHeartbeats 1000000 in
theorem class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM hLN hΛ e Ps yd hh he hPs hs hy hcard a ha lam hTl
  have lemL1 := GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral
  have lemHV := _root_.GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId
  have lemCC := _root_.GlobalTheory.DetIdealPrime.exists_ideal_coprime
  have lemPSI := GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified
  obtain ⟨ψ, b, I, _, φs, n, hb0, hbP, hc, hu, hr, htame, hinf⟩ :=
    lemPSI D G Pl0 T0 A T R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM
      hLN hΛ e Ps yd hh he hPs
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime lam
  obtain ⟨cc, c0, cb, cl, cv⟩ := lemCC D (Vc D i) hO.2.lift.std.1 hO.2.lift.std.2 h e Ps yd he hs hy b hbP _ ψ hc hu hr Λ hΛ
    (Formalism.EigenvalueLevelCeiling.plc lam) hp hTl
  obtain ⟨K, hK1⟩ := lemHV D.host.E ψ I φs n hinf htame b hb0 hu cc c0 cb
  obtain ⟨m, hm, hm1⟩ := lemL1 D T hT ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Λ (O i).s0 (Formalism.EigenvalueLevelCeiling.plc lam) hp hU hTb hTl
  refine ⟨((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL), ?_, ?_⟩
  · intro hmem
    have hco : Nat.Coprime (m * Ideal.absNorm cc ^ K) (Formalism.EigenvalueLevelCeiling.plc lam) := Nat.Coprime.mul_left hm (Nat.Coprime.pow_left _ cl)
    have h1 : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem lam
    obtain ⟨u, w, huw⟩ : IsCoprime ((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL) ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) :=
      Nat.Coprime.cast hco
    exact lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huw ▸ lam.asIdeal.add_mem (lam.asIdeal.mul_mem_left _ hmem) (lam.asIdeal.mul_mem_left _ h1)))
  · have hinj : Function.Injective D.what₂.embLL.toIntAlgHom := D.what₂.embLL.injective
    refine (isIntegral_algHom_iff _ hinj).1 ?_
    have e1 : D.what₂.embLL.toIntAlgHom (((((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL)) : D.what₂.LL) * a) =
        ((m : ℂ) * ((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹) *
        (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ)) *
        ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) := by
      rw [RingHom.toIntAlgHom_apply, map_mul, ha, ← cv]
      push_cast
      rw [map_mul, map_pow, map_natCast, map_natCast]
      ring
    rw [e1]
    refine (hm1.mul hK1).mul ?_
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Nat.cast_pow, Complex.ofReal_natCast]
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ D.R.r : ℕ) : ℤ)))

end GlobalTheory.ClassScalarIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMem
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem pull_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  intro E _ _ _ r U C _ _ M la F h hF c
  have hm : GlobalTheory.LevelCusp.IsMatch (M.comp c).toData (M.comp (h • c)).toData (M.tr h c) :=
    { psi := (M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm
      p0 := (M.comp_basePoint c).trans (M.comp_basePoint (h • c)).symm
      xi := (M.comp_ξ0 c).trans (M.comp_ξ0 (h • c)).symm
      iso := fun u v => by
        show herm (M.comp (h • c)).Gm _ _ = herm (M.comp c).Gm u v
        rw [M.comp_Gm, M.comp_Gm]
        exact M.tr_herm h c u v
      lat := fun v => M.tr_Λ h c v }
  exact GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ (M.tr h c) hm (castWt (M.comp_Ψ c) la)
    (castWt (M.comp_Ψ (h • c)) la) (fun τ i => rfl) _ (fun y => F (h • c) (castFrame (M.comp_Ψ (h • c)) y)) 1
    (GlobalTheory.PullBdd.pull_isBddSec E r U C M la F hF h c).1 (hF (h • c)) (fun x _ => by rw [one_mul]; rfl)

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVWStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_tensorModelVW : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityVW.locality | exact GlobalTheory.WeilLocalityVW.locality | (intros; apply GlobalTheory.WeilLocalityVW.locality <;> assumption)
end

