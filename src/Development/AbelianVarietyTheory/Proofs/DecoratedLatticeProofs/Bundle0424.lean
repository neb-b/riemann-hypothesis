module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  first | exact @GlobalTheory.PhiOneVal.base_deco_fn | exact GlobalTheory.PhiOneVal.base_deco_fn | (intros; apply GlobalTheory.PhiOneVal.base_deco_fn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.FlatEqui

variable {D : D7}

theorem levi_mem_flagN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    d.levi u ∈ flagN d :=
  ((flag_jacobi_structure D S S₀ ρ d).1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩

theorem psiUni_mul (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u v : GL (Fin ρ) (AE D)}
    (hu : u ∈ UX D ρ) (hv : v ∈ UX D ρ) : psiUni ψ (u * v) = psiUni ψ u * psiUni ψ v := by
  have h : ∀ a, psiFlag ψ d (d.levi a) = psiUni ψ a := fun a => by
    have := psiFlag_levi_mul ψ d a (one_mem (stabX d))
    rwa [mul_one] at this
  rw [← h, ← h, ← h, map_mul, psiFlag_mul d ψ (levi_mem_flagN d hu) (levi_mem_flagN d hv)]

theorem flatBF_levi (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (om' : Om B.V₀ J.W) (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ)
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) (γ : UX D ρ) :
    flatBF s (s.om (1, J.d.levi γ.1) Ψ) = star (psiUni ψ γ.1) • flatBF s Ψ := by
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  have he := (_root_.GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).2
  simp only [flatBF, flat, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, he]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ γ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [inv_mul_cancel_left]
  rw [Subgroup.coe_mul, psiUni_mul ψ J.d γ.2 u.2, star_mul', mul_assoc]

theorem flatBF_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom Ψ hΨ h₀ n hn h'
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc]
  rw [e, flatBF_levi ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΨ) ⟨γ, hγ⟩,
    GlobalTheory.T.besselToJacobiFlat_weilRepresentation_cores D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h', psiFlag_levi_mul ψ J.d γ (radX_le_stabX J.d hr), opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]

end GlobalTheory.FlatEqui

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterLocalUnitaryGroupFinitePlaceScalar
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CenterLocU

open Matrix Formalism.UG

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_add' (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem cT_sub' (σ : A →+* A) (M N : Matrix n n A) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem cT_smul' (σ : A →+* A) (c : A) (M : Matrix n n A) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

theorem cT_cT' (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cayley_unitary (σ : A →+* A) (J B V : Matrix n n A) (s : A) (hs : σ s = s)
    (hB : cT σ B * J + J * B = 0) (hV1 : (s • (1 : Matrix n n A) - B) * V = 1) :
    cT σ ((s • (1 : Matrix n n A) + B) * V) * J * ((s • (1 : Matrix n n A) + B) * V) = J := by
  set S : Matrix n n A := s • (1 : Matrix n n A) with hSdef
  have hS : cT σ S = S := by rw [hSdef, cT_smul', cT_one, hs]
  have hc : ∀ M : Matrix n n A, S * M = M * S := fun M => by
    rw [hSdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have key : cT σ (S + B) * J * (S + B) = cT σ (S - B) * J * (S - B) := by
    rw [cT_add', cT_sub', hS]
    have e1 : (S + cT σ B) * J * (S + B) - (S - cT σ B) * J * (S - B)
        = (S * J * B + cT σ B * J * S) + (S * J * B + cT σ B * J * S) := by noncomm_ring
    have e2 : S * J * B + cT σ B * J * S = 0 := by
      rw [Matrix.mul_assoc (cT σ B) J S, ← hc J, ← Matrix.mul_assoc, ← hc (cT σ B),
        Matrix.mul_assoc S J B, Matrix.mul_assoc S (cT σ B) J, ← Matrix.mul_add, add_comm, hB, Matrix.mul_zero]
    rw [e2, add_zero] at e1
    exact sub_eq_zero.1 e1
  calc cT σ ((S + B) * V) * J * ((S + B) * V) = cT σ V * (cT σ (S + B) * J * (S + B)) * V := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ V * (cT σ (S - B) * J * (S - B)) * V := by rw [key]
    _ = cT σ ((S - B) * V) * J * ((S - B) * V) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hV1, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem comm_of_comm_cayley (g B V : Matrix n n A) (s : A) (h2s : IsUnit (2 * s))
    (hV1 : (s • (1 : Matrix n n A) - B) * V = 1) (hV2 : V * (s • (1 : Matrix n n A) - B) = 1)
    (hg : g * ((s • (1 : Matrix n n A) + B) * V) = ((s • (1 : Matrix n n A) + B) * V) * g) :
    g * B = B * g := by
  have e : s • (1 : Matrix n n A) + B = (2 * s) • (1 : Matrix n n A) - (s • (1 : Matrix n n A) - B) := by
    rw [two_mul, add_smul]; abel
  rw [e, Matrix.sub_mul, hV1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_left_inj] at hg
  have hgV : g * V = V * g := by
    have := congrArg (fun M => (↑h2s.unit⁻¹ : A) • M) hg
    simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
    exact this
  have hU : (s • (1 : Matrix n n A) - B) * g = g * (s • (1 : Matrix n n A) - B) := by
    calc (s • (1 : Matrix n n A) - B) * g
        = (s • (1 : Matrix n n A) - B) * g * (V * (s • (1 : Matrix n n A) - B)) := by rw [hV2, Matrix.mul_one]
      _ = (s • (1 : Matrix n n A) - B) * (g * V) * (s • (1 : Matrix n n A) - B) := by simp only [Matrix.mul_assoc]
      _ = (s • (1 : Matrix n n A) - B) * (V * g) * (s • (1 : Matrix n n A) - B) := by rw [hgV]
      _ = ((s • (1 : Matrix n n A) - B) * V) * g * (s • (1 : Matrix n n A) - B) := by simp only [Matrix.mul_assoc]
      _ = g * (s • (1 : Matrix n n A) - B) := by rw [hV1, Matrix.one_mul]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    sub_right_inj] at hU
  exact hU.symm

theorem comm_of_comm_skew (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n A) (hJ : cT σ J = J)
    (hJu : IsUnit J.det) (h2 : IsUnit (2 : A)) (δ : A) (hδ : IsUnit δ) (hδσ : σ δ = -δ)
    (g : Matrix n n A) (hg : ∀ B : Matrix n n A, cT σ B * J + J * B = 0 → g * B = B * g)
    (M : Matrix n n A) : g * M = M * g := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJi : J⁻¹ = cT σ J⁻¹ := Matrix.inv_eq_left_inv (by
    have := cT_mul σ J J⁻¹
    rw [hJ, hJJ, cT_one] at this
    exact this.symm)
  have hsk : ∀ X : Matrix n n A, cT σ X = -X → g * (J⁻¹ * X) = (J⁻¹ * X) * g := fun X hX => hg _ (by
    rw [cT_mul, hX, ← hJi, neg_mul, ← neg_mul, Matrix.mul_assoc, hJJ', Matrix.mul_one, ← Matrix.mul_assoc, hJJ,
      Matrix.one_mul, neg_add_cancel])
  set Y := J * M
  have h1 := hsk (Y - cT σ Y) (by rw [cT_sub', cT_cT' σ hσ, neg_sub])
  have h2' := hsk (δ • (Y + cT σ Y)) (by rw [cT_smul', cT_add', cT_cT' σ hσ, hδσ, neg_smul, add_comm])
  have e : (2 : A) • M = J⁻¹ * (Y - cT σ Y) + (↑hδ.unit⁻¹ : A) • (J⁻¹ * (δ • (Y + cT σ Y))) := by
    rw [Matrix.mul_smul, smul_smul, IsUnit.val_inv_mul, one_smul, ← Matrix.mul_add,
      sub_add_add_cancel, ← two_smul A Y, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ', Matrix.one_mul]
  have h3 : g * ((2 : A) • M) = ((2 : A) • M) * g := by
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2']
  rw [Matrix.mul_smul, Matrix.smul_mul] at h3
  have := congrArg (fun N => (↑h2.unit⁻¹ : A) • N) h3
  simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  exact this

theorem exists_nat_isUnit_sub (K : Type) [Field K] [CharZero K] [Algebra K A] [FiniteDimensional K A]
    (B : Matrix n n A) : ∃ m : ℕ, m ≠ 0 ∧ IsUnit ((m : A) • (1 : Matrix n n A) - B) := by
  let L : Module.End K (n → A) := (Matrix.mulVecLin B).restrictScalars K
  have hfin : {m : ℕ | L.HasEigenvalue (m : K)}.Finite :=
    (Module.End.finite_hasEigenvalue L).preimage Nat.cast_injective.injOn
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, by omega, ?_⟩
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  let T : Module.End K (n → A) :=
    (Matrix.mulVecLin (((N + 1 : ℕ) : A) • (1 : Matrix n n A) - B)).restrictScalars K
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hT : (((N + 1 : ℕ) : A) • (1 : Matrix n n A) - B) *ᵥ x = 0 := hx
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hT
    have hev : L.HasEigenvalue ((N + 1 : ℕ) : K) := by
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx0⟩
      rw [Module.End.mem_eigenspace_iff]
      show B *ᵥ x = ((N + 1 : ℕ) : K) • x
      rw [← hT, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    have := hN hev
    omega
  exact LinearMap.injective_iff_surjective.1 hinj

end Gen

end GlobalTheory.CenterLocU

namespace GlobalTheory.CenterLocU
open Matrix Formalism.UG

section Gen2

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem scalar_of_comm_UJ (K : Type) [Field K] [CharZero K] [Algebra K A] [FiniteDimensional K A]
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n A) (hJ : cT σ J = J) (hJu : IsUnit J.det)
    (δ : A) (hδ : IsUnit δ) (hδσ : σ δ = -δ) (g : Matrix n n A)
    (hg : ∀ h ∈ UJ σ J, g * (h : Matrix n n A) = (h : Matrix n n A) * g) :
    ∃ c : A, g = c • (1 : Matrix n n A) := by
  have h2 : IsUnit (2 : A) := by
    have : (2 : A) = algebraMap K A 2 := (map_ofNat (algebraMap K A) 2).symm
    rw [this]; exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  have hskew : ∀ B : Matrix n n A, cT σ B * J + J * B = 0 → g * B = B * g := by
    intro B hB
    obtain ⟨m, hm, hU⟩ := exists_nat_isUnit_sub K B
    have hUd := (Matrix.isUnit_iff_isUnit_det _).1 hU
    have hV1 : ((m : A) • (1 : Matrix n n A) - B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hUd
    have hV2 : ((m : A) • (1 : Matrix n n A) - B)⁻¹ * ((m : A) • (1 : Matrix n n A) - B) = 1 :=
      Matrix.nonsing_inv_mul _ hUd
    have hC := cayley_unitary σ J B _ (m : A) (map_natCast σ m) hB hV1
    have hWC : (J⁻¹ * cT σ (((m : A) • (1 : Matrix n n A) + B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹) * J) *
        (((m : A) • (1 : Matrix n n A) + B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hC, Matrix.nonsing_inv_mul J hJu]
    let Cu : GL n A := ⟨_, _, mul_eq_one_comm.1 hWC, hWC⟩
    have hCm : Cu ∈ UJ σ J := hC
    have h2m : IsUnit (2 * (m : A)) := by
      have : (2 * (m : A)) = algebraMap K A (2 * m) := by rw [map_mul, map_ofNat, map_natCast]
      rw [this]; exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hm))).map _
    exact comm_of_comm_cayley g B _ (m : A) h2m hV1 hV2 (hg Cu hCm)
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := g)
    (fun i j _ => (comm_of_comm_skew σ hσ J hJ hJu h2 δ hδ hδσ g hskew _).symm)
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end Gen2

end GlobalTheory.CenterLocU

namespace GlobalTheory.CenterLocU

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_anti (D : D7) : ∃ e : D.host.E, D.sp.cm.sig e = -e ∧ e ≠ 0 := by
  have hx : ∃ x : D.host.E, x ∉ Set.range (algebraMap D.host.F D.host.E) := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 (h x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
    rw [D.sp.cm.deg2] at this
    norm_num at this
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - star x, ?_, ?_⟩
  · show star (x - star x) = -(x - star x)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    exact hx (RingHom.mem_range.1 ((D.sp.cm.fixed x).1 (sub_eq_zero.1 h0).symm))

theorem center_scalar_loc : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v), g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) → ∃ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram g).1 = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D V v g hg
  have hσ : ∀ x : D.host.E, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  obtain ⟨e, he, he0⟩ := exists_anti D
  have hJ : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (JR (Fv D.host.F v) V.gram) =
      JR (Fv D.host.F v) V.gram := by
    ext i j
    exact congrArg (inclR (Fv D.host.F v)) (V.herm.eq (V.frame j) (V.frame i))
  have hδσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig (inclR (Fv D.host.F v) e) =
      -inclR (Fv D.host.F v) e := by
    show inclR (Fv D.host.F v) (D.sp.cm.sig e) = _
    exact (congrArg _ he).trans (map_neg _ _)
  have hgc : ∀ h ∈ Formalism.UG.UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (JR (Fv D.host.F v) V.gram),
      ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) * (h : Matrix (Fin V.rank) (Fin V.rank) _) =
        (h : Matrix (Fin V.rank) (Fin V.rank) _) * ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) := by
    intro h hh
    let h' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v := ⟨h, hh⟩
    have e1 := congrArg (fun x => (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram x).1)
      (Subgroup.mem_center_iff.1 hg h')
    simp only [map_mul, Units.val_mul] at e1
    exact e1.symm
  exact scalar_of_comm_UJ (Fv D.host.F v)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (GlobalTheory.Doubling.sigR_invol hσ)
    (JR (Fv D.host.F v) V.gram) hJ
    (GlobalTheory.Doubling.isUnit_det_JR (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero)
    (inclR (Fv D.host.F v) e) ((isUnit_iff_ne_zero.2 he0).map _) hδσ
    ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) hgc

end GlobalTheory.CenterLocU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnLevelIffRowLatticeKeptAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LevRow


open GlobalTheory.FinPl.OrbitCoset in
theorem embA_mem_grpAt {D : D7} {S S₀ A B : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A B) (P : GlobalTheory.FinPl.Pl D → Prop)
    {a : GA D A} (ha : a ∈ grpAt A P) : embA d o a ∈ grpAt S P :=
  wittCoreEmbedding_mem_supportedSubgroup d P (emb_mem_grpAt' o ha)

theorem levrow : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ v : GlobalTheory.FinPl.Pl D, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ a ∈ grpAt (D.sp.X 0) (· = v), ∃ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 ∧ ((y : GL _ _) ∈ F.cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o (a₀ * a * a₀⁻¹)) (latS D) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hE hLev hAd hH v hv a ha
  obtain ⟨y, hy⟩ := GlobalTheory.AdForm.RdVal.finM_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) rfl a
  refine ⟨y, hy.symm, ?_⟩
  have hRep := GlobalTheory.Core.Mi.FinFrame.repM_toH D X h u ψ B F tr hE hAd (a₀ * a * a₀⁻¹)
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ =
      (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH.2
  have hh0 : ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
      (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hfa : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ =
      ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ = 1 := by
      rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
    calc _ = (((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ := by rw [e0, hh0, one_mul]
      _ = _ := by rw [mul_assoc, h1, mul_one]
  have hfg : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a₀ * a * a₀⁻¹) =
      ((tr.h0 * y * tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine (unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans ((congrArg₂ (· * ·) ((unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans (congrArg₂ (· * ·) e0 hy.symm)) hfa).trans ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hRF : Formalism.L2.SG.ColDict.RepF X tr.wt tr.ιA ((B.toH (a₀ * a * a₀⁻¹)).2 : X.B.I.Gf) (tr.h0 * y * tr.h0⁻¹) := by
    have h' := hRep
    rw [hfg] at h'
    exact h'
  obtain ⟨hmemIff, -⟩ := hLev.2 (B.toH (a₀ * a * a₀⁻¹)).2 _ hRF
  have hconj : tr.h0⁻¹ * (tr.h0 * y * tr.h0⁻¹) * tr.h0 = y := by group
  rw [hconj] at hmemIff
  rw [← hmemIff]
  have hk : a₀ * a * a₀⁻¹ ∈ grpAt (D.sp.X 0) (· = v) :=
    by
      have hN : (grpAt (D.sp.X 0) (· = v)).Normal := by unfold grpAt GlobalTheory.FinPl.congGrp; infer_instance
      exact hN.conj_mem a ha a₀
  have hκ : embA B.d B.o (a₀ * a * a₀⁻¹) ∈ grpAt (D.sp.Y 0) (· = v) := embA_mem_grpAt B.d B.o _ hk
  have hKs := _root_.GlobalTheory.Core.Mi.KsetAt.mem_Kset_iff_moves X h v _ hκ
  change (X.xu u)⁻¹ * (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 * X.xu u ∈ X.K2 ↔ _
  rw [← hKs]
  constructor
  · intro h2
    have h3 : (X.xu u)⁻¹ * (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 * X.xu u ∈ X.B.I.Kset := h2.1
    have h4 := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (X.xu_K u) h3)
      (Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I (X.xu_K u))
    have e : X.xu u * ((X.xu u)⁻¹ * (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 * X.xu u) * (X.xu u)⁻¹ =
        (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 := by group
    rw [e] at h4
    exact h4
  · intro h2
    refine ⟨?_, _root_.GlobalTheory.Core.Mi.KTwoAwayLevel.k2cong_conj_of_grpAt X h u v hv _ hκ h2⟩
    exact Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I
      (Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I (X.xu_K u)) h2) (X.xu_K u)

end GlobalTheory.Core.Mi.LevRow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.QStep

theorem gl₂_embX_eq_embA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  intro D ψ σ S Q g
  obtain ⟨a₀, ha⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (ofSplit Q.q) Q.F.F₂ g
  exact ⟨a₀, GlobalTheory.LocGrp.isLoc_unique (ofSplit Q.q)
    (GlobalTheory.NormalFramePeriod.isLoc_embA (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' ha) (Q.loc₂ _), ha⟩

end GlobalTheory.QPl.QStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QSuppTwo.main | exact GlobalTheory.QSuppTwo.main | (intros; apply GlobalTheory.QSuppTwo.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleOfSupportedRankOneUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOneIdele_of_supported_rankOneUnitary : ∀ (D : D7) (L : HSp D) (v : GlobalTheory.FinPl.Pl D) (γ : GA D L), L.rank = 1 → γ ∈ grpAt L (· = v) → ∃ c : AE D, NormOneAt v c ∧ NormOneAt v (cA D c) ∧ Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_of_rank_one | exact GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_of_rank_one | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_of_rank_one <;> assumption)
end

