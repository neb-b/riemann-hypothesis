module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NullNegEvalOfJacobianDetEqZero
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open MeasureTheory Topology

namespace GlobalTheory.ChartSard

theorem null_negEv_of_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  intro X p d U ch φ
  set T : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap with hT
  have hTw : ∀ w, T w = WithLp.toLp 2 w := fun w => rfl
  set g : Fin d → EuclideanSpace ℂ (Fin d) → ℂ :=
    fun j => GlobalTheory.CxPts.ev p (RingHom.id ℂ) U (φ j) ∘ ch.e.symm with hg
  set H : (Fin d → ℂ) → (Fin d → ℂ) := fun w j => -g j (T w) with hH
  refine ⟨H '' {w | DifferentiableAt ℝ H w ∧ (fderiv ℝ H w).det = 0},
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun w => fderiv ℝ H w)
      (fun w hw => hw.1.hasFDerivAt.hasFDerivWithinAt) (fun w hw => hw.2), ?_⟩
  intro z hzs hz hdet
  set w : Fin d → ℂ := (ch.e z).ofLp with hw
  have hTz : T w = ch.e z := rfl
  have hL : ∀ j, HasFDerivAt (g j) (fderiv ℂ (g j) (ch.e z)) (T w) := fun j => by
    rw [hTz]; exact (ch.differentiableAt_ev (φ j) hzs hz).hasFDerivAt
  set M : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun j => -((fderiv ℂ (g j) (ch.e z)).comp T) with hM
  have hHM : HasFDerivAt H M w := by
    refine hasFDerivAt_pi'.2 fun j => ?_
    exact ((hL j).comp w T.hasFDerivAt).neg
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hTv : T v = ∑ b, v b • EuclideanSpace.single b (1 : ℂ) := by
    ext i
    simp [hTw, Pi.single_apply]
  have hMv : M v = 0 := by
    funext j
    have hj := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hj
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hM, ContinuousLinearMap.pi_apply, neg_apply,
      ContinuousLinearMap.comp_apply, hTv, map_sum, map_smul, smul_eq_mul, Pi.zero_apply, neg_eq_zero]
    rw [← hj]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨w, ⟨(hHM.restrictScalars ℝ).differentiableAt, ?_⟩, ?_⟩
  · rw [(hHM.restrictScalars ℝ).fderiv]
    refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩)
    show M v = 0
    exact hMv
  · funext j
    simp only [hH, hg, Function.comp_apply, hTz, ch.e.left_inv hzs, GlobalTheory.CxPts.ev_eq hz]

end GlobalTheory.ChartSard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothSectionsInFunctionField
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem smooth_sections_in_functionField : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [inst' : Algebra ℂ Z'.functionField], Smooth p' → inst' = ffAlg p' → ∀ (W : Z'.Opens), IsAffineOpen W → ∀ (hW : genericPoint Z' ∈ W) (B : Subalgebra ℂ Z'.functionField), (∀ y, y ∈ B ↔ ∃ g : Γ(Z', W), (Z'.presheaf.germ W (genericPoint Z') hW).hom g = y) → Algebra.Smooth ℂ B := by
  intro Z' _ p' inst' hp hinst W hWa hW B hB
  subst hinst
  letI : Algebra ℂ Z'.functionField := ffAlg p'
  let φ : ℂ →+* Γ(Z', W) := (p'.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have h := HasRingHomProperty.appLE @Smooth p' hp ⟨⊤, isAffineOpen_top _⟩ ⟨W, hWa⟩ le_top
  have h' : RingHom.Smooth φ :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.bijective) h
  letI : Algebra ℂ Γ(Z', W) := φ.toAlgebra
  have hs : Algebra.Smooth ℂ Γ(Z', W) := h'
  let g := (Z'.presheaf.germ W (genericPoint Z') hW).hom
  have hg : Function.Injective g := germ_injective_of_isIntegral Z' (genericPoint Z') hW
  have hc : ∀ c : ℂ, g (algebraMap ℂ Γ(Z', W) c) = algebraMap ℂ Z'.functionField c := by
    intro c
    show g (φ c) = _
    simp only [φ, g, Scheme.Hom.appLE, CommRingCat.comp_apply, RingHom.comp_apply]
    show _ = (Z'.presheaf.germ ⊤ (genericPoint Z') trivial).hom ((p'.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl
  let gA : Γ(Z', W) →ₐ[ℂ] Z'.functionField := { g with commutes' := hc }
  let f : Γ(Z', W) →ₐ[ℂ] B := gA.codRestrict B (fun x => (hB _).2 ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => hg (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (hB y.1).1 y.2
    exact ⟨x, Subtype.ext hx⟩
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective f hf)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePoints
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibTrace

theorem trace_quot_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc hk hred h
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJ
  haveI : Module.Finite k (rB k K x {0} ⧸ J) := GlobalTheory.PD.FibFin.finite_quot k K x hc
  haveI : Module.Free k (rB k K x {0} ⧸ J) := Module.Free.of_divisionRing k _
  have hred' : IsReduced (k ⊗[k] (rB k K x {0} ⧸ J)) :=
    isReduced_of_injective (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).toRingHom
      (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).injective
  have key := (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange (O := k) (H := rB k K x {0} ⧸ J) (K := k) hred').2.2
    (Ideal.Quotient.mk J h)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at key
  rw [key]
  have hker : ∀ e : fib k K x, ∀ a ∈ J, e.1 a = 0 := fun e a ha => by
    have : J ≤ RingHom.ker e.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let E : fib k K x ≃ (rB k K x {0} ⧸ J →ₐ[k] k) :=
    { toFun := fun e => Ideal.Quotient.liftₐ J e.1 (hker e)
      invFun := fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ k J), fun j => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        have hm : (⟨_, tco_mem k K x j⟩ : rB k K x {0}) ∈ J := by
          rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]⟩
      left_inv := fun e => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun φ => by
        apply Ideal.Quotient.algHom_ext
        rfl }
  rw [← finsum_comp_equiv E]
  rfl

end GlobalTheory.PD.FibTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

variable (d : ℕ)

theorem X_mem_one (i : Fin (d + 1)) : (X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ 1 :=
  isHomogeneous_X ℂ i

abbrev chart (i : Fin (d + 1)) : (PSpace ℂ d).Opens := Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)

def ratioSec (i j : Fin (d + 1)) : Γ(PSpace ℂ d, chart d i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)
    (Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j))

variable {d} {Z : Scheme.{0}} [IsIntegral Z]


open Classical in
def rat (φ : Z ⟶ PSpace ℂ d) (i j : Fin (d + 1)) : Z.functionField :=
  if h : genericPoint Z ∈ φ ⁻¹ᵁ chart d i then
    Z.presheaf.germ (φ ⁻¹ᵁ chart d i) (genericPoint Z) h (φ.app (chart d i) (ratioSec d i j))
  else 0

variable [Algebra ℂ Z.functionField]

def fld (φ : Z ⟶ PSpace ℂ d) : IntermediateField ℂ Z.functionField := IntermediateField.adjoin ℂ (Set.range (rat φ 0))

def crd (φ : Z ⟶ PSpace ℂ d) : Fin (d + 1) → fld φ := fun j =>
  ⟨rat φ 0 j, IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩⟩

theorem crd_val (φ : Z ⟶ PSpace ℂ d) (j : Fin (d + 1)) : ((crd φ j : fld φ) : Z.functionField) = rat φ 0 j := rfl

end GlobalTheory.PD.XCover
end
end

