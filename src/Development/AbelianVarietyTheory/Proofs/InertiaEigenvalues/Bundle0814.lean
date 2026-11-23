module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHarmonicHighestWeightMultiplicityOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HarmLine

theorem loc_jointTop : ∀ {σ : Type} [DecidableEq σ] {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ) (κ : Fin N → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ) (G P : MvPolynomial σ ℂ), G ≠ 0 → (∀ v ∈ G.vars, (∀ u, z u ≠ v) ∧ ∀ u, y u ≠ v) → GlobalTheory.CompactHarm.JointTop z y κ α β (G * P) → GlobalTheory.CompactHarm.JointTop z y κ α β P := by
  intro σ _ k l N z y κ α β G P hG hGv hJ
  have hd : ∀ u, u ∉ G.vars → ∀ Q : MvPolynomial σ ℂ,
      MvPolynomial.pderiv u (G * Q) = G * MvPolynomial.pderiv u Q := by
    intro u hu Q
    rw [Derivation.leibniz, MvPolynomial.pderiv_eq_zero_of_notMem_vars hu, smul_zero, add_zero, smul_eq_mul]
  have hz : ∀ c Q, MvPolynomial.pderiv (z c) (G * Q) = G * MvPolynomial.pderiv (z c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).1 c rfl) Q
  have hy : ∀ c Q, MvPolynomial.pderiv (y c) (G * Q) = G * MvPolynomial.pderiv (y c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).2 c rfl) Q
  have hmix : ∀ i j, GlobalTheory.Capelli.mixedOp ℂ z y i j (G * P) = G * GlobalTheory.Capelli.mixedOp ℂ z y i j P := by
    intro i j
    rw [GlobalTheory.Capelli.mixedOp_apply, GlobalTheory.Capelli.mixedOp_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [hz, hy]
    exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  have hrz : ∀ c c', GlobalTheory.Capelli.rowOp ℂ z c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ z c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hry : ∀ c c', GlobalTheory.Capelli.rowOp ℂ y c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ y c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hJ
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' h => ?_, fun c => ?_, fun d d' h => ?_, fun d => ?_,
    fun c d => ?_⟩
  · have := h1 i j hij
    rw [hmix] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h2 i
    rw [hmix, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h3 c c' h
    rw [hrz] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h4 c
    rw [hrz, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h5 d d' h
    rw [hry] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h6 d
    rw [hry, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h7 c d
    simp only [hy, hz, ← Finset.mul_sum] at this
    exact (mul_eq_zero.1 this).resolve_left hG

theorem joint_line : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P P' : PolF D m n), P ≠ 0 → GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsHarm w P' → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsNHw w lam P' → GlobalTheory.LowestKType.IsKHw w P → GlobalTheory.LowestKType.IsKHw w P' → ∃ c : ℂ, P' = c • P := by
  intro D n m w lam P P' hP0 hH hH' hN hN' hK hK'
  classical
  set κ : D.what₂.Tau → Fin n → ℂ := fun τ a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ) with hκ
  have hJ := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P hH hN hK
  have hJ' := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P' hH' hN' hK'
  have hU : ∀ τ : D.what₂.Tau, ∃ Q₀ : MvPolynomial (Fin m × Fin n) ℂ, ∀ α β f,
      GlobalTheory.CompactHarm.JointTop (GlobalTheory.HarmLine.zR m n (w.p τ)) (GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β f →
        ∃ r : ℂ, f = r • Q₀ := fun τ =>
    _root_.GlobalTheory.CompactHarm.jointTop_line _ _ (GlobalTheory.HarmLine.zR_inj m n (w.p τ)) (GlobalTheory.HarmLine.yR_inj m n (w.p τ))
      (GlobalTheory.HarmLine.zR_ne_yR m n (w.p τ)) (GlobalTheory.HarmLine.zR_yR_cover m n (w.p τ)) (κ τ)
  choose Q₀ hQ₀ using hU
  let Q : D.what₂.Tau → PolF D m n := fun τ => MvPolynomial.rename (Prod.mk τ) (Q₀ τ)
  have hfac : ∀ (τ : D.what₂.Tau) (P : PolF D m n) α β,
      GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P →
      ∃ R : PolF D m n, P = Q τ * R ∧ ∀ v ∈ R.vars, v.1 ≠ τ := by
    intro τ P α β h
    obtain ⟨s, f, g, hPs, hf, hg⟩ := _root_.GlobalTheory.jointTop_slice (Prod.mk τ) (fun a b h => (Prod.mk.inj h).2) _ _ _ _ _ P h
    choose! r hr using fun i (hi : i ∈ s) => hQ₀ τ α β (f i) (hf i hi)
    refine ⟨∑ i ∈ s, r i • g i, ?_, ?_⟩
    · rw [hPs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hr i hi, map_smul, smul_mul_assoc, mul_smul_comm]
    · intro v hv hvτ
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hv)
      have hvi' : v ∈ (g i).vars := by
        rw [MvPolynomial.smul_eq_C_mul] at hvi
        have := MvPolynomial.vars_mul (MvPolynomial.C (r i)) (g i) hvi
        simpa using this
      exact hg i hi v hvi' ⟨v.2, by rw [← hvτ]⟩
  have hQne : ∀ τ, Q τ ≠ 0 := by
    intro τ h0
    obtain ⟨α, β, hτ⟩ := hJ τ
    obtain ⟨R, hR, -⟩ := hfac τ P α β hτ
    exact hP0 (by rw [hR, h0, zero_mul])
  have hE : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D m n,
      (∀ τ ∈ s, ∃ α β, GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P) →
      ∃ R : PolF D m n, P = (∏ τ ∈ s, Q τ) * R ∧ ∀ v ∈ R.vars, v.1 ∉ s := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro P _; exact ⟨P, by simp, by simp⟩
    | insert τ₀ s hτ₀ ih =>
      intro P hPs
      obtain ⟨R, hPR, hRv⟩ := ih P (fun τ hτ => hPs τ (Finset.mem_insert_of_mem hτ))
      obtain ⟨α, β, hJ0⟩ := hPs τ₀ (Finset.mem_insert_self _ _)
      have hG0 : (∏ τ ∈ s, Q τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hQne τ
      have hGv : ∀ v ∈ (∏ τ ∈ s, Q τ).vars, v.1 ∈ s := by
        intro v hv
        obtain ⟨τ, hτ, hv'⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hv)
        have := MvPolynomial.vars_rename (Prod.mk τ) (Q₀ τ) hv'
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 this
        exact hτ
      have hJR := loc_jointTop _ _ _ α β _ R hG0 (fun v hv =>
        ⟨fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this),
         fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this)⟩) (hPR ▸ hJ0)
      obtain ⟨R', hRR', hR'v⟩ := hfac τ₀ R α β hJR
      refine ⟨R', by rw [hPR, hRR', Finset.prod_insert hτ₀]; ring, ?_⟩
      intro v hv
      rw [Finset.mem_insert, not_or]
      refine ⟨fun h => hR'v v hv h, hRv v ?_⟩
      have hR'0 : R' ≠ 0 := by rintro rfl; simp at hv
      rw [hRR', MvPolynomial.mem_vars_iff_degreeOf_ne_zero, MvPolynomial.degreeOf_mul_eq (hQne τ₀) hR'0]
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hv
      omega
  obtain ⟨R, hR, hRv⟩ := hE Finset.univ P (fun τ _ => hJ τ)
  obtain ⟨R', hR', hR'v⟩ := hE Finset.univ P' (fun τ _ => hJ' τ)
  have hc : ∀ R : PolF D m n, (∀ v ∈ R.vars, v.1 ∉ (Finset.univ : Finset D.what₂.Tau)) →
      R = MvPolynomial.C (R.coeff 0) := fun R h =>
    MvPolynomial.vars_eq_empty_iff_eq_C.1
      (Finset.eq_empty_of_forall_notMem fun v hv => h v hv (Finset.mem_univ _))
  rw [hc R hRv] at hR
  rw [hc R' hR'v] at hR'
  have hc0 : R.coeff 0 ≠ 0 := by
    intro h0; apply hP0; rw [hR, h0]; simp
  refine ⟨R'.coeff 0 / R.coeff 0, ?_⟩
  rw [hR', hR, MvPolynomial.smul_eq_C_mul, ← mul_assoc, mul_comm (MvPolynomial.C _) (∏ τ, Q τ), mul_assoc,
    ← MvPolynomial.C_mul, div_mul_cancel₀ _ hc0]

end GlobalTheory.HarmLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs

section Keep

variable (D : D7) (Dat : D.ntw.Tw → ℕ → Bool → Type) (th : ∀ i j b, Dat i j b → D.nexp.Fm i j b)
  (lev : ∀ i j b, Dat i j b → Finset (PlE D.host))
  (thPsi : ∀ i j b k (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Dat i j b →
    Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b))
  (h1 : ∀ i j b k (d : Dat i j b), thPsi i j b k ∅ 1 d = {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] th i j b d})
  (thU : ∀ i j b (Q : Finset (PlE D.host)) (M : ℕ), Dat i j b →
    D.nexp.Fm i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M))
  (thP : ∀ i j b k Q ψ, D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b))
  (MtLat : ∀ i j b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i j b k Q ψ))
  (h2 : ∀ i j b k Q ψ, (MtLat i j b k Q ψ).FG)
  (h3 : ∀ i j b k Q ψ,
    Submodule.span (FractionRing (D.ntw.Ok i k)) (MtLat i j b k Q ψ : Set (D.nexp.MtV i j b k Q ψ)) = ⊤)

def keepEx : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw :=
  { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }

variable (nth' : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw (keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3))

def keepTw : TwNew D := ⟨D.ntw, keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3, D.nStage_trivialCharacter_coeff_eq, nth', D.ntwbr, D.ntwbr_ind⟩

variable (hU : ∀ i j b M (d : Dat i j b), 1 ≤ j → j ≤ D.R.m →
  thU i j b ∅ M d = th i j b d ⊗ₜ[D.ntw.O i] (1 : AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ M)))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def keepExp (E : NExpTied D) : NExpTied (keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').toD7 :=
  { E with
    acgWt := E.acgWt
    modWt := E.modWt
    fdWt := E.fdWt
    thU_empty := fun i j b M d hj hj' => hU i j b M d hj hj'
    mtV := fun i j b k Q ψ hj hj' hA => by
      letI : AddCommGroup (E.Wt i j b) := E.acgWt i j b
      letI : Module (FractionRing ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').toD7.ntw.O i)) (E.Wt i j b) := E.modWt i j b
      exact { E.mtV i j b k Q ψ hj hj' hA with } }

variable (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
  (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
  (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
  (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def keepSideB (Bs : SideB D cf Rw low Pq S hL eig θ) :
    SideB (keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').toD7 ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').cf cf) ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').row Rw) low Pq
      ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp := keepExp D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth' hU Bs.exp
    pq := fun i j b k Q ψ hj hj' hA => Bs.pq i j b k Q ψ hj hj' hA }

section Same
variable (Bs : SideB D cf Rw low Pq S hL eig θ)

end Same

end Keep

section Keep

end Keep

end GlobalTheory.TwInputs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftWeightInfinitesimalCharacterEqDefiniteParam
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.InertiaEigenvalues.LamParam

theorem infOf_lamV_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (hn : (Vc D j).rank = D.R.nV) (t : D.what₂.Tau), NG.infOf (fun a : Fin D.R.nV => (FWT.lamV D j t).w (Fin.cast hn.symm a)) = NG.paramV D.R (D.hc t) j (1 / 2) := by
  intro D j hn t
  have h := GlobalTheory.Mem.WtPar.infOf_lamLdef_eq_paramV D j t
  rw [← h]
  show NG.infOf (fun a : Fin D.R.nV => (Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) t).w (Fin.cast hn.symm a)) = _
  revert hn
  generalize (Vc D j).rank = n
  intro hn
  subst hn
  rfl

end GlobalTheory.InertiaEigenvalues.LamParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowestWeightVectorsAtRows
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.AdTh.RecPair GlobalTheory.AdTh.VecFock
open scoped ComplexOrder
namespace GlobalTheory.AdTh.PhaseMapFree

theorem isPair_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0)
    (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0) (hV : VStd D i) :
    IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) := by
  have hW := hP.ωP i t
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  refine ⟨hW, hM.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩
  · obtain ⟨a, ha⟩ := exp_mu hL i t τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := hP.vP i t
    have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
      (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
        rw [hP]
        exact under_ne (hes PP (Finset.mem_union.2 hPP)) hv
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]

theorem vec_fock_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP)
    (i : Fin D.R.m) (t : T0) (hV : VStd D i) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
    (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧
    (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧
    ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [pureTensorL_one] at this
  refine ⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hθ,
    isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (hM.order i τ)⟩
  have : gramAt D (Vc D i) τ = 1 := by
    unfold gramAt
    rw [hV.1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem thetaVector_ne_zero_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0)
    (hP : R.IsThP) (i : Fin D.R.m) : R.vP i A.μ0 ≠ 0 :=
  GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i A.μ0)

end GlobalTheory.AdTh.PhaseMapFree

namespace GlobalTheory.AdTh.PhaseMapFree
open GlobalTheory.AdTh.PhaseMap

end GlobalTheory.AdTh.PhaseMapFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfPowEqSelf
section
open Polynomial

namespace GlobalTheory.RangeOfPowerFixed

theorem mem_range_of_pow_eq_self {g : ℕ} [Fact (Nat.Prime g)] {K : Type*} [Field K] [Algebra (ZMod g) K]
    (z : K) (hz : z ^ g = z) : ∃ c : ZMod g, algebraMap (ZMod g) K c = z := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  have hg : 1 < g := (Fact.out : Nat.Prime g).one_lt
  set P : K[X] := X ^ g - X with hPeq
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hg
  have hdeg : P.natDegree = g := Polynomial.natDegree_X_pow_sub_X (R := K) hg

  have hroot : ∀ x : K, x ^ g = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP0, hPeq]
    simp [hx]

  set S : Finset K := insert z (Finset.univ.image (algebraMap (ZMod g) K)) with hSeq
  have hzS : z ∉ Finset.univ.image (algebraMap (ZMod g) K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hcard : S.card = g + 1 := by
    rw [hSeq, Finset.card_insert_of_notMem hzS,
      Finset.card_image_of_injective _ (algebraMap (ZMod g) K).injective, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [hSeq, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' P))
  omega

theorem main : ∀ {g : ℕ} [inst : Fact (Nat.Prime g)] (z : Formalism.CyclotomicNorms.Fbar g), z ^ g = z →
    ∃ (c : ZMod g), (Algebra.algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) : ZMod g → Formalism.CyclotomicNorms.Fbar g) c = z := by
  intro g _ z hz
  exact mem_range_of_pow_eq_self z hz

end GlobalTheory.RangeOfPowerFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem rowParam_of_cuspParam : ∀ (D : D7) (Rw : RowSide D), GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ) → (∀ k v, IsSplitPl D.host (D.naut.plGw k v)) → RowParam D Rw := by
  intro D Rw hP hC hS j hj1 hj2 σ hσ hg
  obtain ⟨π, h⟩ := hP j hj1 hj2 σ hσ hg
  have hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true := fun τ => by
    ext x
    have e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x) :=
      D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x
    rw [e]
    rfl
  have hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) := by
    intro τ
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def]
  refine ⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩
  · obtain ⟨a, b⟩ := h.2.2.2.2.2 τ
    refine ⟨?_, ?_⟩
    · rw [← hpar]; exact a
    · rw [← hembb, b, hpar, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp
  · rw [Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]
end GlobalTheory.TwInputs
end

