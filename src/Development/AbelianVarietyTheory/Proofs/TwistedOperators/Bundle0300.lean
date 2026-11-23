module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqBotOrEqOfStarProjectionEqSmul
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.TrCopy

theorem eq_bot_or_eq_of_starProjection_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U U' : Submodule ℂ H} [U'.HasOrthogonalProjection] (hle : U' ≤ U) (a : ℂ)
    (hPU : ∀ v ∈ U, U'.starProjection v = a • v) {u0 : H} (hu0 : u0 ∈ U) (hne : u0 ≠ 0) : U' = ⊥ ∨ U' = U := by
  have haa : a * a = a := by
    have h1 : U'.starProjection (U'.starProjection u0) = U'.starProjection u0 :=
      (Submodule.starProjection_eq_self_iff (K := U')).2 (U'.starProjection_apply_mem _)
    rw [hPU _ hu0, map_smul, hPU _ hu0, smul_smul] at h1
    exact smul_left_injective ℂ hne h1
  rcases mul_eq_zero.1 (show a * (a - 1) = 0 by rw [mul_sub, haa, mul_one, sub_self]) with h0 | h1
  · left
    refine (Submodule.eq_bot_iff U').2 fun v hv => ?_
    rw [← (Submodule.starProjection_eq_self_iff (K := U')).2 hv, hPU v (hle hv), h0, zero_smul]
  · right
    refine le_antisymm hle fun v hv => ?_
    have hv' : U'.starProjection v = v := by rw [hPU v hv, sub_eq_zero.1 h1, one_smul]
    exact hv' ▸ U'.starProjection_apply_mem v

theorem eq_smul_on_closure_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Set H) (P : H →L[ℂ] H) (a : ℂ)
    (hP : ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v ∈ (Submodule.span ℂ s).topologicalClosure)
    (h : ∀ u ∈ s, ∀ u' ∈ s, ⟪u', P u - a • u⟫_ℂ = 0) :
    ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v = a • v := by
  set A := Submodule.span ℂ s with hA
  let Q : H →L[ℂ] H := P - a • ContinuousLinearMap.id ℂ H
  have hQ : ∀ v, Q v = P v - a • v := fun v => rfl
  have hQA : ∀ v ∈ A, Q v ∈ Aᗮ := by
    intro v hv
    refine (Submodule.span_le (p := Aᗮ.comap (Q : H →ₗ[ℂ] H))).2 ?_ hv
    intro u hu
    show Q u ∈ Aᗮ
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hle : A ≤ (ℂ ∙ Q u)ᗮ := Submodule.span_le.2 (by
      intro u' hu'
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hQ]
      exact h u hu u' hu')
    exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hx))
  have hQcl : ∀ v ∈ A.topologicalClosure, Q v ∈ Aᗮ := fun v hv =>
    (Submodule.topologicalClosure_minimal (s := A) (t := Aᗮ.comap (Q : H →ₗ[ℂ] H)) (fun u hu => hQA u hu)
      ((Submodule.isClosed_orthogonal A).preimage Q.continuous)) hv
  have hcl : A.topologicalClosure ≤ Aᗮᗮ :=
    Submodule.topologicalClosure_minimal _ A.le_orthogonal_orthogonal (Submodule.isClosed_orthogonal _)
  intro v hv
  have h1 : Q v ∈ A.topologicalClosure := by
    rw [hQ]
    exact sub_mem (hP v hv) (Submodule.smul_mem _ _ hv)
  have h2 : ⟪Q v, Q v⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (hQcl v hv) (hcl h1)
  rw [inner_self_eq_zero, hQ, sub_eq_zero] at h2
  exact h2

theorem isIrredSubrep_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type)
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)),
    IsUnitaryRep ρ → ∀ U : Submodule ℂ H, IsCopyFinDS σ M ρ U → IsIrredSubrep ρ U := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ ρ hρ U hU
  classical
  obtain ⟨T, hT, hinj, rfl⟩ := hU
  have hTm := mem_homTensorPi.1 hT
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M

  have hgen : ∀ g w y, ρ g (T w y) ∈ Submodule.span ℂ {v | ∃ w y, v = T w y} := by
    intro g w y
    have e1 := GlobalTheory.TrAct.toInf_apply_homDS D V S M H ρ ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
    rw [hTm.2.1] at e1
    have e2 : ρ g (T w y) = ρ (toInf V g : GA D V) (ρ ((GfC V).subtype (toFin V g)) (T w y)) := by
      conv_lhs => rw [← toInf_mul_toFin g]
      rw [map_mul]
      rfl
    rw [e2, e1]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  have hsub : IsSubrep ρ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    isSubrep_topologicalClosure fun g v hv => Submodule.mem_comap.1
      ((Submodule.span_le (p := Submodule.comap (ρ g : H →ₗ[ℂ] H) _)).2
        (by rintro _ ⟨w, y, rfl⟩; exact hgen g w y) hv)

  obtain ⟨w0, hw0⟩ : ∃ w : W, w ≠ 0 := by
    by_contra h
    push Not at h
    have hne : (⊥ : Subrepresentation σ) ≠ ⊤ := bot_ne_top
    exact hne (by ext v; simp [h v])
  have hTw0 : T w0 ≠ 0 := fun h => hw0 (hinj (h.trans (map_zero T).symm))
  obtain ⟨y0, hy0⟩ : ∃ y, T w0 y ≠ 0 := by
    by_contra h
    push Not at h
    exact hTw0 (ContinuousMultilinearMap.ext h)
  have hu0 : T w0 y0 ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w0, y0, rfl⟩)
  refine ⟨hsub, fun h => hy0 ((Submodule.mem_bot ℂ).1 (h ▸ hu0)), fun U' hU'le hU' => ?_⟩
  haveI : CompleteSpace U' := hU'.1.completeSpace_coe

  have hPc : ∀ g v, U'.starProjection (ρ g v) = ρ g (U'.starProjection v) := by
    intro g v
    have h1 : ρ g (U'.starProjection v) ∈ U' := hU'.2 g _ (U'.starProjection_apply_mem v)
    have h2 : ρ g (v - U'.starProjection v) ∈ U'ᗮ :=
      (hU'.orthogonal hρ).2 g _ (Submodule.sub_starProjection_mem_orthogonal (K := U') v)
    have e : ρ g v = ρ g (U'.starProjection v) + ρ g (v - U'.starProjection v) := by
      rw [← map_add (f := _), add_sub_cancel]
    rw [e, map_add (f := _), (Submodule.starProjection_eq_self_iff (K := U')).2 h1,
      (Submodule.starProjection_apply_eq_zero_iff U').2 h2, add_zero]

  obtain ⟨T', hT'a⟩ : ∃ T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H, ∀ w y, T' w y = U'.starProjection (T w y) :=
    ⟨(ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H U'.starProjection).toLinearMap ∘ₗ T,
      fun _ _ => rfl⟩
  have hΦ' : ∀ w, T' w ∈ homDS M ρ ⊤ := fun w => mem_homPi.2 ⟨fun _ => trivial, fun τ g y => by
    rw [hT'a, hT'a, (hT.1 w).2 τ g y, hPc]⟩

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hρ (hT.1 x) ((map_ne_zero_iff T hinj).2 hx)
  have hBinv : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g v w => by
    change ⟪T (σ g w) _, T (σ g v) _⟫_ℂ = _
    rw [hTm.2.1, hTm.2.1, inner_map_map hρ]
    rfl
  have hCinv : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g v w => by
    change ⟪T (σ g w) _, T' (σ g v) _⟫_ℂ = _
    rw [hT'a, hTm.2.1, hTm.2.1, hPc, inner_map_map hρ, ← hT'a]
    rfl
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hC⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K hKo hKc W W σ σ hadm hadm.1 B C hBpos hBinv hCinv
  obtain ⟨c, hc⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K hKo hKc W σ hirr hadm φ hφ
  have key : ∀ x y, bePi (T' x) (T y) = conj c * bePi (T x) (T y) := fun x y => by
    have := hC x y
    rw [hc, LinearMap.smul_apply, LinearMap.id_apply, map_smulₛₗ, smul_eq_mul] at this
    exact this
  have hgen2 : ∀ u ∈ {v | ∃ w y, v = T w y}, ∀ u' ∈ {v | ∃ w y, v = T w y},
      ⟪u', U'.starProjection u - conj c • u⟫_ℂ = 0 := by
    rintro _ ⟨w, z, rfl⟩ _ ⟨w', z', rfl⟩
    rw [inner_sub_right, inner_smul_right, ← hT'a, inner_eq_bePi hδ hρ (hΦ' w) (hT.1 w'),
      inner_eq_bePi hδ hρ (hT.1 w) (hT.1 w'), key, mul_assoc, sub_self]
  exact eq_bot_or_eq_of_starProjection_eq_smul hU'le (conj c)
    (eq_smul_on_closure_span _ U'.starProjection (conj c) (fun v _ => hU'le (U'.starProjection_apply_mem v)) hgen2)
    hu0 hy0

end GlobalTheory.TrCopy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ c.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · rw [← hFx']; exact hF
  · rw [← hFx']; exact hPF

end GlobalTheory.EvenOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel

variable {D : D7}

theorem gram_det_ne_zero (S : HSp D) : S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv0
  set x : S.V := ∑ j, v j • S.frame j with hxdef
  have hfr : ∀ i, S.hT (S.frame i) x = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxdef, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Formalism.BasicNotions.HSpace.gram, mul_comm]
  have hx : S.hT.flip x = 0 := S.frame.ext fun i => by simpa using hfr i
  have hx0 : x = 0 := S.nondeg.2 x fun y => by
    have := LinearMap.congr_fun hx y
    simpa using this
  funext j
  exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v hx0 j

theorem isUnit_det_incM (S : HSp D) (c : D.host.E) (hc : c ≠ 0) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det := by
  have h1 : (c • S.gram).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (gram_det_ne_zero S)
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) (c • S.gram).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact (isUnit_iff_ne_zero.2 h1).map _

variable {R : Type} [CommRing R]

def coordsEquiv {n m d : ℕ} (e : Fin m ≃ Fin d) (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    Matrix (Fin n) (Fin d) R ≃+ Matrix (Fin m) (Fin n) R where
  toFun u := uᵀ.submatrix e id * G
  invFun x := ((x * G⁻¹).submatrix e.symm id)ᵀ
  left_inv u := by
    dsimp only
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hG, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Function.comp_id, Matrix.submatrix_id_id, Matrix.transpose_transpose]
  right_inv x := by
    dsimp only
    rw [Matrix.transpose_transpose, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id,
      Matrix.submatrix_id_id, Matrix.nonsing_inv_mul_cancel_right _ _ hG]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e id * G = uᵀ.submatrix e id * G + vᵀ.submatrix e id * G
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl

theorem coords (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (c : D.host.E) (hc : c ≠ 0) :
    ∃ f : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      ∀ u, f u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) :=
  ⟨coordsEquiv e _ (isUnit_det_incM S c hc), fun _ => rfl⟩

end GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinAvgSpan

open Formalism.REAL MeasureTheory GlobalTheory.SeriesToClosure Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom

theorem continuous_integral_K {n : ℕ} {ε : Fin n → Bool} {X : Type*} [TopologicalSpace X] (F : X → KG ε → ℂ)
    (hF : Continuous (Function.uncurry F)) : Continuous fun x => ∫ k, F x k ∂(muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ k, g k ∂(muK ε)
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (GlobalTheory.ExpansionAverage.integrable_K g.continuous)
          (GlobalTheory.ExpansionAverage.integrable_K h.continuous)
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hL : Continuous L := AddMonoidHomClass.continuous_of_bound L ((muK ε).real Set.univ) fun g => by
    show ‖∫ k, g k ∂(muK ε)‖ ≤ _
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k =>
      ContinuousMap.norm_coe_le_norm g k)).trans (le_of_eq (mul_comm _ _))
  exact hL.comp (ContinuousMap.curry ⟨_, hF⟩).continuous

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_conjAt (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) :
    Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
    fun k => conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))

theorem continuous_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    Continuous (Function.uncurry fun (x : GA D V) (k : KG ε) => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) :=
  (he.comp continuous_snd).mul (hφ.comp (continuous_fst.mul ((continuous_conjAt hθ hP hJ).comp continuous_snd)))

theorem integrable_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) (x : GA D V) :
    Integrable (fun k => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) (muK ε) :=
  GlobalTheory.ExpansionAverage.integrable_K (he.mul (hφ.comp (continuous_const.mul (continuous_conjAt hθ hP hJ))))

theorem continuous_avg (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) : Continuous (avg θ V τ ε P e φ) :=
  continuous_integral_K _ (continuous_integrand hθ hP hJ he hφ)

theorem avg_add_left (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e₁ e₂ : KG ε → ℂ} (h₁ : Continuous e₁) (h₂ : Continuous e₂) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    avg θ V τ ε P (e₁ + e₂) φ = avg θ V τ ε P e₁ φ + avg θ V τ ε P e₂ φ := funext fun x => by
  simp only [avg, Pi.add_apply, add_mul]
  exact integral_add (integrable_integrand hθ hP hJ h₁ hφ x) (integrable_integrand hθ hP hJ h₂ hφ x)

theorem avg_smul_left (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P (c • e) φ = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem avg_add_right (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ₁ φ₂ : GA D V → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) :
    avg θ V τ ε P e (φ₁ + φ₂) = avg θ V τ ε P e φ₁ + avg θ V τ ε P e φ₂ := funext fun x => by
  simp only [avg, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand hθ hP hJ he h₁ x) (integrable_integrand hθ hP hJ he h₂ x)

theorem avg_smul_right (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P e (c • φ) = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_left_comm (e _) c]
  exact integral_const_mul c _

theorem rTr_avg_same (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : P * g * P⁻¹ ∈ Kset ε) :
    ∃ k₀ : KG ε, ∀ (e : KG ε → ℂ) (φ : GA D V → ℂ),
      rTr V (atTau θ V τ g) (avg θ V τ ε P e φ) = avg θ V τ ε P (fun k => e (k₀⁻¹ * k)) φ := by
  obtain ⟨k₀, hk₀'⟩ : P * g * P⁻¹ ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
  have hk₀ : toMK k₀ = P * g * P⁻¹ := hk₀'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have eg : g = P⁻¹ * toMK k₀ * P := by
    rw [hk₀]
    calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [Matrix.nonsing_inv_mul _ hd, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨k₀, fun e φ => funext fun x => ?_⟩
  have key : ∀ k : KG ε, atTau θ V τ g * atTau θ V τ (P⁻¹ * toMK k * P) =
      atTau θ V τ (P⁻¹ * toMK (k₀ * k) * P) := fun k => by
    rw [eg, ← at_mul hθ hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k₀)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))]
    rfl
  simp only [rTr, avg, mul_assoc x, key]
  rw [← integral_mul_left_eq_self (μ := muK ε)
    (fun k => e (k₀⁻¹ * k) * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) k₀]
  simp only [inv_mul_cancel_left]

theorem rTr_avg_other (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    rTr V (atTau θ V τ' g) (avg θ V τ ε P e φ) = avg θ V τ ε P e (rTr V (atTau θ V τ' g) φ) := funext fun x => by
  simp only [rTr, avg, mul_assoc x]
  congr 1
  funext k
  rw [GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne _
    (conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))) g hg]

end GlobalTheory.KFinAvgSpan

namespace GlobalTheory.KFinAvgSpan


set_option maxHeartbeats 1600000 in
theorem exists_stab_insert : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  intro D θ hθ N τ e he s hτs W' hW'fin hW'c hW'stab
  obtain ⟨F, hFfin, heF, hFc, hFtr⟩ := he
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI := hFfin
  haveI := hW'fin
  let B : F →ₗ[ℂ] W' →ₗ[ℂ] (GA D N.V → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ)
        (b : GA D N.V → ℂ))
      (fun a₁ a₂ b => avg_add_left hθ hP hJ (hFc _ a₁.2) (hFc _ a₂.2) (hW'c _ b.2))
      (fun c a b => avg_smul_left c _ _)
      (fun a b₁ b₂ => avg_add_right hθ hP hJ (hFc _ a.2) (hW'c _ b₁.2) (hW'c _ b₂.2))
      (fun c a b => avg_smul_right c _ _)
  have hB : ∀ (a : F) (b : W'), TensorProduct.lift B (a ⊗ₜ b) =
      GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ) :=
    fun a b => by rw [TensorProduct.lift.tmul]; rfl
  have hcont : ∀ t, Continuous (TensorProduct.lift B t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact continuous_const
    | tmul a b => rw [hB]; exact continuous_avg hθ hP hJ (hFc _ a.2) (hW'c _ b.2)
    | add u v hu hv => rw [map_add (f := _)]; exact hu.add hv
  refine ⟨LinearMap.range (TensorProduct.lift B), inferInstance, ?_, ?_, fun f hf => ⟨⟨e, heF⟩ ⊗ₜ ⟨f, hf⟩, hB _ _⟩⟩
  · rintro _ ⟨t, rfl⟩
    exact hcont t
  · intro τ'' hτ'' g hg hK w hw
    obtain ⟨t, rfl⟩ := hw
    suffices h : ∀ (a : F) (b : W'), rTr N.V (atTau θ N.V τ'' g)
        (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)) ∈
          LinearMap.range (TensorProduct.lift B) by
      induction t using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | tmul a b => rw [hB]; exact h a b
      | add u v hu hv =>
        rw [map_add (f := _)]
        exact add_mem hu hv
    intro a b
    rcases hτ'' with h | hs
    · rw [h] at hK ⊢
      obtain ⟨k₀, hk⟩ := rTr_avg_same hθ hP hJ hK
      have hk' := hk (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)
      refine ⟨⟨_, (hFtr _ a.2 k₀⁻¹).1⟩ ⊗ₜ b, ?_⟩
      rw [hB, hk']
    · have hne : τ ≠ τ'' := fun h => hτs (h ▸ hs)
      rw [rTr_avg_other hθ hP hJ hne hg]
      exact ⟨a ⊗ₜ ⟨_, hW'stab τ'' hs g hg hK b b.2⟩, hB _ _⟩

end GlobalTheory.KFinAvgSpan

end
end

