module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAwayStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  first | exact @GlobalTheory.TwV.Xc.sameOff_len_of_sameAway | exact GlobalTheory.TwV.Xc.sameOff_len_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.sameOff_len_of_sameAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasis
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

section SlopeTestRemainingChoices
variable {E : Type} [Field E]
theorem toMatrix'_stdCo_reindex {n N : ℕ} (h : N = n) (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) :
    LinearMap.toMatrix' (stdCo σ (G.reindex (finCongr h) (finCongr h))).toLinearMap =
      (LinearMap.toMatrix' (stdCo σ G).toLinearMap).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  subst h
  simp

theorem toMatrix'_linEquiv_symm_mul {n : ℕ} (e : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  simp

theorem toMatrix'_toLE_eq {n : ℕ} (g : GL (Fin n) E) : LinearMap.toMatrix' (toLE g).toLinearMap = (g : Matrix (Fin n) (Fin n) E) := by
  simp only [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  exact LinearMap.toMatrix'_toLin' (g : Matrix (Fin n) (Fin n) E)

theorem toMatrix'_toLE_symm_eq {n : ℕ} (g : GL (Fin n) E) :
    LinearMap.toMatrix' (toLE g).symm.toLinearMap = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  rw [Matrix.coe_units_inv, ← toMatrix'_toLE_eq]
  exact (Matrix.inv_eq_left_inv (toMatrix'_linEquiv_symm_mul _)).symm
end SlopeTestRemainingChoices

section Site
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)

theorem Joint.cp_iw_eq_rho (j : ℕ) (La : (sysS H X std).Lt j) (v : (sysS H X std).Pl) : (J.cp std).iw j La v = J.rho std v := by
  cases j with
  | zero => rfl
  | succ i =>
    simp only [Joint.cp, cpAt, chAt]
    split_ifs with hi
    · exact J.iw i hi _ v
    · rfl

theorem Joint.stdCo_cpJ_mat (j : ℕ) (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap).submatrix (Fin.cast hr) (Fin.cast hr) := by
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    exact toMatrix'_stdCo_reindex _ _ _
  | succ i =>
    simp only [Joint.cp, cpAt, chAt, dif_pos hj]
    exact toMatrix'_stdCo_reindex _ _ _

theorem gMat_eq_mul (j : ℕ) (hj : j ≤ D.R.m) (γ : GL (Fin (D.R.N j)) D.host.E) :
    gMat J j hj γ = LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      ((γ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) * (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) := by
  unfold gMat toStdCo stdG
  simp only [LinearEquiv.coe_trans, LinearMap.toMatrix'_comp]
  rw [toMatrix'_toLE_eq, toMatrix'_toLE_symm_eq, mul_assoc (_ * _), ← mul_assoc (LinearMap.toMatrix' _), toMatrix'_linEquiv_symm_mul, one_mul,
    mul_assoc]
end Site

theorem changedFrame_eq_coord_mul_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj hr La v
  have hU' : star (d.eM j La) * d.eM j La = 1 := mul_eq_one_comm.mp (_root_.GlobalTheory.TwV.DelB.Dec.eM_mul_star S d j La)
  have hE : d.eM j La = (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
        (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E))).submatrix
        (finCongr hr) (finCongr hr) := by
    rw [Dec.eM, dif_pos ⟨hj, hr⟩, gMat_eq_mul]
    rfl
  have hC : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix
        (finCongr hr) (finCongr hr)) := by
    rw [Joint.stdCo_cpJ_mat J std j hj hr La, hE, Matrix.submatrix_mul_equiv]
    have h1 : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
        (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
          (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) *
        (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E)) =
        LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap := by
      rw [Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
    rw [h1]
    rfl
  show (star (d.eM j La)).map (J.rho std v) * ((((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap) *
      ((J.cp std).B j La).1).map ((J.cp std).iw j La v)).submatrix (finCongr ((J.cp std).hk j La)) (finCongr ((J.cp std).hk j La))) = _
  rw [Joint.cp_iw_eq_rho, hC]
  change (star (d.eM j La)).map (J.rho std v) * (d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v) =
    ((((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v)
  rw [← Matrix.map_mul, ← mul_assoc, ← mul_assoc, hU', one_mul]

end GlobalTheory.TwV.DelB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem levU_mulVec_mem_hatL (S : StepLevel F E σ J T f bad) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ S.U)
    (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb := by
  refine Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_
  have h1 := Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz
  have h2 : bc (prV (E := E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)
  have h3 := (h2.2 _).1 h1
  have e : (fun i => prV (E := E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) =
      ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (z i) := by
    funext i
    exact RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i
  rw [e]
  exact h3

theorem hatStab_of_levU (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  intro z
  constructor
  · intro hz
    have := levU_mulVec_mem_hatL S κ.1 κ.2 _ hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro hz
    exact levU_mulVec_mem_hatL S κ.1⁻¹ (S.U.inv_mem κ.2) z hz

end Hat

theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x x' p κ hx hp
  obtain ⟨p', hN, hf, hfr⟩ := GlobalTheory.T.chartPoint_frames_move_integralRightTranslate A dtU a hP H i p
    (fun P => ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))
    (fun P => (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))
    (_root_.GlobalTheory.TwV.congAt_fb_lev A dtU a hP H i hi β x p κ hp) hp.frame
  refine ⟨p', ⟨?_, ?_, ?_⟩⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, latAd_stab _ _ _ (hatStab_of_levU _ κ)]
  · intro P
    have e : ratA D.host.F (A.crd i hi) * x'.1 * ratA D.host.F (A.fb i hi β P) =
        ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact hfr P
  · intro P v h hv
    have e : ratA D.host.F (A.crd i hi) * x'.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by
      rw [hx, mul_assoc]
    have h1 := _root_.GlobalTheory.funMoved_mul_level t.seam _ P v h (iotaOf A i hi β P v h) _ κ _ (hp.fnl P v h hv)
    rw [e]
    intro w hw z hz
    have h2 := h1 w (by rw [← hN]; exact hw) z hz
    exact (congrFun (congrFun hf P) w).trans h2

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContractionIdentityFramesWithOperatorScalarStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_identity_frames_with_operator_scalar : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (c : ℂ_[p]) (F g₀ : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; FrInv fd → KapLawLt X ℂ_[p] (thFOf X pos F) → let Y := pendT X E hfin hst hLT pos F; ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc) (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc) (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc) (sO : ∀ j, X.Lt j → Y.Kc) (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) (_ : j < X.mm) (cK : Y.Kc) (hN : RankTie X D j), (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → F j La La' = linSub (fun x y => c * subBG E.toCEmb pos fd j La La' x y) (g₀ j La La')) → MoveH Y u μ cmp (fun j La => glInv X j (BOf fd j La)) Gm j → TieOpS (Y := Y) t u μ cls Gm sO j (eIdx X D pos j hN) (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) → TieSerH Y t u μ cls κ ι (fun j La La' => resV (kapOf X pos j) (g₀ j La La')) sH j (eIdx X D pos j hN) → TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La) * sO j La) j cK → DelYEqH Y (fun j La' => VOf Y.Kc fd c j La') τ j → DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_of_frames_scal | exact GlobalTheory.TwV.DelB.delPolAt_of_frames_scal | (intros; apply GlobalTheory.TwV.DelB.delPolAt_of_frames_scal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CsdScopeOfLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.CsdLift

theorem val_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).val w = 1 := by
  rfl

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem compNorm_quadChar_pow (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) :
    compNorm E (quadChar E ^ a) = 1 := by
  rw [map_pow, compNorm_quadChar, one_pow]

end GlobalTheory.CsdLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueArithmeticElementAtSiteStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvalue_arithmeticElement_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  first | exact @GlobalTheory.TwV.Xc.kapG_at_site | exact GlobalTheory.TwV.Xc.kapG_at_site | (intros; apply GlobalTheory.TwV.Xc.kapG_at_site <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExAllOfGood
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RoadU


open UpperTheory.V.Af in
theorem frobEig_of_dec {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π : CuspSub E a) (Q : GlobalTheory.RealGal.QCM E Ω) (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l))
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hdec : ∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.K).range)
    (hsph : ∀ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w → (CG.mk P).HasSat w' B → SphAt .unr P ι r w' B)
    (hP : IsLift π P) (hB : (CG.mk π).HasSat w B) (hiso : RepIso r (ρ.comp (Bc.res E Ω ↥Q.K)))
    (hunr : ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1) :
    FrobEig ι ρ w (algSat a (normV w) B) := by
  intro A hA
  refine ⟨hunr A hA, fun σ hσ => ?_⟩
  obtain ⟨w', hw', hA', hq⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA (hdec A hA)
  obtain ⟨τ, rfl⟩ := hdec A hA hσ.1
  have hτ : IsFrob (F := ↥Q.K) A (normV w') τ := by
    rw [hq]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 ↥Q.K) ∉ w'.asIdeal := by
    intro h
    apply hl
    rw [← hw']
    change ((l : ℕ) : 𝓞 E) ∈ Ideal.comap (algebraMap (𝓞 E) (𝓞 ↥Q.K)) w'.asIdeal
    simpa using h
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hw', hq]) (by rw [hw']; exact hB)
    simpa using this
  have key := ((hsph w' hw' hB' hl') A hA').2 τ hτ
  obtain ⟨g, hg⟩ := hiso
  have e : ρ (Bc.res E Ω ↥Q.K τ)⁻¹ = g * r τ⁻¹ * g⁻¹ := by
    rw [← map_inv]
    exact hg τ⁻¹
  rw [e, ← hq, ← key, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]


end GlobalTheory.RoadU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
namespace GlobalTheory.GoodCsdTwist

open GlobalTheory.ContraPair

theorem unrAt_mul {K : Type} [Field K] [NumberField K] {χ χ' : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, mul_one]

theorem unrAt_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : (χ⁻¹).UnrAt v := fun x hx => by
  change (χ.loc v x)⁻¹ = 1
  rw [h x hx, inv_one]

theorem unrAt_pow {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : ∀ k : ℕ, (χ ^ k).UnrAt v
  | 0 => fun _ _ => rfl
  | k + 1 => by rw [pow_succ]; exact unrAt_mul (unrAt_pow h k) h

theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem neg_one_zpow_natAbs (z : ℤ) : ((-1 : ℂˣ) ^ z.natAbs) = (-1 : ℂˣ) ^ (-z) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg.neg_one_zpow, (Int.natAbs_even.2 h).neg_one_pow]
  · rw [h.neg.neg_one_zpow, (Int.natAbs_odd.2 h).neg_one_pow]

theorem exists_goodCsd_twist : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧
    InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  intro _ E _ _ _ l a ha π χ ⟨hreg, hpol, hgood⟩ w₀ hw₀
  obtain ⟨n, hn⟩ := GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair E a ha π χ hreg hpol
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  have hb : IsAlgPos χ (fun _ => n φ₀) := by
    rw [show (fun _ => n φ₀) = n from funext fun φ => UpperTheory.heckeChar_parallel_weight _ χ n hn φ₀ φ]
    exact hn
  have hinv : IsAlgPos χ⁻¹ (fun _ => -n φ₀) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hb k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  have ho : (quadChar E ^ (a + (n φ₀).natAbs)).OrderDvd 2 := by
    unfold HChar.OrderDvd
    rw [← pow_mul, mul_comm, pow_mul]
    have : (quadChar E) ^ 2 = 1 := by
      refine Subtype.ext (MonoidHom.ext fun x => ?_)
      change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
      rw [← map_pow, Int.units_sq, map_one]
    rw [this, one_pow]
  have hpos := isAlgPos_mul hinv (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero] at hpos
  have hsign : ∀ v, (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1) = (-1) ^ (-n φ₀) := fun v => by
    change (χ.locInf v (-1))⁻¹ * ((quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1)) = _
    rw [locInf_pow, quadChar_locInf]
    rw [hpol.sign v, pow_add, inv_mul_cancel_left, neg_one_zpow_natAbs]
  have halg := UpperTheory.heckeChar_algebraic_of_sign _ _ (-n φ₀) hpos hsign
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧
      (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := fun w hw => by
    obtain ⟨-, hu, hsat⟩ := hgood.2.2 w hw
    have h1 := GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical E a ha π _ w hsat (GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate E a ha π _ hpol.dual w hw hsat)
    replace h1 := unrAt_inv h1
    rw [inv_inv] at h1
    exact ⟨hu, unrAt_mul (unrAt_inv (_root_.GlobalTheory.NormBelow.unrAt_under_of_compNorm E χ w hw hu h1)) (unrAt_pow (GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt E w hu) _)⟩
  obtain ⟨κ, m, hκ, hres, hκ0, hκu⟩ := _root_.GlobalTheory.HeckeUnrExt.exists_ext_unr E _ (-n φ₀) halg hunr w₀ hw₀
  refine ⟨κ, m, hκ, hκ0, regAlg_twist hreg hκ, ⟨fun v => ?_, ?_⟩, ⟨hgood.1, hgood.2.1, fun w hw => ?_⟩, rfl⟩
  · rw [locInf_pow, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow, dualIsConjBy_one]
    exact UpperTheory.V.Af.Cq.csdTwist E a π _ κ hpol.dual
      (by rw [hres, map_mul, map_inv, map_pow, compNorm_quadChar, one_pow, mul_one])
  · obtain ⟨h1, h2, B, hB⟩ := hgood.2.2 w hw
    refine ⟨h1, h2, B.map (· * κ.val w), ?_⟩
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B (hκu w hw) hB

end GlobalTheory.GoodCsdTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatMulDivPowMemIntegralFiniteAdeleStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_div_pow_mem_integral_finiteAdele : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (∀ w', w' ≠ w → prV (E := E) w' z = 0) → ∀ (ℓ : ℕ), ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E := by
  first | exact @GlobalTheory.DivInt.exists_nat_mul_div_pow_mem | exact GlobalTheory.DivInt.exists_nat_mul_div_pow_mem | (intros; apply GlobalTheory.DivInt.exists_nat_mul_div_pow_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem bAt_orth_lev : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj a
  cases j with
  | zero =>
    refine ⟨?_, fun a' => rfl⟩
    exact J.Gd.cmp.B_std.1
  | succ j =>
    refine ⟨(H.core j hj _).std, fun a' => J.oneB j hj _ _⟩

end GlobalTheory.TwV.DelA
end

