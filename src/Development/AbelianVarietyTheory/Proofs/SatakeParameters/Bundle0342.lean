module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0330
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.AdLevCpl

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 2000000 in
theorem levAt_coupled : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hMu i hi hi2 hAw
  have key : ∀ β β' x x' p p', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' → ∀ z,
      xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
    intro β β' x x' p p' hp hp' z
    have hh : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
    unfold xiAd
    rw [dite_eq_left hh]
    rw [hAw β β' x x' x x' p p' hh.1.choose hh.2.choose hp hp' hh.1.choose_spec hh.2.choose_spec (fun v _ => ⟨rfl, rfl⟩)]
  intro β β' x x' x₁ x₁' κ κ' h1 h1' z
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  obtain ⟨p₁, hp₁⟩ := hEx i (Nat.le_of_succ_le hi) β x₁
  obtain ⟨p₁', hp₁'⟩ := hEx (i + 1) hi β' x₁'
  rw [key β β' x₁ x₁' p₁ p₁' hp₁ hp₁' z, key β β' x x' p p' hp hp' z]
  have hs := _root_.GlobalTheory.LevSrcCpl.levSrc_cpl A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x₁ x₁' κ p p₁' p₁ h1 hp hp₁' hp₁ (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  have ht := _root_.GlobalTheory.CplTarget.levAt_target A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' h1' hp hp' hp₁' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  linear_combination (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1)) * hs +
    (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1)) * ht

end GlobalTheory.AdLevCpl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BasSingleMulSelf
section
set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm

def holCount {n : ℕ} (S : Finset (Fin (n + n))) : ℕ := (S.filter (·.val < n)).card

def holGe (n p : ℕ) : Submodule ℂ (Alt n) :=
  Submodule.span ℂ (bas n '' {S | p ≤ holCount S})

theorem mem_holGe_iff {n p : ℕ} (β : Alt n) :
    β ∈ holGe n p ↔ ∀ S, (bas n).repr β S ≠ 0 → p ≤ holCount S := by
  rw [holGe, Module.Basis.mem_span_image]
  constructor
  · intro h S hS
    exact h (Finsupp.mem_support_iff.2 hS)
  · intro h S hS
    exact h S (Finsupp.mem_support_iff.1 hS)

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitary
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sigD_eq_star' (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = star x := rfl

theorem cpB_eq_bAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)
  (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La)) =
      (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) := by
  cases j with
  | zero => rfl
  | succ i =>
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (i + 1) La).B.1.submatrix _ _ = _
    simp only [chAt, dif_pos hj]
    rfl

theorem unitary_product_of_hermitian_relations {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J c g B : Matrix (Fin N) (Fin N) E) (hc : cT σ c * c = J) (hg : cT σ g * J * g = J) (hB : cT σ B * J * B = 1) :
    star (c * g * B) * (c * g * B) = 1 := by
  have hs : star (c * g * B) = cT σ (c * g * B) := by
    ext i k
    simp only [cT, Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply, hσ]
  rw [hs, cT_mul, cT_mul]
  calc cT σ B * (cT σ g * cT σ c) * (c * g * B) = cT σ B * (cT σ g * (cT σ c * c) * g) * B := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hc, hg, hB]

theorem changed_frame_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La
  have hB := (_root_.GlobalTheory.TwV.DelA.bAt_orth_lev S j hj La.1).1
  have hc := J.pins.crd_orth j hj
  have hg' : (d.gam j hj La)⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj) := inv_mem (d.mem j hj La)
  have hval : (mM d j hj La).1 = (J.A.crd j hj).1 * ((d.gam j hj La)⁻¹).1 * (bAt J j hj La.1).1 := by
    simp only [mM, Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold StdU
    rw [hval]
    exact unitary_product_of_hermitian_relations _ (sigD_eq_star' D) _ _ _ _ hc hg' hB
  · intro v
    rw [_root_.GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis S d j hj h La v, cpB_eq_bAt J std j hj h La,
      show ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (Fin.cast h) =
        ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (finCongr h) from rfl,
      show (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) = (bAt J j hj La.1).1.submatrix (finCongr h) (Fin.cast h) from rfl,
      Matrix.submatrix_mul_equiv, ← Units.val_mul]
    rfl
  · have hdet : ((d.gam j hj La)⁻¹).1.det * (d.gam j hj La).1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hval, uB, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    linear_combination ((J.A.crd j hj).1.det * (bAt J j hj La.1).1.det) * hdet

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut.SsTwist

open Polynomial

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (x.charPol g).scaleRoots (ξ g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_end _ (Units.ne_zero _)]

theorem scaleRoots_cancel {p q : ℂ[X]} {c : ℂ} (hc : c ≠ 0) (H : p.scaleRoots c = q.scaleRoots c) : p = q := by
  have := congrArg (fun P : ℂ[X] => P.scaleRoots c⁻¹) H
  simpa only [← scaleRoots_mul, mul_inv_cancel₀ hc, scaleRoots_one] using this

end GlobalTheory.GalCut.SsTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentatives
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem isPtAd_cls (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) := by
  refine ⟨?_, H.frame i hi c, ?_⟩
  · rw [← H.N_eq i hi c]
    exact H.lat i hi c
  · intro P v h hv
    exact Classical.epsilon_spec (H.fnl i hi ((St i hi).chOf c) P v h hv) c rfl

theorem exists_cls_eq (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) :
    ∃ c : (D.chTw u μ).cls i, (St i hi).chOf c = β ∧ ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      ∃ κ : ((St i hi).K β).lev.U, x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 := by
  obtain ⟨⟨c, rfl⟩, hc⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hc
  rw [Subgroup.mem_subgroupOf] at hg hk
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1 hg
  refine ⟨c, rfl, γ, hγ, ⟨k.1, hk⟩, ?_⟩
  have e1 := congrArg Subtype.val e
  simp only [Subgroup.coe_mul] at e1
  rw [e1, ← hγg]
  rfl

end Cls

theorem ptEx_of_tie (hR : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) (hL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hcls : ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) :=
    fun i hi c => isPtAd_cls hTie i hi c
  refine ⟨fun i hi β x => ?_, hcls⟩
  obtain ⟨c, hcβ, γ, hγ, κ, hx⟩ := exists_cls_eq (St := St) i hi β x
  subst hcβ

  let k : UA D i hi := ⟨κ.1, (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2 |>.1⟩

  let x₁ : UA D i hi := x * k⁻¹
  have hx₁ : x₁.1 = ratA D.host.F γ * ((St i hi).y c).1 := by
    show x.1 * (κ.1)⁻¹ = _
    rw [hx, mul_inv_cancel_right]
  obtain ⟨p₁, hp₁⟩ := hR A dtU a hPin hTie i hi _ ((St i hi).y c) x₁ (A.pt i hi c) γ hγ hx₁ (hcls i hi c)
  have hxk : x.1 = x₁.1 * κ.1 := by
    show x.1 = x.1 * (κ.1)⁻¹ * κ.1
    rw [inv_mul_cancel_right]
  exact hL A dtU a hPin hTie i hi _ x₁ x p₁ κ hxk hp₁

theorem ptEx_isPtAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) :=
  ptEx_of_tie _root_.GlobalTheory.TwRat.ratPt _root_.GlobalTheory.TwV.isPtAd_mul_lev

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormLevelZeroRealisesComplexPoly
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA


set_option maxHeartbeats 1000000 in
theorem cmp_realAt_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) (h : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat 0).V, ∃ V : XR ((sysS H X std).Pj 0) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp 0 x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d 0 (Nat.zero_le _) h La ((ex.tw.fm u μ).emb 0 x) V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP ι hι d h La hLa x
  have hpos := (posTie_at S hP ι hι).2
  obtain ⟨g, hg1, hg2⟩ := latticeTupleLevelZero_point_isComponentPoint S hD La hLa
  have hx : x = ex.tw.e0 u μ ((ex.tw.e0 u μ).symm x) := by simp
  generalize (ex.tw.e0 u μ).symm x = x0 at hx
  subst hx
  have K := lev0AtOf_compatible J.Gd.cmp u w hg
  refine ⟨MvPolynomial.map D.what₂.embLL (K.val x0 La.1 La.2), ?_, ?_⟩
  · rw [(kaAt X H hT).cmp_zero, K.val_cmp x0 La.1 La.2 hLa]
    refine (MvPolynomial.map_map _ _ _).trans ((congrArg (MvPolynomial.map · _) ?_).trans (MvPolynomial.map_map _ _ _).symm)
    ext r
    exact (hpos r).symm
  · intro z z' hz
    have hj : (0:ℕ) ≤ D.R.m := Nat.zero_le _
    set c := J.e0.symm (clsAt X H 0 La.1 La.2) with hc
    have hce : clsAt X H 0 La.1 La.2 = J.e0 c := by simp [c]
    have hU := (J.lev0 (J.chart std 0 hj La)).2.2.1
    have hkmem : ((d.kap 0 hj La) : GL (Fin (D.R.N 0)) _) ∈ (J.Gd.forms u).cls0.lev.U := hU ▸ (d.kap 0 hj La).2
    let κ' : (J.Gd.forms u).cls0.lev.U := ⟨(d.kap 0 hj La).1, hkmem⟩
    have hchi := (J.lev0 (J.chart std 0 hj La)).2.2.2 (d.kap 0 hj La) κ' rfl
    obtain ⟨κ0, hy0, hc0, -⟩ := J.y0 c
    have hpt := d.eq 0 hj La hLa
    rw [hce, hy0] at hpt
    have hIs : (lev0At J.Gd u w hg).A.IsPt La.1 g (GlobalTheory.TwU.ratA D.host.F (d.gam 0 hj La) * ((J.Gd.forms u).cls0.y c).1 * (κ0 * κ').1) := by
      convert hg2 using 2
      rw [hpt, Subgroup.coe_mul]
      simp only [mul_assoc]
      rfl
    have hv := K.val_emb x0 La.1 La.2 g hg1 c (d.gam 0 hj La) (d.mem 0 hj La) (κ0 * κ') hIs z z' hz
    have e1 : (((J.Gd.forms u).cls0.lev.chi (κ0 * κ') : ℂˣ) : ℂ) = (((J.Gd.forms u).cls0.lev.chi κ' : ℂˣ) : ℂ) := by
      have e2 := MonoidHom.map_mul (J.Gd.forms u).cls0.lev.chi κ0 κ'
      rw [hc0, one_mul] at e2
      exact congrArg Units.val e2
    rw [e1] at hv
    show _ = _
    rw [cTw_zero]
    simp only [zpow_zero, neg_zero, dPow, detF, Finset.prod_const_one, mul_one]
    refine hv.trans ?_
    have hy : (J.St 0 hj).eY.symm z' = J.jointCmpEmbeddingY ((J.Gd.forms u).val0.eY.symm z') := by
      rw [Equiv.symm_apply_eq, J.fr0, Equiv.apply_symm_apply]
    rw [ex.tw.embed_mul_block_embedding, hce, hy, J.e0Tw, Dec.chi, hchi]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwOfContinuous
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem exists_place_dvd_prime {K : Type} [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(l : ℤ)}) ⊥
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)
      simp [this])
  have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((l : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    have : ((l : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, hmem⟩

theorem continuous_tw_of_continuous {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {k : Type} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {μ : Γ →* kˣ} (hr : Continuous r) (hμ : Continuous μ) :
    Continuous (UpperTheory.V.Af.tw r μ) := by
  have h1 : Continuous fun s => (UpperTheory.V.Af.tw r μ s).val := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  simp only [← map_inv]
  exact h1.comp continuous_inv

theorem ex_good_of_ex_csd : AutomorphicFormsFiniteGL → Ex .csd → Ex .good := by
  intro hA hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hs
  obtain ⟨w₀, hw₀⟩ := exists_place_dvd_prime (K := E) l
  have hsplit : GlobalTheory.UnitaryBC.IsSplitAt w₀ := by
    by_contra h
    exact (hs.2.2.2.2 w₀ h).1 hw₀
  obtain ⟨κ, m, hκ, -, hs'⟩ := _root_.GlobalTheory.GoodCsdTwist.exists_goodCsd_twist hA E l a ha π χ hs w₀ hsplit
  obtain ⟨r', hr'c, hr'⟩ := hcsd E Ω l ι a ha (π.twist κ) _ hs'
  have hκi : (κ⁻¹).IsAlg (-m) := fun k => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hκ k, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨art, hart, hμ⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ⁻¹ (-m) (isAlgPos_of_isAlg hκi)
  refine ⟨UpperTheory.V.Af.tw r' μ, continuous_tw_of_continuous hr'c hμc, ?_⟩
  have h := UpperTheory.V.Af.Cq.attTwist E Ω l ι a r' (π.twist κ) hr' art κ⁻¹ (-m) μ hart hμ
  rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GalCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetLatticeTuplesAgreeingAwayFromPlace
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

theorem GlobalTheory.TwV.Xc.dt_sameAway_step : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v π, IsUnifAt J v π → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → ∃ k ∈ U1 (sigD D), k ∈ intU D.host.F D.host.E ∧ OneOff ((A0 J).pl v).1 k ∧ (J.fd std).dt j La = (J.fd std).dt j Lb * π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) * k) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v π hπ j hj La Lb hab
  have hA := hD j hj La hab.1
  have hB := hD j hj Lb hab.2.1
  have pa := _root_.GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length S hD hS j hj La hab.1
  have pb := _root_.GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length S hD hS j hj Lb hab.2.1
  have sa := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j hj La Lb hab
  have hone := J.one
  obtain ⟨hadd, hint, -, -⟩ := GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) hone.int hS.1 v
  set n : ℤ := len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 with hn
  set k := ((J.fd std).dt j Lb * π ^ n)⁻¹ * (J.fd std).dt j La with hk

  let oh : (AfE D.host.F D.host.E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (ordA (A0 J) v x)) (fun x y => by simp [hadd x y, ofAdd_add])
  have hoh : ∀ x, ordA (A0 J) v x = Multiplicative.toAdd (oh x) := fun x => rfl
  have hkU : k ∈ U1 (sigD D) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ pb.1 (Subgroup.zpow_mem _ hπ.1 n))) pa.1
  have hkOff : OneOff ((A0 J).pl v).1 k := by
    intro w' hw'
    let f : (AfE D.host.F D.host.E)ˣ →* _ := Units.map (prV (E := D.host.E) w').toMonoidHom
    have hfπ : f π = 1 := Units.ext (hπ.2.1 w' hw')
    have hdet : ∀ x : GL (Fin (D.R.N j)) (AfE D.host.F D.host.E),
        f (Matrix.GeneralLinearGroup.det x) = Matrix.GeneralLinearGroup.det (Formalism.UG.bc (prV (E := D.host.E) w') x) := by
      intro x
      apply Units.ext
      simp [f, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    have hfab : f ((J.fd std).dt j La) = f ((J.fd std).dt j Lb) := by
      rw [hA.2.2.2, hB.2.2.2, hdet, hdet, sa.1 w' hw']
    have : f k = 1 := by
      simp only [hk, map_mul, map_inv, map_zpow, hfπ, one_zpow, mul_one, hfab, inv_mul_cancel]
    exact congrArg Units.val this
  have hkOrd : ordA (A0 J) v k = 0 := by
    have hz : ordA (A0 J) v (π ^ n) = n * ordA (A0 J) v π := by
      rw [hoh, hoh, map_zpow, toAdd_zpow, smul_eq_mul]
    have hi : ∀ x, ordA (A0 J) v x⁻¹ = -ordA (A0 J) v x := by
      intro x; rw [hoh, hoh, map_inv, toAdd_inv]
    rw [hk, hadd, hi, hadd, hz, pa.2 v, pb.2 v, hπ.2.2, hn]
    ring
  refine ⟨k, hkU, ?_, hkOff, ?_⟩
  · exact GlobalTheory.TwV.Xc.mem_intU_of_oneOff_ordA _ _ (sigD D) _ _ _ (A0 J) _ hone.good hone.int hS.1 v k hkU hkOff hkOrd
  · rw [hk, mul_inv_cancel_left]
end

