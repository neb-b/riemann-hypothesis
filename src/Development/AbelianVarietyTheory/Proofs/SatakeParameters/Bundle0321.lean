module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockRowSubstitutionPreservesComplexSpan
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeEqPointLatticeOverCompanion
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatCoCompan


open Formalism.L2.GlobalTheoryTheory.Comp in
theorem latCo_eq_latAd_compan : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  intro D i hi co hco a x Lb hfin hspan
  have horth : IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) := by
    intro u v
    have h := hform_mulVec_rect (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
      (co.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) u v
    rw [Matrix.mul_one] at h
    have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) co.1 * co.1 = (gramN D i hi) := hco
    rw [hc] at h
    have e1 : hform (D.sp.cm.sig : D.host.E →+* D.host.E) 1 (co.1 *ᵥ u) (co.1 *ᵥ v) =
        ∑ b, (D.sp.cm.sig : D.host.E →+* D.host.E) ((co.1 *ᵥ u) b) * (co.1 *ᵥ v) b := by
      simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [e1] at h
    exact h
  have hJ : ∀ M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E), IsLat M → IsLat (dl D.sp.cm.sig (gramN D i hi) M) :=
    fun M hM => GlobalTheory.OrthDual.isLat_dl D.sp.cm.sig (gramN D i hi) (toLE co) horth M hM
  have hLb : IsLat Lb := ⟨hfin, hspan⟩
  have hx : x.1 ∈ UPts D.sp.cm.sig (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := x.2
  have hC : IsLat (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero]; exact hLb
    · rw [GlobalTheory.SDCompan.compan_eq]; exact isLat_sup hLb (isLat_smul (hJ _ hLb) ha)
  refine ⟨?_, hC.1, hC.2⟩
  have hG : compan (sp := D.sp) (gramN D i hi) a (latAd x.1 Lb) = latAd x.1 (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero, GlobalTheory.SDCompan.compan_zero]
    · rw [GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.latAd_eq, GlobalTheory.SDCompan.latAd_eq]
      symm
      rw [glob_sup hLb (isLat_smul (hJ _ hLb) ha), glob_smul (hJ _ hLb) ha,
        glob_dl D.sp.cm.sig (gramN D i hi) hJ hLb x.1 hx]
  unfold latCo
  rw [hG, latAd_rat]

end GlobalTheory.LatCoCompan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonDataStatementsAtSite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HP


set_option maxHeartbeats 4000000 in
theorem cmpJHyp_inTw_site : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (T : ∀ u : D.what₂.Word, Forms0 D u) (c : LatCmp D), CmpTied D X0 T Gt c → FillTie Gt u w hg Fl → SiteGood Z → SiteRest Z c → CmpJHyp c (Z.inTw Fl ht Gt) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt T c K hF G A
  refine HypTiesI.hyp (X0 := X0) ⟨ht, hF, fun j hj => ⟨Z.Fo j hj, Z.loc Fl ht j hj, rfl, ?_⟩⟩ K
  exact
    { frRat := Z.frRat Fl ht j hj
      sameU := Z.sameU Fl ht j hj
      hypT := hypTJ_site Z Fl ht G.siteGood_prime_torsion G.bad_p j hj
      bad_p := G.bad_p j hj
      std := A.std j hj
      psi := A.psi j hj
      chRat := A.chRat j hj
      hypC := hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj
      ok := G.ok j hj
      siteGood_prime_torsion := G.siteGood_prime_torsion j hj
      Lb_eq := fun _ => (reL_symm (rankN D (j + 1) hj) _).symm }

end GlobalTheory.HP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonSiteChartsTwistsEqTupleChain
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Port

theorem gl_one_eq_of_det_eq {R : Type*} [CommRing R] (g h : GL (Fin 1) R)
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : (g : Matrix (Fin 1) (Fin 1) R).det = (h : Matrix (Fin 1) (Fin 1) R).det := by
    have := congrArg Units.val e
    simpa using this
  ext i k
  rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
  simpa [Matrix.det_unique] using e'

theorem siteD_inTw_charts_tw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : GlobalTheory.TwU.ChainCharts D u μ) (hv : ValAll Tw St), Z.Fo = foOf Hh St hv → (∀ j hj, St (j + 1) hj = GlobalTheory.TwU.StepCharts.ofStepIn ((Z.inTw Fl ht Gt).at' j hj).st) ∧ ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → (((Z.inTw Fl ht Gt).at' j hj).st.tw β).ch x = D.chiD (Hh.dt y) ^ cTw D (j + 1) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt Hh St hv hZ
  obtain ⟨Fo, fin, S⟩ := Z
  dsimp only at hZ
  subst hZ
  refine ⟨fun j hj => rfl, ?_⟩
  intro j hj β x y hy
  have hyx : y = detU D (j + 1) hj x := by
    apply Subtype.ext
    apply gl_one_eq_of_det_eq
    rw [det_detU]
    exact hy
  subst hyx
  rfl

end GlobalTheory.Port
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexBlockActionInvReadAsSubstitution
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA.ActInv

theorem det_inv_gl {n : ℕ} {F : Type} [Field F] (A : GL (Fin n) F) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = (A : Matrix (Fin n) (Fin n) F).det⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem det_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((hAt P h pos (fun _ => 1) g v s : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det =
      if Even s.val then (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det
      else (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det⁻¹ := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    show (Matrix.transpose (((reG P h (g (pos ⟨v, s⟩)))⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det = _
    rw [Matrix.det_transpose, det_inv_gl]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det⁻¹ = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]

theorem inv_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    (((hAt P h pos (fun _ => 1) g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) =
      if Even s.val then reM P h (((g (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      else Matrix.transpose (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    rw [← map_inv]
    rfl
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.TwV.DelA.ActInv


open GlobalTheory.TwV.DelA.ActInv in
theorem GlobalTheory.TwV.DelA.actC_inv_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j hN La' M hU hF R
  have hblk := GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU
  have hcoe : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin k) A),
      ((Matrix.GeneralLinearGroup.map f g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) = (g : Matrix (Fin k) (Fin k) A).map f :=
    fun _ _ => rfl
  have hdm : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Matrix (Fin k) (Fin k) A),
      (g.map f).det = f g.det := fun f g => (RingHom.map_det f g).symm
  have hev : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Even s.val ↔ ¬ IsOddPos s := by
    intro v s; unfold IsOddPos; rw [Nat.even_iff]; omega
  have hsc : (∏ v, ∏ s, ((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc).det ^ (-eAt (X.Pj (j + 1)) v s)) =
      ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) := by
    rw [map_prod, ← Equiv.prod_comp pos, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    have he : eAt (X.Pj (j + 1)) v s = eT X D pos (j + 1) (pos ⟨v, s⟩) := by
      show _ = eAt (X.Pj (j + 1)) ((pos.symm (pos ⟨v, s⟩)).1) ((pos.symm (pos ⟨v, s⟩)).2)
      rw [Equiv.symm_apply_apply]
    rw [he, (eT_last_pair X D pos j _).2, Equiv.symm_apply_apply, hcoe, hdm, det_placeBlockMatrix_unit_twist]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    simp only [atR]
    rw [hcoe, hdm, det_inv_gl, map_inv₀]
    split_ifs with h1 h2 h3
    · exact absurd h2 ((hev v s).1 h1)
    · rw [map_inv₀, map_zpow₀, inv_zpow', neg_neg]
      rfl
    · rw [inv_inv, map_zpow₀, neg_sub]
      rfl
    · exact absurd ((hev v s).2 h3) h1
  have hent : ∀ (v : Fin (X.Pj (j + 1)).nV) (s : Fin ((X.Pj (j + 1)).n' v)) (a b : Fin ((X.Pj (j + 1)).m + 1)),
      ((((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc) a b =
      GlobalTheory.FrameB.mk Kc fd j La' v s (Fin.cast (rankJ X (j + 1)) a) (Fin.cast (rankJ X (j + 1)) b) := by
    intro v s a b
    rw [← map_inv, hcoe, Matrix.map_apply, inv_placeBlockMatrix_unit_twist]
    have hb := congrFun (congrFun (hblk v s).1 (finCongr (rkT X D hN) a)) (finCongr (rkT X D hN) b)
    have hinv : (atR D M (pos ⟨v, s⟩))⁻¹ = atR D M⁻¹ (pos ⟨v, s⟩) := by simp [atR, map_inv]
    unfold GlobalTheory.FrameB.mk mAt
    rw [Matrix.submatrix_apply, Matrix.map_apply, hF v, Matrix.submatrix_apply]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    split_ifs at hb with h2 <;> split_ifs with h1
    · exact absurd h2 ((hev v s).1 h1)
    · simp only [Matrix.map_apply, Matrix.transpose_apply] at hb
      rw [hinv] at hb
      exact hb
    · simp only [Matrix.map_apply] at hb
      have e : ((atR D M⁻¹ (pos ⟨v, s⟩))⁻¹ : GL (Fin (D.R.N (j + 1))) ℂ) = atR D M (pos ⟨v, s⟩) := by rw [← hinv, inv_inv]
      refine Eq.trans ?_ hb
      exact congrArg ι (congrArg (fun g : GL (Fin (D.R.N (j + 1))) ℂ => (g : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (finCongr (rkT X D hN) a) (finCongr (rkT X D hN) b)) e)
    · exact absurd ((hev v s).2 h2) h1
  have hsub : (substR (X.Pj (j + 1)) Kc fun v s => (((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc)) = GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, GlobalTheory.FrameB.tau0, MvPolynomial.aeval_X, GlobalTheory.FrameB.frF]
    refine Fintype.sum_equiv (finCongr (rankJ X (j + 1))) _ _ fun b => ?_
    rw [hent v s a b]
    congr 2
  unfold actC
  rw [map_natActR]
  unfold natActR
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hsc, hsub]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitAttUniq

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem repIso_of_dense {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
    (r r' : G E Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (D : Set (G E Ω)) (hD : Dense D)
    (he : ∀ g ∈ D, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    UpperTheory.V.Af.RepIso r r' := by
  have hcp : ∀ g : G E Ω, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc)
    have h2 : Continuous fun g : G E Ω => (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc')
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    intro σ hσ
    simp only [he σ hσ]
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' hcp
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.SplitAttUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockActionStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalBasisCoords_against_blockAction : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n), (∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) → evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧ actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  first | exact @GlobalTheory.TwV.DelA.evC_crdB_actC | exact GlobalTheory.TwV.DelA.evC_crdB_actC | (intros; apply GlobalTheory.TwV.DelA.evC_crdB_actC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCEmbCLam
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem exists_cEmbC_lam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ (E : CEmbC (sysS H X std).G) (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]), ∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (ex.cmp.embW u w hg z) = lam ⟨D.what₂.embLL z, hz⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  have hV : 0 < (sysS H X std).G.P.nV := (Gl.vOf u w hg 0).pos
  obtain ⟨E⟩ := GlobalTheory.TwU.nonempty_cEmbC _ (sysS H X std).G hV
  obtain ⟨lam, hlam⟩ := GlobalTheory.padic_emb_extends_algebraicClosure (D.what₂.places.resChar w) D.what₂.LL D.what₂.embLL
    (E.iK.comp (ex.cmp.embW u w hg))
  exact ⟨E, lam, fun z hz => hlam z hz⟩

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepsOfCls
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.exists_finset_reps_of_cls {T Γ C : Type} [Finite C] (P : T → Prop) (sm : Γ → T → T) (cls : T → C)
    (h : ∀ L L', P L → P L' → cls L = cls L' → ∃ γ, L' = sm γ L) :
    ∃ R : Finset T, (∀ L ∈ R, P L) ∧ ∀ L, P L → ∃ L₀ ∈ R, ∃ γ : Γ, L = sm γ L₀ := by
  classical
  let S : Set C := {x | ∃ L, P L ∧ cls L = x}
  have hS : ∀ x : S, ∃ L, P L ∧ cls L = x.1 := fun x => x.2
  choose f hf using hS
  haveI : Fintype S := Fintype.ofFinite S
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hL
    exact (hf x).1
  · intro L hL
    let x : S := ⟨cls L, L, hL, rfl⟩
    exact ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x), h (f x) L (hf x).1 hL (hf x).2⟩


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.finClasses_sysS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j c
  change (Lv.lev j c).FinClasses
  by_cases hj : j ≤ D.R.m
  · exact GlobalTheory.TwV.exists_finset_reps_of_cls (C := (D.chTw u μ).cls j) _ (Lv.lev j c).smul ((labAt X H).cls j c)
      (fun L L' hL hL' e => (((labAt X H).cls_iff j hj c c L L' hL hL').1 e).2)
  · exact (J.empty j (by omega)).elim c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinStabSite
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem finStab_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), FinStab (sysS H X std).Lv := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  show FinStab Lv
  intro j c La hLa
  by_cases hj : j ≤ D.R.m
  · exact Nat.finite_of_card_ne_zero ((labAt X H).stab_dvd j hj c La hLa).1.ne'
  · exact (J.empty j (by omega)).elim c

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication
section
namespace GlobalTheory.TwV.Lt

theorem inert_theta_admissibility_of_complex_multiplication : Formalism.L2.Th1.CM.CM2 → GlobalTheory.TwV.Lt.AdmAtEnt2 := fun h => by
  haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
  exact Formalism.L2.KerInert.AdmLoc2.admissible_entries_small_chain

end GlobalTheory.TwV.Lt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatKOfStdL
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KerSelfDual

theorem isSDLat_latK_of_stdL : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (co : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → latCo D.sp (gramN D i hi) co a 1 lev.Lb = StandardLatticesGL3.stdL D (D.R.N i) → ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsSDLat D.host.E (D.R.N i) (latK D.sp (gramN D i hi) a x.1 lev.Lb) := by
  intro D i hi T bad lev co a hco hstd x
  have hc : IsOrthCo ((sigD D : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) :=
    GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ co hco
  have hc' : ∃ c, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) c := ⟨toLE co, hc⟩
  have hJ := GlobalTheory.isLat_dl_of_isOrthCo D.sp (gramN D i hi) hc'
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have h1 : Formalism.L2.PairingIndexBounds.F.latAd (1 : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) lev.Lb = lev.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one hLb
  have hm : mvL co (compan (sp := D.sp) (gramN D i hi) a lev.Lb) = StandardLatticesGL3.stdL D (D.R.N i) := by
    rw [← hstd, latCo, h1]
  have hsd := GlobalTheory.FourthRootStd.stdL_isSD D (D.R.N i)
  rw [← hm] at hsd
  obtain ⟨hM, hdl⟩ := GlobalTheory.OrthSelfDual.isLat_and_dl_eq_of_isSDLat_mvL D.sp (gramN D i hi) co _ hc hsd
  exact GlobalTheory.SDCompan.isSDLat_latK D.sp (gramN D i hi) hJ hc' x.1 x.2 lev.Lb a hLb hM hdl

end GlobalTheory.KerSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlaces
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.Joint.basesAt_span : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j La hLa v
  obtain ⟨g, hdet, hg'⟩ := Formalism.L2.G.Pend.latAt_isLattice (sysS H X std) j La.2 hLa v
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hdet
  unfold basesAt
  exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _)) ⟨hu.unit, by rw [hu.unit_spec]; exact hg'⟩
end

