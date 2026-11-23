module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameFactorsCancelPPowerOfPairSeries
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem eFac_mul_pPow : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), E.iK ((pendT X E hfin hst hLT pos F).eS j La * ((pendT X E hfin hst hLT pos F).eT j La')⁻¹) * pPow X j La La' = 1 := by
  intro p _ X _ E hfin hst g hLT T pos F j La La'
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  show E.iK (Pend.eS _ j La * (Pend.eT _ j La')⁻¹) * pPow X j La La' = 1
  simp only [Pend.eS, Pend.eT]
  rw [pPow_eq_prod]
  rw [map_mul, map_inv₀, map_prod, map_prod]
  simp only [map_zpow₀, map_natCast]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun v _ => ?_)
  rw [← zpow_neg, ← zpow_add₀ hp, ← zpow_add₀ hp]
  show (p : ℂ_[p]) ^ _ = 1
  ring_nf
  simp

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSphericalStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w (n := a)) → ξ.UnrAt w := by
  first | exact @GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | exact GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | (intros; apply GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterFiniteIdeleEqProdValuesZpow
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.HeckeFinVal

open Neutral.B1 Formalism.L2.Host PI.HeckeProdW

theorem idele_ext {L : Type} [Field L] [NumberField L] {a c : Ideles L}
    (h1 : ∀ w, pw w a = pw w c) (h2 : ∀ v, pv v a = pv v c) : a = c :=
  Units.ext (Prod.ext (funext fun w => h1 w) (Subtype.ext (funext fun v => h2 v)))

theorem loc_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.UnrAt P) (x : (P.adicCompletion L)ˣ) : ∃ k : ℤ, χ.loc P x = χ.val P ^ k := by
  have hx0 : Valued.v (x : P.adicCompletion L) ≠ 0 := by simp
  set m : ℤ := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hxm : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log hx0).symm
  set ϖ : (P.adicCompletion L)ˣ := atFin P (unif P) with hϖ
  have hϖv : Valued.v (ϖ : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  refine ⟨-m, ?_⟩
  have hu : IsUnitAt P (x * ϖ ^ m) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxm, hϖv, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h3 := hP _ hu
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact h3

theorem eq_prod_val_zpow : ∀ {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (b : Neutral.B1.Ideles L), Formalism.L2.Host.IsFinIdele b → (∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) →
    (∀ P ∈ T, χ.UnrAt P) → ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P := by
  intro L _ _ χ T b hb hout hunr
  classical
  let u : ∀ P : HeightOneSpectrum (𝓞 L), (P.adicCompletion L)ˣ := fun P =>
    ⟨pv P b, pv P b⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hdec : b = ∏ P ∈ T, localIdele L P (u P) := by
    refine idele_ext (fun w => ?_) (fun v => ?_)
    · rw [map_prod]
      rw [Finset.prod_eq_one fun P _ => pw_local w P (u P)]
      exact hb w
    · rw [map_prod]
      by_cases hv : v ∈ T
      · rw [Finset.prod_eq_single v]
        · rw [pv_local_self]
        · intro P _ hPv
          exact pv_local_ne P v (Ne.symm hPv) _
        · intro h; exact absurd hv h
      · rw [Finset.prod_eq_one fun P hP => pv_local_ne P v (fun e => hv (e ▸ hP)) _]
        exact hout v hv
  have hk : ∀ P ∈ T, ∃ k : ℤ, χ.loc P (u P) = χ.val P ^ k := fun P hP => loc_eq_val_zpow χ P (hunr P hP) (u P)
  choose! n hn using hk
  refine ⟨n, ?_⟩
  rw [hdec, map_prod]
  exact Finset.prod_congr rfl fun P hP => hn P hP

end GlobalTheory.HeckeFinVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  first | exact @GlobalTheory.GalCut.infinite_qcm_split_good | exact GlobalTheory.GalCut.infinite_qcm_split_good | (intros; apply GlobalTheory.GalCut.infinite_qcm_split_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugateStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  first | exact @GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | exact GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | (intros; apply GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelic
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem homRe_rfl {E : Type} [Field E] {a b : ℕ} (x : Formalism.L2.Col.HomE E a b) : homRe (rfl : a = a) (rfl : b = b) x = x := by
  apply LinearMap.ext
  intro v
  funext i
  simp [homRe]

theorem reV_rfl {D : D7} {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : reV (rfl : a = a) (rfl : b = b) G = G := by
  funext z
  simp [reV]

theorem inFr_symm_inFr {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (x : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' x) = x := by
  apply LinearMap.ext
  intro v
  simp [Formalism.L2.Col.inFr]

theorem kerTh_homRe {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)} {M' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)}
    {L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N)} {L' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N')}
    (hM : HEq M L) (hM' : HEq M' L') (Ξ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) :
    kerTh B χ SS c M M' (fun x => Ξ (homRe ha hb x)) = reV ha hb (kerTh B χ SS c L L' Ξ) := by
  subst ha hb
  cases eq_of_heq hM
  cases eq_of_heq hM'
  simp only [homRe_rfl, reV_rfl]


set_option maxHeartbeats 1000000 in
theorem kerTh_pair_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj hr hr' La La' hLa hLa'
  obtain ⟨-, -, h1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨-, -, h2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun x =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe hr hr' x) := by
    funext x
    simp only [xiM, movD, Joint.xi0]
    rw [dite_eq_left ⟨hj, hr, hr'⟩, inFr_symm_inFr]
  rw [hx]
  exact kerTh_homRe _ _ _ _ hr hr' h1 h2 _

end GlobalTheory.TwV.DelB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSite
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerSiteSelfDual

theorem isSDLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {n N : ℕ} (h : n = N)
    {L : Submodule (𝓞 E) (Fin n → E)} {M : Submodule (𝓞 E) (Fin N → E)} (hL : HEq L M) (hM : Formalism.BasicNotions.IsSDLat E N M) :
    Formalism.BasicNotions.IsSDLat E n L := by
  subst h
  cases hL
  exact hM


set_option maxHeartbeats 2000000 in
theorem even_and_isSDLat_kerN : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hk, -⟩ := hD j hj La hLa
  refine ⟨hr ▸ Formalism.MainNotions.product_zeroth_first_parts.N_even D.R j, isSDLat_of_heq hr hk ?_⟩
  exact GlobalTheory.KerSelfDual.isSDLat_latK_of_stdL ((J.St j hj).K (J.chart std j hj La)).lev (J.A.crd j hj) J.a
    (J.pins.crd_orth j hj) (J.base j hj _) (J.pt std j hj La)

end GlobalTheory.KerSiteSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem kernelSite_seriesData_below_lastStep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hP hPos hSc
  refine ⟨?_, ?_, ?_, hSc, J.rho std, ?_, ?_, ?_⟩
  · intro j hj L0 hL0 La' hLa'
    exact (hP j hj L0 La' (repOf_lat _ _ j L0 hL0) hLa').1
  · obtain ⟨hpos, hS⟩ := _root_.GlobalTheory.TwV.sNum_lev_site t std J
    exact ⟨hpos, fun hd => _root_.GlobalTheory.TwV.SitePrime.resChar_not_mem_S t std J (hS _ Fact.out hd)⟩
  · exact ⟨(t.O u μ).S, _root_.GlobalTheory.TwV.SitePrime.resChar_not_mem_S t std J, fun j _ L0 _ La' _ y => _root_.GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes t std J S j L0 La' y⟩
  · exact GlobalTheory.TwU.lamPosG_of_lamPos _ S.E D _ _ _ hPos
  · exact fun j La v => GlobalTheory.isUnit_det_frameMatrix_ofCharts _ _ _ j La v
  · refine _root_.GlobalTheory.TwV.frameLatMapLt_of_ties _ S.hfin D (J.fd std) (J.rho std) (halfDiffInv_integral_at_split D _ _ hg) ?_
    intro j hj La La' h1 h2
    have q := hP j hj La La' h1 h2
    exact ⟨q.1, fun v => ⟨(q.2.2.2.2.2.2.2 v).2.2.1, (q.2.2.2.2.2.2.2 v).2.2.2⟩⟩

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdLocOf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latAdLoc_of : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), SplAlg A → LocInt A → Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ → LatAdLoc A Lb := by
  intro F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v
  letI : StarRing E := starRingOfComm
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) :=
    Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY
  set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v :=
    ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf
  have hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f := by
    rw [hY]; ext i j; rfl
  have hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F,
      (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) =
        ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ
          (fun k => (A.eQ v).symm (A.ph v (u k))) := by
    intro u
    rw [hfac]
    funext k
    exact RingHom.map_mulVec f Y u k
  ext z'
  rw [locSp_eq_image A hS hI v, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzz⟩
    rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan] at hz
    set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu
    refine ⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩
    have hzu : z = Y *ᵥ u := by
      rw [hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'
    rw [← hmv, ← hzu]
    funext k
    exact hzz k
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hu, huw⟩ := (locSp_eq_image A hS hI v Lb w).1 hw
    refine ⟨Y *ᵥ u, ?_, ?_⟩
    · have hback : Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ
          (Y *ᵥ u) = u := by
        rw [hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]
      rw [hback]
      exact hu
    · intro k
      have hw' : w = fun k => (A.eQ v).symm (A.ph v (u k)) := funext fun k => (huw k).symm
      subst hwz
      subst hw'
      exact congrFun (hmv u) k

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponent
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem chart_eq_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c La Lb hLa hLb
  unfold Joint.chart
  rcases j with _ | j
  · haveI := J.ch0
    exact Subsingleton.elim _ _
  · simp only
    rw [Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c La, Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c Lb]
    have ea := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c La hLa
    have eb := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c Lb hLb
    have key : ∀ (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (h : (I.at' j hj).C = C) (St' : GlobalTheory.TwU.StepCharts C (j + 1) hj)
        (_ : St' = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st)) (x y : (I.at' j hj).C.cls (j + 1)),
        (I.at' j hj).st.chOf x = (I.at' j hj).st.chOf y →
        St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) x) = St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) y) := by
      intro C h St' hst x y e
      subst h
      subst hst
      exact e
    exact key _ (X.onCh j hj) _ (J.st j hj) _ _ (ea.trans eb.symm)

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponent
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem frM_fd_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), (J.fd std).frM j (c, La) = (J.fd std).frM j (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j c La Lb
  funext v
  cases j with
  | zero =>
    simp only [Joint.fd, fdAtL, fdAt, fdOfCharts, cpAt, chAt]
    rfl
  | succ i => exact Formalism.MainNotions.G.KAat.frM_comp i c La Lb v

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPoints
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem xiM_eq_adelic : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' z = S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe hr hr' z)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj hr hr' La La' z
  have h : j + 1 ≤ D.R.m ∧ ((sysS H X std).Pj j).m + 1 = D.R.N j ∧ ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := ⟨hj, hr, hr'⟩
  have hz : Formalism.L2.Col.inFr ((J.fd std).trG j La).symm ((J.fd std).trG (j + 1) La').symm
      (Formalism.L2.Col.inFr ((J.fd std).trG j La) ((J.fd std).trG (j + 1) La') z) = z := by
    unfold Formalism.L2.Col.inFr
    ext x
    simp
  show Formalism.L2.PairingIndexBounds.F.movD _ _ _ z = _
  unfold Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dite_eq_left h, hz]

end GlobalTheory.TwV.Xc
end

