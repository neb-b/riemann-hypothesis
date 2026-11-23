module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.Joint.isPt_pt_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  have hr := (lev0At J.Gd u w hg).A.rk
  obtain ⟨x0, hx0⟩ := GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
    (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
      (sysS H X std).dG_spec (sysS H X std).om 0 La.2)
  have hs := Classical.epsilon_spec (p := fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hex : ∃ x, J.IsPt std 0 (Nat.zero_le _) La x := by
    refine ⟨⟨_, hs.2⟩, hr, ?_⟩
    ext i j
    rfl
  have hp := Classical.epsilon_spec hex
  obtain ⟨hr', he⟩ := hp
  refine ⟨⟨hr', he⟩, ?_⟩
  have h1 : (J.pt std 0 (Nat.zero_le _) La).1 = Classical.epsilon (fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [show (J.pt std 0 (Nat.zero_le _) La).1 = _ from he]
    ext i j
    rfl
  rw [h1]
  exact hs.1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChart
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.ChartSucc

theorem castSt_ofStepIn_chart {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) :
    St.T = S.T ∧ (St.K (St.chOf c')).lev.Lb = (S.K β).lev.Lb ∧ (St.K (St.chOf c')).lev.U = (S.K β).lev.U ∧
      (St.K (St.chOf c')).lev.Uloc = (S.K β).lev.Uloc ∧ ∀ hc : S.chOf c = β, St.y c' = (S.K β).y ⟨c, hc⟩ := by
  subst hSt hc' h hβ
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory.TwV.ChartSucc

theorem GlobalTheory.TwV.chart_succ_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  obtain ⟨hT', hLb, hU, hUl, hy⟩ := GlobalTheory.TwV.ChartSucc.castSt_ofStepIn_chart (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj)
    _ (clsAt X H (j + 1) La.1 La.2) (clsAt_succ X H j hj La.1 La.2) _ hc
  refine ⟨hT'.symm.trans (J.tie.T_eq (j + 1) hj), hLb, hU, hUl, hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


set_option maxHeartbeats 2000000 in
theorem joint_dt_eq_det_of_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La x hx
  obtain ⟨hr, hx⟩ := hx
  have h1 : (J.fd std).dt j La = Matrix.GeneralLinearGroup.det ((J.cp std).y j La) := rfl
  rw [h1, hx]
  exact ((reindex_rename_point_det_latK D.sp hr 0 0 ((J.cp std).y j La) ⊥).2.1).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearChoiceEqRealisingPolynomial
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem phiC_eq_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Realises X D pos i h a Q R → phiC X D pos i h a Q = R := by
  intro p _ X D pos i n h a Q R hR
  have hmem : Q ∈ (relPhi X D pos i h a).map (LinearMap.fst ℂ _ _) :=
    Submodule.mem_map.2 ⟨(Q, R), hR, rfl⟩
  have hsel : Realises X D pos i h a Q (phiC X D pos i h a Q) := selOf_mem (relPhi X D pos i h a) Q hmem
  have hz : phiC X D pos i h a Q - R = 0 := by
    apply _root_.GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames X D pos i h
    intro f
    rw [map_sub, Pi.sub_apply, hsel f, hR f, sub_self]
  exact sub_eq_zero.1 hz

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpEqImage
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem locSp_eq_image : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → LocInt A → ∀ v (Λ : Submodule (𝓞 E) (Fin n → E)) (z' : Fin n → G.P.Qq v), z' ∈ locSp (G.P.W v) (A.iw v) Λ ↔ ∃ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ, ∀ k, (A.eQ v).symm (A.ph v (z k)) = z' k := by
  intro F E _ _ _ _ _ n p G A hS hI v Λ z'
  have hph := _root_.GlobalTheory.TwV.ph_tensInt_onto A hS v
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨fun k => inclE (F := F) _ (x k), Submodule.subset_span ⟨x, hx, rfl⟩, fun k => ?_⟩
      rfl
    | zero => exact ⟨0, Submodule.zero_mem _, fun k => by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨z₁, hz₁, e₁⟩ := h₁
      obtain ⟨z₂, hz₂, e₂⟩ := h₂
      refine ⟨z₁ + z₂, Submodule.add_mem _ hz₁ hz₂, fun k => ?_⟩
      simp [e₁ k, e₂ k]
    | smul w y _ h =>
      obtain ⟨z, hz, e⟩ := h
      have hw : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) w) ∈ (A.pl v).1.adicCompletionIntegers F :=
        (hI v _).1 ⟨w, rfl⟩
      obtain ⟨s, hs, hse⟩ := hph.2 _ hw
      refine ⟨(⟨s, hs⟩ : intV E (A.pl v).1) • z, Submodule.smul_mem _ _ hz, fun k => ?_⟩
      show (A.eQ v).symm (A.ph v (s * z k)) = (w • y) k
      rw [map_mul, hse, map_mul, e k, RingEquiv.symm_apply_apply, Pi.smul_apply, Algebra.smul_def]
  · rintro ⟨z, hz, hzz⟩
    have key : ∀ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ,
        (fun k => (A.eQ v).symm (A.ph v (z k))) ∈ locSp (G.P.W v) (A.iw v) Λ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have h0 := Submodule.zero_mem (locSp (G.P.W v) (A.iw v) Λ)
        convert h0 using 1
        funext k
        simp
      | add y₁ y₂ _ _ h₁ h₂ =>
        have := Submodule.add_mem _ h₁ h₂
        simpa [Pi.add_def] using this
      | smul s y _ h =>
        obtain ⟨w, hw⟩ := (hI v ((A.eQ v).symm (A.ph v s))).2 (by simpa using hph.1 s.1 s.2)
        have := Submodule.smul_mem _ w h
        convert this using 1
        funext k
        show (A.eQ v).symm (A.ph v (s.1 * y k)) = _
        rw [Pi.smul_apply, Algebra.smul_def, hw, map_mul, map_mul]
    have := key z hz
    convert this using 1
    funext k
    exact (hzz k).symm

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpLatAdIsPt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.SpanPt

theorem colSpan_map {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M X : Matrix (Fin k) (Fin k) K) :
    (colSpan R X).map ((M.mulVecLin).restrictScalars R) = colSpan R (M * X) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1


set_option maxHeartbeats 400000 in
theorem locSp_latAd_isPt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), LatAdLoc A Lb → LbAtB A Lb → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))), A.IsPt i g y → ∀ v, locSp (G.P.W v) (A.iw v) (latAd y Lb) = colSpan (G.P.W v) (((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin n) (Fin n) (G.P.Qq v))) := by
  intro F E _ _ _ _ _ n p G A Lb hA hB i g y hy v
  rw [hA y v, hB v, colSpan_map, GlobalTheory.TwV.FacQPt.facQ_isPt A i g y hy v]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Units.val_mul (bc (A.iw v) A.B)⁻¹, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.TwV.SpanPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumEqAdelicDatum
section
noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inFr_symm_inFr_cancel {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a)
    (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (z : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' z) = z := by
  refine LinearMap.ext fun x => ?_
  simp [Formalism.L2.Col.inFr]


set_option maxHeartbeats 2000000 in
theorem moved_pair_datum_eq_adelic_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J Xi j hj h1 h2 La La' z
  unfold GlobalTheory.TwU.xiM Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dite_eq_left ⟨hj, h1, h2⟩, inFr_symm_inFr_cancel]

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProductStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muCharacter_det_level_eq_local_tame_product : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    MuLaw t u μ dtU → ∀ i, i < D.R.m → ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (κ : ((St j hj).K β).lev.U) (e : SB t μ → t.X.E),
      (∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE (e P)) - 1))) →
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) i P (e P)) = 1 ∧
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) = t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P (e P))) := by
  first | exact @GlobalTheory.LevMuDet.muOf_det_lev | exact GlobalTheory.LevMuDet.muOf_det_lev | (intros; apply GlobalTheory.LevMuDet.muOf_det_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCodimOneStalkDvr
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

theorem sphAt_of_repIso {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : CuspSub E a) {r r' : G E Ω →* GL (Fin a) (Qbar l)}
    (hr : Continuous r) (hiso : UpperTheory.V.Af.RepIso r r') (c : GlobalTheory.RoadU.Sph) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hc : GlobalTheory.RoadU.SphAt c π ι r w B) : GlobalTheory.RoadU.SphAt c π ι r' w B := by
  cases c with
  | unr =>
    obtain ⟨p, hp⟩ := hiso
    intro hl A hA
    obtain ⟨h1, h2⟩ := hc hl A hA
    refine ⟨fun s hs => by rw [hp, h1 s hs]; group, fun σ hσ => ?_⟩
    rw [← h2 σ hσ, hp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  | dR => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .dR w hc
  | crys => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .crys w hc
  | phi =>
    obtain ⟨p, hp⟩ := hiso
    have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
        p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
    intro P AI hT A h O _ _ _ Bw hj g
    have e := GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)
    exact (congrArg (fun x => WD.charPol x g) e).trans (hc P AI hT A h O Bw hj g)

theorem core_of_rowStarCore : GlobalTheory.RoadW.RowStarCore → GlobalTheory.RoadU.Core := by
  intro h
  refine ⟨fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hs => ?_, fun c E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w _ B hB => ?_⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r, hr, -⟩ := h E Ω l ι a ha π hs
    exact ⟨r, hr⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r₀, hr₀, hc⟩ := h E Ω l ι a ha π hs
    refine sphAt_of_repIso ι π hr₀.1 (weak_repIso E Ω l ι a π r₀ r hr₀ hr) c w B ?_
    obtain ⟨h1, h2, h3, h4⟩ := hc w B hB
    cases c
    exacts [h1, h2, h3, h4]

end GlobalTheory.RoadW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPoint
section
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem pow_toNat_split {K : Type} [Field K] {a : K} (ha : a ≠ 0) (e : ℤ) :
    a ^ e.toNat = a ^ (-e).toNat * a ^ e := by
  have h := Int.toNat_sub_toNat_neg e
  calc a ^ e.toNat = a ^ (-e).toNat * a ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by
        rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
        field_simp
    _ = _ := by rw [h]

theorem zT_det_ne {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have h1 : (((f τ)⁻¹).transpose.submatrix id Fin.rev).det
        = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) * (((f τ)⁻¹).transpose).det := by
      exact Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) (((f τ)⁻¹).transpose)
    rw [h1, Matrix.det_transpose, Matrix.det_nonsing_inv]
    refine mul_ne_zero (by simp) ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (hf τ)
  · exact hf τ

theorem det_rev_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
  have : (A.transpose.submatrix Fin.rev id).det = _ := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) A.transpose
  rw [this, Matrix.det_transpose, sgRev]

theorem evD_det {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (DA X Kc j)) : evD X D pos ι hN d f' M.det = (M.map (evD X D pos ι hN d f')).det :=
  RingHom.map_det _ M

theorem det_map_cast {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) {a b : ℕ} (h : a = b) (B : Matrix (Fin b) (Fin b) ℂ) :
    ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = ι B.det := by
  have : ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = (B.map ι).det :=
    Matrix.det_submatrix_equiv_self (finCongr h) (B.map ι)
  rw [this, RingHom.map_det]
  rfl

theorem evD_numD_denD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  intro p _ X D pos Kc _ _ ι j hN d f' hf hd
  classical
  have key := _root_.GlobalTheory.TwV.DelA.evD_blockMats X D pos Kc ι j hN d f' hf hd
  have e : ∀ G : D.what₂.Tau → ℂ, ∏ τ, G τ = ∏ v, ∏ s, G (pos ⟨v, s⟩) := fun G => by
    rw [← Equiv.prod_comp pos G, Fintype.prod_sigma]
  rw [e, map_prod]
  unfold numD denD
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [cT1, szT]
  rw [Equiv.symm_apply_apply]
  obtain ⟨k1, k2, k3⟩ := key v s
  by_cases hs : IsOddPos s
  · simp only [if_pos hs]
    have hY : evD X D pos ι hN d f' (YtMat X Kc j v s).det
        = ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) := by
      rw [evD_det, k3 hs, Matrix.det_smul, det_map_cast, det_rev_transpose, Fintype.card_fin,
        show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
      simp only [map_mul, map_pow]
      ring
    have ha : ι (zT X D pos f' (pos ⟨v, s⟩)).det ≠ 0 := (map_ne_zero ι).2 (zT_det_ne X D pos f' hf _)
    have hb : ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) ≠ 0 := by
      refine (map_ne_zero ι).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (zT_det_ne X D pos f' hf _)) ?_) (hd _))
      simp [sgRev]
    rw [map_mul ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ _), map_zpow₀, map_zpow₀]
    rw [map_mul (evD X D pos ι hN d f'), map_mul (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'),
      map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), k1, hY,
      pow_toNat_split ha (exY X j v s), pow_toNat_split hb (exT X j v s)]
    have h1 : exY X j v s = cMu X j v s - szMu X j v s := rfl
    have h2 : exT X j v s = cMu X j v s - (D.R.N j : ℤ) * cMu X j v s + szMu X j v s := by
      rw [exT, show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
    rw [h1, h2]
    ring
  · simp only [if_neg hs]
    rw [map_one, one_mul, map_pow (evD X D pos ι hN d f'), evD_det, k2 hs, det_map_cast, map_pow]

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolDYGoodDeg
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem polDY_goodDeg : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), ∀ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, GoodDeg X j (α.mapDomain (eIdx X D pos j hN)) := by
  intro p _ X D pos j hN ν hν Q hQ s α hα
  unfold GoodDeg
  intro v t
  have hsz := (_root_.GlobalTheory.TwV.DelA.size_first_last_rows X D pos j hN ν hν).2.1 (pos ⟨v, t⟩)
  unfold szT szMu at hsz
  rw [pos.symm_apply_apply] at hsz
  rw [hsz, Formalism.L2.KerInert.SecondKernelMoveDegree.blk_mapDomain X D pos j hN α v t, Finset.sum_comm,
    polDY_exp_deg D s ν Q hQ α hα (pos ⟨v, t⟩)]
  push_cast
  rfl

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem Joint.site_base_datum_integral_off_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), ∀ j La La' z, IntOff (t.O u μ).S (J.xi0 std S.Xi j La La' z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S j La La' z
  unfold Joint.xi0
  split_ifs with h
  · exact S.law.int _ _ _ _ _ _ _
  · exact Formalism.L2.PairingIndexBounds.F.intOff_zero _

end GlobalTheory.TwV
end

