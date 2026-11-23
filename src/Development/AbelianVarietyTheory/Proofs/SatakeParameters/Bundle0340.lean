module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0335

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePointDetNormOneOrderEqNegLength
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

theorem det_reGL' {R : Type} [CommRing R] {a b : ℕ} (e : Fin a ≃ Fin b) (x : GL (Fin a) R) :
    Matrix.GeneralLinearGroup.det (reGL e x) = Matrix.GeneralLinearGroup.det x := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_reindex_self e _

theorem det_bc' {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (φ : A →+* B) (x : GL m A) :
    ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc φ x) : Bˣ) : B) = φ ((Matrix.GeneralLinearGroup.det x : Aˣ) : A) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

theorem det_castGL' {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    ((Matrix.GeneralLinearGroup.det (castGL h R g) : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) := by
  subst h
  simp [castGL, Matrix.GeneralLinearGroup.val_det_apply]

theorem phiA_det_eps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n k p : ℕ} {G : GAtP p}
    (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (S : Set (GL (Fin n) (AfE F E)))
    (hex : ∃ x, A.IsPt i g x ∧ x ∈ S) (e : Fin n ≃ Fin k) (v : Fin G.P.nV) :
    phiA A v ((Matrix.GeneralLinearGroup.det (reGL e (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S)) : (AfE F E)ˣ) : AfE F E) =
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)).det := by
  rw [det_reGL']
  have hx := (Classical.epsilon_spec hex).1
  have h := congrArg (fun y => ((Matrix.GeneralLinearGroup.det y : _ˣ) : (A.pl v).1.adicCompletion F)) (hx.2 v)
  have e : ∀ (a b : ((A.pl v).1.adicCompletion F)ˣ), a * b * a⁻¹ = b := fun a b => by
    rw [mul_comm a b, mul_inv_cancel_right]
  simp only [map_mul, map_inv] at h
  rw [det_bc', det_bc'] at h
  have h2 : A.ph v (prV (E := E) (A.pl v).1 ((Matrix.GeneralLinearGroup.det (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S) : _ˣ) : _)) =
      A.eQ v ((Matrix.GeneralLinearGroup.det (g v) : _ˣ) : _) := by
    rw [h, e, det_bc', det_castGL']
    rfl
  show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 _)) = _
  rw [h2, RingEquiv.symm_apply_apply, Matrix.GeneralLinearGroup.val_det_apply]

end GlobalTheory.TwV.Xc.PtOrd

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

open Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem latAt_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) ((basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v : GL _ _) : Matrix _ _ _) := by
  have hx : ∃ g : GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v), (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _) := by
    cases j with
    | zero =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
    | succ i =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
  exact Classical.epsilon_spec hx

theorem len_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    len (sysAt Ch std vp unif eO eO_spec dG dG_spec om) v j Lt = -ordP ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w)
      ((Matrix.GeneralLinearGroup.det (basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v) : _ˣ) : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) := by
  have hS := (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.setting v
  have := hS.frac_alt
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  cases j with
  | zero =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v 0 Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om 0 Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om 0 Lt v).isUnit)]
  | succ i =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt v).isUnit)]

theorem cpAt_y_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).y (i + 1) La =
      reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
          (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).y = _
  simp only [chAt, dif_pos hi]

end GlobalTheory.TwV.Xc.PtOrd
end
namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem latticeTuplePoint_det_normOne_order_eq_neg_length : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → (J.fd std).dt j La ∈ U1 (sigD D) ∧ ∀ v : (sysS H X std).Pl, ordA (A0 J) v ((J.fd std).dt j La) = -len (sysS H X std) v j La.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj La hLa
  obtain ⟨⟨hr, hpt⟩, -, -, hdt⟩ := hD j hj La hLa
  refine ⟨hdt ▸ Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) _ (J.pt std j hj La).2, fun v => ?_⟩
  rw [PtOrd.len_bases (chainAt H hT) std _ _ _ _ _ _ _ j La.2 hLa v, neg_neg, hdt]
  unfold ordA
  rw [hpt]
  erw [PtOrd.det_reGL']
  cases j with
  | zero =>
    exact congrArg _ (PtOrd.phiA_det_eps (A0 J) La.1 _ _ (let hG := J.one.good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)
  | succ i =>
    have hP := (_root_.GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero S hD hS i hj ((I.at' i hj).st.eC.symm La.1).1 v).2
    rw [PtOrd.cpAt_y_succ (chainAt H hT) std _ _ _ _ _ _ _ I _ _ _ _ i hj La, ← hP]
    exact congrArg _ (PtOrd.phiA_det_eps _ _ _ _ (let hG := (H.core i hj ((I.at' i hj).st.eC.symm La.1).1).good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)

end GlobalTheory.TwV.Xc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInChar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem reGL_finCongr_twice {R : Type} [CommRing R] {a b : ℕ} (h1 : a = b) (h2 : b = a) (x : GL (Fin a) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h2) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h1) x) = x := by
  subst h1
  apply Units.ext
  ext r s
  rfl


set_option maxHeartbeats 1000000 in
theorem ptS_isPt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj La hLa
  obtain ⟨⟨hr, hx⟩, -⟩ := hD (j + 1) hj La hLa
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  refine ⟨Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2, fun v => ?_, ?_⟩
  · obtain ⟨g, hg'⟩ := (Formalism.L2.G.Cmp.isLattice_iff _ (La.2 v)).1 (hLa v)
    exact Classical.epsilon_spec (p := fun g0 : GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v) =>
      La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g0 : Matrix _ _ _)) ⟨g, by rw [hg', Formalism.L2.G.Cmp.colSpan_eq]⟩
  · have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      show (dite (j + 1 ≤ D.R.m) _ _ : PtCh _ _).y = _
      rw [dite_eq_left hj]
    rw [hx, hy, reGL_finCongr_twice]
    exact (Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩).1

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.DelB.UnitB

theorem det_map_transpose {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    ((M.map σ)ᵀ).det = σ M.det := by
  rw [Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_unitary_prod {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (J c B : Matrix (Fin N) (Fin N) E)
    (hc : (c.map σ)ᵀ * c = J) (hB : (B.map σ)ᵀ * J * B = 1) :
    σ (c.det * B.det) * (c.det * B.det) = 1 := by
  have h : ((c * B).map σ)ᵀ * (c * B) = 1 := by
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (B.map σ)ᵀ * (c.map σ)ᵀ * (c * B) = (B.map σ)ᵀ * ((c.map σ)ᵀ * c) * B := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hB]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, det_map_transpose, Matrix.det_one, Matrix.det_mul] at hd
  exact hd

end GlobalTheory.TwV.DelB.UnitB


open GlobalTheory.TwV.DelB.UnitB in
theorem GlobalTheory.TwV.DelB.detCrdB_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj β B hB hL τ
  refine _root_.GlobalTheory.TwV.UnitPos.norm_embT_unit S hPos ι hι _ ?_ (fun v => _root_.GlobalTheory.TwV.LatDet.crd_mul_det_unit S j hj β B v (hL v)) τ
  have hc := J.pins.crd_orth j hj
  have h1 := det_unitary_prod (sigD D : D.host.E →+* D.host.E) (gramN D j hj) (J.A.crd j hj).1 B.1 hc hB
  have hconj : ∀ y : D.host.E, D.host.conj y = (sigD D : D.host.E →+* D.host.E) y := fun y => (bridge_star_holds D.R D.host y).symm
  rw [hconj, mul_comm]
  exact h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTuple
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem stdG_one_apply {D : D7} {N : ℕ} (J : Matrix (Fin N) (Fin N) D.host.E) (v : Fin N → D.host.E) :
    stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J 1 v = v := by
  have h : ∀ w : Fin N → D.host.E, toLE (1 : GL (Fin N) D.host.E) w = w := by
    intro w
    simp [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]
  show (stdCo _ J) (toLE 1 ((stdCo _ J).symm v)) = v
  rw [h, LinearEquiv.apply_symm_apply]

theorem inFr_stdG_homRe {D : D7} {a b N N' : ℕ} (hr : a = N) (hr' : b = N') (J : Matrix (Fin N) (Fin N) D.host.E)
    (J' : Matrix (Fin N') (Fin N') D.host.E) (g : GL (Fin N) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    Formalism.L2.Col.inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1) (homRe hr hr' x) =
      homRe hr hr' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) J g)) := by
  subst hr hr'
  apply LinearMap.ext
  intro v
  have h1 : ∀ w, (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1).symm w = w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, stdG_one_apply]
  simp only [Formalism.L2.Col.inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, homRe, eMat]
  congr 2
  ext i
  simp [Matrix.toLin'_apply, LinearMap.toMatrix'_mulVec]

end GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.xiM_smul_moveBy : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLa hM La'
  have hj' : j + 1 ≤ D.R.m := hj
  have hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := (GlobalTheory.TwV.DelB.sysS_ranks S).2.2.1 (j + 1)
  obtain ⟨hg, hpt, -, r, hr0, -⟩ := hM
  have hκU := ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U_eq κ.1).1 κ.2).1

  have hdet : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) := det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, hκU⟩
  refine ⟨?_, fun x => ?_⟩
  · have hmu := S.law.mu_alg j hj _ hdet
    have hchi : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
      rw [← hr0]
      exact (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) r).algHom (D.what₂.embLL.toRatAlgHom))
    exact mul_mem hmu (inv_mem hchi)
  · have e1 := _root_.GlobalTheory.TwV.Xc.xiM_eq_adelic S hD hS j hj' hr hr' (c, ((sysS H X std).Lv.lev j c).smul γ La) La' x
    have e2 := _root_.GlobalTheory.TwV.Xc.xiM_eq_adelic S hD hS j hj' hr hr' (c, La) La'
      (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))
    have hch := _root_.GlobalTheory.TwV.Xc.chart_eq_of_comp S hD hS j hj.le c (((sysS H X std).Lv.lev j c).smul γ La) La
      (GlobalTheory.GO.CmpMem.isLatTup_smul _ γ hLa) hLa
    rw [e1, e2, hch]
    have hx0 : (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 * κ.1⁻¹ ∈
        UPts (sigD D) (gramN D j hj.le) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      mul_mem (J.pt std j hj.le _).2 (inv_mem hκU)
    have hlev := S.law.lev j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La')
      (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)) (J.pt std (j + 1) hj' La') κ 1
      (by show _ = _ * _ * _; group) (by simp) (homRe hr hr' x)
    have hrat := S.law.rat j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') (J.pt std j hj.le (c, La))
      (J.pt std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La') g hg 1 (one_mem _)
      (by show _ * _ = _; rw [hpt]; group) (by simp) (homRe hr hr' x)
    rw [inFr_stdG_homRe] at hrat
    rw [hrat] at hlev
    simp only [OneMemClass.coe_one, map_one, (S.law.mu_mul j hj).1, one_mul, Units.val_one, mul_one] at hlev
    have hc : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    linear_combination hlev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem leftSide_odd_grp {M : Type} [CommGroup M] (u e d d' e' : M) (n : ℕ) (c s w : ℤ) (hu : u = e' * d'⁻¹) (he : e * e = 1) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  subst hu
  apply Additive.ofMul.injective
  have he' : Additive.ofMul e + Additive.ofMul e = 0 := by rw [← ofMul_mul, he]; rfl
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv]
  linear_combination (norm := module) (c - w) • he'

theorem leftSide_odd (u e d d' e' : ℂ) (n : ℕ) (c s w : ℤ) (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e * e = 1) (he' : e' * e' = 1)
    (hu : u = e' * d'⁻¹) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  have he0 : e ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he0' : e' ≠ 0 := left_ne_zero_of_mul_eq_one he'
  have h := leftSide_odd_grp (Units.mk0 e' he0' * (Units.mk0 d' hd')⁻¹) (Units.mk0 e he0) (Units.mk0 d hd) (Units.mk0 d' hd')
    (Units.mk0 e' he0') n c s w rfl (Units.ext (by simpa using he))
  have h2 := congrArg Units.val h
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at h2
  subst hu
  exact h2

theorem leftSide_sgRev_sq (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem leftSide_det_zT_odd {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos h]
  have := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) ((f τ)⁻¹).transpose
  rw [show (⇑(Fin.revPerm : Equiv.Perm (Fin n))) = Fin.rev from rfl] at this
  rw [this, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem leftSide_zT_even {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : ¬ IsOddPos (pos.symm τ).2) :
    zT X D pos f τ = f τ := by
  unfold zT; rw [if_neg h]

end GlobalTheory.TwV.DelA
end

namespace GlobalTheory.TwV.DelA

theorem leftSide_at_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG d f' hf' hdf
  have hodd := _root_.GlobalTheory.TwV.DelA.oddDeg_of_realises X D pos Kc ι j hN ν hν Q hQ Gc G hR hG
  have hsub := _root_.GlobalTheory.TwV.DelA.evD_subD X D pos Kc ι j hN Gc G hG hodd d f' hf' hdf
  have hnum := _root_.GlobalTheory.TwV.DelA.evD_numD_denD X D pos Kc ι j hN d f' hf' hdf
  have hex := _root_.GlobalTheory.TwV.DelA.eT_last_pair X D pos j
  have hnn := (_root_.GlobalTheory.TwV.DelA.size_first_last_rows X D pos j hN ν hν).2.2.2.2
  have hR' := hR ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩
  have hR2 := (ev1_eq_prod_det_pow_mul_valZ X D pos j (rkS X D hN) Gc ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩).symm.trans hR'
  clear hR'
  simp only at hR2
  rw [map_mul, hsub, hnum]
  have gen : ∀ (x y z : ℂ) (E : Kc), ι x * (E * ι y) * ι z = E * ι (x * y * z) := by
    intro x y z E; simp only [map_mul]; ring
  rw [gen]
  congr 2
  have hW : (∏ τ, (dfr X D hN d f' τ).det ^ (-(wT X D pos j τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdf τ)
  have key : ∀ A V B P' S W' q Pj Wf : ℂ, Wf ≠ 0 → A * B * P' * Wf = S * W' * Pj → Pj * V = Wf * q →
      A * V * B * P' = S * W' * q := by
    intro A V B P' S W' q Pj Wf hWf hK hP
    apply mul_right_cancel₀ hWf
    linear_combination V * hK + S * W' * hP
  refine key _ _ _ _ _ _ _ _ _ hW ?_ hR2
  unfold sgO
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨h1, h2⟩ := hex τ
  by_cases ho : IsOddPos (pos.symm τ).2
  · simp only [if_pos ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_det_zT_odd X D pos f' τ ho, leftSide_det_zT_odd X D pos (dfr X D hN d f') τ ho]
    exact leftSide_odd _ _ _ _ _ _ _ _ _ (hdf τ) (hf' τ) (leftSide_sgRev_sq _) (leftSide_sgRev_sq _) rfl
  · simp only [if_neg ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_zT_even X D pos f' τ ho, leftSide_zT_even X D pos (dfr X D hN d f') τ ho, ← zpow_natCast,
      Int.toNat_of_nonneg (hnn τ), zpow_sub₀ (hdf τ)]
    simp only [zpow_neg]
    ring

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.posTie_at : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; PosTie (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) ∧ ∀ r : D.what₂.LL, ι (D.what₂.embLL r) = algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w] (ex.cmp.embW u w hg r)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  refine ⟨fun v s x => ?_, fun r => ?_⟩
  · have h := hS v s x
    have hz : (embT D (hT.gat_pos u w hg ⟨v, s⟩)) x ∈ TaylorLogMetric.Qbar := by
      rw [← tEL_emb]
      exact Formalism.L2.G.embLL_mem_alg D _
    have he : TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x = embT D (hT.gat_pos u w hg ⟨v, s⟩) x := rfl
    have hL : TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) = ι ((embT D (hT.gat_pos u w hg ⟨v, s⟩)) x) := by
      unfold TaylorLogMetric.lamC
      rw [dite_eq_left (he ▸ hz)]
      rw [hι ⟨_, hz⟩]
      rfl
    rw [← hL, h, Formalism.L2.Herm.star_conj]
    rfl
  · have hz := Formalism.L2.G.embLL_mem_alg D r
    rw [hι ⟨_, hz⟩, ← S.hK r hz]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_badPrimes_coprime_residueChar : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  first | exact @GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | exact GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | (intros; apply GlobalTheory.TwV.Xc.SBad.bad_prime_to_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesCoefficientsAtKernelSiteOfClassSeries
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieSerH_series_of_classes : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hN : RankTie (sysS H X std) D j), TieSerH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι (fun j La La' => resV (kapOf (sysS H X std) (hT.gat_pos u w hg) j) (d.gS S ι j La La')) (d.sH S ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d ι j hN La _ c' L' _ α _
  exact _root_.GlobalTheory.TwV.DelB.coeff_resV_thCl t u μ _ (sysS H X std) (hT.gat_pos u w hg) (clsAt X H) ι j hN La (c', L') (d.sH S ι j La (c', L')) α

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.systemWeights_eq_shifted_character_exponents : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  first | exact @GlobalTheory.TwV.Xc.fillAt_of_comp | exact GlobalTheory.TwV.Xc.fillAt_of_comp | (intros; apply GlobalTheory.TwV.Xc.fillAt_of_comp <;> assumption)
end

