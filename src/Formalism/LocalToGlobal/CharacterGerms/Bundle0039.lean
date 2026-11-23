module

public import Formalism.LocalToGlobal.CharacterGerms.IteratePderivTripleMultiplication
public import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0038
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0034

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FunEqCoreHolds
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem aOf_eq (Y : FBChart C V O dd) (u : Fin dd → C) :
    Y.aOf u = ∑ i, MvPowerSeries.C (u i ^ V.l * ((V.l.factorial : C))⁻¹) *
      ev (rz 1) ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1) := by
  ext ν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_C_mul]
  show (∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l +
    ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1) = _
  have hup : (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2)) = up 1 := by
    funext q; obtain ⟨q1, q2⟩ := q; fin_cases q1; rfl
  rw [hup]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_rz_iter]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem link (Y : FBChart C V O dd) (u : Fin dd → C) (W : Pt C 2 dd) (hW : ∀ j, constantCoeff (W j) = 0)
    (Wup : Pt C 3 dd) (hW0 : ∀ j, constantCoeff (Wup j) = 0)
    (hd : ∀ i j, pderiv (R := C) ((0 : Fin 3), i) (Wup j) = 0)
    (hr : ∀ j, ev (rz 2) (Wup j) = W j) (γ : Fin 2 × Fin dd →₀ ℕ) :
    coeff γ (ev (n := 2) ![W] (Y.aOf u)) = Phi V u (UU Y Wup) γ := by
  have hz1 := z0_1 W hW
  have hz2 := constant_zero_two_points (p3 0) (z0p3 0) hW0
  rw [aOf_eq, ev_sum hz1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul hz1, Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_C, map_sum, coeff_C_mul]
  unfold Phi
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ev ![W] (ev (rz 1) ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1)) =
      ev (n := 2) ![0, W] ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1) := by
    rw [ev_ev (constant_zero_restrict_points 1) hz1]
    congr 1
    funext k j
    fin_cases k
    · exact ev_zero hz1
    · exact ev_X hz1 0 j
  have e2 : ev (rz 2) ((pderiv (R := C) ((0 : Fin 3), i))^[V.l] (UU Y Wup)) =
      ev (n := 2) ![0, W] ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1) := by
    unfold UU
    rw [d_ev_keep_iter hW0 i (hd i), ev_ev hz2 (constant_zero_restrict_points 2)]
    congr 1
    funext k j
    fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · exact hr j
  have h3 := coeff_rz_iter 2 i V.l (UU Y Wup) γ
  rw [e2] at h3
  rw [e1, h3]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  rfl

theorem coeff_U_eq (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (Phi V u (UU Y (SS Y.B.G)) γ - Phi V u (UU Y (p3 1)) γ - Phi V u (UU Y (p3 2)) γ -
      Phi V u (Y.B.ph2 ^ V.l) γ + Phi V u (QQ Y) γ) := by
  have hU : ∀ {w : Pt C 3 dd}, (∀ j, constantCoeff (w j) = 0) → (∀ j, IntS V (w j)) →
      (∀ i j, pderiv (R := C) ((0 : Fin 3), i) (w j) = 0) →
      IntS V (UU Y w) ∧ FrobD V (UU Y w) ∧ ev (rz 2) (UU Y w) = 1 :=
    fun hw0 hw hd => ⟨UU_int Y hw0 hw, UU_frob Y hw0 hw hd, UU_one Y hw0⟩
  obtain ⟨iS, fS, oS⟩ := hU (triple_sum_constantCoeff Y.B.G) (SS_int Y.B.G Y.intF) (SS_d Y.B.G)
  obtain ⟨i1, f1, o1⟩ := hU (z0p3 1) (fun j => triple_coordinate_integral 1 j) (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j)
  obtain ⟨i2, f2, o2⟩ := hU (z0p3 2) (fun j => triple_coordinate_integral 2 j) (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j)
  have iQ := QQ_int Y
  have iP : IntS V (Y.B.ph2 ^ V.l) := intS_pow Y.intPh2 _
  have i12 : IntS V (UU Y (p3 1) * UU Y (p3 2)) := intS_mul i1 i2
  have f12 : FrobD V (UU Y (p3 1) * UU Y (p3 2)) := frobD_mul i1 i2 f1 f2
  have o12 : ev (rz 2) (UU Y (p3 1) * UU Y (p3 2)) = 1 := by rw [Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul (constant_zero_restrict_points 2), o1, o2, one_mul]
  unfold Phi
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine GmExArith.mm_sum fun i _ => ?_
  have cS := coeff_mul_cong iS iQ (frobX_of iS fS) (frobX_of iQ (QQ_frob Y)) oS (QQ_one Y) i γ
  have cR1 := coeff_mul_cong i12 iP (frobX_of i12 f12) (frobX_of iP (second_pairing_pow_frobenius Y)) o12 (second_pairing_pow_restrict_one Y) i γ
  have cR2 := coeff_mul_cong i1 i2 (frobX_of i1 f1) (frobX_of i2 f2) o1 o2 i γ
  rw [ident] at cS
  have e : u i ^ V.l * coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 1)) -
      u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 2)) - u i ^ V.l * coeff (ix i V.l γ) (Y.B.ph2 ^ V.l) +
      u i ^ V.l * coeff (ix i V.l γ) (QQ Y) =
      u i ^ V.l * (-(coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
        coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - coeff (ix i V.l γ) (QQ Y)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
          coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (Y.B.ph2 ^ V.l)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (UU Y (p3 1)) -
          coeff (ix i V.l γ) (UU Y (p3 2)))) := by ring
  rw [e]
  exact GmExArith.mm_int_mul ((hu i).pow _) (GmExArith.mm_add (GmExArith.mm_add (GmExArith.mm_neg cS) cR1) cR2)

end Formalism.L2.FormalSeriesBounds.FunEq

namespace Formalism.L2.FormalSeriesBounds

open FunEq MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem funEqCore_holds : FunEqCoreSt := by
  intro C _ _ V O _ _ dd Y u hu hV1 μ
  have hS := link Y u (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1))
    (fun j => PartialDerivEval.const_ev (PartialDerivEval.z0_pp 0 1) (Y.B.G.const j)) (SS Y.B.G) (triple_sum_constantCoeff _) (SS_d _)
    (fun j => by
      show ev (rz 2) (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = _
      rw [PartialDerivEval.ev_ev (PartialDerivEval.z0_pp 1 2) (constant_zero_restrict_points 2)]
      congr 1
      funext k m
      fin_cases k
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 m
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 m) μ
  have h1 := link Y u (pt C (n := 2) dd 0) (fun j => PartialDerivEval.z0_pt 0 j) (p3 1) (z0p3 1)
    (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 j) μ
  have h2 := link Y u (pt C (n := 2) dd 1) (fun j => PartialDerivEval.z0_pt 1 j) (p3 2) (z0p3 2)
    (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 j) μ
  unfold cobd
  rw [map_sub, map_sub, map_sub, hS, h1, h2]
  have hA := coeff_U_eq Y u hu μ
  have hB := phiP Y u hu μ
  have hC := phiQ Y u hu hV1 μ
  have e : Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
      coeff μ (frobTw V.l (Y.chartLinearTerm u)) =
      (Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
        Phi V u (Y.B.ph2 ^ V.l) μ + Phi V u (QQ Y) μ) +
      (Phi V u (Y.B.ph2 ^ V.l) μ - coeff μ (frobTw V.l (Y.chartLinearTerm u))) - Phi V u (QQ Y) μ := by ring
  rw [e]
  exact GmExArith.mm_sub (GmExArith.mm_add hA hB) hC

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTDone
section
namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def GeoJ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (OE : Type) [CommRing OE] [StarRing OE] (aG : OE → (G ⟶ G)) (dd : ℕ) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∃ (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
    (U : Out.UnifPre (maximalIdeal T) D A G) (F : FGLaw T dd)
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin dd) m) ⟶ G) (_ : Module OE D.toPre.X) (io : Out.RingAct G OE)
    (oD : D.OAct OE) (oA : A.OAct OE) (act : Germ.OAct OE F),
    F.F = FT ∧ act.act = actT ∧ (∀ a, io.act a = aG a) ∧ IsChartJ G F x ∧ U.OLinear OE oD oA io ∧
      ChartActs G x io act

def PlaceIn (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ (w : PlaceU l OE) (_ : NeZero w.n) (t : Fin w.n ≃ Emb (O := R) w.e) (jj : ZMod d ≃ Fin w.n),
    (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : Emb (O := R) w.e) : OE →+* R) = em a) ∧
    ∃ b : Module.Basis (Fin w.n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := R) w.e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def UpFLaw (p : ℕ) [Fact p.Prime] (T : Type) [CommRing T] (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ)
    (FT : Fin dd → PS T 2 dd) (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
      [Algebra ℤ_[p] O] (iota : T →+* O), IsLocalHom iota →
    ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
    (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
    (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
        (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ maximalIdeal O) →
    ∀ (r : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (r τ) → Fin dd → O),
      (∀ τ, IsEigBasis (fun a i => MvPowerSeries.map iota (actT a i)) τ (W τ)) →
    ∀ j : Fin w.n, ∃ xs : NNReal,
      HasAF v (fun i => MvPowerSeries.map iota (FT i)) (W ((t j : Emb (O := O) w.e) : OE →+* O)) xs ∧
      v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
        (r (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
          ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs

theorem upFLaw_of_geoJ {p : ℕ} [Fact p.Prime] (hUp : UpFSt p) (hp2 : p ≠ 2)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit (p : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    {OE : Type} [CommRing OE] [StarRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (aG : OE → (G ⟶ G)) {dd : ℕ} (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (hdisc : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UpFLaw p T OE dd FT actT := by
  obtain ⟨D, A, U, F, x, iM, io, oD, oA, act, rfl, rfl, -, hx, hO, hA⟩ := hG
  intro C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hbas hfrob r W hW j
  exact hUp T hlT G D A U dd F x hx hp2 OE io oD oA hO hdisc act hA C v O hv iota hloc w t hbas hfrob r W hW j

section Inst

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem ofNat_succ (n : ℕ) [NeZero n] (k : ℕ) : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem jj_add {n : ℕ} [NeZero n] (jj : ZMod d ≃ Fin n) (h : ∀ a, jj (a + 1) = jj a + 1) (a : ZMod d) :
    ∀ k : ℕ, jj (a + (k : ZMod d)) = jj a + Fin.ofNat n k
  | 0 => by
    have : Fin.ofNat n 0 = 0 := by apply Fin.ext; simp [Fin.ofNat]
    simp [this]
  | k + 1 => by
    have e : a + ((k + 1 : ℕ) : ZMod d) = (a + (k : ZMod d)) + 1 := by push_cast; ring
    rw [e, h, jj_add jj h a k, ofNat_succ, add_assoc]

end Inst

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieValL
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

def RawChart.TCoordSt {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
    {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∀ (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ (g : Fin 2) (c : I g), ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t g c)

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]

theorem cc_toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    MvPowerSeries.constantCoeff (toAllS o F) = MvPowerSeries.constantCoeff F := by
  unfold toAllS
  exact VP.cc_subst_eq (fun _ => MvPowerSeries.constantCoeff_X _) F

theorem toAllS_subst {κ : Type} [Finite κ] (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    (hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0) (T : MvPowerSeries κ C) :
    toAllS o (MvPowerSeries.subst E T) = MvPowerSeries.subst (fun x => toAllS o (E x)) T := by
  unfold toAllS
  exact VP.subst_subst hE (fun _ => MvPowerSeries.constantCoeff_X _) T

theorem germLift_gen {σ : Type} [Finite σ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) (t : ∀ g, I o g → MvPowerSeries (I o g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (hT : ∀ w : WV (I o), ∃ T : MvPowerSeries σ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst A T = toAllS o (upG w.1 (t w.1 w.2))) :
    ∀ F ∈ IntGerm V t, ∃ G : MvPowerSeries σ C, IntS V G ∧ MvPowerSeries.subst A G = toAllS o F := by
  intro F hF
  obtain ⟨γ, hγ, rfl⟩ := hF
  choose T hTi hT0 hTA using hT
  have hE : ∀ w : WV (I o), MvPowerSeries.constantCoeff (upG w.1 (t w.1 w.2)) = 0 := fun w => by
    unfold upG
    exact VP.cc_subst (fun _ => MvPowerSeries.constantCoeff_X _) (ht0 _ _)
  refine ⟨MvPowerSeries.subst T γ, IntS.subst hT0 hTi hγ, ?_⟩
  rw [VP.subst_subst hT0 hA, toAllS_subst o hE]
  congr 1
  funext w
  exact hTA w

theorem tLift_gen {σ κ : Type} [Finite σ] [Finite κ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    {π : κ → MvPowerSeries σ C} (hπi : ∀ x, IntS V (π x)) (hπ0 : ∀ x, MvPowerSeries.constantCoeff (π x) = 0)
    (hπ : ∀ x, MvPowerSeries.subst A (π x) = toAllS o (E x))
    {T : MvPowerSeries κ C} (hTi : IntS V T) (hT0 : MvPowerSeries.constantCoeff T = 0) :
    ∃ T' : MvPowerSeries σ C, IntS V T' ∧ MvPowerSeries.constantCoeff T' = 0 ∧
      MvPowerSeries.subst A T' = toAllS o (MvPowerSeries.subst E T) := by
  have hπA : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.subst A (π x)) = 0 := fun x => VP.cc_subst hA (hπ0 x)
  have hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0 := fun x => by
    rw [← cc_toAllS o (E x), ← hπ x]
    exact hπA x
  refine ⟨MvPowerSeries.subst π T, IntS.subst hπ0 hπi hTi, VP.cc_subst hπ0 hT0, ?_⟩
  rw [VP.subst_subst hπ0 hA, toAllS_subst o hE]
  congr 1
  funext x
  exact hπ x

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb]

section Pairs

variable {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Pairs

section Self

variable {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

def ProjSelfSt (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin 2 × Fin dd → PS C 2 dd, (∀ x, IntS V (π x)) ∧
    (∀ x, MvPowerSeries.constantCoeff (π x) = 0) ∧
    ∀ x, pull2 Y p (π x) = toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g x)

theorem germLiftSelf_of (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (hP : ProjSelfSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSelfSt Y p H := by
  intro hsep o S t hS F hF
  unfold pull2
  have hA : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 := VP.cc_linPt Y (uS Y p)
  refine VP.germLift_gen (I := IS I0) hA o t (fun g c => (hS g).1 c) (fun w => ?_) F hF
  obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
  obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
  obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen (I := IS I0) hA o hπi hπ0 hπ hTi hT0
  exact ⟨T', h1, h2, by rw [h3, hTe]⟩

end Self

end Formalism.L2.FormalSeriesBounds
end
end

