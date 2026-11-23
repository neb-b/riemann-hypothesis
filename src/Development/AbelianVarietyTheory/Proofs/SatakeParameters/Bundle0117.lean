module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AlgTAll
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianLocalisationAdelicPointLatticeEq
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll
section
namespace GlobalTheory.ThLoc

theorem algTAll : Formalism.L2.KerInert.AlgTAll := GlobalTheory.ThLoc.Alg.algTAll

end GlobalTheory.ThLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem eig_descends : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  intro D M B j w μ h1 h2 hμ φ hφ κ y hy hgen
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  have hd : (⇑(bC.repr y)) ≠ 0 := by
    intro h
    apply hy
    have h' : bC.repr y = 0 := Finsupp.coe_eq_zero.1 h
    exact bC.repr.injective (h'.trans (map_zero _).symm)
  have hC : ∀ g : G, Matrix.mulVec ((Mg g).map φ) (⇑(bC.repr y)) = 0 := by
    rintro ⟨⟨v, k⟩, hvk⟩
    obtain ⟨s, ϖ, hc, hu, hadd, heig⟩ := hgen v k hvk
    set Mw := M (D.what₂.muTw w) j h1 h2 with hMw
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
      have := hadd 1 0 0
      rw [one_smul, add_zero, one_smul] at this
      simpa using this
    let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
      { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
        map_add' := fun y y' => by
          have := hadd 1 (Mw.real y) (Mw.real y')
          rw [one_smul, one_smul] at this
          simp only [map_add (f := _)]
          exact this
        map_smul' := fun c y => by
          have := hadd c (Mw.real y) 0
          rw [add_zero, htN0, add_zero] at this
          simp only [map_smul, RingHom.id_apply]
          exact this }
    have hagree : ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hty : tC y = φ (κ v k) • y := by
      apply Mw.real_inj
      rw [← hagree, heig, map_smul]
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    rw [hMg, Matrix.sub_mulVec, ← hmat, LinearMap.toMatrix_mulVec_repr, hty, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_smul, Finsupp.coe_smul, sub_self]
  obtain ⟨c, hc0, hcM⟩ := GlobalTheory.PtLocalEig.descent φ Mg (⇑(bC.repr y)) hd hC
  refine ⟨bV.equivFun.symm c, ?_, fun v k hvk => ?_⟩
  · intro h
    apply hc0
    have := congrArg bV.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · apply bV.equivFun.injective
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hM := hcM ⟨(v, k), hvk⟩
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hM
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    rw [map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply, hM]

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwEig

theorem map_mul (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f g : Module.End ℂ E) :
    (Tw.map s (f * g) : Module.End ℂ (Tw s E)) = Tw.map s f * Tw.map s g := LinearMap.ext fun _ => rfl

theorem pow_sub_apply (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Module.End ℂ E)
    (μ : ℂ) (k : ℕ) (y : Tw s E) :
    Tw.out ((((Tw.map s f : Module.End ℂ (Tw s E)) - μ • 1) ^ k) y) = ((f - cj s μ • 1) ^ k) (Tw.out y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    rfl

theorem mem_maxGen (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Module.End ℂ E)
    (μ : ℂ) (y : Tw s E) :
    y ∈ Module.End.maxGenEigenspace (Tw.map s f : Module.End ℂ (Tw s E)) μ ↔ Tw.out y ∈ f.maxGenEigenspace (cj s μ) := by
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  refine exists_congr fun k => ?_
  rw [← pow_sub_apply]
  rfl

theorem sub_eq_map (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Tw.sub s V = V.map (Tw.mkL s E) := by
  ext y
  constructor
  · intro hy; exact ⟨Tw.out y, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact hx

theorem sub_iSup' (s : Bool) {E : Type} {C : Sort*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (Ec : C → Submodule ℂ E) :
    Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  simp only [sub_eq_map, Submodule.map_iSup]

theorem eigAt_tw (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E)
    (x : I → ℂ) :
    Formalism.L2.Col.eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) x =
      Tw.sub s (Formalism.L2.Col.eigAt h fun i => cj s (x i)) := by
  ext y
  simp only [Formalism.L2.Col.eigAt, Submodule.mem_iInf, mem_maxGen]
  show _ ↔ Tw.out y ∈ ⨅ i, (h i).maxGenEigenspace (cj s (x i))
  rw [Submodule.mem_iInf]

end GlobalTheory.TwEig

open GlobalTheory.TwEig in
theorem GlobalTheory.TwEig.pairComm_eigSum_sub_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  intro s E I _ _ h
  refine ⟨fun hc i j => ?_, fun Q => ?_, fun Ec => sub_iSup' s Ec⟩
  · show Tw.map s (h i) * Tw.map s (h j) = Tw.map s (h j) * Tw.map s (h i)
    rw [← map_mul, ← map_mul, (hc i j).eq]
  · simp only [Formalism.L2.Col.eigSum, eigAt_tw]
    rw [sub_iSup']
    let e : (I → ℂ) ≃ (I → ℂ) := ⟨fun x i => cj s (x i), fun x i => cj s (x i),
      fun x => funext fun i => cj_cj s (x i), fun x => funext fun i => cj_cj s (x i)⟩
    rw [← e.iSup_comp]
    refine iSup_congr fun x => ?_
    simp [e, cj_cj]
    exact (sub_iSup' (E := E) s (fun _ : (Q fun i => cj s (x i)) => Formalism.L2.Col.eigAt h x)).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.DualHecke

theorem comp_C_mul_X_dualPoly {K : Type} [Field K] (t u : K) (R : K[X]) :
    (Formalism.L2.DIV.dualPoly t R).comp (C u * X) = Formalism.L2.DIV.dualPoly (t * u) R := by
  unfold Formalism.L2.DIV.dualPoly
  rw [mul_comp, C_comp, comp_assoc, mul_comp, C_comp, X_comp, C_mul]
  congr 2
  ring

theorem dualPoly_heckePolyOf_comp : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  intro K _ n q a b s s' hq hs hn h0 h
  have han : a n ≠ 0 := by
    intro h1
    have e := h n le_rfl
    rw [Nat.sub_self, h0, h1, mul_zero] at e
    exact zero_ne_one e
  have hbn : b n * a n = 1 := by
    have e := h n le_rfl
    rwa [Nat.sub_self, h0] at e
  have hb0 : b 0 = 1 := by
    have e := h 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at e
    exact mul_right_cancel₀ han (by rw [e, one_mul])
  have hdual : ∀ k ≤ n, b n * a k = b (n - k) := by
    intro k hk
    have e := h (n - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk] at e
    rw [← e]
    linear_combination b (n - k) * hbn
  have H := GlobalTheory.PartsCompare.heckePolyOf_dual (n := n) (q := q) hq (a := b) (b := a) hb0 hdual
  have hc := GlobalTheory.PartsCompare.dualPoly_comp (inv_ne_zero hs) (s * s' * (q : K) ^ (n - 1))
    (Formalism.L2.Col.heckePolyOf n q b)
  rw [inv_inv] at hc
  rw [hc, H, comp_C_mul_X_dualPoly]
  congr 1
  field_simp

end GlobalTheory.Hk3.DualHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
section
noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def DvdPow (ϖ : L) (k : ℕ) (a : L) : Prop := ∃ b ∈ Formalism.UG.intL L, a = ϖ ^ k * b

def IndepMod (ϖ : L) {ι : Type} [Fintype ι] {m : ℕ} (z : ι → Fin m → L) : Prop :=
  ∀ d : ι → L, (∀ i, d i ∈ Formalism.UG.intL L) → (∀ r, DvdPow ϖ 1 (∑ i, d i * z i r)) → ∀ i, DvdPow ϖ 1 (d i)

theorem dvdPow_zero_iff {ϖ a : L} : DvdPow ϖ 0 a ↔ a ∈ Formalism.UG.intL L := by
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨a, h, by simp⟩

theorem dvdPow_add {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a + b) := by
  obtain ⟨c, hc, rfl⟩ := ha; obtain ⟨d, hd, rfl⟩ := hb
  exact ⟨c + d, (Formalism.UG.intL L).add_mem hc hd, by ring⟩

theorem dvdPow_neg {ϖ a : L} {k : ℕ} (ha : DvdPow ϖ k a) : DvdPow ϖ k (-a) := by
  obtain ⟨c, hc, rfl⟩ := ha
  exact ⟨-c, (Formalism.UG.intL L).neg_mem hc, by ring⟩

theorem dvdPow_sub {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a - b) := by
  rw [sub_eq_add_neg]; exact dvdPow_add ha (dvdPow_neg hb)

theorem dvdPow_zero (ϖ : L) (k : ℕ) : DvdPow ϖ k 0 := ⟨0, (Formalism.UG.intL L).zero_mem, by simp⟩

theorem dvdPow_mul_int {ϖ a c : L} {k : ℕ} (ha : DvdPow ϖ k a) (hc : c ∈ Formalism.UG.intL L) : DvdPow ϖ k (c * a) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨c * b, (Formalism.UG.intL L).mul_mem hc hb, by ring⟩

theorem dvdPow_sum {ϖ : L} {k : ℕ} {ι : Type} (s : Finset ι) (f : ι → L) (h : ∀ i ∈ s, DvdPow ϖ k (f i)) :
    DvdPow ϖ k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dvdPow_zero ϖ k
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact dvdPow_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem dvdPow_mono {ϖ a : L} {k l : ℕ} (hϖ : ϖ ∈ Formalism.UG.intL L) (hlk : l ≤ k) (ha : DvdPow ϖ k a) : DvdPow ϖ l a := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨ϖ ^ (k - l) * b, (Formalism.UG.intL L).mul_mem ((Formalism.UG.intL L).pow_mem hϖ _) hb, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlk]

end GlobalTheory.Hk3.IntWitt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HkUp

theorem adjoint_apply_of_normal_eigen {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : Commute T (LinearMap.adjoint T))
    (μ : ℂ) (v : V) (hv : T v = μ • v) :
    LinearMap.adjoint T v = (starRingEnd ℂ) μ • v := by
  set S : Module.End ℂ V := T - μ • LinearMap.id with hS
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ) μ • LinearMap.id := by
    rw [hS, map_sub, LinearMap.adjoint.map_smulₛₗ, LinearMap.adjoint_id]
  have hcomm : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    exact (((hT.sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
      ((Commute.one_left _).smul_left _ |>.sub_right (Commute.smul_right (Commute.one_right _) _))))
  have hSv : S v = 0 := by simp [hS, hv]
  have h0 : LinearMap.adjoint S v = 0 := by
    have : ⟪LinearMap.adjoint S v, LinearMap.adjoint S v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply,
        hSv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.mp this
  rw [hSadj] at h0
  simpa [sub_eq_zero] using h0

theorem eigen_up_along_adjoint : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → ∀ i (l : ℂ) w, h i w = l • w → op i (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  intro X E I _ _ _ _ _ _ Θ op h hint hop hh i l w hw
  have hstar : LinearMap.adjoint (h i) w = (starRingEnd ℂ) l • w :=
    adjoint_apply_of_normal_eigen (h i) (hh i) l w hw

  have hcomp : Θ ∘ₗ op i = h i ∘ₗ Θ := LinearMap.ext (hint i)
  have hadj : LinearMap.adjoint (op i) ∘ₗ LinearMap.adjoint Θ
      = LinearMap.adjoint Θ ∘ₗ LinearMap.adjoint (h i) := by
    rw [← LinearMap.adjoint_comp, ← LinearMap.adjoint_comp, hcomp]
  have h1 : LinearMap.adjoint (op i) (LinearMap.adjoint Θ w)
      = (starRingEnd ℂ) l • LinearMap.adjoint Θ w := by
    have := LinearMap.congr_fun hadj w
    simp only [LinearMap.comp_apply] at this
    rw [this, hstar, map_smulₛₗ, RingHom.id_apply]
  have h2 := adjoint_apply_of_normal_eigen (LinearMap.adjoint (op i)) ?_ _ _ h1
  · simpa [LinearMap.adjoint_adjoint] using h2
  · rw [LinearMap.adjoint_adjoint]; exact (hop i).symm

end GlobalTheory.HkUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem conv_map_idem {K : Type} [Field K] {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra K H) (hz : z * z = z)
    (σ : K →+* ℂ) (g : H) : ∑ a, σ (z.coeff a) * σ (z.coeff (a⁻¹ * g)) = σ (z.coeff g) := by
  conv_rhs => rw [← hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp [map_mul]

theorem coeff_conj_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

theorem sum_rep_idem {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) :
    (∑ g, c g • ρ g) * (∑ g, c g • ρ g) = ∑ g, c g • ρ g := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, ← map_mul]
  calc ∑ a, ∑ b, (c a * c b) • ρ (a * b) = ∑ a, ∑ g, (c a * c (a⁻¹ * g)) • ρ g := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun b => by simp
    _ = ∑ g, (∑ a, c a * c (a⁻¹ * g)) • ρ g := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
    _ = ∑ g, c g • ρ g := by simp_rw [hc]

theorem sum_rep_comm {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : H) :
    Commute (∑ h, c h • ρ h) (ρ g) := by
  unfold Commute SemiconjBy
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc]
  congr 2
  group

theorem eH_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hX i
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := fun g => conv_map_idem _ (idemOf_mul_self A.X hX) (sg0 D A) g
  have hcc : ∀ g h, RealDat.eC (A := A) (sg0 D A) (g * h * g⁻¹) = RealDat.eC (A := A) (sg0 D A) h := fun g h => by
    unfold RealDat.eC
    rw [coeff_conj_central _ (fun b => idemOf_central A.X hX b) g h]
  have happ : ∀ x v, (R.HW i (sg0 D A)).e (eH R i x) v = R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) := fun x v => by
    unfold eH RealDat.eWf gaL
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
      MultilinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
    rw [hC.models.gW i (sg0 D A) g x]; rfl
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  have hfix : ∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv := fun x => by
    rw [RealDat.Wat, mem_goodPart]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hrange ▸ LinearMap.mem_range_self _ x
        exact this
      · rw [← happ, h]
    · rintro ⟨_, h⟩
      apply hinj
      refine MultilinearMap.ext fun v => ?_
      rw [happ, h]
  have hI : eH R i * eH R i = eH R i := sum_rep_idem _ _ hc
  refine ⟨hI, fun g => sum_rep_comm _ _ hcc g, hfix, fun t y => ?_⟩
  have hm := hC.thP.thF_mem i t y
  rw [← hrange] at hm
  obtain ⟨x0, hx0⟩ := hm
  have e1 : R.thG i t y = eH R i x0 := by
    apply hinj
    rw [hC.thP.thG i t y, ← hx0]
    refine MultilinearMap.ext fun v => ?_
    rw [happ]
    exact (postOn_apply _ _ _ _).symm
  rw [e1, ← Module.End.mul_apply, hI]

end GlobalTheory.Hk3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianLocalisationAdelicPointLatticeEqStatement
section
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLocalisation_adelicPointLattice_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), Formalism.L2.Col.IsOver v Q → ∀ {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x → Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x₁ Lb) = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x Lb) := by
  first | exact @GlobalTheory.LatAdLoc.loc_latAd_eq | exact GlobalTheory.LatAdLoc.loc_latAd_eq | (intros; apply GlobalTheory.LatAdLoc.loc_latAd_eq <;> assumption)
end

