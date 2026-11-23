module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageOfPk
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def bkMk {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (b : ∀ u, (C.fm u).ramSub → (Fin m → B.LL) → B.LL)
    (hb : ∀ u φ x, B.embLL (b u φ x) = W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x))
    (u : B.Word) : (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  LinearMap.mk₂ B.LL (b u)
    (fun φ ψ x => B.embLL.injective (by
      rw [map_add (f := _), hb, hb, hb, map_add (f := _), (W.Bu_linL u _).map_add (f := _)]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linL u _).map_smul, smul_eq_mul]))
    (fun φ x y => B.embLL.injective (by
      rw [map_add (f := _), hb, hb, hb, map_add (f := _), (W.Bu_linR u _).map_add (f := _)]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linR u _).map_smul, smul_eq_mul]))


open Classical in
def bkOf {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE) (u : B.Word) :
    (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  if H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL then
    bkMk W c (fun u φ x => (H u φ x).choose) (fun u φ x => (H u φ x).choose_spec) u
  else 0

theorem bkOf_spec {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL)
    (u : B.Word) (φ : (C.fm u).ramSub) (x : Fin m → B.LL) :
    W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) = B.embLL (bkOf W c u φ x) := by
  classical
  unfold bkOf
  rw [dite_eq_left H]
  exact (H u φ x).choose_spec.symm

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def prescribedRowLat {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (jE : (Fin m → B.LL) →ₛₗ[B.embLL] W.EE) :
    Submodule (𝓞 B.LL) (Fin m → B.LL) where
  carrier := {x | ∀ w : W.what₂.places.Pl, ∃ d : 𝓞 B.LL, d ∉ (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 B.LL) {y | jE y ∈ W.what₂.RRset (W.what₂.muAt w)}}
  add_mem' := by
    intro x y hx hy w
    obtain ⟨a, ha, hax⟩ := hx w
    obtain ⟨b, hb, hby⟩ := hy w
    refine ⟨a * b, fun h => ((w : HeightOneSpectrum (𝓞 B.LL)).isPrime.mem_or_mem h).elim ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hax
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hby
  zero_mem' := fun w => ⟨1, (Ideal.ne_top_iff_one _).1 (w : HeightOneSpectrum (𝓞 B.LL)).isPrime.ne_top, by simp⟩
  smul_mem' := by
    intro s x hx w
    obtain ⟨a, ha, hax⟩ := hx w
    exact ⟨a, ha, by rw [smul_comm]; exact Submodule.smul_mem _ _ hax⟩
end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

theorem exists_divStage_of_pk : ∀ (B : Base) (C : Cols B) (G : Type) [Group G] (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (n : Nums p W₀) (η : ℕ → B.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w), (∀ v, IsUnit (p.Xo v).det) → ∀ (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V) (h : B.Word → ℝ) (etaF : ℝ), ∃ V : DivStage B C (p.what₂ e W₀ n η hη), DivIs p V ∧ (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧ V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax ∧ ((∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) ∈ Set.range B.embLL) → ∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) = B.embLL (V.div.Bk u φ x)) := by
  intro B C G _ p e W₀ n η hη hXo Ln h etaF
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL (p.what₂ e W₀ n η hη).EE p.nR p.cR ⊥
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin p.nR) (Fin p.nR) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v
  let Lr : Submodule (𝓞 B.LL) (Fin p.nR → B.LL) :=
    prescribedRowLat (p.what₂ e W₀ n η hη) (GlobalTheory.Mem.coordForm B.embLL p.cR)
  let RR : HLat B.LL :=
    { V := Fin p.nR → B.LL, ι := Fin p.nR, b := Pi.basisFun B.LL (Fin p.nR), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let Dd : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := bkOf (p.what₂ e W₀ n η hη) p.cR, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := p.Dall, delP := p.delp,
      delP_le_one := p.delp_le_one }
  let V : DivStage B C (p.what₂ e W₀ n η hη) :=
    { div := Dd
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := GlobalTheory.Mem.coordForm B.embLL p.cR
      jEE_basis := by
        have : (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) = p.cR :=
          funext (GlobalTheory.Mem.coordForm_basisFun B.embLL p.cR)
        show LinearIndependent ℂ (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) ∧
          Submodule.span ℂ (Set.range (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i))) = ⊤
        rw [this]
        exact ⟨p.cR.linearIndependent, p.cR.span_eq⟩
      jN := GlobalTheory.Mem.ramForm (p.what₂ e W₀ n η hη)
      jN_basis := fun u => GlobalTheory.Mem.ramForm_basis (p.what₂ e W₀ n η hη) u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => GlobalTheory.Mem.eMu_ramForm (p.what₂ e W₀ n η hη) u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin p.nR)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, ⟨⟨LinearEquiv.refl _ _, fun x => rfl, fun v hv x y => ?_⟩, fun S N G' => ?_⟩,
    fun u x => Iff.rfl, rfl, rfl, rfl, fun H u φ x => bkOf_spec (p.what₂ e W₀ n η hη) p.cR H u φ x⟩
  · show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) p.Xo v x y
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]
  · intro x
    simp only [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRset]
    exact Iff.rfl

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodIntegralFormsLatticeBaseLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.GoodLatFree

theorem mem_of_span {S V H : Type} [Semiring S] [AddCommGroup V] [Module S V] [AddCommGroup H] [Module ℂ H]
    (f : V →+ H) (τ : S → ℂ) (hfs : ∀ (b : S) (x : V), f (b • x) = τ b • f x) (P : Submodule ℂ H) (X : Set V)
    (hX : ∀ x ∈ X, f x ∈ P) : ∀ v ∈ Submodule.span S X, f v ∈ P := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact P.add_mem h1 h2
  | smul b x _ h => rw [hfs]; exact P.smul_mem _ h

theorem int_span {L V H : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    {iZ : Module ℤ V} (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) :
    ∀ v ∈ @Submodule.span ℤ V _ _ iZ X, j v ∈ P := by
  obtain rfl : iZ = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  exact mem_of_span j.toAddMonoidHom (fun n : ℤ => (n : ℂ)) (fun n x => by
    show j (n • x) = (n : ℂ) • j x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]) P X hX

theorem ring_span {L V H : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) : ∀ v ∈ Submodule.span (𝓞 L) X, j v ∈ P :=
  mem_of_span j.toAddMonoidHom (fun a : 𝓞 L => σ (a : L)) (fun a x => by
    show j (a • x) = σ (a : L) • j x
    rw [← algebraMap_smul L a x, map_smulₛₗ]) P X hX

theorem field_span {L V H : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) : ∀ v ∈ Submodule.span L X, j v ∈ P :=
  mem_of_span j.toAddMonoidHom (fun a : L => σ a) (fun a x => j.map_smulₛₗ a x) P X hX

theorem chiKs_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ i : Fin D.R.m, (R.FW i).ChiKs := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH i g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩


set_option maxHeartbeats 2000000 in
theorem exists_oLat_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (E : M →ₗ[ℂ] (R.toRealDat.HW i (sg0 D A3.A)).H), Function.Injective E → LinearMap.range E = (R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.toRealDat.HW i (sg0 D A3.A)).e → ∃ L : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) M, ∀ x, x ∈ L.carrier ↔ ∃ v ∈ (R.toRealDat.FW i).MK, v ∈ (R.toRealDat.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧ E x = (R.toRealDat.FW i).j (sg0 D A3.A) v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO _ hP hH i M _ _ _ E hinj hrange
  classical
  have hI := hH.aux.integral i
  have hχ := chiKs_of_pins D G Pl0 I0 T A3 Ks R F cG hP hH i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1) hχ F.lv2.P0 F.lv2.ψ0⁻¹
    (fun g => (idemOf A3.A.X).coeff g) (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]⟩
  have hsa : ∀ a, sg0 D A3.A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]

  obtain ⟨S0, hS0⟩ := GlobalTheory.GoodLatDescent.fg_MK_good (R.FW i) hI.2.1 F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
  have hfg : ((Submodule.span (𝓞 Ks) (S0 : Set (Fin (R.nW i) → D.what₂.LL))).restrictScalars ℤ).FG :=
    Submodule.FG.restrictScalars ⟨S0, rfl⟩
  obtain ⟨T0, hT0⟩ := hfg
  have hT : ∀ y, y ∈ Submodule.span ℤ (T0 : Set (Fin (R.nW i) → D.what₂.LL)) ↔
      y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
    intro y
    rw [hT0]
    show y ∈ ((Submodule.span (𝓞 Ks) (S0 : Set (Fin (R.nW i) → D.what₂.LL))) : Set _) ↔ _
    rw [hS0]; rfl

  have hWS : LinearMap.range E = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hrange]; exact (hH.aux.levelW false i _).symm
  have hjW : ∀ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ LinearMap.range E := by
    intro y hy
    rw [hWS, ← GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i]
    have hyW : y ∈ R.toRealDat.WL F.lv2 false i := hy
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i)).repr ⟨y, hyW⟩ k •
        R.toRealDat.bL F.lv2 false i k = y := by
      have h := congrArg (R.toRealDat.WL F.lv2 false i).subtype
        ((Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i)).sum_repr ⟨y, hyW⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      exact h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ, ← GlobalTheory.Mem.LiftTheta.goodForm_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

  have hex : ∀ t, ∃ x : M, t ∈ T0 → E x = (R.FW i).j (sg0 D A3.A) t := by
    intro t
    by_cases ht : t ∈ T0
    · obtain ⟨x, hx⟩ := hjW t ((hT t).1 (Submodule.subset_span (Finset.mem_coe.2 ht))).2
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose g hg using hex

  have hA : ∀ y, y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) →
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    have h1 : y ∈ Submodule.span ℤ (T0 : Set (Fin (R.nW i) → D.what₂.LL)) := (hT y).2 hy
    have h2 : ∀ x ∈ (T0 : Set (Fin (R.nW i) → D.what₂.LL)), (R.FW i).j (sg0 D A3.A) x ∈
        Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) :=
      fun x hx => Submodule.subset_span (Set.mem_image_of_mem _ hx)
    have h1' : y ∈ @Submodule.span ℤ (Fin (R.nW i) → D.what₂.LL) _ _ (AddCommGroup.toIntModule _) (T0 : Set (Fin (R.nW i) → D.what₂.LL)) := by
      convert h1
    have h3 := int_span (L := D.what₂.LL) (V := Fin (R.nW i) → D.what₂.LL) (iZ := AddCommGroup.toIntModule _) ((R.FW i).j (sg0 D A3.A)) (T0 : Set _) _ h2
    exact h3 y h1'
  have hB : ∀ y ∈ (R.FW i).Mj F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    rw [← hspan] at hy
    exact ring_span ((R.FW i).j (sg0 D A3.A)) _ _ (fun x hx => hA x hx) y hy
  have hC : ∀ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    rw [← (GlobalTheory.GoodLat.mj_full (R.FW i) hI.1 hI.2.1 F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)).2] at hy
    exact field_span ((R.FW i).j (sg0 D A3.A)) _ _ (fun x hx => hB x hx) y hy
  have hgen : Submodule.span ℂ ((T0.image g : Finset M) : Set M) = ⊤ := by
    apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_top, Submodule.map_span, Finset.coe_image, Set.image_image]
    have him : (fun t => E (g t)) '' (T0 : Set _) = (R.FW i).j (sg0 D A3.A) '' (T0 : Set _) :=
      Set.image_congr fun t ht => hg t ht
    rw [him]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact hjW t ((hT t).1 (Submodule.subset_span ht)).2
    · rw [hWS, ← GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe]
      beta_reduce
      rw [GlobalTheory.Mem.LiftTheta.goodForm_single]
      exact hC _ (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i) k).2
  refine ⟨⟨T0.image g, hgen⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨c, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_induction _
      (fun w => ∃ v ∈ (R.FW i).MK, v ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧
        w = (R.FW i).j (sg0 D A3.A) v) ?_ ?_ ?_
    · rintro _ _ ⟨v1, h1, h1', rfl⟩ ⟨v2, h2, h2', rfl⟩
      exact ⟨v1 + v2, Submodule.add_mem _ h1 h2, Submodule.add_mem _ h1' h2', (map_add _ _ _).symm⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, (map_zero _).symm⟩
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      have htg := (hT t).1 (Submodule.subset_span (Finset.mem_coe.2 ht))
      obtain ⟨k, hk⟩ := hO (c (g t))
      have hint : IsIntegral ℤ k := by
        have h1 : IsIntegral ℤ (D.what₂.OtoLL (c (g t))) := D.O_int (c (g t))
        rw [← hk] at h1
        exact (isIntegral_algHom_iff (algebraMap Ks D.what₂.LL).toIntAlgHom (algebraMap Ks D.what₂.LL).injective).1 h1
      let kk : 𝓞 Ks := ⟨k, hint⟩
      have hkk : D.what₂.OtoLL (c (g t)) • t = kk • t := by
        rw [← hk, algebraMap_smul, ← algebraMap_smul Ks kk t]
        rfl
      refine ⟨D.what₂.OtoLL (c (g t)) • t, ?_, Submodule.smul_mem _ _ htg.2, ?_⟩
      · rw [hkk]; exact Submodule.smul_mem _ _ htg.1
      · rw [map_smul, hg t ht, map_smulₛₗ, hsa]
        rfl
  · rintro ⟨v, hv1, hv2, hxv⟩
    obtain ⟨n, -, hn⟩ := Submodule.mem_span_finset.1 ((hT v).2 ⟨hv1, hv2⟩)
    have hx : x = ∑ t ∈ T0, ((n t : ℤ) : ℂ) • g t := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hxv, ← hn, map_sum, map_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_zsmul, map_smul, hg t ht, Int.cast_smul_eq_zsmul]
    refine ⟨fun y => ∑ t ∈ T0 with g t = y, (n t : D.what₂.O), ?_⟩
    rw [hx]
    symm
    refine Finset.sum_image' _ fun t _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t' ht' => ?_
    rw [(Finset.mem_filter.1 ht').2, map_intCast]

end GlobalTheory.Mem.GoodLatFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.ThetaLevel

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  have h1 : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, z ^ i‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have : ∀ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ (z ^ i).re := by
      intro i _
      have h2 := (Complex.abs_re_le_norm (z ^ i - 1)).trans_lt (h i)
      rw [Complex.sub_re, Complex.one_re, abs_lt] at h2
      linarith [h2.1]
    have h3 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h4 := h N
  rw [← geom_sum_mul, norm_mul] at h4
  rw [div_lt_iff₀ hpos] at hN
  nlinarith [h1 N]

theorem eventually_smul (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hw : GlobalTheory.Ker.IsWeak ψ S T om)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∃ c : ℂ, om p f = c • f := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  filter_upwards [_root_.GlobalTheory.Mem.CoefInv.eventually_coef_actO D ψ hψ S T μ 𝓕 hμ h𝓕 f hf] with p hp h1 h2
  obtain ⟨g, h⟩ := p
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (om (g, h) f) hf (hw.om_pres _ f hf) (fun w => by
    have e : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := GlobalTheory.AdelicLatMove.actO_actO_inv S T g h w
    have e1 := hp h1 h2 (actO S T g⁻¹ h⁻¹ w)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om (g, h)) (hw.om_pres _) (hw.om_unit μ 𝓕 hμ h𝓕 _)
      (heisO ψ S T (actO S T g⁻¹ h⁻¹ w) f) f (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf
    rw [hw.om_heis g h _ f hf, e] at e2
    simp only [e] at e1
    exact e2.trans e1.symm)
  exact ⟨c, hc⟩

theorem exists_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ f, IsThetaFunO ψ S T f → ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧ IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → om (k, k') f = f := by
  intro D ψ hψ S T om hw hc f hf
  by_cases h0 : f = 0
  · exact ⟨⊤, ⊤, by simp, by simp, fun k _ _ k' _ _ => by rw [h0, map_zero]⟩
  obtain ⟨w, hw0⟩ := Function.ne_iff.1 h0
  have hw0 : f w ≠ 0 := hw0
  have hcont : Continuous fun p : GA D S × GA D T => ‖om p f w / f w - 1‖ :=
    (((hc f hf w).div_const _).sub continuous_const).norm
  have hnear : ∀ᶠ p : GA D S × GA D T in 𝓝 1, ‖om p f w / f w - 1‖ < 1 / 2 := by
    refine hcont.continuousAt.eventually_lt continuousAt_const ?_
    simp [div_self hw0]
  have hN := (eventually_smul D ψ hψ S T om hw f hf).and hnear
  obtain ⟨N, hN1, N', hN2, hsub⟩ := mem_nhds_prod_iff.1 (show _ ∈ 𝓝 ((1 : GA D S), (1 : GA D T)) from hN)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D S N hN1
  obtain ⟨U', hU', hUN'⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D T N' hN2
  refine ⟨U, U', hU, hU', fun k hk hkf k' hk' hkf' => ?_⟩
  obtain ⟨c, hcf⟩ := (hsub (Set.mk_mem_prod (hUN k hk hkf) (hUN' k' hk' hkf'))).1 hkf hkf'
  have hpow : ∀ n : ℕ, om ((k, k') ^ n) f = c ^ n • f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hcf, map_smul, ih, smul_smul, pow_succ']
  have hc1 : c = 1 := eq_one_of_pow_near fun n => by
    have h := (hsub (Set.mk_mem_prod (hUN _ (pow_mem hk n) (pow_mem hkf n))
      (hUN' _ (pow_mem hk' n) (pow_mem hkf' n)))).2
    have e : om (k ^ n, k' ^ n) f = c ^ n • f := hpow n
    rw [e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hw0] at h
    exact h
  rw [hcf, hc1, one_smul]

end GlobalTheory.Mem.ThetaLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrank
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_conjRows_eq {D : D7} (X : HidaSetting D) :
    Module.finrank ℂ (conjRows X) = Module.finrank ℂ (HHX X) := by
  let e := conjL (muX X)
  let j : conjRows X ≃+ HHX X :=
    { toFun := fun f => ⟨e f, f.2⟩
      invFun := fun g => ⟨e.symm g, by
        show e.toLinearEquiv.toLinearMap (e.symm g) ∈ HHX X
        simpa using g.2⟩
      left_inv := fun f => by ext1; simp
      right_inv := fun g => by ext1; simp
      map_add' := fun f g => by ext1; simp }
  have hbij : Function.Bijective (starRingEnd ℂ : ℂ → ℂ) :=
    Function.Involutive.bijective (fun z => by simp)
  have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ : ℂ → ℂ) j hbij (fun r m => by
    ext1
    show e (r • (m : L2X X)) = (starRingEnd ℂ r) • e m
    exact e.map_smulₛₗ r m)
  unfold Module.finrank
  rw [hr]

theorem exists_rowJ_and_finrank_HHX : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c eE hc hv₀ hE hrange hnorm hle hJ1 hJ2
  refine ⟨fun hD => ?_, exists_rowJ_of_evalOn hc hv₀ hE hrange hnorm hle hJ2⟩
  obtain ⟨J1, -⟩ := hJ1
  have hD' : D.what₂.Dall = Module.finrank ℂ (MultR R F) := hD
  rw [hD', J1.finrank_eq, finrank_conjRows_eq]

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelVectorSumOfIsotypicPiecesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_vector_sum_of_isotypic_pieces : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  first | exact @GlobalTheory.decomp_kernels_isotIn | exact GlobalTheory.decomp_kernels_isotIn | (intros; apply GlobalTheory.decomp_kernels_isotIn <;> assumption)
end

