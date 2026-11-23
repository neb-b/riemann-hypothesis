module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0804
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
section
noncomputable section

namespace GlobalTheory.Mem.SRe.SxPass

section Mv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl Formalism.L2.SG.ColDict Formalism.L2.SG.HidaSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {F F' : ∀ u, Forms0 D u}


set_option maxHeartbeats 4000000 in
def trCar (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) : Transport X u (F' u) :=
  { t with
    hc_rep := fun c => by rw [(h u).2.2.2.1]; exact t.hc_rep c
    J_isom := fun c ξ η => by rw [(h u).2.2.2.2]; exact t.J_isom c ξ η }

set_option maxHeartbeats 4000000 in
theorem colDictL_car (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) (hK : X.LevelSubgroupCharacter) :
    colDictL X (trCar h t) hK = colDictL X t hK := by
  refine LinearMap.ext fun T => funext fun c => funext fun z => ?_
  exact congrArg (fun e => t.J (shP X u T.1 (t.hc c)) (e z)) (congrArg DFunLike.coe (h u).2.2.2.2)

theorem chi_of_heq {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} (e : U' = U) (h : HEq chi' chi)
    (x : G) (hx : x ∈ U') : chi' ⟨x, hx⟩ = chi ⟨x, e ▸ hx⟩ := by
  subst e
  rw [eq_of_heq h]

set_option maxHeartbeats 4000000 in
theorem lev_car (h : SameCar F F') {X : HidaSetting D} {u} {t : Transport X u (F u)} {hK : X.LevelSubgroupCharacter} (l : LevelMatch X t hK) :
    LevelMatch X (trCar h t) hK := by
  refine ⟨fun x => ?_, fun g y hr => ⟨?_, fun hk hy => ?_⟩⟩
  · rw [(h u).1]; exact l.1 x
  · rw [(h u).2.1]; exact (l.2 g y hr).1
  · rw [chi_of_heq (h u).2.1 (h u).2.2.1]; exact (l.2 g y hr).2 hk _


set_option maxHeartbeats 4000000 in
def packCar (h : SameCar F F') (P : SPack D F) : SPack D F' :=
  { P with
    tr := fun u => trCar h (P.tr u)
    into := fun u T => by rw [colDictL_car]; exact P.into u T
    bij := fun u => by unfold ColDictBij; rw [colDictL_car]; exact P.bij u
    lev := fun u => lev_car h (P.lev u)
    isom := fun u a b => by rw [colDictL_car]; exact P.isom u a b }


set_option maxHeartbeats 4000000 in
def restCar (h : SameCar F F') {P : SPack D F} (S : SRest P) : SRest (packCar h P) where
  hI := S.hI
  autTie := S.autTie
  colPin := fun u x => Subtype.ext ((LinearMap.congr_fun (colDictL_car h (P.tr u) P.Y.hK) _).trans (congrArg Subtype.val (S.colPin u x)))
  j := S.j
  rowPin := S.rowPin
  locTied := S.locTied


set_option maxHeartbeats 4000000 in
def satCar (h : SameCar F F') (p : RowPk D) (s : p.SAt F) : p.SAt F' :=
  { P := packCar h s.P, S := restCar h s.S, t := s.t, c := s.c, c_pos := s.c_pos, see := s.see, ev := s.ev, rowJ := s.rowJ }

end Mv

section Slot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 8000000 in
theorem sxMv : SxMv := by
  intro K B f T w Z Wt p0 r col N h p0' t col' e ⟨s⟩
  obtain ⟨F₁, hF⟩ := exists_sameF_ofDiv (D := Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) fun u => (col.C.forms u).to0
  obtain ⟨s', -⟩ := _root_.GlobalTheory.Mem.SRe.sAtL_exists_ofDiv B w.C Z (pkOf r).G' (pkOf r).Pl0 (pkOf r).T (pkOf r).A (pkOf r).Ks (pkOf r).R (pkOf r).F
    (fun u => (col.C.forms u).to0) (pkOf r).eE (cast (sx_eq r col) s) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have c := StdUnique.sameStd B f T w Z (New.ofDiv (Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :)))) col ((by with_unfolding_all exact (col' :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have e' : pkOf t = (pkOf r).up Z Z.S N h := eq_of_heq e
  rw [sx_eq t col', e']
  exact ⟨satCar (D := Late.D (upL Z Z.S N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) ((pkOf r).up Z Z.S N h) ((by with_unfolding_all exact (s' :)))⟩

end Slot

end GlobalTheory.Mem.SRe.SxPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem coreCharacter_fieldInclusion_eq_columnHeckeChar {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {h : B.fields.Ok} {W : Set B.places.Pl}
    (z : Dat (w.st Z) w.I h T W) (j : Fin B.R.m) :
    ChrEq (z.core.chiW ((j : ℕ) + 1) z.core.toCore.σ₀) (w.I.C.mu0 j) := by
  have e := Formalism.IndefR.FWT.chiTie_of_chiR z.core z.R.toRealDat z.geo.fw.alg_eq z.geo.fw.laws.pins.2.2.1 z.geo.fw.chiR j
  rw [e]
  have h1 := z.lev.is.mu0 j
  rw [z.lev.C] at h1
  exact h1

theorem embLL_chi {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : Fin B.R.m)
    (p : {p // p ∈ (B.primes w.px).vGs}) (c : (𝓞 B.fields.E ⧸ p.1.asIdeal)ˣ) (y : 𝓞 B.fields.E) (x : B.fields.Eˣ)
    (hx : (x : B.fields.E) = y) (hc : (c : 𝓞 B.fields.E ⧸ p.1.asIdeal) = Ideal.Quotient.mk p.1.asIdeal y) :
    B.embLL ((w.I.Ch.chi j p c : B.fields.Kˣ) : B.fields.K) = (((w.I.C.mu0 j).locK p.1 x : ℂˣ) : ℂ)⁻¹ := by
  have h1 := (w.ok.ch_tied.mu0 j).atg p x y c hx hc
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem app_chiW {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Type} [Monoid A]
    {H₁ H₂ : Host E} {l₁ : Level H₁} {l₂ : Level H₂} {c₁ : Coeff l₁} {c₂ : Coeff l₂}
    {χ₁ : ℕ → (c₁.F →+* ℂ) → A →* Circle} {χ₂ : ℕ → (c₂.F →+* ℂ) → A →* Circle}
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hχ : HEq χ₂ χ₁) (n : ℕ) :
    χ₂ n c₂.F.val.toRingHom = χ₁ n c₁.F.val.toRingHom := by
  cases hH; cases hl; cases hc; cases hχ; rfl

end GlobalTheory.Mem.R3.Rw.ChiTr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem embLL_chi_ext : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX j₁ j₂ hj p₁ p₂ hp c₁ c₂ hc
  have A₁ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₁ j₁
  have A₂ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₂ j₂
  have eH := hX.H
  have el := hX.l
  have ec := hX.c
  have eχ := hX.chiW
  obtain ⟨hP, -⟩ := hE
  clear hX
  rcases B₂ with ⟨P₂⟩
  change P₂ = B₁.toPre at hP
  subst hP
  have ec₀ := app_chiW eH el ec eχ ((j₁ : ℕ) + 1)
  rw [← hj] at A₂
  have A₂' : ChrEq (D := (w₁.st Z₁).toD7) (z₁.core.chiW ((j₁ : ℕ) + 1) z₁.core.Q.c.F.val.toRingHom) (w₂.I.C.mu0 j₂) := by
    rw [← ec₀]
    exact A₂
  have hχ : w₁.I.C.mu0 j₁ = w₂.I.C.mu0 j₂ := (GlobalTheory.ChrEqUnique.chrEq_unique _).1 _ _ _ A₁ A₂'
  rcases p₂ with ⟨q₂, hq₂⟩
  have eq : q₂ = p₁.1 := eq_of_heq hp
  subst eq
  have ecc : c₂ = c₁ := eq_of_heq hc
  subst ecc
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c₂ : 𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)
  have hy0 : ((y : 𝓞 B₁.fields.E) : B₁.fields.E) ≠ 0 := by
    intro h0
    have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
    rw [h0', map_zero] at hy
    exact c₂.ne_zero hy.symm
  rw [embLL_chi w₂ j₂ _ c₂ y (Units.mk0 _ hy0) rfl hy.symm, embLL_chi w₁ j₁ p₁ c₂ y (Units.mk0 _ hy0) rfl hy.symm, hχ]

end GlobalTheory.Mem.R3.Rw.ChiTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.ThetaRead3

theorem lift_postOn {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp [postOn]

theorem thF_congr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (i : Fin D.R.m) (t u : T) (hu : u = t)
    (z : (R.HV i t).H) (z' : (R.HV i u).H) (h : R.extV i u z' = R.extV i t z) : R.thF i u z' = R.thF i t z := by
  subst hu
  rw [hinj i u h]

theorem ofInjective_symm_eq {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (f : X →ₗ[ℂ] Y)
    (hf : Function.Injective f) (a : LinearMap.range f) : f ((LinearEquiv.ofInjective f hf).symm a) = a := by
  have h := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective f hf) a
  exact congrArg Subtype.val h


set_option maxHeartbeats 4000000 in
theorem thetaP_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t x
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hP.char.base.thP hH.aux.ex
  have hM := hP.char.base.models
  have hμ : Used0 D (Y.tup t) := by
    rcases hP.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h, Y.tup0]
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM
  set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt
  obtain ⟨w, hwM, hwK, hwW⟩ := _root_.GlobalTheory.ThetaFireLift.thetaFireL R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev
    hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM
  have hth := Y.tied.lift.theta (Y.tup t) hμ i xM w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW

  set u := Y.tupT (Y.tup t) with hu
  set a := Y.IL.jMt (Y.tup t) hμ i xM with ha
  set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm
    (Submodule.inclusion inf_le_left a) with hz'
  have hz'1 : R.extV i u z' = R.extV i t zt := by
    rw [hz', ofInjective_symm_eq]
    exact Y.mtRead i t hμ x
  have hzz : R.thF i u z' = R.thF i t zt := thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A3.A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A3.A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i u z')
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := e
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i t zt = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0
        rw [hlow v, hzz, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  have h1 := (Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth
  change PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt] at h1
  exact (hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)

end GlobalTheory.Mem.ThetaRead3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwisted
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SerRatRay
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerStdTwist

theorem seriesRatS_of_untwRatS (hRF : GlobalTheory.Published.RayClassFieldSt) (hU : GlobalTheory.SerStd.UntwRatS) : GlobalTheory.SerStd.SeriesRatS := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP hstd gramR c0R c0L hFT u hu
  obtain ⟨ph, hph, hU'⟩ := hU D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP hstd gramR c0R c0L hFT u hu
  refine ⟨ph, hph, fun C hC s hs f hf w hw => ⟨hU' C hC s hs f hf w hw, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩⟩
  · have := _root_.GlobalTheory.TwistRat.isRat_twist hRF D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc hδ dd
      (Or.inl hdd) _ (hU' C hC s hs f hf w hw)
    simpa [mul_assoc] using this
  · obtain ⟨c, hc, dd, hdd, heq⟩ :=
      GlobalTheory.WeilTwistSeries.theta_weil_twist D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc hδ om hom s hs
        f hf w hw
    have h1 := _root_.GlobalTheory.TwistRat.isRat_twist hRF D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc
      hδ dd hdd _ (hU' C hC s hs f hf w hw)
    have h2 := isRat_const_mul T i hV C (κ i) _ c h1 hc
    convert h2 using 2 with g
    rw [heq g]; ring

end GlobalTheory.SerStdTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeLevelIffReductionLevelConjugateCharact
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev

theorem lev_iffQ : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E},
    J' = 1 → J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad),
    S.Lb = Formalism.L2.Col.stdLat E n → ∀ {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n'), 0 < t → n = r + s * t →
    ∀ {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    RdLevOn hc Set.univ S.U S.chi (parFam h t s P χ) emb Q (fun _ => blockTri (blk2 r))
      (fun P => (ξ P.1).comp (blkDet (blk2 r) 1)) →
    ∀ (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    (∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H) →
    (∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K)) →
    (∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K)) →
    ∀ (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
    (∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) →
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  intro F E K _ _ _ _ _ _ _ hc n n' e _ J' J hJ' hJ T f bad S hL r t s h h' ht hn SG Q P χ emb ξ hR P' cg hH hchi hcg g y hgy
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔
      g ∈ lev hc 1 1 (parDat h t s P χ) ∧ ∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, a5⟩
      exact ⟨⟨⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, fun w _ => (hH _).1 a5 w⟩, a4⟩
    · rintro ⟨⟨⟨a1, a2, a3, -⟩, a5⟩, a4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, (hH _).2 fun w => a5 w (Set.mem_univ w)⟩
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ∧ (∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r)) ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, hq⟩
      exact (hR g (Set.mem_univ g) h2 h1).1.2 ⟨fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w), fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2⟩
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      obtain ⟨a, b⟩ := (hR g (Set.mem_univ g) h2 h1).1.1 hy
      refine ⟨⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩, fun PP hP => ?_⟩
      · have := a w
        rwa [← hred h2] at this
      · have := b ⟨PP, hP⟩
        rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  obtain ⟨h3, hq⟩ := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 ⟨h4, hq⟩
  obtain ⟨r1, r2⟩ := hR g (Set.mem_univ g) h2 h1
  have hq' : ∀ PP : Q, redAt 1 PP.1 ⟨g, h2⟩ ∈ blockTri (blk2 r) := fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2
  have hw' : ∀ w : SG, redAt 1 w.1 ⟨g, h2⟩ ∈ (parFam h t s P χ w).H := (r1.1 hy).1
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) =
      emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) *
        ∏ PP ∈ Q, ((((ξ PP)⁻¹ (dBlk (blk2 r) 1 (redFn 1 PP g))) : ℂˣ) : ℂ) := by
    have eQ : (parDat h t s P χ).Q = ∅ := rfl
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2, eQ, Finset.prod_empty, mul_one]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy hw' hq', star_mul']
  congr 1
  · show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
    rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
    have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
      (isOfFinOrder_of_finite ⟨_, hw' w⟩)).norm_eq_one
    refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
    exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
      (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))
  · rw [star_prod, ← Finset.prod_coe_sort Q]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have : Finite (𝓞 E ⧸ PP.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    have ed : dBlk (blk2 r) 1 (redFn 1 PP.1 g) = blkDet (blk2 r) 1 ⟨_, hq' PP⟩ := by
      unfold dBlk
      rw [extendOne_of_mem _ (hq PP.1 PP.2)]
      exact congrArg _ (Subtype.ext (hred h2 PP.1))
    rw [ed, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have b1 := (((Units.coeHom ℂ).comp (ξ PP.1)).isOfFinOrder
      (isOfFinOrder_of_finite (blkDet (blk2 r) 1 ⟨_, hq' PP⟩))).norm_eq_one
    exact Complex.inv_eq_conj b1

end GlobalTheory.SeeSaw.TwLev

end
end

