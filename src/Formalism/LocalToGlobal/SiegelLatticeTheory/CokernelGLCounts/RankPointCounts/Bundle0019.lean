module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCells
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def cellEquiv (hD : Data W S N' K π) :
    Quotient (Setoid.ker (Formalism.L2.SG.Pf.ProdEP2Core.dcMap (Ak S K) (πk W S N' K π hD) (Hk W K g))) ≃
      Quotient (cellRel W N' K g) := by
  refine Equiv.ofBijective (Quotient.lift (fun k => (⟦toCell W S N' K π g hD k⟧ : Quotient (cellRel W N' K g)))
    (fun k₁ k₂ h => ?_)) ⟨?_, ?_⟩
  · apply Quotient.sound
    exact (cellRel_iff W S N' K π g hD k₁ k₂).2
      ((Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).1 h)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h k₁ =>
      induction y using Quotient.inductionOn with
      | h k₂ =>
        apply Quotient.sound
        have h2 := Quotient.exact hxy
        exact (Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).2
          ((cellRel_iff W S N' K π g hD k₁ k₂).1 h2)
  · intro y
    induction y using Quotient.inductionOn with
    | h c =>
      obtain ⟨k, rfl⟩ := toCell_surj W S N' K π g hD c
      exact ⟨⟦k⟧, rfl⟩

theorem card_cells (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hk W K g).map (πk W S N' K π hD)).index := by
  rw [← Nat.card_congr (cellEquiv W S N' K π g hD)]
  exact Formalism.L2.SG.Pf.ProdEP2Core.card_dc (Ak S K) (πk W S N' K π hD) (Hk W K g) (πk_id W S N' K π hD)

end Formalism.L2.SG.Pf.CountAb
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiniteLevelVolumeOfMeasure
section
noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finiteLevelVolume_of_measure (hM : X.MeasTie hb) : FiniteLevelVolumeEquality X hb := by
  unfold FiniteLevelVolumeEquality
  rw [hM.2.2.1]
  haveI : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  let e := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).toHomeomorph.toMeasurableEquiv
  have he : (X.toFin hb : X.B.I.Gf → _) = e := rfl
  have hK : levelUnitary X hb = e '' X.K2 := rfl
  rw [hK, he, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]

theorem mem_rr_iff (x : X.B.I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ↔
      toHA X.B.I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I (toHA X.B.I hb) (toHA_isBridge X.B.I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      h ∈ ratHA X.B.I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA X.B.I hb).injective hyx]

theorem covolTie_of (hM : X.MeasTie hb) : CovolTie X := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' X.B.I X.B.μf
  haveI : (X.B.I.muA X.B.μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨X.B.fund_spec.1, X.B.fund_spec.2.1, X.B.fund_spec.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
  let e := (toHA X.B.I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I :=
    { toFun := fun g => ⟨(toHA X.B.I hb).symm (g : HA _ _ _), (mem_rr_iff X hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA X.B.I hb x, (mem_rr_iff X hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  haveI : Countable Γ := Function.Injective.countable eΓ.injective
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((X.B.I.muA X.B.μf).map e) (X.B.I.muA X.B.μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' X.B.fund) X.measG.μG := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : X.B.I.GA) * x) = (g : HA _ _ _) * e x
    show toHA X.B.I hb ((toHA X.B.I hb).symm g * x) = (g : HA _ _ _) * toHA X.B.I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmap : X.measG.μG (e '' X.B.fund) = X.B.I.muA X.B.μf X.B.fund := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]
  haveI : (X.measG.μG).IsHaarMeasure := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    exact (toHA X.B.I hb).isHaarMeasure_map (X.B.I.muA X.B.μf)
  haveI : (X.measG.μG).IsMulLeftInvariant := inferInstance
  haveI : MeasurableConstSMul Γ (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    ⟨fun c => (continuous_const_mul (c : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurable⟩
  unfold CovolTie covolBy
  split_ifs with h
  · have h1 : IsFundamentalDomain Γ h.choose X.measG.μG := h.choose_spec
    rw [h1.measure_eq hfd, hmap]
    rfl
  · exact absurd ⟨_, hfd⟩ h

section MassData

open Formalism.L2.SG.MassDataConc Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX_holds (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X :=
  MassDataDstarX X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq L A hH hKpp (finiteLevelVolume_of_measure X hb hH.1)
    (covolTie_of X hb hH.1)

end MassData

end Formalism.L2.SG.IntegralApproximation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianW0SpanZero
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Psi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem MMfam_mem_sup (t : Term V M r) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
  have hf : ∀ a, t.f a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hf' : ∀ a, t.f' a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  unfold HermSp.MMfam
  rcases M.split with _ | g
  · rcases i with a | a
    · exact hf a
    · exact hf' a
  · rcases i with a | a
    · exact hf a
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hf' a) (hf a))

theorem hermitian_W0_span_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h w m = 0 := by
  have hle : Submodule.span E (Set.range (H.MMfam t)) ≤ H.Xp t.f ⊔ H.Xp t.f' :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)
  exact hw m (hle hm)

end Psi

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {α : Type*} {r : α → α → Prop}

theorem eqvGen_iff_of (f : α → Prop) (hf : ∀ a b, r a b → (f a ↔ f b)) {a b : α} (h : Relation.EqvGen r a b) :
    (f a ↔ f b) := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem eqvGen_eq_of {β : Type*} (f : α → β) (hf : ∀ a b, r a b → f a = f b) {a b : α} (h : Relation.EqvGen r a b) :
    f a = f b := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

end Gen

theorem relRepC : RelRepC := by
  intro D X Y u u' t hr hG
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨hGF, -, hRF, -, -⟩ := term_function_const D u u' (X.Fu u) t.lam hΛ

  set x : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') := ⟨frq X t.rep, t.rep.2.2.2.2⟩ with hx
  have hcls : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := rfl
  constructor
  · obtain ⟨F', ⟨hP, hmk⟩, hrel⟩ := hr
    have hcls' : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := hcls
    rw [hcls'] at hmk
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')) ⟨F', hP⟩ x :=
      Quot.eqvGen_exact hmk
    exact (eqvGen_iff_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Relevant D.host.F (lf D (X.Fu u)).fl y.1.fl) (fun a b hab => hRF a b hab) he).1 hrel
  · have hG' : TermDef.Gt t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')
        (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x) = 0 := hG
    unfold TermDef.Gt at hG'
    have hout := Quot.out_eq (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u'))
        (Quot.out (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)) x :=
      Quot.eqvGen_exact hout
    have := eqvGen_eq_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Gval (lf D (X.Fu u)) y.1) (fun a b hab => hGF a b hab) he
    rw [← this]; exact hG'

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PointRegroupPf
section
noncomputable section

namespace Formalism.L2.SG.WConst

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem signFlip_involutive {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K),
    Formalism.L2.SG.DataInst.signAux r b (Formalism.L2.SG.DataInst.signAux r b x) = x
  | _, [] => rfl
  | b, (s, t) :: rest => by
    simp only [Formalism.L2.SG.DataInst.signAux, signFlip_involutive r (b + s) rest]
    congr 2
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

variable {D : D7}

def lst (w : Point D.host.E (D.R.rS + 1)) : Formalism.FourierDecayAlt.TB.Pt D.host.E :=
  Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w)

theorem ptOfList_lst (w : Point D.host.E (D.R.rS + 1)) :
    Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) (lst w) = some w := by
  have h : Formalism.L2.SG.DataInst.signPt D.R.rS (lst w) = Formalism.L2.S.ptList w := by
    unfold lst Formalism.L2.SG.DataInst.signPt
    exact signFlip_involutive _ _ _
  have hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS (lst w)) (D.R.rS + 1) := by
    rw [h]; exact Formalism.L2.S.ptList_isPtL w
  unfold Formalism.L2.SG.DataInst.ptOfList
  rw [dite_eq_left hL]
  congr 1
  apply (Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext h

theorem lst_injective : Function.Injective (lst (D := D)) := by
  intro w w' h
  have := (ptOfList_lst w).symm.trans ((congrArg _ h).trans (ptOfList_lst w'))
  exact Option.some_injective _ this

theorem eq_lst_of {p : Formalism.FourierDecayAlt.TB.Pt D.host.E} {w : Point D.host.E (D.R.rS + 1)}
    (hp : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p = some w) : p = lst w :=
  Formalism.L2.SG.RowsAbsX.ptOfList_inj hp (ptOfList_lst w)

section Regroup

open Formalism.L2.SG.Pf.RowForm

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem pointRegroupC_of (hA : ClassAbsC X Y u u' vR i0 i0' νq κ) : PointRegroupC X Y u u' vR i0 i0' νq κ := by
  intro ρ
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set V : Point D.host.E (D.R.rS + 1) → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
    fun w => Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) with hV

  have hsupp : Function.support (ptVal X Y u u' vR i0 i0' νq κ ρ) ⊆ Set.range lst := by
    intro p hp
    rcases h : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p with _ | w
    · exact absurd (by simp [ptVal, h]) hp
    · exact ⟨w, (eq_lst_of h).symm⟩
  rw [← lst_injective.tsum_eq hsupp]

  set f : ClassT X Y u u' κ ρ → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) := fun t =>
    (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) •
      V (Formalism.L2.SG.PairVal.ptOf t.1) with hf
  let e : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) →
      ClassT X Y u u' κ ρ := fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.1⟩
  have huniq : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w w', t.atPt w → t.atPt w' → w = w' :=
    fun t w w' h h' => Formalism.L2.SG.RowsAbsX.atPt_uniq _ _ _ t.cls w w' h h'
  have he : Function.Injective e := by
    rintro ⟨w, t, ht⟩ ⟨w', t', ht'⟩ h
    have htt : t = t' := congrArg Subtype.val h
    subst htt
    have hw : w = w' := huniq t w w' ht.2.2 ht'.2.2
    subst hw
    rfl
  have hpt : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w, t.atPt w → Formalism.L2.SG.PairVal.ptOf t = w := by
    intro t w h
    have hrel := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t w h
    exact huniq t _ _ (Formalism.L2.SG.PairVal.ptOf_spec t ⟨w, h, hrel⟩) h
  have hc : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w, t.atPt w →
      Formalism.L2.SG.PairVal.cTerm vR t = Formalism.L2.SG.PairVal.cAt vR t w :=
    fun t w h => Formalism.L2.SG.PairVal.cTerm_of_atPt vR t h (fun w' h' => huniq t w' w h' h)
  have hFe : ∀ x : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}),
      (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1 =
        f (e x) := by
    rintro ⟨w, t, ht⟩
    simp only [hf, e, hpt t w ht.2.2, hc t w ht.2.2]
  have hfs : Summable f := Summable.of_norm (hA ρ)
  have hsum : Summable (f ∘ e) := hfs.comp_injective he
  have hsumF : Summable (fun x : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) =>
      (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1) := by
    simpa only [Function.comp_def, hFe] using hsum
  have hnorm : Summable (fun x : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) =>
      ‖(((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1‖) := by
    have h0 : Summable (fun x => ‖f (e x)‖) := (hA ρ).comp_injective he
    exact h0.congr (fun x => by rw [← hFe x])

  have h2 : ∀ w, ptVal X Y u u' vR i0 i0' νq κ ρ (lst w) =
      ∑' t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w},
        (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w) • V w := by
    intro w
    simp only [ptVal, ptOfList_lst]
    by_cases hV : V w = 0
    · have hV' : Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) = 0 := hV
      rw [hV', smul_zero]
      simp only [hV, smul_zero, tsum_zero]
    · have h3 := hnorm.sigma_factor w
      simp only [norm_smul] at h3
      have h4 : Summable (fun t : {t : Term D u u' (X.Fu u) (Y.what₂ u) //
          Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w} =>
          ‖((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w‖) := by
        have h5 := h3.div_const ‖V w‖
        have hVn : ‖V w‖ ≠ 0 := norm_ne_zero_iff.2 hV
        simpa only [mul_div_assoc, div_self hVn, mul_one] using h5
      exact ((Summable.of_norm h4).tsum_smul_const (V w)).symm
  rw [tsum_congr h2]
  rw [← hsumF.tsum_sigma]
  rw [tsum_congr hFe]
  have hsuppf : Function.support f ⊆ Set.range e := by
    intro t ht
    by_cases h : ∃ w, t.1.atPt w
    · obtain ⟨w, hw⟩ := h
      exact ⟨⟨w, t.1, t.2.1, t.2.2, hw⟩, rfl⟩
    · exfalso
      apply ht
      simp only [hf, Formalism.L2.SG.PairVal.cTerm, dif_neg h, mul_zero, zero_smul]
  exact he.tsum_eq hsuppf

end Regroup

end Formalism.L2.SG.WConst
end
end

