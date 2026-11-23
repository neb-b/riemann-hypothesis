module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHeckeOperatorsRowsIntertwineThetaLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Hk3.HeckeRowsClose

section TwLemmas
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_sub_injective (s : Bool) {V W : Submodule ℂ E} (h : Tw.sub s V = Tw.sub s W) : V = W := by
  ext x
  exact SetLike.ext_iff.mp h (Tw.mk s x)

theorem tw_span_image (s : Bool) (S : Set E) :
    Submodule.span ℂ ((Tw.mk s : E → Tw s E) '' S) = Tw.sub s (Submodule.span ℂ S) := by
  have h1 : Tw.sub s (Submodule.span ℂ S) = (Submodule.span ℂ S).map (Tw.mkL s E) := by
    ext x
    constructor
    · intro hx; exact ⟨Tw.out x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  rw [h1, Submodule.map_span]; rfl

theorem tw_commute (s : Bool) {a b : Module.End ℂ E} (h : Commute a b) : Commute (Tw.map s a) (Tw.map s b) := by
  show Tw.map s a * Tw.map s b = Tw.map s b * Tw.map s a
  ext x
  exact congrArg (Tw.mk s) (LinearMap.congr_fun h.eq (Tw.out x))

end TwLemmas

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem opC_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hK : (R.toCx3 F).KFormR) (t : T) (i : (A3.rowI t).OpIx)
    (g : Module.End ℂ (R.HX t).H) (hg : ∀ x, R.jX t ((A3.rowI t).opAll i x) = g (R.jX t x)) :
    (R.toCx3 F).opC t (Sum.inl i) = Tw.map (twAt D.what₂.embLL A3.A.v0) g := by
  apply (Module.Basis.mk (hK t).1 (hK t).2.ge).ext
  intro k
  rw [Module.Basis.mk_apply, ← CxData.jR_opR _ hK]
  exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hg _)

set_option maxHeartbeats 1000000 in
theorem span_parts_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hK : (R.toCx3 F).KFormR)
    (op : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H)
    (hOpC : ∀ i, (R.toCx3 F).opC A3.A.μ0 (Sum.inl i) = Tw.map (twAt D.what₂.embLL A3.A.v0) (op i))
    (p : A3.fam3.base3.Ix) :
    Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) =
      Formalism.L2.Col.eigSum op (fun x => cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.μ0).HasRes3 p.1)
        (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i))) := by
  have hFD : FiniteDimensional D.what₂.LL (A3.fam3.amb3.FR A3.A.μ0) :=
    Module.Finite.of_basis (A3.A.fam.R A3.A.μ0).S.basis
  have hFin : Finite (Module.Basis.ofVectorSpaceIndex D.what₂.LL (A3.fam3.amb3.FR A3.A.μ0)) :=
    Module.Finite.finite_basis (CxData.bR (A := A3.fam3.amb3) A3.A.μ0)
  have hjR : ∀ i x, (R.toCx3 F).jR A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i x) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (op i) ((R.toCx3 F).jR A3.A.μ0 x) :=
    fun i x => (CxData.jR_opR _ hK _ (Sum.inl i) x).trans (LinearMap.congr_fun (hOpC i) _)
  have hspan := (GlobalTheory.span_image_eigAt_of_basis A3.fam3.base3.v0.embedding ((R.toCx3 F).jR A3.A.μ0)
    (CxData.bR (A := A3.fam3.amb3) A3.A.μ0) (A3.rowI A3.A.μ0).opAll
    (fun i => Tw.map (E := (R.HX A3.A.μ0).H) (F := (R.HX A3.A.μ0).H) (twAt D.what₂.embLL A3.A.v0) (op i))
    (hK _).1 (hK _).2 hjR).2.1 ((A3.rowI A3.A.μ0).HasRes3 p.1)
  have hTw := (GlobalTheory.TwEig.pairComm_eigSum_sub_iSup (twAt D.what₂.embLL A3.A.v0) op).2.1
    (cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.μ0).HasRes3 p.1))
  apply tw_sub_injective (twAt D.what₂.embLL A3.A.v0)
  rw [← tw_span_image, Set.image_image]
  exact hspan.trans hTw

set_option maxHeartbeats 1000000 in
theorem adj_ne_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hB : R.PThmB)
    (hPos : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0)
    (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c) (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ)
    (hc : EEc R.toRealDat R.SF c ≠ ⊥) :
    ∃ w ∈ EEc R.toRealDat R.SF c, LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hc
  have hc' : R.EEc c ≠ ⊥ := fun h0 => hc ((hEEc c).symm.trans h0)
  have hcar : R.Carries p c := by
    refine ⟨hc', ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hall v ((SetLike.ext_iff.mp (hEEc c) v).mp hv)]
    exact Submodule.zero_mem _
  exact GlobalTheory.thetaUp_injective_on_carried R F hB hPos p c hcar w ((SetLike.ext_iff.mp (hEEc c) w).mpr hw) hw0 (hall w hw)

set_option maxHeartbeats 1000000 in
theorem eep_eq (R : RealDat3 D A3 Ks) (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c) (p : A3.fam3.base3.Ix)
    (op : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H)
    (h' : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ R.HE.H) (Q : ((A3.rowI A3.A.μ0).OpIx → ℂ) → Prop)
    (hspanE : Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) =
      Formalism.L2.Col.eigSum op Q)
    (hLA : (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : EEc R.toRealDat R.SF c ≠ ⊥ ∧
      (EEc R.toRealDat R.SF c).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤ Formalism.L2.Col.eigSum op Q),
        EEc R.toRealDat R.SF c) = Formalism.L2.Col.eigSum h' Q) :
    R.EEp3 p = Formalism.L2.Col.eigSum h' Q := by
  rw [← hLA]
  unfold RealDat3.EEp3 RealDat3.Carries
  simp only [hEEc, hspanE]

set_option maxHeartbeats 1000000 in
theorem exists_core (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hLI : GlobalTheory.Chain.LiftInteg D)
    (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (hJ : InertJunk A3) (hB : R.PThmB)
    (hPos : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) : ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE := by
  obtain ⟨hCore', hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have hCore := hCore' hEx
  obtain ⟨h, hOpsE, hNE, hTop, hEig, -⟩ := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore hS R.SF hSF
  choose hX hXops hXnorm using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).1
  choose pl cX c0 hDict using GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hH R F hLI hC hEx hS hJ
  have hK : (R.toCx3 F).KFormR := RealDat3.kFormR_of hCore.models
  have hOpC : ∀ t i, (R.toCx3 F).opC t (Sum.inl i) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (hX t (pl t i) (cX t i)) :=
    fun t i => opC_eq R F hK t i _ ((hDict t).op _ (hXops t) i)
  have hSys := fun t i => _root_.GlobalTheory.Hk3.SysE.matched_commute R.toRealDat F.lv2 hCore hS R.SF hSF t (pl t i) ((hDict t).good i) (cX t i)
    (c0 t i) ((hDict t).mat i) (hX t) (hXops t)
  refine ⟨fun t i => Tw.map (E := R.HE.H) (F := R.HE.H) (twAt D.what₂.embLL A3.A.v0) (h (pl t i) (c0 t i)), ⟨?_, ?_, ?_⟩⟩
  · intro t i u
    rw [hOpC]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hSys t i).1 h hOpsE (Tw.out (s := twAt D.what₂.embLL A3.A.v0) u))
  · intro i j
    exact tw_commute _ (hNE.1 _ _ ((hDict _).good i) ((hDict _).good j) _ _)
  · intro p
    have hNX := hXnorm A3.A.μ0
    have hspanE := span_parts_eq R F hK (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i)) (hOpC A3.A.μ0) p
    have hNop : ∀ i, Commute (hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))
        (LinearMap.adjoint (hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))) := fun i => by
      have hg := (hDict A3.A.μ0).good i
      have hc := hNX.1 _ _ hg hg (cX A3.A.μ0 i) (dualC (Finsupp.mapRange star (star_zero ℂ) (cX A3.A.μ0 i)))
      rw [← hNX.2 _ hg] at hc
      exact hc
    have hNh : ∀ i, Commute (h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) (LinearMap.adjoint (h (pl A3.A.μ0 i) (c0 A3.A.μ0 i))) :=
      fun i => by
        have hg := (hDict A3.A.μ0).good i
        have hc := hNE.1 _ _ hg hg (c0 A3.A.μ0 i) (dualC (Finsupp.mapRange star (star_zero ℂ) (c0 A3.A.μ0 i)))
        rw [← hNE.2 _ hg] at hc
        exact hc
    have hPC : Formalism.L2.Col.PairComm (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i)) :=
      fun i j => hNX.1 _ _ ((hDict _).good i) ((hDict _).good j) _ _
    obtain ⟨-, hLA⟩ := _root_.GlobalTheory.Hk3.parts_of_adjoint_lift (R.Th A3.A.μ0) (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))
      (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) (fun c => EEc R.toRealDat R.SF c)
      (fun c i => evC (Yc D 0) (pl A3.A.μ0 i) (fun d => c (pl A3.A.μ0 i) (dualLab d)) (c0 A3.A.μ0 i))
      (fun i u => (hSys A3.A.μ0 i).1 h hOpsE u) hNop hNh hPC hTop
      (fun c w hw i => hEig c _ ((hDict _).good i) _ w hw) (adj_ne_zero R F hB hPos hEEc p)
    have hEEp := eep_eq R hEEc p _ (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) _ hspanE (hLA _).2
    exact (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) hEEp).trans
      ((GlobalTheory.TwEig.pairComm_eigSum_sub_iSup (twAt D.what₂.embLL A3.A.v0)
        (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i))).2.1 _).symm

theorem exists_heckeIntertwiningDefinite_of_liftInteg : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type}
    [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F →
    R.toRealDat.ExAt → InertJunk A3 → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) →
    ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE :=
  fun hH _ hCD _ _ _ _ _ _ _ _ _ _ _ _ R F hLI hC hEx hJ hB hPos =>
    exists_core hH R F hLI hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat) hJ hB hPos

end GlobalTheory.Hk3.HeckeRowsClose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.EigenSubquot

open GlobalTheory.SmGL

theorem exists_irreducible_subquotient_eigen : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 →
    (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧
        ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  intro G _ V _ _ ρ S θ x hx hθ
  let S0 : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hS0 : ∀ (g : G) ⦃v : V⦄, v ∈ S0 → ρ g v ∈ S0 := by
    intro g v hv
    have : S0 ≤ S0.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩)
    exact this hv
  have hxS0 : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hgen : ∀ R : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ R → ρ g v ∈ R) → x ∈ R → S0 ≤ R := by
    intro R hR hxR
    exact Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hR h hxR)
  let P : Set (Submodule ℂ V) := {T | T ≤ S0 ∧ x ∉ T ∧ ∀ (g : G) ⦃v : V⦄, v ∈ T → ρ g v ∈ T}
  have hbot : (⊥ : Submodule ℂ V) ∈ P := ⟨bot_le, by simpa using hx, fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun hmem => ?_, fun g v hv => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hmem
      exact (hcP hz).2.1 hxz
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcP hz).2.2 g hvz⟩) ⊥ hbot
  obtain ⟨hTS, hxT, hTst⟩ := hT.prop
  let Sr : Subrepresentation ρ := ⟨S0, hS0⟩
  let Tr : Subrepresentation ρ := ⟨T, hTst⟩
  have hcov : Tr ⋖ Sr := by
    refine ⟨lt_of_le_of_ne (fun v hv => hTS hv) fun h => hxT ?_, fun R h1 h2 => ?_⟩
    · have : x ∈ Sr := hxS0
      rw [← h] at this
      exact this
    by_cases hxR : x ∈ R.toSubmodule
    · exact h2.not_ge fun v hv => hgen R.toSubmodule R.apply_mem_toSubmodule hxR hv
    · have hRP : R.toSubmodule ∈ P := ⟨fun v hv => h2.le hv, hxR, R.apply_mem_toSubmodule⟩
      have hle : T ≤ R.toSubmodule := fun v hv => h1.le hv
      exact h1.not_ge fun v hv => hT.2 hRP hle hv
  refine ⟨_, _, _, subQuot Sr Tr, isIrreducible_subQuot hcov,
    ⟨Sr, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩,
    Submodule.Quotient.mk ⟨x, hxS0⟩, ?_, fun g hg => ?_⟩
  · intro h0
    have h1 := (Submodule.Quotient.mk_eq_zero (T.comap S0.subtype) (x := (⟨x, hxS0⟩ : S0))).1 h0
    exact hxT h1
  · show Submodule.Quotient.mk (Sr.toRepresentation g ⟨x, hxS0⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hθ g hg)

end GlobalTheory.EigenSubquot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.JacTensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def oneBlock (N : ℕ) : (Σ _ : Fin 1, Fin N) ≃ Fin N where
  toFun p := p.2
  invFun i := ⟨0, i⟩
  left_inv p := by
    obtain ⟨a, i⟩ := p
    rw [Subsingleton.elim a 0]
  right_inv _ := rfl

theorem isIrreducible_multiProd_fin_one {N : ℕ} {c : Fin 1 → ℕ} (g : (Σ i, Fin (c i)) ≃ Fin N)
    (s : ∀ i, IrrRep (GL (Fin (c i)) k)) : (multiProd g fun i => (s i).ρ).IsIrreducible := by
  obtain ⟨M, rfl⟩ : ∃ M, c = fun _ => M := ⟨c 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = fun _ => s₀ := ⟨s 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain rfl : M = N := by simpa using Fintype.card_congr g
  obtain ⟨φ₁⟩ := (Placing.parInd_jac_placing k (Fin 1) (Fin M) (fun _ => Fin M) g (oneBlock M) _).1
    (piTensor fun _ : Fin 1 => s₀.ρ)
  obtain ⟨φ₂⟩ := LocGL.nonempty_equiv_multiProd_one s₀.smooth (oneBlock M) fun _ _ => rfl
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (φ₂.trans φ₁.symm) s₀.irr

end GlobalTheory.JacTensor


open GlobalTheory.JacTensor in
theorem GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := by
  intro hGL k _ _ _ _ n π s d e Y _ _ τ hτ hs
  obtain ⟨φ⟩ := LocGL.nonempty_equiv_multiProd_one π.smooth (oneBlock n) fun _ _ => rfl
  have h1 : IsSubquotient τ (jac e (multiProd (oneBlock n) fun _ : Fin 1 => π.π)) :=
    hs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _)
      (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective))
  obtain ⟨b, f, g, t, -, ht⟩ := exists_cell_of_isSubquotient (hGL k).1 (hGL k).2
    (m' := fun a => Fin (d a)) (oneBlock n) e (fun _ => π.smooth)
    (fun _ => hasFiniteLength_of_isIrreducible π.irr) hτ h1
  exact ⟨fun a => ⟨_, multiProd (g a) fun i => (t i a).ρ, isSmooth_parInd _ _,
    isIrreducible_multiProd_fin_one (g a) fun i => t i a⟩, ht⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKillTensor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.AugmentationEigenvector

section General

variable {K X Y : Type} [Group K] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

def aug (ψ : K →* ℂˣ) : MonoidAlgebra ℂ K →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ K ((Units.coeHom ℂ).comp ψ)

theorem aug_single (ψ : K →* ℂˣ) (g : K) (r : ℂ) :
    aug ψ (MonoidAlgebra.single g r) = r * (ψ g : ℂ) := by
  simp [aug]

theorem act_eigen (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (y : X)
    (hy : ∀ g, σ g y = (ψ g : ℂ) • y) (c : MonoidAlgebra ℂ K) :
    σ.asAlgebraHom c y = aug ψ c • y := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, ha, hb, add_smul]
  | single g r => rw [aug_single, Representation.asAlgebraHom_single, LinearMap.smul_apply, hy, smul_smul]

theorem act_comm (σ : Representation ℂ K X) (τ : Representation ℂ K Y) (f : X →ₗ[ℂ] Y)
    (hf : ∀ g x, f (σ g x) = τ g (f x)) (c : MonoidAlgebra ℂ K) (x : X) :
    f (σ.asAlgebraHom c x) = τ.asAlgebraHom c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | single g r => simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hf]

theorem exists_kill [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (hσ : IsSmooth σ) (hψ : IsSmoothChar ψ)
    (h0 : ∀ z, (∀ g, σ g z = (ψ g : ℂ) • z) → z = 0) (z : X) :
    ∃ c, aug ψ c ≠ 0 ∧ σ.asAlgebraHom c z = 0 := by
  classical
  let π := twist σ ψ⁻¹
  have hπ : IsSmooth π := isSmooth_twist hσ hψ.inv
  have hlc : IsLocallyConstant fun g : K => π g z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h : {g : K | π g z = z} ∈ nhds ((fun y => x⁻¹ * y) x) :=
      IsOpen.mem_nhds (hπ z) (by simp)
    filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
    have hy' : π (x⁻¹ * y) z = z := hy
    calc π y z = π x (π (x⁻¹ * y) z) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = π x z := by rw [hy']
  have hfin := hlc.range_finite
  let O : Finset X := hfin.toFinset
  have hO : ∀ w, w ∈ O ↔ ∃ g, π g z = w := fun w => by simp [O]
  have hmem : ∀ g, ∀ w ∈ O, π g w ∈ O := fun g w hw => by
    obtain ⟨x, rfl⟩ := (hO w).1 hw
    exact (hO _).2 ⟨g * x, by rw [map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ g, π g (∑ w ∈ O, w) = ∑ w ∈ O, w := fun g => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_nbij' (fun w => π g w) (fun w => π g⁻¹ w) (hmem g) (hmem g⁻¹)
      (fun w _ => ?_) (fun w _ => ?_) (fun _ _ => rfl)
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hz : ∑ w ∈ O, w = 0 := h0 _ fun g => by
    have h1 := hinv g
    have h2 : π g (∑ w ∈ O, w) = ((ψ g)⁻¹ : ℂˣ).val • σ g (∑ w ∈ O, w) := rfl
    rw [h2] at h1
    conv_rhs => rw [← h1]
    rw [smul_smul, Units.mul_inv, one_smul]
  choose s hs using fun w : O => (hO w).1 w.2
  refine ⟨∑ w : O, MonoidAlgebra.single (s w) ((ψ (s w))⁻¹ : ℂˣ).val, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [aug_single, Units.inv_mul]
    have : O.Nonempty := ⟨z, (hO z).2 ⟨1, by simp⟩⟩
    simpa using this.ne_empty
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, ← hz, ← Finset.sum_coe_sort O]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact hs w

end General

section Tensor

variable {β : Type} [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (Γ j) (X j)) (a : β) {K : Type} [Group K]
  (i : K →* Γ a)

def viaFactor : Representation ℂ K (⨂[ℂ] j, X j) :=
  (piTensor ρ).comp ((MonoidHom.mulSingle Γ a).comp i)

theorem viaFactor_tprod (x : ∀ j, X j) (g : K) (z : X a) :
    viaFactor ρ a i g (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a (i g) z)) := by
  show piTensor ρ (Pi.mulSingle a (i g)) _ = _
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]

theorem viaFactor_alg (x : ∀ j, X j) (c : MonoidAlgebra ℂ K) (z : X a) :
    (viaFactor ρ a i).asAlgebraHom c (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ
        (Function.update x a (Representation.asAlgebraHom ((ρ a).comp i) c z)) :=
  (act_comm ((ρ a).comp i) (viaFactor ρ a i) ((PiTensorProduct.tprod ℂ).toLinearMap x a)
    (fun g z => (viaFactor_tprod ρ a i x g z).symm) c z).symm

theorem exists_kill_tensor (ψ : K →* ℂˣ)
    (h : ∀ z, ∃ c, aug ψ c ≠ 0 ∧ Representation.asAlgebraHom ((ρ a).comp i) c z = 0)
    (v : ⨂[ℂ] j, X j) (b : MonoidAlgebra ℂ K) :
    ∃ c, aug ψ c ≠ 0 ∧
      (viaFactor ρ a i).asAlgebraHom c ((viaFactor ρ a i).asAlgebraHom b v) = 0 := by
  induction v using PiTensorProduct.induction_on generalizing b with
  | smul_tprod r x =>
    obtain ⟨c, hc, hc'⟩ := h (Representation.asAlgebraHom ((ρ a).comp i) b (x a))
    refine ⟨c, hc, ?_⟩
    rw [← Function.update_eq_self a x, map_smul, map_smul, viaFactor_alg, viaFactor_alg, hc',
      MultilinearMap.map_update_zero, smul_zero]
  | add v w hv hw =>
    obtain ⟨c, hc, hc'⟩ := hv b
    obtain ⟨d, hd, hd'⟩ := hw (c * b)
    refine ⟨d * c, by rw [map_mul]; exact mul_ne_zero hd hc, ?_⟩
    rw [map_mul, Module.End.mul_apply] at hd'
    rw [map_mul, Module.End.mul_apply, map_add (f := _), map_add (f := _), hc', zero_add, hd']

end Tensor

theorem exists_eigenvector (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type)
    [(j : β) → Fintype (m j)] [(j : β) → DecidableEq (m j)] (X : β → Type)
    [(j : β) → AddCommGroup (X j)] [(j : β) → Module ℂ (X j)]
    (ρ : (j : β) → Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y)
    (hρ : ∀ j, IsSmooth (ρ j)) (hχ : IsSmoothChar χ) (hs : IsSubquotient τ (piTensor ρ))
    (hy : y ≠ 0)
    (he : ∀ g ∈ KO k (m a),
      τ (Pi.mulSingle a g) y = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • y) :
    ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a),
      ρ a g z = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • z := by
  by_contra hne
  haveI : CompactSpace (KO k (m a)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  let i := (KO k (m a)).subtype
  let ψ : KO k (m a) →* ℂˣ := χ.comp (Matrix.GeneralLinearGroup.det.comp i)
  have hψ : IsSmoothChar ψ :=
    hχ.comp _ (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  have h1 := exists_kill ((ρ a).comp i) ψ (isSmooth_comp (hρ a) i continuous_subtype_val) hψ
    fun z hz => by
      by_contra h
      exact hne ⟨z, h, fun g hg => hz ⟨g, hg⟩⟩
  obtain ⟨S, f, hf⟩ := hs
  obtain ⟨v, rfl⟩ := hf y
  obtain ⟨c, hc, hc'⟩ := exists_kill_tensor ρ a i ψ h1 v.1 1
  rw [map_one, Module.End.one_apply] at hc'
  let e : KO k (m a) →* Levi k m := (MonoidHom.mulSingle (fun j => GL (m j) k) a).comp i
  have h2 := act_comm (S.toRepresentation.comp e) (viaFactor ρ a i) S.toSubmodule.subtype
    (fun _ _ => rfl) c v
  have h3 : Representation.asAlgebraHom (S.toRepresentation.comp e) c v = 0 :=
    Subtype.ext (h2.trans hc')
  have h4 := act_comm (S.toRepresentation.comp e) (τ.comp e) f.toLinearMap
    (fun g x => f.isIntertwining _ _ (e g) x) c v
  rw [h3, map_zero, act_eigen (τ.comp e) ψ (f.toLinearMap v) (fun g => he g.1 g.2)] at h4
  exact hy ((smul_eq_zero.1 h4.symm).resolve_left hc)

end GlobalTheory.AugmentationEigenvector
end
end

