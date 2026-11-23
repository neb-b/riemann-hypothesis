module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0014
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Formalism.LocalToGlobal.LatticeGeometry.FormsK
public import Formalism.LocalRingCardinality.Bundle0005

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

namespace Tw

variable {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem adjoint_map [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (Tw.map s f) = Tw.map s (LinearMap.adjoint f) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  show cj s (inner ℂ (LinearMap.adjoint f (out x)) (out y)) = cj s (inner ℂ (out x) (f (out y)))
  rw [LinearMap.adjoint_inner_left]

theorem linInd' (s : Bool) {ι : Type} {v : ι → E} (h : LinearIndependent ℂ v) :
    LinearIndependent ℂ fun i => mk s (v i) := by
  rw [linearIndependent_iff'] at h ⊢
  intro u g hg i hi
  have h1 : ∑ i ∈ u, cj s (g i) • v i = 0 := hg
  have := congrArg (cj s) (h u (fun i => cj s (g i)) h1 i hi)
  rwa [cj_cj, map_zero] at this

theorem mk_smul (s : Bool) (c : ℂ) (y : E) : mk s (c • y) = cj s c • mk s y := by
  show c • y = cj s (cj s c) • y
  rw [cj_cj]

theorem span_top' (s : Bool) {ι : Type} {v : ι → E} (h : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  change mk s (out x) ∈ _
  generalize out x = y at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [mk_smul]
    exact Submodule.smul_mem _ _ hy

end Tw

section Semi

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem span_semi (f : V →ₛₗ[σ] W) {κ : Type} (c : Module.Basis κ K V) :
    Submodule.span ℂ (Set.range fun i => f (c i)) = Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨c i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span K (Set.range c) := c.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem linInd_semi (f : V →ₛₗ[σ] W) {ι ι' : Type} [Finite ι] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V)
    (h : LinearIndependent ℂ fun i => f (b i)) : LinearIndependent ℂ fun i => f (b' i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have : Finite ι' := Module.Finite.finite_basis b'
  have : Fintype ι' := Fintype.ofFinite ι'
  rw [linearIndependent_iff_card_eq_finrank_span] at h ⊢
  unfold Set.finrank at h ⊢
  rw [span_semi f b']
  rw [span_semi f b] at h
  rw [← h]
  exact (Module.finrank_eq_card_basis b').symm.trans (Module.finrank_eq_card_basis b)

theorem kForm_semi {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (g : V →ₛₗ[σ] H)
    (e : H →ₗ[ℂ] X) (f : V →ₛₗ[σ] X) (hj : ∀ x, e (g x) = f x) (hinj : Function.Injective e)
    (hrange : LinearMap.range e = Submodule.span ℂ (Set.range f)) {ι ι' : Type} [Finite ι] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V)
    (h : LinearIndependent ℂ fun i => f (b i)) :
    LinearIndependent ℂ (fun i => g (b' i)) ∧ Submodule.span ℂ (Set.range fun i => g (b' i)) = ⊤ := by
  refine ⟨LinearIndependent.of_comp e ?_, ?_⟩
  · have e1 : (e ∘ fun i => g (b' i)) = fun i => f (b' i) := funext fun i => hj _
    rw [e1]
    exact linInd_semi f b b' h
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, hrange]
    have e1 : (e ∘ fun i => g (b' i)) = fun i => f (b' i) := funext fun i => hj _
    rw [e1, span_semi f b']

end Semi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Links

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

set_option maxHeartbeats 1000000 in
theorem kFormR_of (hM : R.IsModels) : (R.toCx F).KFormR := by
  intro t
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX t
  have h := kForm_semi (R.jX t) (R.HX t).e (R.B.R t).pres.extL (fun x => hM.jX t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact ⟨Tw.linInd' (E := (R.HX t).H) _ h.1, Tw.span_top' (E := (R.HX t).H) _ h.2⟩

set_option maxHeartbeats 1000000 in
theorem kFormL_of (hM : R.IsModels) : (R.toCx F).KFormL := by
  intro i t
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L i t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HV i t
  have h := kForm_semi (R.jV i t) (R.HV i t).e (R.B.L i t).pres.extL (fun x => hM.jV i t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact ⟨Tw.linInd' (E := (R.HV i t).H) _ h.1, Tw.span_top' (E := (R.HV i t).H) _ h.2⟩


set_option maxHeartbeats 1000000 in
theorem jIsoR_gen (hM : R.IsModels) (cv : CrdV A.fam.amb)
    (hcv : ∀ t x y, cv.hR t x y = (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) :
    (R.toCx F).JIsoR cv := by
  intro t x y
  have key : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
    rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
    congr 1
    exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y
  rw [hcv]
  exact key

theorem jIsoR_of (hM : R.IsModels) : (R.toCx F).JIsoR (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) :=
  jIsoR_gen hM _ fun _ _ _ => rfl


set_option maxHeartbeats 1000000 in
theorem jIsoL_gen (hM : R.IsModels) (cv : CrdV A.fam.amb)
    (hcv : ∀ i t x y, cv.hL i t x y = (A.fam.L i t).S.csum ((x : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V) ((y : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V)) :
    (R.toCx F).JIsoL cv := by
  intro i t x y
  have key : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jV i t x) (R.jV i t y)) =
      A.v0.embedding ((A.fam.L i t).S.csum ((x : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V) ((y : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V)) := by
    rw [(hM.HV i t).2.2, hM.jV, hM.jV, R.emb0]
    congr 1
    exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.L i t).pres x y
  rw [hcv]
  exact key

theorem jIsoL_of (hM : R.IsModels) : (R.toCx F).JIsoL (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) :=
  jIsoL_gen hM _ fun _ _ _ _ => rfl



end RealDat

end Links

section Prim

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

abbrev cv : CrdV A.fam.amb := cvOf A F.P0 F.ψ0 F.P1 F.ψ1

def PThmA : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp i) fun p => R.lam i t p A.v0

def PConj : Prop := ∀ i, (R.FW i).GalA

variable {R F}

end RealDat


end Prim

section Geo

open Formalism.L2.Geo Formalism.MainNotions

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Gm : DV.Geo D.what₂.LL} {Lv : Type} {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL]

end Geo

section Exist

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx


variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

end RealDat


end Exist

section Host


variable (D) in
structure HostHyp : Prop where
  interlace : (Ptw D).Interlace
  gap : ∀ (τ : D.what₂.Tau) (j : Fin D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).e j - (D.hc τ).b j ∧
    ∀ h : (j : ℕ) + 1 < D.R.m, ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨(j : ℕ) + 1, h⟩ - (D.hc τ).e j
  gapR : ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)
  cloudGap : ∀ τ : D.what₂.Tau, 100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 2) - Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 1)
  nodeGap : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)
  nodeGapR : D.NodeGap (256 * (D.R.r : ℝ) ^ 4)


end Host

end Formalism.IndefR.Links

end
