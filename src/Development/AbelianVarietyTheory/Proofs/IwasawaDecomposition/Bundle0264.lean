module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjointCompositeLiftRowMemSpanGoodRationalForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.UpKeep3

section Abstract

theorem mem_span_of_op {K : Type} [Field K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V] [Module K V] [AddCommGroup H]
    [Module ℂ H] (j : V →ₛₗ[σ] H) {ι : Type} (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (C : H →ₗ[ℂ] H) (φ : V → V) (hC : ∀ z, C (j z) = j (φ z)) (v : H) :
    C v ∈ Submodule.span ℂ (Set.range fun z => j (φ z)) := by
  have hv : v ∈ Submodule.span ℂ (Set.range fun k => j (b k)) := hsp ▸ Submodule.mem_top
  have h : Submodule.span ℂ (Set.range fun k => j (b k)) ≤ (Submodule.span ℂ (Set.range fun z => j (φ z))).comap C := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show C (j (b k)) ∈ Submodule.span ℂ (Set.range fun z => j (φ z))
    rw [hC]
    exact Submodule.subset_span ⟨b k, rfl⟩
  exact h hv

theorem sum_apply_j {K : Type} [Field K] {σ : K →+* ℂ} {G V H : Type} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [AddCommGroup H] [Module ℂ H] (j : V →ₛₗ[σ] H) (r : Representation K G V) (ρ : Representation ℂ G H)
    (hj : ∀ g z, j (r g z) = ρ g (j z)) (a : G → K) (z : V) :
    (∑ g, σ (a g) • ρ g) (j z) = j ((∑ g, a g • r g) z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]

theorem adjoint_comm {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (π : H →ₗ[ℂ] H)
    (hπ : ∀ x, ‖π x‖ = ‖x‖) (ρ : E →ₗ[ℂ] E) (hρ : ∀ y, ‖ρ y‖ = ‖y‖) (h : ∀ y, Θ (ρ y) = π (Θ y)) (x : H) :
    ρ (LinearMap.adjoint Θ x) = LinearMap.adjoint Θ (π x) := by
  have hinj : Function.Injective ρ := (injective_iff_map_eq_zero ρ).2 fun y hy => by
    rw [← norm_eq_zero, ← hρ, hy, norm_zero]
  refine ext_inner_left ℂ fun v => ?_
  obtain ⟨y, rfl⟩ := LinearMap.surjective_of_injective hinj v
  rw [(LinearMap.norm_map_iff_inner_map_map ρ).1 hρ, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, h,
    (LinearMap.norm_map_iff_inner_map_map π).1 hπ]

theorem mem_span_untwist {s : Bool} {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : ι → E) (z : E)
    (h : Tw.mk s z ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) : z ∈ Submodule.span ℂ (Set.range f) := by
  have hle : Submodule.span ℂ (Set.range fun i => Tw.mk s (f i)) ≤ Tw.sub s (Submodule.span ℂ (Set.range f)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (R := ℂ) (M := E) ⟨i, rfl⟩
  exact hle h

theorem adjoint_mem_span {K G V E H ι : Type} [Field K] {σ : K →+* ℂ} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (j : V →ₛₗ[σ] E) (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (r : Representation K G V)
    (π : Representation ℂ G H) (hπ : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (Θ : E →ₗ[ℂ] H)
    (hρ : ∃ ρ : Representation ℂ G E, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧ ∀ g y, Θ (ρ g y) = π g (Θ y))
    (a l : G → K) (u : H) (ha : ∑ g, σ (a g) • π g u = u) (hl : ∑ g, σ (l g) • π g u = u) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range fun z => j ((∑ g, a g • r g) ((∑ g, l g • r g) z))) := by
  obtain ⟨ρ, hj, hn, hΘ⟩ := hρ
  have e1 : ∀ g, ρ g (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ (π g u) := fun g =>
    adjoint_comm Θ (π g) ((LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπ g)) (ρ g) (hn g) (hΘ g) u
  have fix : ∀ c : G → K, ∑ g, σ (c g) • π g u = u →
      (∑ g, σ (c g) • ρ g) (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u := fun c hc => by
    conv_rhs => rw [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, e1, map_sum, map_smul]
  have h := mem_span_of_op j b hsp ((∑ g, σ (a g) • ρ g) ∘ₗ (∑ g, σ (l g) • ρ g))
    (fun z => (∑ g, a g • r g) ((∑ g, l g • r g) z))
    (fun z => by rw [LinearMap.comp_apply, sum_apply_j j r ρ hj, sum_apply_j j r ρ hj]) (LinearMap.adjoint Θ u)
  rwa [LinearMap.comp_apply, fix l hl, fix a ha] at h

theorem untwist_adjoint {s : Bool} {E H ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (u : H) (f : ι → E) (f' : κ → E)
    (hf : ∀ i, ∃ k, f i = f' k)
    (h : LinearMap.adjoint (Tw.map s Θ) (Tw.mk s u) ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range f') := by
  rw [Tw.adjoint_map] at h
  refine Submodule.span_mono ?_ (mem_span_untwist (s := s) f _ h)
  rintro _ ⟨i, rfl⟩
  exact (hf i).elim fun k hk => ⟨k, hk.symm⟩

theorem exists_lvl_coord {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (z : S.Forms) :
    ∃ x, S.gaOp r (lvlIdem P ψ) z = S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) := by
  obtain ⟨w, rfl⟩ := S.basis.equivFun.symm.surjective z
  have h : S.gaMat r (lvlIdem P ψ) *ᵥ w ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
    rw [(image_idempotent_spec K _ _).2]
    exact ⟨w, rfl⟩
  obtain ⟨x, hx⟩ := h
  exact ⟨x, (GlobalTheory.Mem.LiftForms.gaOp_coord S r _ w).trans (congrArg _ hx.symm)⟩

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

theorem exists_rowForm {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ} (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (t : T) (z : (A.MtildeCSD t).Forms) :
    ∃ x, (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (lvlIdem P ψ) z) =
      rowForm A P ψ t ((rE D A P ψ t).mulVec x) :=
  (exists_lvl_coord (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ z).elim fun x hx =>
    ⟨x, (congrArg ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X)) hx).trans (GoodProj.rowForm_rE ok P ψ t x).symm⟩

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_lvl_fix (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (u : (R.toCx3 F).EE) (hu : u ∈ (R.toCx3 F).EEl true) :
    ∑ g, A3.A.fam.v0.embedding ((lvlIdem F.P1 F.ψ1).coeff g) • R.gEx F g u = u := by
  rw [(GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC).2] at hu
  refine GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) F.P1 F.ψ1 fun h => ?_
  have := (Submodule.mem_iInf _).1 hu h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem adjoint_mem_tw (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (u : (R.toCx3 F).EE)
    (hu : u ∈ (R.toCx3 F).EEl true) :
    LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u ∈ Submodule.span ℂ (Set.range fun z => (R.toCx3 F).jR A3.A.fam.μ0
      ((∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g)
        ((∑ g, (lvlIdem F.P1 F.ψ1).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g) z))) :=
  adjoint_mem_span (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (E := (R.toCx3 F).FC A3.A.fam.μ0) ((R.toCx3 F).jR A3.A.fam.μ0)
    (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (RealDat3.kFormR_of (F := F) hC.base.models A3.A.fam.μ0).2
    (A3.A.fam.R A3.A.fam.μ0).r (R.gEx F) hH.prim.gUnit.1 ((R.toCx3 F).Θ A3.A.fam.μ0)
    (GlobalTheory.RowsPosRed.exists_rho R F (s := 1) hH.ok hC.base.models hH.prim.gEquiv)
    (fun g => (idemOf A3.A.X).coeff g) (fun g => (lvlIdem F.P1 F.ψ1).coeff g) u
    (GlobalTheory.RowsPosRed.sum_idem_gEx R F (GlobalTheory.CoreOfWeak.core_of_weak R F hC hH.aux.ex).1 u) (sum_lvl_fix R F hC u hu)

theorem adjoint_mem_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (w : R.HE.H)
    (hw : R.HE.e w ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) :
    LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (Set.range fun x =>
      R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) :=
  untwist_adjoint (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.μ0) w
    (fun z => R.jX A3.A.μ0 ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (idemOf A3.A.X)
      ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (lvlIdem F.P1 F.ψ1) z))) _
    (fun z => (exists_rowForm hH.ok.ok2 F.P1 F.ψ1 A3.A.μ0 z).elim fun x hx => ⟨x, congrArg (R.jX A3.A.μ0) hx⟩)
    (adjoint_mem_tw R F hC hH (Tw.mk (twAt D.what₂.embLL A3.A.v0) w) hw)

end GlobalTheory.UpKeep3

namespace GlobalTheory.UpKeep3

theorem adjoint_mem_span_rowForm : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ y, LinearMap.adjoint (R.Th A3.A.μ0) (uE y) ∈ Submodule.span ℂ (Set.range fun x => R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) := by
  intro _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH uE hread y
  have hrow : R.HE.e (uE y) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := by
    have h1 := (Y.Ish.jE y).2
    rw [hread y] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    have e : m = R.HE.e (uE y) := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).injective hm'
    rw [← e]
    exact hm
  exact adjoint_mem_of_row R F hP.char hH (uE y) hrow

end GlobalTheory.UpKeep3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts
open scoped ContDiff ENNReal

namespace GlobalTheory.ChernTransfer

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
  {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D : ℕ} {j : Y ⟶ X} {Φ : CxPts q σ' ≃ₜ CxPts p σ}
  (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j) {B : LB X} {φ : Weight p σ B}

abbrev pullW (φ : Weight p σ B) : Weight q σ' (LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1) :=
  φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)

theorem pullW_φ (i : PUnit → B.ι) (z : CxPts q σ') :
    (pullW hΦ φ).φ i z = φ.φ (i PUnit.unit) (Φ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * φ.φ (i a) (Φ z)).trans (by simp)


include hΦ in
theorem ev_app' (W : X.Opens) (g : Γ(X, W)) (z : CxPts q σ') :
    ev q σ' (j ⁻¹ᵁ W) (j.app W g) z = ev p σ W g (Φ z) := by
  rw [ev, ev, hΦ]
  exact (valR_comp z.1 j W g).symm


include hΦ in
theorem mem_preimage_iff (W : X.Opens) (z : CxPts q σ') :
    z ∈ ptsIn q σ' (j ⁻¹ᵁ W) ↔ Φ z ∈ ptsIn p σ W := by
  change _ ↔ ⊤ ≤ (Φ z).1 ⁻¹ᵁ W
  rw [hΦ]
  rfl

theorem isCInf_pullW (h : φ.IsCInf) : (pullW hΦ φ).IsCInf := fun i z hz => by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h _ _
    (mem_of_mem_linComb (m := fun _ => Φ z) (fun _ => hΦ z) hz PUnit.unit)
  refine ⟨j ⁻¹ᵁ W, ι, inferInstance, fun a => j.app W (g a), F, O, (mem_preimage_iff hΦ W z).2 h₁,
    h₂, ?_, h₄, ?_⟩
  · simpa only [ev_app' hΦ] using h₃
  · simp only [ev_app' hΦ]
    filter_upwards [Φ.continuous.continuousAt.eventually h₅] with w hw
    exact (pullW_φ hΦ i w).trans hw


include hΦ in
theorem holo_trans (c : AlgChart p σ D) (c' : AlgChart q σ' D) :
    DifferentiableOn ℂ (Φ.transOpenPartialHomeomorph c.e ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (j.app c.U (c.x a))).mono fun _ (hv : _ ∈ c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) =>
    ⟨hv.1, (mem_preimage_iff hΦ _ _).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_app' hΦ _ _ _).symm

theorem chernDens_pullW (h : φ.IsCInf) (c : AlgChart p σ D) (c' : AlgChart q σ' D)
    {z : CxPts q σ'} (hz : z ∈ c'.e.source) (hz' : Φ z ∈ c.e.source) :
    c'.chernDens (pullW hΦ φ) z =
      ‖transDet c'.e (Φ.transOpenPartialHomeomorph c.e) z‖ ^ 2 * c.chernDens φ (Φ z) := by
  set e := Φ.transOpenPartialHomeomorph c.e with he
  have ho := isOpen_over c'.e e.open_source
  have hm := mem_over c'.e hz (S := e.source) hz'
  have hi : z ∈ ptsIn q σ' ((LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1).U
      fun _ => pick φ.isLB (Φ z)) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx)
      ((mem_preimage_iff hΦ _ z).2 (mem_pick φ.isLB (Φ z)))
  have e₁ : (fun v => ((pullW hΦ φ).φ (fun _ => pick φ.isLB (Φ z)) (c'.e.symm v) : ℂ))
      =ᶠ[𝓝 (c'.e z)] (fun v => (φ.φ (pick φ.isLB (Φ z)) (c.e.symm v) : ℂ)) ∘ e ∘ c'.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      have : c.e.symm (e (c'.e.symm v)) = Φ (c'.e.symm v) := c.e.left_inv hv.2
      simp only [Function.comp_apply, this, pullW_φ]
  have e₂ : (e ∘ c'.e.symm) (c'.e z) = c.e (Φ z) := congrArg e (c'.e.left_inv hz)
  rw [c'.chernDens_eq (isCInf_pullW hΦ h) hz hi, AlgChart.chernDens]
  have e₃ : c'.hess (pullW hΦ φ) (fun _ => pick φ.isLB (Φ z)) z = _ :=
    ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e₁
  rw [e₃, AlgChart.hess,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (holo_trans hΦ c c') (e₂ ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.contDiffAt c hz' (mem_pick _ _))), e₂,
    Complex.re_ofReal_mul, transDet]
  ring

variable [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')]

theorem chernPart_pullW (R : AnRead p σ D) (R' : AnRead q σ' D) (h : φ.IsCInf) (ε : ℤˣ) :
    (pullW hΦ φ).chernPart D ε = (φ.chernPart D ε).map Φ.symm.toMeasurableEquiv := by
  refine ext_of_cover (fun a : R.ι × R'.ι => (R'.chart a.2).e.source ∩
    (Φ.transOpenPartialHomeomorph (R.chart a.1).e).source)
    (fun a => (R'.chart a.2).e.open_source.inter (OpenPartialHomeomorph.open_source _))
    (fun z => ?_) fun a A hA hs => ?_
  · obtain ⟨a, ha⟩ := R.cover (Φ z)
    obtain ⟨b, hb⟩ := R'.cover z
    exact ⟨(a, b), hb, ha⟩
  set c := R.chart a.1
  set c' := R'.chart a.2
  have h₁ : A ⊆ c'.e.source := hs.trans inter_subset_left
  have h₂ : A ⊆ (Φ.transOpenPartialHomeomorph c.e).source := hs.trans inter_subset_right
  have hA' : MeasurableSet (Φ.symm.toMeasurableEquiv ⁻¹' A) := Φ.symm.toMeasurableEquiv.measurable hA
  have h₃ : Φ.symm.toMeasurableEquiv ⁻¹' A ⊆ c.e.source := fun y hy => by
    have : Φ (Φ.symm y) ∈ c.e.source := h₂ hy
    rwa [Φ.apply_symm_apply] at this
  rw [MeasurableEquiv.map_apply, Weight.chernPart_apply (isCInf_pullW hΦ h) ε c' hA h₁,
    Weight.chernPart_apply h ε c hA' h₃,
    ← chartMeas_apply_of_subset c'.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * c'.chernDens (pullW hΦ φ) y)) hA h₁,
    chartMeas_eq c'.e (Φ.transOpenPartialHomeomorph c.e)
      (ρ' := fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (Φ y))) (holo_trans hΦ c c') hA h₁ h₂
      (fun y hy => by
        rw [chernDens_pullW hΦ h c c' (h₁ hy) (h₂ hy), mul_left_comm,
          ENNReal.ofReal_mul (sq_nonneg _)]),
    chartMeas_apply_of_subset _ _ hA h₂]
  have him : Φ.transOpenPartialHomeomorph c.e '' A = c.e '' (Φ.symm.toMeasurableEquiv ⁻¹' A) := by
    rw [show Φ.symm.toMeasurableEquiv ⁻¹' A = Φ '' A from (Φ.image_eq_preimage_symm A).symm,
      image_image]
    rfl
  rw [him]
  refine lintegral_congr fun v => ?_
  rw [show Φ ((Φ.transOpenPartialHomeomorph c.e).symm v) = c.e.symm v from Φ.apply_symm_apply _]

end GlobalTheory.ChernTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardBaseRowsLabelEqRowsPartFinrank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCount

theorem card_filter_eq_finrank {V Q ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Fintype ι] [Fintype Q] [DecidableEq Q] (x : ι → V) (hx : LinearIndependent ℂ x) (lab : ι → Q)
    (P : Q → Submodule ℂ V) (hmem : ∀ k, x k ∈ P (lab k))
    (hsum : ∑ q, Module.finrank ℂ (P q) ≤ Fintype.card ι) (p : Q) :
    (Finset.univ.filter (fun k => lab k = p)).card = Module.finrank ℂ (P p) := by
  have hle : ∀ q, (Finset.univ.filter (fun k => lab k = q)).card ≤ Module.finrank ℂ (P q) := by
    intro q
    let y : {k // lab k = q} → P q := fun k => ⟨x k.1, by have h := hmem k.1; rwa [k.2] at h⟩
    have hy : LinearIndependent ℂ y := by
      apply LinearIndependent.of_comp (P q).subtype
      exact hx.comp Subtype.val Subtype.val_injective
    have := hy.fintype_card_le_finrank
    rwa [Fintype.card_subtype] at this
  have htot : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card = Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (lab k))]
  by_contra hne
  have hlt : (Finset.univ.filter (fun k => lab k = p)).card < Module.finrank ℂ (P p) := lt_of_le_of_ne (hle p) hne
  have : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card < ∑ q, Module.finrank ℂ (P q) :=
    Finset.sum_lt_sum (fun q _ => hle q) ⟨p, Finset.mem_univ _, hlt⟩
  omega

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : (Tw.sub s V) ≃+ V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      invFun := fun x => ⟨Tw.mk s x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hb : Function.Bijective (cj s) :=
    Function.bijective_iff_has_inverse.2 ⟨cj s, cj_cj s, cj_cj s⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hb (fun _ _ => rfl)
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := Submodule.ext fun _ => Iff.rfl

theorem cnt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ cOf : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, HasLab Y σ (cOf σ)) → ∀ p : A3.fam3.base3.Ix, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost cOf hLab p
  have hR := complex_data_conditions_base_level_of_primitive_links hHo.ok hHo.sep hP.char hHo.prim
  have hRow := hR.rowHyp false
  have hE : (R.toCx3 F).PartsE false := hHo.prim.sumE false
  have hinj : Function.Injective R.HE.e := hP.char.base.models.HE.1
  set L : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e with hL
  have hpart : ∀ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) =
      Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) := by
    intro q
    rw [← finrank_twSub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H), twSub_inf]
    rfl
  have hEp : Module.finrank D.what₂.LL ((s0Of R F).Ep p) = Module.finrank ℂ (R.EEp3 p ⊓ L : Submodule ℂ R.HE.H) := by
    rw [← hpart p]
    exact (R.toCx3 F).finrank_Ep F.cr false hRow.wf hRow.h2 hRow.h3 hE p
  let C := toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop
  let lf : Mult.MMap (R.MY 0) ≃ₗ[ℂ] C.Amb 0 := PiTensorProduct.lift
  let φ : R.HE.H →ₗ[ℂ] C.Amb 0 := lf.toLinearMap ∘ₗ R.HE.e
  have hφ : Function.Injective φ := lf.injective.comp hinj
  have hmemL : ∀ y : R.HE.H, φ y ∈ C.EEc false → y ∈ L := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy
    have : z = R.HE.e y := lf.injective hzy
    subst this
    exact hz
  choose x hxP hxe using fun k => (hLab (D.what₂.ft0 k)).2 k rfl
  have hxφ : ∀ k, φ (x k) = (Y.Iz.jE (D.what₂.onb0 k)).1 := fun k => (hxe k).symm
  have hli0 : LinearIndependent ℂ (fun k => ((Y.Iz.jE (D.what₂.onb0 k)).1 : C.Amb 0)) := by
    have h1 := D.what₂.onb0.toBasis.linearIndependent.map' Y.Iz.jE.toLinearMap Y.Iz.jE.ker
    have h2 := h1.map' (C.EEc false).subtype (Submodule.ker_subtype _)
    exact h2
  have hli : LinearIndependent ℂ x := by
    apply LinearIndependent.of_comp φ
    convert hli0 using 1
    funext k
    exact hxφ k
  have hxL : ∀ k, x k ∈ L := fun k => hmemL _ (by rw [hxφ k]; exact (Y.Iz.jE (D.what₂.onb0 k)).2)

  have hDim : Module.finrank ℂ L ≤ Fintype.card (Fin D.what₂.D0) := by
    let g0 : L →ₗ[ℂ] C.EEc false :=
      (φ.domRestrict L).codRestrict (C.EEc false) (fun y => Submodule.mem_map_of_mem (f := lf.toLinearMap) y.2)
    let g : L →ₗ[ℂ] D.what₂.EE0 := Y.Iz.jE.symm.toLinearMap ∘ₗ g0
    have hg : Function.Injective g := by
      intro a b h
      have h1 : g0 a = g0 b := Y.Iz.jE.symm.injective h
      have h2 : φ a = φ b := congrArg Subtype.val h1
      exact Subtype.ext (hφ h2)
    calc Module.finrank ℂ L ≤ Module.finrank ℂ D.what₂.EE0 := LinearMap.finrank_le_finrank_of_injective hg
      _ = Fintype.card (Fin D.what₂.D0) := Module.finrank_eq_card_basis D.what₂.onb0.toBasis
  have hsum : ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) ≤ Fintype.card (Fin D.what₂.D0) := by
    calc ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H)
        = ∑ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          Finset.sum_congr rfl fun q _ => (hpart q).symm
      _ = Module.finrank ℂ (⨆ q, (R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          (Formalism.IndefR.Cx.finrank_iSup_eq_sum _ (CxData.indep_of_orth _ hE.1)).symm
      _ ≤ Module.finrank ℂ ((R.toCx3 F).EEl false) := Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = Module.finrank ℂ L := finrank_twSub _ L
      _ ≤ Fintype.card (Fin D.what₂.D0) := hDim
  have hcard := card_filter_eq_finrank x hli (fun k => cOf (D.what₂.ft0 k)) (fun q => (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H))
    (fun k => ⟨hxP k, hxL k⟩) hsum p
  have hcount : ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ =
      (Finset.univ.filter (fun k => cOf (D.what₂.ft0 k) = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := D.what₂.ft0) (t := Finset.univ.filter (fun σ => cOf σ = p))
      (fun k hk => by simpa using hk)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [Formalism.BasicNotions.Rows.Data.nRows0, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hσ.2, h⟩
    · intro h; exact h.2
  rw [hEp, ← hcard]
  exact hcount

end GlobalTheory.Mem.R3.LabCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommon
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.Cartier.CommonEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add {D : CartierDiv X} {x : X} {f f' : X.functionField}
    (h : D.GeneratesAt x f) (h' : D.VanishesAt x f') : D.GeneratesAt x (f + f') := by
  obtain ⟨g, hg, a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := hg.vanishesAt_iff.1 h'
  refine ⟨g, hg, a + b, ?_, by rw [map_add (f := _), e, e', add_mul]⟩
  by_contra hu
  have : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact (show a ∈ IsLocalRing.maximalIdeal _ from by simpa using sub_mem this hb) ha

end GlobalTheory.Cartier.CommonEqn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpenStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ), (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y), 0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) → chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  first | exact @GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | exact GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | (intros; apply GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ArInt

theorem isometric_comb_unit_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L : HermLB p) (m : ℕ), (ArInt.comb (fun _ : Unit => L) (fun _ => (m : ℤ))).Isometric (L.pow m) := by
  intro k _ X _ p L m
  rw [← HermLB.icls_eq_iff, icls_comb, HermLB.icls_pow]
  simp

end GlobalTheory.ArInt
end

