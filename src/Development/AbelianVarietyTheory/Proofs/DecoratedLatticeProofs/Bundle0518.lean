module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeq
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

noncomputable section

namespace GlobalTheory.TopVal.OneForm

section Generic

variable {D : D7} {O : Obj D} {c : ℝ}


end Generic

section Rows

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl


set_option maxHeartbeats 800000 in
theorem row_of_pack {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (x : R3.TwIn ex)
    {G : Type} [g : Group G] [fi : Fintype G] {Pl0 I0 T0 : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m)
    {C : Formalism.L2.Pj.CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) = ⟨G, g, fi, Pl0, I0, T0, A3, C, al, R, F, cG⟩)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (hP : F.P1 = P) (hψ : HEq F.ψ1 ψ)
    (τ : T0 → D.what₂.Tup) (j : ∀ s, (Fin (rDim D A3.A P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (τ s))
    (hτ : HEq x.Y.tup τ) (hj : HEq x.Y.jA j) (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL) :
    ∃ (s' : T0) (v' : Fin (rDim D A3.A P ψ s') → D.what₂.LL), x.Y.tup s = τ s' ∧
      HEq (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) (R3.rowForm A3.A P ψ s' v') ∧ HEq (x.Y.jA s v) (j s' v') := by
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  subst hP
  cases hψ
  cases hτ
  cases hj
  exact ⟨s, v, rfl, HEq.rfl, HEq.rfl⟩


set_option maxHeartbeats 800000 in
theorem row_of_args {K : Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : R3.TwArgs ex t) (s : a.x.T)
    (v : Fin (rDim (w.st Z).toD7 a.x.A3.A a.x.F.P1 a.x.F.ψ1 s) → (w.st Z).toD7.what₂.LL) :
    ∃ (s' : R3.TupU w.I (R3.usedOf w.I T Wt))
      (v' : Fin (rDim (w.st Z).toD7 (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s') → (w.st Z).toD7.what₂.LL),
      a.x.Y.tup s = t.r.Y.tup s' ∧
      HEq (R3.rowForm a.x.A3.A a.x.F.P1 a.x.F.ψ1 s v) (R3.rowForm (D := (w.st Z).toD7) (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s' v') ∧
      HEq (a.x.Y.jA s v) (t.r.Y.jA s' v') :=
  row_of_pack a.x (R3.famT t) a.pack (R3.lev1 w.I) (R3.chr1 w.I) rfl HEq.rfl t.r.Y.tup t.r.Y.jA a.tup a.jA s v


set_option maxHeartbeats 800000 in
theorem rowForm_all (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr : R3.TrI X.B px) (s : R3.TupU I U) (a : I.ι) (h : s.1 = I.tup a)
    (v : Fin (rDim X.toD7 (R3.famR X I hX U Xg tr).A (R3.lev1 I) (R3.chr1 I) s) → X.toD7.what₂.LL) :
    ∃ v' : Fin (rDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a)) → X.toD7.what₂.LL,
      (∀ i i', Fin.val i = Fin.val i' → v' i = v i') ∧
      HEq (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) v')
        (R3.rowForm (D := X.toD7) (R3.famR X I hX U Xg tr).A (R3.lev1 I) (R3.chr1 I) s v) := by
  obtain ⟨τ, hτ⟩ := s
  dsimp only at h
  subst h
  exact ⟨v, fun i i' e => congrArg v (Fin.ext e), HEq.rfl⟩


set_option maxHeartbeats 800000 in
theorem one_form_rows {K : Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (rx : RXs t) (s : R3.TupU w.I (R3.usedOf w.I T Wt))
    (v : Fin (rDim (w.st Z).toD7 (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s) → (w.st Z).toD7.what₂.LL) :
    ∃ φ : Frm w.I (t.r.Y.tup s),
      IsRes φ (R3.rowForm (D := (w.st Z).toD7) (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s v) ∧
      ∀ u, RecVal (I := w.I) (l := w.l) (Z := Z) u (t.r.Y.tup s) φ (t.r.Y.jA s v) := by
  have hs : s.1 = w.I.tup (t.r.Y.tup s) :=
    (R3.tup_ixOf w.I s).symm.trans (congrArg w.I.tup (t.r.tup_ix s)).symm
  obtain ⟨v', hv, hf⟩ := rowForm_all (w.st Z) w.I t.hX _ t.r.z.Xg t.r.z.tr s (t.r.Y.tup s) hs v
  have hj : rx.all.jA (t.r.Y.tup s) v' = t.r.Y.jA s v := (rx.jA_use s).2 v' v hv
  obtain ⟨x, ⟨φ, hφ, hres, hx⟩, he⟩ := rx.crd (t.r.Y.tup s) v'
  subst hx
  refine ⟨φ, ⟨_, hres.trans hf⟩, fun u => ?_⟩
  rw [← hj, he]
  have key : ∀ (a : w.C.Tup) (φ : Frm w.I a) hφ,
      RecVal (I := w.I) (l := w.l) (Z := Z) u a φ (rx.e a (Df.toCx w.I t.hX a ⟨φ.1, hφ⟩)) := by
    intro a φ hφ
    refine ⟨fun h => ?_, fun p => rx.eMtTw u a _ p⟩
    subst h
    exact fun p => rx.eMt0 u _ p
  exact key _ φ hφ

end Rows

theorem one_form_congr {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {a a' : (I.rec7 l Z).what₂.Tup} {V V' : Type} {x : V} {x' : V'} {G : (I.rec7 l Z).what₂.Amb a} {G' : (I.rec7 l Z).what₂.Amb a'}
    (ha : a = a') (hx : HEq x x') (hG : HEq G G') (h : ∃ φ : Frm I a', IsRes φ x' ∧ ∀ u, RecVal u a' φ G') :
    ∃ φ : Frm I a, IsRes φ x ∧ ∀ u, RecVal u a φ G := by
  subst ha
  cases hx
  cases hG
  exact h



end GlobalTheory.TopVal.OneForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemma
section
noncomputable section

namespace GlobalTheory.TopVal.Scalar

section Alg

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Matrix GlobalTheory.CoefSpace

theorem schur {G W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (ρ : G → Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) (T : Module.End ℂ W)
    (hT : ∀ h w, T (ρ h w) = ρ h (T w)) : ∃ a : ℂ, ∀ w, T w = a • w := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
  refine ⟨a, fun w => ?_⟩
  have h := (hirr (T.eigenspace a) fun h => ?_).resolve_left ha
  · exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)
  · rintro _ ⟨x, hx, rfl⟩
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [hT, Module.End.mem_eigenspace_iff.1 hx, map_smul]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem exists_ext {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (c : VV K lam →ₛₗ[σ] W) : ∃ c' : VV ℂ lam →ₗ[ℂ] W, ∀ w, c' (bcVV σ lam w) = c w := by
  let b := Module.Basis.mk (bcVV_indep σ lam) (bcVV_span σ lam).ge
  refine ⟨b.constr ℂ fun i => c (bVV K lam i), fun w => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (bVV K lam).sum_repr w, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : bcVV σ lam (bVV K lam i) = b i := (Module.Basis.mk_apply (bcVV_indep σ lam) (bcVV_span σ lam).ge i).symm
  rw [map_smulₛₗ (bcVV σ lam), map_smul, e, Module.Basis.constr_basis, map_smulₛₗ c]

theorem ext_bc {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    {f g : VV ℂ lam →ₗ[ℂ] W} (h : ∀ w, f (bcVV σ lam w) = g (bcVV σ lam w)) : f = g :=
  LinearMap.ext_on_range (bcVV_span σ lam) fun _ => h _

theorem fnOf_actP (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n)
    (y y' : Frames G) (h : ∀ τ, y'.1 τ = (g τ : Matrix (Fin n) (Fin n) ℂ)ᵀ * y.1 τ) :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e := Formalism.L2.Col.evFr_actP G (RingHom.id ℂ) lam g P
  rw [Formalism.L2.Col.evFr_eq_fnOf] at e
  simp only [MvPolynomial.map_id] at e
  rw [e]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, h]
  rfl

theorem exists_equiv (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Frames G → ℂ))
    (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam) :
    ∃ φ : V ≃ₗ[ℂ] VV ℂ lam, ∀ v, j v = fnOf G (shiftOf lam) 1 (φ v).1 := by
  have hf : Function.Injective (fnOf G (shiftOf lam) 1) :=
    Formalism.L2.Col.fnOf_injective G _ 1 (fun τ => by simp) ⟨fun _ => 1, fun τ => by simp⟩
  have hr' : LinearMap.range j = (VV ℂ lam).map (fnOf G (shiftOf lam) 1) := by
    rw [hr, ValC, GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
  refine ⟨(LinearEquiv.ofInjective j hinj).trans ((LinearEquiv.ofEq _ _ hr').trans
    (Submodule.equivMapOfInjective _ hf (VV ℂ lam)).symm), fun v => ?_⟩
  exact (congrArg Subtype.val ((Submodule.equivMapOfInjective _ hf (VV ℂ lam)).apply_symm_apply
    (LinearEquiv.ofEq _ _ hr' (LinearEquiv.ofInjective j hinj v)))).symm

end Alg

section Group

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}

theorem infGL_fin {h : GA D V} (hh : h ∈ GfC V) : infGL θ V h = 1 := by
  have h1 : infHom V h = 1 := hh
  rw [infGL, MonoidHom.comp_apply, h1, map_one]

theorem eqv_real (hθ : IsInfFam θ) (hc : c.Is) (lam : D.what₂.Tau → DomWeight V.rank) (f : VV ℂ lam →ₗ[ℂ] c.W)
    (hf : ∀ γ ∈ GQ V, ∀ x, f (rhoK lam (infGL θ V γ) x) = c.ρ γ (f x)) {u : GA D V} (hu : u ∈ GinfC V) (x : VV ℂ lam) :
    f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := by
  by_contra hne
  have h0 : ∀ f' : (coefA θ V lam 1).W →ₗ[ℂ] c.W, Continuous f' := fun f' => f'.continuous_of_finiteDimensional
  have h1 : Continuous fun h : GA D V => f (rhoK lam (infGL θ V h) x) := (h0 f).comp (coefA_cont lam 1 hθ x)
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun h1 (hc.2.2.1 (f x))) hne
  refine hU ?_
  rw [map_mul, infGL_fin hk, mul_one, map_mul, hc.1 k hk, mul_one]
  exact hf γ hγ x

theorem infGL_rat (hθ : IsInfFam θ) {K : Type} [Field K] (σ : K →+* ℂ) (emb : D.what₂.Tau → D.host.E →+* K)
    (hemb : ∀ τ x, σ (emb τ x) = tauE D τ x) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    infGL θ V γ = fun τ => Formalism.UG.bc σ (embGL emb γE τ) := by
  funext τ
  refine Units.ext (Matrix.ext fun a b => ?_)
  have h1 : ((matHom V (γ : GA D V)).1 a b) = incA D (γE.1 a b) := by
    rw [show matHom V (γ : GA D V) = _ from hγ]
    rfl
  show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((matHom V (γ : GA D V)).1 a b)) = σ (emb τ (γE.1 a b))
  rw [h1, hemb, ← (hθ τ).1]
  exact congrArg (θ τ) ((Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rw [map_one]; rfl))


open Classical in
theorem eqv_transpose (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    (lam : D.what₂.Tau → DomWeight V.rank) (φ : SmT M →ₗ[ℂ] VV ℂ lam)
    (hφ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      (φ (PiTensorProduct.tprod ℂ (Function.update v τ w))).1 =
        actP lam (invTrK (infGL θ V (atTau θ V τ g))) (φ (PiTensorProduct.tprod ℂ v)).1)
    (f : VV ℂ lam →ₗ[ℂ] c.W) (hf : ∀ w v, pr (f w) v = pairBK lam (φ v) w) {u : GA D V} (hu : u ∈ GinfC V) (x : VV ℂ lam) :
    f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  let U : Submonoid (GA D V) :=
    { carrier := {h | ∀ x, f (rhoK lam (infGL θ V h⁻¹) x) = c.ρ h⁻¹ (f x)}
      one_mem' := fun x => by rw [inv_one, map_one, map_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb x => by
        rw [_root_.mul_inv_rev, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha] }
  have key := real_le hθ U (fun τ g hg x => ?_) (inv_mem hu) x
  · rwa [inv_inv] at key
  refine (pair_bijective hθ hp hc hpr).1 (PiTensorProduct.ext (MultilinearMap.ext fun v => ?_))
  let y : M.sm τ := ⟨M.rep τ g (v τ), Submodule.eq_top_iff'.1 (m τ).2.1 _⟩
  have h1 := hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ (f x)) v y rfl
  rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at h1
  show pr _ (PiTensorProduct.tprod ℂ v) = pr _ (PiTensorProduct.tprod ℂ v)
  rw [← h1, hf, hf, pairBK_apply, pairBK_apply, hφ τ g hg v y rfl,
    ← pairingBInvariantK_holds ℂ _ _ lam (infGL θ V (atTau θ V τ g)), ← rhoK_coe lam (infGL θ V (atTau θ V τ g)), rhoK_mul, ← map_mul,
    mul_inv_cancel, map_one, rhoK_one]


open Classical in
theorem exists_scalar (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) {n : ℕ} (hn : V.rank = n)
    (lam : D.what₂.Tau → DomWeight n) {K : Type} [Field K] (σ : K →+* ℂ) (emb : D.what₂.Tau → D.host.E →+* K)
    (hemb : ∀ τ x, σ (emb τ x) = tauE D τ x) (cv : VV K lam →ₛₗ[σ] c.W)
    (hcv : ∀ (γ : GQ V) γE (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → GlobalTheory.Mem.R3.MatEq γE g →
      ∀ v, cv (rhoV emb lam g v) = c.ρ γ.1 (cv v)) (h0 : cv ≠ 0)
    (G G' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (o : Frames G') (ho : (fun τ => (o.1 τ)⁻¹) = 1)
    (j : SmT M →ₗ[ℂ] (Frames G → ℂ)) (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam)
    (heqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : Frames G, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr hn) (finCongr hn))) y' y →
        j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y') :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ w v, pr (cv w) v =
      a * pairB lam (Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)) (MvPolynomial.map σ w.1) := by
  subst hn
  obtain ⟨φ, hφ⟩ := exists_equiv G lam j hinj hr
  have hf : Function.Injective (fnOf G (shiftOf lam) 1) :=
    Formalism.L2.Col.fnOf_injective G _ 1 (fun τ => by simp) ⟨fun _ => 1, fun τ => by simp⟩
  have hpol : ∀ v, Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) = (φ v).1 := fun v => by
    have h := Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o (φ v).1
    rw [ho] at h
    rw [hφ]
    exact h
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hB : (pairBK (K := ℂ) lam).flip.Nondegenerate := LinearMap.flip_nondegenerate.mpr (pairingBNondegenerate_holds ℂ _ _ lam)
  let e := LinearEquiv.ofBijective pr (pair_bijective hθ hp hc hpr)
  let f : VV ℂ lam ≃ₗ[ℂ] c.W := (LinearMap.BilinForm.toDual _ hB).trans (φ.dualMap.trans e.symm)
  have hfp : ∀ w v, pr (f w) v = pairBK lam (φ v) w := fun w v =>
    LinearMap.congr_fun (e.apply_symm_apply (φ.dualMap (LinearMap.BilinForm.toDual _ hB w))) v
  have h2 : ∀ u ∈ GinfC V, ∀ x, f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := fun u hu x => by
    refine eqv_transpose hθ hp hc hpr lam φ.toLinearMap (fun τ g hg v w hw => hf (funext fun y => ?_)) f.toLinearMap hfp hu x
    have ha : IsAtTau θ V τ g (atTau θ V τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ g hg).exists
      rw [atTau, dite_eq_left hex]
      exact hex.choose_spec
    set A := infGL θ V (atTau θ V τ g) with hA
    let y' : Frames G := ⟨fun ρ => ((A ρ)⁻¹ : GL (Fin V.rank) ℂ).1 * y.1 ρ, fun ρ => by
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).mul (y.2 ρ)⟩
    rw [fnOf_actP G lam _ _ y y' fun ρ => by rw [invTrK_coe, Matrix.transpose_transpose]]
    have := heqv τ g hg v w hw y y' fun ρ => by
      have e1 : Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ
          (g.reindex (finCongr rfl) (finCongr rfl)) ρ = (A ρ).1 := by
        by_cases hρ : ρ = τ
        · subst hρ
          rw [Function.update_self]
          exact ha.2.1.symm
        · rw [Function.update_of_ne hρ]
          exact (ha.2.2 ρ hρ).symm
      rw [e1]
      show y.1 ρ = (A ρ).1 * (((A ρ)⁻¹ : GL (Fin V.rank) ℂ).1 * y.1 ρ)
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [hφ, hφ] at this
    exact this
  obtain ⟨c', hc'⟩ := exists_ext σ lam cv
  have h1 : ∀ u ∈ GinfC V, ∀ x, c' (rhoK lam (infGL θ V u) x) = c.ρ u (c' x) := fun u hu x => by
    refine eqv_real hθ hc lam c' (fun γ hγ x => ?_) hu x
    obtain ⟨γE, -, hE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hE' : Bridge.IsRatMat V ⟨γ, hγ⟩ γE := hE.symm
    refine LinearMap.congr_fun (ext_bc σ lam (f := c' ∘ₗ rhoK lam (infGL θ V γ)) (g := c.ρ γ ∘ₗ c') fun w => ?_) x
    have e2 : rhoK lam (infGL θ V γ) (bcVV σ lam w) = bcVV σ lam (rhoV emb lam γE w) := by
      refine Subtype.ext ?_
      show actP lam (infGL θ V γ) (MvPolynomial.map σ w.1) = MvPolynomial.map σ (actP lam (embGL emb γE) w.1)
      rw [GlobalTheory.CoefSpace.map_actP, ← infGL_rat hθ σ emb hemb ⟨γ, hγ⟩ γE hE']
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e2, hc', hc']
    exact hcv ⟨γ, hγ⟩ γE γE hE' ⟨rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩ w
  haveI := hc.2.2.2.1
  obtain ⟨a, ha⟩ := schur (fun h => c.ρ h) hc.2.2.2.2 (c' ∘ₗ f.symm.toLinearMap) fun h w => by
    obtain ⟨u, hu, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    obtain ⟨x, rfl⟩ := f.surjective w
    show c' (f.symm (c.ρ (u * k) (f x))) = c.ρ (u * k) (c' (f.symm (f x)))
    rw [map_mul, hc.1 k hk, mul_one, ← h2 u hu, f.symm_apply_apply, f.symm_apply_apply, h1 u hu]
  have ha' : ∀ w, cv w = a • f (bcVV σ lam w) := fun w => by
    rw [← ha, ← hc']
    exact congrArg c' (f.symm_apply_apply _).symm
  refine ⟨a, fun h => h0 (LinearMap.ext fun w => by rw [ha', h, zero_smul]; rfl), fun w v => ?_⟩
  rw [ha', map_smul, LinearMap.smul_apply, hfp, smul_eq_mul, pairBK_apply, hpol]
  rfl

end Group

end GlobalTheory.TopVal.Scalar

end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelCombStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaStepVector_eq_tupleComb_of_levelComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ : WO S T → ℂ) (dG dQ : WO S T →₀ ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q → (∀ PP ∈ Pg, ∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) → (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dG → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dQ → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj ∅ (fun _ => 1) f₀ (comb ψ S T dG f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ (comb ψ S T dG f₀)) := by
  first | exact @GlobalTheory.HalfProd.stepVec_of_prod | exact GlobalTheory.HalfProd.stepVec_of_prod | (intros; apply GlobalTheory.HalfProd.stepVec_of_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal.Inj

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem exists_fin {D : D7} (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    ∃ g' : GA D V, g' ∈ GfC V ∧ finHom V g' = finHom V g ∧
      ∃ y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        y ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
        ∀ i j, (Formalism.UG.bc (swapAE D) (finHom V g')).1 i j = y.1 (finCongr hn i) (finCongr hn j) := by
  subst hn
  let z := (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).symm (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g)
  have hz : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram z.1 = GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g :=
    (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).apply_symm_apply _
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V _ rfl
  refine ⟨z.1, z.2, congrArg Subtype.val hz, (e ⟨z.1, z.2⟩).1, (e ⟨z.1, z.2⟩).2, fun i j => ?_⟩
  rw [he]
  rfl

theorem eq_zero_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g, (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  have h1 : R.B.jR t x = 0 := by
    funext k
    obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective k
    exact (congrFun (h t x) k).symm.trans ((congrArg ((R.HX t).e (R.jX t x)) hg.symm).trans (hx g))
  have h2 : Function.Injective (R.B.jR t) := GlobalTheory.PresBasic.extL_injective (R.B.R t).pres
  exact (injective_iff_map_eq_zero (R.B.jR t)).1 h2 x h1

theorem eq_zero_of_isRes {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : Col2.TC B X) (a : I.ι) (φ : Frm I a) τ (e : I.tup a = τ)
    (ok : (Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).Ok)
    (h : IsRes φ (0 : ((Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).toCSD ok).Forms)) : φ = 0 := by
  subst e
  obtain ⟨ok', h⟩ := h
  exact (LinearEquiv.map_eq_zero_iff _).1 (eq_of_heq h)


set_option maxHeartbeats 2000000 in
theorem eq_zero_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) :
    ∀ (s : a.x.T) (φ : Frm w.I (a.x.Y.tup s)), IsRes φ (0 : a.x.A3.A.fam.amb.FR s) → φ = 0 := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  intro s φ h
  have e : w.I.tup (Y.tup s) = s.1 :=
    (congrArg w.I.tup ((congrFun hT' s).trans (t.r.tup_ix s))).trans (R3.tup_ixOf w.I s)
  exact eq_zero_of_isRes w.I _ φ s.1 e _ h

theorem exists_hasMat {D : D7} (gP : Formalism.L2.Forms.gramP D = 1) (g : GA D D.sp.X') :
    ∃ g' y, GlobalTheory.Core.Rk.Top.HasMat g' y ∧ y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) ∧
      (finHom D.sp.X').rangeRestrict g = (finHom D.sp.X').rangeRestrict g' := by
  obtain ⟨g', h1, h2, y, h3, h4⟩ := exists_fin _ _ (Formalism.L2.Forms.rankP D) g
  have h6 : y ∈ Formalism.UG.UPts _ (Formalism.L2.Forms.gramP D) _ := h3
  rw [gP] at h6
  exact ⟨g', y, ⟨h1, h4⟩, h6, Subtype.ext h2.symm⟩

theorem eq_zero_of_hasMat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (gP : Formalism.L2.Forms.gramP D = 1)
    (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) →
      (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  refine eq_zero_of_models R h t x fun g => ?_
  exact (exists_hasMat gP g).elim fun g' h1 => h1.elim fun y h2 =>
    (congrArg ((R.HX t).e (R.jX t x)) h2.2.2).trans (hx g' y h2.1 h2.2.1)


end GlobalTheory.TopVal.Inj
end

