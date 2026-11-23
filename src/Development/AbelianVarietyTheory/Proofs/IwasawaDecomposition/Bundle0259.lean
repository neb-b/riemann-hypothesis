module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

theorem theta_eq_zero_of_orth {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]
    {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V} {gE : Representation ℂ G E} {Θ : V →ₗ[ℂ] E}
    (H : Hyp σ j r ρ gE Θ)
    (hRZ : Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ))
    (e a : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e)
    (hfix : ∀ y ∈ LinearMap.range Θ, opV σ (fun g => gE g) a y = y) (f : F) (hea : opF r e f = opF r a f)
    (horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint Θ)).comap j ⊓ LinearMap.range (opF r e) : Submodule K F),
      ⟪j z, j f⟫_ℂ = 0) : Θ (j f) = 0 := by
  have h1 : Θ (j (opF r e f)) = Θ (j f) := by
    rw [hea, j_opF H.jr, theta_opV H.sp H.jr H.eq, hfix _ ⟨_, rfl⟩]
  have h2 : j (opF r e f) ∈ LinearMap.range (opV σ ρ e) := ⟨j f, (j_opF H.jr e f).symm⟩
  obtain ⟨u', hu', hθ⟩ := H.dn e he h2
  have hu'' : u' ∈ Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
      LinearMap.range (opF r e) : Submodule K F) : Set F)) := by
    rw [H.ratLev hRZ e he]
    exact hu'
  have h3 : ⟪u', j f⟫_ℂ = 0 := by
    have hle : Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
        LinearMap.range (opF r e) : Submodule K F) : Set F)) ≤ (Submodule.span ℂ {j f})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact horth z hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu'')
  obtain ⟨⟨w, rfl⟩, -⟩ := hu'
  have h4 : Θ (LinearMap.adjoint Θ w - j f) = 0 := by
    rw [map_sub, hθ, h1, sub_self]
  have h5 : ⟪LinearMap.adjoint Θ w, LinearMap.adjoint Θ w - j f⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h4, inner_zero_right]
  rw [inner_sub_right, h3, sub_zero, inner_self_eq_zero] at h5
  rw [← h1, ← hθ, h5, map_zero]

theorem opF_lvlIdem_fix {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (H : Subgroup G) (ψ : H →* Kˣ) (v : V)
    (hv : ∀ a : H, ρ a.1 v = ((ψ a : Kˣ) : K) • v) : opF ρ (lvlIdem H ψ) v = v := by
  classical
  rw [opF_eq_lift]
  unfold lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  have : ∀ h : H, MonoidAlgebra.lift K (V →ₗ[K] V) G ρ
      (MonoidAlgebra.single (h : G) ((Nat.card H : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K))) v = (Nat.card H : K)⁻¹ • v := by
    intro h
    rw [MonoidAlgebra.lift_single, LinearMap.smul_apply, hv, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

end GlobalTheory.Mem.ThOrth

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators


set_option maxHeartbeats 4000000 in
theorem thG_eq_zero_of_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _Z hP hH i t x hx
  have hok := hH.ok
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hP.char hH.aux.ex
  have hM := hc.models
  have hCore : GlobalTheory.Hk3.Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hRZ : (R.toCx3 F).RatZ := (complex_data_conditions_base_level_of_primitive_links hok hH.sep hP.char hH.prim).ratZ
  have hjr (g : G) (v : A3.fam3.amb3.FL i t) :
      (R.toCx3 F).jL i t ((A3.A.fam.L i t).r g v) =
        (R.toCx3 F).opLC i t (Sum.inr g) ((R.toCx3 F).jL i t v) := by
    have hb := hK i t
    have key : ∀ k : Module.Basis.ofVectorSpaceIndex D.what₂.LL (A3.fam3.amb3.FL i t),
        (R.toCx3 F).opLC i t (Sum.inr g) ((R.toCx3 F).jL i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k)) =
        (R.toCx3 F).jL i t ((A3.A.fam.L i t).r g (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k)) := by
      intro k
      unfold Formalism.IndefR.Cx.CxData.opLC
      rw [dite_eq_left hb]
      have e : (R.toCx3 F).jL i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k) = Module.Basis.mk hb.1 hb.2.ge k :=
        (Module.Basis.mk_apply hb.1 hb.2.ge k).symm
      rw [e, Module.Basis.constr_basis]
      rfl
    have hh := Module.Basis.ext (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t))
      (f₁ := ((R.toCx3 F).jL i t).comp ((A3.A.fam.L i t).r g))
      (f₂ := ((R.toCx3 F).opLC i t (Sum.inr g)).comp ((R.toCx3 F).jL i t))
      (fun k => (key k).symm)
    exact LinearMap.congr_fun hh v
  have H : Hyp A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (A3.A.fam.L i t).r
      (fun g => (R.toCx3 F).opLC i t (Sum.inr g)) (R.gWx F i) ((R.toCx3 F).θ' i t) := by
    refine ⟨Formalism.IndefR.CxPass.lift_embeddings_span hK i t, hjr, ?_, hH.prim.gEquiv.2 i t, hH.prim.gUnit.2 i⟩
    intro g a b
    rw [hJ i t, hJ i t]
    change A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) =
      A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _)
    set_option backward.isDefEq.respectTransparency false in
      rw [CSDForm.csumForm_apply, CSDForm.csumForm_apply]
    exact congrArg A3.fam3.base3.v0.embedding ((hok.ok2.lifts i t).act.unitary g a b)
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 := ⟨hok.ok2.conj, hok.ok2.irr, hok.ok2.lifts i t⟩

  have hopE : opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) := by
    let mA : ((R.HW i (sg0 D A3.A)).H →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H) →+
        (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H →ₗ[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) :=
      { toFun := Tw.map (twAt D.what₂.embLL A3.A.v0), map_zero' := LinearMap.ext fun _ => rfl,
        map_add' := fun _ _ => LinearMap.ext fun _ => rfl }
    rw [show Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) = mA (GlobalTheory.Hk3.eH R.toRealDat i) from rfl]
    unfold opV GlobalTheory.Hk3.eH
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => LinearMap.ext fun y => ?_
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y)
    rw [Formalism.IndefR.Links.emb_eq D.what₂.embLL A3.A.v0, Formalism.IndefR.Links.cj_cj]
    rfl
  have hθ : ∀ (u : (R.toCx3 F).FLC i t),
      Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
        cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) :=
    fun u => rfl
  have hfix : ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t),
      opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) y = y := by
    rintro _ ⟨u, rfl⟩
    rw [hopE]
    change Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i
      (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u))) =
      (R.toCx3 F).θ' i t u
    rw [hθ, map_smul, hL.2.2.2, ← hθ]
    rfl

  set ℓ := A3.A.fam.lvlA F.P0 F.ψ0 with hℓ
  set f0 := liftForm A3.A F.P0 F.ψ0 i t x with hf0
  have hf0l : f0 = GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ x := rfl
  have hlev : f0 ∈ lvlForms (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ := by
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm]
    exact ⟨x, hf0l.symm⟩
  have hfix0 : opF (A3.A.fam.L i t).r (lvlIdem ℓ.P ℓ.ψ) f0 = f0 := by
    exact opF_lvlIdem_fix (A3.A.fam.L i t).r ℓ.P ℓ.ψ f0 hlev
  have hea : opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ) f0 = opF (A3.A.fam.L i t).r (idemOf A3.A.X) f0 := by
    rw [goodAt, opF_mul, LinearMap.comp_apply, hfix0]
    rfl
  have horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ⊓
      LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _),
      ⟪(R.toCx3 F).jL i t z, (R.toCx3 F).jL i t f0⟫_ℂ = 0 := by
    intro z hz
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) ℓ _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq]
      rfl
    have hz' : z ∈ LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := hZeq ▸ hz
    obtain ⟨c, rfl⟩ := hz'
    rw [← GlobalTheory.Mem.LiftForms.lvlForm_lE hB c]
    refine (hJ i t _ _).trans ?_
    have h0 : Formalism.DivisionValues.hform ((A3.A.fam.L i t).S.lvlH (A3.A.fam.L i t).r ℓ.P ℓ.ψ)
        ((A3.A.fam.L i t).lE ℓ ((R.toCx3 F).Zl i t) *ᵥ c) x = 0 := hx c
    show A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) = 0
    rw [CSDForm.csumForm_apply, hf0l, GlobalTheory.Mem.LiftForms.csum_lvlForm, h0, mul_zero, map_zero]
  have key := theta_eq_zero_of_orth H (hRZ.2 i t) (goodAt ℓ.X ℓ.P ℓ.ψ) (idemOf A3.A.X)
    (opF_goodAt_idem _ _ hok.ok2.irr _ _) hfix f0 hea horth
  have h2 := congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) key
  rw [hθ, hP.phs i, map_one, one_smul] at h2
  exact h2

end GlobalTheory.Mem.ThOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableChernPolyTopDensity
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChernMeas

def measPoly (X σ : Type) [MeasurableSpace X] : Subalgebra ℝ (X → MvPolynomial σ ℂ) where
  carrier := {f | ∀ d, Measurable fun x => AddMonoidAlgebra.coeff (f x) d}
  mul_mem' := by
    classical
    intro f g hf hg d
    simp only [Pi.mul_apply, coeff_mul]
    exact Finset.measurable_sum _ fun p _ => (hf p.1).mul (hg p.2)
  add_mem' := by
    intro f g hf hg d
    simp only [Pi.add_apply, MvPolynomial.coeff_add]
    exact (hf d).add (hg d)
  algebraMap_mem' := by
    intro c d
    exact measurable_const (a := AddMonoidAlgebra.coeff (algebraMap ℝ (MvPolynomial σ ℂ) c) d)

theorem C_mem {X σ : Type} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    (fun x => (C (f x) : MvPolynomial σ ℂ)) ∈ measPoly X σ := by
  classical
  intro d
  simp only [coeff_C]
  split_ifs
  · exact hf
  · exact measurable_const

theorem const_mem {X σ : Type} [MeasurableSpace X] (p : MvPolynomial σ ℂ) :
    (fun _ : X => p) ∈ measPoly X σ := fun _ => measurable_const

def evalAt {X σ : Type} [MeasurableSpace X] (x : X) : measPoly X σ →ₐ[ℝ] MvPolynomial σ ℂ :=
  (Pi.evalAlgHom ℝ (fun _ : X => MvPolynomial σ ℂ) x).comp (measPoly X σ).val

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem measurable_curv {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (ξ η : V n) (i j : r) :
    Measurable fun v => curv G v ξ η i j := by
  let f : V n → ℂ := fun x => conn G x ξ i j
  change Measurable fun v => -((1 / 2 : ℂ) * (fderiv ℝ f v η + Complex.I * fderiv ℝ f v (Complex.I • η)))
  exact (((measurable_fderiv_apply_const ℝ f η).add
    ((measurable_fderiv_apply_const ℝ f (Complex.I • η)).const_mul _)).const_mul _).neg

theorem curvPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (i j : r) :
    (fun v => curvPoly G v i j) ∈ measPoly (V n) (Fin n × Fin n) := by
  have e : (fun v => curvPoly G v i j) = ∑ a, ∑ b, (fun v => (C (curv G v (coordVec a) (coordVec b) i j) :
      MvPolynomial (Fin n × Fin n) ℂ)) * fun _ => X (a, b) := by
    funext v
    simp [curvPoly, Finset.sum_apply]
  rw [e]
  exact Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ =>
    Subalgebra.mul_mem _ (C_mem (measurable_curv G _ _ i j)) (const_mem _)

theorem chernPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (k : ℕ) :
    (fun v => chernPoly G v k) ∈ measPoly (V n) (Fin n × Fin n) := by
  let M : Matrix r r (measPoly (V n) (Fin n × Fin n)) := Matrix.of fun i j => ⟨_, curvPoly_mem G i j⟩
  have e : (fun v => chernPoly G v k) = ((Matrix.charpolyRev (-M)).coeff k).1 := by
    funext v
    have h : -curvPoly G v = (-M).map (evalAt v).toRingHom := by
      ext i j : 2
      rfl
    rw [chernPoly, h, charpolyRev_map, Polynomial.coeff_map]
    rfl
  rw [e]
  exact Subtype.property _

theorem measurable_chernTop {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) :
    Measurable (fun v => chernTop R G v) := by
  let P : measPoly (V n) (Fin n × Fin n) :=
    aeval (fun x : ι × ℕ => (⟨_, chernPoly_mem (fun u => G u x.1) x.2⟩ : measPoly (V n) (Fin n × Fin n))) R
  have e (v : V n) : aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R = P.1 v := by
    change _ = evalAt v P
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl
  simp only [chernTop, e, topCoeff]
  refine Measurable.const_mul (Complex.measurable_re.comp ?_) _
  exact Finset.measurable_sum _ fun w _ => (P.2 _).const_mul _

end GlobalTheory.ChernMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem detId_stdL (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : Th.detId H (Th.stdL H N) M = detSub M := by
  classical
  unfold Th.detId detSub
  congr 1
  ext z
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun j i => A i j, fun j => ?_, (Matrix.det_transpose A).symm⟩
    have h1 : (Pi.single j 1 : Fin N → H.E) ∈ Th.stdL H N := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Matrix.of x).transpose, fun v hv => ?_, (Matrix.det_transpose _).symm⟩
    choose b hb using fun i => Submodule.mem_one.1 (hv i trivial)
    have e : (Matrix.of x).transpose.mulVec v = ∑ i, b i • x i := by
      funext j
      rw [Finset.sum_apply]
      show ∑ i, x i j * v i = ∑ i, b i • x i j
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, hb, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)

theorem ordSub_detSub_stdL (N : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) : ordSub w (detSub (Th.stdL H N)) = 0 := by
  rw [← detId_stdL, detId_std, Submodule.one_eq_span]
  have h := ordSub_span_singleton w (1 : H.Eˣ)
  rw [Units.val_one] at h
  rw [h]
  simp [Formalism.L2.Host.ordF]

theorem tildeD_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : Formalism.L2.Host.HChar H.E), Formalism.L2.Host.IsChiPsi H χ → ∀ (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)), Submodule.IsLattice H.E M → ∀ x : DtT H, (QuotientGroup.mk x : DtT H ⧸ UOT H) = relDetT H N (Th.stdL H N) M → ((tildeD H χ x : ℂˣ) : ℂ) = chiId χ (Th.detId H (Th.stdL H N) M) := by
  intro R H χ hχ N M hM x hx
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (KerDet.kernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v y hy _ => hχ.unr v y hy) fun v _ => hχ.unr v
  have hU := (ChiLaws.chi_laws R H χ hχ).1
  have hfin : {w : HeightOneSpectrum (𝓞 H.E) | ordSub w (detSub M) ≠ 0}.Finite := by
    by_cases h : ∃ k : H.Eˣ, (k : H.E) ∈ detSub M
    · obtain ⟨k, hk⟩ := h
      exact DetOrd.ordSub_finite (DetOrd.isFractional_detSub M hM.fg) k hk
    · have hz : ∀ w, ordSub w (detSub M) = 0 := by
        intro w
        unfold ordSub
        have he : {n : ℤ | ∃ k : H.Eˣ, (k : H.E) ∈ detSub M ∧ Formalism.L2.Host.ordF w k = n} = ∅ := by
          ext n
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨k, hk, _⟩
          exact h ⟨k, hk⟩
        rw [he]
        simp
      simp [hz]
  unfold relDetT at hx
  have h1 := hU _ (QuotientGroup.eq.1 hx)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1, tildeD_mk H hK, detId_stdL]
  unfold chiId
  congr 1
  simp only [ordSub_detSub_stdL, sub_zero]
  have h2 : Function.HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 H.E) =>
      Neutral.B1.localIdele H.E w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) ^ (ordSub w (detSub M)).toNat := by
    refine hfin.subset fun w hw h0 => hw ?_
    simp only [h0, Int.toNat_zero, pow_zero]
  refine ((χ.1.comp (finPartI H.E)).map_finprod h2).trans (finprod_congr fun w => ?_)
  rw [map_pow, MonoidHom.comp_apply, KerDet.finPartI_localIdele]
  rfl

end GlobalTheory.Mem.ChiDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

section Helpers

variable {F : Type} [Field F]

theorem spMap_comp_apply_field {Z : Scheme.{0}} {k K : Type} [Field k] [Field K] (σ : k →+* K) (p : Sp k ⟶ Z)
    (w : Sp K) (w' : Sp k) : (spMap σ ≫ p) w = p w' := by
  rw [Scheme.Hom.comp_apply]
  exact congrArg p (Subsingleton.elim (α := PrimeSpectrum k) _ _)

theorem val_spMap_comp_field {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {k K : Type} [Field k]
    [Field K] (σ : k →+* K) (p : Sp k ⟶ M.Z) (y : Ω) : M.val (spMap σ ≫ p) y = σ (M.val p y) := by
  by_cases hy : y ∈ M.O (p (IsLocalRing.closedPoint k))
  · have := RatModel.val_spMap_comp σ p specializes_rfl ⟨y, hy⟩
    rw [RatModel.valLoc_eq_val] at this
    exact this
  · rw [RatModel.val_of_notMem (y := p) (IsLocalRing.closedPoint k) hy, map_zero,
      RatModel.val_of_notMem (y := spMap σ ≫ p) (IsLocalRing.closedPoint K)
        (fun h' => hy (by convert h' using 2; exact (spMap_comp_apply_field σ p _ _).symm))]

theorem bears_spMap {ι : Type} {m : ι → ℕ} {X Y : Var F} (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (A : Mat m X.Fn) {k K : Type} [Field k] [Field K] (σ : k →+* K) (h : Mat m k) (p : Sp k ⟶ Y.X)
    (hb : Bears S φ A h p) : Bears S φ A (h.map σ) (spMap σ ≫ p) := by
  obtain ⟨A', hA', hP⟩ := hb
  refine ⟨A', ?_, ?_⟩
  · convert hA' using 2
    exact spMap_comp_apply_field σ p _ _
  have e : (A' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap σ ≫ p)) =
      ((A' * (A.map φ)⁻¹).map ((ratOf Y).val p)).map σ := by
    funext τ
    ext i j
    exact val_spMap_comp_field (ratOf Y) σ p _
  rw [e, ← Mat.map_inv, ← Mat.map_mul]
  exact hP.map σ fun _ _ => trivial

end Helpers

theorem coBear_spMap : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ _ _ k K _ _ σ x p₁ p₂ hc
  obtain ⟨A, hA, h, hh, h1, h2⟩ := hc
  refine ⟨A, ?_, h.map σ, hh.map σ fun _ _ => trivial, bears_spMap S₁ φ₁ A σ h p₁ h1,
    bears_spMap S₂ φ₂ A σ h p₂ h2⟩
  convert hA using 2
  exact congrArg Eb.S (spMap_comp_apply_field σ x _ _)

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCoveStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → KeepsRad M M' φ f := by
  first | exact @GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | exact GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | (intros; apply GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealReS
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem real_reS : ∀ (D : D7) (Z : SNew D), (Formalism.L2.Theta.RealTied D → Formalism.L2.Theta.RealTied (reS D Z)) ∧ StandardLattice.DstarD (reS D Z) = StandardLattice.DstarD D ∧ (StandardLattice.VolumeEqMass₂ D → StandardLattice.VolumeEqMass₂ (reS D Z)) :=
  fun _ _ => ⟨fun h => ⟨h.cdScale, h.dsig, h.dsig_all, h.vol⟩, rfl, fun h => h⟩

end GlobalTheory.Mem.SRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExtStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_closure_iso_ramified_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e → (∀ y, Valued.v (f y) = Valued.v y ^ e) → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → ∀ b₀ : Kbar v ≃+* Kbar v', (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x)) → ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔ IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  first | exact @GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | exact GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | (intros; apply GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map <;> assumption)
end

