module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FixedSpan

section General

variable {ι G H : Type} {Γ Hs : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
  {p : ∀ i, G →* Γ i} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ξ : ∀ i, Hs i} {π : G →* (H →L[ℂ] H)}
  {B : (∀ i, Hs i) → H}

theorem mem_closure_span_of_orthogonal [DecidableEq ι] [CompleteSpace H] (h : IsRestrTensor p δ ξ π B)
    (U : ∀ i, Submodule ℂ (Hs i)) [∀ i, (U i).HasOrthogonalProjection] (hξ : ∀ᶠ i in cofinite, ξ i ∈ U i) (x : H)
    (hx : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪x, B (Function.update z i w)⟫_ℂ = 0) :
    x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure := by
  set Y := (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure with hY
  haveI : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨a, ha, u, hu, rfl⟩ := Y.exists_add_mem_mem_orthogonal x
  have h1 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪a, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have : Y ≤ (ℂ ∙ B (Function.update z i w))ᗮ :=
      Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
        rintro _ ⟨y, hy, hyU, rfl⟩
        refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
        rw [h.inner_update hz hy, Submodule.inner_right_of_mem_orthogonal (hyU i) hw, zero_mul]))
        (Submodule.isClosed_orthogonal _)
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (this ha)
  have h2 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪u, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have := hx z hz i w hw
    rwa [inner_add_left, h1 z hz i w hw, zero_add] at this
  have h3 : ∀ s : Finset ι, ∀ y, Restr ξ y → (∀ i ∉ s, y i ∈ U i) → ⟪u, B y⟫_ℂ = 0 := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      intro y hy hyU
      exact Submodule.inner_left_of_mem_orthogonal (K := Y)
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, hy, fun i => hyU i (by simp), rfl⟩)) hu
    | insert i s hi ih =>
      intro y hy hyU
      obtain ⟨b, hb, c, hc, e⟩ := (U i).exists_add_mem_mem_orthogonal (y i)
      have e1 : B y = B (Function.update y i b) + B (Function.update y i c) := by
        have := h.pure_update hy i 1 b c
        rwa [one_smul, one_smul, ← e, Function.update_eq_self] at this
      rw [e1, inner_add_right, h2 y hy i c hc, add_zero]
      refine ih _ (SmallThetaModules.restr_update hy i b) fun j hj => ?_
      by_cases hji : j = i
      · subst hji; rwa [Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hyU j (by simp [hji, hj])
  have h4 : u = 0 := h.ext fun y hy => by
    have hf : ({i | y i ≠ ξ i} ∪ {i | ξ i ∈ U i}ᶜ).Finite := Set.Finite.union hy hξ
    rw [inner_zero_right, inner_eq_zero_symm]
    refine h3 hf.toFinset y hy fun i hi => ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_or, not_not] at hi
    exact hi.1 ▸ hi.2
  rwa [h4, add_zero]

theorem exists_update_clm [DecidableEq ι] (h : IsRestrTensor p δ ξ π B) {y : ∀ i, Hs i} (hy : Restr ξ y) (v : ι) :
    ∃ T : Hs v →L[ℂ] H, ∀ w, T w = B (Function.update y v w) := by
  have hr := SmallThetaModules.restr_update hy v
  have h0 : B (Function.update y v 0) = 0 := h.ext fun z hz => by simp [h.inner_update hy hz]
  let T : Hs v →ₗ[ℂ] H :=
    { toFun := fun x => B (Function.update y v x)
      map_add' := fun a b => by simpa using h.pure_update hy v 1 a b
      map_smul' := fun c a => by simpa [h0] using h.pure_update hy v c a 0 }
  have hT : ∀ x, ‖T x‖ ≤ √‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖ * ‖x‖ := fun x => by
    have e := h.inner_update hy (hr x) v x
    rw [Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by
      rw [Function.update_of_ne hu]] at e
    have e' := congrArg norm e
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e'
    refine le_of_sq_le_sq (le_of_eq ?_) (by positivity)
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), mul_comm]
    simpa [T] using e'
  exact ⟨T.mkContinuous _ hT, fun _ => rfl⟩

end General

def fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] (ρ : G →* (X →L[ℂ] X))
    (K : Subgroup G) : Submodule ℂ X := ⨅ k ∈ K, LinearMap.ker ((ρ k - 1 : X →L[ℂ] X) : X →ₗ[ℂ] X)

theorem mem_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ρ : G →* (X →L[ℂ] X)}
    {K : Subgroup G} {x : X} : x ∈ fixedSub ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixedSub, sub_eq_zero]

theorem isClosed_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (ρ : G →* (X →L[ℂ] X)) (K : Subgroup G) : IsClosed (fixedSub ρ K : Set X) := by
  have : (fixedSub ρ K : Set X) = ⋂ k ∈ K, {x | ρ k x = x} := by
    ext x; simp [mem_fixedSub]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_eq (ρ k).continuous continuous_id

theorem inner_eq_zero_of_fixed {Γ X H : Type} [Group Γ] [TopologicalSpace Γ] [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : Γ →* (X →L[ℂ] X)} (hρ : IsUnitaryRep ρ) {τ : Γ → (H →L[ℂ] H)}
    (hτ : ∀ g a b, ⟪τ g a, τ g b⟫_ℂ = ⟪a, b⟫_ℂ) (T : X →L[ℂ] H) (hT : ∀ g w, T (ρ g w) = τ g (T w))
    {K : Subgroup Γ} {x : H} (hx : ∀ k ∈ K, τ k x = x) {w : X} (hw : w ∈ (fixedSub ρ K)ᗮ) : ⟪x, T w⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  refine Submodule.inner_right_of_mem_orthogonal (mem_fixedSub.2 fun k hk => ext_inner_right ℂ fun z => ?_) hw
  obtain ⟨z, rfl⟩ : ∃ z', z = ρ k z' := ⟨ρ k⁻¹ z, by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]⟩
  rw [inner_map_map hρ, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hT]
  conv_rhs => rw [← hx k hk, hτ]

theorem mem_closure_span_fixed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation σ J (fun v => (R v).π) ξ π B → ∀ (Kp : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GLoc σ J v)), (∀ᶠ v in cofinite, ∀ k ∈ Kp v, (R (.inr v)).π k (ξ (.inr v)) = ξ (.inr v)) → ∀ x : H, (∀ v, ∀ k ∈ Kp v, π (emb σ J v k) x = x) → x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, ∀ k ∈ Kp v, (R (.inr v)).π k (y (.inr v)) = y (.inr v)) ∧ z = B y}).topologicalClosure := by
  intro F E _ _ _ _ _ σ n J H _ _ π hπ R ξ B h Kp hξ x hx
  classical
  haveI := hπ.complete
  haveI := fun v => (R v).isIrr.complete
  let K : ∀ v, Subgroup (GPl σ J v) := fun v => match v with
    | .inl _ => ⊥
    | .inr v => Kp v
  haveI : ∀ v, CompleteSpace (fixedSub (R v).π (K v)) := fun v => (isClosed_fixedSub _ _).completeSpace_coe
  have hK : ∀ y : ∀ v, (R v).H, ∀ w, y (.inl w) ∈ fixedSub (R (.inl w)).π (K (.inl w)) := fun y w =>
    mem_fixedSub.2 fun k hk => by
      rw [Subgroup.mem_bot.1 hk, map_one, ContinuousLinearMap.one_apply]
  have key := mem_closure_span_of_orthogonal h (fun v => fixedSub (R v).π (K v)) ?_ x ?_
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_) key
    rintro _ ⟨y, hy, hyU, rfl⟩
    exact ⟨y, hy, fun v => mem_fixedSub.1 (hyU (.inr v)), rfl⟩
  · refine (Set.Finite.image Sum.inr hξ).subset ?_
    rintro (w | v) hv
    · exact absurd (hK ξ w) hv
    · exact ⟨v, fun e => hv (mem_fixedSub.2 e), rfl⟩
  · intro z hz v w hw
    obtain ⟨T, hT⟩ := exists_update_clm h hz v
    rw [← hT]
    refine inner_eq_zero_of_fixed (R v).isIrr.unitary (τ := fun g => π (embPl σ J v g))
      (fun g a b => inner_map_map hπ.unitary _ a b) T (fun g a => ?_) (K := K v) ?_ hw
    · rw [hT, hT, h.apply_embPl (SmallThetaModules.restr_update hz v a), Function.update_self, Function.update_idem]
    · rcases v with v | v
      · intro k hk
        rw [Subgroup.mem_bot.1 hk, map_one, map_one, ContinuousLinearMap.one_apply]
      · exact hx v

end GlobalTheory.FixedSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.LiftOntoGood

theorem mem_range_of_fixed {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (hsa : LinearMap.adjoint e = e) (hid : e * e = e) (hfix : ∀ y, e (th y) = th y)
    (hinj : ∀ v, e v = v → LinearMap.adjoint th v = 0 → v = 0) (x : Y) (hx : e x = x) : x ∈ LinearMap.range th := by
  have hcomp : e ∘ₗ th = th := LinearMap.ext hfix
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range th)]
  intro v hv
  have hv0 : LinearMap.adjoint th v = 0 := by
    refine ext_inner_left ℂ fun z => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hv _ (LinearMap.mem_range_self _ z)
  have h1 : LinearMap.adjoint th (e v) = 0 := by
    have e2 : LinearMap.adjoint th (e v) = LinearMap.adjoint (e ∘ₗ th) v := by
      rw [LinearMap.adjoint_comp, hsa, LinearMap.comp_apply]
    rw [e2, hcomp, hv0]
  have h2 : e (e v) = e v := by rw [← Module.End.mul_apply, hid]
  have h3 : e v = 0 := hinj (e v) h2 h1
  rw [← hx, ← LinearMap.adjoint_inner_left, hsa, h3, inner_zero_left]


set_option maxHeartbeats 1000000 in
theorem goodW_le_range : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp _ _ hU j
  have hM : R.toRealDat.IsModels := hC.base.models
  have hC3 := RealDat3.characterisation_of_weak hC hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hsa : LinearMap.adjoint (GlobalTheory.Hk3.eH R.toRealDat j) = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.LiftScalarL.adjoint_eH R.toRealDat hM hX j
  have hc : ∀ g, ∑ a, RealDat.eC (A := A3.A) (sg0 D A3.A) a * RealDat.eC (A := A3.A) (sg0 D A3.A) (a⁻¹ * g) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g := fun g => GlobalTheory.Hk3.conv_map_idem _ (idemOf_mul_self A3.A.X hX) (sg0 D A3.A) g
  have hidem : GlobalTheory.Hk3.eH R.toRealDat j * GlobalTheory.Hk3.eH R.toRealDat j = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.Hk3.sum_rep_idem _ _ hc
  have hinj := (hM.HW j (sg0 D A3.A)).1
  have hrange := (hM.HW j (sg0 D A3.A)).2.1
  have hfixth : ∀ y, GlobalTheory.Hk3.eH R.toRealDat j (R.thG j A3.A.μ0 y) = R.thG j A3.A.μ0 y := by
    intro y
    have hm := hC3.thP.thF_mem j A3.A.μ0 y
    rw [← hrange] at hm
    obtain ⟨x0, hx0⟩ := hm
    have e1 : R.thG j A3.A.μ0 y = GlobalTheory.Hk3.eH R.toRealDat j x0 := by
      apply hinj
      rw [hC3.thP.thG j A3.A.μ0 y, ← hx0, GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j x0]
    rw [e1, ← Module.End.mul_apply, hidem]
  have key := mem_range_of_fixed (R.thG j A3.A.μ0) (GlobalTheory.Hk3.eH R.toRealDat j) hsa hidem hfixth (hUp j A3.A.μ0)
  intro w hw
  have hw' : w ∈ LinearMap.range ((R.toCx3 F).w0C false j) := hw
  rw [GlobalTheory.LevelRange.range_w0C_eq R F hOk hC hU false j] at hw'
  obtain ⟨x, rfl⟩ : ∃ x : (R.HW j (sg0 D A3.A)).H, Tw.mk (twAt D.what₂.embLL A3.A.v0) x = w := ⟨w, rfl⟩
  have hgood : (R.HW j (sg0 D A3.A)).e x ∈
      R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := hw'
  have hfix : GlobalTheory.Hk3.eH R.toRealDat j x = x := by
    apply hinj
    rw [GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j]
    exact GlobalTheory.LiftScalarCompare.postOn_of_good hgood
  obtain ⟨y, hy⟩ := key _ hfix
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hC.phase j).1, norm_zero] at this
    exact one_ne_zero this
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y), ?_⟩
  show cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.μ0 ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y) = x
  rw [map_smul, smul_inv_smul₀ hne, hy]

end GlobalTheory.LiftOntoGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCuspidalMultiplicityTrace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

noncomputable section

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.OpTrace GlobalTheory.DiscreteSum ContinuousLinearMap
open scoped InnerProductSpace

theorem hasSum_trace_restrict {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : Type}
    {W : ι → Submodule ℂ K} [hW : ∀ i, CompleteSpace (W i)]
    (hs : IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ) {T : K →L[ℂ] K} (hT : IsTraceClass T)
    (hTW : ∀ i, ∀ x ∈ W i, T x ∈ W i) :
    (∀ i, IsTraceClass (T.restrict (hTW i))) ∧ Summable (fun i => ‖trace (T.restrict (hTW i))‖) ∧
      HasSum (fun i => trace (T.restrict (hTW i))) (trace T) := by
  let b : ∀ i, HilbertBasis (stdIndex (W i)) ℂ (W i) := fun i => stdBasis (H := W i)
  let v : (Σ i, stdIndex (W i)) → K := fun a => (W a.1).subtypeₗᵢ (b a.1 a.2)
  have ho : Orthonormal ℂ v := hs.OrthogonalFamily.orthonormal_sigma_orthonormal fun i => (b i).orthonormal
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine eq_zero_of_isHilbertSum hs fun i y hy => ?_
    have h1 := ((b i).hasSum_repr ⟨y, hy⟩).mapL ((innerSL ℂ x).comp (W i).subtypeL)
    have h2 : ∀ j, ((innerSL ℂ x).comp (W i).subtypeL) ((b i).repr ⟨y, hy⟩ j • b i j) = 0 := fun j => by
      have h3 : ⟪v ⟨i, j⟩, x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨⟨i, j⟩, rfl⟩)
      have h4 : ⟪x, (b i j : K)⟫_ℂ = 0 := inner_eq_zero_symm.1 h3
      simp [inner_smul_right, h4]
    have h5 : ⟪x, y⟫_ℂ = 0 := by
      have := h1.unique (hasSum_zero.congr_fun fun j => (h2 j))
      simpa using this
    exact inner_eq_zero_symm.1 h5
  let e : HilbertBasis (Σ i, stdIndex (W i)) ℂ K := HilbertBasis.mkOfOrthogonalEqBot ho hsp
  have he : ∀ a, e a = v a := fun a => by simp [e]
  have hR : ∀ i, (T.restrict (hTW i)) = (W i).orthogonalProjection ∘L T ∘L (W i).subtypeL := fun i => by
    ext x
    simp [Submodule.orthogonalProjection_mem_subspace_eq_self (K := W i) ⟨_, hTW i x x.2⟩]
  have htc : ∀ i, IsTraceClass (T.restrict (hTW i)) := fun i => by
    rw [hR i]; exact hT.comp_comp _ _
  have hterm : ∀ a : Σ i, stdIndex (W i), ⟪e a, T (e a)⟫_ℂ = ⟪b a.1 a.2, T.restrict (hTW a.1) (b a.1 a.2)⟫_ℂ :=
    fun a => by rw [he]; rfl
  have hsum := hT.hasSum_trace e
  have hnorm := hT.summable_norm e
  simp only [hterm] at hsum hnorm
  refine ⟨htc, ?_, hsum.sigma fun i => (htc i).hasSum_trace (b i)⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hnorm.sigma
  rw [← ((htc i).hasSum_trace (b i)).tsum_eq]
  exact norm_tsum_le_tsum_norm ((htc i).summable_norm (b i))

end GlobalTheory.CuspTraceSum

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.OpTrace GlobalTheory.DiscreteSum GlobalTheory.AutMult GlobalTheory.AutomorphicL2Unitary MeasureTheory

theorem hasSum_multIn_repTrace {G K : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ρ : G →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) (hD : IsDiscreteSum ρ) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hT : IsTraceClass (repOp ρ μ f)) :
    (∀ c : UDual G, multIn c.rep.π ρ ⊤ ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧
      (Summable fun c : UDual G => ‖((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧
      HasSum (fun c : UDual G => ((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f) (trace (repOp ρ μ f)) := by
  obtain ⟨⟨ι, W, hWi, hs⟩, hfin⟩ := hD
  haveI : ∀ i, CompleteSpace (W i) := fun i => (hWi i).1.completeSpace
  have hR : IsRepOp ρ μ f (repOp ρ μ f) := hρ.isRepOp hf hfs
  have hTW : ∀ i, ∀ x ∈ W i, repOp ρ μ f x ∈ W i := fun i x hx => (hWi i).1.map_mem_of_isRepOp hR hx
  obtain ⟨htc, hsn, hsum⟩ := hasSum_trace_restrict hs hT hTW
  have hrest : ∀ i, repOp (hWi i).1.rep μ f = (repOp ρ μ f).restrict (hTW i) := fun i =>
    ContinuousLinearMap.ext fun x => Subtype.ext (((hWi i).1.coe_repOp_rep hR).2 x)
  let cls : ι → UDual G := fun i => (⟨W i, (hWi i).1.rep, isIrrUnitary_rep hρ (hWi i)⟩ : IrrU G).cl
  have hcls : ∀ c i, cls i = c ↔ IsCopy c.rep.π ρ (W i) := fun c i => by
    conv_lhs => rw [← UDual.cl_rep c]
    rw [IrrU.cl_eq_iff]
    exact ⟨fun h => ⟨(hWi i).1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  have htr : ∀ c i, cls i = c →
      IsTraceClass (repOp c.rep.π μ f) ∧ repTrace c.rep.π μ f = trace ((repOp ρ μ f).restrict (hTW i)) := by
    intro c i hi
    obtain ⟨_, e, he⟩ := (hcls c i).1 hi
    have h2 : IsTraceClass (repOp (hWi i).1.rep μ f) := by rw [hrest]; exact htc i
    obtain ⟨h3, h4⟩ := ((hWi i).1.isUnitaryRep hρ).repTrace_eq_of_equiv c.rep.isIrr.unitary hf hfs
      e.symm.toContinuousLinearEquiv (fun g x => by
        apply e.injective
        rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, he, LinearIsometryEquiv.apply_symm_apply,
          LinearIsometryEquiv.apply_symm_apply]) h2
    refine ⟨h3, h4.trans ?_⟩
    rw [repTrace, hrest]
  have hmult : ∀ c : UDual G, (cls ⁻¹' {c}).Finite ∧ multIn c.rep.π ρ ⊤ = (cls ⁻¹' {c}).ncard := by
    intro c
    obtain ⟨h1, h2⟩ := multIn_eq_ncard hρ c.rep.isIrr (hfin c.rep) hWi hs
    have e : cls ⁻¹' {c} = {i | IsCopy c.rep.π ρ (W i)} := Set.ext fun i => hcls c i
    rw [e]
    exact ⟨h1, h2⟩
  have hfib : ∀ c : UDual G, ∑' b : ↑(cls ⁻¹' {c}), trace ((repOp ρ μ f).restrict (hTW b)) =
      ((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f := by
    intro c
    rw [tsum_congr fun b : ↑(cls ⁻¹' {c}) => (htr c b b.2).2.symm, tsum_const, nsmul_eq_mul, (hmult c).2,
      Cardinal.toNat_natCast, Nat.card_coe_set_eq]
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · rw [(hmult c).2] at hc
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (by exact_mod_cast hc)
    exact (htr c i hi).1
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_)
      (hsn.hasSum.tsum_fiberwise cls).summable
    rw [← hfib]
    exact norm_tsum_le_tsum_norm (hsn.subtype _)
  · exact (hsum.tsum_fiberwise cls).congr_fun fun c => (hfib c).symm

end GlobalTheory.CuspTraceSum

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.DiscreteSum

theorem hasSum_mCusp_repTrace : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, (∀ c : UDual (GA D V), mCusp V μ c.rep.π ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧ (Summable fun c : UDual (GA D V) => ‖((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧ HasSum (fun c : UDual (GA D V) => ((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f) (trace (RcuspOp V μ f)) := by
  intro hP D V μ _ _ f hf
  have hfc := continuous_of_mem_ccAd hf
  have h := hasSum_multIn_repTrace (isUnitaryRep_Rcusp V μ)
    (Published.cuspDiscreteDecomposition_of_traceClass hP D V μ) μ hfc.1 hfc.2 (hP D V μ f hf)
  have e : ∀ c : UDual (GA D V), mCusp V μ c.rep.π = multIn c.rep.π (Rcusp V μ) ⊤ := fun c =>
    (multIn_rep (isSubrep_L2cusp V μ)).symm
  simp only [e]
  exact h

end GlobalTheory.CuspTraceSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslate
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

open scoped Pointwise

namespace GlobalTheory.OpConv

theorem isIntegralOp_conv_and_translate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth σ → ∀ f ∈ GlobalTheory.SplitWeil.SB G, ∀ f' ∈ GlobalTheory.SplitWeil.SB G, ∀ A B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f' B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (conv μ f f') (A ∘ₗ B) ∧ ∀ g : G, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun x => f' (g⁻¹ * x)) (σ g ∘ₗ B) := by
  intro G _ _ _ _ _ _ μ _ W _ _ σ hσ f hf f' hf' A B hA hB
  have hfc : Continuous f := hf.1.continuous
  have hf'c : Continuous f' := hf'.1.continuous
  have horb : ∀ (l : Module.Dual ℂ W) (v : W), Continuous fun y => l (σ y v) := fun l v =>
    ((hσ.isLocallyConstant_orbit v).comp l).continuous
  refine ⟨fun v l => ?_, fun g v l => ?_⟩
  ·
    have h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') →
        f x * f' (x⁻¹ * y) = 0 := by
      intro x y h
      by_contra hne
      have h1 := subset_tsupport f (left_ne_zero_of_mul hne)
      have h2 := subset_tsupport f' (right_ne_zero_of_mul hne)
      exact h ⟨h1, x, h1, _, h2, by simp⟩
    have hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f')) := hf.2.prod (hf.2.mul hf'.2)
    have hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := by
      refine continuousOn_univ.1 (continuousOn_integral_of_compact_support
        (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hf.2 ?_ fun y x _ hx => ?_)
      · exact ((hfc.comp continuous_snd).mul
          (hf'c.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ :=
      HasCompactSupport.intro (hf.2.mul hf'.2) fun y hy => by
        simp [fun x => h0 x y fun h => hy h.2]
    have hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      ((hfc.comp continuous_fst).mul (hf'c.comp (continuous_fst.inv.mul continuous_snd))).mul
        ((horb l v).comp continuous_snd)
    have hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]
    have hconv : conv μ f f' = fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := rfl
    rw [hconv]
    refine ⟨(hcont.mul (horb l v)).integrable_of_hasCompactSupport (hcs.mul_right), ?_⟩
    have hx : ∀ x, l (σ x (B v)) = ∫ y, f' (x⁻¹ * y) * l (σ y v) ∂μ := by
      intro x
      have := (hB v (l ∘ₗ σ x)).2
      simp only [LinearMap.comp_apply] at this
      rw [this, ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) * l (σ y v)) x]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp [map_mul, Module.End.mul_apply]
    rw [LinearMap.comp_apply, (hA (B v) l).2]
    simp_rw [hx, ← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap_of_hasCompactSupport hF hFc]
    simp_rw [integral_mul_const]
  ·
    have hx : ∀ y, f' y * l (σ g (σ y v)) = (fun x => f' (g⁻¹ * x) * l (σ x v)) (g * y) := by
      intro y
      simp [map_mul, Module.End.mul_apply]
    have hc : Continuous fun x => f' (g⁻¹ * x) * l (σ x v) :=
      (hf'c.comp (continuous_const.mul continuous_id)).mul (horb l v)
    have hs : HasCompactSupport fun x => f' (g⁻¹ * x) * l (σ x v) :=
      ((hf'.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹))).mul_right
    refine ⟨hc.integrable_of_hasCompactSupport hs, ?_⟩
    have := (hB v (l ∘ₗ σ g)).2
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.comp_apply, this,
      ← integral_mul_left_eq_self (fun x => f' (g⁻¹ * x) * l (σ x v)) g]
    exact integral_congr_ae (.of_forall fun y => hx y)

end GlobalTheory.OpConv
end

