module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelTensorValues
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpan

theorem exists_form {G Γ W X Y : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [AddCommGroup Y]
    [Module ℂ Y] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (h : G)
    (hfin : Finite (Bridge.stab ι J h)) (w : W) (p : X → G) (Φ : X → W →ₗ[ℂ] Y) (v : Y)
    (law : ∀ x γ (k : J), p x = ι γ * h * k → Φ x (ρ γ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • v) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, ∃ N : G → ℕ, (∀ x, Φ x (f (p x)) = (N (p x) : ℂ) • v) ∧
      ∀ γ (k : J), N (ι γ * h * k) ≠ 0 := by
  let S : G → Set Γ := fun x => {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}
  have hS : ∀ x, (S x).Finite := by
    intro x
    rcases (S x).eq_empty_or_nonempty with e | ⟨γ₀, h₀⟩
    · rw [e]; exact Set.finite_empty
    · refine (Set.finite_range fun δ : Bridge.stab ι J h => γ₀ * δ.1).subset fun γ hγ => ⟨⟨γ₀⁻¹ * γ, ?_⟩, by simp⟩
      rw [Bridge.mem_stab]
      have := J.mul_mem h₀ (J.inv_mem hγ)
      convert this using 1
      simp only [map_mul, map_inv]
      group
  let term : G → Γ → W := fun x γ =>
    if hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J then ((χ ⟨_, hm⟩ : ℂˣ) : ℂ) • ρ γ w else 0
  have hsupp : ∀ x, Function.support (term x) ⊆ (hS x).toFinset := by
    intro x γ hγ
    by_contra hn
    have : ¬ h⁻¹ * (ι γ)⁻¹ * x ∈ J := fun hm => hn ((hS x).mem_toFinset.2 hm)
    exact hγ (dif_neg this)
  have hterm : ∀ δ x (k : J) γ, term (ι δ * x * k) (δ * γ) = ((χ k : ℂˣ) : ℂ) • ρ δ (term x γ) := by
    intro δ x k γ
    have e : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
      simp only [map_mul]; group
    by_cases hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J
    · have hm' : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := e ▸ J.mul_mem hm k.2
      have e' : (⟨_, hm'⟩ : J) = ⟨_, hm⟩ * k := Subtype.ext e
      simp only [term, dif_pos hm, dif_pos hm']
      rw [e', map_mul χ, map_mul ρ, map_smul, smul_smul, Units.val_mul, mul_comm]
      rfl
    · have hm' : ¬ h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := fun hh =>
        hm ((J.mul_mem_cancel_right k.2).1 (e ▸ hh))
      simp only [term, dif_neg hm, dif_neg hm', map_zero, smul_zero]
  refine ⟨fun x => ∑ᶠ γ, term x γ, ?_, fun x => (hS x).toFinset.card, fun x => ?_, fun γ k => ?_⟩
  · intro δ x k
    show ∑ᶠ γ, term (ι δ * x * k) γ = ((χ k : ℂˣ) : ℂ) • ρ δ (∑ᶠ γ, term x γ)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
    have hf : (Function.support (term x)).Finite := (hS x).toFinset.finite_toSet.subset (hsupp x)
    have := (((χ k : ℂˣ) : ℂ) • ρ δ).toAddMonoidHom.map_finsum hf
    refine Eq.trans ?_ this.symm
    exact finsum_congr fun γ => hterm δ x k γ
  · show Φ x (∑ᶠ γ, term (p x) γ) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [finsum_eq_sum_of_support_subset _ (hsupp _), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hm : h⁻¹ * (ι γ)⁻¹ * p x ∈ J := (hS _).mem_toFinset.1 hγ
    simp only [term, dif_pos hm]
    rw [map_smul, law x γ ⟨_, hm⟩ (by simp only []; group), smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  · refine (Finset.card_pos.2 ⟨γ, (hS _).mem_toFinset.2 ?_⟩).ne'
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    convert k.2 using 1
    group

theorem law_abstract {H G' W X : Type} [Group H] [Group G'] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (L : W →ₗ[ℂ] (X → ℂ))
    (x h γ k a : H) (hu : h⁻¹ * γ⁻¹ * x = k * a) (c : ℂ) (hk : ρ k⁻¹ = 1) (hh : ρ h⁻¹ = 1) (hx : ρ x = 1)
    (hLk : ∀ w, om (k, 1) (L w) = c • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (w : W) (g : G') :
    om (x, g) (L (ρ γ w)) = om (γ, 1) (c • om (h, g) (L w)) := by
  have e4 : x = γ * h * k * a := by rw [mul_assoc _ k, ← hu]; group
  have e5 : (x, g) = ((γ, 1) : H × G') * ((h, g) * ((k, 1) * (a, 1))) := by
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e4]; simp only [mul_assoc]
  have e6 : ρ a * ρ γ = 1 := by
    have : a = k⁻¹ * h⁻¹ * γ⁻¹ * x := by rw [e4]; group
    rw [this, map_mul, map_mul, map_mul, hx, hk, hh, one_mul, one_mul, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [e5, map_mul om, Module.End.mul_apply, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa,
    ← Module.End.mul_apply (ρ a), e6, Module.End.one_apply, hLk, map_smul]

theorem map_quot {H G : Type} [Group H] [Group G] (p : H →* G) (x h γ : H) (k : G) (e : p x = p γ * p h * k) :
    p (h⁻¹ * γ⁻¹ * x) = k := by
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

theorem kernel_law {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (c : CoefA S) (hc : c.Is) (J : Subgroup (Bridge.Gf S)) (χ : J →* ℂˣ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ J, ∀ w, om (k, 1) (Λ w) = ((χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {h x : GA D S} (hh : h ∈ GfC S) (hx : x ∈ GfC S) (γ : GQ S) (k : J)
    (e : fin S x = Bridge.ratF S γ * fin S h * k) (w : c.W) (g : GA D T) :
    thetaKO om x g (Λ (c.ρ γ w)) = ((χ k : ℂˣ) : ℂ)⁻¹ * thetaKO om h g (Λ w) := by
  refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S (h⁻¹ * (γ : GA D S)⁻¹ * x)).elim fun k' hk0 => hk0.2.elim fun a ha0 => ?_
  have hk := hk0.1
  have ha := ha0.1
  have e2 : fin S k' = k := ha0.2.2.trans (map_quot (finHom S).rangeRestrict x h γ k e)
  have hk' : fin S k' ∈ J := by rw [e2]; exact k.2
  have e3 : (⟨fin S k', hk'⟩ : J) = k := Subtype.ext e2
  have h1 : ∀ w, om (k', 1) (Λ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • Λ w := fun w =>
    (hΛk k' hk hk' w).trans (congrArg (fun z : J => ((χ z : ℂˣ) : ℂ)⁻¹ • Λ w) e3)
  have h2 := law_abstract om c.ρ Λ x h γ k' a ha0.2.1 _ (hc.1 _ (inv_mem hk)) (hc.1 _ (inv_mem hh)) (hc.1 _ hx)
    h1 (hΛa a ha) w g
  refine (congrFun h2 0).trans ?_
  have h3 := hom.om_aut γ γ.2 1 (one_mem _) _ (hom.om_pres (h, g) _ (hΛ w))
  refine (congrFun ((om ((γ : GA D S), 1)).map_smul _ _) 0).trans ?_
  exact congrArg (fun z : ℂ => ((χ k : ℂˣ) : ℂ)⁻¹ * z) h3

theorem ne_zero_of_coset {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (N : G → ℕ) (h y : G)
    (hN : ∀ γ (k : J), N (ι γ * h * k) ≠ 0) (γ : Γ) (u : J) (e : h = ι γ * y * u) : N y ≠ 0 := by
  have := hN γ⁻¹ u⁻¹
  rwa [e, map_inv, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left] at this

theorem coeff_ne_zero {I : Type} [Fintype I] (r : ℕ) (s N : I → ℕ) (hr : r ≠ 0) (hs : ∀ i, s i ≠ 0) (i₀ : I)
    (hN : N i₀ ≠ 0) : ∑ i, (r : ℂ)⁻¹ * (s i : ℂ)⁻¹ * (N i : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < ∑ i, (r : ℝ)⁻¹ * (s i : ℝ)⁻¹ * (N i : ℝ) :=
    Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, by have := hs i₀; positivity⟩
  have h' := Complex.ofReal_ne_zero.2 h.ne'
  push_cast at h'
  exact h'

theorem exists_integral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : MeasureTheory.Measure (GA D S)} {𝓕 : Set (GA D S)}
    (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (Cl : Type) [Fintype Cl] (y : Cl → GA D S)
    (hy : Bridge.IsReps (Bridge.ratF S) (levEnv S β L).J (fun k => fin S (y k)))
    (hyf : ∀ k, Finite (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k))))
    (hh : ∀ k, y k ∈ GfC S) {h : GA D S} (hf : h ∈ GfC S) (w : c.W) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ, ∃ a : ℂ, a ≠ 0 ∧
      ∀ g, ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = a * thetaKO om h g (Λ w) := by
  let Φ : Cl → c.W →ₗ[ℂ] (GA D T → ℂ) := fun k =>
    LinearMap.pi fun g => LinearMap.proj (0 : WO S T) ∘ₗ om (y k, g) ∘ₗ Λ
  have hex := exists_form (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ (fin S h)
    (GlobalTheory.SplitReps.finite_stab_of_reps _ le_rfl hy hyf _) w (fun k => fin S (y k)) Φ
    (fun g => thetaKO om h g (Λ w)) (fun x γ k e => funext fun g =>
      kernel_law hom c hc _ _ Λ hΛ hΛa hΛk hf (hh x) γ k e w g)
  refine hex.elim fun f hf0 => hf0.2.elim fun N hN => ?_
  have hrel : (levEnv S β L).J.relIndex (levEnv S β L).J ≠ 0 := by simp
  have h0 : ∃ k, N (fin S (y k)) ≠ 0 := by
    refine (hy (fin S h)).exists.elim fun k hk => hk.elim fun γ hγ => hγ.elim fun u e => ⟨k, ?_⟩
    exact ne_zero_of_coset (Bridge.ratF S) _ N _ _ hN.2 γ u e
  refine h0.elim fun k₀ hk₀ => ⟨f, hf0.1, _, coeff_ne_zero _
    (fun k => Nat.card (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k)))) (fun k => N (fin S (y k))) hrel
    (fun k => (have := hyf k; Nat.card_pos.ne')) k₀ hk₀, fun g => ?_⟩
  refine (GlobalTheory.LiftUnfold.integral_theta hom hs hp c hc β L hL hf0.1 Λ hΛ hΛa hΛk hν _ Cl y le_rfl hrel hy hh g).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : thetaKO om (y k) g (Λ (f (fin S (y k)))) = (N (fin S (y k)) : ℂ) * thetaKO om h g (Λ w) :=
    congrFun (hN.1 k) g
  rw [h1, ← mul_assoc]

theorem mem_span_of_linear {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (j : I → H)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (T : H →ₗ[ℂ] Y) (y : H) (a : ℂ) (ha : a ≠ 0) (v : Y) (e : T y = a • v) :
    v ∈ Submodule.span ℂ (Set.range fun x => T (j x)) := by
  have h1 : T y ∈ (Submodule.span ℂ (Set.range j)).map T := Submodule.mem_map_of_mem (hj ▸ Submodule.mem_top)
  rw [Submodule.map_span, ← Set.range_comp, e] at h1
  exact (Submodule.smul_mem_iff _ ha).1 h1

theorem span_eq_top_of_model {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (e : H →ₗ[ℂ] Y)
    (he : Function.Injective e) (j : I → H) (x : I → Y) (hj : ∀ i, e (j i) = x i)
    (hx : Submodule.span ℂ (Set.range x) = LinearMap.range e) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine Submodule.map_injective_of_injective he ?_
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, ← hx]
  exact congrArg (fun z => Submodule.span ℂ (Set.range z)) (funext hj)

end GlobalTheory.KernelSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubini
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRoute

theorem lift_eq_integral_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  have hK1 : ∀ g, IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := _root_.GlobalTheory.FunObj.routeBig_kerBig_integrableOn hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hmeas : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := _root_.GlobalTheory.BigRoute.aestronglyMeasurable_kerBig hL W B ρ t i j M hM Θ Θ' hΘ g₁
  have hinv : ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := _root_.GlobalTheory.BigRouteInv.kerBig_rat_mul hL W B ρ t i j Θ Θ' hΘ g₁
  have hgrow : GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)),
      ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := _root_.GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hRD : GlobalTheory.Grow.RapidDec _ F := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  have hkm : AEStronglyMeasurable (fun g => ((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖
      ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)) ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas.norm.integral_prod_right'
  obtain ⟨C, A, hCA⟩ := hgrow
  have hkb : ∀ g, ‖((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)‖ ≤
      C * 2 ^ A * GlobalTheory.Grow.quotHeight _ g ^ A := fun g => by
    rw [Complex.norm_real]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (fun γ hγ g => by simp only [hinv γ hγ g]) hCA g
  have hkF := hRD.integrableOn_mul_of_le hH hfd hkm hkb
  have hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => F p.1 * kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
    have hFm : AEStronglyMeasurable F ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
      hRD.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        F p.1 * kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
          ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) :=
      hFm.comp_fst.mul hmeas
    refine (integrable_prod_iff hm2).2
      ⟨.of_forall fun g => (hK1 g).const_mul (F g), ?_⟩
    refine hkF.norm.congr (.of_forall fun g => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  refine ⟨Filter.Eventually.of_forall hK1, ?_⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid i (j + 1)) =
      Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))) := by
    intro u
    have hint : ∀ d ∈ Θ.support, IntegrableOn (fun g => W.kerA (.right i (j + 1)) d.1.2 g u * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd => (hA d hd).1.2 u
    have e : ∀ g, F g * kerBig W Θ g g₁ u = ∑ d ∈ Θ.support,
        Θ d * (W.kerA (.down t (i + 1) j) d.2 u g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * F g)) := by
      intro g
      simp only [kerBig, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun d hd => ((hint d hd).const_mul _).const_mul _]
    simp only [integral_const_mul, Finsupp.sum]
  have hint2 : ∀ d ∈ Θ.support, Integrable (fun u => W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1)))
      ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := fun d hd => (hA d hd).2 g₁
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)), kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid (i + 1) (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid (i + 1) (j + 1)) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), (Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))))
        ∂M.ν (.grid (i + 1) (j + 1)) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]
        simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl

end GlobalTheory.BigRoute

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformAdelicSchwartzHasFiniteLevelCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaLevelF

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


set_option maxHeartbeats 2000000 in
theorem infIdem_smul (z : AF F ⊗[F] E) :
    pairA F 1 0 • z = TensorProduct.map (GlobalTheory.ThetaLevel.infIncl F) LinearMap.id
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' =>
    rw [smul_add (pairA F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) z z',
      map_add]

theorem finIdem_smul (z : AF F ⊗[F] E) (hz : infPartF F E z = 0) : pairA F 0 1 • z = z := by
  have h1 : pairA F 0 1 + pairA F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := infIdem_smul z
  rw [show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = 0 from hz, map_zero] at h2
  calc pairA F 0 1 • z = pairA F 0 1 • z + pairA F 1 0 • z := by rw [h2, add_zero]
    _ = z := by rw [← add_smul, h1, one_smul]

theorem e_eq_fin {nS nT : ℕ} {B : WOF F E nS nT → WOF F E nS nT → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (u : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) :
    co.e u = ((fun i => pairA F 0 ((co.e u).1 i).2), (fun i => pairA F 0 ((co.e u).2 i).2)) := by
  have hu' : pairA F 0 1 • u = u := by
    ext a b
    exact finIdem_smul (u a b) (congrFun (congrFun hu a) b)
  have h2 := congrArg co.e hu'
  rw [LinearEquiv.map_smul] at h2
  conv_lhs => rw [← h2]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact Prod.ext (zero_mul _) (one_mul _)
  · exact Prod.ext (zero_mul _) (one_mul _)


set_option maxHeartbeats 1000000 in
theorem thetaTr_levelF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  obtain ⟨K, hK⟩ := GlobalTheory.ThetaLevel.schr_fin_fix F B.ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  let f2 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (WOF F E nS nT) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr B.ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin co u hinf]
    exact hK _ hu.1 _ hu.2
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e w) Φ)
  rw [map_add (f := _)]
  have h1 : GlobalTheory.WeilM.schr B.ψ (co.e w + co.e u) Φ = fun x =>
      B.ψ (-(⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr B.ψ (co.e w) (GlobalTheory.WeilM.schr B.ψ (co.e u) Φ) x :=
    funext (GlobalTheory.ThetaLevel.schr_add B.ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : symplOHF σ JS JT ξ₀ w u =
      ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [symplOHF, GlobalTheory.TransportF.symplOF_eq_symp hA hB, co.form]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaLevelF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobalStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_lattice_invariant_schwartz_global : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  first | exact @GlobalTheory.VacAvg.avg_eigen | exact GlobalTheory.VacAvg.avg_eigen | (intros; apply GlobalTheory.VacAvg.avg_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreservesStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_unitary_action_preserves : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ →
    ∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.LocalUnitaryL2.lintegral_eq | exact GlobalTheory.LocalUnitaryL2.lintegral_eq | (intros; apply GlobalTheory.LocalUnitaryL2.lintegral_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricAction
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lUnif_topR_of_geoAct : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  intro hC hV D G _ _ Pl0 T0 A T _ R κ v₀ hI hM hT hpb hκ hn hg
  exact lUnif_topN T R κ v₀ (nTop T κ) (hasB_nTop T hT.laws κ) hM.HW
    (_root_.GlobalTheory.UnifAll.unif_all hC hV D G Pl0 T0 A T R κ v₀ hI hM hT hpb hκ hn) hg

end GlobalTheory.HolDict
end

