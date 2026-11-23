module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryUniformisationBaseChangeInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepBC


set_option maxHeartbeats 1600000 in
theorem exists_pelUnif_baseChange_of_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → ∃ (t₁ : SAB H (Sp V₁)) (P₁ : PELUnif (maximalIdeal V₁) t₁) (p : IsPullDeg ρ P.D.toPre P₁.D.toPre), GenOf Xo c (spMap fK ≫ y) t₁ ∧ (∀ (a : 𝓞 E) x, p.xe (a • x) = a • p.xe x) ∧ ∀ x r, Formalism.L2.Pj.PsiCoord P.D.toPre (p.xe x) r → ∃ w : V₁ˣ, Formalism.L2.Pj.PsiCoord P₁.D.toPre x (w * ρ r) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV t y P hG V₁ _ _ _ ρ fK hV₁ hρ hl hfK
  have hR : GlobalTheory.Mum.Base V := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  have hR₁ : GlobalTheory.Mum.Base V₁ := ⟨⟨hV₁.1, inferInstance, hV₁.2.1, hV₁.2.2.1⟩, hV₁.2.2.2⟩
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨Wo, hWo, ⟨hψ⟩⟩ := h5.psiOnExists V (maximalIdeal V) hR.1 P.D
  let WS : Set (PrimeSpectrum V) := (Wo : Set (Sp V))
  have hWS : IsOpen WS := Wo.isOpen
  have hbot : (⊥ : PrimeSpectrum V) ∈ WS := by
    have := hWo
    rw [genericPoint_eq_bot_of_affine] at this
    exact this
  obtain ⟨_, ⟨f, rfl⟩, hf, hfW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hWS
  have hf0 : f ≠ 0 := by
    intro e
    apply hf
    rw [e]
    show (0 : V) ∈ (⊥ : PrimeSpectrum V).asIdeal
    exact Ideal.zero_mem _
  have hψW : ∀ x, PsiUnitOn P.D.toPre x (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
    intro x j U hU hUW
    exact GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn V P.D.toPre Wo hψ x j U hU (hUW.trans hfW)
  have hρf : ρ f ≠ 0 := fun e => hf0 (hρ (e.trans (map_zero ρ).symm))
  obtain ⟨t₁, P₁, p, ⟨m₀⟩, hlin, -⟩ := GlobalTheory.LocalPull.exists_pelUnif_pull V V₁ hR hR₁ t P ρ hl f hρf hψW
  refine ⟨t₁, P₁, p, ?_, hlin, fun x r hr => GlobalTheory.PelCoordPull.psiCoord_pull p x r hr⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hG
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨e⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) e⟩
  have sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
      ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, semiPull f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
    have h := isGrpPullback_pullback t.G f
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
        pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
        pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
      Over.OverMorphism.ext (by
        show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP, cub, sym, adj, prim, n, -⟩ := sabPull CubePf.cubePull (jK V₁) t₁
  let tK₁ : SAB H (Sp (FractionRing V₁)) := ⟨(Over.pullback (jK V₁)).obj t₁.G, semiPull _ t₁.G t₁.semi,
    OAct.pullback _ t₁.G t₁.act, PP, cub, sym, adj, prim⟩
  have n' : SABMap tK₁ t₁ (jK V₁) := n
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ t t₁ tK₁ _ _ m₀ n'
  have sq : jK V₁ ≫ spMap ρ = spMap fK ≫ jK V := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact (hfK a).symm
  rw [sq] at b
  obtain ⟨c', -⟩ := sabCancel pullCubCancel E H _ _ _ t tK tK₁ _ _ m₁ b
  obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tK tK₁ _ _ m₂ c'
  refine ⟨tK₁, ⟨n'⟩, ⟨?_⟩⟩
  rw [Category.assoc]
  exact d

end GlobalTheory.USepBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorMapsIntoIdealOfNotOntoMod
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

open scoped TensorProduct

private theorem finite_projective_of_free_int (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N] :
    Module.Finite (𝓞 E) N ∧ Module.Projective (𝓞 E) N := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) N
  haveI : Module.IsTorsionFree (𝓞 E) N := by
    refine Module.isTorsionFree_iff_smul_eq_zero.2 fun a x hax => ?_
    by_contra hk
    push_neg at hk
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    have h0 : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hk.1
    have h1 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul, hax, smul_zero]
    exact hk.2 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast h0))
  haveI : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

private theorem finrank_quot_tensor {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    [Module.Finite O N] [Module.Projective O N] (I : Ideal O) [I.IsMaximal] :
    Module.finrank (O ⧸ I) ((O ⧸ I) ⊗[O] N) = Module.finrank O N := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := O) (M := N) (S := O ⧸ I) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
  exact h1

private theorem one_tmul_eq_zero_iff {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (x : N) :
    (1 : O ⧸ I) ⊗ₜ[O] x = 0 ↔ x ∈ I • (⊤ : Submodule O N) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul N I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

private theorem one_tmul_surjective {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O)
    (t : (O ⧸ I) ⊗[O] N) : ∃ x : N, (1 : O ⧸ I) ⊗ₜ[O] x = t := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.quotTensorEquivQuotSMul N I t)
  refine ⟨x, (TensorProduct.quotTensorEquivQuotSMul N I).injective ?_⟩
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, hx]

theorem exists_ker_vec_of_not_onto_mod {O P X : Type} [CommRing O] [IsDomain O] [AddCommGroup P] [Module O P]
    [Module.Finite O P] [Module.Projective O P] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (f : P →ₗ[O] X) (hr : Module.finrank O P = Module.finrank O X) (I : Ideal O)
    (hI : I.IsMaximal) (hi : LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≠ ⊤) :
    ∃ v : P, f v ∈ I • (⊤ : Submodule O X) ∧ ∃ ℓ : P →ₗ[O] O, ℓ v ∉ I := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field _
  have hns : ¬ Function.Surjective (f.baseChange (O ⧸ I)) := fun hs => hi <| eq_top_iff.2 fun x _ => by
    obtain ⟨t, ht⟩ := hs (1 ⊗ₜ x)
    obtain ⟨v, rfl⟩ := one_tmul_surjective I t
    rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub, one_tmul_eq_zero_iff] at ht
    have : x = f v - (f v - x) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left ⟨v, rfl⟩) (Submodule.mem_sup_right ht)
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_quot_tensor, finrank_quot_tensor, hr]), injective_iff_map_eq_zero] at hns
  push_neg at hns
  obtain ⟨t, ht, ht0⟩ := hns
  obtain ⟨v, rfl⟩ := one_tmul_surjective I t
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at ht
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ I) ht0
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property I.mkQ
    ((g.restrictScalars O).comp (TensorProduct.mk O (O ⧸ I) P 1)) I.mkQ_surjective
  refine ⟨v, ht, ℓ, fun hv => hg ?_⟩
  have := LinearMap.congr_fun hℓ v
  exact this.symm.trans ((Submodule.Quotient.mk_eq_zero I).2 hv)

theorem IsOpp.exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 := by
  intro E _ _ _ H D X _ _ _ _ y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  obtain ⟨_, _⟩ := finite_projective_of_free_int E Z'
  obtain ⟨_, _⟩ := finite_projective_of_free_int E X
  have hrank : Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) X := by
    have := h.finrank_int_eq
    rw [GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z'] at this
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos this).trans hr
  refine exists_ker_vec_of_not_onto_mod (y.comp Z'.subtype) hrank 𝔭 h𝔭 ?_
  rwa [LinearMap.range_comp, Submodule.range_subtype]

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.GMem

theorem exists_yy : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (mu : X), ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 mu
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  have hpow : f p ^ (X₁.S.r * X₁.S.N) = 1 := (hx w hw).1
  let z := pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p)
  have hz : z ^ (X₁.S.r * X₁.S.N) = 1 := by
    simp only [z]
    rw [← map_pow, hpow, map_one]
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg (fun q => q.left) ha
  simp only [Over.comp_left, Over.homMk_left] at e
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK := by
    simp [spMap, jFK, ← Spec.map_comp]
  rw [e2]
  exact e.symm

end GlobalTheory.GSep.GMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePointsJoinedBySpecialisationChain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem fibre_chain : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  intro X₁ z₁ Y πY hZH y y' hy hy'
  obtain ⟨U₀, EE, -, -, -, hHom, hProp⟩ := hZH
  obtain ⟨U, hU, hiso⟩ := GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M πY hHom
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  haveI := X₁.M.lft
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := Y.s) (U := Set.univ) isOpen_univ isCompact_univ
    simpa using this
  haveI : IsNoetherian Y.Z := {}
  haveI : IsProper πY := hProp
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁.M.Z := (GlobalTheory.isNormalScheme_iff_pred _).1 X₁.normal
  have hc := GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z πY hN U hU hiso z₁
  have hS : ∀ x s, s ∈ πY.base ⁻¹' {z₁} → x ⤳ s → x ∈ closure (πY.base ⁻¹' {z₁}) → x ∈ πY.base ⁻¹' {z₁} := by
    intro x s hs hxs hx
    have h1 : πY.base x ⤳ z₁ := by
      have := hxs.map πY.base.hom.continuous
      rwa [show πY.base s = z₁ from hs] at this
    have h2 : z₁ ⤳ πY.base x := by
      rw [specializes_iff_mem_closure]
      have hcont := πY.base.hom.continuous
      have : closure (πY.base ⁻¹' {z₁}) ⊆ πY.base ⁻¹' closure {z₁} :=
        closure_minimal (Set.preimage_mono subset_closure) (isClosed_closure.preimage hcont)
      exact this hx
    exact (h1.antisymm h2).eq
  exact GlobalTheory.SpecChain.eqvGen_of_isPreconnected _ hc hS y hy y' hy'

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixIsUnitAdaptedBasis
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobUnit

theorem isUnit_of_isUnit_map {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) (b : B) (hb : IsUnit (θ b)) : IsUnit b := by
  obtain ⟨u, hu⟩ := hb
  obtain ⟨b', hb'⟩ := hF.surj (↑u⁻¹ : O)
  have hx0 : θ (b * b' - 1) = 0 := by
    rw [map_sub, map_mul, hb', ← hu, map_one, Units.mul_inv, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hx0
  haveI := hF.complete
  have hj : (p : B) * y ∈ (⊥ : Ideal B).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (p : B))))
  have hu1 := (Ideal.mem_jacobson_bot.1 hj) (-(-1) ^ p)
  have hgeom := mul_neg_geom_sum (-(b * b' - 1)) p
  have h2 : (1 - -(b * b' - 1)) * ∑ i ∈ Finset.range p, (-(b * b' - 1)) ^ i =
      (p : B) * y * (-(-1) ^ p) + 1 := by
    rw [hgeom, neg_pow, hy]; ring
  have h3 : IsUnit (1 - -(b * b' - 1)) := isUnit_of_mul_isUnit_left (h2 ▸ hu1)
  have h4 : (1 - -(b * b' - 1)) = b * b' := by ring
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left h3

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (a : O) :
    ∃ r : O, r ^ p = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Fact.out : p.Prime).pos
  have h1 : v z ≤ 1 := by
    have := hv.map_le_one a
    rw [← hz, map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' (Fact.out : p.Prime).ne_zero).1 this
  obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
  exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩

theorem frob_matrix_isUnit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA U hU
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hm : ∀ x : O, ¬IsUnit x ↔ x ∈ IsLocalRing.maximalIdeal O := fun x =>
    (IsLocalRing.mem_maximalIdeal x).symm
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (hm _).1 (Fact.out)
  have hσ : ∀ b, ∃ z, F.σ b = b ^ p + (p : F.B) * z := fun b => by
    obtain ⟨z, hz⟩ := F.σ_pow b
    exact ⟨z, by rw [← hz]; ring⟩
  have hσm : ∀ b, F.θ b ∈ IsLocalRing.maximalIdeal O → F.θ (F.σ b) ∈ IsLocalRing.maximalIdeal O := by
    intro b hb
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add (f := _), map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hb _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ hpm)
  have key : ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) →
      ∀ l, ¬IsUnit (F.θ (w l)) := by
    intro w hw
    have h1 := _root_.GlobalTheory.QLog.small_first_of_frob p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU w hw
    have h2 := _root_.GlobalTheory.SmallSecond.small_second p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU (fun j => w (Sum.inr j)) (by
      intro l
      rw [hm]
      have hsplit : U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) (fun j => w (Sum.inr j)) :
          Fin d ⊕ Fin k → F.B) j)) l = U.mulVec (fun j => F.σ (w j)) l -
          ∑ m, U l m * F.σ ((Sum.elim (fun i => w (Sum.inl i)) (fun _ => 0) :
            Fin d ⊕ Fin k → F.B) m) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        cases m <;> simp
      rw [hsplit, map_sub]
      refine Ideal.sub_mem _ ((hm _).1 (hw l)) ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (hσm _ ?_)
      cases m with
      | inl i => simpa using (hm _).1 (h1 i)
      | inr j => simp)
    intro l
    cases l with
    | inl i => exact h1 i
    | inr j => exact h2 j
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_map F.frame
  rw [RingHom.map_det]
  by_contra hdet
  set M := (U.map F.θ).map (IsLocalRing.residue O) with hMdef
  have hM : M.det = 0 := by
    rw [show M = (IsLocalRing.residue O).mapMatrix (F.θ.mapMatrix U) from rfl, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 hdet)
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hlift : ∀ l, ∃ b : F.B, IsLocalRing.residue O (F.θ b) ^ p = x l := by
    intro l
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (x l)
    obtain ⟨r, hr⟩ := exists_pow_eq (p := p) hv a
    obtain ⟨b, hb⟩ := F.frame.surj r
    exact ⟨b, by rw [hb, ← map_pow, hr, ha]⟩
  choose w hw using hlift
  have hres : ∀ b, IsLocalRing.residue O (F.θ (F.σ b)) = IsLocalRing.residue O (F.θ b) ^ p := by
    intro b
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add (f := _), map_pow, map_mul, map_natCast, map_add (f := _), map_pow, map_mul,
      (IsLocalRing.residue_eq_zero_iff _).2 hpm, zero_mul, add_zero]
  have hk := key w (by
    intro l
    rw [hm, ← IsLocalRing.residue_eq_zero_iff]
    have := congrFun hx l
    simp only [Matrix.mulVec, dotProduct, hMdef, Matrix.map_apply, Pi.zero_apply] at this ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simpa [hres, hw] using this)
  apply hx0
  funext l
  rw [← hw l, (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 (hk l)), zero_pow (Fact.out : p.Prime).ne_zero,
    Pi.zero_apply]

end GlobalTheory.FrobUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointMemberHasLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.IntTerm

theorem torsion_has_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 xb hxb
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) (T.hom ≫ spMap 𝔪.yK) (pushHom 𝔪.cart T xb)
    (by rw [← map_pow, hxb, map_one])
  refine ⟨a, ?_⟩
  have h1 : (T.hom ≫ spMap 𝔪.yK) ≫ (X₁.ρ.pt a).left = xb.left ≫ 𝔪.φ := congrArg (fun z => z.left) ha
  rw [← h1]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom 𝔪.yK)
    (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))).symm

end GlobalTheory.GSep.IntTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarisatiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv) | (exact GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv) | (intros; apply GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv <;> assumption)
end

