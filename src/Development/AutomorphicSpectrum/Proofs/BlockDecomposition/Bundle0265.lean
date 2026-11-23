module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLift
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0261
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Chart

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem idealPowι_comp_pullback_map_cokernel_eq_zero {A : Type} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (D : Subobject E) (m : ℕ)
    (hD : powSub I E m ≤ D) :
    idealPowι I ((Scheme.Modules.pullback φ).obj E) m ≫
      (Scheme.Modules.pullback φ).map (cokernel.π D.arrow) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage
    (idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ m)))).1
  rw [comp_zero, ← Category.assoc, Abelian.image.fac]
  apply biproduct.hom_ext'
  intro k
  rw [comp_zero, idealSumMap, biproduct.ι_desc_assoc, smulHom_comp, ← appTop_algebraMap φ hφ,
    ← pullback_map_smulHom_appTop, ← Functor.map_comp, ← smulHom_comp]
  obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap E (I ^ m) (idealGen_mem (I ^ m) k)
  have hι : idealPowι I E m ≫ cokernel.π D.arrow = 0 := by
    have h := Subobject.ofMkLE_arrow (f := idealPowι I E m) (X := D) hD
    rw [← h, Category.assoc, cokernel.condition, comp_zero]
  rw [hL, ← Abelian.image.fac (idealSumMap E (I ^ m)), Category.assoc, Category.assoc, hι,
    comp_zero, comp_zero, Functor.map_zero]

theorem chartIn_of_pullback_app_eq_zero (φ : Z ⟶ X) {E : X.Modules} [E.IsQuasicoherent]
    (D : Subobject E) [(D : X.Modules).IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (x : Γ(E, V))
    (hx : ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
      ((Scheme.Modules.pullback φ).map (cokernel.π D.arrow)).app U
        (GlobalTheory.QCoh.pullbackSections φ E h x) = 0) :
    ChartIn φ V (secsSub D V) x := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have hx' := hx U hU h
  rw [GlobalTheory.QCoh.pullback_map_app_pullbackSections] at hx'
  letI := GlobalTheory.QCoh.appLEModule φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  haveI := GlobalTheory.QCoh.appLE_isScalarTower φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  have hbc := GlobalTheory.QCoh.isBaseChange_pullbackSections φ (cokernel D.arrow) hU hV h
  let πl : Γ(E, V) →ₗ[Γ(X, V)] Γ(cokernel D.arrow, V) :=
    { toFun := (cokernel.π D.arrow).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hsurj : Function.Surjective πl := surjective_cokernel_π_app D.arrow hV
  have hex : Function.Exact (secsSub D V).subtype πl := by
    intro m
    have hm : m ∈ Set.range (secsSub D V).subtype ↔ m ∈ Set.range (D.arrow.app V) := by
      rw [Submodule.coe_subtype, Subtype.range_coe_subtype]
      rfl
    rw [hm, mem_range_app_iff D.arrow hV m]
    rfl
  have hex' := rTensor_exact Γ(Z, U) hex hsurj
  refine (hex' _).1 ?_
  rw [LinearMap.rTensor_tmul]
  have h1 : (1 : Γ(Z, U)) ⊗ₜ[Γ(X, V)] πl x = 0 := by
    apply hbc.equiv.injective
    rw [hbc.equiv_tmul, one_smul, map_zero]
    exact hx'
  rw [← TensorProduct.comm_tmul, h1, map_zero]

theorem chartIn_adjKer : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X),
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S →
    ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)),
    (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V →
    ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  intro A _ _ I X Z _ _ _ φ hφ E hE S hS B hB V hV x hx n
  have : E.IsQuasicoherent := hE.1
  have : ((S n : Subobject E) : X.Modules).IsQuasicoherent := hS.qcoh n
  apply chartIn_of_pullback_app_eq_zero φ (S n) V hV x
  intro U hU h
  obtain ⟨y, rfl⟩ := hx
  set g := (Scheme.Modules.pullback φ).map (cokernel.π (S n).arrow) with hg
  have hK : pullSys I φ E S n ≤ kernelSubobject g := by
    change imageSubobject ((Scheme.Modules.pullback φ).map (S n).arrow) ⊔
      powSub I _ (n + 1) ≤ kernelSubobject g
    refine sup_le (image_le_kernel _ _ ?_) (le_kernelSubobject _ _ ?_)
    · rw [hg, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    · rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_pullback_map_cokernel_eq_zero I φ hφ E (S n) (n + 1) (hS.pow_le n),
        comp_zero]
  have hBle : B ≤ kernelSubobject g := by
    rw [← hB n] at hK
    exact le_sup_left.trans hK
  have hBg : B.arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow hBle, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  have h0 : (adjMap φ B).app V ((adjKer φ B).arrow.app V y) = 0 := by
    have hk : (adjKer φ B).arrow ≫ adjMap φ B = 0 := kernelSubobject_arrow_comp _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hk]
    rfl
  have h1 : (cokernel.π B.arrow).app (φ ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app E).app V
        ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [adjMap, Adjunction.homEquiv_unit] at h0
    exact h0
  have hfac : g = cokernel.π B.arrow ≫ cokernel.desc B.arrow g hBg := (cokernel.π_desc _ _ _).symm
  have h2 : (cokernel.π B.arrow).app U
      (GlobalTheory.QCoh.pullbackSections φ E h ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [GlobalTheory.QCoh.pullbackSections_apply]
    erw [GlobalTheory.QCoh.hom_app_res (cokernel.π B.arrow) h]
    rw [h1, map_zero]
  rw [hfac, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h2, map_zero]

end GlobalTheory.CompanionTheory.GE.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleTwistDifference
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X : Scheme.{0}}

theorem res_res_units {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (resG_resG h₁ h₂ _)

theorem mul_chart_cancel {S : Type} [CommRing S] (u G k' k u' a : S) (h : u = G * k' * u') (h' : k' * k = 1) :
    u * (k * a) = G * (u' * a) := by
  subst h
  linear_combination (G * u' * a) * h'

theorem eq_of_resG_near {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ y ∈ U, ∃ (W : X.Opens) (_ : y ∈ W) (hW : W ≤ U), resG X hW a = resG X hW b) : a = b :=
  ext_germ fun y hy => by
    obtain ⟨W, hyW, hW, e⟩ := h y hy
    rw [← germ_resG hW y hyW a, ← germ_resG hW y hyW b, e]

theorem iso_sec_chart {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) (p p' : B.ι) (q q' : A.ι)
    {W : X.Opens} (h₁ : W ≤ B.U p) (h₁' : W ≤ B.U p') (h₂ : W ≤ A.U q) (h₂' : W ≤ A.U q') :
    resG X (le_inf h₁ h₂) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X h₂ (a.f q) =
      resG X (le_inf h₁ h₁') (B.g p p' : Γ(X, B.U p ⊓ B.U p')) *
        (resG X (le_inf h₁' h₂') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')) : Γ(X, B.U p' ⊓ A.U q')) *
          resG X h₂' (a.f q')) := by
  have hW : W ≤ (LB.div B A).U (p, q) ⊓ (LB.div B A).U (p', q') :=
    le_inf (le_inf h₁ h₂) (le_inf h₁' h₂')
  have e := congrArg (res hW) (hw (p, q) (p', q'))
  have e₂ : res hW ((LB.div B A).g (p, q) (p', q')) =
      res (le_inf h₁ h₁') (B.g p p') * (res (le_inf h₂ h₂') (A.g q q'))⁻¹ := by
    exact (map_mul (res hW) _ _).trans (congrArg₂ (· * ·) (res_res_units _ _ _)
      ((map_inv (res hW) _).trans (congrArg (·⁻¹) (res_res_units _ _ _))))
  rw [map_mul, e₂, res_res_units, res_res_units] at e
  have e₃ := congrArg (fun u : Γ(X, W)ˣ => (u : Γ(X, W))) e
  simp only [Units.val_mul] at e₃
  rw [sec_compat a q q' h₂ h₂']
  have e₄ : ((res (le_inf h₂ h₂') (A.g q q'))⁻¹ : Γ(X, W)ˣ).val * resG X (le_inf h₂ h₂') (A.g q q' : Γ(X, A.U q ⊓ A.U q')) = 1 :=
    Units.inv_mul (res (le_inf h₂ h₂') (A.g q q'))
  exact mul_chart_cancel _ _ _ _ _ _ e₃ e₄

theorem exists_secMaps {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) :
    ∃ b : B.Sec, SecMaps w a b := by
  have hself : ∀ (p : B.ι) {W : X.Opens} (h : W ≤ B.U p),
      resG X (le_inf h h) (B.g p p : Γ(X, B.U p ⊓ B.U p)) = 1 := by
    intro p W h
    have e := congrArg (fun u : Γ(X, B.U p)ˣ => resG X h (u : Γ(X, B.U p))) (hB.g_self p)
    simp only [val_res, resG_resG, Units.val_one, map_one] at e
    exact e
  have glue : ∀ p : B.ι, ∃ b : Γ(X, B.U p), ∀ q : A.ι, resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) b =
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q) := by
    intro p
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun q : A.ι => B.U p ⊓ A.U q) (B.U p)
      (fun _ => homOfLE inf_le_left)
      (fun y hy => by
        obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (fun q q' => by
        have h₁ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
        have h₂ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
        have h₃ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
        have k := iso_sec_chart hw a p p q q' h₁ h₁ h₂ h₃
        rw [hself p h₁, one_mul] at k
        change resG X inf_le_left _ = resG X inf_le_right _
        rw [map_mul, map_mul]
        repeat rw [resG_resG]
        exact k)
    exact ⟨b, hb⟩
  choose b hb using glue
  refine ⟨⟨b, fun p p' => ?_⟩, fun r => hb r.1 r.2⟩
  refine eq_of_resG_near fun y hy => ?_
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
  have h₀ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p ⊓ B.U p' := inf_le_left
  have h₁ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p := inf_le_left.trans inf_le_left
  have h₁' : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p' := inf_le_left.trans inf_le_right
  have h₂ : B.U p ⊓ B.U p' ⊓ A.U q ≤ A.U q := inf_le_right
  refine ⟨B.U p ⊓ B.U p' ⊓ A.U q, ⟨hy, hq⟩, h₀, ?_⟩
  have e₁ := congrArg (resG X (le_inf h₁ h₂)) (hb p q)
  have e₂ := congrArg (resG X (le_inf h₁' h₂)) (hb p' q)
  rw [map_mul, resG_resG, resG_resG] at e₁ e₂
  have k := iso_sec_chart hw a p p' q q h₁ h₁' h₂ h₂
  change resG X h₀ (resG X inf_le_left (b p)) = resG X h₀ ((B.g p p' : Γ(X, B.U p ⊓ B.U p')) * resG X inf_le_right (b p'))
  rw [map_mul, resG_resG, resG_resG]
  exact e₁.trans (k.trans (congrArg _ e₂.symm))

theorem relAmple_tw_of_roots : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  intro R _ X Q m ζ hQ hva A C n hn hA hC hAQ hCQ
  have hM : (tw C A (-1)).IsLB := isLB_tw hC hA _
  have hD : 1 ≤ n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
  have hP := isLB_pw hM ((n * (n + 1) : ℕ) : ℤ)
  have hcls : GlobalTheory.CechPic.cls _ hP = GlobalTheory.CechPic.cls Q hQ := by
    have hc : GlobalTheory.CechPic.cls _ hM = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
      refine (GlobalTheory.CechPic.cls_div hC (isLB_pw hA _) hM).trans ?_
      rw [GlobalTheory.AmpleStabFinite.cls_pw hA]
      simp
    have e₁ : ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hA _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hAQ)
    have e₂ : (n : ℤ) • GlobalTheory.CechPic.cls C hC = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hC _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hCQ)
    rw [GlobalTheory.AmpleStabFinite.cls_pw hM, hc, smul_sub]
    have f₁ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls C hC = ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₂, smul_smul]; congr 1 <;> (push_cast; ring)
    have f₂ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = (n : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₁, smul_smul]; congr 1 <;> (push_cast; ring)
    rw [f₁, f₂, ← sub_smul]
    simp
  obtain ⟨w, hw⟩ : LBIso Q (pw (tw C A (-1)) ((n * (n + 1) : ℕ) : ℤ)) := (GlobalTheory.CechPic.cls_eq_iff hQ hP).1 hcls.symm
  choose t ht using fun i => exists_secMaps hQ hP hw (ζ i)
  obtain ⟨hs, hci⟩ := (veryAmpleBy_iff X.hom ζ).1 hva
  have ht' := iSup_nonzeroLocus_of_secMaps hs hQ hP ht
  refine GlobalTheory.Unif.relAmple_of_veryAmpleBy hM hD t ((veryAmpleBy_iff X.hom t).2 ⟨ht', ?_⟩)
  rw [toProj_eq_of_secMaps hs ht' ht]
  exact hci

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLiftStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_extension_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (X : RootExt l 𝓛.D 𝓛.t) (θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj), n ≠ 0 → (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → ∃ e : X.E →+* 𝒯.A.Acr n, Function.Bijective e ∧ (∀ z, e (algebraMap 𝓛.D X.E z) = θ.φ z) ∧ ∀ j m, e (X.r j m) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j m : 𝒯.A.A)) := by
  first | exact @GlobalTheory.CompanionTheory.TowerAcr.tower_acr | exact GlobalTheory.CompanionTheory.TowerAcr.tower_acr | (intros; apply GlobalTheory.CompanionTheory.TowerAcr.tower_acr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSumStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_epsilon_root_idempotent_sum : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A),
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) →
  (∀ m, ρ (m + 1) ^ l = ρ m) → ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | exact GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | (intros; apply GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}}

def secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens} (x : SecOn (pw N a) V)
    (y : SecOn (pw N b) V) : SecOn (pw N c) V :=
  GlobalTheory.LB.mkSec (L := pw N c) (fun i => @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i)) (fun i j => by
    have hx := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have hy := GlobalTheory.LB.coord_rel y i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    subst h
    have e : ((N.g i j ^ (a + b) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) =
        ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ b : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) := by
      rw [zpow_add, Units.val_mul]
    erw [map_mul, map_mul]
    erw [hx, hy, e, map_mul]
    rw [show (AbLaw.pw N a).g i j = N.g i j ^ a from rfl, show (AbLaw.pw N b).g i j = N.g i j ^ b from rfl]
    exact mul_mul_mul_comm _ _ _ _)

@[simp] theorem coord_secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens}
    (x : SecOn (pw N a) V) (y : SecOn (pw N b) V) (i : N.ι) :
    GlobalTheory.LB.coord (secMulOn h x y) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i) := rfl

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) : SecOnR f (pw N a) V →ₗ[R] SecOnR f (pw N c) V where
  toFun x := SecOnR.of f _ V (secMulOn h ((SecOnR.of f _ V).symm x) y)
  map_add' x x' := GlobalTheory.LB.sec_ext fun (i : N.ι) => add_mul (R := Γ(X, V ⊓ N.U i)) _ _ _
  map_smul' r x := GlobalTheory.LB.sec_ext fun (i : N.ι) => mul_assoc (G := Γ(X, V ⊓ N.U i)) _ _ _

theorem coord_mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) (x : SecOnR f (pw N a) V) (i : N.ι) :
    SecOnR.coord (mulRight f h y x) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (SecOnR.coord x i) (GlobalTheory.LB.coord y i) :=
  rfl

def oneOn (N : LB X) {a : ℤ} (h : a = 0) (V : X.Opens) : SecOn (pw N a) V :=
  GlobalTheory.LB.mkSec (L := pw N a) (fun _ => 1) (fun i j => by
    subst h
    rw [map_one, map_one, show (AbLaw.pw N 0).g i j = N.g i j ^ (0 : ℤ) from rfl, zpow_zero,
      Units.val_one]
    erw [map_one, one_mul])

section Tower

variable (I : Ideal R)

abbrev toR (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) :
    (Y e).left ⟶ Spec (CommRingCat.of R) :=
  (Y e).hom ≫ thick R I e

theorem toR_w (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ) :
    β e ≫ toR I Y (e + 1) =
      toR I Y e ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, toR, toR, ← Category.assoc, (hβ e).w,
    Category.assoc, thickTrans_comp]

variable {ι : Type} (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (N : ∀ e, LB (Y e).left) (D : ∀ e, Finset ι → (Y e).left.Opens) (d : ℤ)

abbrev Tm (e : ℕ) (t : ℤ) (S : Finset ι) : Type :=
  SecOnR (toR I Y e) (pw (N e) (d * t)) (D e S)

def resT (hD : ∀ e (S S' : Finset ι), S ⊆ S' → D e S' ≤ D e S) (e : ℕ) (t : ℤ) {S S' : Finset ι}
    (h : S ⊆ S') : Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e t S' :=
  SecOnR.restrict (toR I Y e) _ (hD e S S' h)

def mulT (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) :
    Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e (t + 1) S :=
  mulRight (toR I Y e) (by ring) σ

theorem mulT_comm (e : ℕ) (t : ℤ) (S : Finset ι) (σ τ : SecOn (pw (N e) d) (D e S))
    (x : Tm I Y N D d e t S) :
    mulT I Y N D d e (t + 1) S σ (mulT I Y N D d e t S τ x) =
      mulT I Y N D d e (t + 1) S τ (mulT I Y N D d e t S σ x) := by
  refine SecOnR.ext_iff.mpr fun i => ?_
  unfold mulT
  first
  | (erw [coord_mulRight, coord_mulRight, coord_mulRight, coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; ring)

def oneT (e : ℕ) (S : Finset ι) : Tm I Y N D d e 0 S :=
  SecOnR.of _ _ _ (oneOn (N e) (mul_zero d) (D e S))

def redL (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : V' ≤ β e ⁻¹ᵁ V) :
    SecOnR (toR I Y (e + 1)) (L (e + 1)) V →ₗ[R] SecOnR (toR I Y e) (L e) V' :=
  (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).symm.toLinearMap ∘ₗ SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' h

def red (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen)
    (hDβ : ∀ e (S : Finset ι), D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (e : ℕ) (S : Finset ι) :
    SecOnR (toR I Y (e + 1)) (pw (N (e + 1)) a) (D (e + 1) S) →ₗ[R]
      SecOnR (toR I Y e) (pw (N e) a) (D e S) :=
  redL I Y β hβ (fun e => pw (N e) a) (fun e => pullPow (v e) a)
    (fun e => ⟨isLB_pw (hN e).1 a, pullPow_isGen (v e) a (hN e).2⟩) e (D (e + 1) S) (D e S) (hDβ e S)

end Tower

section Sub

variable {ι : Type} [DecidableEq ι]

theorem sub_pair_left (i j : ι) : ({i} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)

theorem sub_pair_right (i j : ι) : ({j} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem sub_triple_ij (i j k : ι) : ({i, j} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_jk (i j k : ι) : ({j, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_ik (i j k : ι) : ({i, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

end Sub

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_of_affine_cover : ∀ {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent] (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ∀ {ι : Type} (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) → iSup V = ⊤ → (∀ i, secs S (V i) ⊆ secs T (V i)) → S ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | exact GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | (intros; apply GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorNoetherianAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_noetherian_affine_open : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.krull_noeth_chart | exact GlobalTheory.CompanionTheory.GE.krull_noeth_chart | (intros; apply GlobalTheory.CompanionTheory.GE.krull_noeth_chart <;> assumption)
end

