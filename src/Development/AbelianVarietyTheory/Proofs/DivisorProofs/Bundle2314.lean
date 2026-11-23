module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqOfTangentDerivativeAtOriginEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSectionsOfAlgebraicAffineNbhd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

theorem exists_points_equiv {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    {X : Scheme.{0}} (t : X ⟶ Sp V₁) (g : X ⟶ Sp W₀) (hg : t ≫ spMap ρ ≫ spMap ib = g) :
    ∃ Φ : (Over.mk t ⟶ D.P.A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)),
      ∀ x a, (Φ x a).left = x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  obtain ⟨E1, hE1⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback
    (isGrpPullback_pullback Q.B (spMap ρ)) t (t ≫ spMap ρ) rfl
  obtain ⟨E2, hE2⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (t ≫ spMap ρ) g
    (by rw [Category.assoc]; exact hg)
  let P : (Over.mk t ⟶ D.P.A) →* (Fin 8 → (Over.mk t ⟶ (Over.pullback (spMap ρ)).obj Q.B)) :=
    Pi.monoidHom fun a =>
      { toFun := fun x => x ≫ pr a
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  have hP : Function.Bijective P := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · obtain ⟨z, -, hz⟩ := huniv (Over.mk t) (P x)
      exact (hz x fun a => rfl).trans (hz y fun a => (congrFun h a).symm).symm
    · obtain ⟨z, hz, -⟩ := huniv (Over.mk t) y
      exact ⟨z, funext hz⟩
  refine ⟨(MulEquiv.ofBijective P hP).trans (MulEquiv.piCongrRight fun _ => E1.trans E2), fun x a => ?_⟩
  show (E2 (E1 (x ≫ pr a))).left = _
  rw [hE2, hE1, Over.comp_left]
  simp only [Category.assoc]

theorem spMap_three {A B C E : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing E] (f : A →+* B) (g : B →+* C)
    (h : C →+* E) : spMap h ≫ spMap g ≫ spMap f = spMap ((h.comp g).comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_c_defOver {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (hc : ∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left)
    (B₀ : Over (Sp W₀)) (β : Q.B.left ⟶ B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (hβc : ∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∀ mu a, DefOver k₀ (spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  intro mu a
  have h : spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
      spMap ((ev.comp ρ).comp ib) ≫ (c₀ (mu a)).left := by
    rw [reassoc_of% (hc mu a), hβc, ← spMap_three]
    simp only [Category.assoc]
  rw [h]
  refine ⟨spMap (((ev.comp ρ).comp ib).codRestrict k₀ hk) ≫ (c₀ (mu a)).left, ?_⟩
  rw [← Category.assoc]
  congr 1
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_torsion_defOver {W₀ : Type} [CommRing W₀] [IsNoetherianRing V₁] (ρ : V →+* V₁) (ib : W₀ →+* V)
    (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) (N : ℕ) (hN : 1 ≤ N) (hNu : IsUnit (N : V₁))
    (x : Over.mk (spMap ev) ⟶ D.P.A) (hx : x ^ N = 1) (a : Fin 8) :
    DefOver k₀ (x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (spMap ev) (spMap ((ev.comp ρ).comp ib))
    (spMap_three _ _ _)
  have hNK : (N : K) ≠ 0 := by
    have := (hNu.map ev).ne_zero
    simpa using this
  have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
  have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} =>
    (Φ y.1 a).left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  have hσf : spMap σ.toRingHom ≫ spMap ((ev.comp ρ).comp ib) = spMap ((ev.comp ρ).comp ib) := by
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ (hk w)
  let h : Over.mk (spMap ((ev.comp ρ).comp ib)) ⟶ Over.mk (spMap ((ev.comp ρ).comp ib)) :=
    Over.homMk (spMap σ.toRingHom) hσf
  refine ⟨⟨Φ.symm (fun b => h ≫ Φ x b), ?_⟩, ?_⟩
  · have e : (fun b => h ≫ Φ x b) ^ N = 1 := by
      funext b
      rw [Pi.pow_apply, ← MonObj.comp_pow, ← Pi.pow_apply, ← map_pow, hx, map_one, Pi.one_apply, MonObj.comp_one]
    rw [← map_pow, e, map_one]
  · show (Φ (Φ.symm fun b => h ≫ Φ x b) a).left = _
    rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
    rfl

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinPrinc

theorem surj_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (hP : IsPullback f₁ f₂ g₁ g₂) (hs : Function.Surjective g₂) : Function.Surjective f₁ := by
  have h := hP.map (forget CommRingCat)
  intro r
  obtain ⟨r₂, hr₂⟩ := hs (g₁ r)
  obtain ⟨x, hx, -⟩ := ((Types.isPullback_iff _ _ _ _).1 h).2.2 r r₂ hr₂.symm
  exact ⟨x, hx⟩

theorem principal_of_pull : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  intro g n _ _ P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart _ hs₂ _ β c c₁ hpb hc₁
  obtain ⟨φ, φ₂, hφ, hsq, hw, -⟩ := hpb
  obtain ⟨hA₁, hK₁⟩ := hc₁
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hf₁ : Function.Surjective f₁.hom := surj_of_isPullback hP hs₂
  let f := Spec.map f₁
  have hPc : cls c₁.P c₁.isLB = pull φ₂ (cls c.P c.isLB) := (cls_eq_iff _ (pull_isLB c.isLB _)).2 hw
  have hpair : ∀ {T : Over (Spec P)} {T' : Over (Spec R₁)} (u : T'.left ⟶ T.left) (a b : T ⟶ c.A)
      (a' b' : T' ⟶ c₁.A), a'.left ≫ φ = u ≫ a.left → b'.left ≫ φ = u ≫ b.left →
      GlobalTheory.PrincipalIntegral.pair (cls c₁.P c₁.isLB) a' b' = pull u (GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) a b) := fun u a b a' b' ha hb => by
    rw [GlobalTheory.PrincipalIntegral.pair, GlobalTheory.PrincipalIntegral.pair, hPc, ← pull_comp, ← pull_comp, SiegelDescent.lift_comp_square hsq u a b a' b' ha hb]
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hD₁ : c₁.diag.IsLB := pull_isLB c₁.isLB _
  have hd : cls c₁.diag hD₁ = pull φ (cls c.diag hD) :=
    hpair φ (𝟙 c.A) (𝟙 c.A) (𝟙 c₁.A) (𝟙 c₁.A) (by simp) (by simp)
  have hdiso : LBIso c₁.diag (c.diag.pull φ) := by
    refine (cls_eq_iff hD₁ (pull_isLB hD _)).1 ?_
    rw [cls_pull hD, hd]
  haveI := c.ab.proper
  haveI := c.ab.smooth
  have hA : Out.RelAmple c.A c.diag :=
    GlobalTheory.SharpLift.relAmple_of_closed_proper P c.A c.diag hD R₁ f₁.hom hf₁ c₁.A φ hφ.1 c₁.diag hD₁ hdiso hA₁
  refine ⟨hA, fun T x hx => ?_⟩
  obtain ⟨hpos, hdet⟩ := isE8_W8
  let G := Out.powObj c.A 8
  let pr : Fin 8 → (G ⟶ c.A) := Out.powPr c.A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over (Spec P)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hG : IsAbelianScheme G := AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7
  let G' := (Over.pullback f).obj G
  let ψ : G'.left ⟶ G.left := Pdiv.PullbackComparison.pφ f G
  have hψ : IsGrpPullback G' G f ψ := Pdiv.PullbackComparison.isGrpPullback f G
  choose pr' hpr using fun u => SharpPull.exists_lift hψ hφ (pr u)
  have hmon' : ∀ u, IsMonHom (pr' u) := fun u => SharpPull.isMonHom_lift hψ hφ (hpr u)
  have huniv' : ∀ (T : Over (Spec R₁)) (y : Fin 8 → (T ⟶ c₁.A)), ∃! x : T ⟶ G', ∀ u, x ≫ pr' u = y u :=
    fun T y => by
    obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hφ T (y u))
    obtain ⟨x, rfl⟩ := SharpPull.push_surj hψ x₀
    refine ⟨x, fun u => SharpPull.push_inj hφ ?_, fun x' hx' => SharpPull.push_inj hψ (hu _ fun u => ?_)⟩
    · rw [SharpPull.push_comp hψ hφ (hpr u), hx₀ u]
    · rw [← SharpPull.push_comp hψ hφ (hpr u), hx' u]
  let L := LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) fun uv => W8 uv.1 uv.2
  let L' := LB.LinComb c₁.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left)
    fun uv => W8 uv.1 uv.2
  have hL : L.IsLB := LB.isLB_linComb c.isLB _ _
  have hL' : L'.IsLB := LB.isLB_linComb c₁.isLB _ _
  have hLW : cls L hL = quad (cls c.P c.isLB) W8 pr := cls_linComb c.isLB _ _ _
  have hLW' : cls L' hL' = quad (cls c₁.P c₁.isLB) W8 pr' := cls_linComb c₁.isLB _ _ _
  have hiso : LBIso L' (L.pull ψ) := by
    refine (cls_eq_iff hL' (pull_isLB hL _)).1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cls_pull hL, hLW, hLW', quad, quad, map_sum]
    exact Finset.sum_congr rfl fun uv _ => by rw [map_zsmul, hpair ψ _ _ _ _ (hpr uv.1) (hpr uv.2)]
  have hadd := pair_mul c hl.globalFns hA
  have hadd' := pair_mul c₁ hl.globalFns hA₁
  have hK' : Out.KTriv G' L' := kTriv_of_kernel hadd' (pair_comm c₁) hmon' huniv' hL' hLW' hdet fun T x hx =>
    hK₁ T x ((cls_eq_zero_iff (pull_isLB c₁.isLB _)).1 hx)
  have hAL : Out.RelAmple G L :=
    PosDefAmple.relAmple_linComb_of_posDef hl.globalFns g n 8 _ _ _ _ c G pr W8 hmon huniv hA hpos
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf₁
  haveI : IsLocalHom f₁.hom := Function.Surjective.isLocalHom f₁.hom hf₁
  have hK : Out.KTriv G L := GlobalTheory.SharpLift.kTriv_of_localHom P R₁ f₁.hom G hG L hL hAL G' ψ hψ L' hL' hiso hK'
  have hx' : GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) (snd c.A T ≫ x) (fst c.A T) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 hx
  exact kernel_of_kTriv (n := 8) (G := G) hadd (pair_comm c) hmon huniv hL hLW (0 : Fin 8) hK T x hx'

end GlobalTheory.ArtinPrinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupLocalCoordinatesAtOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

theorem coords_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ δ : Fin n → Derivation ℤ (G.left.presheaf.stalk (origin G)) (G.left.presheaf.stalk (origin G)), (∀ a O (hO : origin G ∈ O) f, δ a ((G.left.presheaf.germ O (origin G) hO).hom f) = (G.left.presheaf.germ O (origin G) hO).hom (dd a O f)) → ∃ z : Fin n → G.left.presheaf.stalk (origin G), (∀ i, evO G (z i) = 0) ∧ (∀ a i, evO G (δ a (z i)) = if a = i then 1 else 0) ∧ maximalIdeal (G.left.presheaf.stalk (origin G)) = (maximalIdeal R).map (constO G) ⊔ Ideal.span (Set.range z) := by
  intro R _ _ _ _ G _ _ hsm n v dd hinv δ hδ
  letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra
  obtain ⟨hN, hF, hFin⟩ := GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal R G hsm
  have key : ∀ a f, evO G (δ a f) = tanDer G (v a) f := by
    intro a f
    obtain ⟨O, hx, g, rfl⟩ := G.left.presheaf.exists_germ_eq f
    rw [hδ a O hx g]
    exact GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative R G (v a) (dd a) (hinv a) O hx g
  have hadd : ∀ a x y, tanDer G (v a) (x + y) = tanDer G (v a) x + tanDer G (v a) y := by
    intro a x y
    rw [← key, ← key, ← key, map_add (f := _), map_add (f := _)]
  have hmul : ∀ a x y, tanDer G (v a) (x * y) = evO G x * tanDer G (v a) y + evO G y * tanDer G (v a) x := by
    intro a x y
    rw [← key, ← key, ← key, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul]
  have hc : ∀ a r, tanDer G (v a) (algebraMap R _ r) = 0 := by
    intro a r
    rw [← key]
    show evO G (δ a (constO G r)) = 0
    rw [← GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial,
      GlobalTheory.Heat.isInv_constFn R G (v a) (dd a) (hinv a) ⊤ r, map_zero, map_zero]
  let φ : TanM (𝟙 (Sp R)) G →+ (G.left.presheaf.stalk (origin G) → R) :=
    { toFun := fun w => tanDer G w
      map_zero' := funext fun f => by
        have h := _root_.GlobalTheory.CoordsOrigin.tanDer_smul R G 0 0 f
        rwa [zero_smul, zero_mul] at h
      map_add' := fun u w => funext fun f => _root_.GlobalTheory.CoordsOrigin.tanDer_add R G u w f }
  have hlin : ∀ (c : Fin n → R) f, tanDer G (∑ a, c a • v a) f = ∑ a, c a * tanDer G (v a) f := by
    intro c f
    have h1 : tanDer G (∑ a, c a • v a) f = φ (∑ a, c a • v a) f := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => _root_.GlobalTheory.CoordsOrigin.tanDer_smul R G (c a) (v a) f
  have hbasis : ∀ D : G.left.presheaf.stalk (origin G) → R, (∀ x y, D (x + y) = D x + D y) →
      (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (algebraMap R _ r) = 0) →
      ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * tanDer G (v a) x := by
    intro D h1 h2 h3
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_tangentVector_of_originDerivation R G D h1 h2 h3
    refine ⟨fun a => v.repr w a, ?_, ?_⟩
    · intro x
      rw [← hw x, ← hlin]
      congr 1
      exact (v.sum_repr w).symm
    · intro c hc'
      have hw' : ∑ a, c a • v a = w := _root_.GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer R G _ _ fun f => by rw [hlin, hw, hc' f]
      funext a
      rw [← hw', v.repr_sum_self]
  obtain ⟨z, hz0, hz1, hz2⟩ := _root_.GlobalTheory.CoordsAlg.coords_of_derivation_basis R _ (evO G) (GlobalTheory.FormalOrigin.evO_constO R G) hF hFin n
    (fun a => tanDer G (v a)) hadd hmul hc hbasis
  exact ⟨z, hz0, fun a i => by rw [key]; exact hz1 a i, hz2⟩

end GlobalTheory.CoordsOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoordinateStratumEtaleChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.LogPair TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem smooth_quotient_of_isEtCoord (Y : Scheme.{0}) (q : Y ⟶ Sp ℂ) (n : ℕ) (U : Y.Opens) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n))
    (hE : IsEtCoord q U z) :
    ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  let A := MvPolynomial (Fin n) ℂ
  let B := Γ(Y, U)
  let φ : A →+* B := MvPolynomial.eval₂Hom (cstOn q U) z
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.Etale A B := RingHom.etale_algebraMap.1 hE
  let I : Ideal A := Ideal.span (MvPolynomial.X '' (J : Set (Fin n)))
  have hI : I.map (algebraMap A B) = Ideal.span (z '' (J : Set (Fin n))) := by
    rw [Ideal.map_span, Set.image_image]
    congr 1
    ext x
    simp only [RingHom.algebraMap_toAlgebra, φ, Set.mem_image, Finset.mem_coe]
    constructor <;> rintro ⟨j, hj, rfl⟩ <;> exact ⟨j, hj, by rw [MvPolynomial.eval₂Hom_X']⟩
  have h1 : (algebraMap ℂ (A ⧸ I)).Smooth := by
    rw [RingHom.smooth_algebraMap]
    haveI : Algebra.Smooth ℂ (MvPolynomial {x // x ∉ (J : Set (Fin n))} ℂ) := ⟨inferInstance, inferInstance⟩
    exact Algebra.Smooth.of_equiv (quotientSpanXEquiv ℂ (J : Set (Fin n))).symm
  have h2 : (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).Smooth := by
    rw [RingHom.smooth_algebraMap]; infer_instance
  let e : ((A ⧸ I) ⊗[A] B) ≃+* B ⧸ Ideal.span (z '' (J : Set (Fin n))) :=
    ((Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hI)
  have h12 : ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I))).Smooth :=
    RingHom.Smooth.comp h1 h2
  have h3 : (e.toRingHom.comp ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I)))).Smooth :=
    have he : e.toRingHom.Smooth := RingHom.Smooth.of_bijective e.bijective
    RingHom.Smooth.comp h12 he
  convert h3 using 1
  ext c
  simp only [RingHom.comp_apply]
  have k1 : algebraMap ℂ (A ⧸ I) c = Ideal.Quotient.mk I (MvPolynomial.C c) := rfl
  have k2 : algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I (MvPolynomial.C c)) =
      (1 : A ⧸ I) ⊗ₜ[A] (algX q U c) := by
    have hm : Ideal.Quotient.mk I (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hm,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    congr 1
    simp [RingHom.algebraMap_toAlgebra, φ]
    rfl
  have k3 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm (algX q U c ⊗ₜ[A] (1 : A ⧸ I)) =
      Ideal.Quotient.mk _ (algX q U c) := by
    rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [k1, k2]
  simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul, k3,
    Ideal.quotEquivOfEq_mk]

theorem smooth_coordStratum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ J : Finset (Fin n), ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  intro Y _ _ q n _ U z hF J
  exact smooth_quotient_of_isEtCoord Y q n U z J (_root_.GlobalTheory.FrameEtale.isEtCoord_of_isFrame ℂ Y q n U z hF).2

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DenseSec
theorem chart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := _root_.GlobalTheory.DenseSec.exists_etChart
theorem hensel : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := _root_.GlobalTheory.DenseSec.hensel_etChart
theorem fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := _root_.GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre
theorem reduce : (∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := _root_.GlobalTheory.DenseAff.denseSections_of_algebraic

theorem image_maximalIdeal_infinite {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hker : RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R) :
    (algebraMap R Ω '' (maximalIdeal R : Set R)).Infinite := by
  have hle : RingHom.ker (algebraMap R Ω) ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨m0, hm0, hm0k⟩ : ∃ m0 ∈ maximalIdeal R, m0 ∉ RingHom.ker (algebraMap R Ω) := by
    by_contra hcon
    push_neg at hcon
    exact hker (le_antisymm hle hcon)
  rw [RingHom.mem_ker] at hm0k
  have hne : ∀ n k : ℕ, n < k → algebraMap R Ω (m0 ^ (n + 1)) ≠ algebraMap R Ω (m0 ^ (k + 1)) := by
    intro n k hnk heq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnk
    have h1 : algebraMap R Ω (m0 ^ (d + 1)) = 1 := by
      have hpow : algebraMap R Ω (m0 ^ (n + 1)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hm0k
      have : algebraMap R Ω (m0 ^ (n + 1)) * algebraMap R Ω (m0 ^ (d + 1)) = algebraMap R Ω (m0 ^ (n + 1)) * 1 := by
        rw [_root_.mul_one, ← map_mul, ← _root_.pow_add, heq]
        congr 2
        omega
      exact mul_left_cancel₀ hpow this
    have h2 : 1 - m0 ^ (d + 1) ∈ maximalIdeal R :=
      hle (by rw [RingHom.mem_ker, map_sub, map_one, h1, sub_self])
    have h3 : m0 ^ (d + 1) ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hm0 _ d.succ_pos
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.add_mem _ h2 h3))
  have hinj : Function.Injective (fun n : ℕ => algebraMap R Ω (m0 ^ (n + 1))) := by
    intro n k h
    by_contra hnk
    rcases lt_or_gt_of_ne hnk with hlt | hlt
    · exact hne n k hlt h
    · exact hne k n hlt h.symm
  exact Set.infinite_of_injective_forall_mem hinj (fun n => ⟨m0 ^ (n + 1), Ideal.pow_mem_of_mem _ hm0 _ n.succ_pos, rfl⟩)

theorem exists_eval_ne_zero_of_infinite {Ω : Type} [Field Ω] (S : Set Ω) (hS : S.Infinite) (g : ℕ)
    (Q : MvPolynomial (Fin g) Ω) (hQ : Q ≠ 0) : ∃ c : Fin g → Ω, (∀ i, c i ∈ S) ∧ MvPolynomial.eval c Q ≠ 0 := by
  obtain ⟨T, hTS, hT⟩ := hS.exists_subset_card_eq (Q.totalDegree + 1)
  by_contra hcon
  push_neg at hcon
  apply hQ
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ => T) (fun i => ?_) (fun x hx => hcon x (fun i => hTS (hx i)))
  rw [hT]
  exact Nat.lt_succ_of_le (MvPolynomial.degreeOf_le_totalDegree Q i)

theorem key : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0 := by
  intro R _ _ hc A _ _ _ ε Ω _ _ hker hirr f hf
  obtain ⟨g, t, h, ht0, hεh, hch⟩ := chart R A ε
  obtain ⟨Q, hQ, hQv⟩ := fibre R A g t h hch Ω hirr f hf
  obtain ⟨c', hc'S, hc'Q⟩ := exists_eval_ne_zero_of_infinite _ (image_maximalIdeal_infinite hker) g Q hQ
  choose c hcm hcc using hc'S
  obtain ⟨a, hah, hat⟩ := hensel R hc A g t h hch ε hεh c (fun i => by simpa [ht0] using hcm i)
  refine ⟨a, fun h0 => hc'Q ?_⟩
  have hv := hQv ((Algebra.ofId R Ω).comp a) (by simpa using (hah.map (algebraMap R Ω)).ne_zero) h0
  have hc' : c' = fun i => ((Algebra.ofId R Ω).comp a) (t i) := by
    funext i
    simp [hat, hcc]
  rw [hc']
  exact hv

theorem dense_sections : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := reduce key
end GlobalTheory.DenseSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_field_cancel (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X)
    (h : spMap io ≫ a = spMap io ≫ b) : a = b := by
  haveI : Epi (spMap io) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap io)).1 h

end GlobalTheory.Mum
end

