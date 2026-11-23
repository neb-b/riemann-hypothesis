module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.VarFlag

section Tri

variable {ι : Type} {m : ι → ℕ}

theorem par_map {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) {M : Mat m R} (hu : ∀ τ, IsUnit (M τ).det)
    (hl : ∀ τ i k, i < k → M τ i k = 0) : Par m ⊤ (M.map ψ) := fun τ => by
  refine ⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩
  · show (ψ.mapMatrix (M τ)).det ≠ 0
    rw [← RingHom.map_det]
    exact ((hu τ).map ψ).ne_zero
  · show ψ (M τ i j) = 0
    rw [hl τ i j hij, map_zero]

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem carries_at_image {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} (hc : C.Carries p g) :
    ∃ (φ₀ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))
      (g₀ : EigFrame Z φ₀ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
      g₀.Tri (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t ∧
      g₀.Tri (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g t' := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, h2, h3⟩ := hc
  have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
    have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
      (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
        (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫
          spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hρ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ stalkPt C.Y y =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hx₀ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ (stalkPt C.Y y ≫ C.π ≫ genι Z) =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  refine ⟨(C.Y.X.presheaf.stalkSpecializes hsp).hom.comp φ₁, ?_⟩
  let g₀ := Classical.choose (ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀)
  have hg₀ := Classical.choose_spec (ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀)
  exact ⟨g₀, t, t', ValCoord.tri_bc hx₀ hg₀ (by rw [← CarriesAt.algebraMap_eq_comp_specializes hsp]; exact h2),
    ValCoord.tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)⟩

theorem tri_of_carries {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} {g' : EigFrame Z φ' x}
    (hg : C.Carries p g) (hg' : C.Carries p g') : ∃ t, g.Tri (RingHom.id K) g' t := by
  obtain ⟨φ₀, g₀, t, s, T1, T2⟩ := carries_at_image C hg
  obtain ⟨φ₀', g₀', t₂, s₂, T1', T2'⟩ := carries_at_image C hg'
  have hinj : Function.Injective
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) :=
    IsFractionRing.injective _ _
  obtain rfl : φ₀' = φ₀ := RingHom.ext fun a =>
    hinj ((RingHom.congr_fun T1'.2.1 a).symm.trans (RingHom.congr_fun T1.2.1 a))
  have hφ : φ' = φ := T2'.2.1.trans T2.2.1.symm
  obtain ⟨T, hT, hTd, hTl⟩ := (g₀.tri_iff (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t).1 T1
  obtain ⟨T₂, hT₂, hT₂d, hT₂l⟩ := (g₀'.tri_iff (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t₂).1 T1'
  obtain ⟨h, hh, hhd, hhl⟩ := (g₀.tri_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g s).1 T2
  obtain ⟨h₂, hh₂, hh₂d, hh₂l⟩ := (g₀'.tri_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g' s₂).1 T2'
  have hS₀ : g₀.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g₀ inferInstance
  have hid : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (RingHom.id _) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp]

  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ (RingHom.id _)
    inferInstance hS₀ hid (RingHom.id_comp _).symm).1 g₀'
  have hMd := hMu M hM

  have hc1 : g₀.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0
      (T₂ * M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ C.f0 (RingHom.id _)
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) M T₂ inferInstance hM hT₂
    rwa [RingHom.comp_id] at this
  have heq := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hT.1 hT.2.1).1
    C.f0).1).unique hT hc1
  have hPT : Par Dw.mult ⊤ T := CarriesAt.par_of_tri (fun τ i => by rw [hTd]; exact Units.ne_zero _) hTl
  have hPT₂ : Par Dw.mult ⊤ T₂ := CarriesAt.par_of_tri (fun τ i => by rw [hT₂d]; exact Units.ne_zero _) hT₂l
  have hPM : Par Dw.mult ⊤
      (M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have e : M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) =
        T₂⁻¹ * T := by
      rw [heq, ← mul_assoc, Mat.inv_mul hPT₂.det_ne, one_mul]
    rw [e]
    exact hPT₂.inv.mul hPT
  have hMl : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hik => by
    have h0 := (hPM τ).2.2.2 i k i.2 hik
    exact hinj (by rw [map_zero]; exact h0)

  have hSg : g.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g inferInstance
  have hidK : x = spMap (RingHom.id K) ≫ x := by
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨N, hN, -⟩, -⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g _ φ' _ (RingHom.id K)
    inferInstance hSg hidK (by rw [RingHom.id_comp]; exact hφ)).1 g'
  have c1 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (N * h.map (RingHom.id K)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g _ _ _ g'
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom (RingHom.id K) h N inferInstance hh hN
    rwa [RingHom.id_comp] at this
  have c2 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ g' (RingHom.id _)
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom M h₂ inferInstance hM hh₂
    rwa [RingHom.comp_id] at this
  have heqK := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hh₂.1 hh₂.2.1).1
    g').1).unique c1 c2
  have hmid : h.map (RingHom.id K) = h := funext fun τ => by ext i j; rfl
  rw [hmid] at heqK
  have hPh : Par Dw.mult ⊤ h := CarriesAt.par_of_tri (fun τ i => by rw [hhd]; exact Units.ne_zero _) hhl
  have hPh₂ : Par Dw.mult ⊤ h₂ := CarriesAt.par_of_tri (fun τ i => by rw [hh₂d]; exact Units.ne_zero _) hh₂l
  have hPMK := par_map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom hMd hMl
  have hNe : N = h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom * h⁻¹ := by
    rw [← heqK, mul_assoc, Mat.mul_inv hPh.det_ne, mul_one]
  have hPN : Par Dw.mult ⊤ N := by
    rw [hNe]
    exact (hPh₂.mul hPMK).mul hPh.inv
  exact ⟨fun τ i => Units.mk0 _ (CarriesAt.Par.diag_ne hPN τ i),
    (g.tri_iff _ g' _).2 ⟨N, hN, fun _ _ => rfl, fun τ i k hik => (hPN τ).2.2.2 i k i.2 hik⟩⟩

theorem carriesTri : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)},
    ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  intro E _ _ _ H Dw l Xo c Y C K _ φ φ' x p g g' hg hg'
  exact tri_of_carries C hg hg'

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames ev ev_appLE ev_res ev_congr le_preimage_comp le_preimage_mono vec actR_vec
  spMap_ev_top ev_appTop eigLie vec_mem_eigLie initSpan)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.CompHS (flagOpen dense_flagOpen opensRange_inc)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

def cstF (X : FlagCover Y) (V : X.YY.Opens) (r : c.F) : Γ(X.YY, V) :=
  resG X.YY (le_top : V ≤ ⊤) ((X.π ≫ Y.s).appTop.hom (toΓ c.F r))

theorem ev_cstF (X : FlagCover Y) {S : Type} [CommRing S] (w : Sp S ⟶ X.YY) (V : X.YY.Opens) (hw : ⊤ ≤ w ⁻¹ᵁ V)
    (ψ : c.F →+* S) (hψ : w ≫ X.π ≫ Y.s = spMap ψ) (r : c.F) : ev w V hw (cstF X V r) = ψ r := by
  unfold cstF
  rw [ev_res w le_top hw le_top, ev_appTop]
  have key : (ev (w ≫ X.π ≫ Y.s) ⊤ le_top).comp (toΓ c.F) = ψ := by
    have : spMap ((ev (w ≫ X.π ≫ Y.s) ⊤ le_top).comp (toΓ c.F)) = spMap ψ := (spMap_ev_top _).trans hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  exact RingHom.congr_fun key r

def eigDefect (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (a : 𝓞 E)
    (j : Fin (X.F.M k).n) : Γ(X.YY, X.F.U k) :=
  ∑ m, (X.π.appLE (X.F.M k).U (X.F.U k) (X.F.le k)).hom ((X.F.M k).ρ a j m) * X.F.u k σ m i -
    cstF X (X.F.U k) (embK c σ a) * X.F.u k σ j i

theorem ev_eigDefect (X : FlagCover Y) {S : Type} [CommRing S] (w : Sp S ⟶ X.YY) (k : X.F.J)
    (hw : ⊤ ≤ w ⁻¹ᵁ X.F.U k) (ψ : c.F →+* S) (hψ : w ≫ X.π ≫ Y.s = spMap ψ) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (a : 𝓞 E) (j : Fin (X.F.M k).n) :
    ev w _ hw (eigDefect X k σ i a j) =
      (((X.F.M k).ρ a).map (ev (w ≫ X.π) (X.F.M k).U (X.F.inM hw rfl))).mulVec
        (fun m => X.F.uAt k w hw σ m i) j - ψ (embK c σ a) * X.F.uAt k w hw σ j i := by
  unfold eigDefect
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, map_mul, ev_cstF X w _ hw ψ hψ]
  simp only [map_mul, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_appLE w X.π (X.F.le k) hw (X.F.inM hw rfl)]
  rfl

theorem eigDefect_eq_zero (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (a : 𝓞 E)
    (j : Fin (X.F.M k).n) : eigDefect X k σ i a j = 0 := by
  refine GlobalTheory.DRFlag.AdaptedOfStep.eq_zero_of_dense (dense_flagOpen X) _ fun K _ w hw hwD => ?_
  obtain ⟨ψ, hψ⟩ : ∃ ψ : c.F →+* K, spMap ψ = w ≫ X.π ≫ Y.s := ⟨_, spMap_ev_top _⟩
  letI : Algebra c.F K := ψ.toAlgebra
  have hall : ⊤ ≤ w ⁻¹ᵁ flagOpen X := ((IsLocalRing.closed_point_mem_iff (U := w ⁻¹ᵁ flagOpen X)).1 hwD).ge
  have hr : Set.range w ⊆ Set.range X.inc := by
    rintro _ ⟨p, rfl⟩
    have : w p ∈ flagOpen X := hall (Set.mem_univ p)
    rw [← opensRange_inc X] at this
    exact this
  let w' : Sp K ⟶ X.Yo := IsOpenImmersion.lift X.inc w hr
  have hw' : w' ≫ X.inc = w := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨y, hyd⟩ : ∃ y : Sp K ⟶ Xo.XF c, y = w' ≫ pullback.snd X.π Y.j := ⟨_, rfl⟩
  have hx : w ≫ X.π = y ≫ Y.j := by
    rw [← hw', hyd, Category.assoc, Category.assoc, pullback.condition]
  have hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    have e1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    calc y ≫ pullback.snd _ _ = (w ≫ X.π) ≫ Y.s := by rw [hx, Category.assoc, e1]
      _ = spMap ψ := by rw [Category.assoc, hψ]
  have htop := X.top K y hy w hx k hw σ
  have hmem : X.F.vecAt k w hw hx σ i ∈ eigLie c (y ≫ Y.j) σ := by
    rw [← htop]; exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have heig := (vec_mem_eigLie (X.F.M k).toMChart (y ≫ Y.j) (X.F.inM hw hx) σ
    (fun m => X.F.uAt k w hw σ m i)).1 hmem a
  rw [ev_eigDefect X w k hw ψ hψ.symm, ev_congr hx _ _ (X.F.inM hw hx), heig]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact sub_self _

theorem actR_vecAt (X : FlagCover Y) {R : Type} [CommRing R] (φ : c.F →+* R) (z : Sp R ⟶ X.YY) (k : X.F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hφ : z ≫ X.π ≫ Y.s = spMap φ) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (a : 𝓞 E) :
    actR Y.t.act a (X.F.vecAt k z hz rfl σ i) = φ (embK c σ a) • X.F.vecAt k z hz rfl σ i := by
  show actR Y.t.act a (vec _ _ _ _) = φ (embK c σ a) • vec _ _ _ _
  rw [actR_vec, ← map_smul]
  congr 1
  funext j
  have h := ev_eigDefect X z k hz φ hφ σ i a j
  rw [eigDefect_eq_zero, map_zero] at h
  rw [Pi.smul_apply, smul_eq_mul]
  exact sub_eq_zero.1 h.symm

theorem existsUnique_of_retraction {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ}
    (v e : Fin m → N) (ρ : N →ₗ[R] Fin m → R) (hρ : ∀ i, ρ (v i) = Pi.single i 1) (P : N → Prop)
    (hv : ∀ i, P (v i)) (he : ∀ w, P w → ∃! a : Fin m → R, w = ∑ k, a k • e k) (hli : LinearIndependent R v)
    (w : N) (hw : P w) : ∃! a : Fin m → R, w = ∑ i, a i • v i := by
  classical
  choose A hA _ using fun i => he (v i) (hv i)
  let C : Matrix (Fin m) (Fin m) R := Matrix.of fun k i => ρ (e k) i
  have hAC : Matrix.of A * C = 1 := by
    ext i j
    have h := congrFun (congrArg ρ (hA i)) j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hρ, map_sum] at h
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine Eq.trans ?_ (h.symm.trans ?_)
    · rfl
    · rw [Pi.single_apply]; simp only [eq_comm]
  have hCA : C * Matrix.of A = 1 := mul_eq_one_comm.1 hAC
  have hek : ∀ k, e k = ∑ i, C k i • v i := fun k => by
    simp only [hA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ j, (∑ i, C k i * A i j) = (1 : Matrix (Fin m) (Fin m) R) k j := fun j => by
      rw [← hCA, Matrix.mul_apply]; rfl
    simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  obtain ⟨b, hb, -⟩ := he w hw
  have hex : w = ∑ i, (∑ k, b k * C k i) • v i := by
    rw [hb]
    simp only [Finset.sum_smul, ← smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [hek k, Finset.smul_sum]
  refine ⟨_, hex, fun a ha => funext fun i => ?_⟩
  exact (Fintype.linearIndependent_iffₛ.1 hli) _ _ (ha.symm.trans hex) i

theorem framesExist_flagCover (X : FlagCover Y) : FramesExist X := by
  intro R _ _ φ z k hz hφ
  have hf : Nonempty (GlobalTheory.ShFam.EigFrame Y φ (z ≫ X.π)) := by
    have hc : (z ≫ X.π) ≫ Y.s = spMap φ ≫ spMap (RingHom.id c.F) := by
      rw [Category.assoc, hφ]
      exact ((congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)).symm
    have h := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y R φ (pullback.lift _ _ hc)
      (pullback.lift_snd _ _ _)
    rwa [pullback.lift_fst] at h
  obtain ⟨f⟩ := hf
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun σ i => X.F.vecAt k z hz rfl σ i)
    (fun σ i a => actR_vecAt X φ z k hz hφ σ i a) (fun σ w hw => ?_), fun σ i => rfl⟩
  obtain ⟨W, hW⟩ := X.F.uAt_split k z hz σ
  refine existsUnique_of_retraction (fun i => X.F.vecAt k z hz rfl σ i) (f.vec σ)
    ((Matrix.mulVecLin W).comp (vec (X.F.M k).toMChart (z ≫ X.π) (X.F.inM hz rfl)).symm.toLinearMap)
    (fun i => ?_) (fun u => ∀ a, actR Y.t.act a u = φ (embK c σ a) • u)
    (fun i a => actR_vecAt X φ z k hz hφ σ i a) (fun u hu => f.existsUnique_sum σ u hu)
    (X.F.linearIndependent_vecAt k z hz rfl σ) w hw
  show W.mulVec ((vec _ _ _).symm (vec _ _ _ _)) = _
  rw [LinearEquiv.symm_apply_apply]
  funext r
  have := congrFun (congrFun hW r) i
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [Matrix.mulVec, dotProduct, this, Pi.single_apply]

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlagSpec

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt stalkPt genericPt constF)
open GlobalTheory.VarFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)

theorem sp_comp_sp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ψ : S →+* T) (φ : R →+* S) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem eq_spMap_of_comp {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {ι : R →+* R'}
    (hι : Function.Injective ι) {h : Sp R ⟶ Sp S} {φ : S →+* R} (e : spMap ι ≫ h = spMap (ι.comp φ)) :
    h = spMap φ := by
  obtain ⟨p, rfl⟩ := Spec.map_surjective h
  have h1 : ι.comp p.hom = ι.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← e, ← sp_comp_sp]; rfl
  have hp : p.hom = φ := RingHom.ext fun a => hι (RingHom.congr_fun h1 a)
  rw [← hp]; rfl

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genericPt_genStr {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    {e : F ≃+* c.F} (C : FlagCpt Z e) :
    genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genStr Z = spMap (constF e C.Y) := by
  letI := (constF e C.Y).toAlgebra
  rw [← Category.assoc, ← C.y0_x, Category.assoc, GlobalTheory.Toroidal.genStr, Z.jQ_over]
  exact GlobalTheory.ShFam.ptF_snd _

theorem flagSpaceComponent_stalkPoint_over_coefficientField {Y : Model Xo c (RingHom.id c.F)} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Y e) (y : C.Y.X)
    {φ : c.F →+* C.Y.X.presheaf.stalk y} {f : EigFrame Y φ (stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y)}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h : f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t) :
    stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y ≫ Y.s = spMap φ := by
  have hg : GlobalTheory.Toroidal.genι Y ≫ Y.s = GlobalTheory.Toroidal.genStr Y := by
    rw [GlobalTheory.Toroidal.genι, GlobalTheory.Toroidal.genStr, pullback.condition]
    exact (congrArg (pullback.snd Y.s (spMap (RingHom.id c.F)) ≫ ·) (spMap_id' _)).trans (Category.comp_id _)
  refine eq_spMap_of_comp (IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField) ?_
  rw [← h.2.1, ← genericPt_genStr C, ← hg]
  have h1 := congrArg (· ≫ Y.s) h.1
  simp only [Category.assoc] at h1
  exact h1.symm

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [dualMap]

theorem isFrameAt_map {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {z : Sp R ⟶ Z} {k : F.J} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k}
    {g : EigFrame Y φ (z ≫ π)} (hg : IsFrameAt F z k hz g) (ψ : R →+* R') {φ' : c.F →+* R'}
    {g' : EigFrame Y φ' ((spMap ψ ≫ z) ≫ π)} (hg' : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v g embτ basisIdx) ψ g') :
    IsFrameAt F (spMap ψ ≫ z) k (GlobalTheory.FlagMod.le_preimage_comp _ hz) g' := by
  intro σ i
  rw [hg' σ i, hg σ i, ← GlobalTheory.FlagMod.tanPull_left ψ (Category.assoc _ _ _).symm,
    F.tanPull_vecAt k ψ z hz _ rfl rfl]

theorem co_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {R : Type} [CommRing R] {φ : c.F →+* R} (z : Sp R ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') {g g' : EigFrame Y φ (z ≫ π)} (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') (τ : E →+* ℂ) :
    (g.co g' τ).BlockTriangular id ∧ ∀ i, IsUnit (g.co g' τ i i) := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have e : g.co g' τ = (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) := by
    refine GlobalTheory.ShFam.EigFrame.co_eq fun i => ?_
    rw [funext (hg τ), hg' τ i, GlobalTheory.LieMet.isComb_iff]
    exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i
  rw [e]
  exact ⟨F.B_map_tri k k' τ _, fun i => (F.isUnit_B_diag k k' τ i).map (GlobalTheory.FlagMod.ev z _ hh)⟩

end GlobalTheory.VarFlagSpec


open GlobalTheory.VarFlagSpec GlobalTheory.ShFam in
theorem GlobalTheory.VarFlag.rel_specialise : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y),
    GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C →
    ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ X.YY) (v : Sp A ⟶ C.Y.X),
    u ≫ X.π = v ≫ C.π ≫ GlobalTheory.Toroidal.genι Y →
    GlobalTheory.VarFlag.Rel X.F C (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) →
    GlobalTheory.VarFlag.Rel X.F C (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C hCT A _ _ _ u v huv hL
  set ι := algebraMap A (FractionRing A) with hι_def
  have hι : Function.Injective ι := IsFractionRing.injective A (FractionRing A)
  set ρ := IsLocalRing.residue A with hρ_def

  set y := v (IsLocalRing.closedPoint A) with hy_def
  let ψA : C.Y.X.presheaf.stalk y →+* A := (Scheme.stalkClosedPointTo v).hom
  have hv : v = spMap ψA ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk v).symm
  obtain ⟨φ₁, f, t, hf0, -⟩ := C.gr_spec y
  have hxA : u ≫ X.π = spMap ψA ≫ (stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y) := by
    rw [huv, hv, Category.assoc]
  have hsA : u ≫ X.π ≫ Y.s = spMap (ψA.comp φ₁) := by
    rw [← Category.assoc, hxA]
    simp only [Category.assoc]
    rw [flagSpaceComponent_stalkPoint_over_coefficientField C y hf0, sp_comp_sp]

  obtain ⟨kk, hkk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover u
  obtain ⟨gA, hgA⟩ := hFE A (ψA.comp φ₁) u kk hkk hsA
  obtain ⟨fA, hfA⟩ := f.exists_isMap ψA (φ' := ψA.comp φ₁) (x' := u ≫ X.π) rfl hxA

  obtain ⟨φL, k0, hz0, gL, hsL, hgL, hcL⟩ := hL
  obtain rfl : φL = ι.comp (ψA.comp φ₁) := GlobalTheory.ShFam.EigLoc.spMap_inj (by
    rw [← hsL, Category.assoc, hsA, sp_comp_sp])
  have hxL : (spMap ι ≫ u) ≫ X.π = spMap ι ≫ (u ≫ X.π) := Category.assoc _ _ _
  obtain ⟨fL, hfL⟩ := fA.exists_isMap ι (φ' := ι.comp (ψA.comp φ₁)) rfl hxL
  obtain ⟨gL', hgL'⟩ := gA.exists_isMap ι (φ' := ι.comp (ψA.comp φ₁)) rfl hxL
  have hgL'fr := isFrameAt_map X.F hgA ι hgL'
  have hfLf : f.IsMap (ι.comp ψA) fL := fun τ i => by
    rw [hfL τ i, hfA τ i, GlobalTheory.GradedPieces.dual_comp]
  have hcF : C.Carries (spMap ι ≫ v) fL :=
    ⟨y, ι.comp ψA, φ₁, f, t, 1, by rw [hv, ← Category.assoc, sp_comp_sp], hf0,
      hfLf.tri rfl (by rw [hxL, hxA, ← Category.assoc, sp_comp_sp])⟩
  obtain ⟨t1, ht1⟩ := hCT (FractionRing A) _ _ _ _ fL gL hcF hcL
  have hfLid : fL.IsMap (RingHom.id _) fL := fun τ i => by rw [spMap_dualMap_id, Category.id_comp]

  have key : ∀ τ, (fA.co gA τ).BlockTriangular id ∧ ∀ i, IsUnit (fA.co gA τ i i) := by
    intro τ
    have h1 := ht1.co τ hfLid
    have h2 := co_of_isFrameAt X.F _ k0 kk hz0 _ hgL hgL'fr τ
    have hm : fL.co gL' τ = (fA.co gA τ).map ι := hfL.co τ hgL' hxL
    have hT1 : (fL.co gL τ).BlockTriangular id := fun a i h => h1.1 a i h
    have htri : (fL.co gL' τ).BlockTriangular id := by
      rw [← fL.co_mul gL gL' τ]; exact hT1.mul h2.1
    have hMt : (fA.co gA τ).BlockTriangular id := fun a i h => hι (by
      have := htri h
      rw [hm, Matrix.map_apply] at this
      rw [this, map_zero])
    refine ⟨hMt, fun i => ?_⟩
    have hdet := fA.isUnit_det_co gA τ
    rw [Matrix.det_of_upperTriangular hMt] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => fA.co gA τ j j) (Finset.mem_univ i)) hdet

  have hxk : (spMap ρ ≫ u) ≫ X.π = spMap ρ ≫ (u ≫ X.π) := Category.assoc _ _ _
  obtain ⟨fk, hfk⟩ := fA.exists_isMap ρ (φ' := ρ.comp (ψA.comp φ₁)) rfl hxk
  obtain ⟨gk, hgk⟩ := gA.exists_isMap ρ (φ' := ρ.comp (ψA.comp φ₁)) rfl hxk
  have hfkf : f.IsMap (ρ.comp ψA) fk := fun τ i => by
    rw [hfk τ i, hfA τ i, GlobalTheory.GradedPieces.dual_comp]
  have hmk : ∀ τ, fk.co gk τ = (fA.co gA τ).map ρ := fun τ => hfk.co τ hgk hxk
  refine ⟨ρ.comp (ψA.comp φ₁), kk, GlobalTheory.FlagMod.le_preimage_comp _ hkk, gk, ?_, isFrameAt_map X.F hgA ρ hgk, ?_⟩
  · rw [Category.assoc, hsA, sp_comp_sp]
  · refine ⟨y, ρ.comp ψA, φ₁, f, t, fun τ i => (((key τ).2 i).map ρ).unit,
      by rw [hv, ← Category.assoc, sp_comp_sp], hf0,
      by rw [hxk, hxA, ← Category.assoc, sp_comp_sp], rfl, fun τ i => ⟨fun a => fk.co gk τ a i, ?_, ?_, ?_⟩⟩
    · rw [hmk]; beta_reduce; rw [Matrix.map_apply, IsUnit.unit_spec]
    · intro a ha
      rw [hmk]; beta_reduce; rw [Matrix.map_apply, (key τ).1 ha, map_zero]
    · rw [← funext (hfkf τ)]
      exact fk.co_spec gk τ i
end
end

