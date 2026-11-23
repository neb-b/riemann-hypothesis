module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsTensorOrderOfCover
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TranslateEq

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
open scoped TensorProduct

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]

theorem chart_sep [Finite T] (Γ : QFGroup R T) (B : Type) [CommRing B] [Algebra R B]
    (c : Spec (CommRingCat.of B) ⟶ Γ.G.left) [IsOpenImmersion c]
    (hc : c ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (I : Type) (_ : Finite I) (τ : I → T) (e : I → B →ₐ[R] FractionRing R),
      (∀ i, Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ c = (Γ.pt (τ i)).left) ∧
      ∀ b, (∀ i, e i b = 0) → b = 0 := by
  classical
  let I := {t : T // Set.range (Γ.pt t).left ⊆ Set.range c}
  have lift : ∀ i : I, ∃ e : B →ₐ[R] FractionRing R,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ c = (Γ.pt i.1).left := by
    intro i
    let g := IsOpenImmersion.lift c (Γ.pt i.1).left i.2
    have hg : g ≫ c = (Γ.pt i.1).left := IsOpenImmersion.lift_fac _ _ _
    let φ : B →+* FractionRing R := (Spec.preimage g).hom
    have hφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
    have hcomp : φ.comp (algebraMap R B) = algebraMap R (FractionRing R) := by
      have h1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R B))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, ← hc, ← Category.assoc, hg]
        exact Over.w (Γ.pt i.1)
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    refine ⟨{ φ with commutes' := fun r => congr($hcomp r) }, ?_⟩
    exact (congrArg (· ≫ c) hφ).trans hg
  choose e he using lift
  refine ⟨I, inferInstance, Subtype.val, e, he, fun b hb => ?_⟩
  haveI : Flat Γ.G.hom := Γ.flat
  haveI : Module.Flat R B := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := hc ▸ inferInstance
    rw [Flat.SpecMap_iff] at this
    exact (RingHom.flat_algebraMap_iff).1 this
  haveI : IsReduced (pullback Γ.G.hom (genPt R).hom) := Γ.gen_reduced
  have hred : _root_.IsReduced (B ⊗[R] FractionRing R) := by
    have h1 : IsReduced (pullback (c ≫ Γ.G.hom) (genPt R).hom) :=
      isReduced_of_isOpenImmersion ((pullbackRightPullbackFstIso Γ.G.hom (genPt R).hom c).inv ≫ pullback.snd _ _)
    rw [hc] at h1
    have h2 : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) := h1
    have h3 := isReduced_of_isOpenImmersion (pullbackSpecIso R B (FractionRing R)).inv
    exact (affine_isReduced_iff _).1 h3
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  rw [map_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun Q hQ => ?_)
  let P : Spec (CommRingCat.of B) := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R).toRingHom ⟨Q, hQ⟩
  have hP : (Γ.G.hom (c P)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, hc]
    refine eq_bot_iff.2 fun r hr => ?_
    have h1 : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R) (algebraMap R B r) ∈ Q := hr
    rw [AlgHom.commutes, ← (Algebra.TensorProduct.includeRight :
      FractionRing R →ₐ[R] B ⊗[R] FractionRing R).commutes] at h1
    by_contra h0
    have h2 : algebraMap R (FractionRing R) r ≠ 0 := fun h =>
      h0 ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R (FractionRing R)) r h)
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 ((Ne.isUnit h2).map _))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hP
  have hr : Set.range (Γ.pt t).left ⊆ Set.range c := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P, by rw [← hx, Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) x y]⟩
  have hPx : Spec.map (CommRingCat.ofHom (e ⟨t, hr⟩).toRingHom) x = P :=
    c.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, he, hx])
  have hbP : b ∈ P.asIdeal := by
    rw [← hPx]
    change e ⟨t, hr⟩ b ∈ PrimeSpectrum.asIdeal x
    rw [hb]
    exact Ideal.zero_mem _
  exact hbP

theorem sec_zero [Finite T] (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤))
    (hs : ∀ t, valAt (Γ.pt t).left ⊤ le_top s = 0) : s = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem s 0 𝒰.openCover fun k => ?_
  rw [map_zero]
  let c : Spec (CommRingCat.of (𝒰.X k)) ⟶ Γ.G.left := 𝒰.f k
  haveI : IsOpenImmersion c := 𝒰.openCover.map_prop k
  letI : Algebra R (𝒰.X k) := (Spec.preimage (c ≫ Γ.G.hom)).hom.toAlgebra
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ (𝒰.X k) c (Spec.map_preimage (c ≫ Γ.G.hom)).symm
  have h0 := hi ((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).hom (c.appTop s)) fun i => by
    have h1 := hs (τ i)
    rw [← he i, valAt_top, Scheme.Hom.comp_appTop] at h1
    exact (congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (e i).toRingHom)) (c.appTop s))).symm.trans h1
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).inv $h0)
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  exact h2

def pullSec {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A)) (f : A) : Γ(X, ⊤) :=
  j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)

theorem valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a b : Γ(X, ⊤)) : valAt x ⊤ le_top (a - b) = valAt x ⊤ le_top a - valAt x ⊤ le_top b := by
  simp only [valAt_top, map_sub]

theorem valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

section Omega

variable (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)


end Omega


end GlobalTheory.CompanionTheory.Ar.BT.TranslateEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Frames

open GlobalTheory.CompanionTheory.Ar

variable {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {i : Ω₀ →+* Ω} {Li Li₀ : Type} [AddCommGroup Li] [Module Ω Li]
  [AddCommGroup Li₀] [Module Ω₀ Li₀] {ι : Li₀ →+ Li}

theorem linearIndependent_comp_basis (h : IsExtOver i ι) {K : Type} (B : Module.Basis K Ω₀ Li₀) :
    LinearIndependent Ω fun k => ι (B k) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e : s ≃ Fin s.card := s.equivFin
  have hb : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k : K)) :=
    B.linearIndependent.comp (fun k => (e.symm k : K)) (Subtype.val_injective.comp e.symm.injective)
  have h3 := (h.2 s.card _ hb).comp e e.injective
  convert h3 using 1
  funext k
  simp

theorem exists_dual_ext (h : IsExtOver i ι) (hs : Submodule.span Ω (Set.range ι) = ⊤)
    (φ : Module.Dual Ω₀ Li₀) : ∃ φ' : Module.Dual Ω Li, ∀ e, φ' (ι e) = i (φ e) := by
  classical
  let B := Module.Basis.ofVectorSpace Ω₀ Li₀
  have hli : LinearIndependent Ω fun k => ι (B k) := linearIndependent_comp_basis h B
  have hmem : ∀ e : Li₀, ι e ∈ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    intro e
    have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [h.1]; exact Submodule.smul_mem _ _ hx
  have hsp : ⊤ ≤ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact hmem e
  let B' := Module.Basis.mk hli hsp
  refine ⟨B'.constr Ω (fun k => i (φ (B k))), fun e => ?_⟩
  have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hk : ι (B k) = B' k := (Module.Basis.mk_apply hli hsp k).symm
    rw [hk, Module.Basis.constr_basis]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul a x _ hx =>
    rw [h.1]
    simp only [map_smul, hx, smul_eq_mul, map_mul]

theorem two_frames (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li) (hext : IsExtOver i ι)
    (hs : Submodule.span Ω (Set.range ι) = ⊤) (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ)
    (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω)
    (m : Ω₀) (hL : Submodule.span W L = Submodule.span W (ι '' L₀))
    (hT : ∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) (hTb : ∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j))
    (hm : ∀ j, m • b₀ j ∈ L₀) (hπ : ∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0)
    (hint : ∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) (hκ : ∀ j, κ • b j ∈ L)
    (hb : ∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) :
    (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧
      ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  classical
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hin : ι (m • b₀ j) ∈ Submodule.span W L := by
      rw [hL]; exact Submodule.subset_span ⟨_, hm j, rfl⟩
    have key : ∀ x ∈ Submodule.span W L, T x ∈ Submodule.span W (Set.range b) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hT y hy
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy =>
        rw [Subring.smul_def, map_smul]
        have hw := Submodule.smul_mem _ w hy
        rwa [Subring.smul_def] at hw
    have hj := key _ hin
    rwa [hext.1, map_smul, hTb, smul_smul, mul_comm] at hj
  · have hv : κ • b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a)) :=
      Submodule.smul_mem _ κ (hb j)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hv
    have hcW : ∀ a, i m * c a ∈ W := by
      intro a
      obtain ⟨ψ, hψ⟩ := exists_dual_ext hext hs (π₀ a)
      have hψv : ψ (κ • b j) = c a := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hc, map_sum, Finset.sum_eq_single a]
        · rw [map_smul, hψ, hπ, if_pos rfl, map_one, smul_eq_mul, mul_one]
        · intro x _ hx
          rw [map_smul, hψ, hπ, if_neg (Ne.symm hx), map_zero, smul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      have hspan : κ • b j ∈ Submodule.span W (ι '' L₀) := by
        rw [← hL]; exact Submodule.subset_span (hκ j)
      have key : ∀ x ∈ Submodule.span W (ι '' L₀), i m * ψ x ∈ W := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨e, he, rfl⟩ := hy
          rw [hψ, ← map_mul]; exact hint a e he
        | zero => simp
        | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact W.add_mem hy hz
        | smul w y _ hy =>
          rw [Subring.smul_def, map_smul, smul_eq_mul, mul_left_comm]
          exact W.mul_mem w.2 hy
      rw [← hψv]; exact key _ hspan
    rw [mul_smul, ← hc, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [smul_smul]
    have ha := Submodule.smul_mem (Submodule.span W (Set.range fun a => ι (b₀ a))) (⟨_, hcW a⟩ : W)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at ha

end GlobalTheory.CompanionTheory.Ar.Frames
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieTangent

theorem existsUnique_semilinear_lifts :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R')
      (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E']
      (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'),
      ∃! j : E →ₛₗ[c] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  intro S G _ R R' _ _ c x E _ _ E' _ _ M M'
  have hc : Spec.map (CommRingCat.ofHom c) ≫ x = spMap c ≫ x := rfl
  have h : ∀ e, ∃ e', M'.pt e' = epsBase c hc ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base c hc (M.tan e))
  choose a ha using h
  refine ⟨{ toFun := a, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro e e'
    apply M'.inj
    rw [M'.add, ha, ha, ha, M.add, MonObj.comp_mul]
  · intro r e
    apply M'.inj
    rw [M'.pt_smul, ha, ha, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]
  · intro e
    change (M'.pt (a e)).left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt e).left
    rw [Category.comp_id, ha]
    rfl
  · intro j hj
    ext e
    refine M'.inj ((?_ : M'.pt (j e) = epsBase c hc ≫ M.pt e).trans (ha e).symm)
    apply Over.OverMorphism.ext
    have := hj e
    change _ ≫ _ = _ ≫ _ at this
    rw [Category.comp_id] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringChartPoint
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

abbrev chartRing {κ : Type} (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem stalk_value (hg : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (p : Cpt ξ) (φ : regAt ξ p →+* R)
    (z : Spec (CommRingCat.of R) ⟶ X) (hzc : centre z = p.1) (hv : ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a))
    (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)) :
    ∃ hm : genMap ξ ⟨centre z, h⟩ s ∈ regAt ξ p,
      (Scheme.stalkClosedPointTo z).hom s = φ ⟨genMap ξ ⟨centre z, h⟩ s, hm⟩ := by
  obtain ⟨pp, hpp⟩ := p
  dsimp only at hzc
  subst hzc
  refine ⟨⟨s, rfl⟩, ?_⟩
  obtain ⟨h', s', e1, e2⟩ := hv ⟨genMap ξ ⟨centre z, h⟩ s, ⟨s, rfl⟩⟩
  have e3 : s' = s := hg.inj ⟨centre z, h⟩ e1
  subst e3
  exact e2


set_option backward.isDefEq.respectTransparency false in
theorem spec_square {F : Type} [Field F] (θ : Ω →+* F) {A : Subring F} [IsLocalRing A]
    (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z)
    (hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) :
    Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  have e : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) := RingHom.ext hs
  have e1 := LieTangent.spec_centre z
  have e2 := LieTangent.spec_genMap ξ ⟨centre z, h⟩
  calc Spec.map (CommRingCat.ofHom A.subtype) ≫ z
      = Spec.map (CommRingCat.ofHom A.subtype) ≫
          (Spec.map (CommRingCat.ofHom (R := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom) ≫
            X.fromSpecStalk (centre z)) := by rw [e1]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ (Spec.map (CommRingCat.ofHom (genMap ξ ⟨centre z, h⟩)) ≫
            X.fromSpecStalk (centre z)) := by
        rw [← Category.assoc, ← Category.assoc, LieTangent.spec_comp, LieTangent.spec_comp, e]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
        exact congrArg (_ ≫ ·) e2

theorem point_of_local_subring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ (F : Type) [Field F] (θ : Ω →+* F) (A : Subring F) [IsLocalRing A], (∀ j, θ (x j / x c) ∈ A) → ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧ (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  intro X Ω _ ξ κ x c hT hc F _ θ A _ hA
  have hC : ∀ s ∈ chartRing x c, θ s ∈ A := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hA j
    | algebraMap r =>
      have : θ (algebraMap ℤ Ω r) = (r : F) := by simp
      rw [this]
      exact intCast_mem A r
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let θC : chartRing x c →+* A :=
    (θ.comp (chartRing x c).val.toRingHom).codRestrict A (fun s => hC s s.2)
  obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ ℤ κ x hT c hc
    (Ideal.comap θC (IsLocalRing.maximalIdeal A)) inferInstance
  have hunit : ∀ s (hs : s ∈ chartRing x c), unitAt ξ p s ↔ IsUnit (⟨θ s, hC s hs⟩ : A) := by
    intro s hs
    rw [← hpu ⟨s, hs⟩, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    rfl
  have hreg : ∀ a ∈ regAt ξ p, θ a ∈ A := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 ha
    obtain ⟨u, hu⟩ := (hunit s hs).1 hsu
    have h1 : (((u⁻¹ : Aˣ) : A) : F) * θ s = 1 := by
      have h2 := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at h2
      exact h2
    have h3 : θ a = (((u⁻¹ : Aˣ) : A) : F) * θ (s * a) := by
      rw [map_mul, ← mul_assoc, h1, one_mul]
    rw [h3]
    exact mul_mem ((u⁻¹ : Aˣ) : A).2 (hC _ hsa)
  let φ : regAt ξ p →+* A := (θ.comp (regAt ξ p).subtype).codRestrict A (fun a => hreg a a.2)
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 a.2
    have hua : IsUnit (⟨θ (s * a), hC _ hsa⟩ : A) := by
      have h1 : (⟨θ (s * a), hC _ hsa⟩ : A) = ⟨θ s, hC s hs⟩ * φ a :=
        Subtype.ext (map_mul θ s a)
      rw [h1]
      exact ((hunit s hs).1 hsu).mul ha
    obtain ⟨h0, -, hi⟩ := (hunit _ hsa).2 hua
    have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
    have ha0 : (a : Ω) ≠ 0 := right_ne_zero_of_mul h0
    have hinv : (a : Ω)⁻¹ ∈ regAt ξ p := by
      have h1 : (a : Ω)⁻¹ = s * (s * a)⁻¹ := by field_simp
      rw [h1]
      exact mul_mem hsu.2.1 hi
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
  obtain ⟨z, ⟨hzc, hzv⟩, -⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ hT.gen p A φ hloc
  have h : genPt ξ ⤳ centre z := by rw [hzc]; exact p.2
  have hp : (⟨centre z, h⟩ : Cpt ξ) = p := Subtype.ext hzc
  have hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s) := by
    intro s
    obtain ⟨hm, e⟩ := stalk_value hT.gen p φ z hzc hzv h s
    rw [e]
    rfl
  exact ⟨z, h, by rw [hp]; exact hpc, hs, spec_square θ z h hs⟩

end GlobalTheory.CompanionTheory.Ar.ChartPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosed
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem NormAt.isoAt_of_integrallyClosed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ),
    NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) →
      IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end GlobalTheory.CompanionTheory.Ar
end

