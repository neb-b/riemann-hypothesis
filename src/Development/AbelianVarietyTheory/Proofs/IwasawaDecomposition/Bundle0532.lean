module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharBundlePrimitive
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBot
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem riemannRoch_ne_bot_of_holomorphicSection_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ)
    (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  intro F _ Y σ R D hR hH
  refine hR ?_
  have P := GlobalTheory.Cartier.presents_toLB D
  have hs : ∀ s : (Y.lb D).Sec, s = 0 := fun s => by
    have hm : P.rat s ∈ Y.H0 D := P.rat_mem s
    rw [hH, Submodule.mem_bot] at hm
    exact P.rat_injective (hm.trans (map_zero P.rat).symm)
  have hx : ∀ x : SecC Y.str σ (Y.lb D), x = 0 := fun x => by
    have hle : Submodule.span ℂ (Set.range (SecC.of Y.str σ : (Y.lb D).Sec → _)) ≤ ⊥ :=
      Submodule.span_le.2 (by
        rintro _ ⟨s, rfl⟩
        rw [hs s, map_zero]
        exact zero_mem _)
    exact (Submodule.mem_bot ℂ).1 (hle (SecC.span_range_of.ge Submodule.mem_top))
  have hb := GlobalTheory.AnRead.bijective_valC Y.isProjOver R P.isLB
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  obtain ⟨x, hxf⟩ := hb.2 ⟨f, hf⟩
  rw [hx x, map_zero] at hxf
  exact (congrArg Subtype.val hxf).symm

end GlobalTheory.ShFam.Hor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem smooth_gtCoord_q {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    (c : GtCoord (⊥ : Ideal R) D 0 H) : Smooth c.q.left := by
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  obtain ⟨-, -, -, -, h1, -⟩ := (GlobalTheory.splitTorus_properties (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1))))).1 D.X
  have : Smooth (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ D.X) _
  have H' := (GlobalTheory.UnitRigidity.isPullback_act c.i c.q c.isKernel).map (Over.forget _)
  have a1 : Smooth (snd (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X)
      (thickObj R ⊥ 0 H)).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus _ D.X).hom (thickObj R ⊥ 0 H).hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H'.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact c.q.left)⟩ a1

theorem Ray.smooth_q {oa : D.OAct O} (Y : Ray oa) : Smooth Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc := smooth_gtCoord_q c
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F

  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ

  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]

  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]

  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.LevelPlaceSep

theorem not_mem_two {D : D7} (P : PlE D.host) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : P ∈ placesOver D.host.E p) (h2 : P ∈ placesOver D.host.E q) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have e := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
  push_cast at e
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  have h1' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h2
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h1') (P.asIdeal.mul_mem_left _ h2')

theorem mem_placesOver_of_comap {D : D7} {P P' : PlE D.host}
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) {p : ℕ}
    (hP : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have e : ((p : ℕ) : 𝓞 D.host.E) = (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) (p : 𝓞 (maximalRealSubfield D.host.E)) := (map_natCast _ p).symm
  show ((p : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
  have hP' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hP
  rw [e, ← Ideal.mem_comap, ← h, Ideal.mem_comap, ← e]
  exact hP'

theorem isConjPl_conjPlE {D : D7} (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.LocM.complexConj_eq_conj,
      GlobalTheory.FixedPlaceSplit.host_conj_conj]
  rw [this]

theorem eq_of_qpOf {D : D7} (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hPq : ∀ v, NG.OverPl (Pq v) v) (S : Finset (PlE D.host)) {P P' : PlE D.host}
    (hP : P ∈ qpOf D Pq S) (hP' : P' ∈ qpOf D Pq S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) (hv' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) : P = P' := by
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P P' (hv'.trans hv.symm) with e | e
  · exact e.symm
  have hw : (Pq v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal := hPq v
  have hS : Pq v ∈ S := by
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P (Pq v) (hw.trans hv.symm) with e' | e'
    · rw [e']; exact qpOf_sub D Pq S hP
    · rw [e', ← e]; exact qpOf_sub D Pq S hP'
  exact (qpOf_eq D Pq S hP hv hS).trans (qpOf_eq D Pq S hP' hv' hS).symm

theorem g_ne_g {D : D7} {k k' : Fin 2} (h : k ≠ k') : D.host.g k ≠ D.host.g k' := by
  have h0 := D.host.g_ne
  fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]

theorem levelPlaces_sep : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  intro D T i Q Pq sp hPq hQs hQ hpDs hsp
  obtain ⟨pp, hpp, hne, hpD⟩ : ∃ pp : ℕ, pp.Prime ∧ (∀ k, pp ≠ D.host.g k) ∧
      ∀ P, P ∈ T.pD i ↔ P ∈ placesOver D.host.E pp := by
    refine ⟨if T.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_,
      fun P => by rw [← Finset.mem_coe, T.pD_eq i]⟩
    · split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    · intro k
      split_ifs
      · exact (D.host.pde_ne_g k).2
      · exact (D.host.pde_ne_g k).1
  have hG : ∀ kv, NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := fun kv => D.naut.plGw_over kv.1 kv.2
  have c2 : ∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i) := fun P hP hP' =>
    (hQ P (qpOf_sub D Pq Q hP)).1 (qpOf_sub D Pq _ hP')
  have c3 : ∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i) := fun kv =>
    ⟨fun h => (hQ _ (qpOf_sub D Pq Q h)).2 kv.1 (hG kv),
     fun h => not_mem_two _ hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD _).1 (qpOf_sub D Pq _ h)) (hG kv)⟩
  have c4 : ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ h
    by_cases hk : k = k'
    · subst hk
      have : v = v' := D.naut.plGw_inj k h
      rw [this]
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (by rw [h]; exact hG ⟨k', v'⟩)).elim
  refine ⟨?_, c2, c3, c4⟩
  intro P P' hP hP' hv
  have hcP : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P).w_under; rw [hsp P hP] at this; exact this
  have hcP' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P').w_under; rw [hsp P' hP'] at this; rw [this, hv]
  have hc : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := hcP.trans hcP'.symm
  have same : ∀ {p : ℕ}, P' ∈ placesOver D.host.E p → P ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc.symm h
  have same' : ∀ {p : ℕ}, P ∈ placesOver D.host.E p → P' ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc h
  rcases hP with hP | hP | ⟨kv, rfl⟩ <;> rcases hP' with hP' | hP' | ⟨kv', rfl⟩
  · exact eq_of_qpOf Pq hPq Q hP hP' _ hcP hcP'
  · exact ((hQ P (qpOf_sub D Pq Q hP)).1 ((hpD P).2 (same ((hpD P').1 (qpOf_sub D Pq _ hP'))))).elim
  · exact ((hQ P (qpOf_sub D Pq Q hP)).2 kv'.1 (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).1 ((hpD P').2 (same' ((hpD P).1 (qpOf_sub D Pq _ hP))))).elim
  · exact eq_of_qpOf Pq hPq _ hP hP' _ hcP hcP'
  · exact (not_mem_two P hpp (D.host.g_prime kv'.1) (hne kv'.1) ((hpD P).1 (qpOf_sub D Pq _ hP))
      (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).2 kv.1 (same' (hG kv))).elim
  · exact (not_mem_two P' hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD P').1 (qpOf_sub D Pq _ hP'))
      (same' (hG kv))).elim
  · obtain ⟨k, v⟩ := kv
    obtain ⟨k', v'⟩ := kv'
    by_cases hk : k = k'
    · subst hk
      rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (NX.pG D ⟨k, v⟩) (NX.pG D ⟨k, v'⟩) hc.symm with e | e
      · exact e.symm
      · have hc2 := isConjPl_conjPlE (NX.pG D ⟨k, v⟩)
        rw [← e] at hc2
        exact (D.naut.plGw_nconj k v v' hc2).elim
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (same (hG ⟨k', v'⟩))).elim

end GlobalTheory.LevelPlaceSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

def IsTwInv (φ : InvFun (𝓞 E)) : Prop :=
  ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def IsPosFn (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Nontrivial X], ∀ be ∈ levelForms H 1 X,
    (∀ y, y ≠ 0 → 0 < be y y) → 0 < φ.evalZ be

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def polOf (Z : Model Xo c β) (m : ℕ) (BD : EffCartierData Z.X) : LB Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm Z) m) (GlobalTheory.CechPic.dual BD.lb)

def selfTor (Z : Model Xo c β) (h₁ : SmoothOfRelativeDimension D.dim (genStr Z)) (h₂ : FinalTheorems.Snc (genBdIdeal Z))
    (h₃ : ∀ x ∈ genBd Z, HasToricChart Z x) (BD : EffCartierData Z.X)
    (h₄ : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) (h₅ : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support)
    (m : ℕ) (hm : 0 < m) : TorModel Z where
  Z := Z
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Z.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Z.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := h₁
  snc := h₂
  toric := h₃
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := BD
  BD_supp := h₄
  BD_pos := h₅
  m0 := m
  torModel_multiplicity_pos := hm

end Defs

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem preimage_le_of_isTanAtG (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ v ⁻¹ᵁ W := by
  intro y hy
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero y
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ T := hy
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (hT h₁)
  rw [← epsZero_comp_of_isTanAtG t hv] at h₂
  exact h₂

theorem tanForm_dUnit (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(t.G.left, W))
    (a b : Γ(Sp k, T))
    (e : (v.appLE W _ (preimage_le_of_isTanAtG t hv hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (tanForm t hv).app T (pullbackSections x (omega t.G) hT (dUnit t.G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have c := baseMap_d (sec_hom (MonObj.one (X := t.G))) (sec_hom (epsZero k)) hv.1
    (epsZero_comp_of_isTanAtG t hv) hW hT hV (preimage_le_of_isTanAtG t hv hW hT) f
  refine (congrArg ((epsIso k).hom.app T) c).trans ?_
  rw [e, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, GlobalTheory.LB.resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : T ≤ ⊤)))).trans (_root_.mul_one b)

variable {k' : Type} [CommRing k'] (φ : k →+* k')

theorem spMap_dualMap_comp : spMap (Formalism.L2.Pj.dualMap φ) ≫ (specO k (DualNumber k)).hom =
    (specO k' (DualNumber k')).hom ≫ spMap φ := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_epsFn :
    (spMap (Formalism.L2.Pj.dualMap φ)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Formalism.L2.Pj.dualMap φ))) DualNumber.eps).symm.trans ?_
  refine congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom ?_
  change Formalism.L2.Pj.dualMap φ DualNumber.eps = _
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem tanForm_baseChange {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (hv : IsTanAtG t x v)
    (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V)
    (s : Γ(omega t.G, V)) :
    ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      (spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤)) := by
  have := t.semi
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V)
      (x := x (spMap φ y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap φ y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle s)
    have hf' : dUnit t.G c.le f = resM (omega t.G) hle s := hf
    have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      (v.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)
    have e₁ := tanForm_dUnit t hv c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_dualMap_epsFn φ)))
    have e₂ := tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a)
      ((spMap φ).appLE T _ le_rfl b) (by
        refine (appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (tanForm t hv') le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap φ) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap φ) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (tanForm t hv) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem tanEv_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (v : Sp (DualNumber k) ⟶ t.G.left) (hv : IsTanAtG t x v) (k' : Type) [CommRing k'] (φ : k →+* k') (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)), tanEv t hv' h' s = φ (tanEv t hv h s) := by
  intro E _ _ _ H X t k _ x V h v hv k' _ φ hv' h' s
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (tanForm_baseChange t φ h hv hv' h' s)).trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (appLE_top (spMap φ) _)).trans ?_
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _)

end GlobalTheory.LocM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_value_at_theta_point : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  first | exact @GlobalTheory.KeyFourth.value_at_thetaPt | exact GlobalTheory.KeyFourth.value_at_thetaPt | (intros; apply GlobalTheory.KeyFourth.value_at_thetaPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace

namespace GlobalTheory


open Scheme.IdealSheafData in
theorem vanishingIdeal_comap_of_isOpenImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (B : Closeds X) (B' : Closeds A), (∀ x : A, x ∈ B' ↔ g x ∈ B) → (Scheme.IdealSheafData.vanishingIdeal B).comap g = Scheme.IdealSheafData.vanishingIdeal B' := by
  intro A X g _ B B' h
  have hB : (vanishingIdeal B).support = B := by
    ext x
    simp
  have hr : (vanishingIdeal B).radical = vanishingIdeal B := by
    rw [← vanishingIdeal_support, hB]
  have hs : ((vanishingIdeal B).comap g).support = B' := by
    ext x
    simp [support_comap, h]
  rw [← hs, vanishingIdeal_support]
  ext U : 2
  rw [radical_ideal, ideal_comap_of_isOpenImmersion, ← Ideal.comap_radical, ← radical_ideal, hr]

end GlobalTheory
end

