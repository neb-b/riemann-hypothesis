module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem isDual_of_iso (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left) (h : IsDual A B' P') (hP : P.IsLB) (x : B ⟶ B') (hx : IsIso x)
    (hm : IsMonHom x) (e : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : IsDual A B P := by
  have c : cls P hP = cls _ (pull_isLB h.isLB (lift (fst A B) (snd A B ≫ x)).left) :=
    (cls_eq_iff _ _).2 e
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    rw [evc, c, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (M : LB (A ⊗ T).left) (hM : M.IsLB) (w : T ⟶ B),
      LBIso M (ev P (fst A T) (snd A T ≫ w)) ↔ LBIso M (ev P' (fst A T) (snd A T ≫ w ≫ x)) := by
    intro T M hM w
    rw [← cls_eq_iff hM (pull_isLB hP _), ← cls_eq_iff hM (pull_isLB h.isLB _), cls_ev hP, cls_ev h.isLB, key,
      Category.assoc]
  refine ⟨hP, (isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (triv_ev_iff hP _ _).2 ?_, fun T M hM hM' ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ x)
  · rw [key, MonObj.one_comp]
    exact (triv_ev_iff h.isLB _ _).1 h.zero
  · obtain ⟨z, hz, hu⟩ := h.univ T M hM hM'
    refine ⟨z ≫ inv x, (iso T M hM _).2 ?_, fun w hw ↦ ?_⟩
    · rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · rw [← hu _ ((iso T M hM w).1 hw), Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem transport : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → P.IsLB → ∀ x : B ⟶ B', IsIso x → IsMonHom x → LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsDual A B P :=
  fun S A B B' _ _ _ P P' h hP x hx hm e ↦ isDual_of_iso S A B B' P P' h hP x hx hm e

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

variable {X Y : Scheme.{0}}

def evU {Z : Scheme.{0}} (g : Z ⟶ X) {W : X.Opens} (hg : ∀ z, g z ∈ W) (f : Γ(X, W)ˣ) : Γ(Z, ⊤)ˣ :=
  res (fun z _ => hg z : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ W) (pullU g W f)

def rat (π : X ⟶ Y) {V W : Y.Opens} (f : Γ(X, π ⁻¹ᵁ V)ˣ) (g : Γ(X, π ⁻¹ᵁ W)ˣ) :
    Γ(X, π ⁻¹ᵁ (V ⊓ W))ˣ :=
  res (π.preimage_mono inf_le_left) f * (res (π.preimage_mono inf_le_right) g)⁻¹

def Chart (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) : Type :=
  {p : (V : Y.Opens) × Γ(X, π ⁻¹ᵁ V)ˣ // E p.1 p.2}


open Classical in
def trans (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) (i j : Chart π E) :
    Γ(Y, i.1.1 ⊓ j.1.1)ˣ :=
  if h : ∃ u, pullU π _ u = rat π i.1.2 j.1.2 then h.choose else 1

section Eigen

variable {K : Type} [Field K] {A A' T : Over (Sp K)} [GrpObj A] [GrpObj A']

end Eigen

end GlobalTheory.EigenDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambda
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerFinite

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    (x y : Y ⟶ A) : evc hP x y = lam (cls L hL) x y := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem add_inv_eq_of_same {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a a' : Y ⟶ A) (t : Y ⟶ T)
    (h₁ : Same A (abelian₂ A L) N a t) (h₂ : Same A (abelian₂ A L) N a' t) :
    CechPic.pull a.left (cls L hL) + CechPic.pull (a⁻¹).left (cls L hL) =
      CechPic.pull a'.left (cls L hL) + CechPic.pull (a'⁻¹).left (cls L hL) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e := ((same_iff hP hN a t).1 h₁).trans ((same_iff hP hN a' t).1 h₂).symm
  rw [evc_lam hL hP, evc_lam hL hP] at e
  have e' := congrArg (CechPic.pull (lift (a⁻¹ * a'⁻¹) (𝟙 Y)).left) e
  simp only [pull_lam, lift_fst, lift_snd_assoc, Category.id_comp] at e'
  simp only [lam] at e'
  rw [show a⁻¹ * a'⁻¹ * a = a'⁻¹ by rw [mul_right_comm, inv_mul_cancel, _root_.one_mul],
    show a⁻¹ * a'⁻¹ * a' = a⁻¹ from inv_mul_cancel_right _ _] at e'
  linear_combination (norm := abel) e'.symm

theorem isFinite_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  intro R _ _ A _ hB L hL hA T _ _ N hN H h hh hH
  haveI := hB.comm
  have := hB.proper
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A L hL).1 hA
  have hAT : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback A.hom T.hom
  have : IsProper (snd A T).left := MorphismProperty.of_isPullback hAT inferInstance
  have : IsAffineHom (fst A T).left := MorphismProperty.of_isPullback hAT.flip inferInstance
  let f : H.left ⟶ T.left := (h ≫ snd A T).left
  have hf : f ≫ T.hom = H.hom := Over.w (h ≫ snd A T)
  have : IsProper f := inferInstanceAs (IsProper (h.left ≫ (snd A T).left))
  change IsFinite f
  suffices LocallyQuasiFinite f from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (f ⁻¹' {z}) with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField x₀
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField x₀
  let g : Spec (CommRingCat.of K) ⟶ T.left := y₀ ≫ f
  let π : pullback f g ⟶ H.left := pullback.fst f g
  let q : pullback f g ⟶ Spec (CommRingCat.of K) := pullback.snd f g
  let Z : Scheme.{0} := pullback f g
  have hpb : IsPullback π q f g := IsPullback.of_hasPullback f g
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  let P : Over (Sp R) := Over.mk (y₀ ≫ H.hom)
  let Q : Over (Sp R) := Over.mk (π ≫ H.hom)
  let yo : P ⟶ H := Over.homMk y₀ rfl
  let qo : Q ⟶ P := Over.homMk q (by
    show q ≫ y₀ ≫ H.hom = π ≫ H.hom
    rw [← hf, ← Category.assoc π, hpb.w]
    simp only [g, Category.assoc])
  let p₁ : Q ⟶ H := Over.homMk π rfl
  have hpt : p₁ ≫ h ≫ snd A T = qo ≫ yo ≫ h ≫ snd A T := by
    ext
    exact hpb.w
  let w : H ⟶ A := h ≫ fst A T
  have hs₁ : Same A (abelian₂ A L) N (p₁ ≫ w) (p₁ ≫ h ≫ snd A T) :=
    (hH _ _ _).2 ⟨p₁, by ext <;> simp [w]⟩
  have hs₂ : Same A (abelian₂ A L) N (qo ≫ yo ≫ w) (p₁ ≫ h ≫ snd A T) := by
    rw [hpt]
    exact (hH _ _ _).2 ⟨qo ≫ yo, by ext <;> simp [w]⟩
  have key := add_inv_eq_of_same hL hN.isLB _ _ _ hs₁ hs₂
  rw [← GrpObj.comp_inv qo, Over.comp_left _ _ _ qo, Over.comp_left _ _ _ qo, pull_comp qo.left,
    pull_comp qo.left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w).left,
    GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w)⁻¹.left, map_zero, add_zero] at key
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (p₁ ≫ w).left := inferInstanceAs (IsAffineHom (π ≫ h.left ≫ (fst A T).left))
  have : Z.IsQuasiAffine := GlobalTheory.AmpleStabFinite.quasiAffine_of_pull_add (p₁ ≫ w).left ((p₁ ≫ w)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [GlobalTheory.AmpleStabFinite.cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add]
      exact (congrArg _ key).trans (zsmul_zero _))
  have : IsAffine Z := GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set Z).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun v hv => ?_
  have e : f v = g (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = x₀ := Scheme.fromSpecResidueField_apply x₀ _
    exact (show f v = z from hv).trans ((show f x₀ = z from hx₀).symm.trans (congrArg f e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.TwistKerFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem fibre_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
    [IsClosedImmersion f] [GeometricallyConnected s] [Surjective (f ≫ s)] {g g' : ℕ}
    (hg' : SmoothOfRelativeDimension g' s) (hg : SmoothOfRelativeDimension g (f ≫ s))
    (hle : g' ≤ g) (K : Type) [Field K] [Algebra R K] :
    IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))) := by
  have H₁ := IsPullback.of_hasPullback f (pullback.fst s (spMap (algebraMap R K)))
  have H₂ := IsPullback.of_hasPullback s (spMap (algebraMap R K))
  have H := H₁.paste_vert H₂
  have h₁ : SmoothOfRelativeDimension g' (pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H₂ hg'
  have h₂ : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback H hg
  have : Surjective (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := MorphismProperty.of_isPullback H ‹_›
  have : Smooth s := hg'.smooth
  have : AlgebraicGeometry.IsIntegral (Limits.pullback s (spMap (algebraMap R K))) := GlobalTheory.isIntegral_of_isPullback_of_smooth H₂
  have : Smooth (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := h₂.smooth
  have : AlgebraicGeometry.IsReduced (Limits.pullback f (pullback.fst s (spMap (algebraMap R K)))) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K)))
  have : Nonempty ↥(Limits.pullback (C := Scheme.{0}) f (pullback.fst s (spMap (algebraMap R K)))) := by
    obtain ⟨z, -⟩ := (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))).surjective (default : PrimeSpectrum K)
    exact ⟨z⟩
  exact GlobalTheory.DivisiblePart.isIso_of_dim_le _ _ h₁ h₂ hle

end GlobalTheory.AbMonoIso

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} [IsLocallyNoetherian S] (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    [Flat (f ≫ p)] {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have : Smooth p := hg'.smooth
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : IsLocallyNoetherian (Limits.pullback p j) := isLocallyNoetherian_of_isOpenImmersion gX
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_isProper s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g g' : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g' B'.hom → g' ≤ g → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S _ B B' _ _ hB hB' g g' hg hg' hle x _ _
  have := hB.proper
  have := hB.smooth
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : Flat (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) hle
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem IsDual.eq_of_evc {S : Scheme.{0}} {A B' T : Over S} [GrpObj A] [GrpObj B'] {P' : LB (A ⊗ B').left}
    (h : IsDual A B' P') {y₁ y₂ : T ⟶ B'}
    (e : evc h.isLB (fst A T) (snd A T ≫ y₁) = evc h.isLB (fst A T) (snd A T ≫ y₂)) : y₁ = y₂ := by
  have hM : (ev P' (fst A T) (snd A T ≫ y₁)).IsLB := pull_isLB h.isLB _
  have ha : IsAdditive (ev P' (fst A T) (snd A T ≫ y₁)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
    rw [evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)
  exact (h.univ T _ hM ha).unique ((cls_eq_iff hM hM).1 rfl)
    ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)

theorem comp_mul_eq {S : Scheme.{0}} {G Y : Over S} [MonObj G] (f : Y ⟶ G ⊗ G) :
    f ≫ μ = (f ≫ fst G G) * (f ≫ snd G G) := by
  show _ = lift _ _ ≫ μ
  rw [lift_comp_fst_snd]

theorem isMonHom_of_classifying : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → IsAdditive (swap P') → P.IsLB →
    IsAdditive (swap P) → ∀ x : B ⟶ B', LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsMonHom x := by
  intro S A B B' _ _ _ P P' h' ha' hP ha x e
  have hP' := h'.isLB
  have hE : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB hP' _
  have c : cls P hP = cls _ hE := (cls_eq_iff hP hE).2 e
  have K : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B), evc hP a b = evc hP' a (b ≫ x) := by
    intro Y a b
    have k := evc_ev hP' (fst A B) (snd A B ≫ x) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, c]
  have hs : (swap P).IsLB := pull_isLB hP _
  have hs' : (swap P').IsLB := pull_isLB hP' _
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 ha Y b b' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at k
  have addR' : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B'),
      evc hP' a (b * b') = evc hP' a b + evc hP' a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs').1 ha' Y b b' a
    rwa [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs'] at k
  have oneR : ∀ (Y : Over S) (a : Y ⟶ A), evc hP a (1 : Y ⟶ B) = 0 := fun Y a ↦ by
    rw [← evc_swap hP hs]; exact ha.evc_one hs a
  have oneR' : ∀ (Y : Over S) (a : Y ⟶ A), evc hP' a (1 : Y ⟶ B') = 0 := fun Y a ↦ by
    rw [← evc_swap hP' hs']; exact ha'.evc_one hs' a
  have u : ∀ (G : Over S) [MonObj G], snd A (𝟙_ (Over S)) ≫ (η : 𝟙_ (Over S) ⟶ G) = 1 := fun G _ ↦ by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over S))) (toUnit _)]
  refine ⟨?_, ?_⟩
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← K, u, u, oneR, oneR']
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← Category.assoc, comp_mul_eq, comp_mul_eq, ← K, addR, K, K, ← addR']
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefPow

theorem height_pow (HE : GlobalTheory.Published.ArExists) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) (L : HermLB p) (n : ℕ)
    {h h' : X → ℝ} (H : L.IsArithHeight h) (H' : (L.pow n).IsArithHeight h') : h' x = n * h x := by
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    PtHtComb.height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  rw [← hht H', ← hht H, ← hF, ← hF, HermLB.icls_pow, map_nsmul, nsmul_eq_mul]

theorem isNef_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  intro HC k _ X _ p D hX M n N
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨h₀, H₀⟩ := hex (HermLB.triv p)
    have H : (M.pow 0).IsArithHeight h₀ := M.isometric_pow_zero.symm.isArithHeight hX H₀
    have T := (H₀.isNef_iff hX).1 (HermLB.isNef_triv p D)
    exact (H.isNef_iff hX).2 ⟨N.semiPos.pow 0, T.2⟩
  · have : Module.Finite ℤ k := hX.finite
    refine ⟨N.semiPos.pow n, (nefFib_pow_iff k X p hX.isProjOver M n hn).2 N.vertical,
      fun Z i _ _ _ hc hd => ?_⟩
    obtain ⟨h, H⟩ := hex M
    obtain ⟨h', H'⟩ := hex (M.pow n)
    obtain ⟨r, hr⟩ := exists_isRatSec ((M.pow n).restr i).isLB
    obtain ⟨r₀, hr₀, h0⟩ := N.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H'.point Z i hc hd r hr, height_pow HE hX (HtSelfInter.isAlgPt_genericPoint i hc hd) M n H H',
      H.point Z i hc hd r₀ hr₀]
    exact mul_nonneg (Nat.cast_nonneg _) h0

end GlobalTheory.NefPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoLiftSmallArtinExtensions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open IsLocalRing

namespace GlobalTheory.ArtinOpen

theorem stalk_hom_ext_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) (R : CommRingCat.{0})
    [IsLocalRing R] (g₁ g₂ : X.presheaf.stalk x ⟶ R) [IsLocalHom g₁.hom] [IsLocalHom g₂.hom]
    (h : f.stalkMap x ≫ g₁ = f.stalkMap x ≫ g₂) : g₁ = g₂ := by
  have e : Spec.map g₁ ≫ X.fromSpecStalk x = Spec.map g₂ ≫ X.fromSpecStalk x := by
    rw [← cancel_mono f, Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, h]
  have e2 := (SpecToEquivOfLocalRing X R).symm.injective (a₁ := ⟨x, g₁, inferInstance⟩)
    (a₂ := ⟨x, g₂, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simpa using e3

theorem isOpenImmersion_of_lift : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f := by
  intro X Y f _ _ _ hlift
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Flat f := by
    refine (Flat.iff_flat_stalkMap f).2 fun x => ?_
    have hres := _root_.GlobalTheory.residueFieldMap_surjective_of_mono f x
    refine GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow (f.stalkMap x).hom (fun n => _root_.GlobalTheory.SmallLift.exists_retraction f hlift x hres n) ?_
    intro n g₁ g₂ h₁ h₂ h
    have := stalk_hom_ext_of_mono f x
      (CommRingCat.of (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ (n + 1)))
      (CommRingCat.ofHom g₁) (CommRingCat.ofHom g₂) (by ext a; exact congr($h a))
    exact congrArg CommRingCat.Hom.hom this
  exact IsOpenImmersion.of_flat_of_mono f

end GlobalTheory.ArtinOpen
end

