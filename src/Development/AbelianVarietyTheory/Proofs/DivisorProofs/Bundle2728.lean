module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0479
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.DegSep

variable {S : Scheme.{0}}

theorem one_left' (T : Over S) (G : Over S) [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  have h := Over.w (toUnit T)
  change (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

theorem comp_pow_id (T G : Over S) [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem isUnit_natCast_Γ (K : Type) [Field K] (n : ℕ) (hn : (n : K) ≠ 0) : IsUnit (n : Γ(Sp K, ⊤)) := by
  have h : IsUnit (n : K) := hn.isUnit
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  simpa using this

theorem deg_eq_card_ker (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ) (hn : (n : K) ≠ 0)
    (hiso : IsIsogeny f) (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) :
    deg f = Nat.card (ptMap f).ker := by
  have hfl : Flat f.hom.left := (_root_.GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  have hprop : IsProper B.X.hom := B.ab.proper
  let e : Sp K ⟶ B.X.left := η[B.X].left
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hecl : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ B.X.hom) := by rw [he1]; infer_instance
    exact IsClosedImmersion.of_comp e B.X.hom
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hifu : FormallyUnramified i := inferInstance

  let T : Over (Sp K) := Over.mk (i ≫ A.X.hom)
  let x : T ⟶ A.X := Over.homMk i
  have hx1 : x ≫ f.hom = 1 := by
    ext1
    rw [Over.comp_left, one_left']
    change i ≫ f.hom.left = (i ≫ A.X.hom) ≫ e
    rw [hpi, pullback.condition]
  have hxn := hker T x hx1
  have hleft : i ≫ (Out.mulA A.X n).left = p ≫ η[A.X].left := by
    have h : (x ^ n).left = (1 : T ⟶ A.X).left := by rw [hxn]
    rw [← comp_pow_id, one_left'] at h
    change i ≫ (Out.mulA A.X n).left = _ at h
    rw [h]
    change (i ≫ A.X.hom) ≫ _ = _
    rw [hpi]
  let j : pullback f.hom.left e ⟶ pullback (Out.mulA A.X n).left η[A.X].left :=
    pullback.lift i p hleft
  have hmu : FormallyUnramified (Out.mulA A.X n).left :=
    GlobalTheory.formallyUnramified_mulA (Sp K) A.X n (isUnit_natCast_Γ K n hn)
  have hsnd : FormallyUnramified (pullback.snd (Out.mulA A.X n).left η[A.X].left) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hmu
  have hjfu : FormallyUnramified j := by
    have : FormallyUnramified (j ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact hifu
    exact FormallyUnramified.of_comp j (pullback.fst _ _)
  have hpfu : FormallyUnramified p := by
    have : j ≫ pullback.snd _ _ = p := pullback.lift_snd _ _ _
    rw [← this]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ hjfu hsnd
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p

  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem deg_eq_card_ker_of_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 →
    IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) →
    deg f = Nat.card (ptMap f).ker :=
  fun K _ A B f n hn hiso hker => deg_eq_card_ker K A B f n hn hiso hker

end GlobalTheory.AV.DegSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

theorem ker_eq_range_of_range_eq_ker {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (_ : Module.Finite K V) (_ : Module.Finite K W) (f : V →ₗ[K] W)
    (g : W →ₗ[K] V) (hd : Module.finrank K V = Module.finrank K W) (h0 : g ∘ₗ f = 0)
    (h1 : LinearMap.range g = LinearMap.ker f) : LinearMap.ker g = LinearMap.range f := by
  have e1 := g.finrank_range_add_finrank_ker
  have e2 := f.finrank_range_add_finrank_ker
  rw [h1] at e1
  exact (Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 h0) (by omega)).symm

theorem rigExt_field_of_charP (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height ∧
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span K (Set.range fun x : G.RigExt => SemiHom.rig (absFrob h G) x) := by
  obtain ⟨-, f1, d1, d2⟩ := _root_.GlobalTheory.PDivGroup.finrank_rigExt_omega p K h G
  obtain ⟨-, f2, d3, -⟩ := _root_.GlobalTheory.PDivGroup.finrank_rigExt_omega p K h (frobTwist h G)
  have h4 := le_antisymm (range_rigExtMap_verschiebung_le h G) (GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' p K h G)
  have h5 := le_antisymm (_root_.GlobalTheory.PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega p K h G)
    (LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G))
  have h6 : rigExtMap (verschiebung h G) ∘ₗ rigExtMap (relFrob h G) = 0 := by
    rw [← rigExtMap_comp, verschiebung_comp_relFrob]
    exact (GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id p K h
      (frobTwist h G) (frobTwist h G)).2
  exact ⟨f1, d1, d2, h4, h5, ker_eq_range_of_range_eq_ker f2 f1 _ _
    (d3.trans ((frobTwist_height h G).trans d1.symm)) h6 (h4.trans h5.symm),
    range_rigExtMap_relFrob h G⟩

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionLocallyCutOutByIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

section Transport

variable {O T V W : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]
  (ψ : O →+* Module.End T V) (ν : O →+* Module.End T W) (e : V ≃ₗ[T] W) (he : ∀ c v, e (ψ c v) = ν c (e v))
include he

theorem mem_eigSub_transport (τ : O →+* T) (v : V) : e v ∈ eigSub ν τ ↔ v ∈ eigSub ψ τ := by
  simp only [mem_eigSub]
  refine forall_congr' fun c => ?_
  rw [← he, ← map_smul, e.injective.eq_iff]

theorem eigSub_transport (τ : O →+* T) : (eigSub ψ τ).map (e : V →ₗ[T] W) = eigSub ν τ := by
  ext w
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, ← mem_eigSub_transport ψ ν e he]
  simp

theorem finrank_eigSub_transport (τ : O →+* T) :
    Module.finrank T (eigSub ψ τ) = Module.finrank T (eigSub ν τ) := by
  rw [← eigSub_transport ψ ν e he τ]
  exact (e.submoduleMap (eigSub ψ τ)).finrank_eq

theorem lieMod_transport (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) :
    LieMod ψ ω ρ τ ↔ LieMod ν ω ρ τ := by
  constructor
  · intro h w hw
    obtain ⟨u, hu, hs⟩ := h (e.symm w) (by
      apply e.injective
      rw [he, map_smul, LinearEquiv.apply_symm_apply, hw])
    refine ⟨fun i => e (u i), fun i => (mem_eigSub_transport ψ ν e he _ _).2 (hu i), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← hs, LinearEquiv.apply_symm_apply]
  · intro h v hv
    obtain ⟨u, hu, hs⟩ := h (e v) (by rw [← he, hv, map_smul])
    refine ⟨fun i => e.symm (u i), fun i => ?_, ?_⟩
    · rw [← mem_eigSub_transport ψ ν e he, LinearEquiv.apply_symm_apply]
      exact hu i
    · apply e.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, hs]
      simp

end Transport

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_baseMap {R : Type} [CommRing R] {S : Scheme.{0}} (s : S ⟶ Sp R) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ βB : R →+* Γ(S, U), ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'),
      spMap f ≫ hU.fromSpec ≫ s = spMap β → β = f.comp βB := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, fun R' _ f β h => ?_⟩
  have h2 : spMap (f.comp (Spec.preimage (hU.fromSpec ≫ s)).hom) = spMap β := by
    rw [← h, ← spMap_comp_spMap']
    congr 1
    show Spec.map (CommRingCat.ofHom (Spec.preimage (hU.fromSpec ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h3 := Spec.map_injective h2
  exact (congrArg CommRingCat.Hom.hom h3).symm

theorem lieHer_iff_mat {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {S : Scheme.{0}}
    {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {U : S.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) Γ(S, U))
    (hM : ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
      ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
        ∀ (c : 𝓞 D.F) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
          e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') (act.toF D) c v) = matAct M f c (e v))
    {R' : Type} [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R') :
    LieHer b act β (spMap f ≫ hU.fromSpec) ↔ LieHerMat b M f β := by
  unfold LieHer LieHerMat LieRankAt
  refine forall_congr' fun T' => forall_congr' fun _ => forall_congr' fun g => ?_
  have hx : spMap g ≫ spMap f ≫ hU.fromSpec = spMap (g.comp f) ≫ hU.fromSpec := by
    rw [← Category.assoc, spMap_comp_spMap']
  rw [hx]
  obtain ⟨e, he⟩ := hM T' (g.comp f)
  refine and_congr ?_ ?_
  · rw [GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition]
    exact lieMod_transport _ _ e he _ _ _
  · refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h =>
      forall_congr' fun i => ?_
    have hx2 : spMap h ≫ spMap (g.comp f) ≫ hU.fromSpec = spMap (h.comp (g.comp f)) ≫ hU.fromSpec := by
      rw [← Category.assoc, spMap_comp_spMap']
    rw [hx2]
    obtain ⟨e2, he2⟩ := hM k (h.comp (g.comp f))
    haveI : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap (h.comp (g.comp f)) ≫ hU.fromSpec) A) :=
      Module.Finite.equiv e2.symm
    rw [GlobalTheory.T.lieMult_iff_finrank_simultaneousEigenSubmodule _ _ _ _ _ _ _ _ inferInstance, finrank_eigSub_transport _ _ e2 he2]

theorem lieHerMat_iff_le {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {B : Type}
    [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K₂ : Ideal B)
    (hK₂ : ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f))
    {T : Type} [CommRing T] (f : B →+* T) :
    LieHerMat b M f (f.comp βB) ↔ lieIdeal b βB M ⊔ K₂ ≤ RingHom.ker f := by
  constructor
  · intro h
    obtain ⟨hL, hR⟩ := h T (RingHom.id T)
    have hJ : lieIdeal b βB M ≤ RingHom.ker f := (_root_.GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker _ _ _ b _ βB n M T f).1 hL
    exact sup_le hJ ((hK₂ T f hJ).1 hR)
  · intro hK T' _ g
    have hker : RingHom.ker f ≤ RingHom.ker (g.comp f) := fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, hx, map_zero]
    have hJ : lieIdeal b βB M ≤ RingHom.ker (g.comp f) := le_sup_left.trans (hK.trans hker)
    have h2 : K₂ ≤ RingHom.ker (g.comp f) := le_sup_right.trans (hK.trans hker)
    exact ⟨(_root_.GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker _ _ _ b _ βB n M T' (g.comp f)).2 hJ, (hK₂ T' (g.comp f) hJ).2 h2⟩

theorem lieHer_ideal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : OActN D.O A) (z : S),
  ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'), spMap f ≫ hU.fromSpec ≫ s = spMap β →
      (LieHer b act β (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) := by
  intro p _ D R _ b S s A _ _ hA act z
  obtain ⟨U, hU, hz, n, M, hM⟩ := GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group (𝓞 D.F) S A hA (act.toF D) z
  obtain ⟨βB, hβB⟩ := exists_baseMap s hU
  obtain ⟨K₂, hK₂⟩ := GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition p D R b Γ(S, U) βB n M
  refine ⟨U, hU, hz, lieIdeal b βB M ⊔ K₂, fun R' _ f β hc => ?_⟩
  obtain rfl := hβB R' f β hc
  rw [lieHer_iff_mat b act hU M hM f]
  exact lieHerMat_iff_le b βB M K₂ hK₂ f

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem psiQ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ), (∀ χ, u.PsiNorm χ (Real.exp (-q χ))) → ∀ χ, l.q χ = q χ := by
  intro o Ω _ _ _ S ρ p _ y₀ u l q hq χ
  have := GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ)
  exact neg_injective (Real.exp_injective this)

theorem labels_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy ∧ D.Compat yy₁ yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c yy₁ hLab y h
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hS, hi, hR, y₀, hy₀, u, l, j, hq, hyy, hmat⟩ := hLab
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, hint₂⟩ :=
    _root_.GlobalTheory.Poinc.GLiftRechart.main g n F W Z i D.X hg hn hodd himm he8 hth D.proj D.ε D.diag p (y (cPt p)) (D.lift c y h)
  obtain ⟨u₂, e, T, hpsi, htor, heps, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨l₂⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  set L₂ : ℕ := D.X.S.r * D.X.S.N with hL₂
  set L₁ : ℕ := X₁.S.r * X₁.S.N with hL₁
  let jj : u₂.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X) := e.trans j
  have hrange : (nsmulAddMonoidHom L₂ : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      ((nsmulAddMonoidHom L₂ : (Fin 8 → c.T.D.toPre.X) →+ (Fin 8 → c.T.D.toPre.X)).range).comap jj.toAddMonoidHom := by
    rintro _ ⟨z, rfl⟩
    exact ⟨jj z, by simp⟩
  let f := QuotientAddGroup.map _ _ jj.toAddMonoidHom hrange
  have hf : ∀ χ, f (QuotientAddGroup.mk χ) = QuotientAddGroup.mk (jj χ) := fun χ => rfl
  refine ⟨f.comp l₂.yy, ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, u₂, l₂, jj, ?_, ?_, ?_⟩, ?_⟩
  · intro χ
    rw [GlobalTheory.Poinc.GLift.psiQ _ _ _ ρ₂ p y₂ u₂ l₂ (fun χ => l.q (e χ)) (fun χ => hpsi χ _ (l.q_eq (e χ))) χ]
    exact hq (e χ)
  · intro a χ ha
    simp only [AddMonoidHom.comp_apply, ha]
    rfl
  · intro m pk pk' x x' E hm hx hx' hxx
    obtain ⟨q₁, hq₁y, hq₁⟩ := hfw m pk x hm hx
    obtain ⟨q₁', hq₁y', hq₁'⟩ := hfw m pk' x' hm hx'
    have := hmat m q₁ q₁' (T x) (T x') E hm hq₁ hq₁' (heps x x' E hxx)
    rw [hq₁y, hq₁y'] at this
    exact this
  · intro a μ hμ
    obtain ⟨pk, x, hx, hxa⟩ := GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model _ _ _ ρ' p y₀ u a
    have h1 := l.yy_eq a pk x hx hxa
    have h2 := hyy a pk.y h1
    have hL₁pos : 1 ≤ L₁ := by
      obtain ⟨jr, hjr, hr⟩ := X₁.ρ.r_eq
      have h1' : 0 < X₁.S.r := by rw [hr]; exact pow_pos X₁.ρ.n_prime.pos _
      have h2' : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdvd : L₁ ∣ L₂ := by
      obtain ⟨t, ht⟩ := D.dvd
      refine ⟨t * (D.m * D.X.S.r), ?_⟩
      rw [hL₂, D.sq, ht]; ring
    have hL₂pos : 1 ≤ L₂ := by
      obtain ⟨jr, hjr, hr⟩ := D.X.ρ.r_eq
      have h1' : 0 < D.X.S.r := by rw [hr]; exact pow_pos D.X.ρ.n_prime.pos _
      have h2' : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdpos : 1 ≤ L₂ / L₁ := by
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint _ _ _ ρ' p y₀ u L₁ L₂ (L₂ / L₁) pk x hL₁pos hdpos
      (Nat.div_mul_cancel hdvd).symm hx
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw L₂ pk' x hL₂pos hpk'
    have h3 := (htor (T.symm x) a).2 (by simpa using hxa)
    have h4 := l₂.yy_eq (D.lab a) pk₂ (T.symm x) hpk₂ h3
    show f (l₂.yy (D.lab a)) = _
    rw [h4, hf]
    have h5 : jj pk₂.y = (L₂ / L₁) • j pk.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h5]
    rw [hμ] at h2
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq).1 h2.symm
    apply (QuotientAddGroup.eq).2
    refine ⟨z, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← smul_neg, ← smul_add, ← hz, smul_smul, Nat.div_mul_cancel hdvd]

end GlobalTheory.Poinc.GLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p → ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  first | (exact @GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat) | (exact GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat) | (intros; apply GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingIntegral
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pairing_integral : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (v w : AfP p ⊗[ℚ] VQ D), v ∈ LaHat D → w ∈ LaHat D → IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) v w) := by
  first | (exact @GlobalTheory.LKGeo.formInt_laHat) | (exact GlobalTheory.LKGeo.formInt_laHat) | (intros; apply GlobalTheory.LKGeo.formInt_laHat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingAdjointInvolution
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_adjoint_involution : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  first | (exact @GlobalTheory.LKGeo.adj_actOn_afP) | (exact GlobalTheory.LKGeo.adj_actOn_afP) | (intros; apply GlobalTheory.LKGeo.adj_actOn_afP  <;> assumption)
end

