module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpFamilyMatrixRelationsDense
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
section
noncomputable section

namespace GlobalTheory.CoveringCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Fibres

def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)

theorem splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩

theorem exists_finite_splitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩

end Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end One

end GlobalTheory.CoveringCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondOfEigenbasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodPoint

variable {E : Type} [Field E] [NumberField E]

theorem exists_embedding {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (τ : 𝓞 E →+* k) :
    ∃ τ₀ : E →+* ℂ, β.comp (τ₀.comp (algebraMap (𝓞 E) E)) = τ := by
  have : CharZero k := charZero_of_injective_ringHom β.injective
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hb : Function.Bijective fun φ : E →+* ℂ => β.comp φ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨fun φ ψ h => RingHom.ext fun a => β.injective (DFunLike.congr_fun h a),
      by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  obtain ⟨τ₀, h⟩ := hb.2 (IsFractionRing.lift hτ)
  refine ⟨τ₀, RingHom.ext fun a => ?_⟩
  exact (DFunLike.congr_fun h _).trans (IsFractionRing.lift_algebraMap hτ a)

variable [IsCMField E] {H : Host E}

theorem detCond_of_eigenbasis
    (lie : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}))
    (D : Datum H) (t : SAB H (Sp ℂ)) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty)
    (v : Fin g → (epsR ℂ ⟶ t.G)) (hv : IsLieBasis v)
    (heig : ∀ i (a : 𝓞 E), (v i ≫ t.act.act a).left = spMap (epsScale (ty i (a : E))) ≫ (v i).left)
    {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) : DetCond D t.act (spMap β) (β H.rt0) := by
  obtain ⟨t', m⟩ : ∃ t' : SAB H (Sp k), Nonempty (SABMap t' t (spMap β)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap β) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨v', hv', hφ⟩ := exists_isLieBasis_baseChange ℂ k β t.G t'.G m.cm.F m.cart t.semi.smooth g v hv
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have dm : ∀ c : ℂ, spMap (Chart.dualMapR β) ≫ spMap (epsScale c) =
      spMap (epsScale (β c)) ≫ spMap (Chart.dualMapR β) := fun c => by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_comp _ _))
    ext a <;> simp [epsScale, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have key : ∀ τ₀ : E →+* ℂ, LieMult t.act (spMap β) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := lie k (𝓞 E) t'.G t'.act g v' (fun i => β.comp ((ty i).comp (algebraMap (𝓞 E) E))) t'.semi.smooth hv'
      (fun i a => m.cart.1.hom_ext ?_ ?_) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
    · rw [LiePull.lieMult_pull _ _ _ t.G t'.G _ _ t.act t'.act m.cart m.act, Category.id_comp] at h
      convert h using 1
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun e => by rw [e], fun e => ?_⟩)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun a => β.injective (DFunLike.congr_fun e a))
    · have e := heig i a
      rw [Over.comp_left] at e
      rw [Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc, e, Category.assoc, hφ,
        ← Category.assoc, dm, Category.assoc]
    · rw [Over.w, Category.assoc, Over.w]
      exact (sc _).symm
  intro τ
  obtain ⟨τ₀, rfl⟩ := exists_embedding β τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (hty τ₀).1 (β.injective h)]; exact key τ₀
  · rw [← (hty τ₀).2 fun e => h (congrArg β e)]; exact key τ₀

theorem exists_fibre_unif {S : Scheme.{0}} (t : SAB H (Sp ℂ)) (t₀ : SAB H S) (y : Sp ℂ ⟶ S) (m : SABMap t t₀ y)
    {L : LB t.G.left} {g : ℕ} (u : HolUnif t.G L g) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ e : (Fin g → ℂ) → (Over.mk y ⟶ t₀.G), (∀ z, (e z).left = (u.ex z).left ≫ m.cm.F) ∧
      ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
        (∀ w, ∃! v : epsPt y ⟶ t₀.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
        (∀ v : epsPt y ⟶ t₀.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
          ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧
      (∀ z, e z = 1 ↔ u.ex z = 1) ∧
      (∀ a z w, u.ex w = u.ex z ≫ t.act.act a → e w = e z ≫ t₀.act.act a) ∧
      ∀ (k : ℤ) z w c, Out.WeilIs t.G t.PP.L k (u.ex z) (u.ex w) c → Out.WeilIs t₀.G t₀.PP.L k (e z) (e w) c := by
  obtain ⟨φ, hφ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) y (Category.id_comp y).symm
  obtain ⟨ψ, hψ⟩ := LiePull.exists_pushEquiv m.cart (epsR ℂ) (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) rfl
  have hee : (fun z => (φ (u.ex z)).left) = fun z => (u.ex z).left ≫ m.cm.F := funext fun z => hφ _
  have hol : IsHolTo Set.univ (fun z => (u.ex z).left ≫ m.cm.F) := fun U f => by
    obtain ⟨a, b⟩ := u.hol (m.cm.F ⁻¹ᵁ U) ((m.cm.F.app U).hom f)
    simp only [← valAt'_comp, Set.mem_univ, true_and]
    exact ⟨a, b⟩
  have key : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ t.G), IsTangent v ∧ u.IsDiff w v ↔
      IsDerivAt0 (fun z => (φ (u.ex z)).left) w (ψ v).left := fun w v => by
    have e₀ : IsTangent v ∧ u.IsDiff w v ↔ IsDerivAt0 (fun z => (u.ex z).left) w v.left :=
      and_congr (by rw [IsTangent, ← TangentOrigin.ex_zero_left u]) Iff.rfl
    rw [e₀, hee, hψ]
    exact ⟨fun h => FibreDeriv.isDerivAt0_comp h _,
      fun h => FibreDeriv.isDerivAt0_of_isPullback m.cart.1 (fun z => Over.w (u.ex z)) hol (Over.w v) h⟩
  refine ⟨fun z => φ (u.ex z), fun z => hφ _, ⟨fun z w => by simp only [u.ex_add, map_mul],
    φ.surjective.comp u.ex_onto, by rw [hee]; exact hol, fun w => ?_, fun v hv => ?_⟩,
    fun z => φ.map_eq_one_iff, fun a z w h => Over.OverMorphism.ext ?_, fun k z w c h => ?_⟩
  · obtain ⟨v, hv, huniq⟩ := h₂ w
    refine ⟨ψ v, (key w v).1 hv, fun v' hv' => ?_⟩
    obtain ⟨v', rfl⟩ := ψ.surjective v'
    rw [huniq v' ((key w v').2 hv')]
  · obtain ⟨v, rfl⟩ := ψ.surjective v
    have ht : IsTangent v := by
      rw [IsTangent, ← TangentOrigin.ex_zero_left u]
      refine m.cart.1.hom_ext (by rw [Category.assoc, ← hψ, hv, hφ]) ?_
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans (Eq.trans ?_ (Over.w (u.ex 0)).symm))
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      ext a
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [← key, ht, true_and]
    exact h₁ v ht
  · rw [Over.comp_left, hφ, hφ, h, Over.comp_left, Category.assoc, m.act, Category.assoc]
  · obtain ⟨ω, hω, -⟩ := m.lin
    have H := fun (y' : Sp ℂ ⟶ S) (hy' : y' = (𝟙_ (Over (Sp ℂ))).hom ≫ y) (x₀ y₀ : Over.mk y' ⟶ t₀.G)
        (hx : x₀.left = (u.ex z).left ≫ m.cm.F) (hy : y₀.left = (u.ex w).left ≫ m.cm.F) =>
      show Out.WeilIs t₀.G t₀.PP.L k x₀ y₀ c by
        subst hy'
        exact (weilIs_grpPullback_of_comm' _ _ t₀.G t.G y _ _ _ t₀.PP.isLB t.PP.isLB m.cart ⟨ω, hω⟩ _ k _ _ x₀ y₀ c
          hx hy).1 h
    exact H y (Category.id_comp y).symm _ _ (hφ _) (hφ _)

theorem exists_halfLevel {D : Datum H} (l : Level H) {Q : Type} [Group Q] (ev : D.La → Q)
    (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ b, ev (l.M • b) = 1) :
    ∃ κ : D.La → Q, (∀ a b, κ (a + b) = κ a * κ b) ∧ (∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), κ a = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), κ a = ev a := by
  obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hM : ∀ a ∈ (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La), ev a = 1 := fun a ha => by
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, -, rfl⟩ := ha
    rw [Nat.cast_smul_eq_nsmul, hker]
  refine ⟨fun a => ev (u • a), fun a b => by simp only [smul_add, hadd], fun a ha => hM _ ?_, fun a ha => ?_⟩
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu ha
  · have h : ev (v • a) = 1 := hM _ (by rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hv ha)
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, hadd, h, _root_.one_mul]

end GlobalTheory.PeriodPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpFamilyMatrixRelationsDenseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_fromSet_sharpClass : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧ (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧ ∀ j i, t.pt i ≫ t.act j = (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  first | exact @GlobalTheory.sharp_family_relations | exact GlobalTheory.sharp_family_relations | (intros; apply GlobalTheory.sharp_family_relations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticKodairaSpencerClass
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Exist

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

theorem ptDer_add {X : Scheme.{0}} {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f + δ' W f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W hW, h'.add W hW]
    ring
  · intro W hW f f'
    rw [h.mul W hW, h'.mul W hW]
    ring
  · intro W W' e hW f
    rw [h.res W W' e hW, h'.res W W' e hW]

theorem locDer_sub {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}
    {W₀ W₁ : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D W₀ d)
    (h' : LocDer q p m D W₁ d') : LocDer q p m (fun _ => 0) (W₀ ⊓ W₁) (fun W f => d W f - d' W f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]
    ring
  · intro W hW f f'
    rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]
    ring
  · intro W W' e hW f
    rw [h.res W W' e (hW.trans inf_le_left), h'.res W W' e (hW.trans inf_le_right), map_sub]
  · intro W hW r
    rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self, const_zero]

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
  (m : A₀.left ⟶ X)

theorem ex_hom (z : Fin g → ℂ) : (u.ex z).left ≫ A₀.hom = 𝟙 _ := Over.w (u.ex z)

theorem ex_per (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem dom_open (W : X.Opens) : IsOpen (dom u m W) := (u.hol (m ⁻¹ᵁ W) 0).1

theorem dom_inf {W W' : X.Opens} {z : Fin g → ℂ} : z ∈ dom u m (W ⊓ W') ↔ z ∈ dom u m W ∧ z ∈ dom u m W' :=
  top_le_preimage_inf _ _ _

theorem dom_per (l : u.Λ) (W : X.Opens) (z : Fin g → ℂ) : z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  simp only [dom, Set.mem_ofPred_eq, ex_per]

theorem val_hol (W : X.Opens) (c : Γ(A₀.left, m ⁻¹ᵁ W)) :
    DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) c) (dom u m W) := (u.hol (m ⁻¹ᵁ W) c).2

theorem fn_hol (W : X.Opens) (f : Γ(X, W)) : DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) :=
    funext fun z => (valAt'_comp _ _ _ _).symm
  rw [this]
  exact val_hol u m W _

theorem fn_diffAt {W : X.Opens} (f : Γ(X, W)) {z : Fin g → ℂ} (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W f) z :=
  (fn_hol u m W f).differentiableAt ((dom_open u m W).mem_nhds hz)

theorem fderiv_res {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(dom_open u m W').mem_nhds hz] with y hy
  exact valAt'_res _ h f hy

theorem fderiv_per (l : u.Λ) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext x
  simp only [fn, ex_per]

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer ((u.ex z).left ≫ m) (fun W f => fderiv ℂ (fn u m W f) z w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW f f'
    have : fn u m W (f + f') = fn u m W f + fn u m W f' := funext fun y => valAt'_add _ _ _ _
    rw [this, fderiv_add (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  · intro W hW f f'
    have : fn u m W (f * f') = fn u m W f * fn u m W f' := funext fun y => valAt'_mul _ _ _ _
    rw [this, fderiv_mul (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  · intro W W' h hW f
    rw [fderiv_res u m h f hW]

theorem fderiv_const_eq {R : Type} [CommRing R] {x₀ : R →+* ℂ} {p : X ⟶ Sp R} (hm : m ≫ p = A₀.hom ≫ spMap x₀)
    (r : R) (z w : Fin g → ℂ) : fderiv ℂ (fn u m ⊤ (constFn p ⊤ r)) z w = 0 := by
  have : fn u m ⊤ (constFn p ⊤ r) =
      fun _ => valAt' (spMap x₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    funext y
    refine (valAt'_appLE _ p ⊤ ⊤ le_top _ le_top).trans ?_
    rw [Category.assoc, hm, ← Category.assoc, ex_hom]
    exact congrArg (fun x => valAt' x ⊤ _) (Category.id_comp _)
  rw [this]
  simp

def ev (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (z : Fin g → ℂ) (W : X.Opens)
    (f : Γ(X, W)) : ℂ :=
  valAt' (u.ex z).left (m ⁻¹ᵁ (W ⊓ W₀)) (d (W ⊓ W₀) (resG X inf_le_left f))

variable {R : Type} [CommRing R] {p : X ⟶ Sp R} {D : R → ℂ} {W₀ : X.Opens}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)}

theorem ev_eq (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} {W W' : X.Opens} (h : W' ≤ W) (h₀ : W' ≤ W₀)
    (hz : z ∈ dom u m W') (f : Γ(X, W)) :
    ev u m W₀ d z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W') (d W' (resG X h f)) := by
  rw [ev, ← res_res (inf_le_left : W ⊓ W₀ ≤ W) (le_inf h h₀), hd.res _ _ _ inf_le_right]
  exact (valAt'_res (u.ex z).left (V := m ⁻¹ᵁ W') _ _ hz).symm

theorem ptDer_ev (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) :
    PtDer ((u.ex z).left ≫ m) (ev u m W₀ d z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW f f'
    simp only [ev, map_add (f := _), hd.add _ inf_le_right, valAt'_add]
  · intro W hW f f'
    have h : z ∈ dom u m (W ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    simp only [ev, map_mul, hd.mul _ inf_le_right, valAt'_add, valAt'_mul, valAt'_comp]
    rw [valAt'_res _ _ f h, valAt'_res _ _ f' h]
  · intro W W' e hW f
    have h : z ∈ dom u m (W' ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    rw [ev_eq u m hd (inf_le_left.trans e) inf_le_right h f, ev, res_res]

theorem ev_base (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) (r : R) :
    ev u m W₀ d z ⊤ (constFn p ⊤ r) = D r := by
  rw [ev_eq u m hd le_top le_rfl hz, res_const, hd.base _ le_rfl]
  exact valAt'_constFn _ _ (ex_hom u z) _ _ hz

theorem ev_hol (W : X.Opens) (f : Γ(X, W)) :
    DifferentiableOn ℂ (fun z => ev u m W₀ d z W f) (dom u m (W ⊓ W₀)) := val_hol u m _ _

theorem ev_per (l : u.Λ) (z : Fin g → ℂ) : ev u m W₀ d (z + l) = ev u m W₀ d z := by
  funext W f
  simp only [ev, ex_per]

theorem fderiv_field_hol (W : X.Opens) (f : Γ(X, W)) {S : Set (Fin g → ℂ)} (hS : S ⊆ dom u m W)
    (h : Fin g → (Fin g → ℂ) → ℂ) (hh : ∀ a, DifferentiableOn ℂ (h a) S) :
    DifferentiableOn ℂ (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) S := by
  have e : (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) =
      fun z => ∑ a, h a z * fderiv ℂ (fn u m W f) z (Pi.single a 1) := by
    funext z
    conv_lhs => rw [show (fun a => h a z) = ∑ a, h a z • (Pi.single a 1 : Fin g → ℂ) from
      (pi_eq_sum_univ' _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
  rw [e]
  refine DifferentiableOn.fun_sum fun a _ => (hh a).mul ?_
  exact (((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (dom_open u m W)).2 (fn_hol u m W f)).2 _).mono hS

theorem exists_affine_dom (z : Fin g → ℂ) : ∃ i : X.affineOpens, z ∈ dom u m i.1 := by
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨⟨W, hW⟩, (top_le_preimage_iff_mem _ _).2 hx⟩

theorem exists_ksRel : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  intro P₀ u Hm χ hu R _ x₀ X p m hp hm D hD
  choose d hd using fun i : X.affineOpens => _root_.GlobalTheory.KS.exists_locDer_of_smooth R x₀ _ X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose c hc using fun i j : X.affineOpens =>
    GlobalTheory.KS.locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hd i) (hd j))
  let C : X.affineOpens → X.affineOpens → (Fin P₀.g → ℂ) → Fin P₀.g → ℂ :=
    fun i j z a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (c i j a)
  have hC : ∀ i j z W f, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m W →
      ev u m i.1 (d i) z W f - ev u m j.1 (d j) z W f = fderiv ℂ (fn u m W f) z (C i j z) := by
    intro i j z W f hi hj hW
    have h : z ∈ dom u m (W ⊓ (i.1 ⊓ j.1)) := (dom_inf u m).2 ⟨hW, (dom_inf u m).2 ⟨hi, hj⟩⟩
    rw [ev_eq u m (hd i) inf_le_left (inf_le_right.trans inf_le_left) h,
      ev_eq u m (hd j) inf_le_left (inf_le_right.trans inf_le_right) h, ← valAt'_sub,
      hc i j _ inf_le_right _ z h, fderiv_res u m _ _ h]
  have hco : ∀ i j k z, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m k.1 → C i j z + C j k z = C i k z := by
    intro i j k z hi hj hk
    refine (_root_.GlobalTheory.KS.VertFamily.existsUnique_vector P₀ u Hm χ hu R x₀ X p m hp hm z _ (ptDer_fderiv u m z (C i k z))
      (fun r => fderiv_const_eq u m hm.w r z _)).unique (fun W f hW => ?_) (fun _ _ _ => rfl)
    rw [map_add (f := _), ← hC i j z W f hi hj hW, ← hC j k z W f hj hk hW, ← hC i k z W f hi hk hW]
    ring
  choose t h hh hch using fun a : Fin P₀.g =>
    GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full X.affineOpens (fun i => dom u m i.1)
      (fun i j z => C i j z a) (fun i => dom_open u m _) (fun i l z hz => (dom_per u m l _ z).2 hz)
      (exists_affine_dom u m)
      (fun i j => (val_hol u m _ (c i j a)).mono fun z hz => (dom_inf u m).2 hz)
      (fun i j l z _ => by simp only [C, ex_per])
      (fun i j k z hz => congrFun (hco i j k z hz.1.1 hz.1.2 hz.2) a)
  choose κ hκ using exists_affine_dom u m
  let s : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ := fun z W f =>
    ev u m (κ z).1 (d (κ z)) z W f + fderiv ℂ (fn u m W f) z (fun a => h a (κ z) z)
  have hs : ∀ j z W f, z ∈ dom u m j.1 → z ∈ dom u m W →
      s z W f = ev u m j.1 (d j) z W f + fderiv ℂ (fn u m W f) z (fun a => h a j z) := by
    intro j z W f hj hW
    have e₁ := hC (κ z) j z W f (hκ z) hj hW
    have e₂ : C (κ z) j z = (fun a => h a j z) - fun a => h a (κ z) z :=
      funext fun a => hch a (κ z) j z ⟨hκ z, hj⟩
    rw [e₂, map_sub] at e₁
    simp only [s]
    linear_combination e₁
  refine ⟨Matrix.of t, s, fun z => ptDer_add (ptDer_ev u m (hd _) (hκ z)) (ptDer_fderiv u m z _), fun z r => ?_,
    fun W f z hz => ?_, fun l W f z hz => ?_⟩
  · simp only [s]
    rw [ev_base u m (hd _) (hκ z), fderiv_const_eq u m hm.w, add_zero]
  · have hz' : z ∈ dom u m (W ⊓ (κ z).1) := (dom_inf u m).2 ⟨hz, hκ z⟩
    have hn := (dom_open u m _).mem_nhds hz'
    have h₁ := (ev_hol u m (W₀ := (κ z).1) (d := d (κ z)) W f).add
      (fderiv_field_hol u m W f (S := dom u m (W ⊓ (κ z).1)) (fun y hy => ((dom_inf u m).1 hy).1)
        (fun a => h a (κ z)) fun a => (hh a (κ z)).1.mono fun y hy => ((dom_inf u m).1 hy).2)
    refine ((h₁.congr fun y hy => ?_).differentiableAt hn).differentiableWithinAt
    exact hs (κ z) y W f ((dom_inf u m).1 hy).2 ((dom_inf u m).1 hy).1
  · rw [hs (κ z) (z + l) W f ((dom_per u m l _ z).2 (hκ z)) ((dom_per u m l _ z).2 hz), ev_per, fderiv_per]
    have e : (fun a => h a (κ z) (z + l)) = (fun a => h a (κ z) z) + (Matrix.of t).mulVec (star (l : Fin P₀.g → ℂ)) :=
      funext fun a => (hh a (κ z)).2 l z (hκ z)
    rw [e, map_add (f := _)]
    simp only [s]
    ring

end GlobalTheory.KS.Exist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scheme_map_of_projective_coordinates : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  first | exact @GlobalTheory.ZM.RepMap.exists_map_of_coord | exact GlobalTheory.ZM.RepMap.exists_map_of_coord | (intros; apply GlobalTheory.ZM.RepMap.exists_map_of_coord <;> assumption)
end

