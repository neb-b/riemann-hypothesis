module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslates
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOrigin
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameImm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section Group

variable {g : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}

theorem deriv_one (h0 : e 0 = (1 : Over.mk y ⟶ G).left) : IsDerivAt0 e 0 (1 : epsPt y ⟶ G).left := by
  let φ : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have h1 : (1 : epsPt y ⟶ G).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 := by
    rw [h0, ← MonObj.comp_one φ]
    rfl
  have h2 : spMap GlobalTheory.TangentOrigin.fstC ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    rw [← Category.assoc, GlobalTheory.FrameTangent.spMap_comp']
    have : GlobalTheory.TangentOrigin.fstC.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
      RingHom.ext fun r => by simp
    rw [this]
    simp [spMap]
  rw [h1, GlobalTheory.PointUnif.isDerivAt0_iff]
  refine ⟨h2, fun U hU f => ?_⟩
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h2 ▸ (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp _ _ U hU0 hU, map_zero]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem deriv_list (h0 : e 0 = (1 : Over.mk y ⟶ G).left) :
    ∀ (m : ℕ) (w : Fin m → Fin g → ℂ) (v : Fin m → (epsPt y ⟶ G)), (∀ i, IsDerivAt0 e (w i) (v i).left) →
      IsDerivAt0 e (∑ i, w i) (List.ofFn v).prod.left
  | 0, w, v, _ => by simpa using deriv_one h0
  | m + 1, w, v, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact GlobalTheory.PointUnif.deriv_mul h0 (h 0) (deriv_list h0 m _ _ fun i => h i.succ)

end Group

theorem anPt_imm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  classical
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ w hw
  by_contra hcon
  push Not at hcon
  apply hw
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have h0 : (fun z => (Φ.e z).left) 0 = (1 : Over.mk y.x ⟶ Xo.univ.t.G).left := congrArg (·.left) he0
  have d0 := deriv_one (e := fun z => (Φ.e z).left) h0
  have dw : IsDerivAt0 (fun z => (Φ.e z).left) w (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    refine ⟨d0.1, fun U hU f => (d0.2 U hU f).trans ?_⟩
    rw [map_zero]
    refine (hcon U f ?_).symm
    have h3 := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
    exact (congrArg (fun p : Sp ℂ ⟶ Xo.univ.t.G.left => ⊤ ≤ p ⁻¹ᵁ U) d0.1).mp h3
  let q := (Fintype.equivFin (Lt1 Dw)).symm
  have key : ∀ w' : Fin g → ℂ, IsDerivAt0 (fun z => (Φ.e z).left) w' (1 : epsPt y.x ⟶ Xo.univ.t.G).left →
      IsCombAt y.x (m := Fintype.card (Lt1 Dw)) (fun i => y.u (q i).1 (q i).2) (fun i => w' (el.symm (q i)))
        (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    intro w' hw'
    let v : Fin (Fintype.card (Lt1 Dw)) → (epsPt y.x ⟶ Xo.univ.t.G) := fun i =>
      GlobalTheory.FrameTangent.smT y.x (w' (el.symm (q i)))
        (GlobalTheory.FrameTangent.ovT (t := Xo.univ.t) (y.tan (q i).1 (q i).2))
    refine ⟨v, fun i => rfl, GlobalTheory.PointUnif.deriv_unique ?_ hw'⟩
    have hs : w' = ∑ i, w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ) := by
      exact (pi_eq_sum_univ' w').trans
        (Equiv.sum_comp (q.trans el.symm) (fun j => w' j • (Pi.single j 1 : Fin g → ℂ))).symm
    have := deriv_list (e := fun z => (Φ.e z).left) h0 _
      (fun i => w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ)) v
      fun i => GlobalTheory.PointUnif.deriv_smul (Φ.der (q i)) _
    rwa [← hs] at this
  have ht : IsTanAt y.x (1 : epsPt y.x ⟶ Xo.univ.t.G).left := ⟨Over.w _, d0.1.trans h0⟩
  have hu := (GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c ℂ y _ ht).unique
    (y₁ := fun ℓ => w (el.symm ℓ)) (y₂ := fun ℓ => (0 : Fin g → ℂ) (el.symm ℓ)) (key w dw) (key 0 d0)
  funext j
  simpa using congrFun hu (el j)

end GlobalTheory.FrameImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatRoots
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FlatRoots

theorem exists_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (t : Sp S ⟶ Y) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Sp B ⟶ X),
      φ.FaithfullyFlat ∧ w ≫ f = spMap φ ≫ t := by
  haveI : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let e := (pullback t f).isoSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (e.inv ≫ pullback.fst t f)
  have hff : ψ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hψ]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨Γ(pullback t f, ⊤), inferInstance, ψ.hom, e.inv ≫ pullback.snd t f, hff, ?_⟩
  change _ = Spec.map ψ ≫ t
  rw [hψ, Category.assoc, Category.assoc, pullback.condition]

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (J : Type) (t : J → (Sp S ⟶ Y)) (s : Finset J) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B), φ.FaithfullyFlat ∧
      ∀ i ∈ s, ∃ w : Sp B ⟶ X, w ≫ f = spMap φ ≫ t i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, inferInstance, RingHom.id S, RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s _ ih =>
    obtain ⟨B, _, φ, hφ, h⟩ := ih
    obtain ⟨C, _, ψ, w, hψ, hw⟩ := exists_lift f B (spMap φ ≫ t j)
    refine ⟨C, inferInstance, ψ.comp φ, RingHom.FaithfullyFlat.stableUnderComposition φ ψ hφ hψ, fun i hi => ?_⟩
    rw [spMap_comp, Category.assoc]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨w, hw⟩
    · obtain ⟨v, hv⟩ := h i hi
      exact ⟨spMap ψ ≫ v, by rw [Category.assoc, hv]⟩

end FlatRoots

theorem exists_faithfullyFlat_roots :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (N k : ℕ), 0 < N → 0 < k → ∀ (J : Type) [Fintype J] (t : J → (ptO Xo x0 ⟶ Xo.univ.t.G)), (∀ i, t i ^ k = 1) → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ ∀ i, (w i ^ N).left = spMap φ ≫ (t i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 N k hN _ J _ t _
  haveI := UnivPol.isLocallyNoetherian Xo
  obtain ⟨h1, h2, h3, -⟩ := hL.mulN _ (UnivPol.pol Xo) N hN
  let m : Xo.univ.t.G ⟶ Xo.univ.t.G := (𝟙 Xo.univ.t.G) ^ N
  haveI : IsFinite m.left := h1
  haveI : Flat m.left := h2
  haveI : Surjective m.left := h3
  obtain ⟨B, _, φ, hφ, h⟩ := FlatRoots.exists_lifts m.left S J (fun i => (t i).left) Finset.univ
  choose w hw using fun i => h i (Finset.mem_univ i)
  have hb : ∀ i, w i ≫ Xo.univ.t.G.hom = spMap φ ≫ x0 := fun i => by
    rw [← Over.w m, ← Category.assoc, hw i, Category.assoc, Over.w (t i)]
    rfl
  refine ⟨B, inferInstance, φ, fun i => Over.homMk (w i) (hb i), hφ, fun i => ?_⟩
  have e : ∀ x : ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G, x ^ N = x ≫ m := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, Over.comp_left]
  exact hw i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFlatUniversalTorsionTuple
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorsTuple

theorem exists_power {X : Scheme.{0}} (Q : Over X) [IsAffineHom Q.hom] [Flat Q.hom] (J : Type) [Finite J] :
    ∃ (R : Over X) (p : J → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : J → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by

  have key : ∀ n : ℕ, ∃ (R : Over X) (p : Fin n → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : Fin n → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by
    intro n
    induction n with
    | zero =>
      refine ⟨Over.mk (𝟙 X), fun i => i.elim0, ?_, ?_, fun T u => ⟨Over.homMk T.hom (by simp), fun i => i.elim0⟩⟩
      · show IsAffineHom (𝟙 X)
        infer_instance
      · show Flat (𝟙 X)
        infer_instance
    | succ n ih =>
      obtain ⟨R, p, hRa, hRf, hR⟩ := ih
      have ha : IsAffineHom (pullback.fst R.hom Q.hom) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
          (IsPullback.of_hasPullback R.hom Q.hom).flip ‹_›
      let R' : Over X := Over.mk (pullback.fst R.hom Q.hom ≫ R.hom)
      let a : R' ⟶ Q := Over.homMk (pullback.snd R.hom Q.hom) pullback.condition.symm
      let b : R' ⟶ R := Over.homMk (pullback.fst R.hom Q.hom) rfl
      refine ⟨R', Fin.cons (α := fun _ => R' ⟶ Q) a (fun i => b ≫ p i), ?_, ?_, ?_⟩
      · show IsAffineHom (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · show Flat (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · intro T u
        obtain ⟨v, hv⟩ := hR T (fun i => u i.succ)
        have hc : v.left ≫ R.hom = (u 0).left ≫ Q.hom := by rw [Over.w v, Over.w (u 0)]
        refine ⟨Over.homMk (pullback.lift v.left (u 0).left hc) (by
          change _ ≫ pullback.fst R.hom Q.hom ≫ R.hom = _
          rw [pullback.lift_fst_assoc, Over.w v]), ?_⟩
        refine Fin.cases ?_ (fun i => ?_)
        · apply Over.OverMorphism.ext
          simp only [a, Fin.cons_zero, Over.comp_left, Over.homMk_left]
          exact pullback.lift_snd _ _ _
        · apply Over.OverMorphism.ext
          simp only [b, Fin.cons_succ, Over.comp_left, Over.homMk_left, ← hv i]
          rw [pullback.lift_fst_assoc]
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  obtain ⟨R, p, ha, hf, hu⟩ := key n
  refine ⟨R, fun j => p (e j), ha, hf, fun T u => ?_⟩
  obtain ⟨v, hv⟩ := hu T (fun i => u (e.symm i))
  exact ⟨v, fun j => by simpa using hv (e j)⟩

theorem exists_point {X : Scheme.{0}} (R : Over X) [IsAffineHom R.hom] [Flat R.hom] (S : Type) [CommRing S]
    (x0 : Sp S ⟶ X) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Over.mk (spMap φ ≫ x0) ⟶ R), φ.Flat ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : Over.mk (spMap ψ ≫ x0) ⟶ R),
        ∃ χ : B →+* T, χ.comp φ = ψ ∧ u.left = spMap χ ≫ w.left := by

  have : IsAffine (pullback x0 R.hom) := inferInstance
  let e := (pullback x0 R.hom).isoSpec
  obtain ⟨φ, hφ⟩ : ∃ φ : S →+* Γ(pullback x0 R.hom, ⊤), spMap φ = e.inv ≫ pullback.fst x0 R.hom :=
    ⟨_, Spec.map_preimage _⟩
  have hw : (e.inv ≫ pullback.snd x0 R.hom) ≫ R.hom = (Over.mk (spMap φ ≫ x0)).hom := by
    simp [hφ, pullback.condition]
  refine ⟨Γ(pullback x0 R.hom, ⊤), inferInstance, φ, Over.homMk (e.inv ≫ pullback.snd x0 R.hom) hw, ?_, ?_⟩
  · have hfl : Flat (spMap φ) := by
      rw [hφ]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl
  · intro T _ ψ u
    let g : Sp T ⟶ pullback x0 R.hom := pullback.lift (spMap ψ) u.left (Over.w u).symm
    obtain ⟨χ, hχ⟩ : ∃ χ : Γ(pullback x0 R.hom, ⊤) →+* T, spMap χ = g ≫ e.hom := ⟨_, Spec.map_preimage _⟩
    refine ⟨χ, ?_, ?_⟩
    · have h1 : spMap (χ.comp φ) = spMap ψ := by
        change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ) = _
        rw [Spec.map_comp]
        change spMap χ ≫ spMap φ = _
        rw [hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_fst _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    · rw [hχ]
      change u.left = (g ≫ e.hom) ≫ e.inv ≫ pullback.snd x0 R.hom
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact (pullback.lift_snd _ _ _).symm

theorem exists_kernel {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] :
    ∃ (Q : Over X) (j : Q ⟶ A), IsAffineHom Q.hom ∧ Flat Q.hom ∧ j ^ k = 1 ∧
      ∀ (T : Over X) (u : T ⟶ A), u ^ k = 1 → ∃ v : T ⟶ Q, v ≫ j = u := by

  have hm : ∀ {T : Over X} (u : T ⟶ A), u ^ k = u ≫ mulA A k := by
    intro T u
    rw [show mulA A k = 𝟙 A ^ k from rfl, MonObj.comp_pow, Category.comp_id]

  let Q : Over X := Over.mk (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left : _ ⟶ X)
  have hjw : pullback.fst (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left ≫ A.hom = Q.hom := by
    rw [← Over.w (mulA A k), pullback.condition_assoc, Over.w]
    exact Category.comp_id _
  let j : Q ⟶ A := Over.homMk (pullback.fst _ _) hjw
  refine ⟨Q, j, ?_, ?_, ?_, ?_⟩
  · show IsAffineHom (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · show Flat (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · rw [hm j]
    apply Over.OverMorphism.ext
    show (j ≫ mulA A k).left = (toUnit Q ≫ MonObj.one).left
    rw [Over.comp_left, Over.comp_left]
    exact pullback.condition
  · intro T u hu
    have h0 : u ≫ mulA A k = toUnit T ≫ MonObj.one := by
      rw [← hm u, hu]
      rfl
    have h1 : u.left ≫ (mulA A k).left = T.hom ≫ (MonObj.one : 𝟙_ (Over X) ⟶ A).left := by
      have h2 := congrArg (fun f => f.left) h0
      simp only [Over.comp_left] at h2
      exact h2
    refine ⟨Over.homMk (pullback.lift u.left T.hom h1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact pullback.lift_fst _ _ _

theorem exists_tuple {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (J : Type) [Finite J] :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (Over.mk (spMap φ ≫ x0) ⟶ A)), φ.Flat ∧
      (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (Over.mk (spMap ψ ≫ x0) ⟶ A)),
        (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  obtain ⟨Q, j, hQa, hQf, hj, hQ⟩ := exists_kernel A k
  have := hQa
  have := hQf
  obtain ⟨R, p, hRa, hRf, hR⟩ := exists_power Q J
  have := hRa
  have := hRf
  obtain ⟨B, iB, φ, w, hφ, hw⟩ := exists_point R S x0
  refine ⟨B, iB, φ, fun i => w ≫ p i ≫ j, hφ, fun i => ?_, ?_⟩
  · show (w ≫ p i ≫ j) ^ k = 1
    rw [← Category.assoc, ← MonObj.comp_pow, hj, MonObj.comp_one]
  · intro T _ ψ u hu
    choose v hv using fun i => hQ _ (u i) (hu i)
    obtain ⟨v', hv'⟩ := hR _ v
    obtain ⟨χ, hχ, hχw⟩ := hw T ψ v'
    refine ⟨χ, hχ, fun i => ?_⟩
    rw [← hv i, ← hv' i]
    simp [hχw]

end TorsTuple

theorem exists_flat_universal_torsion_tuple :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (J : Type) [Fintype J], ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.Flat ∧ (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)), (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 k hk J _

  have hN := hL.mulN
  unfold MulNSt at hN
  obtain ⟨hloc, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨hfin, hfl, -⟩ := hN Xo.X (UnivPol.pol Xo) k hk
  have hfin' : IsFinite (mulA Xo.univ.t.G k).left := hfin
  have hfl' : Flat (mulA Xo.univ.t.G k).left := hfl
  exact TorsTuple.exists_tuple Xo.univ.t.G k S x0 J

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetAllComponentsMax
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.NetMax

open GlobalTheory.NetMulti

theorem exists_net_all_components_max : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] [Nonempty Comp] (Xx : Comp → DataX E r) (la : ∀ k, Wt (Xx k).Ψ r) (M w L : ℝ), 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → (∀ k, (∑ τ, (Xx k).spread (la k) τ) ≤ w) → (∀ k, ∀ v ∈ (Xx k).L', herm (Xx k).Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ (Xx k).Γ, (Xx k).χ (la k) γ = 1 ∧ ∀ τ : (Xx k).Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = (Xx k).flowMat v τ ((M : ℂ) * τ.1 b)) → Real.log (fdeg E) ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log (dE E) ≤ 4 * fdeg E * L → (∀ k, Real.log (1 + ∑ τ, ∑ i, |(la k τ i : ℝ)|) ≤ 3 * L ∧ Real.log (Xx k).NA ≤ 30 * fdeg E * L ∧ Real.log (Xx k).NC ≤ 30 * fdeg E * L ∧ Real.log (Xx k).g ≤ 30 * fdeg E * L) → Real.log (Fintype.card Comp) ≤ 41 * (fdeg E * r * L) ^ 2 → ∃ NN : Finset (FPt (fun k => (Xx k).toData)), NN.Nonempty ∧ (∀ P ∈ holSub (fun k => (Xx k).toData) la, ∃ p ∈ NN, supN (fun k => (Xx k).toData) la P ≤ 4 * ((fun k => (Xx k).toData) p.1).pnorm (la p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * (fdeg E * r * L) ^ 3 := by
  classical
  intro E _ _ _ r Comp _ _ Xx la M w L hr hL hM hw hsp hT hfL hrL hML hwL hdL hk hC

  have hf1 : (1 : ℝ) ≤ fdeg E := by
    have h2 := GlobalTheory.BoundedBasis.finrank_eq_two_mul_fdeg (E := E)
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : 1 ≤ fdeg E := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 1 ≤ (fdeg E : ℝ) * r * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL

  have hnet : ∀ k, ∃ N : Finset (Frame (Xx k).Ψ r), N.Nonempty ∧ (∀ y ∈ N, y ∈ (Xx k).dom) ∧
      (∀ Q ∈ (Xx k).SS (la k), ∀ x ∈ (Xx k).dom, ∃ y ∈ N,
        (Xx k).pnorm (la k) Q x ≤ 4 * (Xx k).pnorm (la k) Q y) ∧
      Real.log (16 * N.card) ≤ 1000 * ((fdeg E : ℝ) * r * L) ^ 3 := by
    intro k
    have hex := GlobalTheory.exists_finite_net (Xx k) (la k) M w (by linarith) (hsp k) hw (hT k)
    dsimp only at hex
    obtain ⟨N, hne, hdom, hmax, -, hsz⟩ := hex
    refine ⟨N, hne, hdom, hmax, ?_⟩
    obtain ⟨hs, hNA, hNC, hg⟩ := hk k
    have hk0 : Real.log (Xx k).k0 ≤ 4 * L := by
      have h1 : Real.log (Xx k).k0 ≤ Real.log 2 := Real.log_le_log (Xx k).minWeight_pos (Xx k).k0_le
      have h2 := Real.log_two_lt_d9
      norm_num at h2
      linarith
    have hcub := GlobalTheory.NetSize.net_size_cubic (fdeg E) r L M w (Xx k).k0 (dE E)
      (∑ τ, ∑ i, |(la k τ i : ℝ)|) (Xx k).NA (Xx k).NC (Xx k).g hf1 hr1 hL hM hw (Xx k).minWeight_pos
      (GlobalTheory.NetMulti.one_le_absDisc E) (by positivity) (by exact_mod_cast (Xx k).NA_pos)
      (by exact_mod_cast (Xx k).NC_pos) (by exact_mod_cast (Xx k).g_pos) hfL hrL hML hwL hk0 hdL
      hs hNA hNC hg
    have hcard : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.2 hne
    rw [Real.log_mul (by norm_num) hcard.ne']
    linarith
  choose N hNne hNdom hNmax hNsz using hnet

  let NN : Finset (FPt (fun k => (Xx k).toData)) :=
    Finset.univ.sigma fun k => (N k).subtype fun y => y ∈ ((Xx k).dom : Set (Frame (Xx k).Ψ r))
  have hmemNN : ∀ k y (hy : y ∈ (Xx k).dom), y ∈ N k →
      (⟨k, ⟨y, hy⟩⟩ : FPt (fun k => (Xx k).toData)) ∈ NN := by
    intro k y hy hyN
    simp only [NN, Finset.mem_sigma, Finset.mem_univ, Finset.mem_subtype, true_and]
    exact hyN
  have hNNne : NN.Nonempty := by
    obtain ⟨k⟩ := (inferInstance : Nonempty Comp)
    obtain ⟨y, hy⟩ := hNne k
    exact ⟨_, hmemNN k y (hNdom k y hy) hy⟩
  refine ⟨NN, hNNne, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨p, hpNN, hpmax⟩ := NN.exists_max_image
      (fun q => ((Xx q.1).toData).pnorm (la q.1) (P q.1) q.2) hNNne
    refine ⟨p, hpNN, ?_⟩
    have hSS := GlobalTheory.NetMulti.component_mem_SS (fun k => (Xx k).toData) la hP
    have hp0 : 0 ≤ ((Xx p.1).toData).pnorm (la p.1) (P p.1) p.2 := by
      unfold Data.pnorm
      exact mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)
    unfold supN
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    unfold supE
    refine iSup_le fun q => ?_
    obtain ⟨k, x, hx⟩ := q
    obtain ⟨y, hy, hxy⟩ := hNmax k (P k) (hSS k) x hx
    have hle := hpmax _ (hmemNN k y (hNdom k y hy) hy)
    apply ENNReal.ofReal_le_ofReal
    simp only at hle hxy ⊢
    linarith
  ·
    have h2 : ∀ k, 16 * ((N k).card : ℝ) ≤ Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) := by
      intro k
      have hc : (0 : ℝ) < (N k).card := by exact_mod_cast Finset.card_pos.2 (hNne k)
      exact (Real.log_le_iff_le_exp (by positivity)).1 (hNsz k)
    have h1 : (NN.card : ℝ) ≤ ∑ k : Comp, ((N k).card : ℝ) := by
      have : NN.card ≤ ∑ k : Comp, (N k).card := by
        simp only [NN, Finset.card_sigma]
        exact Finset.sum_le_sum fun k _ =>
          (Finset.card_subtype _ _).trans_le (Finset.card_filter_le _ _)
      exact_mod_cast this
    have hcardle : 16 * (NN.card : ℝ) ≤
        Fintype.card Comp * Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) := by
      calc 16 * (NN.card : ℝ) ≤ 16 * ∑ k : Comp, ((N k).card : ℝ) := by linarith
        _ = ∑ k : Comp, 16 * ((N k).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ ∑ _k : Comp, Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) :=
          Finset.sum_le_sum fun k _ => h2 k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hNNpos : 0 < 16 * (NN.card : ℝ) := by
      have : (0 : ℝ) < NN.card := by exact_mod_cast Finset.card_pos.2 hNNne
      positivity
    have hCpos : (0 : ℝ) < Fintype.card Comp := by exact_mod_cast Fintype.card_pos
    set A := (fdeg E : ℝ) * r * L with hAdef
    have hA23 : A ^ 2 ≤ A ^ 3 := by nlinarith [sq_nonneg A, mul_nonneg (sq_nonneg A) (sub_nonneg.2 hA)]
    calc Real.log (16 * NN.card) ≤ Real.log (Fintype.card Comp * Real.exp (1000 * A ^ 3)) :=
          Real.log_le_log hNNpos hcardle
      _ = Real.log (Fintype.card Comp) + 1000 * A ^ 3 := by
          rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 1041 * A ^ 3 := by linarith

end GlobalTheory.NetMax
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) → ∃ (s : Finset (Matrix (Fin n) (Fin r) E)) (cf : Matrix (Fin n) (Fin r) E → ℂ), (∀ y ∈ s, ∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ z, F z = ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := by
  first | exact @GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | exact GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | (intros; apply GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates <;> assumption)
end

