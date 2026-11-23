module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

theorem cotMap_list_prod {S : Scheme.{0}} {T G : Over S} [GrpObj G] [QuasiSeparated G.hom] {s : 𝟙_ (Over S) ⟶ T} :
    ∀ {m : ℕ} (z : Fin m → (T ⟶ G)) (hz : ∀ i, s ≫ z i = η) (h : s ≫ (List.ofFn z).prod = η),
      cotMap (List.ofFn z).prod h = ∑ i, cotMap (z i) (hz i)
  | 0, z, hz, h => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact cotMap_eq_zero (by rw [List.ofFn_zero, List.prod_nil, Hom.one_def]) _
  | m + 1, z, hz, h => by
    have e : (List.ofFn z).prod = z 0 * (List.ofFn fun i : Fin m => z i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have h₁ : (η : 𝟙_ (Over S) ⟶ G) = 1 := by rw [Hom.one_def]; simp
    have h' : s ≫ (List.ofFn fun i : Fin m => z i.succ).prod = η := by
      have := h
      rw [e, MonObj.comp_mul, hz 0, h₁, _root_.one_mul] at this
      exact this.trans h₁.symm
    rw [Fin.sum_univ_succ, ← cotMap_list_prod (fun i : Fin m => z i.succ) (fun i => hz _) h',
      ← cotMap_mul (hz 0) h' (e ▸ h)]
    congr 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
variable {G' : Over (Sp k)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}

theorem exists_fibre_vector (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ y : specO k (DualNumber k) ⟶ G', epsZero k ≫ y = η ∧ y.left ≫ φ = v := by
  refine ⟨Over.homMk (hp.1.lift v _ hv.1) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_),
    hp.1.lift_fst _ _ _⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (sec (epsZero k) ≫ ·) (hp.1.lift_fst _ _ _)).trans ?_)
    exact (epsZero_comp_of_isTanAtG t hv).trans (unitSec_comp hp).symm
  · exact (Over.w _).trans (Over.w _).symm

theorem tanForm_eq_fibre (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v)
    {y : specO k (DualNumber k) ⟶ G'} (hy : epsZero k ≫ y = η) (e : y.left ≫ φ = v) :
    tanForm t hv = omegaBase hp ≫ cotMap y hy ≫ (epsIso k).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso k).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ := le_of_sq (unitSec_comp hp) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₂ := le_of_sq (epsZero_comp_of_isTanAtG t hv) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₃ := (le_preimage_of_comp e).2 (le_refl (v ⁻¹ᵁ W))
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl
    k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap y hy).app _) (omegaBase_dUnit hp le_rfl le_rfl k₁ le_rfl a)).trans ?_
  exact (cotMap_d y hy k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE e _ _ _ a))

theorem tanEv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V),
    ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (cf : Fin m → k)
      (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w), IsCombAtG t x v cf w →
      ∀ s : Γ(GlobalTheory.LieVB.omega t.G, V), tanEv t hw h s = ∑ i, cf i * tanEv t (hv i) h s := by
  rintro E _ _ _ H X t k _ x V h m v hv cf w hw ⟨u, hu, hw'⟩ s
  have hp := isGrpPullback_pullback t.G x
  have := t.semi
  have : QuasiSeparated ((Over.pullback x).obj t.G).hom := MorphismProperty.of_isPullback hp.1 inferInstance
  choose y hy ey using fun i => exists_fibre_vector t hp (hv i)
  obtain ⟨yw, hyw, eyw⟩ := exists_fibre_vector t hp hw
  let z := fun i => ptMap (dualScale (cf i)) ≫ y i
  have hz (i : Fin m) : epsZero k ≫ z i = η := by
    rw [← Category.assoc, epsZero_dualScale, hy]
  have hu' : u = fun i => pushHom hp _ (z i) := funext fun i => Over.OverMorphism.ext <| by
    refine (hu i).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    rw [ey]
    rfl
  have hprod : yw = (List.ofFn z).prod := by
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine eyw.trans (hw'.symm.trans ?_)
    rw [hu']
    exact (congrArg (fun q => q.left) ((map_list_prod (pushHom hp (specO k (DualNumber k))) (List.ofFn z)).trans
      (congrArg List.prod List.map_ofFn))).symm
  subst hprod
  let σ := (omegaBase hp).app ⊤ (pullbackSections x (omega t.G) h s)
  let F : (conormal (unitSec ((Over.pullback x).obj t.G)) ⟶ conormal (sec (epsZero k))) →+ k :=
    AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
      (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
        (map_add _ _ _)
  have hF {v' : Sp (DualNumber k) ⟶ t.G.left} (hv' : IsTanAtG t x v') {y'} (hy' : epsZero k ≫ y' = η)
      (e : y'.left ≫ pullback.fst t.G.hom x = v') : tanEv t hv' h s = F (cotMap y' hy') := by
    rw [tanEv, tanForm_eq_fibre t hp hv' hy' e]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hF hw hyw eyw, cotMap_list_prod z hz, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := cotMap_comp (hy i) (epsZero_dualScale (cf i)) rfl (hz i)
  rw [cotMap_dualScale] at e
  rw [hF (hv i) (hy i) (ey i), ← e]
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom
    ((epsIso k).hom.app_smul (cst k (cf i)) ((cotMap (y i) (hy i)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRep

theorem exists_finite_free_rep (O : Type) [CommRing O] [HenselianLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Sp O)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (j : Sp A ⟶ Y), Module.Finite O A ∧ Module.Free O A ∧
      j ≫ f = spMap (algebraMap O A) ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (h : Sp B ⟶ Y), h ≫ f = spMap (algebraMap O B) → ∃! φ : A →ₐ[O] B, spMap (φ : A →+* B) ≫ j = h := by
  have : HenselianLocalRing (CommRingCat.of O) := ‹_›
  have hfin : IsFinite ((finitePart f).ι ≫ f) := isFinite_finitePart f
  have : IsAffine (finitePart f).toScheme := isAffine_of_isAffineHom ((finitePart f).ι ≫ f)
  let A : CommRingCat.{0} := Γ((finitePart f).toScheme, ⊤)
  let i : Spec A ≅ (finitePart f).toScheme := (finitePart f).toScheme.isoSpec.symm
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.hom ≫ (finitePart f).ι ≫ f)
  have h₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have h₂ : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have h₃ : Module.Finite O A := h₁
  have h₄ : Module.Flat O A := h₂
  have hj : (i.hom ≫ (finitePart f).ι) ≫ f = spMap (algebraMap O A) := by
    rw [Category.assoc, ← hψ]; rfl
  refine ⟨A, inferInstance, inferInstance, i.hom ≫ (finitePart f).ι, h₃,
    Module.free_of_flat_of_isLocalRing, hj, fun B _ _ _ h hh => ?_⟩
  have : IsFinite (spMap (algebraMap O B)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 ‹_›)
  obtain ⟨l, hl, -⟩ := existsUnique_lift_finitePart f _ h hh
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (R := A) (S := .of B) (l ≫ i.inv)
  have hχ' : Spec.map χ ≫ i.hom ≫ (finitePart f).ι = h := by
    rw [hχ, Category.assoc, i.inv_hom_id_assoc, hl]
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ χ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ hh
    rw [← hχ', Category.assoc, hj]
  refine ⟨⟨χ.hom, fun r => congr(($hc).hom r)⟩, hχ', fun φ hφ => ?_⟩
  have h₅ : spMap (φ : A →+* B) = Spec.map χ := by
    rw [← cancel_mono (i.hom ≫ (finitePart f).ι)]
    exact hφ.trans hχ'.symm
  have h₆ := Spec.map_injective h₅
  exact AlgHom.ext fun a => congr(($h₆).hom a)

theorem exists_finite_free_torsion_rep : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  intro X G _ _ hG O _ _ x q hq
  obtain ⟨hf, hqf⟩ := _root_.GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow X G hG q hq
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let m : G ⟶ G := (𝟙 G) ^ q
  have hm : ∀ {T : Over X} (g : T ⟶ G), g ≫ m = g ^ q := fun g => by
    rw [MonObj.comp_pow, Category.comp_id]
  have : Flat m.left := hf
  have : LocallyQuasiFinite m.left := hqf
  have : LocallyOfFiniteType (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact m.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated m.left := IsSeparated.of_comp _ G.hom
  let e : Sp O ⟶ G.left := (1 : Over.mk x ⟶ G).left
  have he : e ≫ G.hom = x := Over.w (1 : Over.mk x ⟶ G)
  have h1 : ∀ (B : Type) [CommRing B] [Algebra O B],
      (1 : overAt x B ⟶ G).left = spMap (algebraMap O B) ≫ e := fun B _ _ => by
    let t : overAt x B ⟶ Over.mk x := Over.homMk (spMap (algebraMap O B)) rfl
    rw [← MonObj.comp_one t]
    rfl
  have : LocallyQuasiFinite (pullback.snd m.left e) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (IsPullback.of_hasPullback m.left e) hqf
  obtain ⟨A, _, _, j, hA₁, hA₂, hj, H⟩ := exists_finite_free_rep O (pullback.snd m.left e)
  have hu : (j ≫ pullback.fst m.left e) ≫ m.left = spMap (algebraMap O A) ≫ e := by
    rw [Category.assoc, pullback.condition, reassoc_of% hj]
  let u : overAt x A ⟶ G := Over.homMk (j ≫ pullback.fst m.left e) (by
    rw [← Over.w m, ← Category.assoc]
    exact (congrArg (· ≫ G.hom) hu).trans (by rw [Category.assoc, he]; rfl))
  refine ⟨A, inferInstance, inferInstance, u, hA₁, hA₂, ?_, fun B _ _ _ g hg => ?_⟩
  · rw [← hm]
    exact Over.OverMorphism.ext (hu.trans (h1 A).symm)
  have hg' : g.left ≫ m.left = spMap (algebraMap O B) ≫ e := by
    rw [← Over.comp_left, hm, hg, h1]
  obtain ⟨φ, hφ, hφ'⟩ := H B (pullback.lift g.left (spMap (algebraMap O B)) hg') (pullback.lift_snd _ _ _)
  refine ⟨φ, Over.OverMorphism.ext ?_, fun φ' h' => hφ' φ' ?_⟩
  · change spMap (φ : A →+* B) ≫ j ≫ pullback.fst m.left e = g.left
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc]
      exact (congrArg CommaMorphism.left h').trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hj]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ'.comp_algebraMap]

end GlobalTheory.TorsionRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.TwoMarkings

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ}

theorem linearIndependent_dirs {i : Fin Fu.n} {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ}
    {y : Sp ℂ ⟶ Xo.XF c} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hy : y ≫ pullback.fst _ _ = Fu.u i P) (hj : y ≫ Z.jQ = a.1.1)
    {v₀ : Letter Dw → (Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left)}
    (h1 : ∀ z, v₀ z ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (h2 : ∀ z, v₀ z ≫ Z.m.φ = a.2.v z.1 z.2)
    (h3 : ∀ z, IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ z ≫ Z.m0.toSABMap.φ)) :
    LinearIndependent ℂ W := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hj]
  have hty : ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := fun z =>
    (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ z.1 (h3 z)).1 fun b =>
      (eig_iff Z.m0.toSABMap (h1 z) b _).2 ((eig_iff Z.m (h1 z) b _).1 (h2 z ▸ a.2.eig z.1 z.2 b))
  obtain ⟨t1, t2, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 0
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [(t1 _ _ hv).1, ← hy, Category.assoc])
  rw [Fintype.linearIndependent_iff]
  rintro cf hc ⟨τ, k⟩
  have hb := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hy k1).1 (t1 _ _ hv)))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1
      ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ τ hv).2 (fun j hj => absurd rfl hj) b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hb
  have hcomb : ∀ d : Fin (Dw.mult τ) → ℂ, ∑ k, d k • W ⟨τ, k⟩ = 0 →
      IsCombAtG Z.t (a.1.1 ≫ genι Z) (fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ) d (v' ≫ Z.m.φ) := fun d hd =>
    (comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) d k1).2 ((comb_iff Z.m0.toSABMap hy (fun k => h1 ⟨τ, k⟩) d k1).1
      ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _ _ (fun k => h3 ⟨τ, k⟩) d _).2 (hd ▸ hv)))
  have hτ : ∑ k, cf ⟨τ, k⟩ • W ⟨τ, k⟩ = 0 := by
    funext j
    have hz : ∀ ρ, (e j).1 ≠ ρ → (∑ k, cf ⟨ρ, k⟩ • W ⟨ρ, k⟩) j = 0 := fun ρ hρ => by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Pi.smul_apply, by_contra fun h => hρ (hty ⟨ρ, k⟩ j h), smul_zero]
    by_cases h : (e j).1 = τ
    · have := congrFun hc j
      rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single τ (fun ρ _ hρ => hz ρ (h ▸ hρ.symm)) (by simp)] at this
      exact this
    · exact hz τ h
  exact congrFun (hb.unique (hcomb _ hτ) (hcomb 0 (by simp))) k

theorem per_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a
  haveI := Z.jQ_open
  refine ⟨?_, ?_⟩
  · rintro i j Q Q' ⟨P, W, y, hP, hy, hj, -⟩ ⟨P', W', y', hP', hy', hj', -⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    exact Fu.disj i j P P' hP hP' (hy.symm.trans hy')
  · rintro i Q Q' ⟨P, W, y, hP, hy, hj, hv, hQ⟩ ⟨P', W', y', hP', hy', hj', hv', hQ'⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    choose v₀ h1 h2 h3 using hv
    choose v₁ k1 k2 k3 using hv'
    obtain rfl : v₀ = v₁ := funext fun z =>
      Z.m.cart.1.hom_ext ((h2 z).trans (k2 z).symm) ((h1 z).trans (k1 z).symm)
    obtain ⟨gam, h, g1, g2, g3, g4⟩ := (Fu.fibre i P P' hP hP').1 (hy.symm.trans hy')
    have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
      LinearMap.toMatrix'_mulVec _ z
    obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ Fu i P P' gam
      (LinearMap.toMatrix' h.toLinearMap) hP hP' g1 g2 g3 (fun a => by rw [hm, g4])
    simp only [hm] at h5
    obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P' hP'
    have hW : ∀ z, h (W z) = W' z := fun z => (t3 _ (t1 _ _ (k3 z))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ Fu i P hP i P' h.toLinearMap hP' h5 _ _).1 (h3 z)) (k3 z)
    refine ⟨gam, g1, g2, fun v => funext fun z => ?_⟩
    refine Fintype.linearIndependent_iffₛ.1 (linearIndependent_dirs hP' hy' hj' k1 k2 k3) _ _ ?_ z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hQ', g4, hQ, map_sum]
    simp only [map_smul, hW]

end GlobalTheory.ShFam.Hor.TwoMarkings
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open CategoryTheory.Limits

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (y₀ : FrPt Xo c (Formalism.L2.Pj.CAt σ)), cxPt Z y₀ ∈ ch.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ ch.e (cxPt Z y₀) ∈ B ∧ B ⊆ ch.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∀ y : FrPt Xo c (Formalism.L2.Pj.CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ d g ty Fu ch y₀ hy₀
  have := Z.jQ_open
  let L := EuclideanSpace.equiv (Fin d) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm ch
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.e.target | ⊤ ≤ (ch.e.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  have hb₀ : ch.e (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.e.map_source hy₀, ?_⟩
    rw [ch.e.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.e.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.e.symm b).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift d (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (ch.e (cxPt Z y₀)))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb y hy => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h1 : w b = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y :=
      (cancel_mono Z.jQ).1 ((hw b hb1).trans (congrArg Subtype.val hy))
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    rw [h2, h1]
    exact GlobalTheory.ShFam.ptF_fst y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZeroSubspaceSpannedByDataZeroSubspaceLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  first | exact @GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift | exact GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift | (intros; apply GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift <;> assumption)
end

