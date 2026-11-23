module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLattice
section
open NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem stab_hatL_mapsTo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  intro hF x hx v hv
  obtain ⟨y, rfl⟩ := hx
  have hw := (hF v).1 hv
  refine (hF _).2 fun i => ?_
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype with hY
  have hval : ((Formalism.L2.DIV.frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) =
      (β : Matrix (Fin n) (Fin n) _) * Y * ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Units.val_mul]
    rfl
  have hmv : ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((Formalism.L2.DIV.frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) =
      Y *ᵥ (((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) := by
    rw [hval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  rw [hmv]
  simp only [Matrix.mulVec, dotProduct]
  refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
  simp only [hY, Matrix.map_apply]
  exact (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j |>.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

open Opposite TopologicalSpace

theorem uConst_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → UConst A.hom := by
  intro R _ A _ hA R' _ _ X' s' φ hpb
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsm : Smooth s' := MorphismProperty.of_isPullback hpb ‹_›
  have hpr : IsProper s' := MorphismProperty.of_isPullback hpb ‹_›
  have hgc : GeometricallyConnected s' := MorphismProperty.of_isPullback hpb ‹_›
  haveI : GeometricallyIntegral s' :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X' _ s' hsm hgc
  have hiso : IsIso s'.appTop := GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth s' ⊤
  have hbij := ConcreteCategory.bijective_of_isIso s'.appTop
  intro g hg
  have hc : ∀ (U V : X'.affineOpens) (h : V.1 ≤ U.1),
      X'.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, htu⟩ := X'.sheaf.existsUnique_gluing' (fun U : X'.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X').ge (fun U ↦ g (op U)) (by
      intro U V
      refine X'.sheaf.eq_of_locally_eq' (fun W : {W : X'.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens X'} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(X', a)),
            X'.presheaf.map f'.op (X'.presheaf.map f.op x) = X'.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))

  have hres : ∀ (r : R') (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) =
        algebraMap R' (Sec s' U.1) r := by
    intro r U
    rfl
  have hres' : ∀ (x : Γ(Sp R', ⊤)) (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop x) =
        algebraMap R' (Sec s' U.1) ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) := by
    intro x U
    have := hres ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) U
    rw [Iso.hom_inv_id_apply] at this
    exact this
  obtain ⟨r₀, hr₀⟩ := hbij.2 t
  subst hr₀
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R')).hom r₀, ?_, ?_⟩
  · intro U
    exact (ht U.unop).symm.trans (hres' r₀ U.unop)
  · intro r hr
    have h1 : s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r) = s'.appTop r₀ := by
      apply htu
      intro U
      exact (hres r U).trans (hr (op U)).symm
    have h2 := hbij.1 h1
    rw [← h2, Iso.inv_hom_id_apply]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstant
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem frame_coord : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R),
      (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧
        ∀ w, w = ∑ i, l i w • Φ.w i := by
  intro R _ C _ F hF n Φ
  have hd : ∀ i (w : Glob1 F), d0 F (fun T ↦ Φ.δ i T (w.1 T)) = 0 := by
    intro i w
    funext T T' φ
    rw [amitsur_d0_apply, w.2 φ, Φ.nat]
    exact sub_self _
  let c : Fin n → Glob1 F → R := fun i w ↦ (hF _ (hd i w)).exists.choose
  have hc : ∀ i w T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (c i w) :=
    fun i w ↦ (hF _ (hd i w)).exists.choose_spec
  have uniq : ∀ i w (r : R), (∀ T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) r) → c i w = r :=
    fun i w r hr ↦ (hF _ (hd i w)).unique (hc i w) hr
  refine ⟨fun i ↦
    { toFun := c i
      map_add' := fun w w' ↦ uniq i (w + w') _ (fun T ↦ by
        rw [Submodule.coe_add, Pi.add_apply, map_add (f := _), hc, hc, map_add (f := _)])
      map_smul' := fun r w ↦ uniq i (r • w) _ (fun T ↦ by
        rw [Submodule.coe_smul, Pi.smul_apply, ← algebraMap_smul (F.obj T) r (w.1 T), map_smul, hc,
          RingHom.id_apply, smul_eq_mul, smul_eq_mul, map_mul]) },
    fun i w T ↦ hc i w T, fun w ↦ ?_⟩
  apply Subtype.ext
  funext T
  rw [Submodule.coe_sum, Finset.sum_apply]
  conv_lhs => rw [Φ.sum T (w.1 T)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hc, Submodule.coe_smul, Pi.smul_apply, algebraMap_smul]
  rfl

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.TwoFormSum

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def coordPair (f g : Module.Dual B Ω[B⁄R]) : Module.Dual B (Om R B 2) :=
  exteriorPower.pairingDual B Ω[B⁄R] 2 (exteriorPower.ιMulti B 2 ![f, g])

theorem coordPair_wedge (f g : Module.Dual B Ω[B⁄R]) (a b : Ω[B⁄R]) :
    coordPair f g (wedge R B a b) = f a * g b - g a * f b := by
  rw [wedge_eq_ιMulti, coordPair, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

theorem ιMulti_two (v : Fin 2 → Ω[B⁄R]) : exteriorPower.ιMulti B 2 v = wedge R B (v 0) (v 1) := by
  rw [wedge_eq_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem sum_sum_eq_lt {M : Type} [AddCommGroup M] {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j + g j i else 0) := by
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if j < i then g i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rcases lt_trichotomy i j with h | h | h
        · simp [h, not_lt.2 h.le]
        · subst h; simp [hg]
        · simp [h, not_lt.2 h.le]
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) := by
        rw [Finset.sum_comm (f := fun i j ↦ if j < i then g i j else 0)]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp

def expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) : Om R B 2 →ₗ[B] Om R B 2 :=
  ∑ i, ∑ j, if i < j then (coordPair (δ i) (δ j)).smulRight (wedge R B (w i) (w j)) else 0

theorem expand_apply {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) (x : Om R B 2) :
    expand w δ x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  simp only [expand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

theorem eq_expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R])
    (hs : ∀ ω, ω = ∑ i, δ i ω • w i) (x : Om R B 2) :
    x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  rw [← expand_apply]
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2 (M := Ω[B⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hL : wedge R B (v 0) (v 1) = ∑ i, ∑ j, (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j) := by
      conv_lhs => rw [hs (v 0), hs (v 1)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    rw [ιMulti_two, expand_apply]
    conv_lhs => rw [hL,
      sum_sum_eq_lt (fun i j ↦ (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)) (fun i ↦ by simp)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [coordPair_wedge, wedge_swap (w j) (w i), smul_neg, sub_smul]; abel
    · simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), ← hy, ← hz]
  | smul c y _ hy => rw [map_smul, ← hy]

end Alg

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem coordPair_nat {n : ℕ} (Φ : Frame F n) (i j : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (x : Om R (F.obj T) 2) :
    coordPair (Φ.δ i T') (Φ.δ j T') (pOm F 2 φ x) = mp F φ (coordPair (Φ.δ i T) (Φ.δ j T) x) := by
  have hx : x ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ιMulti_two, pOm_wedge, coordPair_wedge, coordPair_wedge, Φ.nat, Φ.nat, Φ.nat, Φ.nat]
    simp only [map_sub, map_mul]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
  | smul c y _ hy => rw [pOm_smul, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.AbCoh.TwoFormSum

namespace GlobalTheory.AbCoh


open TwoFormSum in
theorem twoForm_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) →
      ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  intro R _ C _ F ⟨n, ⟨Φ⟩⟩ h0 ζ hζ
  let g : Fin n → Fin n → C0 F := fun i j T ↦ coordPair (Φ.δ i T) (Φ.δ j T) (ζ T)
  have hg : ∀ i j, d0 F (g i j) = 0 := by
    intro i j
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [g]
    rw [hζ φ, coordPair_nat, sub_self]
    rfl
  choose c hc using fun i j ↦ (h0 (g i j) (hg i j)).exists
  let e : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm
  refine ⟨n * n, fun k ↦ (if (e k).1 < (e k).2 then c (e k).1 (e k).2 else 0) • Φ.w (e k).1,
    fun k ↦ Φ.w (e k).2, ?_⟩
  funext T
  simp only [wsum]
  rw [Fintype.sum_equiv e _ (fun p ↦ wedge R (F.obj T)
      (((if p.1 < p.2 then c p.1 p.2 else 0) • Φ.w p.1 : Glob1 F).1 T) ((Φ.w p.2).1 T)) (fun k ↦ rfl),
    Fintype.sum_prod_type]
  conv_lhs => rw [eq_expand (fun i ↦ (Φ.w i).1 T) (fun i ↦ Φ.δ i T) (Φ.sum T) (ζ T)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, wedge_smul_left]
  split_ifs
  · have := hc i j T
    simp only [g] at this
    rw [this, algebraMap_smul]
  · simp

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFrameOfIsBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem hasFrame_of_isBaseChange : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (j : W →ₗ[R] Glob1 F), (∀ T : C, ∃ e : W →ₗ[R] Ω[F.obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange (F.obj T) e) → HasFrame F := by
  intro R _ C _ F W _ _ _ _ j h
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin' R W
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property v (LinearMap.id) hv
  have hw : ∀ x : W, x = ∑ i, σ x i • v (Pi.single i 1) := by
    intro x
    have := LinearMap.congr_fun hσ x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    conv_lhs => rw [← this]
    conv_lhs => rw [show σ x = ∑ i, σ x i • Pi.single i (1 : R) from by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  choose e he hb using h
  let l : Fin n → W →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ σ
  let δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
    fun i T ↦ (hb T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l i)
  have hδ : ∀ i T (x : W), δ i T (e T x) = algebraMap R (F.obj T) (σ x i) := by
    intro i T x
    exact (hb T).lift_eq _ x
  refine ⟨n, ⟨⟨fun i ↦ j (v (Pi.single i 1)), δ, ?_, ?_⟩⟩⟩
  · intro i T T' φ ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      have h1 : p1 F φ (e T x) = e T' x := by
        rw [he T x, he T' x]; exact ((j x).2 φ).symm
      rw [h1, hδ, hδ]
      exact ((mp F φ).commutes _).symm
    · intro s ω hω
      rw [oneFormsMapOfFunctorMorphism_smul, LinearMap.map_smul, LinearMap.map_smul, hω, smul_eq_mul, smul_eq_mul, map_mul]
    · intro a b ha hb'
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb', map_add (f := _)]
  · intro T ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      simp_rw [hδ, ← he T, algebraMap_smul]
      conv_lhs => rw [hw x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp_rw [map_smul]
    · intro s ω hω
      conv_lhs => rw [hω]
      simp_rw [LinearMap.map_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
    · intro a b ha hb'
      conv_lhs => rw [ha, hb']
      simp_rw [map_add (f := _), add_smul, Finset.sum_add_distrib]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedDerivHilbertEisensteinSplitLattice
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_iterD_gval_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t u hk ha hτ
  obtain ⟨r, hr, hrad⟩ := _root_.GlobalTheory.HilbFam.exists_radius_moebius_perturbation τ c t hτ
  obtain ⟨M, hM, hbd⟩ := _root_.GlobalTheory.HilbFam.exists_summable_bound_terms F k 𝔞 𝔟 a₀ a x τ c t ha hτ
  set D : ℂ := ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k with hD
  set G : (Emb F → ℂ) → ℂ := fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) with hG
  have hcoord : ∀ z ∈ Metric.ball (0 : Emb F → ℂ) r, ∀ i, ‖z i‖ < r := fun z hz i ↦
    (norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.1 hz)
  have hne : ∀ w : ℂ, ‖w‖ < r → 1 + w * c ≠ 0 := fun w hw h ↦ by
    have := (hrad w hw).1
    rw [h, norm_zero] at this
    linarith
  have hψ : ∀ y : ℂ, DifferentiableOn ℂ (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) (Metric.ball 0 r) := by
    intro y w hw
    have h0 := hne w (mem_ball_zero_iff.1 hw)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 + w * c) w := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ y * w) w := by fun_prop
    exact (((h1.inv h0).pow k).mul (h2.div h1 h0).cexp).differentiableWithinAt
  have key := _root_.GlobalTheory.HilbFam.hasSum_iterD_termwise (Emb F) F u r
    (fun ξ z ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))))
    (fun z ↦ D⁻¹ * G z) M hr hM
    (fun ξ z hz ↦ by
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      refine (HasFDerivAt.finsetProd (𝕜 := ℂ) (u := (Finset.univ : Finset (Emb F)))
        (g := fun i (z : Emb F → ℂ) ↦ (1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))
        (fun i _ ↦ DifferentiableAt.hasFDerivAt ?_)).differentiableAt
      have h1 := ((hψ ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hcoord z hz i))))
      exact h1.comp z (differentiableAt_apply (𝕜 := ℂ) i z))
    (fun ξ z hz ↦ hbd ξ z (fun i ↦ hrad _ (hcoord z hz i)))
    (fun z hz ↦ by
      have := _root_.GlobalTheory.HilbFam.hasSum_movedPoint F k 𝔞 𝔟 a₀ a x τ c t z hk ha (fun i ↦ ⟨hne _ (hcoord z hz i), by
        have := (hrad _ (hcoord z hz i)).2
        linarith⟩)
      rw [div_eq_inv_mul] at this
      exact this)
  have hc := _root_.GlobalTheory.HilbFam.iterD_const_mul_reindex (Emb F) (Emb F) (Equiv.refl _) u G D⁻¹ 0
  simp only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id, List.map_id_fun] at hc
  have hc' : iterD u (fun z ↦ D⁻¹ * G z) 0 = iterD u G 0 / D := by
    rw [div_eq_inv_mul]; exact hc
  rw [hc'] at key
  convert key using 2 with ξ
  have := _root_.GlobalTheory.IterDProd.iterD_prod (Emb F) u r
    (fun i w ↦ (1 + w * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * w / (1 + w * c)))
    (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ)) hr
    (fun i ↦ hψ _)
  rw [this]
  congr 1
  exact Finset.prod_congr rfl (fun i _ ↦ (_root_.GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag k _ c _).symm)

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffReal
section
open Formalism.L2.DIV

namespace GlobalTheory.CuspMult

theorem idemOf_coeff_real : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ)
    (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X →
    ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  intro K G _ _ _ σ X hX hS g
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_idemOf, map_sum, star_sum]
  refine Finset.sum_nbij' (fun χ t => χ t⁻¹) (fun χ t => χ t⁻¹) hS hS
    (fun χ _ => by simp) (fun χ _ => by simp) fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  simp only [map_mul, map_div₀, map_natCast, star_mul', star_div₀, star_natCast]
  rw [h1, h2]
  rfl

end GlobalTheory.CuspMult
end

