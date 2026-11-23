module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC structureModule)
open GlobalTheory.VB

namespace GlobalTheory.LieVB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {O : Type} [CommRing O]

instance mono_toBidual_dual : Mono (cartierDualToBidual (dual F)) := by
  have h : cartierDualToBidual (dual F) ≫
      dualMap (cartierDualToBidual F) = 𝟙 _ := by
    ext V l : 3
    exact dual_ext fun W h s => congrArg (dualApp l h) (resM_self _ s)
  exact mono_of_mono_fac h

theorem mono_toBidual_of_mono (i : G ⟶ F) [Mono i] [Mono (cartierDualToBidual F)] : Mono (cartierDualToBidual G) :=
  mono_of_mono_fac (toBidual_naturality_dualSheafTranspose i).symm

theorem mono_toBidual_of_isVectorBundle {r : ℕ} (h : IsVB F r) : Mono (cartierDualToBidual F) :=
  have := h.isIso_toBidual_of_local_frames
  inferInstance

def IsRegularFn (D : Γ(X, ⊤)) : Prop :=
  ∀ (V : X.Opens) (a : Γ(X, V)), resG X (le_top : V ≤ ⊤) D * a = 0 → a = 0

theorem isRegularFn_of_ne_zero [IsIntegral X] {D : Γ(X, ⊤)} (h : D ≠ 0) : IsRegularFn D := by
  intro V a e
  rcases eq_or_ne V ⊥ with rfl | hV
  · exact Subsingleton.elim _ _
  · obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 hV
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    refine (mul_eq_zero.1 e).resolve_left fun h0 => h ?_
    exact map_injective_of_isIntegral X (homOfLE le_top) (h0.trans (map_zero _).symm)

theorem IsRegularFn.eq_zero_of_smul {D : Γ(X, ⊤)} (h : IsRegularFn D) [Mono (cartierDualToBidual F)]
    {V : X.Opens} {s : Γ(F, V)} (e : resG X (le_top : V ≤ ⊤) D • s = 0) : s = 0 := by
  refine QCoh.injective_app_of_mono (cartierDualToBidual F) V (Eq.trans ?_ (map_zero _).symm)
  refine dual_ext fun W hW l => h W _ ?_
  have := congrArg (fun t => dualApp l le_rfl (resM F hW t)) e
  simp only [resM_smul, map_smul, resG_resG, map_zero] at this
  exact this

theorem IsRegularFn.hom_eq_zero {D : Γ(X, ⊤)} (h : IsRegularFn D) [Mono (cartierDualToBidual F)]
    {φ : G ⟶ F} (e : D • φ = 0) : φ = 0 := by
  ext V s : 3
  exact h.eq_zero_of_smul congr(($e).app V s)

section Im

variable (ρ : O →+* End F) (σ : O →+* Γ(X, ⊤))

def eigenEval : F ⟶ dual (eigen (dualAct ρ) σ) := cartierDualToBidual F ≫ dualMap (eigenι (dualAct ρ) σ)

theorem eigenEval_eq : eigenEval ρ σ =
    eigenπ ρ σ ≫ cartierDualToBidual _ ≫ dualMap (dualQuotIso ρ σ).inv := by
  have hι : (dualQuotIso ρ σ).hom ≫ eigenι _ _ = dualMap (eigenπ ρ σ) := by
    simp only [dualQuotIso, asIso_hom, dualQuotHom, eigenLift_ι]
  rw [toBidual_naturality_dualSheafTranspose_assoc, ← dualMap_comp, ← hι, Iso.inv_hom_id_assoc,
    eigenEval]

def eigenIm : X.Modules := image (eigenEval ρ σ)

def eigenImπ : F ⟶ eigenIm ρ σ := factorThruImage _

def eigenImι : eigenIm ρ σ ⟶ dual (eigen (dualAct ρ) σ) := image.ι _

instance epi_eigenImπ : Epi (eigenImπ ρ σ) := inferInstanceAs (Epi (factorThruImage _))

instance mono_eigenImι : Mono (eigenImι ρ σ) :=
  inferInstanceAs (Mono (image.ι (eigenEval ρ σ)))

instance mono_toBidual_eigenImage : Mono (cartierDualToBidual (eigenIm ρ σ)) :=
  mono_toBidual_of_mono (eigenImι ρ σ)

theorem act_eigenImπ (a : O) : act ρ a ≫ eigenImπ ρ σ = σ a • eigenImπ ρ σ := by
  have h : eigenImπ ρ σ ≫ eigenImι ρ σ = eigenEval ρ σ := image.fac _
  rw [← cancel_mono (eigenImι ρ σ), Category.assoc, Linear.smul_comp, h, eigenEval_eq,
    ← Category.assoc, act_eigenπ, Linear.smul_comp]

def quotToIm : eigenQuot ρ σ ⟶ eigenIm ρ σ := eigenDesc (eigenImπ ρ σ) (act_eigenImπ ρ σ)

variable {ρ σ}

theorem comp_eq_zero_of_comp_eigenImπ [Mono (cartierDualToBidual G)] {φ : F ⟶ G}
    (h : ∀ a, act ρ a ≫ φ = σ a • φ) {k : H ⟶ F} (hk : k ≫ eigenImπ ρ σ = 0) : k ≫ φ = 0 := by
  have h' (a : O) : dualMap φ ≫ act (dualAct ρ) a = σ a • dualMap φ := by
    rw [act_dualAct, ← dualMap_comp, h, dualMap_smul]
  have hfac : eigenImπ ρ σ ≫ eigenImι ρ σ = eigenEval ρ σ := image.fac _
  rw [← cancel_mono (cartierDualToBidual G), Category.assoc, toBidual_naturality_dualSheafTranspose, ← eigenLift_ι _ _ _ h',
    dualMap_comp, zero_comp, ← Category.assoc (cartierDualToBidual F), ← eigenEval, ← hfac,
    Category.assoc, reassoc_of% hk, zero_comp]

def eigenImDesc [Mono (cartierDualToBidual G)] (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) :
    eigenIm ρ σ ⟶ G :=
  Abelian.epiDesc (eigenImπ ρ σ) φ (comp_eq_zero_of_comp_eigenImπ h (kernel.condition _))

@[reassoc (attr := simp)] theorem eigenImπ_desc [Mono (cartierDualToBidual G)] (φ : F ⟶ G)
    (h : ∀ a, act ρ a ≫ φ = σ a • φ) : eigenImπ ρ σ ≫ eigenImDesc φ h = φ :=
  Abelian.comp_epiDesc _ _ _

variable {ρ' : O →+* End G} (σ)

variable (ρ)

variable {ρ σ}

theorem isIso_eigenπ_of_actsThrough (h : ActsThrough ρ σ) : IsIso (eigenπ ρ σ) :=
  ⟨eigenDesc (𝟙 F) fun a => by rw [Category.comp_id, h a, smulHom_eq_smul_id],
    eigenπ_desc _ _ _ _, by rw [← cancel_epi (eigenπ ρ σ)]; simp⟩

theorem isIso_eigenImπ_of_actsThrough [Mono (cartierDualToBidual F)] (h : ActsThrough ρ σ) :
    IsIso (eigenImπ ρ σ) :=
  ⟨eigenImDesc (𝟙 F) fun a => by rw [Category.comp_id, h a, smulHom_eq_smul_id],
    eigenImπ_desc _ _, by rw [← cancel_epi (eigenImπ ρ σ)]; simp⟩

theorem isZero_eigenIm_of_actsThrough {τ : O →+* Γ(X, ⊤)} (h : ActsThrough ρ τ) {a : O}
    (ha : IsRegularFn (τ a - σ a)) : IsZero (eigenIm ρ σ) := by
  refine IsZero.of_epi_eq_zero (eigenImπ ρ σ) (ha.hom_eq_zero ?_)
  rw [sub_smul, ← act_eigenImπ, h a, smulHom_comp]
  exact sub_self _

end Im

section Proj

variable (ρ : O →+* End F) (σ : O →+* Γ(X, ⊤))

structure IsEigenProj (ε : F ⟶ F) (D : Γ(X, ⊤)) : Prop where

  act_comp : ∀ a, act ρ a ≫ ε = σ a • ε

  exists_sum : ∃ (n : ℕ) (c : Fin n → Γ(X, ⊤)) (b : Fin n → O),
    ε = ∑ i, c i • act ρ (b i) ∧ D = ∑ i, c i * σ (b i)

variable {ρ σ}

namespace IsEigenProj

variable {ε : F ⟶ F} {D : Γ(X, ⊤)} (h : IsEigenProj ρ σ ε D)
include h

theorem comp_eq_smul {φ : F ⟶ G} (hφ : ∀ a, act ρ a ≫ φ = σ a • φ) : ε ≫ φ = D • φ := by
  obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
  simp only [Preadditive.sum_comp, Linear.smul_comp, hφ, Finset.sum_smul, mul_smul]

theorem isEquivariant : IsEquivariant ρ ρ ε := fun a => by
  obtain ⟨n, c, b, rfl, -⟩ := h.exists_sum
  have e (x : O) : act ρ a ≫ act ρ x = act ρ x ≫ act ρ a :=
    congrArg End.asHom ((map_mul ρ x a).symm.trans
      ((congrArg ρ (mul_comm x a)).trans (map_mul ρ a x)))
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp, e]

theorem comp_act (a : O) : ε ≫ act ρ a = σ a • ε := (h.isEquivariant a).symm.trans (h.act_comp a)

theorem dual : IsEigenProj (dualAct ρ) σ (dualMap ε) D := by
  constructor
  · intro a
    rw [act_dualAct, ← dualMap_comp, h.comp_act, dualMap_smul]
  · obtain ⟨n, c, b, rfl, e⟩ := h.exists_sum
    refine ⟨n, c, b, (map_sum (AddMonoidHom.mk' (fun φ : F ⟶ F => dualMap φ) dualMap_add) _ _).trans
      (Finset.sum_congr rfl fun i _ => dualMap_smul _ _), e⟩

theorem pullback (f : Y ⟶ X) : IsEigenProj (pullAct ρ f) (f.appTop.hom.comp σ)
    ((Scheme.Modules.pullback f).map ε) (f.appTop D) := by
  constructor
  · intro a
    rw [act_pullAct, ← Functor.map_comp, h.act_comp, pullback_map_smul]
    rfl
  · obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
    refine ⟨n, fun i => f.appTop (c i), b, ?_, by simp⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Functor.map_sum]
    exact Finset.sum_congr rfl fun i _ => pullback_map_smul _ _ _

theorem of_iso {ρ' : O →+* End G} {φ : F ≅ G} (hφ : IsEquivariant ρ ρ' φ.hom) :
    IsEigenProj ρ' σ (φ.inv ≫ ε ≫ φ.hom) D := by
  constructor
  · intro a
    rw [reassoc_of% isEquivariant_inv hφ a, reassoc_of% h.act_comp a, Linear.smul_comp,
      Linear.comp_smul]
  · obtain ⟨n, c, b, rfl, e⟩ := h.exists_sum
    refine ⟨n, c, b, ?_, e⟩
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp,
      hφ _, Iso.inv_hom_id_assoc]

theorem comp_eigenImπ_eq_zero (hD : IsRegularFn D) {k : G ⟶ F} (hk : k ≫ ε = 0) :
    k ≫ eigenImπ ρ σ = 0 :=
  hD.hom_eq_zero (by
    rw [← Linear.comp_smul, ← h.comp_eq_smul (act_eigenImπ ρ σ), reassoc_of% hk, zero_comp])

variable [Mono (cartierDualToBidual F)]

variable (hD : IsRegularFn D)
include hD

omit hD

variable (f : Y ⟶ X) (hf : IsRegularFn (f.appTop D))

variable [Mono (cartierDualToBidual ((Scheme.Modules.pullback f).obj F))]

end IsEigenProj

end Proj

section Examples₂

open Polynomial

variable (F G)

def twoAct : ℤ[X] →+* End (F ⊞ G) :=
  eval₂RingHom' (Int.castRingHom _) (End.of (2 • (biprod.snd ≫ biprod.inr)))
    fun n => Int.cast_commute n _


variable (X) in
def zeroChar : ℤ[X] →+* Γ(X, ⊤) := (Int.castRingHom _).comp constantCoeff

theorem act_twoAct_X : act (twoAct F G) Polynomial.X = 2 • (biprod.snd ≫ biprod.inr) :=
  congrArg End.asHom (eval₂_X (S := End (F ⊞ G)) _ _)


variable {F G} in
theorem act_comp_of_X {ρ : ℤ[X] →+* End F} {φ : F ⟶ G} (h : act ρ Polynomial.X ≫ φ = 0)
    (a : ℤ[X]) : act ρ a ≫ φ = zeroChar X a • φ := by
  have e : act ρ a = act ρ a.divX ≫ act ρ Polynomial.X + smulHom F (zeroChar X a) := by
    change (ρ a).asHom = _
    conv_lhs => rw [← X_mul_divX_add a, map_add (f := ρ), map_mul]
    change act ρ a.divX ≫ act ρ Polynomial.X + act ρ (C (a.coeff 0)) = _
    exact congrArg (fun e : End F => act ρ a.divX ≫ act ρ Polynomial.X + e.asHom)
      congr($(RingHom.ext_int (ρ.comp C) (scalarAct F (Int.castRingHom _))) (a.coeff 0))
  rw [e, Preadditive.add_comp, Category.assoc, h, Limits.comp_zero, zero_add, smulHom_comp]
  rfl

theorem isEigenProj_twoAct :
    IsEigenProj (twoAct F G) (zeroChar X) (2 • (biprod.fst ≫ biprod.inl)) 2 := by
  constructor
  · exact act_comp_of_X (by simp [act_twoAct_X])
  · refine ⟨2, ![2, -1], ![1, Polynomial.X], ?_, by simp [zeroChar]⟩
    have e : act (twoAct F G) 1 = 𝟙 _ := congrArg End.asHom (map_one (twoAct F G))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, act_twoAct_X, e,
      two_smul, neg_smul, one_smul, ← biprod.total]
    abel

def eigenImTwoIso [Mono (cartierDualToBidual F)] (h : IsRegularFn (2 : Γ(X, ⊤))) :
    eigenIm (twoAct F G) (zeroChar X) ≅ F where
  hom := eigenImDesc biprod.fst (act_comp_of_X (by simp [act_twoAct_X]))
  inv := biprod.inl ≫ eigenImπ _ _
  hom_inv_id := by
    have := (isEigenProj_twoAct F G).comp_eigenImπ_eq_zero h (k := biprod.inr) (by simp)
    rw [← cancel_epi (eigenImπ _ _), eigenImπ_desc_assoc, Category.comp_id]
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [this]
  inv_hom_id := by simp

theorem actsThrough_pull_twoAct (f : Y ⟶ X) (hY : (2 : Γ(Y, ⊤)) = 0) :
    ActsThrough (pullAct (twoAct F G) f) (f.appTop.hom.comp (zeroChar X)) := fun a => by
  have := act_comp_of_X (ρ := pullAct (twoAct F G) f) (φ := 𝟙 _) (by
    rw [act_pullAct, act_twoAct_X, Functor.map_nsmul, Category.comp_id,
      ← Nat.cast_smul_eq_nsmul Γ(Y, ⊤), Nat.cast_ofNat, hY, zero_smul]) a
  rw [Category.comp_id] at this
  rw [this, smulHom_eq_smul_id]
  simp [zeroChar]


variable {F G} in
theorem not_isIso_quotToIm_twoAct {r s : ℕ} (hF : IsVB F r) (hG : IsVB G (s + 1))
    (h : IsRegularFn (2 : Γ(X, ⊤))) (f : Y ⟶ X) [Nonempty Y] (hY : (2 : Γ(Y, ⊤)) = 0) :
    ¬IsIso (quotToIm (twoAct F G) (zeroChar X)) := fun _ => by
  have := mono_toBidual_of_isVectorBundle hF
  have := isIso_eigenπ_of_actsThrough (actsThrough_pull_twoAct F G f hY)
  have h₁ := ((hF.of_iso (asIso (quotToIm _ _) ≪≫ eigenImTwoIso F G h).symm).pullback f).of_iso
    (asIso (eigenπ _ _) ≪≫ pullbackQuotIso _ _ f).symm
  have := h₁.rank_unique ((hF.biprod hG).pullback f)
  omega

end Examples₂

end GlobalTheory.LieVB
