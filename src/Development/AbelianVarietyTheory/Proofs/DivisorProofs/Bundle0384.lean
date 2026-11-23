module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrank
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem adjoin_gen_eq_top {k F : Type} [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hm : (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) = k⟮x⟯ := by
    rw [IntermediateField.adjoin_map]; simp
  have hy : (y : F) ∈ (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) := by
    rw [hm]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

theorem val_lt_one_of_ord_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (t : F)
    (h : ord v t = 1) : v.1 t < 1 := by
  unfold ord at h
  by_cases h0 : v.1 t = 0
  · rw [h0] at h; simp at h
  · have hl : WithZero.log (v.1 t) < WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      simp; omega
    exact (WithZero.log_lt_log h0 one_ne_zero).1 hl

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem zeros_finite_sum_eq_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧
      ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  intro k F _ _ _ _ _ hF x hx
  haveI : FiniteDimensional k⟮x⟯ F := (_root_.GlobalTheory.Nef.isFF_main k F hF).1 x hx
  set t : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ with ht
  have htx : algebraMap k⟮x⟯ F t = x := rfl
  have htr : Transcendental k t := by
    intro ha
    exact hx ((IntermediateField.isAlgebraic_iff).1 ha)
  have htop : k⟮t⟯ = ⊤ := adjoin_gen_eq_top x
  have hL : IsFF k k⟮x⟯ := by
    refine ⟨t, htr, ?_⟩
    rw [htop]
    have : Module.Free (⊤ : IntermediateField k k⟮x⟯) k⟮x⟯ :=
      Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  obtain ⟨v0, hv0, huniq⟩ := GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator k k⟮x⟯ t htr htop
  obtain ⟨ρ, hρ⟩ := (_root_.GlobalTheory.Nef.place_res_exists_pow k k⟮x⟯ F).1
  have ht0 : t ≠ 0 := by
    intro h; apply hx; rw [← htx, h, map_zero]; exact isAlgebraic_zero
  obtain ⟨hfin, hsum⟩ := _root_.GlobalTheory.Nef.FundId.sum_ord_eq_finrank k k⟮x⟯ F hL ρ hρ v0 t ht0 hv0
  have hset : {v : Place k F | v.1 x < 1} = {p | ρ p = v0} := by
    ext p
    obtain ⟨e, he, hpow, -⟩ := (_root_.GlobalTheory.Nef.place_res_exists_pow k k⟮x⟯ F).2 ρ hρ p
    simp only [Set.mem_setOf_eq]
    change p.1 (algebraMap k⟮x⟯ F t) < 1 ↔ ρ p = v0
    rw [hpow t]
    constructor
    · intro h
      apply huniq
      by_contra hn
      exact absurd h (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
    · intro h
      rw [h]
      exact pow_lt_one₀ zero_le' (val_lt_one_of_ord_eq_one v0 t hv0) he.ne'
  rw [hset]
  exact ⟨hfin, by simpa [htx] using hsum⟩

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionFinitarySheafSectionLocallyConstant
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSmooth

abbrev sr (Ω : Type) [Field Ω] (s : Finset Ω) : Subring Ω := Subring.closure (s : Set Ω)

variable (Ω : Type) [Field Ω]

theorem sr_mono {s t : Finset Ω} (h : s ≤ t) : sr Ω s ≤ sr Ω t :=
  Subring.closure_mono (Finset.coe_subset.2 h)

def incl {s t : Finset Ω} (h : s ≤ t) : CommRingCat.of (sr Ω s) ⟶ CommRingCat.of (sr Ω t) :=
  CommRingCat.ofHom (Subring.inclusion (sr_mono Ω h))

theorem incl_apply {s t : Finset Ω} (h : s ≤ t) (y : sr Ω s) : ((incl Ω h).hom y : Ω) = (y : Ω) := by
  rw [incl, CommRingCat.hom_ofHom, Subring.coe_inclusion]

theorem incl_id (s : Finset Ω) : incl Ω (le_refl s) = 𝟙 _ := by
  ext x; rfl

theorem incl_comp {s t u : Finset Ω} (h : s ≤ t) (h' : t ≤ u) : incl Ω (h.trans h') = incl Ω h ≫ incl Ω h' := by
  ext x
  simp only [incl, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Subring.coe_inclusion]

theorem incl_comp_subtype {s t : Finset Ω} (h : s ≤ t) :
    incl Ω h ≫ CommRingCat.ofHom (sr Ω t).subtype = CommRingCat.ofHom (sr Ω s).subtype := by
  ext y
  rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    Subring.coe_subtype, Subring.coe_subtype, incl_apply]

def diag : Finset Ω ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (sr Ω s)
  map {s t} h := incl Ω h.le
  map_id s := incl_id Ω s
  map_comp f g := incl_comp Ω f.le g.le

def cocone : Cocone (diag Ω) where
  pt := CommRingCat.of Ω
  ι := { app := fun s => CommRingCat.ofHom (sr Ω s).subtype
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact incl_comp_subtype Ω h.le }

theorem cocone_ι (s : Finset Ω) : (cocone Ω).ι.app s = CommRingCat.ofHom (sr Ω s).subtype := rfl

theorem cocone_ι_apply (s : Finset Ω) (y : sr Ω s) : ((cocone Ω).ι.app s).hom y = (y : Ω) := rfl

theorem surj (x : Ω) : ∃ (s : Finset Ω) (y : sr Ω s), x = ((cocone Ω).ι.app s).hom y :=
  ⟨{x}, ⟨x, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, (cocone_ι_apply Ω {x} ⟨x, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩).symm⟩

theorem inj [DecidableEq Ω] (i j : Finset Ω) (xi : sr Ω i) (xj : sr Ω j)
    (h : ((cocone Ω).ι.app i).hom xi = ((cocone Ω).ι.app j).hom xj) :
    ∃ (k : Finset Ω) (f : i ⟶ k) (g : j ⟶ k), ((diag Ω).map f).hom xi = ((diag Ω).map g).hom xj := by
  refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, Subtype.ext ?_⟩
  rw [cocone_ι_apply, cocone_ι_apply] at h
  change ((incl Ω (le_sup_left : i ≤ i ⊔ j)).hom xi : Ω) = ((incl Ω (le_sup_right : j ≤ i ⊔ j)).hom xj : Ω)
  rw [incl_apply, incl_apply, h]

def coconeIsColimit [DecidableEq Ω] : IsColimit (cocone Ω) := by
  haveI : ReflectsColimitsOfShape (Finset Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone Ω)) ?_ ?_)
  · intro x
    exact surj Ω x
  · intro i j xi xj h
    exact inj Ω i j xi xj h

end GlobalTheory.EtC.GalSmooth

namespace GlobalTheory.EtC


open GalSmooth in
theorem galois_sec_isLocallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (x : Sec F (Spec (CommRingCat.of Ω))),
      IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω => Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
  intro R _ F hF K Ω _ _ _ _ x
  classical
  obtain ⟨s, y, hy⟩ := (((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).2.1 hF) (Finset Ω) (diag Ω) (cocone Ω)
    (coconeIsColimit Ω)).1 x
  have key : ∀ τ : Ω ≃ₐ[K] Ω, Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
      ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (sr Ω s).subtype))).hom y := by
    intro τ
    rw [← hy, cocone_ι]
    show _ = ((onRings F).map (CommRingCat.ofHom (sr Ω s).subtype ≫ CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
    rw [Functor.map_comp]
    rfl
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ₀
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | τ₀⁻¹ * σ ∈ (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp [one_mem])] with τ hτ
  have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
    have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b (IntermediateField.subset_adjoin K _ hb)
    have h2 := congrArg τ₀ h1
    simpa [AlgEquiv.mul_apply] using h2
  have hc : (τ : Ω →+* Ω).comp (sr Ω s).subtype = (τ₀ : Ω →+* Ω).comp (sr Ω s).subtype := by
    ext a
    exact RingHom.eqOn_set_closure hs a.2
  rw [key τ, key τ₀, hc]

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.PicSpec

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  Eq.symm (NatTrans.naturality_apply φ.hom g.op x)

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (ψ : F ⟶ G) (φ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (Sec.map ψ x) = Sec.map (ψ ≫ φ) x := rfl

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  simpa [Sec.map] using this

theorem res_isZero {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs

theorem resι_d {R : Type} [CommRing R] (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  unfold resι res
  rw [Category.assoc, (injectiveResolution F).ι'.comm 0 1]
  simp

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  have h2 := congrArg (fun f => f.hom (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u))) this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

theorem glMat_map {U V : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) =
      Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem generalLinearGroup_det_map_fin_one {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : GL (Fin 1) A) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f M) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det M) := by
  ext
  simp

theorem glMat_δ1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (((ofCat (glCat 1)).δ 1).app (op U) y) =
      glMat (((ofCat (glCat 1)).δ 0).app (op U) y) * glMat (((ofCat (glCat 1)).δ 2).app (op U) y) := by
  have h : ((show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 2) =
      (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 1 ≫
        (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 1 2 :=
    ComposableArrows.map'_comp _ 0 1 2
  exact h

theorem face_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) (i : Fin 3) :
    (L.app (op (SimplexCategory.mk 1))).app (op U) ((E.δ i).app (op U) x) =
      ((ofCat (glCat 1)).δ i).app (op U) ((L.app (op (SimplexCategory.mk 2))).app (op U) x) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (SimplicialObject.δ_naturality L i) (op U)) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  rw [NatTrans.naturality_apply (L.app (op (SimplexCategory.mk 1))) g.op x, glMat_map, generalLinearGroup_det_map_fin_one]

theorem lineUnit_face {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.face 0) * lineUnit L (x.face 2) := by
  unfold lineUnit Sx.face
  rw [face_nat, face_nat, face_nat, glMat_δ1, map_mul]

def fam {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ Gm).X s) U
  | 1, s, h, _, x => Sec.map ((res ℤ Gm).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
  | _, _, _, _, _ => 0

theorem fam_zero {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0})
    (x : Sx E 0 U) : fam L 0 s h U x = 0 := rfl

theorem fam_add_two {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -((p + 2 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E (p + 2) U) : fam L (p + 2) s h U x = 0 := rfl

theorem fam_one {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : fam L 1 0 h U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  simp [fam, Sec.map]

theorem fam_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0})
    (g : V ⟶ U) (x : Sx E p U) : Sec.res g (fam L p s h U x) = fam L p s h V (x.res g) := by
  match p with
  | 0 => simp [fam_zero]
  | 1 =>
    simp only [fam]
    rw [sec_map_res, sec_map_res, unitSec_res, lineUnit_res]
  | p + 2 => simp [fam_add_two]

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem ev_zero_cochain {E : Spc} {I : Cx ℤ} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (0 : Cochain ((chains ℤ).obj E) I n) p s h U x = 0 := by
  have hZero := CupSpec.ev_zero (I := I) p s h U x
  exact hZero

theorem fam_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains ℤ).obj E) (res ℤ Gm) 1)
    (hα : ∀ p s h U x, ev α p s h U x = fam L p s h U x) : δ 1 2 α = 0 := by
  have hExt := CupSpec.ev_ext (δ 1 2 α) 0
  apply hExt
  intro p t ht U x
  rw [ev_zero_cochain]
  have hDeltaSucc := CupSpec.ev_δ_succ (m := 2) (by norm_num) α U
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    have hDeltaZero := CupSpec.ev_δ_zero (m := 2) (by norm_num) α U 1 2 (by simp) ht x
    rw [hDeltaZero, hα, fam_zero, sec_map_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key : ev (δ 1 2 α) 1 1 ht U x = Sec.map ((res ℤ Gm).d 0 1) (ev α 1 0 (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ev α 0 1 (by simp) U (x.face i) :=
      hDeltaSucc 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, fam_zero, fam_one, smul_zero, Finset.sum_const_zero, add_zero, sec_map_comp, resι_d]
    rfl
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key : ev (δ 1 2 α) 2 0 ht U x = Sec.map ((res ℤ Gm).d (-1) 0) (ev α 2 (-1) (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ev α 1 0 (by simp) U (x.face i) :=
      hDeltaSucc 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, fam_one]
    rw [show fam L 2 (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three, lineUnit_face,
      unitSec_mul, sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  | p + 3 =>
    have key := hDeltaSucc (p + 2) (t - 1) t (by omega) ht x
    rw [key]
    simp only [hα, fam_add_two, sec_map_zero, zero_add, smul_zero, Finset.sum_const_zero]

theorem exists_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  have hExists := GlobalTheory.EtC.exists_cochain_ev_eq_of_natural ℤ (fam L) (fam_nat L)
  obtain ⟨α, hα⟩ := hExists
  refine ⟨Cocycle.mk α 2 (by norm_num) (fam_cocycle L α hα), fun U x => ?_, fun U x => ?_⟩
  · exact (hα 0 1 _ U x).trans (fam_zero L 1 _ U x)
  · exact (hα 1 0 _ U x).trans (fam_one L _ U x)

theorem spec {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = picClass L ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨γ, h0, h1⟩ := exists_cocycle L
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
    ⟨_, γ, rfl, h0, h1⟩

theorem cocycle_ext {E : Spc} (γ γ' : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = ev γ'.1 0 1 (by simp) U x)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = ev γ'.1 1 0 (by simp) U x) : γ = γ' := by
  have hExt := CupSpec.ev_ext γ.1 γ'.1
  refine Cocycle.ext (hExt fun p s h U x => ?_)
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    exact h0 U x
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact h1 U x
  | p + 2 =>
    have hZ := res_isZero Gm s (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.PicSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedBlocksMulInvIntegralUnitDet
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.GlueBlocks

theorem isIntV_det {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {d : ℕ}
    (X : Matrix (Fin d) (Fin d) C) (hX : ∀ a b, IsIntV v (X a b)) : IsIntV v X.det := by
  let A' : Matrix (Fin d) (Fin d) (PTb.intRing v) := Matrix.of fun a b => ⟨X a b, hX a b⟩
  have hA : (PTb.intRing v).subtype.mapMatrix A' = X := by ext a b; rfl
  have : X.det = (PTb.intRing v).subtype A'.det := by
    rw [RingHom.map_det, hA]
  rw [this]
  exact (A'.det).2

theorem glue_mul_glue_inv : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (ι : Type) (lab : Fin d → ι)
    (S : ι → Finset (Fin d)) (x y : ι → Matrix (Fin d) (Fin d) C),
    (∀ i a, a ∈ S i → lab a = i) →
    (∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) → (∀ i a b, y i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) →
    (∀ i a b, IsIntV v (x i a b)) → (∀ i a b, IsIntV v (y i a b)) →
    (∀ i a c, a ∈ S i → c ∈ S i → ∑ b, x i a b * y i b c = if a = c then 1 else 0) →
    (∀ a b, IsIntV v (glue lab S x a b)) ∧ glue lab S x * glue lab S y = 1 ∧
      v (glue lab S x).det = 0 := by
  intro C _ v d ι lab S x y hlab hx hy hxi hyi hinv
  have hint : ∀ z : ι → Matrix (Fin d) (Fin d) C, (∀ i a b, IsIntV v (z i a b)) →
      ∀ a b, IsIntV v (glue lab S z a b) := by
    intro z hz a b
    simp only [glue, Matrix.of_apply]
    split_ifs
    · exact hz _ _ _
    · unfold IsIntV; rw [v.map_one]
    · unfold IsIntV; rw [v.map_zero]; exact le_top
  have hmul : glue lab S x * glue lab S y = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases ha : a ∈ S (lab a)
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c = x (lab a) a b * y (lab a) b c := by
        intro b
        simp only [glue, Matrix.of_apply, if_pos ha]
        by_cases hxb : x (lab a) a b = 0
        · rw [hxb, zero_mul, zero_mul]
        · have hb := (hx _ _ _ hxb).2
          have hl : lab b = lab a := hlab _ _ hb
          rw [if_pos (hl ▸ hb), hl]
      simp_rw [hterm]
      by_cases hc : c ∈ S (lab a)
      · exact hinv _ _ _ ha hc
      · have h0 : ∀ b, y (lab a) b c = 0 := by
          intro b; by_contra hne; exact hc (hy _ _ _ hne).2
        simp only [h0, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl; exact hc ha
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c =
          if a = b then glue lab S y b c else 0 := by
        intro b
        simp only [glue, Matrix.of_apply, if_neg ha]
        split_ifs <;> simp
      simp_rw [hterm]
      rw [Finset.sum_ite_eq Finset.univ a (fun b => glue lab S y b c), if_pos (Finset.mem_univ _)]
      simp only [glue, Matrix.of_apply, if_neg ha]
  refine ⟨hint x hxi, hmul, ?_⟩
  have hd : (glue lab S x).det * (glue lab S y).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have h1 : v (glue lab S x).det + v (glue lab S y).det = 0 := by
    rw [← v.map_mul, hd, v.map_one]
  have hX : (0 : WithTop ℝ) ≤ v (glue lab S x).det := isIntV_det v _ (hint x hxi)
  have hY : (0 : WithTop ℝ) ≤ v (glue lab S y).det := isIntV_det v _ (hint y hyi)
  exact ((add_eq_zero_iff_of_nonneg hX hY).1 h1).1

end GlobalTheory.GlueBlocks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullbackPushforward_functorial : ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n) := by
  first | (exact @GlobalTheory.EtC.ZcFun.main) | (exact GlobalTheory.EtC.ZcFun.main) | (intros; apply GlobalTheory.EtC.ZcFun.main  <;> assumption)
end

