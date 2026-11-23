module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QkPullEquiv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.TorusExt

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem weilQkIs_of_pull (hG : GlobalFnsSt) (hF : Compat φ F) {k : ℕ} {p q : QkPt D F k} {p' q' : QkPt D' F k}
    (hp : p'.y = hD.xe.symm p.y) (hpg : IsPullGtF φ hD F p.g p'.g) (hq : q'.y = hD.xe.symm q.y)
    (hqg : IsPullGtF φ hD F q.g q'.g) {ζ : F} (H : WeilQkIs D' F k p' q' ζ) : WeilQkIs D F k p q ζ := by
  intro w v hw hv s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ β
  obtain ⟨α, rfl⟩ := hD.xe.surjective β
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w', hw', tw⟩ := phiRel_transport hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k p p' hp hpg w hw
  obtain ⟨v', hv', tv⟩ := phiRel_transport hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k q q' hq hqg v hv
  choose dn hdn using exists_fam_field_pull hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k
  have e := (isSmul_iff _ _ _).1 (H w' v' hw' hv' _ _ _ _ _ (tv _ _ _ _ (hdn s) (hdn s₁) r₁)
    (tw _ _ _ _ (hdn s₁) (hdn s₂) r₂) (tw _ _ _ _ (hdn s) (hdn s₃) r₃) (tv _ _ _ _ (hdn s₃) (hdn s₄) r₄))
  refine sec_ext_val D.P.isLB (s := s₂.s (hD.xe α)) (s' := (ζ • s₄).s (hD.xe α)) fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
  have a := FamFieldPull.IsSecPull.val (hdn s₂ α) (hκ.fam α) κ' y hJ hJ'
  have b := FamFieldPull.IsSecPull.val (hdn s₄ α) (hκ.fam α) κ' y hJ hJ'
  have c : κ' ≫ (fst (TF (R := R') F) D'.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left := by
    rw [← hκ.fst, ← Category.assoc, hκ.inv_hom]
  rw [hκ.inv_hom] at a b
  rw [e, sval_smul _ _ _ _ y hJ', c, mul_left_comm, ← b] at a
  rw [sval_smul _ _ _ _ y hJ]
  exact a

variable (hG : GlobalFnsSt) (hF : Compat φ F) (hB : D.TauBimult) (hB' : D'.TauBimult) {k : ℕ}

theorem pullQk_injective : Function.Injective (pullQk hD hG hF hB hB' (k := k)) := fun _ _ h =>
  qk_ext (hD.xe.symm.injective (congrArg QkPt.y h)) (pullGt_injective hD hG hF (congrArg QkPt.g h))

theorem qkAdd_pullQk_iff (p q r : QkPt D F k) : QkAdd p q r ↔
    QkAdd (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) (pullQk hD hG hF hB hB' r) :=
  ⟨qkAdd_pullQk hD hG hF hB hB', fun h => (qkAdd_iff hB _ _ _).2 ((equiv_pullQk hD hG hF hB hB' _ _).1
    ((qkAdd_iff_of_equiv hB' (qk_equiv_refl hB' _) (qk_equiv_refl hB' _)
      (qkAdd_pullQk hD hG hF hB hB' (qkAdd_qkAdd hB p q))).1 h))⟩

theorem weilQkIs_pullQk_iff (p q : QkPt D F k) (z : F) : WeilQkIs D F k p q z ↔
    WeilQkIs D' F k (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) z := by
  obtain ⟨a₁, a₂⟩ := (eq_pullQk_iff hD hG hF hB hB' p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (eq_pullQk_iff hD hG hF hB hB' q _).1 rfl
  exact ⟨weilQkIs_pull hD hF a₁ a₂ b₁ b₂, weilQkIs_of_pull hD hG hF a₁ a₂ b₁ b₂⟩

theorem comm_proj {f' : D'.P.A ⟶ D'.P.A} {f : D.P.A ⟶ D.P.A}
    (h : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f) :
    f'.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ f.left := by
  have e : f'.left ≫ hD.e.hom.left = hD.e.hom.left ≫ ((Over.pullback (specOf φ)).map f).left :=
    congrArg (fun q => q.left) h
  have g : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) g).trans (Category.assoc _ _ _).symm)))

theorem qkAct_pullQk_iff {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] {o : D.OAct O}
    {o' : D'.OAct O} (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y)
    (ho : ∀ a, (o'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (o.onB.act a).left) (a : O)
    (p q : QkPt D F k) : QkAct o a p q ↔ QkAct o' a (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) :=
  ⟨qkAct_pullQk hD hG hF hB hB' hx ho, fun h => (qkAct_iff hB hG o _ _ _).2
    ((equiv_pullQk hD hG hF hB hB' _ _).1 ((qkAct_iff_of_equiv hB' hG o' (qk_equiv_refl hB' _)
      (qkAct_pullQk hD hG hF hB hB' hx ho (qkAct_qkSmul hB hG o a p))).1 h))⟩

theorem exists_equiv_pullQk : ∃ τ : QkPt D F k ≃ QkPt D' F k, ⇑τ = pullQk hD hG hF hB hB' :=
  ⟨Equiv.ofBijective _ ⟨pullQk_injective hD hG hF hB hB', pullQk_surjective hD hG hF hB hB'⟩, rfl⟩

end GlobalTheory.QkPullEquiv

namespace GlobalTheory


open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkPullEquiv in
theorem exists_qk_pull_equiv : Laws → Laws2 → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ k : ℕ, ∃ τ : QkPt D F k ≃ QkPt D' F k, (∀ p p', τ p = p' ↔ p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g) ∧ (∀ p q, QkPt.Equiv D F p q ↔ QkPt.Equiv D' F (τ p) (τ q)) ∧ (∀ p q r, QkAdd p q r ↔ QkAdd (τ p) (τ q) (τ r)) ∧ (∀ p q z, WeilQkIs D F k p q z ↔ WeilQkIs D' F k (τ p) (τ q) z) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (o : D.OAct O) (o' : D'.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ a, o'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (o.onB.act a)) → ∀ a p q, QkAct o a p q ↔ QkAct o' a (τ p) (τ q) := by
  intro hL _ R R' _ _ _ _ φ D D' hD hB hB' F _ _ _ hF k
  have hG := hL.globalFns
  obtain ⟨τ, hτ⟩ := exists_equiv_pullQk hD hG hF hB hB' (k := k)
  refine ⟨τ, ?_⟩
  rw [hτ]
  exact ⟨fun p p' => eq_comm.trans (eq_pullQk_iff hD hG hF hB hB' p p'),
    fun p q => (equiv_pullQk hD hG hF hB hB' p q).symm, qkAdd_pullQk_iff hD hG hF hB hB',
    weilQkIs_pullQk_iff hD hG hF hB hB',
    fun O _ _ _ _ o o' hx ho => qkAct_pullQk_iff hD hG hF hB hB' hx fun a => comm_proj hD (ho a)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialFibreProjectionAbelianPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialPoints

theorem exists_torsion_lift {T M N : Type} [CommGroup T] [CommGroup M] [Group N] (i : T →* M) (q : M →* N) (n : ℕ)
    (hqi : ∀ t, q (i t) = 1) (hker : ∀ x, q x = 1 → ∃ t, i t = x) (hq : Function.Surjective q)
    (hT : ∀ t : T, ∃ s : T, s ^ n = t) (b : N) (hb : b ^ n = 1) : ∃ x, x ^ n = 1 ∧ q x = b := by
  obtain ⟨x, rfl⟩ := hq b
  obtain ⟨t, ht⟩ := hker (x ^ n) (by rw [map_pow, hb])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨x * (i s)⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← map_pow, ht, mul_inv_cancel]
  · rw [map_mul, map_inv, hqi, inv_one, _root_.mul_one]

theorem exists_projection :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∃ π : (Over.mk (spMap f) ⟶ G) →* (Over.mk (spMap f) ⟶ D.P.A), (∀ x, ∃ y : Sp κ ⟶ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, y ≫ (fstG (IsLocalRing.maximalIdeal V) 0 G).left = x.left ∧ y ≫ g.pG.left = (π x).left) ∧ ∀ n : ℕ, 1 ≤ n → ∀ b, b ^ n = 1 → ∃ x, x ^ n = 1 ∧ π x = b := by
  intro V _ _ _ D G _ _ _ c K _ _ f hf
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Sp K ⟶ Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)),
      r₀ ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap f := by
    have h₂ : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), f a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      by_contra h
      exact ha (hf.map_nonunit a (Ne.isUnit h))
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ f h₂)), ?_⟩
    rw [← Spec.map_comp]
    rfl
  have := c.q_hom
  have := c.i_hom
  have := c.q_surj
  have hk := c.isKernel
  let T : Over (Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) := Over.mk r₀
  let eG := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) G T _ hr₀
  let eB := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) D.P.A T _ hr₀
  let q := IsMonHom.monoidHom c.q T
  let i := IsMonHom.monoidHom c.i T
  let e := splitTorusPointsEquiv _ D.X T
  have hqi : ∀ t, q (i t) = 1 := fun t => by
    change (t ≫ c.i) ≫ c.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, comp_toUnit]
    rfl
  have hker : ∀ x, q x = 1 → ∃ t, i t = x := fun x hx =>
    ⟨hk.lift x (toUnit _) (by rw [show x ≫ c.q = 1 from hx, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hq : Function.Surjective q := fun b => by
    have : LocallyOfFiniteType (c.q.left ≫ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom) := by
      rw [Over.w c.q]
      exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)))
    have : LocallyOfFiniteType c.q.left :=
      locallyOfFiniteType_of_comp _ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom
    obtain ⟨x, hx⟩ := GeomSurj.exists_lift_of_surjective c.q.left b.left
    exact ⟨Over.homMk x (by rw [← Over.w c.q, ← Category.assoc, ← hx]; exact Over.w b),
      Over.OverMorphism.ext hx.symm⟩
  refine ⟨eB.toMonoidHom.comp (q.comp eG.symm.toMonoidHom), fun x => ?_, fun n hn b hb => ?_⟩
  · obtain ⟨x, rfl⟩ := eG.surjective x
    refine ⟨x.left, (TorsionLift.ptsEquiv_left _ _ _ _ _ x).symm, ?_⟩
    change _ = (eB (q (eG.symm (eG x)))).left
    rw [eG.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans (TorsionLift.ptsEquiv_left _ _ _ _ _ (q x)).symm
  · obtain ⟨x, hx, hxb⟩ := exists_torsion_lift
      ((i.comp e.symm.toMonoidHom) : (Multiplicative D.X →* Γ(T.left, ⊤)ˣ) →* _) q n
      (fun t => hqi _) (fun x hx => by
        obtain ⟨t, ht⟩ := hker x hx
        exact ⟨e t, (congrArg i (e.symm_apply_apply t)).trans ht⟩) hq
      (TorsLift.exists_pow_eq_hom (M := Γ(T.left, ⊤)ˣ) n (TorsLift.exists_pow_eq_unit K n hn))
      (eB.symm b) (by rw [← map_pow, hb, map_one])
    refine ⟨eG x, by rw [← map_pow, hx, map_one], ?_⟩
    change eB (q (eG.symm (eG x))) = b
    rw [eG.symm_apply_apply, hxb, eB.apply_symm_apply]

end GlobalTheory.SpecialPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftGlobal

open CommPairing GlobalLift

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem exists_symLift_pull_val (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) :
    ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', ⟨e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, v⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q


omit [GrpObj A] in
theorem exists_lift_res {T : Over S} (V : T.left.Opens) {Z : Scheme.{0}} (ρ : Z ⟶ (T ⊗ A).left)
    (hρ : ∀ z, (fst T A).left (ρ z) ∈ V) :
    ∃ n : Z ⟶ (overRes V ⊗ A).left, n ≫ (overResι V ▷ A).left = ρ := by
  obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = ρ ≫ (fst T A).left :=
    ⟨IsOpenImmersion.lift V.ι (ρ ≫ (fst T A).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hρ y), IsOpenImmersion.lift_fac _ _ _⟩
  let ρ' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ T ⊗ A := Over.homMk ρ rfl
  let v' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ overRes V := Over.homMk v (by
    show v ≫ V.ι ≫ T.hom = ρ ≫ (T ⊗ A).hom
    rw [← Category.assoc, hv, Category.assoc, Over.w (fst T A)])
  have e : v' ≫ overResι V = ρ' ≫ fst T A := Over.OverMorphism.ext hv
  have e' : lift v' (ρ' ≫ snd T A) ≫ overResι V ▷ A = ρ' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, e]
    · rw [Category.assoc, whiskerRight_snd, lift_snd]
  exact ⟨(lift v' (ρ' ≫ snd T A)).left, congrArg (fun q => q.left) e'⟩

omit [GrpObj A] in
theorem mono_res {T : Over S} (V : T.left.Opens) : Mono (overResι V ▷ A).left := by
  have : Mono (overResι V).left := inferInstanceAs (Mono V.ι)
  have : Mono (overResι V) := Over.mono_of_mono_left _
  have : Mono (overResι V ▷ A) := ⟨fun a b e => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← cancel_mono (overResι V), Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, e,
        Category.assoc]
    · rw [← whiskerRight_snd (overResι V), ← Category.assoc, e, Category.assoc]⟩
  infer_instance

theorem tval_agree (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {T : Over S}
    {x : T ⟶ A} {V V' : T.left.Opens} {θ : ThetaGrp A L k (overRes V)} {θ' : ThetaGrp A L k (overRes V')}
    (H : SymLift A L k n (overResι V ≫ x) θ) (H' : SymLift A L k n (overResι V' ≫ x) θ')
    {Z : Scheme.{0}} (r : Z ⟶ (overRes V ⊗ A).left) (r' : Z ⟶ (overRes V' ⊗ A).left)
    (hr : r ≫ (overResι V ▷ A).left = r' ≫ (overResι V' ▷ A).left) (z : Z) (J) (hJ : Good L z J) :
    tval θ r z J = tval θ' r' z J := by
  have mem : ∀ (W : T.left.Opens) (s : Z ⟶ (overRes W ⊗ A).left) (y : Z),
      (fst T A).left ((s ≫ (overResι W ▷ A).left) y) ∈ W := fun W s y => by
    have e : (overResι W ▷ A).left ≫ (fst T A).left = (fst (overRes W) A).left ≫ W.ι := by
      rw [← Over.comp_left, whiskerRight_fst]; rfl
    exact (congrArg (fun q => q (s y) ∈ W) e).mpr ((fst (overRes W) A).left (s y)).2
  obtain ⟨m, hm⟩ := exists_lift_res (V ⊓ V') (r ≫ (overResι V ▷ A).left)
    (fun y => ⟨mem V r y, hr ▸ mem V' r' y⟩)
  have inc : ∀ (W : T.left.Opens), V ⊓ V' ≤ W → ∃ i : overRes (V ⊓ V') ⟶ overRes W,
      i ≫ overResι W = overResι (V ⊓ V') := fun W hW =>
    ⟨Over.homMk (T.left.homOfLE hW) (by
      show T.left.homOfLE hW ≫ W.ι ≫ T.hom = (V ⊓ V').ι ≫ T.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]), Over.OverMorphism.ext (T.left.homOfLE_ι hW)⟩
  obtain ⟨i, hi⟩ := inc V inf_le_left
  obtain ⟨i', hi'⟩ := inc V' inf_le_right
  obtain ⟨ξ, Hξ, vξ⟩ := exists_symLift_pull_val hL i H
  obtain ⟨ξ', Hξ', vξ'⟩ := exists_symLift_pull_val hL i' H'
  rw [← Category.assoc, hi] at Hξ
  rw [← Category.assoc, hi'] at Hξ'
  have := mono_res (A := A) V
  have := mono_res (A := A) V'
  have e : m ≫ (i ▷ A).left = r := by
    rw [← cancel_mono (overResι V ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, hm]
  have e' : m ≫ (i' ▷ A).left = r' := by
    rw [← cancel_mono (overResι V' ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi', hm, hr]
  rw [← e, ← e', ← vξ _ _ z J hJ, ← vξ' _ _ z J hJ]
  exact val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn ξ ξ' Hξ Hξ') m

theorem exists_lift_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {T : Over S} {x : T ⟶ A}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L k (overRes V), SymLift A L k n (overResι V ≫ x) θ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  choose V hV θ hθ using h
  choose m hm using fun p => exists_lift_res (A := A) (V p) ((fst T A).left ⁻¹ᵁ V p).ι (fun z => z.2)
  have loc : ∀ p, ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
      (fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) ![k, -k]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((fst T A).left ⁻¹ᵁ V p).toScheme) (z : Z) (J), Good L z J →
        val t r z J = tval (θ p) (r ≫ m p) z J := fun p => by
    have e₀ : m p ≫ (snd (overRes (V p)) A).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (snd T A).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have e₁ : m p ≫ (translPt A (θ p).pt).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (translPt A x).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whisker_translPt, (hθ p).pt_eq]
    obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := Fin 2)
      (φ' := fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) (ε' := ![k, -k])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ k) e₀
        · exact congrArg (fun q => f q ^ (-k)) e₁)
      (LB.pullGen L ![(snd (overRes (V p)) A).left, (translPt A (θ p).pt).left] ![k, -k] (θ p).φ (m p))
      (DVR.pullGen_isGen _ _ _ _ (θ p).isGen _)
    exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩
  choose t ht hv using loc
  obtain ⟨u, hu, -⟩ := glue_gen hL (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]
    (fun p => (fst T A).left ⁻¹ᵁ V p) (fun y => ⟨(fst T A).left y, hV _⟩) t ht
    (fun p q Z r r' z J hJ e => by
      rw [hv p Z r z J hJ, hv q Z r' z J hJ]
      exact tval_agree hG hA hL hn (hθ p) (hθ q) _ _ (by rw [Category.assoc, Category.assoc, hm, hm, e]) z J hJ)
  exact ⟨⟨x, u, hu⟩, rfl⟩

end GlobalTheory.SymLiftGlobal

namespace GlobalTheory

theorem exists_symLift_global : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k →
    IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  intro hLaw S _ P k hk hu T x hx
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local hLaw.globalFns P.isAb P.isLB hk
    (hLaw.symLift S P k hk hu T x hx).1
  obtain ⟨nu, hnu⟩ := exists_gen_negLB hLaw.globalFns S P k T
  exact SymLiftOdd.exists_symLift hLaw.globalFns P.isAb P.isLB hk hx θ hθ hnu

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionLiftSpecialFibreOfGenericRational
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem epi_spMap_of_finite_of_injective (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W]
    (hinj : Function.Injective (algebraMap V W)) : Epi (spMap (algebraMap V W)) := by
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have hfl : Module.Flat V W := inferInstance
  have : Flat (spMap (algebraMap V W)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 hfl
  have : Surjective (spMap (algebraMap V W)) :=
    ⟨Algebra.IsIntegral.comap_surjective V W⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_torsion_lift_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  intro hD hU V _ _ _ hV G _ _ _ _ C _ _ ga m hm hrat κ _ _ f hf x hx
  obtain ⟨W, _, _, _, _, _, f', hfin, hinj, hloc, -, hcomp, hy⟩ :=
    exists_finite_extension_torsion_lift hU V G m hm κ f hf {x} (by simpa using hx)
  obtain ⟨y, hy, hy'⟩ := hy x (Finset.mem_singleton_self x)
  let : Algebra V C := (ga.comp (algebraMap V (FractionRing V))).toAlgebra
  have hC : Function.Injective (algebraMap V C) :=
    ga.injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hC
  let β : W →ₐ[V] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hβ : Function.Injective β.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker β.toRingHom) = ⊥
    rw [RingHom.comap_ker]
    refine (RingHom.injective_iff_ker_eq_bot _).1 ?_
    rw [show β.toRingHom.comp (algebraMap V W) = algebraMap V C from β.comp_algebraMap]
    exact hC
  have hβα : β.toRingHom.comp (algebraMap V W) = ga.comp (algebraMap V (FractionRing V)) :=
    β.comp_algebraMap
  have hw : spMap β.toRingHom ≫ spMap (algebraMap V W) = spMap ga ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hβα]
  let j : Over.mk (spMap ga ≫ jK V) ⟶ Over.mk (spMap (algebraMap V W)) :=
    Over.homMk (spMap β.toRingHom) hw
  obtain ⟨x₀, hx₀⟩ := hrat (j ≫ y) (by rw [← comp_pow, hy, comp_one])
  obtain ⟨h₀, hh₀, -⟩ := hD V W C (algebraMap V W) β.toRingHom ga hloc hβ hβα G.left y.left x₀
    hx₀.symm
  have hepi := epi_spMap_of_finite_of_injective V W hinj
  let h : baseOver (Sp V) ⟶ G := Over.homMk h₀ (by
    rw [← cancel_epi (spMap (algebraMap V W))]
    exact ((reassoc_of% hh₀) _).trans ((Over.w y).trans (Category.comp_id _).symm))
  let a : Over.mk (spMap (algebraMap V W)) ⟶ baseOver (Sp V) :=
    Over.homMk (spMap (algebraMap V W)) (Category.comp_id _)
  have ha : a ≫ h = y := Over.OverMorphism.ext hh₀
  have : Epi a.left := hepi
  have : Epi a := Over.epi_of_epi_left a
  refine ⟨h, ?_, ?_⟩
  · rw [← cancel_epi a, comp_pow, ha, hy, comp_one]
  · rw [← hy', ← hh₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def HasWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gs ((τ ≫ i) * g).left z U f = (gm τ.left z ⊤ (charUnit S X α)).val * gs g.left z U f

def GenWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    {Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J : (Z.left ⟶ Y) → L.ι), Good L z J →
    val t ((τ ≫ i) * g).left z J = gm τ.left z ⊤ (charUnit S X α) * val t g.left z J

def Red {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) {K K' : Type} [Fintype K] [Fintype K'] {ψ : K → (Φ.E.B.left ⟶ Y)} {ε : K → ℤ}
    {φt : K' → (Φ.G.left ⟶ Y)} {εt : K' → ℤ} (t : LB.Gen (LB.LinComb L φt εt)) (b : LB.Sec (LB.LinComb L ψ ε))
    (φ : (Φ.H 1).Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
    r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
    gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval b (r ≫ Φ.D.q.left) z J * (val t r z J).val

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_model_labelled_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  first | exact @GlobalTheory.ZH.utest_torsion_points | exact GlobalTheory.ZH.utest_torsion_points | (intros; apply GlobalTheory.ZH.utest_torsion_points <;> assumption)
end

