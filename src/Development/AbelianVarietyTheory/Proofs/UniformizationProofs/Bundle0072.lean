module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroup
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_addG : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  intro V _ _ _ _ D A G _ _ U θ
  have := U.semi.smooth
  have := U.semi.separated
  have := U.semi.quasiCompact
  obtain ⟨v, hv⟩ := exists_addSec _ G U.P (𝟙_ _) θ (toUnit _)
  obtain ⟨v', hv'⟩ := exists_sec U.P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left ≫ 𝟙 G.left) (fun _ => (snd G G).left ≫ 𝟙 G.left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))
    (fun U _ h => by simp only [Category.comp_id]) v
  obtain ⟨r, hr, n, a, b, hab⟩ := GlobalTheory.exists_smul_eq_sum_mul_of_isDomain V G.left U.P.L.L U.P.L.isLB G G (Fin 1) (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) v'
  have mv : ∀ s : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ))),
      ∃ σ : U.SecGT (𝟙_ _) 2, ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
        sval σ (lift (toUnit T) x).left z J = sval s x.left z J := fun s => by
    obtain ⟨σ, hσ⟩ := exists_sec U.P.L.isLB (K' := Fin 1) (φ' := fun _ => (snd (𝟙_ _) G).left)
      (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun U _ h => by simp only [Category.comp_id])
      (H1.SectionArithmetic.pullSec s (snd (𝟙_ _) G).left)
    refine ⟨σ, fun T x z J hJ => (hσ _ _ z J hJ).trans ?_⟩
    rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, ← Over.comp_left, lift_snd]
  choose mv hmv using mv
  refine ⟨r, n, fun i => mv (a i), fun i => mv (b i), hr, fun T x y z J hJ => ?_⟩
  have e := hab T.left (lift x y).left z J hJ
  rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd, hv' _ _ z J hJ, hv T x y z J hJ,
    toUnit_unique (lift x y ≫ toUnit _) (toUnit T)] at e
  have g : gs (lift x y).left z ⊤ (scal (G ⊗ G).hom r) = gs (𝟙 _) z ⊤ (scal T.hom r) := by
    have p : ∀ {Z Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of V)) (w : Z),
        gs f w ⊤ (scal q r) = gs (f ≫ q) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) :=
      fun f q w => gs_pull f q w ⊤ trivial _
    rw [p, p, Over.w, Category.id_comp]
  simp only [hmv _ T _ z J hJ]
  rw [e, g, _root_.mul_assoc]

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsProdB
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem prod_famT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by
  have e₁ : famφT D T α 1 = (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (mul_comm (snd T D.P.A) (DVR.cP D (T ⊗ D.P.A) α))
  have e₂ : famφT D T α 2 = (DVR.cP D (T ⊗ D.P.A) α).left := rfl
  have e₃ : famφT D T α 3 = (1 : T ⊗ D.P.A ⟶ D.P.A).left := rfl
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

theorem exists_isProdB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (k l : ℕ) (β ga α : D.X), β + ga = α → ∀ (f : SecBT D T k β) (g : SecBT D T l ga),
    ∃ h : SecBT D T (k + l) α, IsProdB f g h := by
  intro R _ _ D T k l β ga α hα f g
  subst hα
  let a : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ β
  let b : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ ga
  let x : T ⊗ D.P.A ⟶ D.P.A := snd T D.P.A
  have hu := DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b x)).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := famφT D T (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b x h
      have p₂ := prod_famT D T β k h
      have p₃ := prod_famT D T ga l h
      have p₄ := prod_famT D T (β + ga) (k + l) h
      rw [DVR.cPoint_add] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b, x]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b x)).left) hu))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub r hJ a b x).trans ?_)))))
  rw [DVR.comp_cP, DVR.comp_cP]; rfl

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLimitUnit
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.FormalValue

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NormGen

theorem exists_factor {V W : Type} [CommRing V] [CommRing W] (I : Ideal V) (φ : V →+* W) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp W) (σ : Z ⟶ Sp (V ⧸ I ^ (e + 1))) (h : σ ≫ thick V I e = r ≫ spMap φ) :
    ∃ ρ : Z ⟶ Sp (W ⧸ I.map φ ^ (e + 1)), ρ ≫ thick W (I.map φ) e = r := by
  let ψ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  have hr : Z.toSpecΓ ≫ Spec.map ψ = r := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hk : I.map φ ^ (e + 1) ≤ RingHom.ker ψ.hom := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro v hv
    have e₁ : CommRingCat.ofHom φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv ≫ σ.appTop := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, h]
    have e₂ := congrArg (fun q => q.hom v) e₁
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero] at e₂
    exact e₂
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ.hom hk)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← hr]
  rfl

theorem gs_valR {A : Type} [CommRing A] {X Z : Scheme.{0}} (ρ : Z ⟶ Sp A) (y : Sp A ⟶ X) (V : X.Opens)
    (ht : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) (z : Z) :
    gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (valR y V s)) = gs (ρ ≫ y) z V s := by
  rw [valR, dite_eq_left ht, Iso.hom_inv_id_apply, ← gs_pull ρ y z V (ht trivial)]
  exact gs_res ρ z ht trivial _

theorem valR_id {A : Type} [CommRing A] (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR, dite_eq_left (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := by
    exact (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_limit_unit (U : PreU I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.P.A.left)
    (hb : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → xe ≫ (U.gt e).pG.left = r ≫ b)
    {jL : U.P.L.L.ι} {jM : D.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.P.L.L.U jL) (hM : ⊤ ≤ b ⁻¹ᵁ D.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.P.L.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.P.L.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.P.L.U jM) (hb e Z r xe h)).mpr (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (toStkA_map_valR _ _ _ _ (ht _) _).trans (Eq.trans ?_ (toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact U.w_compat e _ (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := exists_unit_limit (I.map φ) _ hc fun e => isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1, map_one,
    map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [valR_id, Category.comp_id] at k
  exact k

theorem one_pG (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left)
    (oe : Z ⟶ (thickObj R I e G).left) (h : oe ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left) :
    oe ≫ (U.gt e).pG.left = r ≫ (1 : T ⟶ D.P.A).left := by
  have hf : ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H],
      eSec (thickObj R I e H) ≫ (fstG I e H).left = thick R I e ≫ eSec H := fun H _ => by
    show eSec (thickObj R I e H) ≫ pullback.fst H.hom (thick R I e) = _
    simp [eSec]
  have hp : eSec (thickObj R I e G) ≫ (U.gt e).pG.left = thick R I e ≫ eSec D.P.A := by
    have := (U.gt e).q_hom
    have h : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.P.A) :=
      congrArg (·.left) (IsMonHom.one_hom (U.gt e).q)
    rw [← hf D.P.A, ← h, Category.assoc]
    rfl
  have hσ : (oe ≫ (thickObj R I e G).hom) ≫ thick R I e = r ≫ T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (oe ≫ ·) pullback.condition.symm
  have := fstG_mono (I := I) (G := G) e
  have ho : oe = (oe ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc _ (eSec _), hf, ← Category.assoc _ (thick R I e), hσ,
      one_left, Category.assoc]
  rw [ho, Category.assoc _ (eSec _), hp, ← Category.assoc _ (thick R I e), hσ, one_left, Category.assoc]

theorem gw_change (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.P.A.left} (hp : xe ≫ (fstG I e G).left = p) (hq : xe ≫ (U.gt e).pG.left = q)
    {j j' : D.P.L.ι} {k k' : U.P.L.L.ι} (hj : q z ∈ D.P.L.U j) (hj' : q z ∈ D.P.L.U j') (hk : p z ∈ U.P.L.L.U k)
    (hk' : p z ∈ U.P.L.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.P.L.g j j') * (gm p z _ (U.P.L.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_normAt : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∃ ν, U.NormAt x ν := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW a x hx
  have := hW.2.2.2.2
  obtain ⟨jx, hjx⟩ := exists_chart U.P.L.isLB (x.left (cpt W))
  obtain ⟨jo, hjo⟩ := exists_chart U.P.L.isLB ((1 : TA V W ⟶ G).left (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.P.isLB ((1 : TA V W ⟶ D.P.A).left (cpt W))
  replace hjx := (top_le_iff_cpt (A := W) x.left _).2 hjx
  replace hjo := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ G).left _).2 hjo
  replace hjM := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ D.P.A).left _).2 hjM
  obtain ⟨α, hα⟩ := exists_limit_unit U (algebraMap V W) x.left (Over.w x) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => (hx e Z r xe h).1) hjx hjM
  obtain ⟨β, hβ⟩ := exists_limit_unit U (algebraMap V W) (1 : TA V W ⟶ G).left (Over.w _) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => one_pG U (T := TA V W) e Z r xe h) hjo hjM
  obtain ⟨ν, hν⟩ := exists_gen_of_local (V := W) U.P.L.L U.P.L.isLB (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![-1, 1]
  have ht : ⊤ ≤ LB.wchart U.P.L.L (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![jx, jo] := fun y _ =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hjx trivial, hjo trivial]
  obtain ⟨n, hn⟩ : ∃ n : Γ(Sp W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JG), Good U.P.L.L z JG →
      val ν r z JG = (gm (r ≫ x.left) z _ (U.P.L.L.g (JG (r ≫ x.left)) jx))⁻¹ *
        gm (r ≫ (1 : TA V W ⟶ G).left) z _ (U.P.L.L.g (JG (r ≫ (1 : TA V W ⟶ G).left)) jo) * gm r z ⊤ n := by
    refine ⟨res (X := Sp W) ht (ν.s ![jx, jo]), fun Z r z JG hG => ?_⟩
    refine (gen_trans hν r z (hG.mem _ r) (ht trivial)).trans (congrArg₂ (· * ·) ?_ (gm_res r z ht trivial _).symm)
    rw [trF, Fin.prod_univ_two]
    exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
  refine ⟨UU.scaleGen (β * α⁻¹ * n⁻¹ : Γ(Sp W, ⊤)ˣ) ν, UU.scaleGen_isGen _ hν,
    fun e Z (r : Z ⟶ Sp W) xe oe h₁ h₂ z JG J hG hJ => ?_⟩
  have q₁ := (hx e Z r xe h₁).1
  have q₂ := one_pG U (T := TA V W) e Z r oe h₂
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h => h trivial
  have a₁ := eq_inv_of_mul_eq_one_right (hα e Z r xe h₁ z)
  have a₂ := eq_inv_of_mul_eq_one_right (hβ e Z r oe h₂ z)
  have w₁ : U.wv e xe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) xe z (J j) (fun _ => JG k)) q₁ h₁).trans
    (gw_change U e xe z h₁ q₁ (hJ _) (m hjM) (hG _) (m hjx))
  have w₂ : U.wv e oe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) oe z (J j) (fun _ => JG k)) q₂ h₂).trans
    (gw_change U e oe z h₂ q₂ (hJ _) (m hjM) (hG _) (m hjo))
  rw [a₁] at w₁
  rw [a₂] at w₂
  have v := val_scaleGen (β * α⁻¹ * n⁻¹) ν r hG
  rw [hn Z r z JG hG, map_mul, map_mul, map_inv, map_inv] at v
  refine (congrArg₂ (· * ·) v w₂).trans (Eq.trans ?_ w₁.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.NormGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullSecSval
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pullSec_sval {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans
    (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)

theorem whisker_famφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (α : D.X) (i : Fin 4) : (ρ ▷ D.P.A).left ≫ famφT D T α i = famφT D T' α i := by
  have hu : ρ ▷ D.P.A ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  fin_cases i
  · show (ρ ▷ D.P.A ≫ snd T D.P.A).left = (snd T' D.P.A).left
    rw [whiskerRight_snd]
  · show (ρ ▷ D.P.A ≫ padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (snd T' D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, whiskerRight_snd, ← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ D.c α).left = (toUnit (T' ⊗ D.P.A) ≫ D.c α).left
    rw [← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit (T' ⊗ D.P.A) ≫ η[D.P.A]).left
    rw [← Category.assoc, hu]

theorem expT_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → ∃ (σ' : U.SecGT T' k) (f' : ∀ α, SecBT D T' k α), U.ExpT T' k σ' f' ∧ PullT ρ f f' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T') (s : Raw D F k), PullB D F φ k f' s ↔ PullB D F (φ ≫ ρ) k f s := by
  intro R _ _ I D A G _ _ U T T' ρ k σ f H
  obtain ⟨σ', hσ⟩ := exists_pullSec_sval σ (ρ ▷ G).left (fun _ => (snd T' G).left) (fun _ => by
    show (ρ ▷ G ≫ snd T G).left = _
    rw [whiskerRight_snd])
  choose f' hf using fun α => exists_pullSec_sval (f α) (ρ ▷ D.P.A).left (famφT D T' α) (whisker_famφT D ρ α)
  have s1 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (snd T B).left = (snd T' B).left := fun B => by
    show (ρ ▷ B ≫ snd T B).left = _
    rw [whiskerRight_snd]
  have s2 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun B => by
    show (ρ ▷ B ≫ fst T B).left = (fst T' B ≫ ρ).left
    rw [whiskerRight_fst]
  refine ⟨σ', f', fun e => ?_, fun α Z r z J hJ => hf α Z r z J hJ, fun F _ _ φ s => ?_⟩
  · obtain ⟨s, hs⟩ := H e
    refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hJ => ?_⟩
    have := hs Z x (rG ≫ (ρ ▷ G).left) (rB ≫ (ρ ▷ D.P.A).left) (by rw [Category.assoc, s1, h1])
      (by rw [Category.assoc, s1, h2])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h3, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => (hf α Z rB z J hJ).trans (this.1 α hα), ?_⟩
    rw [hσ Z rG z JG hG, this.2]
    exact Finset.sum_congr rfl fun α _ => by rw [hf α Z rB z J hJ]
  · have e : (φ ▷ D.P.A).left ≫ (ρ ▷ D.P.A).left = ((φ ≫ ρ) ▷ D.P.A).left := by
      rw [comp_whiskerRight]; rfl
    have key : ∀ α (z : (DegPre.BF D F).left) J, Good D.P.L z J →
        sval (f' α) (φ ▷ D.P.A).left z J = sval (f α) ((φ ≫ ρ) ▷ D.P.A).left z J := fun α z J hJ =>
      (hf α _ (φ ▷ D.P.A).left z J hJ).trans (congrArg (fun q => sval (f α) q z J) e)
    exact ⟨fun h α z J hJ => (h α z J hJ).trans (key α z J hJ), fun h α z J hJ => (h α z J hJ).trans (key α z J hJ).symm⟩

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralWitness
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntWit

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs
  · simp only [map_zero]
  · rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans (gs_zero r z _)

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j : K → L.ι) :
    s.f j = 0 := by
  refine fn_ext (V := LB.wchart L φ j) fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem integral_witness : AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X), U.FE F k → U.Supp F k β → ∃ (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f ∧ PullB D F (toUnit _) k f s ∧ DegPre.FamFE D F k s ∧ (∃ j, (s β).f j ≠ 0) ∧ ∃ j, (f β).f j ≠ 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k β hFE hS
  obtain ⟨t, s, ⟨n, c, σ, f, hE, -, hB⟩, j₀, hj₀⟩ := hS
  obtain ⟨hG, hP⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U F (𝟙_ _) (toUnit _) k
  choose s' hs' using fun i => (hP (f i)).exists
  have hex : ∃ i, ∃ j, (s' i β).f j ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hj₀ (eq_zero_of_sval D.P.isLB (s β) (fun y J hJ => ?_) j₀)
    have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
    refine (hB β _ (𝟙 _) (toUnit (TF (R := V) F) ▷ D.P.A).left (w.trans (Category.id_comp _).symm) y J hJ).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (congrArg (_ * ·) ((hs' i β y J hJ).symm.trans (sval_eq_zero _ (hn i) _ _ _))).trans (mul_zero _)
  obtain ⟨i, j, hj⟩ := hex
  obtain ⟨t', ht'⟩ := (hG (σ i)).exists
  refine ⟨σ i, f i, s' i, hE i, hs' i,
    hFE t' (s' i) (IntExp.expF_of_expT V _ D A G U F k (σ i) (f i) t' (s' i) (hE i) ht' (hs' i)), ⟨j, hj⟩, ?_⟩
  by_contra hn
  push Not at hn
  exact hj (eq_zero_of_sval D.P.isLB (s' i β)
    (fun y J hJ => (hs' i β y J hJ).trans (sval_eq_zero _ hn _ _ _)) j)

end GlobalTheory.UU.IntWit
end
end

