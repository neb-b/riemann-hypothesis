module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVIsoExtendsOfIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.RosMove

def rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) : Fin 6 → (A ⊗ A ⟶ A) :=
  ![(fst A A ≫ f) * snd A A, fst A A ≫ f, snd A A, fst A A * (snd A A ≫ g), fst A A, snd A A ≫ g]

theorem rosO_left {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) (k : Fin 6) :
    (rosO A f g k).left = rosatiφ A f g k := by
  fin_cases k <;> rfl

theorem lift_rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A)
    (k : Fin 6) : lift x y ≫ rosO A f g k = ![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] k := by
  fin_cases k <;> simp [rosO, MonObj.comp_mul]

theorem val_origin {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {f g : A ⟶ A}
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    (hu : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem val_move (hG : GlobalFnsSt) {F : Type} [Field F] [IsAlgClosed F] {S S' : Scheme.{0}} (t : Sp F ⟶ S) (t' : Sp F ⟶ S')
    {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] (hA : IsAbelianScheme A)
    (hA' : IsAbelianScheme A') {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (Φ : (Over.mk t ⊗ A).left ⟶ A'.left) (w : LB.Iso (L.pull (snd (Over.mk t) A).left) (L'.pull Φ)) (hw : w.IsGen)
    (hΦ : Φ ≫ A'.hom = (fst (Over.mk t) A).left ≫ t') (ψ : (Over.mk t ⟶ A) →* (Over.mk t' ⟶ A'))
    (hψ : ∀ x, (lift (𝟙 (Over.mk t)) x).left ≫ Φ = (ψ x).left) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (f' g' : A' ⟶ A')
    (hf : ∀ x, ψ (x ≫ f) = ψ x ≫ f') (hg : ∀ x, ψ (x ≫ g) = ψ x ≫ g')
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : u.IsGen)
    (u₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {u' : LB.Gen (LB.LinComb L' (rosatiφ A' f' g') rosatiε)} (hu' : u'.IsGen)
    (u₀' : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ u' (zero2 A')) (LB.oneGen L'))
    (z : Sp F) (N) (J) (hN : Good L z N) (hJ : Good L' z J) (b b' : Over.mk t ⟶ A) :
    val u' (lift (ψ b) (ψ b')).left z J =
      (∏ k, gw w (lift (𝟙 (Over.mk t)) (lift b b' ≫ rosO A f g k)).left z (J (ψ (lift b b' ≫ rosO A f g k)).left)
        (fun _ => N (lift b b' ≫ rosO A f g k).left) ^ rosatiε k) * val u (lift b b').left z N := by
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  let Y : Over S := T ⊗ (A ⊗ A)
  let p : Y.left ⟶ Sp F := (fst T (A ⊗ A)).left
  let Y' : Over S' := Over.mk (p ≫ t')
  let Θ : (Y ⟶ A) → (Y' ⟶ A') := fun x => Over.homMk ((lift (fst T (A ⊗ A)) x).left ≫ Φ) (by
    show ((lift (fst T (A ⊗ A)) x).left ≫ Φ) ≫ A'.hom = p ≫ t'
    rw [Category.assoc, hΦ, ← Category.assoc, ← Over.comp_left, lift_fst])
  let pt : (T ⟶ A ⊗ A) → (T' ⟶ Y') := fun c => Over.homMk (lift (𝟙 T) c).left (by
    show (lift (𝟙 T) c).left ≫ (fst T (A ⊗ A)).left ≫ t' = t'
    rw [← Category.assoc, ← Over.comp_left, lift_fst]; exact Category.id_comp _)
  have hΘ : ∀ c x, pt c ≫ Θ (snd _ _ ≫ x) = ψ (c ≫ x) := fun c x => by
    ext
    show (lift (𝟙 T) c).left ≫ (lift (fst T (A ⊗ A)) (snd _ _ ≫ x)).left ≫ Φ = _
    rw [← Category.assoc, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hψ]
  let H : Y' ⟶ A' ⊗ A' := lift (Θ (snd _ _ ≫ fst A A)) (Θ (snd _ _ ≫ snd A A))
  have hH : ∀ x y, pt (lift x y) ≫ H = lift (ψ x) (ψ y) := fun x y => by
    rw [comp_lift, hΘ, hΘ, lift_fst, lift_snd]
  have hr : ∀ x y k, lift (ψ x) (ψ y) ≫ rosO A' f' g' k = ψ (lift x y ≫ rosO A f g k) := fun x y k => by
    rw [lift_rosO, lift_rosO]
    fin_cases k <;> simp [hf, hg]
  have := hA.smooth
  have := hA'.proper
  have sm : Smooth (A ⊗ A).hom := by
    show Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have sp : Smooth p := by
    show Smooth (pullback.fst t (A ⊗ A).hom); infer_instance
  have rd : IsReduced Y.left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hE : ∀ k, (Θ (snd _ _ ≫ rosO A f g k)).left = H.left ≫ rosatiφ A' f' g' k := fun k => by
    rw [← rosO_left, ← Over.comp_left]
    refine ComplexPoints.hom_ext_of_points (X := Y.left) p A'.hom ((Over.w _).trans (Over.w _).symm) fun x hx => ?_
    let x₀ : T ⟶ Y := Over.homMk x (by
      show x ≫ Y.hom = t
      rw [← Over.w (fst T (A ⊗ A)), ← Category.assoc]
      exact (congrArg (· ≫ t) hx).trans (Category.id_comp _))
    have e : x₀ = lift (𝟙 T) (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst]; ext; exact hx
      · rw [lift_snd, ← comp_lift, ← comp_lift, lift_fst_snd, Category.comp_id]
    have e' : x = (pt (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A))).left := congrArg (·.left) e
    rw [e', ← Over.comp_left, ← Over.comp_left, hΘ, ← Category.assoc (pt _), hH, hr]
  let φ : Fin 6 → (Y.left ⟶ (T ⊗ A).left) := fun k => (lift (fst T (A ⊗ A)) (snd _ _ ≫ rosO A f g k)).left
  have hφ : ∀ k, φ k ≫ (snd T A).left = (snd T (A ⊗ A)).left ≫ rosatiφ A f g k := fun k => by
    rw [← rosO_left, ← Over.comp_left, ← Over.comp_left, lift_snd]
  have hφc : ∀ c k, (lift (𝟙 T) c).left ≫ φ k = (lift (𝟙 T) (c ≫ rosO A f g k)).left := fun c k => by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  obtain ⟨a, ha, va⟩ := exists_gen hL (φ' := fun k => φ k ≫ (snd T A).left) (ε' := rosatiε)
    (fun U _ h => by simp only [hφ]) (LB.pullGen L _ _ u (snd T (A ⊗ A)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨s, hs, vs⟩ := GlobalTheory.EndRosati.exists_gen_through hL hL' w hw φ rosatiε a ha
  have ev : ∀ (c : T ⟶ A ⊗ A) (y : Sp F) N J, Good L y N → Good L' y J → val s (lift (𝟙 T) c).left y J =
      (∏ k, gw w (lift (𝟙 T) (c ≫ rosO A f g k)).left y (J (ψ (c ≫ rosO A f g k)).left)
        (fun _ => N (c ≫ rosO A f g k).left) ^ rosatiε k) * val u c.left y N := fun c y N J hN hJ => by
    rw [vs _ _ y J N hJ hN, va _ _ y N hN, val_pull hN, ← Over.comp_left, lift_snd]
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
    rw [hφc, hψ, ← Over.comp_left, lift_snd]
  have ev' : ∀ (x x' : T ⟶ A) (y : Sp F) J, Good L' y J →
      val (LB.pullGen L' _ _ u' H.left) (lift (𝟙 T) (lift x x')).left y J = val u' (lift (ψ x) (ψ x')).left y J :=
    fun x x' y J hJ => by rw [val_pull hJ, ← hH]; rfl
  have hp : Function.Surjective p.appTop.hom := by
    let β : Y ≅ A ⊗ (A ⊗ T) := β_ _ _ ≪≫ α_ _ _ _
    have e : p = β.hom.left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left := by
      have : fst T (A ⊗ A) = β.hom ≫ snd A (A ⊗ T) ≫ snd A T := by simp [β, Y]
      exact congrArg (·.left) this
    rw [e]
    refine surj_comp ?_ (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget S).map β.hom))
    have : IsIso β.hom.left.appTop := inferInstanceAs (IsIso (β.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso β.hom.left.appTop).2
  refine (ev' b b' z J hJ).symm.trans (Eq.trans ?_ (ev _ z N J hN hJ))
  refine gen_unique' hL' (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (hE k)) p
    (lift (𝟙 T) (lift 1 1)).left (by rw [← Over.comp_left, lift_fst]; rfl) hp
    (DVR.pullGen_isGen _ _ _ _ hu' _) hs (fun y I hI => ?_) _ _ z J hJ
  choose M hM using fun χ : Sp F ⟶ A.left => exists_chart hL (χ y)
  have o : ∀ k, lift (1 : T ⟶ A) 1 ≫ rosO A f g k = 1 := fun k => by
    rw [lift_rosO]; fin_cases k <;> simp [MonObj.one_comp]
  refine (ev' _ _ y I hI).trans (Eq.trans ?_ (ev _ y M I hM hI).symm)
  rw [map_one, val_origin u₀' (T := T') hI, val_origin u₀ (T := T) hM]
  simp [o, rosatiε, Fin.prod_univ_succ]

theorem rosV_move : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  intro hL R R' _ _ _ _ D D' F _ _ _ _ N N' ν ν' O _ _ oa oa' Φ w φ wv hw hΦ hφ hwv hact a ρ ρ' ⟨u, hu, u₀, hρ⟩
    ⟨u', hu', u₀', hρ'⟩ b b'
  have := oa.hom a
  have := oa.hom (star a)
  let ψ : (TF (R := R) F ⟶ D.P.A) →* (TF (R := R') F ⟶ D'.P.A) :=
    (ν'.eA.toMonoidHom.comp φ).comp ν.eA.symm.toMonoidHom
  have e : ∀ x, ψ (ν.eA x) = ν'.eA (φ x) := fun x => by simp [ψ]
  have ea : ∀ y x, ν.eA (actV ν oa y x) = ν.eA x ≫ oa.act y := fun y x => ν.eA.apply_symm_apply _
  have hf : ∀ y x, ψ (x ≫ oa.act y) = ψ x ≫ oa'.act y := fun y x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [← ea, e, e, hact]; exact ν'.eA.apply_symm_apply _
  have hψ : ∀ x, (lift (𝟙 (TF (R := R) F)) x).left ≫ Φ = (ψ x).left := fun x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [e, hφ]
  let z : Sp F := IsLocalRing.closedPoint F
  have hN : Good D.P.L z ν.J := fun q => ν.good q trivial
  have hJ : Good D'.P.L z ν'.J := fun q => ν'.good q trivial
  have H := val_move hL.globalFns _ _ D.P.isAb D'.P.isAb D.P.isLB D'.P.isLB Φ w hw hΦ ψ hψ _ _ _ _ (hf (star a)) (hf a)
    hu u₀ hu' u₀' z ν.J ν'.J hN hJ (ν.eA b) (ν.eA b')
  let W : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x =>
    gw w (lift (𝟙 (TF (R := R) F)) x).left z (ν'.J (ψ x).left) (fun _ => ν.J x.left)
  have hW : ∀ x, toStk z (wv x) = (W (ν.eA x)).val := fun x => by
    rw [hwv, ← e]
    have m₁ : Φ ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left) :=
      (congrArg (fun q : Sp F ⟶ _ => q z ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left)) (hψ (ν.eA x))).mpr (hJ _)
    have m₂ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : TF (R := R) F ⟶ _ => q.left z ∈ D.P.L.U (ν.J (ν.eA x).left))
        (lift_snd (𝟙 (TF (R := R) F)) (ν.eA x))).mpr (hN _)
    exact toStk_valF _ (_ ⊓ _) z ⟨mem_pull.2 m₁, mem_pull.2 m₂⟩ _
  have H' : val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J =
      (∏ k, W (lift (ν.eA b) (ν.eA b') ≫ rosO _ (oa.act (star a)) (oa.act a) k) ^ rosatiε k) * val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J := by
    rw [← e, ← e]; exact H
  have v : toStk z (ρ b b') = (val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J).val := by
    rw [hρ]; exact toStk_valF _ _ z (hN.mem _ _) _
  have v' : toStk z (ρ' (φ b) (φ b')) = (val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J).val := by
    rw [hρ']; exact toStk_valF _ _ z (hJ.mem _ _) _
  apply (toStk z).injective
  simp only [map_mul, hW, v, v', ea, ← Units.val_mul, H', lift_rosO]
  congr 1
  clear_value W
  apply Additive.ofMul.injective
  simp [rosatiε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.RosMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PolIsoDescent

open GlobalTheory.GenSpread

theorem flat_surjective {F C : Type} [Field F] [Field C] (i : Sp F ⟶ Sp C) : Flat i ∧ Surjective i :=
  have : Subsingleton (Sp C) := inferInstanceAs (Subsingleton (PrimeSpectrum C))
  ⟨inferInstance, ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩⟩

theorem charZero_of_hom {F C : Type} [Field F] [Field C] [CharZero C] (i : Sp F ⟶ Sp C) : CharZero F :=
  charZero_of_injective_ringHom (f := (Spec.preimage i).hom) (RingHom.injective _)

theorem exists_torsion_of_algClosed (hM : MulNSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F C : Type}
    [Field F] [IsAlgClosed F] [Field C] [IsAlgClosed C] [CharZero C] (i : Sp F ⟶ Sp C) (t : Sp C ⟶ S) {n : ℕ}
    (hn : 1 ≤ n) (x : Over.mk (i ≫ t) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ z : Over.mk t ⟶ P.A, z ^ n = 1 ∧ x.left = i ≫ z.left := by
  have := charZero_of_hom i
  obtain ⟨_, _⟩ := flat_surjective i
  have : Epi i := Flat.epi_of_flat_of_surjective _
  have h := (hM S P n hn).2.2.2.2
  have h₁ := h F (i ≫ t) (Nat.cast_ne_zero.2 (by omega))
  have h₂ := h C t (Nat.cast_ne_zero.2 (by omega))
  let ρ : Over.mk (i ≫ t) ⟶ Over.mk t := Over.homMk i rfl
  let r : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (i ≫ t) ⟶ P.A // x ^ n = 1} := fun z =>
    ⟨ρ ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩
  have hr : Function.Injective r := fun a b e => Subtype.ext (Over.OverMorphism.ext
    ((cancel_epi i).1 (congrArg (fun q => q.1.left) e)))
  have : Finite {x : Over.mk (i ≫ t) ⟶ P.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [h₁]; positivity)
  obtain ⟨z, hz⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₂.trans h₁.symm⟩).2 ⟨x, hx⟩
  exact ⟨z.1, z.2, (congrArg (fun q => q.1.left) hz).symm⟩

theorem eq_of_torsion (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] [IsAlgClosed F]
    (W : PolAV (Sp F)) {s : Sp F ⟶ S} {f₁ f₂ : W.A.left ⟶ P.A.left} (h₁ : IsGrpPullback W.A P.A s f₁)
    (h₂ : IsGrpPullback W.A P.A s f₂) (l₁ : LBIso W.L (P.L.pull f₁)) (l₂ : LBIso W.L (P.L.pull f₂)) {M : ℕ}
    (hM : 3 ≤ M) (hF : (M : F) ≠ 0)
    (h : ∀ y : Over.mk (𝟙 (Sp F)) ⟶ W.A, y ^ M = 1 → y.left ≫ f₁ = y.left ≫ f₂) : f₁ = f₂ := by
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso h₁ h₂
  obtain ⟨w, hw⟩ := l₁.trans W.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull W.isLB _)
    (lbIso_pull_of_lbIso l₂ θ.hom.left e.symm).symm
  have := MatchRigid.aut_eq_id hL W (𝟙 _) hM hF θ w hw fun y hy =>
    Over.OverMorphism.ext (h₂.1.hom_ext (by rw [Over.comp_left, Category.assoc, e, h y hy]) (by rw [Over.w, Over.w]))
  rw [← e, this, Over.id_left, Category.id_comp]

theorem comp_eq_of_rational (hL : Laws) {S U : Scheme.{0}} [IsLocallyNoetherian S] (B B' : PolAV S) {C : Type}
    [Field C] [IsAlgClosed C] [CharZero C] (κ : Sp C ⟶ U) (j : U ⟶ S)
    (rB : ∀ x : Over.mk (κ ≫ j) ⟶ B.A, x ^ 3 = 1 → ∃ x₀ : U ⟶ B.A.left, x.left = κ ≫ x₀)
    (rB' : ∀ x : Over.mk (κ ≫ j) ⟶ B'.A, x ^ 3 = 1 → ∃ x₀ : U ⟶ B'.A.left, x.left = κ ≫ x₀)
    {Q : Over (Sp C)} [GrpObj Q] {f : Q.left ⟶ B.A.left} {f' : Q.left ⟶ B'.A.left}
    (hf : IsGrpPullback Q B.A (κ ≫ j) f) (hf' : IsGrpPullback Q B'.A (κ ≫ j) f')
    (hl : LBIso (B'.L.pull f') (B.L.pull f)) {F : Type} [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ Q.left)
    (e : x ≫ f' = x' ≫ f') (e' : (x ≫ Q.hom) ≫ κ = (x' ≫ Q.hom) ≫ κ) : x ≫ f = x' ≫ f := by
  have := charZero_of_hom (x ≫ Q.hom)
  obtain ⟨W, h, hh, -, hm, hw⟩ := hL.polBaseChange S _ (((x ≫ Q.hom) ≫ κ) ≫ j) B'
  have hp : IsGrpPullback W.A B'.A (((x ≫ Q.hom) ≫ κ) ≫ j) h := ⟨hh, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hh.w x), (Over.OverMorphism.ext hy : y₀ = toBase hh.w y), ← hm]
    rfl⟩
  have key : ∀ i : Sp F ⟶ Sp C, (x ≫ Q.hom) ≫ κ = i ≫ κ → ∃ a : W.A.left ⟶ Q.left, a ≫ f' = h ∧
      a ≫ Q.hom = W.A.hom ≫ i ∧ IsGrpPullback W.A B.A (((x ≫ Q.hom) ≫ κ) ≫ j) (a ≫ f) ∧
      LBIso W.L (B.L.pull (a ≫ f)) := fun i hi => by
    have hi' : ((x ≫ Q.hom) ≫ κ) ≫ j = i ≫ κ ≫ j := by rw [hi, Category.assoc]
    have w : h ≫ B'.A.hom = (W.A.hom ≫ i) ≫ κ ≫ j := by rw [hh.w, hi', Category.assoc]
    have a₁ := hf'.1.lift_fst _ _ w
    have a₂ := hf'.1.lift_snd _ _ w
    exact ⟨_, a₁, a₂, ((hf'.cancel (hp.congr hi' a₁.symm) a₂).comp hf).congr hi'.symm rfl,
      (LBIso.symm hw).trans W.isLB (LB.isLB_pull B'.isLB _) (LB.isLB_pull B.isLB _) (lbIso_pull_comp _ a₁.symm rfl hl)⟩
  obtain ⟨a, a₁, a₂, a₃, a₄⟩ := key _ rfl
  obtain ⟨a', a₁', a₂', a₃', a₄'⟩ := key _ e'
  have E : a ≫ f = a' ≫ f := by
    refine eq_of_torsion hL B W a₃ a₃' a₄ a₄' le_rfl (by norm_num) fun y hy => ?_
    have hyw : y.left ≫ W.A.hom = 𝟙 _ := Over.w y
    let ρ : Over.mk ((x ≫ Q.hom) ≫ κ ≫ j) ⟶ Over.mk (𝟙 _ ≫ ((x ≫ Q.hom) ≫ κ) ≫ j) := Over.homMk (𝟙 _) (by simp)
    obtain ⟨z, hz, ez⟩ := exists_torsion_of_algClosed hL.mulN B' (x ≫ Q.hom) (κ ≫ j) (n := 3) (by norm_num)
      (ρ ≫ pushHom hp _ y) (by rw [← MonObj.comp_pow]; erw [← map_pow, hy, map_one, MonObj.comp_one])
    replace ez : y.left ≫ h = (x ≫ Q.hom) ≫ z.left := (Category.id_comp _).symm.trans ez
    obtain ⟨z₀, hz₀⟩ := rB' z hz
    have hzw : z.left ≫ B'.A.hom = 𝟙 _ ≫ κ ≫ j := (Over.w z).trans (Category.id_comp _).symm
    let u : Over.mk (𝟙 (Sp C)) ⟶ Q := Over.homMk (hf'.1.lift z.left (𝟙 _) hzw) (hf'.1.lift_snd _ _ _)
    have u₁ : u.left ≫ f' = z.left := hf'.1.lift_fst _ _ _
    have u₂ : u.left ≫ Q.hom = 𝟙 _ := Over.w u
    let σ : Over.mk (𝟙 _ ≫ κ ≫ j) ⟶ Over.mk (κ ≫ j) := Over.homMk (𝟙 _) rfl
    let σ' : Over.mk (κ ≫ j) ⟶ Over.mk (𝟙 _ ≫ κ ≫ j) := Over.homMk (𝟙 _) (by simp)
    have hu : u ^ 3 = 1 := by
      have inj : Function.Injective (pushHom hf' (Over.mk (𝟙 _))) := fun p q h => Over.OverMorphism.ext
        (hf'.1.hom_ext (congrArg (fun m => m.left) h) (by rw [Over.w, Over.w]))
      have : pushHom hf' _ u = σ ≫ z := Over.OverMorphism.ext (u₁.trans (Category.id_comp _).symm)
      apply inj
      rw [map_pow, this, ← MonObj.comp_pow, hz, MonObj.comp_one, map_one]
    obtain ⟨v₀, hv₀⟩ := rB (σ' ≫ pushHom hf _ u)
      (by rw [← MonObj.comp_pow]; erw [← map_pow, hu, map_one, MonObj.comp_one])
    replace hv₀ : u.left ≫ f = κ ≫ v₀ := (Category.id_comp _).symm.trans hv₀
    have fin : ∀ (i : Sp F ⟶ Sp C) (b : W.A.left ⟶ Q.left), (x ≫ Q.hom) ≫ κ = i ≫ κ → b ≫ f' = h →
        b ≫ Q.hom = W.A.hom ≫ i → y.left ≫ b ≫ f = (i ≫ κ) ≫ v₀ := fun i b hi b₁ b₂ => by
      have : y.left ≫ b = i ≫ u.left := hf'.1.hom_ext
        (by rw [Category.assoc, b₁, ez, Category.assoc i, u₁, hz₀, ← Category.assoc, hi, Category.assoc])
        (by rw [Category.assoc, b₂, reassoc_of% hyw, Category.assoc, u₂]; exact (Category.comp_id _).symm)
      rw [reassoc_of% this, hv₀, Category.assoc]
    rw [fin _ a rfl a₁ a₂, fin _ a' e' a₁' a₂', e']
  have w : (x ≫ f') ≫ B'.A.hom = 𝟙 _ ≫ ((x ≫ Q.hom) ≫ κ) ≫ j := by simp [hf'.1.w]
  have y₁ := hh.lift_fst _ _ w
  have y₂ := hh.lift_snd _ _ w
  have fin : ∀ (p : Sp F ⟶ Q.left) (b : W.A.left ⟶ Q.left), x ≫ f' = p ≫ f' → b ≫ f' = h →
      b ≫ Q.hom = W.A.hom ≫ p ≫ Q.hom → p = hh.lift _ _ w ≫ b := fun p b hp b₁ b₂ => hf'.1.hom_ext
    (by rw [Category.assoc, b₁, y₁, hp]) (by rw [Category.assoc, b₂, reassoc_of% y₂])
  rw [fin x' a' e a₁' a₂', Category.assoc, ← E, ← Category.assoc, ← fin x a rfl a₁ a₂]

theorem isGrpPullback_of_one (hL : Laws) {S S' : Scheme.{0}} {t : S' ⟶ S} {G : Over S} [GrpObj G] {Q : Over S'}
    [GrpObj Q] (hG : IsAbelianScheme G) (hQ : IsAbelianScheme Q) {f : Q.left ⟶ G.left}
    (hf : IsPullback f Q.hom G.hom t) (h₀ : eSec Q ≫ f = t ≫ eSec G) : IsGrpPullback Q G t f := by
  have hp := isGrpPullback_pullback G t
  let e : Q ≅ (Over.pullback t).obj G :=
    Over.isoMk (hf.isoIsPullback _ _ hp.1) (hf.isoIsPullback_hom_snd _ _ hp.1)
  have he : e.hom.left ≫ pullback.fst G.hom t = f := hf.isoIsPullback_hom_fst _ _ hp.1
  have : IsMonHom e.hom := hL.rigidity _ _ _ hQ (TLinPf.isAb_pullback t G hG) e.hom
    (Over.OverMorphism.ext (hp.1.hom_ext
      ((Category.assoc _ _ _).trans ((congrArg (eSec Q ≫ ·) he).trans (h₀.trans (PolExtend.eSec_fst t G).symm)))
      (by rw [Over.w, Over.w])))
  exact ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) he

theorem lbIso_descend (hG : GlobalFnsSt) {K C : Type} [Field K] [Field C] (κ : Sp C ⟶ Sp K) (X : Over (Sp K))
    [GrpObj X] (hX : IsAbelianScheme X) {L M : LB X.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso (L.pull (pullback.fst X.hom κ)) (M.pull (pullback.fst X.hom κ))) : LBIso L M := by
  obtain ⟨h₁, h₂⟩ := flat_surjective κ
  have hN := LB.isLB_div hM hL
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨i, hi⟩ := exists_chart hN (eSec X (default : PrimeSpectrum K))
  exact exists_gen_of_rigidified_of_flat_baseChange hG _ _ κ X _ hX hN h₁ h₂ inferInstance
    (IsoExtend.exists_gen_of_chart hN _ i fun y => by
      rw [Subsingleton.elim (α := Sp K) y (default : PrimeSpectrum K)]; exact hi)
    ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)

end GlobalTheory.PolIsoDescent


open GlobalTheory.PolIsoDescent GlobalTheory.GenSpread in
theorem GlobalTheory.polAV_iso_descends_of_ratTors : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  intro hL hL₂ hext R _ _ _ ⟨_, _, _⟩ C _ _ _ B B' rB rB' φ g hφ hg hl
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing R) C).injective
  let κ : Sp C ⟶ Sp (FractionRing R) := jFK (R := R) C
  let X := (Over.pullback (jK R)).obj B'.A
  let Y := (Over.pullback (jK R)).obj B.A
  let Q := (Over.pullback κ).obj X
  have hX : IsAbelianScheme X := TLinPf.isAb_pullback _ _ B'.isAb
  have hY : IsAbelianScheme Y := TLinPf.isAb_pullback _ _ B.isAb
  have hQ : IsAbelianScheme Q := TLinPf.isAb_pullback _ _ hX
  let π : Q.left ⟶ X.left := pullback.fst X.hom κ
  let p : X.left ⟶ B'.A.left := pullback.fst B'.A.hom (jK R)
  have hπ : IsGrpPullback Q X κ π := isGrpPullback_pullback X κ
  have hp : IsGrpPullback X B'.A (jK R) p := isGrpPullback_pullback B'.A (jK R)
  have hY' := isGrpPullback_pullback B.A (jK R)
  have hf' := hπ.comp hp
  have pb : ∀ A : Over (Sp R), IsPullback (snd (TF (R := R) C) A).left (fst (TF (R := R) C) A).left A.hom (κ ≫ jK R) :=
    fun A => (IsPullback.of_hasPullback (TF (R := R) C).hom A.hom).flip
  let c := hf'.1.isoIsPullback _ _ (pb B'.A)
  have c₁ : c.hom ≫ (snd (TF (R := R) C) B'.A).left = π ≫ p := hf'.1.isoIsPullback_hom_fst _ _ _
  have c₂ : c.hom ≫ (fst (TF (R := R) C) B'.A).left = Q.hom := hf'.1.isoIsPullback_hom_snd _ _ _
  have hφ' : φ.inv ≫ fst _ _ = fst _ _ := by rw [← hφ, Iso.inv_hom_id_assoc]
  let f : Q.left ⟶ B.A.left := (c.hom ≫ φ.inv.left) ≫ (snd (TF (R := R) C) B.A).left
  have hfp : IsPullback f Q.hom B.A.hom (κ ≫ jK R) := by
    have : IsIso φ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map φ.inv))
    have h : IsPullback (c.hom ≫ φ.inv.left) Q.hom (fst (TF (R := R) C) B.A).left (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.assoc, ← Over.comp_left, hφ', c₂, Category.comp_id]⟩
    exact Category.id_comp (κ ≫ jK R) ▸ h.paste_horiz (pb B.A)
  have pt : ∀ (x : TF (R := R) C ⟶ B.A) (u : Sp C ⟶ Q.left), u ≫ π ≫ p = (g x).left → u ≫ Q.hom = 𝟙 _ →
      u ≫ f = x.left := fun x u u₁ u₂ => by
    have : u ≫ c.hom = (lift (𝟙 _) (g x)).left := (pb B'.A).hom_ext
      (by rw [Category.assoc, c₁, u₁, ← Over.comp_left, lift_snd])
      (by rw [Category.assoc, c₂, u₂, ← Over.comp_left, lift_fst]; rfl)
    change u ≫ (c.hom ≫ _) ≫ _ = _
    rw [Category.assoc, reassoc_of% this, ← Over.comp_left, ← Over.comp_left, ← hg, Category.assoc,
      Iso.hom_inv_id_assoc, lift_snd]
  have one : ∀ P : PolAV (Sp R), (1 : TF (R := R) C ⟶ P.A).left = (κ ≫ jK R) ≫ eSec P.A := fun _ => rfl
  have hf : IsGrpPullback Q B.A (κ ≫ jK R) f := by
    refine GlobalTheory.PolIsoDescent.isGrpPullback_of_one hL B.isAb hQ hfp ((pt 1 _ ?_ (Over.w η[Q])).trans (one B))
    rw [map_one, one, ← Category.assoc]
    erw [PolExtend.eSec_fst κ X, Category.assoc, PolExtend.eSec_fst (jK R) B'.A, Category.assoc]
  have hl' : LBIso (B'.L.pull (π ≫ p)) (B.L.pull f) := GlobalTheory.GenSpread.lbIso_pull_comp (c.hom ≫ φ.inv.left)
    (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id_assoc, c₁]) rfl hl.symm
  have wf : f ≫ B.A.hom = (Q.hom ≫ κ) ≫ jK R := by rw [hfp.w, Category.assoc]
  obtain ⟨f₀, hf₀⟩ := exists_desc_of_smooth_of_geometricPoints (FractionRing R) C X Y hX.smooth
    (have := hY.proper; inferInstance) (hY'.1.lift f (Q.hom ≫ κ) wf) ((hY'.1.lift_snd _ _ _).trans hπ.1.w.symm)
    fun F _ _ x x' e => by
      have e' : (x ≫ Q.hom) ≫ κ = (x' ≫ Q.hom) ≫ κ := by
        rw [Category.assoc, Category.assoc, ← hπ.1.w]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom) e).trans (Category.assoc _ _ _))
      refine hY'.1.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hY'.1.lift_fst]
        exact GlobalTheory.PolIsoDescent.comp_eq_of_rational hL B B' κ (jK R) (fun x hx => (rB x hx).elim fun a h => ⟨a.left, h⟩)
          (fun x hx => (rB' x hx).elim fun a h => ⟨a.left, h⟩) hf hf' hl' x x'
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) e).trans (Category.assoc _ _ _))) e'
      · rw [Category.assoc, Category.assoc, hY'.1.lift_snd, ← Category.assoc, ← Category.assoc]
        exact e'
  have ef : π ≫ f₀.left ≫ pullback.fst B.A.hom (jK R) = f :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst B.A.hom (jK R)) hf₀).trans (hY'.1.lift_fst _ _ _))
  obtain ⟨k₁, k₂⟩ := GlobalTheory.PolIsoDescent.flat_surjective κ
  have h₀ : IsGrpPullback X B.A (jK R) (f₀.left ≫ pullback.fst B.A.hom (jK R)) :=
    isGrpPullback_of_fpqc _ _ _ (jK R) κ B.A X Q π _ k₁ k₂ inferInstance hπ (hf.congr rfl ef.symm)
      (by rw [Category.assoc, hY'.1.w, ← Category.assoc, Over.w f₀])
  obtain ⟨ψ, hψ, eψ⟩ := grpPullback_iso h₀ hY'
  rw [← eψ] at ef
  obtain ⟨Ψ, m, hΨ, l⟩ := polAV_iso_extends_of_isIntegrallyClosed hL hL₂ R B B' ψ hψ
    (GlobalTheory.PolIsoDescent.lbIso_descend hL.globalFns κ X hX (LB.isLB_pull B'.isLB _) (LB.isLB_pull B.isLB _)
      (LBIso.trans (LB.isLB_pull (LB.isLB_pull B'.isLB _) _) (LB.isLB_pull B'.isLB _) (LB.isLB_pull (LB.isLB_pull B.isLB _) _)
        (GlobalTheory.GenSpread.lbIso_pull_pull B'.isLB π rfl).symm
        (LBIso.trans (LB.isLB_pull B'.isLB _) (LB.isLB_pull B.isLB _) (LB.isLB_pull (LB.isLB_pull B.isLB _) _) hl'
          (GlobalTheory.GenSpread.lbIso_pull_pull B.isLB π ef.symm)))) hext
  refine ⟨Ψ, m, l, fun x => Over.OverMorphism.ext ?_⟩
  have w : (g x).left ≫ B'.A.hom = 𝟙 _ ≫ κ ≫ jK R := (Over.w (g x)).trans (Category.id_comp _).symm
  have u₁ := hf'.1.lift_fst _ _ w
  have q : ψ.hom.left ≫ pullback.fst B.A.hom (jK R) = p ≫ Ψ.hom.left := by
    rw [← hΨ]
    exact ExtUnique.pullback_map_left_fst (jK R) Ψ.hom
  rw [← pt x _ u₁ (hf'.1.lift_snd _ _ w), ← ef, q, Over.comp_left]
  exact (congrArg (· ≫ Ψ.hom.left) u₁).symm.trans (by simp only [Category.assoc])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionPower_calculus_geometric_fibre : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  first | exact @GlobalTheory.OneBasis.Calc.main | exact GlobalTheory.OneBasis.Calc.main | (intros; apply GlobalTheory.OneBasis.Calc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianHomExtensionOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.LN.homExt_of_laws : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → _root_.GlobalTheory.LN.HomExtSt := by
  intro _ _
  unfold _root_.GlobalTheory.LN.HomExtSt
  exact _root_.GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (_root_.GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion
      (_root_.GlobalTheory.UU.TorsionCount.card_torsion_points _root_.GlobalTheory.globalFns_holds
        _root_.GlobalTheory.rigidity_holds))

end GlobalTheory.LN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionIsometryValuesIsTorsionLabelSystemStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem : BrGtSt → BrWpSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ n a, ν.QPt (I.ev n a) (q n a)) → Labels N D.EF I.ζ q ∧ ∀ k, 0 < k → ∀ (x : 𝓞 E) (a : D.La), ∃ z, ν.eX (q k (x • a)).1.1.toAdd = x • ν.eX (q k a).1.1.toAdd + k • z := by
  first | exact @GlobalTheory.ModelData.labels_of_tateIsoQ | exact GlobalTheory.ModelData.labels_of_tateIsoQ | (intros; apply GlobalTheory.ModelData.labels_of_tateIsoQ <;> assumption)
end

