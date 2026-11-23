module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Defs
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

def ThG (m : ℕ) {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (x : T ⟶ G) (c : Γ(T.left, ⊤)) : Prop :=
  x ^ (m ^ 2) = 1 ∧ ∃ (t : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T))
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, (snd T G ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T)) (θ : ThetaGrp G L ((m ^ 2 : ℕ) : ℤ) T),
    α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT G 1).left) (rigT G L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull G L (mulT G _ m) (snd _ G ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift G L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf G L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good L z J → VVRank.sv G t (ptSecT G 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (rigT G L ρ T ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val

def NZ {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) : Prop :=
  ∃ g : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left g = closedPoint V ∧ g ∈ nonzeroLocus σ

def UnivBasis {K : Type} [CommRing K] (x : Sp K ⟶ S) (e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [CommRing K'] (i : K →+* K') (x' : Sp K' ⟶ S) (h : spMap i ≫ x = x') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')),
    ∃! c : Γ((Over.mk x').left, ⊤),
      s = c • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)


variable {G L} in
def IsRigidificationPullbackCompatibleIso {S' : Scheme.{0}} {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left} {L' : LB A.left} (w : LB.Iso L' (L.pull φ))
    (f : S' ⟶ S) (ρ' : LB.Gen (L'.pull (eSec A))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (J) (J'), Good L z J → Good L' z J' →
    val (L := L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ (r ≫ f) z J =
      wVal w z J J' (r ≫ eSec A) * val (L := L') (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ' r z J'
end Defs

theorem thG_iff {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : GlobalTheory.UT.SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (c : F) :
    ThG A.A A.L ρ m th x (fnOf c) ↔ x ^ (m ^ 2) = 1 ∧ ∃ t, GlobalTheory.UT.ThC A ρ m th x t c := Iff.rfl

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
  {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}

theorem val_rigT (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T₀.left) (z : Z) {J} (hJ : Good L₀ z J) :
    val (rigT G L₀ ρ₀ T₀ k) r z J =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J ^ k := by
  have hz := hJ.mem (fun _ : Fin 1 => T₀.hom ≫ eSec G) r
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J
    (fun _ => J (r ≫ T₀.hom ≫ eSec G)) (fun _ => by rw [Category.assoc])]
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hz _).trans (gm_pull r T₀.hom z _ (rigT_le G L₀ _ hz) _)


include hτ in
theorem IsRigidificationPullbackCompatibleIso.rigT (h : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'}
    (hJ : Good L₀ z J) (hJ' : Good L₁ z J') : val (rigT G L₀ ρ₀ T₀ k) (r ≫ τ) z J =
      wVal w z J J' (r ≫ T.hom ≫ eSec A) ^ k * val (rigT A L₁ ρ₁ T k) r z J' := by
  rw [val_rigT k _ z hJ, val_rigT k _ z hJ', Category.assoc, hτ, ← Category.assoc, h _ _ z J J' hJ hJ', mul_zpow,
    Category.assoc]

theorem norm_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ} {a : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
      val α₀ (r ≫ psi hp τ hτ) z J = (wVal w z J J' (r ≫ (snd T A).left) ^ a *
        wVal w z J J' (r ≫ (snd T A ^ m).left) ^ (-((1 : ℕ) : ℤ))) * val α r z J')
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J') :
    val α₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = val (Out.rigT G L₀ ρ₀ T₀ (a - 1)) (r ≫ τ) z J ↔
      val α (r ≫ (ptSecT A 1).left) z J' = val (Out.rigT A L₁ ρ₁ T (a - 1)) r z J' := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    H _ _ _ _ _ hJ hJ', Category.assoc, Category.assoc, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, ← zpow_add,
    show a + -((1 : ℕ) : ℤ) = a - 1 from rfl, mul_right_inj]

theorem value_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {a : ℤ} {t₀ : LB.Sec (LPow G L₀ a T₀)} {t : LB.Sec (LPow A L₁ a T)}
    (ht : SecRel hp τ hτ w t t₀) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J')
    (c : Z.presheaf.stalk z) :
    VVRank.sv G t₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = c * (val (Out.rigT G L₀ ρ₀ T₀ a) (r ≫ τ) z J).val ↔
      VVRank.sv A t (r ≫ (ptSecT A 1).left) z J' = c * (val (Out.rigT A L₁ ρ₁ T a) r z J').val := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    ht _ _ _ _ _ hJ hJ', Category.assoc, NormTheta.ptSec_snd, Units.val_mul, mul_left_comm, Units.mul_right_inj]

theorem value_at {a : ℤ} {t : LB.Sec (LPow A L₁ a T)} {c : Γ(T.left, ⊤)} (hL₁ : L₁.IsLB)
    (h : ∀ z J, Good L₁ z J → VVRank.sv A t (ptSecT A 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) (𝟙 _) z J).val)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L₁ z J) :
    VVRank.sv A t (r ≫ (ptSecT A 1).left) z J = gs r z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) r z J).val :=
  sv_of_isValueAt (x := (1 : T ⟶ A)) (ρ := Out.rigT A L₁ ρ₁ T a) (isValueAt_of_sv hL₁ fun y J hJ => by
    rw [Category.id_comp]; exact h y J hJ) r z hJ

theorem ThG.move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T₀.left, ⊤)} (H : ThG G L₀ ρ₀ m th₀ x₀ c) : ThG A L₁ ρ₁ m th x (τ.appTop.hom c) := by
  obtain ⟨-, t₀, α₀, s₀, θ₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨t, ht⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ t₀
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α₀ h₁
  obtain ⟨θ, hθ, hθ'⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn h₄
  refine ⟨hn, t, α, s, θ, hα, corr_of_val hL₁ fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅, fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    rw [val_pull hJ']
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').1 ((val_pull hJ _ _ _).symm.trans (val_corr hJ h₂ _))
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := (value_iff hp τ hτ hr ht (𝟙 _) y hJ hJ' _).1 (value_at hL₀ h₆ (𝟙 _ ≫ τ) y hJ)
    rw [Category.id_comp (ptSecT A 1).left] at q
    exact q.trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)

theorem ThG.up [IsIso τ] [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x₀ ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T.left, ⊤)} (H : ThG A L₁ ρ₁ m th x c) : ThG G L₀ ρ₀ m th₀ x₀ ((inv τ).appTop.hom c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s
  obtain ⟨t₀, ht⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ t
  obtain ⟨α₀, hα, vα⟩ := ThetaPtUp.exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α h₁
  obtain ⟨θ₀, hθ, hθ'⟩ := ThetaPtUp.symLift_up hp τ hτ hw hL₀ hL₁ hx h₀ h₄
  refine ⟨hn, t₀, α₀, s₀, θ₀, hα, corr_of_val hL₀ fun y J hJ => ?_,
    ThetaPtUp.isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅,
    fun y J hJ => ?_⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    rw [val_pull hJ, ← IsIso.inv_hom_id τ]
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').2 ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' h₂ _))
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := (value_iff hp τ hτ hr ht (inv τ) y hJ hJ' _).2 (value_at hL₁ h₆ (inv τ) y hJ')
    rw [IsIso.inv_hom_id, Category.id_comp] at q
    exact q.trans (congrArg (· * _) ((gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])).symm)

theorem ThG.smul (hL₁ : L₁.IsLB) {m : ℕ} {x : T ⟶ A} {th th' : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {a c : Γ(T.left, ⊤)}
    (h : SecM.ofSec A th' = a • SecM.ofSec A th) (H : ThG A L₁ ρ₁ m th x c) : ThG A L₁ ρ₁ m th' x (a * c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  have tw : ∀ {p q : ℤ} {κ : T ⊗ A ⟶ A} {β} (_ : β.IsGen) {u u' : LB.Sec (LPow A L₁ q T)} {v : LB.Sec (LPow A L₁ p T)},
      SecM.ofSec A u' = a • SecM.ofSec A u → IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u v →
      IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u' (SecM.toSec A (a • SecM.ofSec A v)) := by
    intro p q κ β hβ u u' v hu hv
    refine VVRank.isTwistPull_of_sv A hL₁ hβ fun y J hJ => ?_
    have e₁ := sv_of_eq_mul (s := u') (t := u) (c := a) (fun j => congrArg (fun q => q.1 j) hu)
      (𝟙 _ ≫ (lift (fst T A) κ).left) y hJ
    have e₂ := sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A v)) (t := v) (c := a) (fun j => rfl) (𝟙 _) y hJ
    rw [e₁, e₂, VVRank.sv_of_isTwistPull A hv (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, lift_fst, mul_left_comm]
  refine ⟨h₀, SecM.toSec A (a • SecM.ofSec A t), α, SecM.toSec A (a • SecM.ofSec A s), θ, h₁, h₂, tw h₁ h h₃, h₄,
    tw θ.isGen rfl h₅, fun y J hJ => ?_⟩
  rw [sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A t)) (t := t) (c := a) (fun j => rfl) _ y hJ, h₆ y J hJ,
    ptSecT_fst, ← _root_.mul_assoc, gs_mul _ y ⊤ trivial]


include hp in
theorem exists_rigidificationPullbackCompatibleIso (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hρ : ρ₀.IsGen) :
    ∃ ρ₁ : LB.Gen (L₁.pull (eSec A)), ρ₁.IsGen ∧ IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀ := by
  have e : eSec A ≫ φ = f ≫ eSec G := by
    have := over_one hp (T := baseOver S') (T₀ := baseOver S) f ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (f ≫ ·) (Category.id_comp _)))
  obtain ⟨ρ₁, h₁, h₂⟩ := exists_gen_through (φ' := fun _ : PUnit => eSec A) (φ := fun _ : PUnit => eSec G)
    (ε := fun _ => 1) (h := f) hw hL₀ hL₁ (fun _ => e) ρ₀ hρ
  exact ⟨ρ₁, h₁, fun Z r z J J' hJ hJ' => (h₂ Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])⟩

end Move

theorem ThG.unique (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} {m : ℕ} (hm : Odd m) (hu : IsUnit ((m ^ 2 : ℕ) : Γ(S, ⊤))) {T : Over S}
    {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {x : T ⟶ P.A} {c c' : Γ(T.left, ⊤)} (H : ThG P.A P.L ρ m th x c)
    (H' : ThG P.A P.L ρ m th x c') : c = c' := by
  obtain ⟨hx, t, α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ := H
  obtain ⟨-, t', α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩ := H'
  have hL := P.isLB
  obtain ⟨-, huniq⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns P.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  obtain rfl : s₁ = s₁' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A hs₁ _ y hJ).trans
      (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull P.A hs₁' _ y hJ).symm))
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  obtain rfl : t = t' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A ht _ y hJ).trans
      (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull P.A ht' _ y hJ).symm))
  refine fn_ext (V := ⊤) fun y _ => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL y
  exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSums
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ArcSeries

section Comp
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def homComp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x)) :
    NumD.Hom k N N'' :=
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  { φ := I'.φ.comp I.φ
    h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
    h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
    θ_eq x y u := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.θ_eq x y u)
      have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    σ_eq x := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.σ_eq x)
      have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
      apply Additive.ofMul.injective
      simp only [e, map_mul, map_inv, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    lam := I'.lam * Units.map g.toMonoidHom I.lam
    th_eq x := by
      rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq, hk]
      simp only [Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      ring
    e := I.e.trans I'.e
    c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
    ψ_eq χ := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.ψ_eq χ)
      have b := congrArg Additive.ofMul (I'.ψ_eq (I.e χ))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq] at a b ⊢
      linear_combination (norm := abel) a + b }

theorem homComp_rel (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x))
    {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b) (h' : I'.Rel b c) : (homComp I I' k hk).Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  have p := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (h.2 χ)
  have q := congrArg Additive.ofMul (h'.2 (I.e χ))
  apply Additive.ofMul.injective
  simp only [homComp, e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq, h.1] at p q ⊢
  linear_combination (norm := abel) p + q
end Comp

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]; exact Iff.rfl⟩

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  have : IsIntegral S x := hx.map_of_comp_eq ((algebraMap R K).codRestrict S h) (RingHom.id K) rfl
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

theorem exists_map {O O₁ K : Type} [CommRing O] [CommRing O₁] [Field K] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (io : O₁ →+* K)
    (hio : ∀ a, io (algebraMap O O₁ a) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {k : ℕ} (hk : 0 < k) {t : K}
    (ht : t ^ k = algebraMap (PowerSeries O) K PowerSeries.X) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (Φ : PowerSeries O₁ →+* K), Module.Finite (PowerSeries O) R₁ ∧
      (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ R₁ := by
  obtain ⟨Φ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free O O₁ K (algebraMap _ K) io hio
  obtain ⟨Φ, h4, h5, h6⟩ := _root_.GlobalTheory.exists_ringHom_powerSeries_root O₁ K Φ₁ k t hk (ht.trans h2.symm)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := O₁)
  refine ⟨Algebra.adjoin _ (io '' s ∪ {t}), Φ, Algebra.finite_adjoin_of_finite_of_isIntegral
    ((s.finite_toSet.image _).union (Set.finite_singleton _)) ?_, fun a => (h4 a).trans (h1 a), h5, fun f => ?_⟩
  · rintro x (⟨a, -, rfl⟩ | rfl)
    · exact (Algebra.IsIntegral.isIntegral (R := O) a).map_of_comp_eq PowerSeries.C io (RingHom.ext fun a => (hio a).symm)
    · exact IsIntegral.of_pow hk (ht ▸ isIntegral_algebraMap)
  · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h6 f)
    rintro x (⟨g, rfl⟩ | rfl)
    · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h3 g)
      rintro x (⟨g, rfl⟩ | ⟨a, rfl⟩)
      · exact Subalgebra.algebraMap_mem _ g
      · have ha : a ∈ Submodule.span O (s : Set O₁) := hs ▸ Submodule.mem_top
        change io a ∈ Algebra.adjoin (PowerSeries O) (io '' s ∪ {t})
        induction ha using Submodule.span_induction with
        | mem x hx => exact Algebra.subset_adjoin (.inl ⟨x, hx, rfl⟩)
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ a b => rw [map_add]; exact add_mem a b
        | smul c x _ a => rw [Algebra.smul_def, map_mul, hio]; exact mul_mem (Subalgebra.algebraMap_mem _ _) a
    · exact Algebra.subset_adjoin (.inr rfl)

def Sums {R K F : Type} [CommRing R] [Field K] [Field F] [Algebra R K] (X : R) (io : F →+* K) (N : NumD F)
    (be : LinearMap.BilinForm ℤ N.X) (m j : ℕ) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j) (t : Kˣ)
    (v w : La → K) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
    (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) → ‖gam (algebraMap R K X)‖ < 1 →
    ∀ (N' : NumD C) (I : NumD.Hom (gam.comp io) N N') (k : ℕ) (β : N'.Form k), I.lam = 1 →
    (∀ y z, β.be (I.e y) (I.e z) = be y z) → ∀ u rm rj : Cˣ, (u : C) = gam (algebraMap R K X) →
    (rm : C) = gam (t ^ j : Kˣ) → (rj : C) = gam (t ^ m ^ 2 : Kˣ) →
    ∀ (q' : La → N'.QT (m ^ 2)) (p : La → (N'.twist β u).QT (m ^ 2)),
    (∀ x, (q' x).1.1.toAdd = I.e (q x).1.1.toAdd ∧ I.Rel (q x).1.2 (q' x).1.2) → (∀ x, TwRel β u rm (q' x) (p x)) →
    (∀ x, gam (v x) = (N'.twist β u).tx m (p x)) ∧
    ∀ (qz' : N'.QT j) (pz : (N'.twist β u).QT j), qz'.1.1.toAdd = I.e qz.1.1.toAdd → I.Rel qz.1.2 qz'.1.2 →
      TwRel β u rj qz' pz → ∃ s : Cˣ, ∀ x, gam (w x) = s * (N'.twist β u).ev m (p x) pz.1.2

theorem exists_sums {O O₁ K F : Type} [CommRing O] [CommRing O₁] [Field K] [Field F] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (f : O₁ →+* F) (io : F →+* K)
    (hio : ∀ a, io (f (algebraMap O O₁ a)) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {N : NumD F}
    (be : LinearMap.BilinForm ℤ N.X) {m j : ℕ} (hm : Odd m) (hj : 0 < j) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j)
    (t : Kˣ) (ht : (t : K) ^ (m ^ 2 * j) = algebraMap (PowerSeries O) K PowerSeries.X) {N₀ : NumD O₁}
    (I₀ : NumD.Hom f N₀ N) (hl : I₀.lam = 1)
    (hq : ∀ x, ∃ p₀ : N₀.QT (m ^ 2), (q x).1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 (q x).1.2)
    (hz : ∃ p₀ : N₀.QT j, qz.1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 qz.1.2) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (v w : La → K), Module.Finite (PowerSeries O) R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O) io N be m j q qz t v w := by
  have hk : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  obtain ⟨R₁, Φ, hR, h1, h2, h3⟩ := exists_map (io.comp f) hio hk ht
  choose p₀ hp hp' using hq
  obtain ⟨q₀, hz, hz'⟩ := hz
  let be₀ : LinearMap.BilinForm ℤ N₀.X := be.comp I₀.e.toAddMonoidHom.toIntLinearMap I₀.e.toAddMonoidHom.toIntLinearMap
  let s : ℕ := ((m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd)).toNat
  refine ⟨R₁, fun x => Φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x)),
    fun x => Φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x) q₀ s), hR, fun x => h3 _, ?_⟩
  intro C _ _ _ gam g1 g2 N' I k β hI hβ u rm rj hu hrm hrj q' p hq' hp''
  obtain ⟨S, hS⟩ := exists_ball C
  have n1 : ∀ g, ‖(gam.comp Φ) g‖ ≤ 1 := fun g => (hS _).1 (mem_of_isIntegral (S.comap gam)
    (fun r => (hS _).2 (g1 r)) ((Algebra.IsIntegral.isIntegral (⟨_, h3 g⟩ : R₁)).map R₁.val))
  have n2 : ‖(gam.comp Φ) PowerSeries.X‖ < 1 := by
    rw [← ht, map_pow, norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hk.ne'] at g2
    rwa [RingHom.comp_apply, h2]
  let t' : Cˣ := Units.map gam.toMonoidHom t
  let J := homComp I₀ I ((gam.comp Φ).comp PowerSeries.C) fun x => congrArg gam (h1 x)
  have hJ : J.lam = 1 := by
    change I.lam * Units.map _ I₀.lam = 1
    rw [hI, hl, map_one, mul_one]
  have e1 : t' ^ j = rm := Units.ext (by rw [hrm, ← map_pow]; rfl)
  have key := fun x => _root_.GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root O₁ C (gam.comp Φ) n1 n2 t' u rm rj m j hm hj (congrArg gam h2.symm) e1
    (Units.ext (by rw [hrj, ← map_pow]; rfl))
    (Units.ext (by rw [hu, ← e1, ← pow_mul, mul_comm j, ← ht, ← map_pow, map_pow gam]; simp))
    N₀ N' J k be₀ β (fun y z => hβ _ _) (p₀ x) (q' x) (p x) ((hq' x).1.trans (congrArg I.e (hp x)))
    (homComp_rel _ _ _ _ (hp' x) (hq' x).2) (hp'' x)
  refine ⟨fun x => ?_, fun qz' pz a b c => ⟨(J.lam * J.h q₀.1.2.b ^ (m ^ 2))⁻¹ * t' ^ s, fun x => ?_⟩⟩
  · rw [(key x).1, hJ, Units.val_one, one_mul]; rfl
  · have := (key x).2 q₀ qz' pz (a.trans (congrArg I.e hz)) (homComp_rel _ _ _ _ hz' b) c s (Int.self_le_toNat _)
    rw [Units.val_mul, mul_assoc, Units.val_pow_eq_pow_val, this, Units.inv_mul_cancel_left]; rfl

end GlobalTheory.ArcSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.FullPoint.fullAt_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (o : Full D K) :
    FullAt Y y o ↔ FullPoint.IsFibre Y.oF y o ∧ ∀ f : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap f →
      o.ρ = f (baseKA l).ρ ∧ (o.I.ζ l.A : K) = f (baseKA l).ζ :=
  ⟨fun ⟨φ, a, b, c, d, e, f⟩ => ⟨⟨φ, a, b, c, d, e⟩, f⟩, fun ⟨⟨φ, a, b, c, d, e⟩, f⟩ => ⟨φ, a, b, c, d, e, f⟩⟩

theorem GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  intro hv _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y K _ _ bF
  refine ⟨fun o hρ hζ => ?_, fun y => ?_, fun K' _ f y o o' h h' => ?_⟩
  · obtain ⟨y, ⟨h₁, h₂⟩, hu⟩ := FullPoint.existsUnique_point hv.1.1 Y bF o hρ hζ
    refine ⟨y, ⟨h₁, (FullPoint.fullAt_iff Y y o).2 ⟨h₂, fun f hf => ?_⟩⟩,
      fun y' h => hu y' ⟨h.1, ((FullPoint.fullAt_iff Y y' o).1 h.2).1⟩⟩
    rw [pullback.condition, ← Category.assoc, h₁, ← spMap_comp] at hf
    obtain rfl := FullPoint.spMap_inj hf
    exact ⟨hρ _ rfl, hζ _ rfl⟩
  · obtain ⟨o, h⟩ := FullPoint.exists_isFibre Y.oF y
    exact ⟨o, (FullPoint.fullAt_iff Y y o).2 h⟩
  · obtain ⟨hρ, hζ, ψ, g₁, g₂, g₃, g₄⟩ := h'
    obtain ⟨h₁, h₂⟩ := (FullPoint.fullAt_iff Y y o).1 h
    refine (FullPoint.fullAt_iff Y _ o').2 ⟨FullPoint.IsFibre.ext f h₁ ψ g₁ g₂ g₃ g₄, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap j :=
      ⟨(Spec.preimage (y ≫ pullback.fst _ _ ≫ Xo.s)).hom, (Spec.map_preimage _).symm⟩
    rw [Category.assoc, hj, ← spMap_comp] at hg
    obtain rfl := FullPoint.spMap_inj hg
    rw [hρ, hζ _ l.A_pos, (h₂ j hj).1, (h₂ j hj).2]
    exact ⟨rfl, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionPolarizedCMObjectExtendsAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.FullExtend

theorem main : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K), ∃ o' : Full D K', FullExt f o o' ∧ (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧ ∀ m j z v, 0 < j → o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  intro hV _ _ _ _ _ _ E _ _ _ H D K K' _ _ _ _ _ f o
  obtain ⟨o', h₁, h₂, h₃⟩ := exists_fullExt hV.1.1 D f o
  exact ⟨o', h₁, h₂, fun m j z v _ => h₃ m j z v⟩

end GlobalTheory.FullExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFramePull
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.Mono

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨_, fun Z r z J hJ => ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem isFrame_pull {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {R₁ R₂ : Type} [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂)
    (hh : ∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) (x : Sp (FractionRing R₁) ⟶ S)
    (x' : Sp (FractionRing R₂) ⟶ S) (hx : spMap h' ≫ x = x') {n : ℕ} (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)))
    (hf : GlobalTheory.LN.IsFrame G L N x f) : ∃ f', GlobalTheory.LN.IsFrame (n := n) G L N x' f' := by
  let ρ : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap h') hx
  have e : ∀ _ : Fin 1, (ρ ▷ G).left ≫ (snd (Over.mk x) G).left = (snd (Over.mk x') G).left := fun _ => by
    rw [← Over.comp_left, whiskerRight_snd]
  choose f' hf' using fun i => exists_pull (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk x) G).left)
    (φ' := fun _ : Fin 1 => (snd (Over.mk x') G).left) (ε := fun _ => (N : ℤ)) (f i) (ρ ▷ G).left e
  refine ⟨f', fun W _ _ _ hW φ gam hg χ hχ => ?_⟩
  have hχ' : spMap (gam.comp h') ≫ x = jK W ≫ χ := by rw [sp_comp, Category.assoc, hx, hχ]
  obtain ⟨b', hb, hs⟩ := hf W hW (φ.comp h) (gam.comp h') (fun r => by
    rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ hχ'
  refine ⟨b', hb, fun i => ?_⟩
  obtain ⟨s, h₁, h₂⟩ := hs i
  refine ⟨s, fun z J hJ => (h₁ z J hJ).trans ?_, h₂⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  refine congrArg _ (Eq.trans ?_ (hf' i _ _ z J hJ).symm)
  have hc : (Over.homMk (spMap (gam.comp h')) hχ' : Over.mk (jK W ≫ χ) ⟶ Over.mk x) =
      (Over.homMk (spMap gam) hχ : Over.mk (jK W ≫ χ) ⟶ Over.mk x') ≫ ρ := Over.OverMorphism.ext (sp_comp h' gam)
  rw [hc, comp_whiskerRight, Over.comp_left]

theorem mono : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), h.Finite → (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) → (GlobalTheory.LN.TraitData Y a g y₁ → GlobalTheory.LN.TraitData Y a (h.comp g) (spMap h' ≫ y₁)) ∧ (RealAt Y a g y₁ → RealAt Y a (h.comp g) (spMap h' ≫ y₁)) ∧ ∀ (N n : ℕ) f, GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N (y₁ ≫ Y.j) f → ∃ f', GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N ((spMap h' ≫ y₁) ≫ Y.j) f' := by
  intro _ _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ R₁ _ _ g y₁ _ _ _ R₂ _ _ h h' hfin hh
  refine ⟨fun hT => ⟨?_, fun W _ _ _ hW φ gam hg χ hχ => ?_⟩, fun hR => hR.comp h h' hfin hh,
    fun N n f hf => isFrame_pull _ _ N h h' hh _ _ (Category.assoc _ _ _).symm f hf⟩
  · have e : spMap h' ≫ jK R₁ = jK R₂ ≫ spMap h :=
      (sp_comp (algebraMap R₁ _) h').symm.trans ((congrArg spMap (RingHom.ext hh)).trans (sp_comp h (algebraMap R₂ _)))
    rw [Category.assoc, hT.1, sp_comp, ← Category.assoc, e]
    simp only [Category.assoc]
  · exact hT.2 W hW (φ.comp h) (gam.comp h') (fun r => by rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ
      (by rw [sp_comp, Category.assoc, ← hχ, Category.assoc])

end GlobalTheory.Ex.Mono
end
end

