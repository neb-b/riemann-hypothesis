module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionsPowVeryAmpleAreFormsOfClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0159
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem surjective_mulN_of_isAbelianScheme (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) (n : ℕ) (hn : (n : K) ≠ 0) : Surjective (mulN B n).left := by
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hft : LocallyOfFiniteType B.hom := inferInstance
  have : Flat (mulN B n).left :=
    MulEtaleDvr.flat_mulN_field K B n (isUnit_iff_ne_zero.2 hn) hft
  have : IsProper ((mulN B n).left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper (mulN B n).left := IsProper.of_comp _ B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : LocallyOfFinitePresentation (mulN B n).left := inferInstance
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have hc : IsClopen (Set.range (mulN B n).left) :=
    ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩

theorem abelian_torsion_finite_and_mulN_surjective :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) :=
  ⟨AbTorsionFinite.finite_torsion,
    fun K _ _ B _ hB n hn => surjective_mulN_of_isAbelianScheme K B hB n hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLifts

theorem exists_compatible_sections_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  intro R _ _ _ I hI Y β hβ hfl hpr N v hN K _ g₀ hg₀ X₀ π f₀ hπ N₀ w₀ hN₀ hw₀ h1 s₀
  have step : ∀ e (s' : LB.Sec (N e)), ∃ s : LB.Sec (N (e + 1)),
      ∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        gs (β e) z _ (s.f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
    intro e s'
    obtain ⟨j, hj, w, hw⟩ := exists_closedFibre R I Y β hβ N v hN e
    have g := (isGen_iff _).1 hw
    have g' := (isGen_iff _).1 hw₀
    obtain ⟨w'', T⟩ := exists_comp (hN 0).1 w w₀ g g' (hN (e + 1)).1 hN₀
    have hne : I ^ (e + 1 + 1) ≠ ⊤ := fun h =>
      hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero _)))
    have : Nontrivial (R ⧸ I ^ (e + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    have : IsLocalRing (R ⧸ I ^ (e + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have h := hπ.paste_horiz hj
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    exact _root_.GlobalTheory.SecLiftClosed.exists_lift (R ⧸ I ^ (e + 1 + 1)) _ (Y (e + 1)).hom (hfl (e + 1)) (hpr (e + 1)) (N (e + 1))
      (hN (e + 1)).1 K _ (hg₀.comp (Ideal.Quotient.factor_surjective _)) X₀ (π ≫ j) f₀ h N₀ w'' hN₀
      ((isGen_iff _).2 (T.pgen_comp (hN 0).1 g g')) h1 _ _ (Ideal.Quotient.factor_surjective _) _ (β e)
      (Y e).hom (hβ e) (N e) (v e) (hN e).1 (hN e).2 s'
  choose L hL using step
  exact ⟨fun e => Nat.rec (motive := fun e => LB.Sec (N e)) s₀ L e, rfl, fun e => hL e _⟩

end GlobalTheory.SecLifts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionOfVanishingAfterBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormCorr

section
open MvPolynomial

variable {X X' Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem eval₂_scale {σ A : Type} [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsHom_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsHom r z U h a = gs r z U a := (gs_eq r z U h a).symm

def cstGerm (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (gsHom p z ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_eval {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (eval₂Hom (AbLaw.cst p U) x F) = eval₂ (cstGerm (r ≫ p) z) (fun j => gs r z U (x j)) F := by
  rw [← gsHom_apply r z U h, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    exact (gsHom_apply r z U h _).trans (((gs_res r z le_top h _).trans (gs_pull r p z ⊤ trivial _)).trans
      (gsHom_apply (r ≫ p) z ⊤ trivial _).symm)
  · ext j
    exact gsHom_apply r z U h _

theorem const_comp (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem gs_sec {H : LB X} (s : LB.Sec H) (r : Z ⟶ X) (z : Z) {i j : H.ι} (hi : r z ∈ H.U i) (hj : r z ∈ H.U j) :
    gs r z _ (s.f i) = (gm r z _ (H.g i j)).val * gs r z _ (s.f j) := by
  have hm : r z ∈ H.U i ⊓ H.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (s.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

def formSec {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) {F : MvPolynomial σ R}
    {t : ℕ} (hF : F.IsHomogeneous t) : LB.Sec (AbLaw.pw H t) where
  f := fun k => eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_eval p (𝟙 X) y (H.U i) hy.1 _ F).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (congrArg Units.val (map_zpow (gm (𝟙 X) y (H.U i ⊓ H.U j)) (H.g i j) t))
      (gs_eval p (𝟙 X) y (H.U j) hy.2 _ F)).symm)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, ← eval₂_scale _ _ _ hF]
    congr 1
    exact funext fun a => gs_sec (s a) _ y hy.1 hy.2

def pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} (w : LB.Iso H' (H.pull β)) (t : ℤ) :
    LB.Iso (AbLaw.pw H' t) ((AbLaw.pw H t).pull β) := ⟨fun p => w.s p ^ t⟩

theorem gw_pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} (w : LB.Iso H' (H.pull β)) (t : ℤ) (r : Z ⟶ X') (z : Z)
    (j : H.ι) (k : H'.ι) : gw (pwIso w t) r z j k = gw w r z j k ^ t :=
  map_zpow (gm r z ((H.pull β).U (fun _ => j) ⊓ H'.U k)) (w.s (fun _ => j, k)) t

theorem pgen_pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} (hw : PGen w) (t : ℤ) :
    PGen (pwIso w t) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have e := congrArg (· ^ t) (hw Y f y j j' k k' hj hj' hk hk')
  simp only [mul_zpow, inv_zpow] at e
  refine (gw_pwIso w t f y j k).trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_))
    (gw_pwIso w t f y j' k').symm))
  · exact (map_zpow _ _ _).symm
  · exact (map_zpow _ _ _).symm

def Rel {H : LB X} {H' : LB X'} (β : X' ⟶ X) (w : LB.Iso H' (H.pull β)) (s : LB.Sec H) (s' : LB.Sec H') : Prop :=
  ∀ z (k : H.ι) (k' : H'.ι), β z ∈ H.U k → z ∈ H'.U k' →
    gs β z _ (s.f k) = (gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k')

theorem Rel.form {σ : Type} {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} {s : σ → LB.Sec H}
    {s' : σ → LB.Sec H'} (h : ∀ j, Rel β w (s j) (s' j)) (p : X ⟶ Spec (CommRingCat.of R))
    {F : MvPolynomial σ R} {t : ℕ} (hF : F.IsHomogeneous t) (z : X') (k : H.ι) (k' : H'.ι) (hk : β z ∈ H.U k)
    (hk' : z ∈ H'.U k') :
    gs β z _ (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F) = (gw w (𝟙 _) z k k' ^ (t : ℤ)).val *
      gs (𝟙 _) z _ (eval₂Hom (AbLaw.cst (β ≫ p) (H'.U k')) (fun j => (s' j).f k') F) := by
  rw [gs_eval p β z _ hk, gs_eval (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, zpow_natCast, Units.val_pow_eq_pow_val,
    ← eval₂_scale _ _ _ hF]
  congr 1
  exact funext fun j => h j z k k' hk hk'

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (AbLaw.cst p U a) = cstGerm (r ≫ p) z a := by
  have e := gs_eval (σ := Empty) p r z U h Empty.elim (MvPolynomial.C a)
  rwa [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C] at e

theorem gs_lin {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs r z U (∑ i, AbLaw.cst p U (c i) * x i) = ∑ i, cstGerm (r ≫ p) z (c i) * gs r z U (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← gsHom_apply r z _ h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, gsHom_apply, gsHom_apply, gs_cst p r z _ h]

theorem germ_rel {n : ℕ} {M : LB X} {M' : LB X'} {β : X' ⟶ X} {w : LB.Iso M' (M.pull β)} {σ : LB.Sec M}
    {σ' : LB.Sec M'} {τ : Fin n → LB.Sec M} {τ' : Fin n → LB.Sec M'} (hσ : Rel β w σ σ')
    (hτ : ∀ i, Rel β w (τ i) (τ' i)) (p : X ⟶ Spec (CommRingCat.of R)) (c : Fin n → R) (z : X') (k : M.ι)
    (k' : M'.ι) (hk : β z ∈ M.U k) (hk' : z ∈ M'.U k') :
    gs β z _ (σ.f k) = gs β z _ (∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k) ↔
      gs (𝟙 _) z _ (σ'.f k') = gs (𝟙 _) z _ (∑ i, AbLaw.cst (β ≫ p) (M'.U k') (c i) * (τ' i).f k') := by
  have e : gs β z _ (∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k) = (gw w (𝟙 _) z k k').val *
      gs (𝟙 _) z _ (∑ i, AbLaw.cst (β ≫ p) (M'.U k') (c i) * (τ' i).f k') := by
    rw [gs_lin p β z _ hk, gs_lin (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hτ i z k k' hk hk']
    ring
  rw [e, hσ z k k' hk hk', Units.mul_right_inj]

end

theorem exists_form_correction : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull β)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (β) z ∈ (H).U k → z ∈ (H').U k' → gs (β) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ F : MvPolynomial (Fin (n + 1)) A, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (β ≫ f) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous t ∧ (∀ d, g (AddMonoidAlgebra.coeff G d) = 0) ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F - G) = 0) := by
  intro A _ _ _ X f hf H n s hH hva K _ g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs₀ t h1 hsurj A' _ g X' β f' hβ H' w s'
    hH' hw hs' F hF hF0
  have hM := isLB_pw hH (t : ℤ)
  have hM' := isLB_pw hH' (t : ℤ)
  obtain ⟨m, τ, hτ⟩ := _root_.GlobalTheory.SecBasis.exists_basis A X f hf ⟨H, hH, n, s, hva⟩ (AbLaw.pw H t) hM K g₀ hg₀ X₀ π f₀ hπ
    (AbLaw.pw H₀ t) (pwIso w₀ t) (isLB_pw hH₀ _) ((isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw₀) t)) h1
  choose Q hQ hτQ using fun i => _root_.GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre A X f hf H n s hH hva K g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs₀ t h1
    hsurj (τ i)
  have hL := LB.isLB_pull hM (𝟙 X)
  have hu := CubePf.idIsoL_isGen hL
  choose P hP using fun σ => GlobalTheory.SecPullIso.exists_pull (𝟙 X) (AbLaw.pw H t) _ _ hM hL hu σ
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨c, hc, -⟩ := hτ A (RingHom.id A) X (𝟙 X) f hid _ _ (fun i => P (τ i)) hL hu (fun i => hP (τ i))
    (P (formSec f s hF))
  have hc' : ∀ k, (formSec f s hF).f k = ∑ i, AbLaw.cst f ((AbLaw.pw H t).U k) (c i) * (τ i).f k := fun k =>
    fn_ext fun z hz => by
      obtain ⟨k', hk'⟩ := exists_chart hL z
      refine (germ_rel (hP _) (fun i => hP (τ i)) f c z k k' hz hk').2 ?_
      rw [Category.id_comp]
      exact congrArg _ (hc k')
  have hw' := (isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw) (t : ℤ))
  choose τ' hτ' using fun i => GlobalTheory.SecPullIso.exists_pull β (AbLaw.pw H t) _ _ hM hM' hw' (τ i)
  have hrel : Rel β (pwIso w t) (formSec f s hF) (formSec (β ≫ f) s' hF) := fun z k k' hk hk' =>
    (Rel.form hs' f hF z k k' hk hk').trans
      (congrArg (· * _) (congrArg Units.val (gw_pwIso w t (𝟙 _) z k k').symm))
  have hc'' : ∀ k', (formSec (β ≫ f) s' hF).f k' =
      ∑ i, AbLaw.cst f' ((AbLaw.pw H' t).U k') (g (c i)) * (τ' i).f k' := fun k' =>
    Eq.trans (fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM (β z)
      exact (germ_rel hrel hτ' f c z k k' hk hz).1 (congrArg _ (hc' k))) (by
      rw [hβ.w, const_comp]
      rfl)
  have hgc : (fun i => g (c i)) = 0 :=
    (hτ A' g X' β f' hβ _ _ τ' hM' hw' hτ' (formSec (β ≫ f) s' hF)).unique hc'' fun k' =>
      (hF0 k').trans (Finset.sum_eq_zero fun i _ =>
        (congrArg (· * (τ' i).f k') (map_zero (AbLaw.cst f' ((AbLaw.pw H' t).U k')))).trans (zero_mul _)).symm
  refine ⟨∑ i, MvPolynomial.C (c i) * Q i,
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (hQ i).C_mul _, fun d => ?_, fun k => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [MvPolynomial.coeff_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [MvPolynomial.coeff_C_mul, map_mul, congrFun hgc i, Pi.zero_apply, zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, sub_eq_zero, map_sum]
      refine (hc' k).trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_mul, MvPolynomial.eval₂Hom_C, hτQ i k]
      rfl

end GlobalTheory.FormCorr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_kTriv : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → GlobalTheory.AbLaw.IsProjBy G.hom → KTriv A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → KTriv G' L' := by
  intro hG R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hA h hL hL₀ hw hP hk
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ G L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R G hA hP L _ hL hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ G), GlobalTheory.UU.InK G L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (GlobalTheory.UU.inK_one hL (𝟙_ _))
  have hprop := hA.proper
  have hH' : IsProper H.hom := by rw [← Over.w j]; infer_instance
  have hsec : e.left ≫ H.hom = 𝟙 (Sp R) := Over.w e
  have hcl : IsClosedImmersion e.left := by
    have : IsClosedImmersion (e.left ≫ H.hom) := by
      rw [hsec]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp R)))
    exact IsClosedImmersion.of_comp e.left H.hom
  obtain ⟨a, ha, key⟩ := GlobalTheory.T.closed_immersion_generic_unit_locus R K _ _ e.left H.hom hcl inferInstance inferInstance (fun B _ y t hy => by
    have hdi : (y ≫ j.left) ≫ G.hom = t ≫ spMap (algebraMap R K) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ A := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (algebraMap R K)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := GlobalTheory.UU.InK.eq_one hk (GlobalTheory.UU.inK_of_push h hL hL₀ hw x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : toUnit _ ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, he, MonObj.comp_one]
    exact ⟨(toUnit (Over.mk (t ≫ spMap (algebraMap R K)))).left, congrArg (fun q => q.left) h1⟩)
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' hw' B _ t x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hrep _ _).1 (GlobalTheory.KTrivSpread.memKL_push h' hL hL' hw' t x hx)
  obtain ⟨y, hy⟩ := key R' g hg _ z.left t (Over.w z)
  let u : Over.mk (t ≫ spMap g) ⟶ 𝟙_ (Over (Sp R)) := Over.homMk y (by
    have := Over.w z
    rw [← hy, Category.assoc, hsec] at this
    exact this)
  have hu : u ≫ e = z := Over.OverMorphism.ext hy
  have h1 : pushPt h'.1.w x = pushPt h'.1.w (1 : Over.mk t ⟶ G') := by
    refine Eq.trans ?_ (map_one (pushHom h' (Over.mk t))).symm
    rw [← hz, ← hu, Category.assoc, he, MonObj.comp_one]
  exact Over.OverMorphism.ext (h'.1.hom_ext (congrArg (fun q => q.left) h1) (by rw [Over.w, Over.w]))

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.NeutralLevel

theorem isGrpPullback_of_iso_inv {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (e : (Over.pullback f).obj G ≅ G') (he : IsMonHom e.hom) :
    IsGrpPullback G' G f (e.inv.left ≫ pullback.fst G.hom f) :=
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G f)).congr (Category.id_comp _) rfl

theorem exists_extension {S S' T : Scheme.{0}} {f : S' ⟶ S} {j : T ⟶ S'} {G : Over S} {G' : Over S'} {A : Over T}
    [GrpObj G] [GrpObj G'] [GrpObj A] {φ : G'.left ⟶ G.left} {ψ : A.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (hA : IsGrpPullback A G' j ψ) (c : ℕ)
    (hc : ∀ a : 𝟙_ (Over T) ⟶ A, ∃ s : 𝟙_ (Over S') ⟶ G', j ≫ s.left = (a ^ c).left ≫ ψ)
    (t : T ⟶ S) (ht : t = j ≫ f) (y : Over.mk t ⟶ G) :
    ∃ s : S' ⟶ G.left, s ≫ G.hom = f ∧ j ≫ s = (y ^ c).left := by
  have H := hA.comp h
  obtain rfl : t = (𝟙_ (Over T)).hom ≫ j ≫ f := ht.trans (Category.id_comp _).symm
  let a : 𝟙_ (Over T) ⟶ A := Over.homMk (H.1.lift y.left (𝟙_ (Over T)).hom (Over.w y)) (H.1.lift_snd _ _ _)
  have ha : pushHom H _ a = y := Over.OverMorphism.ext (H.1.lift_fst _ _ _)
  obtain ⟨s, hs⟩ := hc a
  refine ⟨s.left ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, h.1.w, ← Category.assoc, Over.w s]
    exact Category.id_comp _
  · rw [← ha, ← map_pow, ← Category.assoc]
    exact (congrArg (· ≫ φ) hs).trans (Category.assoc _ _ _)

theorem exists_ampleCub_fibre {S S' T : Scheme.{0}} {f : S' ⟶ S} (j : T ⟶ S') {G : Over S} {G' : Over S'}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)
    (L : LB ((Over.pullback j).obj G').left) (hL : AmpleCub ((Over.pullback j).obj G') L)
    (t : T ⟶ S) (ht : j ≫ f = t) :
    ∃ N : LB ((Over.pullback t).obj G).left, AmpleCub ((Over.pullback t).obj G) N := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G t)
    (((isGrpPullback_pullback G' j).comp h).congr ht rfl)
  exact _root_.GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso _ _ _ e he L hL

theorem smoothOfRelativeDimension_model {K W : Type} [Field K] [CommRing W] [IsDomain W]
    [Algebra K (FractionRing W)] (P : Out.PolAV (Sp K)) (G : Over (Sp W)) [GrpObj G] (hG : SmConn G)
    (hm : IsModel (L := FractionRing W) P.A G) : SmoothOfRelativeDimension P.g G.hom := by
  obtain ⟨e, -⟩ := hm
  obtain ⟨-, _, -, -, _⟩ := hG
  refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic W G P.g ?_
  have w : e.hom.left ≫ _ = pullback.snd G.hom (Out.jK W) := Over.w e.hom
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGrpPullback_pullback P.A (spMap (algebraMap K (FractionRing W)))).1 P.smoothDim)

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_level_model : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  intro V K _ _ _ _ _ _ R K' _ _ _ _ _ _ _ hR hc P
  have : IsFractionRing R K' := hR.2.2.2
  let f := spMap (algebraMap K K')
  let P' : Out.PolAV (Sp K') :=
    have h := isGrpPullback_pullback P.A f
    have hL' := LB.isLB_pull P.isLB (pullback.fst P.A.hom f)
    have hw := (isGen_iff _).1 (PolBaseChange.lbIso_refl hL').choose_spec
    { A := (Over.pullback f).obj P.A
      isAb := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback f P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull (pullback.fst P.A.hom f)
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨G', _, hG', he, c, hc1, hext⟩ := _root_.GlobalTheory.SS.exists_neutral_group_model R K' hR P'.A P'.isAb
    (GlobalTheory.AbProj.isProjBy_of_isPullback P' (IsPullback.id_horiz _))
  obtain ⟨L', hL'⟩ := GlobalTheory.SS.exists_ampleCub_spFibre R K' hR P' G'.Y hG' G'.e he
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R K' hc P.A P.isAb G'.Y hG' ⟨G'.e, he⟩
  refine ⟨s, c, hc1, fun W hW hsW hl => ?_⟩
  obtain ⟨G, _, _, ε, hG, hε, hcomm, hm⟩ := hs W hW hsW hl
  have h := isGrpPullback_of_iso_inv _ G ε hε
  have hA := isGrpPullback_of_iso_inv _ G'.Y G'.e he
  exact ⟨G, inferInstance, FractionRing W, inferInstance, inferInstance, inferInstance, inferInstance, hG, hcomm, hm,
    smoothOfRelativeDimension_model P G hG hm,
    exists_ampleCub_fibre _ h L' hL' _ (spMap_comp_spMap _ _),
    fun y => exists_extension h hA c hext _ (spMap_comp_spMap _ _).symm y⟩

end GlobalTheory.NeutralLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoordinates_exist_unique_separate_points : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (s : Sp K ⟶ S) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (Ix : Type) (x : Ix → (Over.mk s ⟶ P.A)), (∀ i, x i ^ m ^ 2 = 1) → (∀ z, ∃ v : Ix → K, IsCoordPt P m x z fun i => fnOf (v i)) ∧ (∀ z (v v' : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → ((IsCoordPt P m x z fun i => fnOf (v' i)) ↔ ∃ c : Kˣ, v' = (c : K) • v)) ∧ (∀ v : Ix → K, (IsThetaPt P m x fun i => fnOf (v i)) ↔ IsCoordPt P m x 1 fun i => fnOf (v i)) ∧ (3 ≤ m → (∀ y : Over.mk s ⟶ P.A, y ^ m ^ 2 = 1 → ∃ i, x i = y) → ∀ z z' (v : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → (IsCoordPt P m x z' fun i => fnOf (v i)) → z = z' ∧ v ≠ 0) := by
  first | exact @GlobalTheory.CoordSep.coord_exists_unique_separate | exact GlobalTheory.CoordSep.coord_exists_unique_separate | (intros; apply GlobalTheory.CoordSep.coord_exists_unique_separate <;> assumption)
end

