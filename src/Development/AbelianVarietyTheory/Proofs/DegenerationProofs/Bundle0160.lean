module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0159
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionLiftClosedBaseChangeOfH1Vanishes
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecLiftClosed

variable {X Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem gs_comb {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (W : X.Opens) (hz : r z ∈ W)
    (c : Fin n → R) (u : Fin n → Γ(X, W)) :
    gs r z W (∑ i, AbLaw.cst p W (c i) * u i) =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) * gs r z W (u i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hz _).symm.trans ((gs_mul r z _ hz _ _).trans ?_)
  exact congrArg (· * _) ((gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _))

theorem gs_const_comp (q : Z ⟶ Spec (CommRingCat.of R')) (h : R →+* R') (z : Z) (a : R) :
    gs (q ≫ Spec.map (CommRingCat.ofHom h)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (h a)) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

def combSec {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (c : Fin n → R) (τ : Fin n → LB.Sec M) :
    LB.Sec M where
  f := fun k => ∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_comb p (𝟙 X) y (M.U i) hy.1 _ _).trans (Eq.trans ?_ (congrArg (_ * ·)
      (gs_comb p (𝟙 X) y (M.U j) hy.2 _ _)).symm)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.SecPullIso.gs_sec_trans (τ a) (𝟙 X) y hy.1 hy.2, mul_left_comm]

theorem exists_lift : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH A' _ g hg X' β f' hβ M' w hM' hw s'
  obtain ⟨n, τ, hτ⟩ := _root_.GlobalTheory.SecBasis.exists_basis A X f hf hp M hM K g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH
  choose τ' hτ' using fun i => (GlobalTheory.SecPullIso.section_pull X X' β M M' w hM hM' hw (τ i)).1.exists
  obtain ⟨c, hc, -⟩ := hτ A' g X' β f' hβ M' w τ' hM' hw hτ' s'
  choose d hd using fun i => hg (c i)
  refine ⟨combSec f d τ, fun z k k' hk hk' => ?_⟩
  refine (gs_comb f β z (M.U k) hk _ _).trans ?_
  rw [hc k', gs_comb f' (𝟙 X') z (M'.U k') hk', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hβ.w, gs_const_comp, hd, hτ' i z k k' hk hk', Category.id_comp, mul_left_comm]

end GlobalTheory.SecLiftClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivLocal

open GlobalTheory.AbLaw GlobalTheory.UU

theorem ring_retraction {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] (φ : A →+* C) (hφ : φ.Finite)
    (ε : C →+* A) (he : ∀ a, ε (φ a) = a)
    (h : ∀ c, c - φ (ε c) ∈ (IsLocalRing.maximalIdeal A).map φ) (c : C) : φ (ε c) = c := by
  algebraize [φ]
  have hle : (⊤ : Submodule A C) ≤ LinearMap.range (Algebra.linearMap A C) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun x _ => ?_
    refine Submodule.mem_sup.2 ⟨φ (ε x), ⟨ε x, rfl⟩, x - φ (ε x), ?_, by ring⟩
    rw [Ideal.smul_top_eq_map]
    exact h x
  obtain ⟨a, rfl⟩ := hle (Submodule.mem_top (x := c))
  exact congrArg φ (he a)

theorem comp_section_eq_id_spec {A : Type} [CommRing A] [IsLocalRing A] {C : CommRingCat.{0}}
    (f : Spec C ⟶ Spec (CommRingCat.of A)) [hf : IsFinite f] (e : Spec (CommRingCat.of A) ⟶ Spec C)
    (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ Spec C),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  have hφ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hf
  have he' : φ ≫ ε = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, he, Spec.map_id])
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map φ.hom
  let τ : IsLocalRing.ResidueField A →+* C ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp φ.hom) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have k := h _ (spMap τ) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)
  rw [← Spec.map_comp, ← Spec.map_comp] at k
  have k' := Spec.map_injective k
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  refine ring_retraction φ.hom hφ ε.hom (fun a => congrArg (fun q => q.hom a) he') (fun x => ?_) c
  exact Ideal.Quotient.eq.1 (congrArg (fun q => q.hom x) k').symm

theorem comp_section_eq_id {A : Type} [CommRing A] [IsLocalRing A] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of A)) [IsFinite f] (e : Spec (CommRingCat.of A) ⟶ H) (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ H),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  have : IsAffine H := isAffine_of_isAffineHom f
  have k := comp_section_eq_id_spec (H.isoSpec.inv ≫ f) (e ≫ H.isoSpec.hom) (by simpa using he)
    fun T t y hy => by
      have := h T t (y ≫ H.isoSpec.inv) (by simpa using hy)
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]
      simp
  rw [← cancel_epi H.isoSpec.inv, ← cancel_mono H.isoSpec.hom]
  simpa using k

theorem kTriv_of_closed_fibre : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  intro hLaws _ A _ _ _ B _ _ hB L hLB hL hk
  have hG := hLaws.globalFns
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG A B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG A B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ (T : Over (Spec (CommRingCat.of A))) (x : T ⟶ B), InK B L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (inK_one hLB (𝟙_ _))
  have h := isGrpPullback_pullback B (spMap (IsLocalRing.residue A))
  have hL' : (L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))).IsLB := DVR.linComb_isLB _ hLB _ _
  have key : H.hom ≫ e.left = 𝟙 _ := by
    refine comp_section_eq_id H.hom e.left (Over.w e) fun T t y hy => ?_
    have hdi : (y ≫ j.left) ≫ B.hom = t ≫ spMap (IsLocalRing.residue A) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ (Over.pullback (spMap (IsLocalRing.residue A))).obj B :=
      Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (IsLocalRing.residue A)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := InK.eq_one hk (inK_of_push h hLB hL' (lbIso_self hL') x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : z ≫ toUnit H ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, Category.assoc, he, MonObj.comp_one, MonObj.comp_one]
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    exact (congrArg (fun q => y ≫ q ≫ e.left) h2).symm.trans (congrArg (fun q => q.left) h1)
  have hj1 : j = 1 := by
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    have h1 : toUnit H ≫ e = 𝟙 H :=
      Over.OverMorphism.ext ((congrArg (fun q => q ≫ e.left) h2).trans key)
    rw [← Category.id_comp j, ← h1, Category.assoc, he, MonObj.comp_one]
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedThetaTranslateConstantRigidifiedPullba
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ThMove
open GlobalTheory.TranslMove

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem sval_all {S : Scheme.{0}} {A T : Over S} {L : LB A.left} {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {q : T.left ⟶ (T ⊗ A).left} {p : T.left ⟶ A.left}
    {e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => p) (fun _ => k))} {c : Γ(T.left, ⊤)}
    (H : ∀ z J, Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s q z J =
      gs (𝟙 _) z ⊤ c * (val e (𝟙 _) z J).val) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (r ≫ q) z J = gs r z ⊤ c * (val e r z J).val := by
  have hJ₀ : Good L (r z) (fun χ : T.left ⟶ A.left => J (r ≫ χ)) := fun χ => hJ (r ≫ χ)
  have a := congrArg (r.stalkMap z).hom (H (r z) _ hJ₀)
  rw [map_mul, ← gs_stalkMap r z ⊤ trivial] at a
  refine Eq.trans ?_ (a.trans (congrArg _ ?_))
  · rw [sval_of s (r ≫ q) z J (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => by rw [Category.assoc])]
    exact gs_comp r q z _ (hJ₀.mem _ q) _
  · have m := hJ.mem (fun _ : Fin 1 => p) r
    exact (congrArg _ (gs_unit (𝟙 _) (r z) _ m _).symm).trans ((gs_stalkMap r z _ m _).symm.trans (gs_unit r z _ m _))

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}
  {Ψ : (T' ⊗ P'.A).left ⟶ (T ⊗ P.A).left}

theorem secRel_of_thru (h₁ : Ψ ≫ (fst T P.A).left = (fst T' P'.A).left ≫ h)
    (h₂ : Ψ ≫ (snd T P.A).left = (snd T' P'.A).left ≫ φ) {k : ℕ} {s : LB.Sec (LPow P.A P.L (k : ℤ) T)}
    {s' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')} (H : Thru w k h s s') : SecRel w Ψ s s' := by
  intro Z r z J J' hJ hJ'
  rw [zpow_natCast, Units.val_pow_eq_pow_val]
  exact H Z r (r ≫ Ψ) (by rw [Category.assoc, h₁]) (by rw [Category.assoc, h₂]) z J J' hJ hJ'

theorem secRel_unique {k : ℤ} {s : LB.Sec (LPow P.A P.L k T)} {a b : LB.Sec (LPow P'.A P'.L k T')}
    (ha : SecRel w Ψ s a) (hb : SecRel w Ψ s b) : a = b :=
  FieldBaseChange.sec_ext' P'.isLB (fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.isLB y
    exact (Units.mul_right_inj _).1 ((ha _ _ y J J' hJ hJ').symm.trans (hb _ _ y J J' hJ hJ')))

theorem val_rigT_move {ρ ρ'} (R : RigPull P'.A P.A f φ w ρ' ρ) (hh : h ≫ T.hom = T'.hom ≫ f) (k : ℤ) (y : T'.left)
    {J J'} (hJ : Good P.L y J) (hJ' : Good P'.L y J') :
    val (rigT P.A P.L ρ T k) h y J =
      wv w y J J' (1 : T' ⟶ P'.A).left ^ k * val (rigT P'.A P'.L ρ' T' k) (𝟙 _) y J' := by
  rw [FrameMove.val_rigT _ _ _ hJ, FrameMove.val_rigT _ _ _ hJ', hh, Category.id_comp, ← mul_zpow]
  refine congrArg (· ^ k) ?_
  exact (val_move (fun _ => PolBaseChange.eSec_comm R.1) R.2.2.2 T'.hom hJ hJ').trans
    (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))

end

theorem thC_move : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R') F' ⟶ A'.A) (t : SecA A F (m ^ 2)) (t' : SecA A' F' (m ^ 2)) (c : F), x'.left ≫ ψ = spMap σ ≫ x.left → Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) t t' → ThC A ρ m th x t c → ThC A' ρ' m th' x' t' (σ c) := by
  intro R R' _ _ _ _ gam A A' ψ ω ρ ρ' hR F F' _ _ _ _ σ _ m th th' x x' t t' c hx hth ht H
  obtain ⟨α, s₁, θ, gα, nα, tw, sl, ac, hv⟩ := H
  have gp := hR.1
  have hw := hR.2.1
  have := A'.isAb.comm
  replace hx : (spMap σ : (TFK (R := R') F').left ⟶ (TFK (R := R) F).left) ≫ x.left = x'.left ≫ ψ := hx.symm
  have hh := base_comm (x := x') (x₀ := x) gp hx
  obtain ⟨Ψ, h₁, h₂⟩ : ∃ Ψ : (TFK (R := R') F' ⊗ A'.A).left ⟶ (TFK (R := R) F ⊗ A.A).left,
      Ψ ≫ (fst _ A.A).left = (fst _ A'.A).left ≫ spMap σ ∧ Ψ ≫ (snd _ A.A).left = (snd _ A'.A).left ≫ ψ :=
    ⟨pullback.lift ((fst _ A'.A).left ≫ spMap σ) ((snd _ A'.A).left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hh, gp.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h0 := pt_pow (x := x') (x₀ := x) gp hx 0
  rw [pow_zero, pow_zero] at h0
  have s₂ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ (snd _ A'.A).left = (1 : TFK (R := R') F' ⟶ A'.A).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have s₃ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ (snd _ A'.A ^ m).left =
      (1 : TFK (R := R') F' ⟶ A'.A).left := by
    rw [← Over.comp_left, FrameMove.comp_pow, ptSecT, lift_snd, one_pow]
  have e₀ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ Ψ =
      spMap σ ≫ (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
    refine FrameMove.prod_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
        lift_fst, lift_fst, Over.id_left, Over.id_left, Category.id_comp]
      exact (Category.comp_id _).symm
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, s₂, ← Over.comp_left, ptSecT, lift_snd, h0]
  obtain ⟨α', gα', vα⟩ := exists_genRel A.isLB A'.isLB hw Ψ h₂ (pt_pow gp h₂ m) α gα
  obtain ⟨s₁', tw'⟩ := VVRank.exists_isTwistPull A'.A (ψ := mulT A'.A _ m) (hm := lift_snd _ _) A'.isLB gα' th'
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow gp h₂ m) h₂) vα tw tw' (secRel_of_thru h₁ h₂ hth)
  obtain ⟨θ', sl', a⟩ := exists_symLift gp A.isLB A'.isLB hw h₁ h₂
    (fun θ => pt_pow_eq_one (AbLaw.FromCube.kerPow AbLaw.CubeAssembly.cube_and_sections.1) A' (m ^ 2) rfl θ) hx sl
  obtain ⟨u, ac', R₂⟩ := a _ _ _ ac R₁
  obtain rfl : u = t' := secRel_unique R₂ (secRel_of_thru h₁ h₂ ht)
  refine ⟨α', s₁', θ', gα', corr_of_val A'.isLB fun y J' hJ' => ?_, tw', sl', ac', fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt A.isLB y
    have a₁ := vα _ (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left y J J' hJ hJ'
    have a₂ := (val_pull hJ α _ (spMap σ)).symm.trans ((val_corr hJ nα (spMap σ)).trans
      (val_rigT_move hR hh _ y hJ hJ'))
    rw [e₀, a₂, s₂, s₃, ← zpow_add] at a₁
    rw [val_pull hJ', Category.id_comp]
    exact (mul_left_cancel a₁).symm
  · obtain ⟨J, hJ⟩ := exists_good_pt A.isLB y
    have a₁ := R₂ _ (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left y J J' hJ hJ'
    have a₂ := (sval_all hv (spMap σ) y hJ).trans
      (congrArg (fun v => _ * Units.val v) (val_rigT_move hR hh _ y hJ hJ'))
    rw [Units.val_mul, mul_left_comm] at a₂
    rw [e₀, s₂] at a₁
    exact ((Units.mul_right_inj _).1 (a₁.symm.trans a₂)).trans (congrArg (· * _) (FrameMove.gs_spMap σ y c))

end GlobalTheory.OneBasis.ThMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.SemiDivisible

theorem pow_surj_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hq : Function.Surjective q) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : ∀ t : T, ∃ s, s ^ n = t) (hB : ∀ b : B, ∃ c, c ^ n = b) (y : G) :
    ∃ x : G, x ^ n = y := by
  obtain ⟨c, hc⟩ := hB (q y)
  obtain ⟨z, rfl⟩ := hq c
  obtain ⟨t, ht⟩ := hk (y * (z ^ n)⁻¹) (by rw [map_mul, map_inv, map_pow, hc, mul_inv_cancel])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨i s * z, ?_⟩
  rw [mul_pow, ← map_pow, ht, inv_mul_cancel_right]

theorem pow_surj_chars (X : Type) [AddCommGroup X] [Module.Free ℤ X] (U : Type) [CommGroup U]
    (n : ℕ) (hU : ∀ u : U, ∃ v, v ^ n = u) (t : Multiplicative X →* U) :
    ∃ s : Multiplicative X →* U, s ^ n = t := by
  choose r hr using hU
  let b := Module.Free.chooseBasis ℤ X
  let φ : X →ₗ[ℤ] Additive U :=
    b.constr ℤ fun j => Additive.ofMul (r (t (Multiplicative.ofAdd (b j))))
  let ψ : X →ₗ[ℤ] Additive U := (MonoidHom.toAdditiveRight t).toIntLinearMap
  have h : n • φ = ψ := b.ext fun j => by
    rw [LinearMap.smul_apply, b.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨AddMonoidHom.toMultiplicativeLeft φ.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun h x.toAdd)

theorem pow_surj_units (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n)
    (u : Γ(Sp k, ⊤)ˣ) : ∃ v : Γ(Sp k, ⊤)ˣ, v ^ n = u := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (show 0 < n by omega)
  have h : e.symm z ^ n = u.val := by rw [← map_pow, hz, e.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega)).1 (h ▸ u.isUnit)
  exact ⟨hu.unit, Units.ext h⟩

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left]
    (y : 𝟙_ (Over (Sp k)) ⟶ B) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left
      = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x)
    ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem pow_surj_abelian (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B]
    (hB : IsAbelianScheme B) {n : ℕ} (hn : 1 ≤ n) (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ n = y := by
  have := hB.comm
  have hf : IsFinite ((𝟙 B) ^ n : B ⟶ B).left := GlobalTheory.MulFiniteAny.isFinite_mulA k B hB n hn
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := GlobalTheory.AbLaw.MulN.isMonHom_mulA B n
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k B hB _ hm hf).2
  obtain ⟨x, hx⟩ := exists_lift_point ((𝟙 B) ^ n : B ⟶ B) y
  exact ⟨x, by rw [← hx, MonObj.comp_pow, Category.comp_id]⟩

end GlobalTheory.SS.SemiDivisible


open GlobalTheory.SS.SemiDivisible in
theorem GlobalTheory.SS.torusExtension_points_divisible : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ (n : ℕ), 1 ≤ n → ∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ n = y := by
  rintro k _ _ G _ _ ⟨E⟩ n hn
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  refine pow_surj_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k))))
    (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) (fun b => exists_lift_point E.q b) ?_ n ?_
    (pow_surj_abelian k E.B E.isAbelian hn)
  · intro x hx
    have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · intro t
    let e := GlobalTheory.splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
    obtain ⟨s, hs⟩ := pow_surj_chars E.X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ n
      (pow_surj_units k hn) (e t)
    exact ⟨e.symm s, e.injective (by rw [map_pow, e.apply_symm_apply, hs])⟩
end

