module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.SumFE

open GlobalTheory.IndivisibleSection (smulSec)

theorem sval_smulSec {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (smulSec a s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem app_eq_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) (j) :
    (h.app _).hom (s.f j) = (h.app _).hom (s'.f j) := by
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ (𝟙 Y' ≫ h)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)

theorem sec_eq_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval s (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J = sval s' (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J) → s = s' := by
  intro R _ _ _ hB D K _ φ ε s s' H
  have := hB.1
  have := hB.2.2.2
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine DVR.SecOps.sec_ext fun j => sub_eq_zero.1 ?_
  refine (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R _ (IsAdicComplete.le_jacobson_bot (maximalIdeal R)) D.toPre.P.A).1 _
    (DVR.linComb_isLB _ D.toPre.P.isLB φ ε) ⟨fun i => s.f i - s'.f i, fun i j => by
      simp only [map_sub, s.compat, s'.compat, mul_sub]⟩ (fun e i => ?_) j
  exact (map_sub _ _ _).trans (sub_eq_zero.2 (app_eq_of_sval D.toPre.P.isLB (fun y J hJ => H e _ (𝟙 _) y J hJ) i))

theorem sec_eq_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (K : Type) [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.P.L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J → sval s (x ≫ (DegPre.prB D (FractionRing R)).left) z J = sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J) → s = s' := by
  intro R _ _ D K _ φ ε s s' H
  have := D.P.isAb.smooth
  have : IsDominant (TF (R := R) (FractionRing R)).hom := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)) ∘
      PrimeSpectrum.comap (algebraMap (FractionRing R) (FractionRing R)))
    rw [Algebra.algebraMap_self, PrimeSpectrum.comap_id]
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    have : IsAffine (TF (R := R) (FractionRing R)).left := inferInstanceAs (IsAffine (Spec _))
    quasiCompact_of_compactSpace _
  have := IsSchemeTheoreticallyDominant.of_isDominant (X := Spec (CommRingCat.of (FractionRing R)))
    (TF (R := R) (FractionRing R)).hom
  have : IsSchemeTheoreticallyDominant (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback _ D.P.A.hom)
  have : QuasiCompact (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) := inferInstance
  exact DVR.SecOps.sec_ext fun j => (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom).app_injective _
    (app_eq_of_sval D.P.isLB (fun y J hJ => H _ (𝟙 _) y J hJ) j)

theorem trF_prB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (mu : D.X), (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left := by
  intro R _ _ D mu
  rw [← Over.comp_left, ← Over.comp_left, DegPre.trF, lift_snd, padd, padd, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc]

theorem gs_scal_generic {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Z : Scheme.{0}}
    (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R) :
    gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) =
      gs x z ⊤ (scal ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) r)) := by
  have e := congrArg (fun h => h.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have w : (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom =
      ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
    refine (Over.w _).trans ((Over.w (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_)
    congr 1
    change Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) ≫ jK R = jK R
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine (gs_pull x _ z ⊤ trivial _).symm.trans (congrArg (gs x z ⊤) ?_)
  change scal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) r = _
  rw [w, scal, scal, e]
  rfl

theorem scal_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R), (r ≠ 0 → IsUnit (gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r))) ∧ ∀ (c : FractionRing R) (r' : R), c * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) r' → gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) * gs x z ⊤ (scal (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left c) = gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r') := by
  intro R _ _ D Z x z r
  refine ⟨fun hr => ?_, fun c r' hc => ?_⟩
  · have hu : IsUnit (algebraMap R (FractionRing R) r) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    rw [gs_scal_generic, gs_eq _ z ⊤ trivial]
    exact ((((hu.map _).map _).map _).map _)
  · rw [gs_scal_generic, gs_scal_generic, ← hc, ← gs_mul x z ⊤ trivial, mul_comm c]
    simp only [scal, map_mul]

theorem tfe_of_isSum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  intro R _ _ _ hB D a a' h h' hE n j Ix w s F σ hs hF hw hrel mu β
  generalize hβ' : β + shift h h' n j mu = β'
  intro u hu
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.TwFam.Gen0.main R hB D a a' h h' hE n j mu β β' hβ'.symm
  obtain ⟨c, hc⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hB D a h hE.1 hE.2.2.2.1 n j mu β β' u₀ hu₀).2.2 u hu.1
  obtain ⟨⟨r', r⟩, hrc⟩ := IsLocalization.surj (nonZeroDivisors R) c
  have hTw : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := Over.w _
  have hT := trF_prB R D.toPre mu
  generalize hTe : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left = T at hTw hT
  have mkG : ∀ t : SecT D.toPre a n j β, ∃ G : SecT D.toPre a n j β', ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left)
      (z : Z) (J), Good D.toPre.P.L z J → sval G y z J = sval t (y ≫ T) z J * (val u₀ y z J).val := by
    intro t
    obtain ⟨G, hG⟩ := exists_sec hL (φ' := tφ D.toPre a β') (ε' := tε n j) (fun U _ g => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, dε, zpow_neg, Finset.prod_inv_distrib, hTe]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec t T u₀ hu₀)
    exact ⟨G, fun Z y z J hJ => (hG Z y z J hJ).trans (sval_pullMulSec t T u₀ hu₀ y z hJ)⟩
  have key : ∀ (b b' : D.toPre.X) (t : SecT D.toPre a n j b) (t' : SecT D.toPre a n j b'), b = β → b' = β' →
      TRel h mu t t' → ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      gs y z ⊤ (scal D.toPre.P.A.hom r.1) * sval t' y z J =
        gs y z ⊤ (scal D.toPre.P.A.hom r') * (sval t (y ≫ T) z J * (val u₀ y z J).val) := by
    intro b b' t t' h1 h2 hR Z y z J hJ
    subst h1 h2
    obtain ⟨G, hG⟩ := mkG t
    have e : smulSec (scal D.toPre.P.A.hom r.1) t' = smulSec (scal D.toPre.P.A.hom r') G :=
      sec_eq_of_generic R D.toPre (Fin 5) _ _ _ _ fun Z x z J hJ => by
        rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hR u hu Z x z J hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT,
          ← (scal_generic R D.toPre Z x z r.1).2 c r' hrc, Category.assoc]
        ring
    rw [← hG _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, e]
  obtain ⟨G, hG⟩ := mkG (F β)
  have eB : smulSec (scal D.toPre.P.A.hom r.1) (F β') = smulSec (scal D.toPre.P.A.hom r') G := by
    refine sec_eq_of_thick R hB D (Fin 5) _ _ _ _ fun e Z x z J hJ => ?_
    rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ]
    obtain ⟨x', hx'⟩ : ∃ x' : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left,
        x' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ T :=
      ⟨pullback.lift _ (x ≫ pullback.snd _ _) (by
        rw [Category.assoc, hTw]
        exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)),
        pullback.lift_fst _ _ _⟩
    classical
    have hS : ∀ i ∉ (hs e).toFinset, Van (maximalIdeal R) (s i) e := fun i hi =>
      by_contra fun hc => hi ((hs e).mem_toFinset.2 hc)
    generalize (hs e).toFinset = S at hS
    have e₁ := hF e ((S ∪ S.image (σ mu).symm).image (σ mu)) (fun i hi => hS i fun m => hi (Finset.mem_image.2
      ⟨(σ mu).symm i, Finset.mem_union_right _ (Finset.mem_image_of_mem _ m), (σ mu).apply_symm_apply i⟩)) β' Z x z J hJ
    have e₂ := hF e (S ∪ S.image (σ mu).symm) (fun i hi => hS i fun m => hi (Finset.mem_union_left _ m)) β Z x' z J hJ
    rw [hx'] at e₂
    rw [e₁, e₂, Finset.sum_filter, Finset.sum_filter, Finset.sum_image (σ mu).injective.injOn, Finset.sum_mul,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : w i = β
    · have hi' : w (σ mu i) = β' := by rw [hw, hi, hβ']
      rw [if_pos hi, if_pos hi']
      exact key _ _ _ _ hi hi' (hrel mu i) _ _ z J hJ
    · have hi' : ¬ w (σ mu i) = β' := fun h2 => hi (add_right_cancel ((hw mu i).symm.trans (h2.trans hβ'.symm)))
      rw [if_neg hi, if_neg hi', zero_mul, mul_zero, mul_zero]
  intro Z x z J hJ
  obtain ⟨hunit, hmul⟩ := scal_generic R D.toPre Z x z r.1
  refine (hunit (nonZeroDivisors.ne_zero r.2)).mul_left_cancel ?_
  rw [← sval_smulSec _ _ _ _ hJ, eB, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT, ← hmul c r' hrc,
    Category.assoc]
  ring

end GlobalTheory.TwFam.SumFE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationMulOfRelatedPairs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.ProdRel

variable {R : Type} [CommRing R] [IsDomain R]


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem comp_tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) {T : Over (Spec (CommRingCat.of R))} (r : T ⟶ D.P.A) (k : Fin 5) :
    r.left ≫ tφ D a β k = ((![r, r * cP D T β, cP D T β, 1, r ≫ a] : Fin 5 → (T ⟶ D.P.A)) k).left := by
  fin_cases k
  · show r.left ≫ 𝟙 _ = r.left; simp
  · show r.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c β)).left = (r * cP D T β).left
    rw [← Over.comp_left, padd, ← Hom.mul_def, MonObj.comp_mul, Category.comp_id]
    congr 2
    exact comp_cP D r β
  · show r.left ≫ (toUnit D.P.A ≫ D.c β).left = (cP D T β).left
    rw [← Over.comp_left]; exact congrArg _ (comp_cP D r β)
  · show r.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left
    rw [← Over.comp_left, Hom.one_def, ← Category.assoc, toUnit_unique (r ≫ toUnit _) (toUnit T)]
  · show r.left ≫ a.left = (r ≫ a).left; rw [Over.comp_left]


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem formEq (D : DegPre R) (a : D.P.A ⟶ D.P.A) (mu β β' β₁ β₁' : D.X) (n j n' j' : ℤ) :
    FormEq (Sum.elim (Sum.elim (Sum.elim (dφ D a mu β β₁) (dφ D a mu β' β₁'))
        (fun k => (lift (cP D (DegPre.BF D (FractionRing R)) β₁) (lift (cP D (DegPre.BF D (FractionRing R)) β₁')
          (DegPre.prB D (FractionRing R)))).left ≫ thφ D.P.A (x3 D.P.A) k))
        (fun k => (lift (cP D (DegPre.BF D (FractionRing R)) β) (lift (cP D (DegPre.BF D (FractionRing R)) β')
          (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)))).left ≫ thφ D.P.A (x3 D.P.A) k))
      (Sum.elim (Sum.elim (Sum.elim (dε n j) (dε n' j')) thε) (fun k => - thε k))
      (dφ D a mu (β + β') (β₁ + β₁')) (dε (n + n') (j + j')) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [prod_cub, prod_cub]
  simp only [dφ, dε, Sum.elim_inl, Sum.elim_inr]
  simp only [← Category.assoc, ← Over.comp_left]
  simp only [comp_tφ]
  simp only [Fin.prod_univ_five, tε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zpow_one, neg_neg]
  have htr : DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DegPre.prB D (FractionRing R) * cP D (DegPre.BF D (FractionRing R)) mu := by
    simp only [DegPre.trF, DegPre.prB, lift_snd, padd, ← Hom.mul_def]; rfl
  rw [htr, cPoint_add, cPoint_add]
  generalize DegPre.prB D (FractionRing R) = Y
  generalize cP D (DegPre.BF D (FractionRing R)) mu = Cm
  generalize cP D (DegPre.BF D (FractionRing R)) β = Cb
  generalize cP D (DegPre.BF D (FractionRing R)) β' = Cb'
  generalize cP D (DegPre.BF D (FractionRing R)) β₁ = Cc
  generalize cP D (DegPre.BF D (FractionRing R)) β₁' = Cc'
  rw [mul_comm Cc Y, mul_comm Cc' Y, mul_comm Cb (Y * Cm), mul_comm Cb' (Y * Cm), mul_comm (Cc * Cc') Y,
    mul_comm (Cb * Cb') (Y * Cm)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem trF_prB (D : DegPre R) (mu : D.X) : DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
    DegPre.prB D (FractionRing R) * cP D (DegPre.BF D (FractionRing R)) mu := by
  simp only [DegPre.trF, DegPre.prB, lift_snd, padd, ← Hom.mul_def]; rfl

theorem zF_prB (D : DegPre R) : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := by
  simp only [DegPre.zF, DegPre.prB, lift_snd, Hom.one_def]


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_prodFac (D : DegPre R) (hB : D.TauBimult) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) (n j n' j' : ℤ)
    (mu β β' β₁ β₁' : D.X) (uf : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β₁) (dε n j)))
    (ug : LB.Gen (LB.LinComb D.P.L (dφ D a mu β' β₁') (dε n' j')))
    (hf : IsFac D a h n j mu β β₁ uf) (hg : IsFac D a h n' j' mu β' β₁' ug) :
    ∃ w : LB.Gen (LB.LinComb D.P.L (dφ D a mu (β + β') (β₁ + β₁')) (dε (n + n') (j + j'))),
      IsFac D a h (n + n') (j + j') mu (β + β') (β₁ + β₁') w ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
        val w x z J = val uf x z J * val ug x z J *
          val D.cub.t (x ≫ (lift (cP D (DegPre.BF D (FractionRing R)) β₁) (lift (cP D (DegPre.BF D (FractionRing R)) β₁')
            (DegPre.prB D (FractionRing R)))).left) z J *
          (val D.cub.t (x ≫ (lift (cP D (DegPre.BF D (FractionRing R)) β) (lift (cP D (DegPre.BF D (FractionRing R)) β')
            (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)))).left) z J)⁻¹ := by
  let c1 := LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (cP D (DegPre.BF D (FractionRing R)) β₁) (lift (cP D (DegPre.BF D (FractionRing R)) β₁')
      (DegPre.prB D (FractionRing R)))).left
  let c2 := LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (cP D (DegPre.BF D (FractionRing R)) β) (lift (cP D (DegPre.BF D (FractionRing R)) β')
      (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)))).left
  let w0 := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ uf ug) c1)
    (LB.invGen D.P.L _ _ c2)
  have hw0 : w0.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hf.1 hg.1)
    (pullGen_isGen _ _ _ _ D.cub.isGen _)) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (formEq D a mu β β' β₁ β₁' n j n' j') w0 hw0
  have ev : ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
      val w x z J = val uf x z J * val ug x z J * val c1 x z J * (val c2 x z J)⁻¹ := fun Z x z J hJ => by
    exact (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) (val_inv _ _)))
  refine ⟨w, ⟨hw, fun z J hJ => ?_⟩, fun Z x z J hJ => ?_⟩
  · rw [ev _ _ z J hJ, hf.2 z J hJ, hg.2 z J hJ, val_cub D.cub (DegPre.zF D (FractionRing R)) hJ,
      val_cub D.cub (DegPre.zF D (FractionRing R)) hJ, comp_cP, comp_cP, comp_cP, comp_cP, zF_prB,
      trF_prB, MonObj.comp_mul, zF_prB, comp_cP, _root_.one_mul, (isCub_cubV D.cub hJ).face₃]
    have t := tau_mul (𝟙 (TF (R := R) (FractionRing R))) hJ hB β β' mu
    rw [tau_symm (𝟙 (TF (R := R) (FractionRing R))) hJ (β + β'), tau_symm (𝟙 (TF (R := R) (FractionRing R))) hJ β,
      tau_symm (𝟙 (TF (R := R) (FractionRing R))) hJ β'] at t
    simp only [Over.id_left, Category.id_comp] at t
    have t' := congrArg Additive.ofMul t
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_one] at t' ⊢
    linear_combination (norm := module) -t'
  · exact (ev _ _ z J hJ).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem comp_cub (D : DegPre R) (β β' : D.X) {T : Over (Spec (CommRingCat.of R))} (r : T ⟶ D.P.A) :
    r.left ≫ (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left =
      (lift (cP D T β) (lift (cP D T β') r) : T ⟶ G3 D.P.A).left := by
  rw [← Over.comp_left, comp_lift, comp_lift, Category.comp_id, ← comp_cP D r β, ← comp_cP D r β']
  rfl

theorem trel_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (mu β β' β₁ β₁' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β') (p : SecT D.toPre a n'' j'' (β + β')) (f₁ : SecT D.toPre a n j β₁) (g₁ : SecT D.toPre a n' j' β₁') (p₁ : SecT D.toPre a n'' j'' (β₁ + β₁')), β₁ = β + shift h h' n j mu → β₁' = β' + shift h h' n' j' mu → IsProdT f g p → IsProdT f₁ g₁ p₁ → TRel h mu f f₁ → TRel h mu g g₁ → TRel h mu p p₁ := by
  intro R _ _ _ hA D a a' h h' hE n j n' j' n'' j'' hn hj mu β β' β₁ β₁' f g p f₁ g₁ p₁ e e' hp hp₁ hf hg
  subst hn hj
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.TwFam.Gen0.main R hA D a a' h h' hE n j mu β β₁ e
  obtain ⟨v', hv'⟩ := _root_.GlobalTheory.TwFam.Gen0.main R hA D a a' h h' hE n' j' mu β' β₁' e'
  obtain ⟨v'', hv''⟩ := _root_.GlobalTheory.TwFam.Gen0.main R hA D a a' h h' hE (n + n') (j + j') mu (β + β') (β₁ + β₁') (by
    rw [e, e']; simp only [shift, add_smul]; abel)
  obtain ⟨uf, huf⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hA D a h hE.1 hE.2.2.2.1 n j mu β β₁ v hv).1
  obtain ⟨ug, hug⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hA D a h hE.1 hE.2.2.2.1 n' j' mu β' β₁' v' hv').1
  obtain ⟨w, hw, ew⟩ := exists_prodFac D.toPre D.tau_bimult a h n j n' j' mu β β' β₁ β₁' uf ug huf hug
  intro u hu Z x z J hJ
  have e₁ := hp₁ Z (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J hJ
  have e₂ := hp Z (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J hJ
  rw [Category.assoc, comp_cub] at e₁
  rw [Category.assoc, show ((DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ _ = _
    from comp_cub D.toPre β β' (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R))] at e₂
  rw [e₁, e₂, hf uf huf Z x z J hJ, hg ug hug Z x z J hJ,
    (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hA D a h hE.1 hE.2.2.2.1 _ _ mu _ _ v'' hv'').2.1 u w hu hw Z x z J hJ, ew Z x z J hJ]
  have key : ∀ {S : Type} [CommRing S] (s t : S) (c₁ c₂ b₁ b₂ : Sˣ),
      s * b₁.val * (t * b₂.val) * c₁.val = s * t * c₂.val * (b₁ * b₂ * c₁ * c₂⁻¹).val := by
    intro S _ s t c₁ c₂ b₁ b₂
    simp only [Units.val_mul]
    linear_combination (-(s * t * b₁.val * b₂.val * c₁.val)) * c₂.mul_inv
  exact key _ _ _ _ _ _

end GlobalTheory.TwFam.ProdRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumTermsEqThetaConstantTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TwistTranslate


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem twistSum_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ C lab _ T hT c τ _ χ hχ hyp
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, hval⟩ := GlobalTheory.T.torsionFrames_sectionValues_ratio_rootOfUnity V 𝔪.A ρA hρA _ (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) _ _ _
    (htors (lab c + τ)) he₂ th _ (hth (lab c + τ))
  have hsum := hov 1 le_rfl w'' (fun z J _ => (pow_one _).symm) hw''g th s _ hs hval
  obtain ⟨e, he⟩ := _root_.GlobalTheory.Poinc.Sep.eq_yK_zeta_pow_of_pow_eq_one g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 u hu
  refine ⟨e, ?_⟩
  rw [← he]
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'' χ' =
      ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' => by
    rw [GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (c := 1) (fun z J _ => by rw [hw''v, map_one, _root_.one_mul]) s χ',
      _root_.one_mul]
  have hA := admissibleBase_of_completeNormalLocalCharZero 𝔪.cn
  have key := ((GlobalTheory.AdicSum.sumF_calculus V _ hA (FractionRing V) _
    (coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'') 0 _ 0).2.2 (Fin 8 → X) 𝔪.e₈
    𝔪.e₈.injective (fun j hj => absurd ⟨𝔪.e₈.symm j, 𝔪.e₈.apply_symm_apply j⟩ hj)).2 hsum
  convert key using 2 with mu
  simp only [Function.comp_apply, hco, hTc]

end GlobalTheory.Poinc.Sep.TwistTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupAbelianWhereTrivialisationsUnits
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PsiUnitAb

theorem subset_abLocus_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G := by
  have hI1 := @GlobalTheory.T.torsion_fixed_unramified_complete_trait
  have hI2 := @GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion
  intro R _ _ _ hR D A G _ _ hG U W hW x hx
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, hu⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by exact_mod_cast h⟩
    · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  have := x.isPrime
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R x.asIdeal
  have hcx : spMap φ (closedPoint V) = x := PrimeSpectrum.ext hc
  have huV : IsUnit (n : V) := by simpa using hu.map φ
  have h1 := hI1 R hR D A G hG U W hW V φ hV hφ (hcx ▸ hx) n hn huV
  have h2 := hI2 R hR D A G hG U V φ hV hφ n hn huV h1
  have key := abLocus_pullback (G' := (Over.pullback (spMap φ)).obj G) abLocusOne hG (isGrpPullback_pullback G (spMap φ)).1 (closedPoint V)
  rw [← hcx]
  exact key.2 h2

end GlobalTheory.Mum.PsiUnitAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_closedFibre_subset_isAffineOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) →
    ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR _ _ G _ _ hG _ s hs
  exact _root_.GlobalTheory.Mum.exists_affine_open_of_finset_closedFibre R hR.1 G hG s hs

end GlobalTheory.Mum
end

