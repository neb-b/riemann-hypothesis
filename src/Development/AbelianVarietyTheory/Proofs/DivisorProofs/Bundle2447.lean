module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionTensorQuotientRingEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxIntegralClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwist
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteOverPSpace

theorem isProjOver_and_isAmpleLB : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (n k : ℕ) (Z : Scheme.{0}) (p : Z ⟶ PSpace o n), 1 ≤ k → IsFinite p → IsProjOver (p ≫ PSpace.str o n) ∧ (lbPow ((ProjSpace.O1 o n).pull p) k).IsLB ∧ IsAmpleLB (lbPow ((ProjSpace.O1 o n).pull p) k) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ Z), LBIso ((lbPow ((ProjSpace.O1 o n).pull p) k).pull h) (lbPow ((ProjSpace.O1 o n).pull (h ≫ p)) k) := by
  intro o _ _ n k Z p hk hp
  have hO := ProjSpace.O1_isLB o n
  have hA : IsAmpleLB ((ProjSpace.O1 o n).pull p) := (isAmple_projective_O_one o n).pull_of_isAffineHom p
  refine ⟨isProjOver_comp_of_isFinite p ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩, isLB_lbPow hA.isLB k,
    (isAmpleLB_pow_iff hA.isLB hk).2 hA, fun Y h => ?_⟩
  refine (CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA.isLB k) h) (isLB_lbPow (pull_isLB hO (h ≫ p)) k)).1 ?_
  rw [CechPic.cls_pull (isLB_lbPow hA.isLB k), CechPic.cls_lbPow hA.isLB, CechPic.cls_lbPow (pull_isLB hO (h ≫ p)),
    CechPic.cls_pull hO, CechPic.cls_pull hO, CechPic.pull_comp, map_nsmul]

end GlobalTheory.FiniteOverPSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymmPoincare

universe u

section Linear

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  {ψ : Module.Dual K V →ₗ[K] Module.Dual K V →ₗ[K] K} {β : V →ₗ[K] Module.Dual K V}

end Linear

section Swap

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A B : Over S} [GrpObj A] [GrpObj B]

theorem isCorrForm_swap {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) : IsCorrForm κ t B A (swap P) (-φ.flip) := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  have m : IsMor κ ((A ⊗ B).hom ≫ t) κ ((B ⊗ A).hom ≫ t) (RingHom.id R) (lift (snd B A) (fst B A)).left :=
    (homMor κ t (lift (snd B A) (fst B A))).isMor
  have k := isChern_pull m hc
  rw [crystallinePull2_sum_cup] at k
  refine ⟨n, fun i ↦ -b i, a, ?_, fun x y ↦ ?_⟩
  · convert k using 2 with i
    rw [pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, Submodule.coe_neg, map_neg, map_neg,
      LinearMap.neg_apply, neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφ, map_neg, ← Finset.sum_neg_distrib, neg_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem isCorrForm_of_iso {P Q : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : IsCorrForm κ t A B Q φ := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  exact ⟨n, a, b, (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ hP hQ e _ hc, hφ⟩

theorem skew_of_symm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P)
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x :=
  LinearMap.congr_fun₂ (H.unique C hP (isCorrForm_of_iso (isCorrForm_swap H) (pull_isLB hP _) hP hs)) x y

end Swap

end GlobalTheory.SymmPoincare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSub
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftDiff

private theorem thickHom_ext {R : Type} [CommRing R] {I : Ideal R}
    {powers : DividedPowers I} {X : Scheme.{0}} {s : X ⟶ Sp R}
    {T T' : Thick powers s} {f g : T ⟶ T'} (h : ∀ b, f.φ b = g.φ b) : f = g := by
  change Thick.Hom T T' at f g
  cases f with
  | mk φ φ₀ comm dp pt =>
    cases g with
    | mk ψ ψ₀ comm' dp' pt' =>
      have e : φ = ψ := AlgHom.ext h
      subst ψ
      have e₀ : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
        obtain ⟨b, rfl⟩ := T.surj c
        rw [comm, comm']
      subst ψ₀
      rfl

theorem spMap_fst_surjective {B : Type} [CommRing B] (f : DualNumber B →+* B) (hf : ∀ c, f c = c.fst) :
    Function.Surjective (spMap f) := by
  intro q
  refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap B (DualNumber B) (f c) ∈ q.asIdeal ↔ c ∈ q.asIdeal
  rw [hf]
  have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem le_preimage_of_red {B : Type} [CommRing B] {X : Scheme.{0}} (f : DualNumber B →+* B)
    (hf : ∀ c, f c = c.fst) {y : Sp (DualNumber B) ⟶ X} {x : Sp B ⟶ X} (e : spMap f ≫ y = x) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_fst_surjective f hf p
  have := h (Set.mem_univ q)
  rw [← e] at this
  exact this

theorem ev_eq_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (ω : Form s)
    {T₁ T₂ T : Thick (dp0 R) s} (a : T₁ ⟶ T₂) (ψ : T₂ ⟶ T) (φ : T₁ ⟶ T) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (e : a ≫ ψ = φ) : ev ω.1 φ = ev ω.1 ψ := by
  rw [← e, ev_comp, show ev ω.1 a = 0 from ω.2 a h₁ h₂, map_zero, zero_add]

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A']
  {i : A.left ⟶ A'.left}

theorem ev_sec_sub_ev_tan (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) :
    ∃ (hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
        spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
        ((fibMor h).isMor.obj P.ext).x)
      (ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x),
      ev ((fibMor h).isMor.pullForm ω).1 P.sec - ev ((fibMor h).isMor.pullForm ω).1 (P.tan hv) =
        ev ω.1 (idLift _ _ hc ec) - ev ω.1 (idLift _ _ ht et) := by
  let g : DualNumber K →+* P.B := (algebraMap K P.B).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have w : (P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap g := ((fibMor h).isMor.obj P.triv).w
  have hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) := by
    rw [Category.assoc, w]
    exact (Cris.spMap_comp g (algebraMap P.B (DualNumber P.B))).symm.trans (congrArg spMap (RingHom.ext fun _ ↦ rfl))
  have ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
      ((fibMor h).isMor.obj P.ext).x := by
    let π' : DualNumber P.B →+* P.B := TrivSqZeroExt.fstHom K P.B P.B
    have e : π'.comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := RingHom.ext fun _ ↦ rfl
    show spMap π' ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i = P.x ≫ i
    rw [← Category.assoc, ← Cris.spMap_comp, e, Cris.spMap_id, Category.id_comp]
  have ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) :=
    ((fibMor h).isMor.obj (P.tr v).triv).w
  have et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) ((P.isTransl_trx v).red hv))
  refine ⟨hc, ec, ht, et, ?_⟩
  refine congrArg₂ (· - ·) (ev_eq_of_triv ω ?a (idLift _ _ hc ec) ((fibMor h).isMor.functor.map P.sec) rfl rfl ?ea)
    (ev_eq_of_triv ω ?b (idLift _ _ ht et) ((fibMor h).isMor.functor.map (P.tan hv)) rfl rfl ?eb)
  case a =>
    exact { φ := { algebraMap P.B (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := algebraMap P.B (DualNumber P.B)
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := rfl }
  case b =>
    exact { φ := { RingHom.id (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := RingHom.id _
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := by
              show spMap (RingHom.id (DualNumber P.B)) ≫ P.trx v ≫ i = P.trx v ≫ i
              rw [Cris.spMap_id, Category.id_comp] }
  case ea => exact thickHom_ext fun _ ↦ rfl
  case eb => exact thickHom_ext fun _ ↦ rfl

theorem liftVal_sub_snd : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  intro K _ A _ A' _ i h hA ω U hU P hP y₁ y₂ h₁ h₂ n u c hu hdiff
  obtain ⟨m, r, t, H⟩ := _root_.GlobalTheory.CechKS.FormLocal.ev_idLift_sub_eq_sum (DualNumber K) A'.left (A'.hom ≫ 𝟙 _) ω U hU
  have hPU : ⊤ ≤ (P.x ≫ i) ⁻¹ᵁ U := hP
  have red : ∀ c : DualNumber P.B, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) c = c.fst :=
    fun _ ↦ rfl
  have hU₁ : ⊤ ≤ y₁ ⁻¹ᵁ U := le_preimage_of_red _ red h₁.2 hPU
  have hU₂ : ⊤ ≤ y₂ ⁻¹ᵁ U := le_preimage_of_red _ red h₂.2 hPU
  have k1 := H ((liftMor (epsDP K) h).isMor.obj P.eps) (SqExt.ofModule K P.B P.B).sq rfl y₁ y₂ h₁.1 h₂.1
    h₁.2 h₂.2 hU₁ hU₂
  have e1 : liftVal h ω.1 h₁ - liftVal h ω.1 h₂ =
      -∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
    rw [← neg_sub]; exact congrArg Neg.neg k1
  have f2 : ∀ f, (valR y₂ U f).fst = valR P.x (i ⁻¹ᵁ U) ((i.app U).hom f) := fun f ↦ by
    rw [← GlobalTheory.Points.valR_comp, ← h₂.2, GlobalTheory.Points.valR_spMap_comp _ _ _ hU₂]; exact (red _).symm
  have step2 : ∀ a, ∑ k, valR P.x (i ⁻¹ᵁ U) ((i.app U).hom (r k)) *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd =
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
    intro a
    have X := ev_sec_sub_ev_tan (K := K) (A := A) (A' := A') (i := i) h ω P (hu a)
    obtain ⟨hc, ec, ht, et, E⟩ := X
    have F := _root_.GlobalTheory.CechKS.ev_sec_sub_ev_tan K A hA (u a) (hu a) ((fibMor h).isMor.pullForm ω) P
    have hUt : ⊤ ≤ (P.trx (u a) ≫ i) ⁻¹ᵁ U := fun p hp ↦ hP.tr (hu a) hp
    have hUc : ⊤ ≤ (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ⁻¹ᵁ U :=
      fun _ _ ↦ hPU (Set.mem_univ _)
    have k2 := H ((fibMor h).isMor.obj P.ext) (SqExt.ofModule K P.B P.B).sq rfl _ _ ht hc et ec hUt hUc
    have F3 : (∑ k, valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (r k) *
        (valR (P.trx (u a) ≫ i) U (t k) - valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (t k))) =
        TrivSqZeroExt.inr (algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω))) := k2.symm.trans (E.symm.trans F)
    have F' := congrArg (fun z : DualNumber P.B ↦ z.snd) F3
    simp only [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_sum] at F'
    rw [← F']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_comp,
      GlobalTheory.Points.valR_comp, GlobalTheory.Points.valR_comp]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have D : ∀ k, valR y₁ U (t k) - valR y₂ U (t k) = TrivSqZeroExt.inr (∑ a, c a *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd) := fun k ↦ hdiff (t k)
  refine (congrArg (fun z : DualNumber P.B ↦ z.snd) e1).trans ?_
  have G := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ congrArg (valR y₂ U (r k) * ·) (D k)
  refine (congrArg (fun z : DualNumber P.B ↦ (-z).snd) G).trans ?_
  simp only [TrivSqZeroExt.snd_neg, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, f2, smul_eq_mul, MulOpposite.op_zero,
    zero_smul, add_zero, neg_inj]
  simp only [← step2, Finset.mul_sum]
  clear H k1 e1 hdiff D G step2 f2 red
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.CechKS.LiftDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingOfEssFiniteType
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem formalFibre_isRegularRing_of_essFiniteType :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (R K : Type) [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R]
      [Field K] [Algebra R K] [Algebra.EssFiniteType R K],
      (∀ a : Λ, algebraMap R K (algebraMap Λ R a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro Λ _ _ _ _ R K _ _ _ _ _ _ _ hK
  obtain ⟨n, P, hP, φ, hφ⟩ := _root_.GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType Λ R
  let R₀ := Localization.AtPrime P
  letI : Algebra R₀ R := φ.toRingHom.toAlgebra
  letI : Algebra R₀ K := ((algebraMap R K).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower R₀ R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherianRing R₀ := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hsurj : Function.Surjective (algebraMap R₀ R) := hφ
  haveI : Algebra.FiniteType R₀ R := Algebra.FiniteType.of_surjective (Algebra.ofId R₀ R) hsurj
  haveI : Algebra.EssFiniteType R₀ R := inferInstance
  haveI : Algebra.EssFiniteType R₀ K := Algebra.EssFiniteType.comp R₀ R K
  have hK₀ : ∀ a : Λ, algebraMap R₀ K (algebraMap Λ R₀ a) = 0 → a = 0 := by
    intro a ha
    apply hK a
    have h1 : algebraMap R₀ K (algebraMap Λ R₀ a) = algebraMap R K (φ (algebraMap Λ R₀ a)) := rfl
    rw [h1, φ.commutes] at ha
    exact ha
  have hreg := _root_.GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial Λ n P K hK₀
  obtain ⟨e⟩ := _root_.GlobalTheory.adicCompletion_tensor_quotient_ringEquiv R₀ R K hsurj
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SFour

theorem pow_le_map {V V' : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing V'] [IsLocalRing V']
    (io : V →+* V') (hfin : io.Finite) :
    ∃ J : ℕ, ∀ j : ℕ, maximalIdeal V' ^ (J * j) ≤ (maximalIdeal V ^ j).map io := by
  letI := io.toAlgebra
  haveI : Module.Finite V V' := hfin
  obtain ⟨E, hE⟩ := GlobalTheory.Poinc.OrbTrace.exists_pow_le (A := V) (B := V') (maximalIdeal V') (maximalIdeal.isMaximal V') 1
  have h1 : maximalIdeal V' ^ E ≤ (maximalIdeal V).map io := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hE x hx
    have hu' : IsUnit u := by
      by_contra h
      exact hu ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [pow_one] at hux
    exact (Ideal.unit_mul_mem_iff_mem _ hu').1 hux
  refine ⟨E, fun j => ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono h1 j

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A]
  [IsLocalRing A]

theorem term_mem (Φ : VPre bar q W A) (y : Φ.Y) (mu : Fin s → Φ.X y) (cc : Φ.Q) (j : ℕ)
    (hj : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) : Φ.term y mu cc ∈ maximalIdeal (Φ.V y) ^ j := by
  have hnn : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have hle : j ≤ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    have e1 : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnn i)
    rw [← e1] at hj
    exact_mod_cast hj
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _

end GlobalTheory.Poinc.SFour

namespace GlobalTheory.Poinc.SFour

theorem four_of_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.ClassSums N₁ → Φ.Four N₁ := by
  intro O _ bar q s W A _ _ _ _ Φ N₁ hcs y₀ N₀
  classical
  obtain ⟨N, hN0, hN1, hNd, k, hk0, hk, L, _, _, _, _, _, _, 𝔷, f, hz, hf, hy, hσ⟩ := hcs y₀ N₀
  refine ⟨N, hN0, hNd, k, hk0, hk, fun l a c e => ?_⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := OrbTrace.exists_classes (O := O) (N₁ := N₁) hN1 a
  set F : integralClosure A L := ∑ c' ∈ C, ∏ i, f (fun u => c' (i, u)) (c i) with hF
  have hFix : ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
      σ (F : L) = F := by
    intro σ hσ'
    obtain ⟨ga, h1, h2, h3, h4⟩ := hσ σ hσ'
    have e1 : ((F : integralClosure A L) : L) = ∑ c' ∈ C, ∏ i, (f (fun u => c' (i, u)) (c i) : L) := by
      rw [hF]; push_cast; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [map_prod, h4]
    exact OrbTrace.sum_comp_eq C hC1 hC2 hC3 ga h1 h2 h3 (fun c' => ∏ i, (f (fun u => c' (i, u)) (c i) : L))
      (fun c₁ c₂ h => Finset.prod_congr rfl fun i _ => by rw [hf _ _ _ fun u => h _])
  haveI := hz
  obtain ⟨g₀, b, hb, hbF⟩ := GlobalTheory.DecompFixed.exists_approx_integralClosure A (FractionRing A) L 𝔷 F hFix e
  refine ⟨g₀, fun y j => ?_⟩
  obtain ⟨V', _, _, io, ev', hfin, hloc, hpure, hcomm, hcomap, hcls⟩ := hy y
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  obtain ⟨J, hJ⟩ := pow_le_map io hfin
  set j' := J * j + j with hj'
  have hjj : j ≤ j' := Nat.le_add_left _ _
  have hJj : maximalIdeal V' ^ j' ≤ (maximalIdeal (Φ.V y) ^ j).map io :=
    (Ideal.pow_le_pow_right (Nat.le_add_right _ _)).trans (hJ j)
  have hmap : ∀ n, (maximalIdeal (Φ.V y) ^ n).map io ≤ maximalIdeal V' ^ n := by
    intro n
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 <|
      (IsLocalRing.mem_maximalIdeal _).2 fun h => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit io x h)) n
  choose S₀ hSa hSb hSc using fun κ cc => hcls κ cc j'
  set T : Finset (Fin s → Φ.X y) := C.biUnion (fun c' => Finset.univ.biUnion
    (fun i => S₀ (fun u => c' (i, u)) (c i))) with hT
  have hSfin : {mu : Fin l × Fin s → Φ.X y | mu ∈ orbit O N₁ N (k y) a ∧ ∀ i, (fun u => mu (i, u)) ∈ T}.Finite := by
    refine ((Set.Finite.pi' (fun _ : Fin l => T.finite_toSet)).image (fun x j => x j.1 j.2)).subset ?_
    intro mu hmu
    exact ⟨fun i u => mu (i, u), hmu.2, rfl⟩
  refine ⟨hSfin.toFinset, fun mu hmu => (hSfin.mem_toFinset.1 hmu).1, fun mu hmu hmuS => ?_, ?_⟩
  · rw [hSfin.mem_toFinset] at hmuS
    obtain ⟨i, hi⟩ : ∃ i, (fun u => mu (i, u)) ∉ T := by
      by_contra hcon
      push_neg at hcon
      exact hmuS ⟨hmu, hcon⟩
    obtain ⟨gm, g1, g2, g3, g4⟩ := hmu
    obtain ⟨c', hc', hcc⟩ := hC3 (fun idx => gm (a idx)) ⟨gm, g1, g2, g3, fun idx => OrbTrace.cm_refl _⟩
    have hcong : ∀ v, CongMod N (mu (i, v)) (k y (c' (i, v))) := fun v =>
      OrbTrace.cm_trans (g4 _) (OrbTrace.cm_map (k y) (OrbTrace.cm_symm (hcc _)))
    have hnot : (fun u => mu (i, u)) ∉ S₀ (fun u => c' (i, u)) (c i) := fun h =>
      hi (Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩⟩)
    have h1 := hSb (fun u => c' (i, u)) (c i) (fun u => mu (i, u)) hcong hnot
    have hnn : ∀ fi i', 0 ≤ qW W (Φ.δ y fi) (fun u => mu (i', u)) := fun fi i' =>
      qW_nonneg Φ.posW (Φ.bal y fi).1 (Φ.nonneg y fi) _
    calc (j : ℤ) ≤ j' := by exact_mod_cast hjj
      _ ≤ ∑ fi, qW W (Φ.δ y fi) (fun u => mu (i, u)) := h1
      _ ≤ ∑ fi, lin W mu (Φ.δ y fi) := Finset.sum_le_sum fun fi _ =>
          Finset.single_le_sum (f := fun i' => qW W (Φ.δ y fi) (fun u => mu (i', u))) (fun i' _ => hnn fi i')
            (Finset.mem_univ i)
  · have key : ∀ c' ∈ C, ∀ i (U : Finset (Fin s → Φ.X y)), S₀ (fun u => c' (i, u)) (c i) ⊆ U →
        (∀ ν ∈ U, ∀ v, CongMod N (ν v) (k y (c' (i, v)))) →
        ev' (f (fun u => c' (i, u)) (c i)) - io (∑ ν ∈ U, Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν) ∈
          maximalIdeal V' ^ j' := by
      intro c' hc' i U hU hU'
      rw [← Finset.sum_sdiff hU, map_add (f := _)]
      have e2 : ∀ x y z : V', x - (y + z) = (x - z) - y := fun _ _ _ => by ring
      rw [e2]
      refine sub_mem (hSc _ _) (hmap j' (Ideal.mem_map_of_mem io (Ideal.sum_mem _ fun ν hν => ?_)))
      obtain ⟨hνU, hνS⟩ := Finset.mem_sdiff.1 hν
      exact term_mem Φ y ν (c i) j' (hSb _ _ ν (hU' ν hνU) hνS)
    have hsum := OrbTrace.sum_orbit_eq C hC1 hC2 hC3 (k y) (hk y) T hSfin.toFinset (fun mu => hSfin.mem_toFinset)
      (fun i ν => Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν)
    have hF' : ev' F - io (∑ mu ∈ hSfin.toFinset, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) *
        mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v))) ∈ maximalIdeal V' ^ j' := by
      rw [hsum]
      rw [← Ideal.Quotient.eq]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, map_sum ev', map_sum io, map_sum (Ideal.Quotient.mk _), map_sum (Ideal.Quotient.mk _)]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      rw [map_prod ev', map_prod io, map_prod (Ideal.Quotient.mk _), map_prod (Ideal.Quotient.mk _)]
      refine Finset.prod_congr rfl fun i _ => Ideal.Quotient.eq.2 (key c' hc' i _ ?_ ?_)
      · intro ν hν
        exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hν⟩⟩,
          hSa _ _ ν hν⟩
      · intro ν hν
        exact (Finset.mem_filter.1 hν).2
    have hD : ev' F - io (Φ.ev y g₀) ∈ ((maximalIdeal A ^ e).map (Φ.ev y)).map io := by
      have h1 := Ideal.mem_map_of_mem ev' hbF
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, map_mul, map_sub] at h1
      have hu : IsUnit (ev' b) := by
        by_contra h
        exact hb (by rw [← hcomap]; exact Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have h2 := (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
      have h3 : ev' (algebraMap A (integralClosure A L) g₀) = io (Φ.ev y g₀) := RingHom.congr_fun hcomm g₀
      rwa [h3] at h2
    rw [← hpure (maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y))]
    refine Ideal.mem_comap.2 ?_
    rw [Ideal.map_sup, map_sub]
    have h4 := sub_mem (Ideal.mem_sup_left (T := ((maximalIdeal A ^ e).map (Φ.ev y)).map io) (hJj hF'))
      (Ideal.mem_sup_right (S := (maximalIdeal (Φ.V y) ^ j).map io) hD)
    rwa [sub_sub_sub_cancel_left] at h4

end GlobalTheory.Poinc.SFour
end

