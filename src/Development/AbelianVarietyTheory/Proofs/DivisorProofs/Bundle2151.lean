module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.FormLocal

open KaehlerDifferential
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

section Alg

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C}

theorem mul_eq_zero_of_sq (hJ : J ^ 2 = 0) {a b : C} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

def diffDer (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) :
    letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
    Derivation R B C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  { toFun := fun b ↦ ρ₁ b - ρ₂ b
    map_add' := fun a b ↦ by simp only [map_add (f := _)]; ring
    map_smul' := fun r b ↦ by
      simp only [map_smul, RingHom.id_apply, smul_sub]
    map_one_eq_zero' := by simp
    leibniz' := fun a b ↦ by
      change ρ₁ (a * b) - ρ₂ (a * b) = ρ₂ a * (ρ₁ b - ρ₂ b) + ρ₂ b * (ρ₁ a - ρ₂ a)
      have h0 := mul_eq_zero_of_sq hJ (hd a) (hd b)
      simp only [map_mul]
      linear_combination h0 }

def diffLam (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) : Ω[B⁄R] →+ C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).toAddMonoidHom

variable (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

theorem diffLam_smul (b : B) (m : Ω[B⁄R]) :
    diffLam hJ ρ₁ ρ₂ hd (b • m) = ρ₂ b * diffLam hJ ρ₁ ρ₂ hd m := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).map_smul b m

theorem diffLam_D (t : B) : diffLam hJ ρ₁ ρ₂ hd (D R B t) = ρ₁ t - ρ₂ t := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact (diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential_comp_D t

theorem diffLam_mem (m : Ω[B⁄R]) : diffLam hJ ρ₁ ρ₂ hd m ∈ J := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => rw [diffLam_smul, diffLam_D]; exact J.mul_mem_left _ (hd c)
  | h0 => rw [map_zero]; exact J.zero_mem
  | ha x y hx hy => rw [map_add (f := _)]; exact J.add_mem hx hy

end Alg

section Alg2

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C} (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

def diagLift : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] C where
  toFun c := ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]; ring
  map_mul' a b := by
    have h0 := mul_eq_zero_of_sq hJ (diffLam_mem hJ ρ₁ ρ₂ hd a.snd) (diffLam_mem hJ ρ₁ ρ₂ hd b.snd)
    have e : (MulOpposite.op b.fst • a.snd : Ω[B⁄R]) = b.fst • a.snd := rfl
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, map_add (f := _), e, diffLam_smul]
    linear_combination -h0
  commutes' r := by
    simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem diagLift_apply (c : TrivSqZeroExt B Ω[B⁄R]) :
    diagLift hJ ρ₁ ρ₂ hd c = ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd := rfl

theorem diagLift_inl (b : B) : diagLift hJ ρ₁ ρ₂ hd (TrivSqZeroExt.inl b) = ρ₂ b := by
  simp [diagLift_apply]

theorem diagLift_diagSec (b : B) : diagLift hJ ρ₁ ρ₂ hd (diagSec R B b) = ρ₁ b := by
  rw [diagLift_apply, fst_derSec, snd_derSec, diffLam_D]; ring

theorem diagLift_sub_mem (c : TrivSqZeroExt B Ω[B⁄R]) : diagLift hJ ρ₁ ρ₂ hd c - ρ₂ c.fst ∈ J := by
  rw [diagLift_apply, add_sub_cancel_left]; exact diffLam_mem hJ ρ₁ ρ₂ hd _

end Alg2

section Repr

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_sum_smul_D (m : Ω[B⁄R]) : ∃ (n : ℕ) (r t : Fin n → B), m = ∑ k, r k • D R B (t k) := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => exact ⟨1, fun _ ↦ b, fun _ ↦ c, by simp⟩
  | h0 => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | ha x y hx hy =>
    obtain ⟨n, r, t, rfl⟩ := hx
    obtain ⟨n', r', t', rfl⟩ := hy
    refine ⟨n + n', Fin.append r r', Fin.append t t', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end Repr

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {U : X.Opens}

def valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) : CechDR.Sec s U →ₐ[R] C :=
  { (GlobalTheory.Points.valMap y U hy).hom with
    commutes' := fun r ↦ by
      have e1 := GlobalTheory.Points.valR_appLE y s (U := ⊤) (V := U) le_top hy
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [hs, GlobalTheory.Points.valR_specMap, GlobalTheory.Points.valR_eq y U hy] at e1
      exact e1 }

theorem valR_eq_valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) (f : Γ(X, U)) : valR y U f = valHom y hy hs f :=
  GlobalTheory.Points.valR_eq y U hy f

theorem valHom_pt {C : Type} [CommRing C] [Algebra R C] (hU : IsAffineOpen U) (y : Sp C ⟶ X)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (hs : y ≫ s = spMap (algebraMap R C)) :
    spMap (valHom y hy hs : CechDR.Sec s U →+* C) ≫ CechDR.affPt s ⟨U, hU⟩ = y :=
  GlobalTheory.Points.specMap_valMap_fromSpec hU y hy

theorem ringHom_ext_affPt {C : Type} [CommRing C] (hU : IsAffineOpen U) {a b : CechDR.Sec s U →+* C}
    (h : spMap a ≫ CechDR.affPt s ⟨U, hU⟩ = spMap b ≫ CechDR.affPt s ⟨U, hU⟩) : a = b := by
  have h1 : spMap a = spMap b := (cancel_mono hU.fromSpec).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

def diagPr (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    (diagExt R B).thick x hx ⟶ Thick.triv B x hx where
  φ := (diagExt R B).π
  φ₀ := RingHom.id B
  comm _ := rfl
  dp := (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ha,
    fun n hn a ha ↦ by
      have ha' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) a = 0 := ha
      have hm := (divided₂ (diagExt R B).sq).dpow_mem hn ha
      have hm' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) ((divided₂ (diagExt R B).sq).dpow n a) = 0 := hm
      rw [hm', ha', DividedPowers.dpow_eval_zero _ hn]⟩
  pt := by rw [spMap_id, Category.id_comp]

theorem fst_ev_secHom (ω : Form s) (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (j : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R])
    (hj : ∀ b, (j b).fst = b) :
    (ev ω.1 ((diagExt R B).secHom hx j hj)).fst = - ev ω.1 (diagPr B x hx) := by
  have h0 : ev ω.1 ((diagExt R B).secHom hx j hj ≫ diagPr B x hx) = 0 := ω.2 _ rfl rfl
  rw [ev_comp] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Geo

theorem ev_idLift_sub_eq_sum : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ω : Form s) (U : X.Opens), IsAffineOpen U → ∃ (n : ℕ) (r t : Fin n → Γ(X, U)), ∀ (T : Thick (dp0 R) s) (hJ : T.J ^ 2 = 0), T.δ = divided₂ hJ → ∀ (y₁ y₂ : Sp T.B ⟶ X) (h₁ : y₁ ≫ s = spMap (algebraMap R T.B)) (h₂ : y₂ ≫ s = spMap (algebraMap R T.B)) (e₁ : spMap T.π ≫ y₁ = T.x) (e₂ : spMap T.π ≫ y₂ = T.x), ⊤ ≤ y₁ ⁻¹ᵁ U → ⊤ ≤ y₂ ⁻¹ᵁ U → ev ω.1 (idLift T y₂ h₂ e₂) - ev ω.1 (idLift T y₁ h₁ e₁) = ∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
  intro R _ X s ω U hU
  have hx := CechDR.affPt_w s ⟨U, hU⟩
  obtain ⟨n, r, t, hΩ⟩ := exists_sum_smul_D (connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx)
  refine ⟨n, r, t, ?_⟩
  intro T hJ hδ y₁ y₂ h₁ h₂ e₁ e₂ hy₁ hy₂
  have p₁ := valHom_pt hU y₁ hy₁ h₁
  have p₂ := valHom_pt hU y₂ hy₂ h₂
  have hπ : T.π.comp (valHom y₁ hy₁ h₁ : CechDR.Sec s U →+* T.B) = T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B) :=
    ringHom_ext_affPt hU (by rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, p₁, p₂, e₁, e₂])
  have hd : ∀ b, valHom y₁ hy₁ h₁ b - valHom y₂ hy₂ h₂ b ∈ T.J := fun b ↦
    (T.ker _).1 (by rw [map_sub, sub_eq_zero]; exact RingHom.congr_fun hπ b)
  let Φ : (diagExt R (CechDR.Sec s U)).thick (CechDR.affPt s ⟨U, hU⟩) hx ⟶ T :=
    { φ := diagLift hJ _ _ hd
      φ₀ := T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B)
      comm := fun c ↦ by
        have h0 := (T.ker _).2 (diagLift_sub_mem hJ _ _ hd c)
        rw [map_sub, sub_eq_zero] at h0
        exact h0.symm
      dp := by
        have key : DividedPowers.IsDPMorphism (divided₂ (diagExt R (CechDR.Sec s U)).sq) (divided₂ hJ)
            (diagLift hJ _ _ hd : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R] →+* T.B) :=
          isDPMorphism_sqDP _ hJ _ fun (a : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R]) ha ↦ by
            have ha' : a.fst = 0 := ha
            have h0 := diagLift_sub_mem hJ _ _ hd a
            rwa [ha', map_zero, sub_zero] at h0
        rw [hδ]
        exact key
      pt := by rw [Cris.spMap_comp, Category.assoc, p₂, e₂] }
  let a₁ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₁ h₁ :=
    Thick.trivHom (valHom y₁ hy₁ h₁) p₁
  let a₂ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₂ h₂ :=
    Thick.trivHom (valHom y₂ hy₂ h₂) p₂
  have k₂ := Form.ev_sq ω a₂ (idLift T y₂ h₂ e₂)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) Φ rfl rfl
    fun c ↦ (diagLift_inl hJ _ _ hd c).symm
  have k₁ := Form.ev_sq ω a₁ (idLift T y₁ h₁ e₁)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)) Φ rfl rfl
    fun c ↦ (diagLift_diagSec hJ _ _ hd c).symm
  have f₁ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl
  have f₂ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)
  rw [k₁, k₂, add_sub_add_right_eq_sub, ← map_sub]
  change diagLift hJ _ _ hd _ = _
  rw [diagLift_apply, TrivSqZeroExt.fst_sub, f₁, f₂, sub_self, map_zero, zero_add]
  have hc : (ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) -
      ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _))).snd =
      connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, hΩ, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [diffLam_smul, diffLam_D]
  exact (congrArg₂ (fun a b ↦ a * b) (valR_eq_valHom y₂ hy₂ h₂ (r k))
    (congrArg₂ (fun a b ↦ a - b) (valR_eq_valHom y₁ hy₁ h₁ (t k)) (valR_eq_valHom y₂ hy₂ h₂ (t k)))).symm

end GlobalTheory.CechKS.FormLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.CycAwayCover

theorem isUnit_natCast_cycAway {M : ℕ} (hM : M ≠ 0) : IsUnit (M : cycAway M) := by
  refine isUnit_iff_exists_inv.2 ⟨⟨(M : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩, ?_⟩
  exact Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))

def awayToCyc (M : ℕ) (hM : M ≠ 0) : Localization.Away (M : ℤ) →+* cycAway M :=
  IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) (g := Int.castRingHom (cycAway M))
    (by simpa using isUnit_natCast_cycAway hM)

theorem awayToCyc_injective {M : ℕ} (hM : M ≠ 0) : Function.Injective (awayToCyc M hM) := by
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  rw [awayToCyc, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away (M : ℤ)) hle).eq_iff,
    (Int.castRingHom (cycAway M)).injective_int.eq_iff]

theorem finite_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Finite := by
  letI := (awayToCyc M hM).toAlgebra
  have hv : ∀ hx, (⟨(M : ℂ)⁻¹, hx⟩ : cycAway M) =
      algebraMap (Localization.Away (M : ℤ)) (cycAway M) (IsLocalization.Away.invSelf (M : ℤ)) := by
    intro hx
    have h1 : (M : cycAway M) * ⟨(M : ℂ)⁻¹, hx⟩ = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))
    have h2 : (M : cycAway M) * algebraMap (Localization.Away (M : ℤ)) (cycAway M)
        (IsLocalization.Away.invSelf (M : ℤ)) = 1 := by
      have := congrArg (algebraMap (Localization.Away (M : ℤ)) (cycAway M))
        (IsLocalization.Away.mul_invSelf (S := Localization.Away (M : ℤ)) (M : ℤ))
      simpa using this
    exact (isUnit_natCast_cycAway hM).mul_left_cancel (h1.trans h2.symm)
  have hint : Algebra.IsIntegral (Localization.Away (M : ℤ)) (cycAway M) := by
    constructor
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hM, by
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
          exact sub_eq_zero.2 (GlobalTheory.SiegelTor.zetaAway_pow_self hM)⟩
      · convert (isIntegral_algebraMap (R := Localization.Away (M : ℤ)) (x := IsLocalization.Away.invSelf (M : ℤ)) : IsIntegral _ (algebraMap (Localization.Away (M : ℤ)) (cycAway M) _)) using 1
        exact hv _
    | zero => exact isIntegral_zero
    | one => exact isIntegral_one
    | add x y _ _ hx hy => exact hx.add hy
    | neg x _ hx => exact hx.neg
    | mul x y _ _ hx hy => exact hx.mul hy
  haveI : Algebra.FiniteType (Localization.Away (M : ℤ)) (cycAway M) := by
    refine ⟨⟨{zetaAway M}, eq_top_iff.2 ?_⟩⟩
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self _))
      · convert Subalgebra.algebraMap_mem (Algebra.adjoin (Localization.Away (M : ℤ)) ((({zetaAway M} : Finset (cycAway M)) : Set (cycAway M)))) (IsLocalization.Away.invSelf (M : ℤ)) using 1
        exact hv _
    | zero => exact Subalgebra.zero_mem _
    | one => exact Subalgebra.one_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | neg x _ hx => exact Subalgebra.neg_mem _ hx
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  exact (Algebra.IsIntegral.finite : Module.Finite (Localization.Away (M : ℤ)) (cycAway M))

theorem etale_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Etale := by
  letI := (awayToCyc M hM).toAlgebra
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  haveI : IsDomain (Localization.Away (M : ℤ)) := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (M : ℤ)) :=
    IsLocalization.isDedekindDomain ℤ hle (Localization.Away (M : ℤ))
  haveI : Module.Finite (Localization.Away (M : ℤ)) (cycAway M) := finite_awayToCyc hM
  haveI : FaithfulSMul (Localization.Away (M : ℤ)) (cycAway M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (awayToCyc_injective hM)
  haveI : Module.Flat (Localization.Away (M : ℤ)) (cycAway M) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (M : ℤ)) (cycAway M) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI := formallyUnramified_cycAway hM (Localization.Away (M : ℤ))
  exact (Algebra.Etale.of_formallyUnramified_of_flat : Algebra.Etale (Localization.Away (M : ℤ)) (cycAway M))

theorem exists_cycAway_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  intro M S hM hS
  have hM0 : M ≠ 0 := hM.ne'
  have hSu : IsUnit ((Int.castRingHom Γ(S, ⊤)) (M : ℤ)) := by simpa using hS
  let φ : S ⟶ Sp (Localization.Away (M : ℤ)) :=
    S.toSpecΓ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) hSu)
  let S' : Over S := Over.mk (pullback.fst φ (spMap (awayToCyc M hM0)))
  haveI : IsFinite (spMap (awayToCyc M hM0)) := (IsFinite.SpecMap_iff _).2 (finite_awayToCyc hM0)
  haveI : Etale (spMap (awayToCyc M hM0)) := HasRingHomProperty.Spec_iff.2 (etale_awayToCyc hM0)
  refine ⟨S', pullback.snd φ (spMap (awayToCyc M hM0)), ?_, ?_, ?_⟩
  · exact (inferInstance : IsFinite (pullback.fst φ (spMap (awayToCyc M hM0))))
  · exact (inferInstance : Etale (pullback.fst φ (spMap (awayToCyc M hM0))))
  · intro T f t₁
    haveI : IsOpenImmersion (spMap (algebraMap ℤ (Localization.Away (M : ℤ)))) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (M : ℤ))))))
    have e : f ≫ φ = t₁ ≫ spMap (awayToCyc M hM0) :=
      (cancel_mono (spMap (algebraMap ℤ (Localization.Away (M : ℤ))))).1 (specZIsTerminal.hom_ext _ _)
    refine ⟨pullback.lift f t₁ e, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    rintro g ⟨h1, h2⟩
    exact pullback.hom_ext (h1.trans (pullback.lift_fst _ _ e).symm) (h2.trans (pullback.lift_snd _ _ e).symm)

end GlobalTheory.CycAwayCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ObsCob

theorem exists_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T''), L.IsObs θ → L.IsOb2 α w 0 → ∃ g : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))) ∧ ∀ T T' T'' a b, θ T T' T'' a b (w.1 T) = L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w θ hθ h0
  obtain ⟨θ', σ, z, hθ', hσ, hz, hzv⟩ := h0
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  refine ⟨fun T T' a ↦ σ T' (f T T' a), fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · exact (_root_.GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  · have huniq := ((_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
      (L.ker T) (L.B T'') _ _ (L.ρ (a ≫ b)) _ _ (hθ T T' T'' a b)).2.2.1 (hθ' T T' T'' a b))
    rw [huniq, ← (hzv T T' T'' a b).2]
    have hnat := (_root_.GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    rw [← e, d1_apply, map_add (f := _), map_sub, hnat]
    rfl

end GlobalTheory.ObsCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPull

theorem specOf_genericPoint {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) :
    (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ρ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective ρ hρ

theorem exists_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → IsLocalHom ρ → ∀ D : DegData R (maximalIdeal R), ∃ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D.toPre D'.toPre) := by
  intro R R' _ _ _ _ _ _ ρ hρ hloc D
  obtain ⟨L, -⟩ := _root_.GlobalTheory.allSixLaws
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  have hη : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W := by
    rw [specOf_genericPoint ρ hρ]; exact hW
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    ((IsLocalRing.local_hom_tfae ρ).out 1 3).1 hloc
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg L.polBaseChange L.globalFns R R' (maximalIdeal R)
    (maximalIdeal R') ρ hI D W hψ hη
  exact ⟨D', ⟨hD⟩⟩

end GlobalTheory.MumPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBDescent

theorem descCompat_of_lbIso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) →
    ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  intro X Y f L hL hI
  obtain ⟨w, hw⟩ := hI
  have hP := (isGen_iff w).1 hw
  have hle : ∀ i j, chart f L i j ≤ (L.pull (pullback.snd f f)).U (fun _ => j) ⊓ (L.pull (pullback.fst f f)).U (fun _ => i) :=
    fun i j z hz => ⟨mem_pull.2 hz.2, mem_pull.2 hz.1⟩
  refine ⟨fun i j => res (hle i j) (w.s (fun _ => j, fun _ => i)), ?_⟩
  intro z i i' j j' hi hi' hj hj'
  have hc : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b →
      gm (𝟙 _) z (chart f L a b) (res (hle a b) (w.s (fun _ => b, fun _ => a))) =
        gw w (𝟙 _) z b (fun _ => a) := fun a b ha hb =>
    gm_res (𝟙 _) z (hle a b) ⟨ha, hb⟩ _
  have key := hP _ (𝟙 _) z j' j (fun _ => i') (fun _ => i) hj' hj (mem_pull.2 hi') (mem_pull.2 hi)
  have e1 : gm (𝟙 _) z _ ((L.pull (pullback.fst f f)).g (fun _ => i') (fun _ => i)) =
      gm (pullback.fst f f) z _ (L.g i' i) := by
    have := gm_pull_g L (pullback.fst f f) (𝟙 _) z (fun _ => i') (fun _ => i) (mem_pull.2 hi') (mem_pull.2 hi)
    rw [Category.id_comp] at this
    exact this
  have e2 : (gm (pullback.fst f f) z _ (L.g i' i))⁻¹ = gm (pullback.fst f f) z _ (L.g i i') := by
    rw [inv_eq_iff_mul_eq_one, gm_cocycle hL _ z hi' hi hi', gm_self hL _ z hi']
  rw [Category.id_comp, e1, e2] at key
  rw [hc i' j' hi' hj', hc i j hi hj, key]
  ac_rfl

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  first | exact @GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | exact GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | (intros; apply GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus <;> assumption)
end

