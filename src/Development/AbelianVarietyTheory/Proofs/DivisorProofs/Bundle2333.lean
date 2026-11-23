module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatible
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLineBundleIsoOfAppellHumbertAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

section Helpers
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ}

def twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (Fl (halfL g v)) (halfR g v)
  map_add' v w := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_add (f := _), Pi.add_apply]
  map_smul' c v := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem halfL_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfL g (twistLeft Fl v) = Fl (halfL g v) := halfL_append _ _

theorem halfR_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfR g (twistLeft Fl v) = halfR g v := halfR_append _ _

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem comp_psum {T T' : Over (Sp ℂ)} (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    h ≫ psum A x I = psum A (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

end GlobalTheory.AdjPullFrame

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem ex_twistLeft {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistLeft Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A ≫ f, snd A A] I.down := by
  have e : (sqUnif A u).ex (twistLeft Fl v) = (sqUnif A u).ex v ≫ lift (fst A A ≫ f) (snd A A) := by
    change lift (u.ex (halfL g (twistLeft Fl v))) (u.ex (halfR g (twistLeft Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A ≫ f) (snd A A)
    rw [halfL_twistLeft, halfR_twistLeft, hFl, comp_lift, lift_fst_assoc, lift_snd]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

theorem ex_twistRight {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistMap Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A, snd A A ≫ f] I.down := by
  have e : (sqUnif A u).ex (twistMap Fl v) = (sqUnif A u).ex v ≫ lift (fst A A) (snd A A ≫ f) := by
    change lift (u.ex (halfL g (twistMap Fl v))) (u.ex (halfR g (twistMap Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A) (snd A A ≫ f)
    rw [halfL_twist, halfR_twist, hFl, comp_lift, lift_fst, lift_snd_assoc]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

end GlobalTheory.AdjPullFrame

end Helpers


open GlobalTheory.LamPullFrame GlobalTheory.ProdUnifSq GlobalTheory.AdjPullFrame in
theorem GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
  intro A _ _ g hA _ N _ hN M u Hm χ hM hF f f' F F' _ _ hFe hF'e hadj
  have hp : IsProjOver A.hom := GlobalTheory.ProjSpace.isProjOver_of_relAmple hN
  obtain ⟨U1, h1ex, h1Λ, h1fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A ≫ f, snd A A] I.down)
    (fun I => sumL g I ∘ₗ twistLeft F) (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistLeft u f F hFe I v)
  obtain ⟨U2, h2ex, h2Λ, h2fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A, snd A A ≫ f'] I.down)
    (fun I => sumL g I ∘ₗ twistMap F') (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistRight u f' F' hF'e I v)
  let UN := GlobalTheory.SameFactor.divUnif U1 U2 (h2ex.trans h1ex.symm)
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
    (GlobalTheory.ProjSpace.isProjOver_pullback hp hp) _
    (LB.isLB_div (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)) (g + g) UN
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro w hw p z hz
  obtain ⟨hz2, hz1⟩ := (top_le_preimage_inf _ _ _).1 hz
  change ⊤ ≤ (U1.ex z).left ⁻¹ᵁ _ at hz1 hz2
  rw [h1ex] at hz1 hz2
  have hw' : w ∈ sqLat u.Λ := by
    have h : w ∈ U1.Λ := hw
    rw [h1Λ] at h
    exact h
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw'
  let j1 : (abelian₂ A M).ι := fun I => p.2 I
  let j2 : (abelian₂ A M).ι := fun I => p.1 I
  have hc1 : ⊤ ≤ ((sqUnif A u).ex (twistLeft F z)).left ⁻¹ᵁ (abelian₂ A M).U j1 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j1).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A ≫ f, snd A A] I.down).left) p.2).1 hz1 I
    rw [← Over.comp_left, ← ex_twistLeft u f F hFe I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hc2 : ⊤ ≤ ((sqUnif A u).ex (twistMap F' z)).left ⁻¹ᵁ (abelian₂ A M).U j2 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j2).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A, snd A A ≫ f'] I.down).left) p.1).1 hz2 I
    rw [← Over.comp_left, ← ex_twistRight u f' F' hF'e I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hwt1 : twistLeft F w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨?_, by rw [halfR_twistLeft]; exact hr⟩
    rw [halfL_twistLeft, ← u.ker, hFe, (u.ker _).2 hl, MonObj.one_comp]
  have hwt2 : twistMap F' w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨by rw [halfL_twist]; exact hl, ?_⟩
    rw [halfR_twist, ← u.ker, hF'e, (u.ker _).2 hr, MonObj.one_comp]
  have fac1 := lam_factor hM u u rfl hF j1 (twistLeft F z) (twistLeft F w) hwt1 hc1
  have fac2 := lam_factor hM u u rfl hF j2 (twistMap F' z) (twistMap F' w) hwt2 hc2
  rw [halfL_twistLeft, halfL_twistLeft, halfR_twistLeft, halfR_twistLeft, ← map_add (f := _)] at fac1
  rw [halfL_twist, halfL_twist, halfR_twist, halfR_twist, ← map_add (f := _)] at fac2
  have sw := GlobalTheory.AnyAppellHumbert.hermForm_swap hF.1
  have hE : hf Hm (F (halfL g z)) (halfR g w) + hf Hm (halfR g z) (F (halfL g w)) + hf Hm (F (halfL g w)) (halfR g w) =
      hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) + hf Hm (halfL g w) (F' (halfR g w)) := by
    have e1 : hf Hm (F (halfL g z)) (halfR g w) = hf Hm (halfL g z) (F' (halfR g w)) := hadj _ _
    have e3 : hf Hm (F (halfL g w)) (halfR g w) = hf Hm (halfL g w) (F' (halfR g w)) := hadj _ _
    have e2 : hf Hm (halfR g z) (F (halfL g w)) = hf Hm (F' (halfR g z)) (halfL g w) := by
      change hermForm Hm (halfR g z) (F (halfL g w)) = hermForm Hm (F' (halfR g z)) (halfL g w)
      rw [sw (F (halfL g w)) (halfR g z), hadj, ← sw]
    rw [e1, e2, e3]
  rw [hE] at fac1
  have n1 : (lamUnif u u rfl).fr j1 (twistLeft F (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add (f := _), ex_add_mem (sqUnif A u) _ hwt1]
    exact hc1
  have n2 : (lamUnif u u rfl).fr j2 (twistMap F' (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add (f := _), ex_add_mem (sqUnif A u) _ hwt2]
    exact hc2
  have hP1 : ∀ v, U1.fr p.2 v = (lamUnif u u rfl).fr j1 (twistLeft F v) := fun v => by
    refine (h1fr p.2 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j1 (twistLeft F v)).symm)
    rfl
  have hP2 : ∀ v, U2.fr p.1 v = (lamUnif u u rfl).fr j2 (twistMap F' v) := fun v => by
    refine (h2fr p.1 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j2 (twistMap F' v)).symm)
    rfl
  have hUN : ∀ v, UN.fr p v = U2.fr p.1 v * (U1.fr p.2 v)⁻¹ := fun v => rfl
  rw [hUN, hUN, hP1, hP1, hP2, hP2, fac1, fac2]
  have ne := Complex.exp_ne_zero (↑Real.pi * (hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) +
    hf Hm (halfL g w) (F' (halfR g w))))
  field_simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.LeadTerm

theorem int_bound {X : Type} [AddCommGroup X] (q : X → ℤ) (h0 : ∀ x, 0 ≤ q x) (hz : q 0 = 0)
    (hneg : ∀ a, q (-a) = q a)
    (hcub : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b))
    (m α : X) (j : ℕ) (hj : q α ≤ j) : q α ≤ j * q m + q (m + α) := by
  have hlin : ∀ (n : ℕ) (y : X),
      q (n • m + y) = q (n • m) + q y + n * (q (m + y) - q m - q y) := by
    intro n y
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hcub (n • m) m y
      rw [succ_nsmul]
      push_cast
      linarith
  have h2 : q (m + m) = 4 * q m := by
    have h := hcub m m (-m)
    simp only [add_neg_cancel_right, add_neg_cancel, hneg, hz] at h
    linarith
  have hsq : ∀ n : ℕ, q (n • m) = (n : ℤ) ^ 2 * q m := by
    intro n
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hlin n m
      rw [succ_nsmul, h, ih, h2]
      push_cast
      ring
  rcases (h0 m).lt_or_eq with hm | hm
  · have : (j : ℤ) ≤ j * q m := by nlinarith
    linarith [h0 (m + α)]
  · have hB : q α ≤ q (m + α) := by
      by_contra hlt
      push_neg at hlt
      set n : ℕ := (q α).toNat + 1 with hn
      have hnz : (n : ℤ) = q α + 1 := by
        rw [hn]; push_cast; rw [Int.toNat_of_nonneg (h0 α)]
      have h := hlin n α
      rw [hsq n, ← hm] at h
      have hpos := h0 (n • m + α)
      rw [hnz] at h
      nlinarith
    rw [← hm]
    linarith

theorem exists_mul_eq_of_addVal_le {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] (x y : R)
    (h : IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ y) ≤
      IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ x)) :
    ∃ s ∉ P, ∃ a : R, s * x = a * y := by
  obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  have hinj := IsLocalization.injective (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P)
  refine ⟨s, s.2, a, hinj ?_⟩
  have hs := IsLocalization.mk'_spec (Localization.AtPrime P) a s
  rw [map_mul, map_mul, hc, ← hs]
  ring

theorem lead_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax α
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hκ0 : κ 0 = 1 := by
    have h := hcub 0 0 0
    simp only [add_zero] at h
    exact mul_right_cancel (b := κ 0 * κ 0 * κ 0)
      (by simpa only [_root_.mul_assoc, _root_.one_mul] using h)

  have hr : ∀ x, ∃ s : R, (κ x : K) = algebraMap R K s := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, by simp [hx, hκ0]⟩
    · obtain ⟨s, -, hs⟩ := hmax x hx
      exact ⟨s, hs⟩
  choose r hr using hr
  have hr0 : ∀ x, r x ≠ 0 := by
    intro x h
    have := hr x
    rw [h, map_zero] at this
    exact (κ x).ne_zero this
  have hrneg : ∀ a, r (-a) = r a := by
    intro a; apply hinjK; rw [← hr, ← hr, hneg]
  have hrz : r 0 = 1 := by
    apply hinjK; rw [← hr, hκ0]; simp
  have hrcub : ∀ a a' b, r (a + a' + b) * r a * r a' * r b = r (a + a') * r (a + b) * r (a' + b) := by
    intro a a' b
    apply hinjK
    simp only [map_mul, ← hr]
    exact_mod_cast congrArg Units.val (hcub a a' b)

  have hZ : ∀ (j : ℕ) (m : X), ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) =
      algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α) := by
    intro j m
    have hm0 : algebraMap R K (r m) ≠ 0 := by rw [← hr]; exact (κ m).ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hr, map_mul, map_pow]
    field_simp
    ring

  set Φ : Ideal R → ℕ → Prop := fun P j => ∀ m, ∃ s ∉ P, ∃ a : R, s * (r m ^ j * r (m + α)) = a * r α
  have hloc : ∀ P : Ideal R, ∀ hP : P.IsPrime, P.height = 1 →
      ∃ J : ℕ, (r α ∉ P → J = 0) ∧ ∀ j ≥ J, Φ P j := by
    intro P hP h1
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
    set D := Localization.AtPrime P
    have hne : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) ≠ ⊤ := by
      intro x h
      rw [IsDiscreteValuationRing.addVal_eq_top_iff] at h
      exact hr0 x (IsLocalization.injective D (Ideal.primeCompl_le_nonZeroDivisors P)
        (by rw [h, map_zero]))
    set v : X → ℕ := fun x => (IsDiscreteValuationRing.addVal D (algebraMap R D (r x))).toNat
    have he : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) = (v x : ℕ∞) :=
      fun x => (ENat.coe_toNat (hne x)).symm
    have hvz : v 0 = 0 := by
      have := he 0
      rw [hrz, map_one, IsDiscreteValuationRing.addVal_one] at this
      exact_mod_cast this.symm
    have hvneg : ∀ a, v (-a) = v a := by intro a; simp only [v, hrneg]
    have hvcub : ∀ a a' b, v (a + a' + b) + v a + v a' + v b = v (a + a') + v (a + b) + v (a' + b) := by
      intro a a' b
      have := congrArg (fun t => IsDiscreteValuationRing.addVal D (algebraMap R D t)) (hrcub a a' b)
      simp only [map_mul, IsDiscreteValuationRing.addVal_mul, he] at this
      exact_mod_cast this
    refine ⟨v α, fun hα => ?_, fun j hj m => ?_⟩
    · have hu : IsUnit (algebraMap R D (r α)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff D P (r α)).mpr hα
      have := he α
      rw [← hu.unit_spec, IsDiscreteValuationRing.addVal_eq_zero_of_unit] at this
      exact_mod_cast this.symm
    · have hb := int_bound (fun x => (v x : ℤ)) (fun x => by positivity) (by simp [hvz])
        (fun a => by simp [hvneg]) (fun a a' b => by exact_mod_cast hvcub a a' b) m α j
        (by exact_mod_cast hj)
      have hb' : v α ≤ j * v m + v (m + α) := by exact_mod_cast hb
      apply exists_mul_eq_of_addVal_le P
      rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        he, he, he, nsmul_eq_mul]
      exact_mod_cast hb'

  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one (hr0 α)
  have hev : ∀ P ∈ {P : Ideal R | P.IsPrime ∧ P.height = 1 ∧ r α ∈ P},
      ∀ᶠ j in Filter.atTop, Φ P j := by
    rintro P ⟨hP, h1, -⟩
    obtain ⟨J, -, hJ⟩ := hloc P hP h1
    exact Filter.eventually_atTop.mpr ⟨J, hJ⟩
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp ((Filter.eventually_all_finite hfin).mpr hev)
  have hall : ∀ j ≥ J, ∀ P : Ideal R, P.IsPrime → P.height = 1 → Φ P j := by
    intro j hj P hP h1
    by_cases hα : r α ∈ P
    · exact hJ j hj P ⟨hP, h1, hα⟩
    · obtain ⟨J', hJ'0, hJ'⟩ := hloc P hP h1
      exact hJ' j (by rw [hJ'0 hα]; exact Nat.zero_le _)

  have hint : ∀ j ≥ J, ∀ m, ∃ c : R,
      algebraMap R K c = ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) := by
    intro j hj m
    rw [hZ]
    have hα0 : algebraMap R K (r α) ≠ 0 := by rw [← hr]; exact (κ α).ne_zero
    obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (K := K)
      (algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α)) (by
        intro P hP h1
        obtain ⟨s, hs, a, ha⟩ := hall j hj P hP h1 m
        refine ⟨s, hs, a, ?_⟩
        rw [mul_div_assoc', ← map_mul, ha, map_mul, mul_div_cancel_right₀ _ hα0])
    exact ⟨c, hc⟩

  have hstep : ∀ k ≥ J + 2, ∀ m, ∃ c : R,
      ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) = algebraMap R K (r m * c) := by
    intro k hk m
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, hc⟩ := hint (i - 1) (by omega) m
    refine ⟨c, ?_⟩
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at hc
    rw [pow_succ', _root_.mul_assoc, Units.val_mul, ← hc, map_mul, hr]
  refine ⟨J + 2, fun k hk => ⟨fun m hm => ?_, fun n => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hstep k hk m
    obtain ⟨s, hs, hsκ⟩ := hmax m hm
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩
  · refine (_root_.GlobalTheory.QuadTend.finite_not_mem_pow R X κ hneg hcub hmax n).subset ?_
    intro m hm hm'
    apply hm
    obtain ⟨s, hs, hsκ⟩ := hm'
    obtain ⟨c, hc⟩ := hstep k hk m
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩

end GlobalTheory.LeadTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumCoc
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.diagSum_coc : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (N : ℕ), (p : R) ^ N = 0 → diagSum R (G.A N) (p ^ N) (d.coc N) = chi (p ^ N) d.g (G.A N) (t.y N) := by
  intro R _ A _ p G t c d N hN
  let e : ℕ → (G.A N →ₐ[R] G.A N) := fun j ↦ (toConv (AlgHom.id R (G.A N)) ^ j).ofConv
  let K : ℕ → G.A N := fun j ↦ fv d.f (G.A N) (G.A N) (e j) (t.y N) + e j (d.h N)
  have hm : ∀ j, (mulBy R (G.A N) j : G.A N →ₐ[R] G.A N) = e j := fun j ↦ by
    have h := comp_mulBy_pts (AlgHom.id R (G.A N)) j
    rwa [AlgHom.id_comp] at h
  have hy : ∀ j, spOver (e j) ≫ t.y N = t.y N ^ j := fun j ↦ by
    rw [← hm]; exact t.mulBy_y N j
  have he1 : e 1 = AlgHom.id R (G.A N) := by simp only [e, pow_one, ofConv_toConv]
  have hes : ∀ i, (toConv (e i) * toConv (AlgHom.id R (G.A N))).ofConv = e (i + 1) := fun i ↦ by
    simp only [e, toConv_ofConv, pow_succ]
  have hterm : ∀ i, Algebra.TensorProduct.lift (mulBy R (G.A N) i : G.A N →ₐ[R] G.A N) (AlgHom.id R (G.A N))
      (fun _ _ ↦ Commute.all _ _) (d.coc N) = d.g (G.A N) (t.y N ^ i) (t.y N) - (K (i + 1) - K i - K 1) := by
    intro i
    rw [hm i, Dat.lift_coc R A p G t c d N (G.A N) (e i) (AlgHom.id R _), hy, spOver_id, Category.id_comp, hes]
    simp only [K, he1]
  have hq : e (p ^ N) = e 0 := t.inj N (G.A N) _ _ (by rw [hy, hy, t.y_pow, pow_zero])
  have hz : ((p ^ N : ℕ) : G.A N) = 0 := by
    rw [Nat.cast_pow, ← map_natCast (algebraMap R (G.A N)), ← map_pow, hN, map_zero]
  rw [diagSum, LinearMap.sum_apply]
  simp only [AlgHom.toLinearMap_apply, hterm]
  rw [chi, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ K j), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hz, zero_mul, sub_zero]
  have : K (p ^ N) = K 0 := by simp only [K, hq]
  rw [this, sub_self, sub_zero]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOfTensorSectionAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.CanTens

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

theorem presents_dual {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (-D) (CechPic.dual L) fun i => (r i)⁻¹ := by
  refine ⟨isLB_dual h.isLB, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  change (((r i)⁻¹ : X.functionFieldˣ) : X.functionField) =
    fnOf (L.U i ⊓ L.U j) hij ((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) * ((r j)⁻¹ : X.functionFieldˣ)
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, h.isRatSec i j hij, mul_inv]

end GlobalTheory.LatChain.CanTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTorsionBundleAbelianSchemeSqZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero : ∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  first | (exact @GlobalTheory.CechPic.exists_isGen_of_lbPow_of_sqZero_abelianScheme) | (exact GlobalTheory.CechPic.exists_isGen_of_lbPow_of_sqZero_abelianScheme) | (intros; apply GlobalTheory.CechPic.exists_isGen_of_lbPow_of_sqZero_abelianScheme <;> assumption)
end

