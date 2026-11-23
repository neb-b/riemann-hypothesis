module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem cubeRel_of_two_comparisons {S : Type} [CommRing S] (c : S) (u k k' r pa pb pm p0 pab pam pbm pabm : Sˣ)
    (h₁ : (pam * pbm).val = c * (u * k * pa * pb).val) (h₂ : (pabm * pm).val = c * (u * k' * pab * p0).val)
    (hk : k' = 1) (h₀ : p0 * r = 1) : pabm * pa * pb * pm * r * k = pab * pam * pbm := by
  subst hk
  have h0 : (p0 : S) * r = 1 := by rw [← Units.val_mul, h₀, Units.val_one]
  ext
  simp only [Units.val_mul, Units.val_one] at h₁ h₂ ⊢
  linear_combination ((pa : S) * pb * k * r) * h₂ + (c * u * pab * pa * pb * k) * h0 - (pab : S) * h₁

theorem tauBimult_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.TauBimult) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ hψ
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨th, hth, -⟩ := (GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1).1 θ
  obtain ⟨s₀, hs₀, -⟩ := (GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1).2 f
  obtain ⟨r, n, t, t', s, s', hr, hexp, -, hadd⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  have hP : PsiRel D (TF (R := V) (Kbar V)) s₀ := psiRel_of_pullB V D (Kbar V) f s₀ hs₀ hψ
  obtain ⟨hf, hsupp⟩ := _root_.GlobalTheory.UU.theta_support_eq_univ hL hL2 V hV D A G U θ f hθ
  have hne : ∃ j, (s₀ 0).f j ≠ 0 := (pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ 0).2 (hf 0)
  refine (GlobalTheory.T.tau_bimult_psi_even_over_extension_field V D (Kbar V)).1.1 ?_
  intro z J hJ a b m
  obtain ⟨⟨u, hu, -⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D) (F := Kbar V) hG 2 m (a + b)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.UU.SchurComp.components_proportional hL hL2 V hV D A G U 2 (by norm_num) (a + b) m u hu (hsupp (a + b))
  have hs : ∀ i z J, Good D.P.L z J → sval (s i (a + b + 2 • m)) (𝟙 _) z J =
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) *
        (sval (s i (a + b)) (DegPre.trF D (Kbar V) m).left z J * (val u (𝟙 _) z J).val) :=
    fun i => hc (t i) (s i) (hexp i).1
  have h₁ := psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hadd hP hne a b m (a + b) rfl c u hs z J hJ
  have h₂ := psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hadd hP hne (a + b) 0 m (a + b)
    (add_zero _).symm c u hs z J hJ
  rw [zero_add] at h₂
  have h₀ := psi_zero_mul_rigV V D (Kbar V) s₀ hP hne z J hJ
  have hc0 : cT D (TF (R := V) (Kbar V)) 0 = 1 := by
    have h := FirstSlot.cT_add D (TF (R := V) (Kbar V)) 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hk : cubV D.cub z J (cT D _ (a + b)) (cT D _ 0) (cT D _ m) = 1 := by
    rw [hc0]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  exact cubeRel_of_two_comparisons _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ hk h₀

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescendedBundleAmpleSpecialFibre
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.AmpleZero

theorem isField_quot (V : Type) [CommRing V] [IsLocalRing V] :
    IsField (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
  refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 ?_
  rw [zero_add, pow_one]
  infer_instance

theorem exists_prime_ne_zero (F : Type) [Field F] (m : ℕ) : ∃ n : ℕ, n.Prime ∧ m < n ∧ (n : F) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  obtain ⟨n, hn, hpr⟩ := Nat.exists_infinite_primes (max m p + 1)
  refine ⟨n, hpr, by omega, fun h => ?_⟩
  have hd := (CharP.cast_eq_zero_iff F p n).1 h
  rcases (Nat.dvd_prime hpr).1 hd with e | e
  · exact CharP.char_ne_one F p e
  · omega

theorem relAmple_zero : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, RelAmple (t.l 0).Q.B (t.l 0).D.M.L.L := by
  intro hc hL V _ _ _ A G _ _ s t
  obtain ⟨k, σ, hk, hσ⟩ := GlobalTheory.UU.EffSpecial.exists_sec_special hL V A G s t
  have hF := isField_quot V
  obtain ⟨K, _, _, φ, -⟩ : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K)
      (_ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* K), True := by
    let := hF.toField
    exact ⟨AlgebraicClosure (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), inferInstance, inferInstance,
      algebraMap _ _, trivial⟩
  obtain ⟨n, hn, hlt, hne⟩ := exists_prime_ne_zero K (2 * k)
  have hu : IsUnit (n : V) := by
    by_contra h
    have hm : (n : V) ∈ IsLocalRing.maximalIdeal V ^ (0 + 1) := by
      rw [zero_add, pow_one]; exact h
    have e := congrArg φ (Ideal.Quotient.eq_zero_iff_mem.2 hm)
    rw [map_natCast, map_natCast, map_zero] at e
    exact hne e
  refine GlobalTheory.AmpleCrit.relAmple_of_effective hc _ hF (t.l 0).Q.B (t.l 0).Q.isAb (t.l 0).D.M.L (t.l 0).D.M.c k σ hk hσ K
    (Spec.map (CommRingCat.ofHom φ)) n hn hne (Nat.not_dvd_of_pos_of_lt (by omega) hlt) fun x hx hT => ?_
  exact GlobalTheory.UU.SpecialPairing.pairing_nondegenerate hc hL V A G s t K _ n hu x hx fun y hy =>
    KerPair.cubWeil_of_gen hL.globalFns _ _ (t.l 0).Q.isAb _ _ n _ x y hx hy hT

end GlobalTheory.UU.AmpleZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenPsiOfThetaExpansionPsiRelation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiEven_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.PsiEven) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ hψ
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨th, hth, -⟩ := GlobalTheory.UU.PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.UU.PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨r, n, t, t', s, s', hr, hE, -, hB⟩ := GlobalTheory.AddClosure.main hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  have hP : PsiRel D (TF (R := V) (Kbar V)) s₀ := GlobalTheory.psiRel_of_pullB V D (Kbar V) f s₀ hs₀ hψ
  have hsupp := _root_.GlobalTheory.UU.theta_support_eq_univ hL hL2 V hV D A G U θ f hθ
  have h0 : ∃ j, (s₀ 0).f j ≠ 0 := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ 0).2 (hsupp.1 0)
  rw [← (GlobalTheory.TauValues.main V D (Kbar V)).2]
  intro z J hJ m
  obtain ⟨⟨u, hu, -⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D) (F := Kbar V) hG 2 m 0
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.UU.SchurComp.components_proportional hL hL2 V hV D A G U 2 (by norm_num) 0 m u hu (hsupp.2 0)
  have e1 := GlobalTheory.psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hB hP h0 0 0 m 0
    (add_zero 0).symm a u (fun i z J hJ => ha _ _ (hE i).1 z J hJ) z J hJ
  have e2 := GlobalTheory.T.psi_mul_psi_addition_second_variable V D (Kbar V) s₀ r n s s' hr hB hP h0 m 0 rfl a u
    (fun i z J hJ => ha _ _ (hE i).2 z J hJ) z J hJ
  have hc0 : cT D (TF (R := V) (Kbar V)) 0 = 1 := by
    have h := GlobalTheory.FirstSlot.cT_add D (TF (R := V) (Kbar V)) 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hcub : cubV D.cub z J (cT D (TF (R := V) (Kbar V)) 0) (cT D (TF (R := V) (Kbar V)) 0)
      (cT D (TF (R := V) (Kbar V)) m) = 1 := by
    rw [hc0]
    exact (isCub_cubV D.cub hJ).face _ _
  simp only [hcub, _root_.mul_one] at e1
  have e4 := Units.ext (e1.trans e2.symm)
  rw [_root_.mul_assoc] at e4
  erw [_root_.zero_add] at e4
  exact (mul_left_cancel e4).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismOfMultiplicativeSectionFamilyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_automorphism_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  first | exact @GlobalTheory.exists_iso_of_multiplicative_section_family | exact GlobalTheory.exists_iso_of_multiplicative_section_family | (intros; apply GlobalTheory.exists_iso_of_multiplicative_section_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.CubeProj

open CubeGen

theorem isProjBy_baseChange {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : IsProjBy f) {φ : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (h : IsPullback φ f' f t) : IsProjBy f' := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective t
  obtain ⟨H, hH, n, s, hs⟩ := hf
  have hH' : (H.pull φ).IsLB := DVR.linComb_isLB _ hH _ _
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hH'
  choose s' hs' using fun (j : Fin (n + 1)) => (GlobalTheory.SecPullIso.section_pull X X' φ H _ w hH hH' hw (s j)).1.exists
  refine ⟨_, hH', n, s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g.hom X' f' φ h.w ?_
    _ w s' hH' hw hs'⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have : IsClosedImmersion (pullback.lift φ f' h.w) := by rw [e]; infer_instance
  exact this

theorem exists_gen_theta_of_isProjBy (hG : GlobalFnsSt) (R₀ : Type) [CommRing R₀]
    (A : Over (Spec (CommRingCat.of R₀))) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (hp : IsProjBy A.hom) (M : LB A.left) (hM : M.IsLB) : ∃ t : LB.Gen (Theta A M), t.IsGen := by
  have hI := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hPerf := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy
  have hSegre := GlobalTheory.AbLaw.isProjBy_tensor
  have hClosed := GlobalTheory.TrivLocus.isClosed_trivLocus
  have hOpen := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre hG GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension hG GlobalTheory.KuennethOne.kuenneth_injective)
  have := hA.geomConnected
  have H := fibTriv_clopen M (thφ A (x3 A)) thε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      isProjBy_baseChange hp (IsPullback.of_hasPullback A.hom (j ≫ A.hom))
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ thφ A (x3 A) k) thε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := hPerf R _ _ sm (hSegre R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc),
      fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M (thφ A (x3 A)) thε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M (thφ A (x3 A)) thε (x3 A 2).left := fun t => by
    have hr : Set.range ((Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec ((Spec (CommRingCat.of R₀)).residueField (A.hom t)) ⟶ Spec (CommRingCat.of R₀) => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨(Spec (CommRingCat.of R₀)).residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm))⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM (thφ A (x3 A)) thε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => prod_face _ 0 (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

theorem exists_gen_theta_abelianVariety : GlobalFnsSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen :=
  fun hG K _ _ B _ _ hB hp M hM => exists_gen_theta_of_isProjBy hG K B hB hp M hM

end GlobalTheory.AbLaw.CubeProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosure
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem fe_all_degrees : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U =>
    D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  intro h1 h2 V _ _ _ hV D A G _ _ U hτ hFE
  have hsupp : ∀ N : ℕ, 1 ≤ N → ∃ β, U.Supp (Kbar V) N β := fun N hN => by
    obtain ⟨mu, hmu⟩ := (_root_.GlobalTheory.UU.Weight.main h1 h2 V hV D A G U N hN).2.1 0
    exact ⟨_, hmu⟩
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hFE
  | succ k hk ih =>
    exact GlobalTheory.UU.SchurConst.main h1 h2 V hV D A G U (k + 1) (by omega)
      (_root_.GlobalTheory.UU.FESection.main h1 h2 V hV D A G U hτ k hk hFE ih (hsupp 1 le_rfl) (hsupp k hk))

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIsoStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_polarised_abelianSchemes_iso : GlobalFnsSt → SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) := by
  first | exact @GlobalTheory.unifPre_polarised_iso | exact GlobalTheory.unifPre_polarised_iso | (intros; apply GlobalTheory.unifPre_polarised_iso <;> assumption)
end

