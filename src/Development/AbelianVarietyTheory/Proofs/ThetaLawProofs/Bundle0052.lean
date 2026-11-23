module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZeros
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFinsetKTrivOfSubring
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory


open scoped CategoryTheory.Obj in
theorem exists_finset_kTriv_of_subring :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) [IsNoetherianRing R₀] (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → Out.RelAmple A₀ L₀ → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.KTriv A₁ (L₀.pull π) := by
  intro S _ _ R₀ _ P A₀ _ φ L₀ hA hL hamp hφ e
  let r : S →+* IsLocalRing.ResidueField S := IsLocalRing.residue S
  letI : GrpObj ((Over.pullback (spMap r)).obj P.A) := Functor.grpObjObj
  have h₁ := isGrpPullback_pullback P.A (spMap r)
  have hc : spMap r ≫ spMap R₀.subtype = spMap (r.comp R₀.subtype) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ := h₁.comp hφ
  rw [hc] at h₂
  have he : LBIso (L₀.pull (pullback.fst P.A.hom (spMap r) ≫ φ))
      (P.L.pull (pullback.fst P.A.hom (spMap r))) :=
    LBIso.symm (LBIso.chartPull (chartPullPull P.L _)
      (chartPullSame L₀ (fun _ : PUnit => pullback.fst P.A.hom (spMap r) ≫ φ) (fun _ => φ) (fun _ => 1) _
        fun _ => rfl) e)
  have hK := (amplePt _ _ _ _ _ _ h₁ _ _ P.isLB (pull_isLB hL _) he P.ample P.ktriv).2
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R₀ A₀ L₀ _ (r.comp R₀.subtype) _ _ hA hL hamp h₂ hK
  have hu : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  refine ⟨{g}, fun R₁ h hF A₁ _ π hπ => H R₁ (Subring.inclusion h) A₁ π ?_ hπ⟩
  have hg₁ : g ∈ R₁ := hF (by simp)
  exact IsUnit.of_mul_eq_one (⟨g, hg₁⟩ : R₁) (Subtype.ext hg)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsInvariantOfSplitZerosTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory

theorem exists_ker_int_matrix_four_of_torsion_lift {G G' : Type} [CommGroup G] [CommGroup G']
    (φ : G →* G') (N g m : ℕ) (hN : 1 ≤ N) (hm : m ∣ N) (ξ : Fin (N ^ (2 * g)) → G)
    (hξ : ∀ a, ξ a ^ N = 1) (hinj : Function.Injective fun a => φ (ξ a))
    (hker : ∀ u : G, u ^ N = 1 → φ u = 1 → u = 1)
    (hG : ∀ k : ℕ, k ∣ N → Nat.card {x : G' // x ^ k = 1} = k ^ (2 * g))
    (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    ∃ a : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin (N ^ (2 * g)), Function.Injective a ∧
      ∀ I c, ∏ r, ξ (a I r) ^ al r c = 1 := by
  classical
  have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hm hN
  have hdet0 : al.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at h1
    exact pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)) h1.symm
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  let ψ : Fin (N ^ (2 * g)) → {x : G' // x ^ N = 1} := fun a =>
    ⟨φ (ξ a), by rw [← map_pow, hξ, map_one]⟩
  have hfin : Finite {x : G' // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hG N dvd_rfl]; positivity)
  have hψ : Function.Bijective ψ :=
    Function.Injective.bijective_of_nat_card_le (fun a a' h => hinj (congrArg Subtype.val h))
      (by rw [hG N dvd_rfl, Nat.card_fin])
  have hc := card_ker_int_matrix_four G' m (2 * g) al hm1 hal fun k hk => hG k (hk.trans hm)
  have hfin2 : Finite {ζ : Fin 4 → G' // ∀ c, ∏ r', ζ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  obtain ⟨e⟩ : Nonempty ((Fin 4 → Fin (m ^ g)) ≃ {ζ : Fin 4 → G' // ∀ c, ∏ r', ζ r' ^ al r' c = 1}) := by
    rw [← Finite.card_eq, hc, Nat.card_pi]
    simp only [Nat.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have htor : ∀ I r, (e I).1 r ^ N = 1 := by
    intro I r
    have h1 : ∏ c, (∏ r', (e I).1 r' ^ al r' c) ^ al r c = 1 := by
      simp only [(e I).2, one_zpow, Finset.prod_const_one]
    simp only [← Finset.prod_zpow, ← zpow_mul] at h1
    rw [Finset.prod_comm] at h1
    have h2 : ∀ r', ∏ c, (e I).1 r' ^ (al r' c * al r c) = if r' = r then (e I).1 r' ^ m else 1 := by
      intro r'
      have h3 := congrFun (congrFun hal' r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul] at h3
      have h4 : ∏ c, (e I).1 r' ^ (al r' c * al r c) = (e I).1 r' ^ (∑ c, al r' c * al r c) := by
        simp only [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add]
      rw [h4, h3]
      split_ifs <;> simp
    simp only [h2, Finset.prod_ite_eq', Finset.mem_univ, if_true] at h1
    obtain ⟨q, rfl⟩ := hm
    rw [pow_mul, h1, one_pow]
  choose a ha using fun I r => hψ.2 ⟨(e I).1 r, htor I r⟩
  have ha' : ∀ I r, φ (ξ (a I r)) = (e I).1 r := fun I r => congrArg Subtype.val (ha I r)
  refine ⟨a, fun I I' h => e.injective (Subtype.ext (funext fun r => ?_)), fun I c => hker _ ?_ ?_⟩
  · rw [← ha', ← ha', h]
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun r _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow]
  · simp only [map_prod, map_zpow, ha', (e I).2]

theorem exists_split_ker_of_split_torsion (laws : Out.Laws) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (N m : ℕ) (hN : IsUnit (N : R)) (hm : m ∣ N)
    (ξ : Fin (N ^ (2 * P.g)) → (𝟙_ (Over (Sp R)) ⟶ P.A)) (hξ : ∀ a, ξ a ^ N = 1)
    (hd : ∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p)
    (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    ∃ ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp R)) ⟶ P.A),
      (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) ∧
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  let k := AlgebraicClosure (IsLocalRing.ResidueField R)
  let f : R →+* k := (algebraMap (IsLocalRing.ResidueField R) k).comp (IsLocalRing.residue R)
  let t : Sp k ⟶ Sp R := Spec.map (CommRingCat.ofHom f)
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hNk : (N : k) ≠ 0 := by simpa using (hN.map f).ne_zero
  letI : CommGroup (𝟙_ (Over (Sp R)) ⟶ P.A) := Hom.commGroup
  letI : CommGroup (Over.mk t ⟶ P.A) := Hom.commGroup
  let φ : (𝟙_ (Over (Sp R)) ⟶ P.A) →* (Over.mk t ⟶ P.A) :=
    MonoidHom.mk' (fun u => toUnit (Over.mk t) ≫ u) fun u v => MonObj.comp_mul _ _ _
  have hφ : ∀ u, (φ u).left = (toUnit (Over.mk t)).left ≫ u.left := fun u => rfl
  obtain ⟨p₀⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨hf, -, -, het, -⟩ := laws.mulN (Sp R) P N hN1
  have het' := het (by simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hmul : ∀ {Z : Over (Sp R)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A N = y ^ N :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨a, ha, ha'⟩ := exists_ker_int_matrix_four_of_torsion_lift φ N P.g m hN1 hm ξ hξ
    (fun a a' h => by
      by_contra hne
      apply hd a a' hne ((toUnit (Over.mk t)).left p₀)
      have h1 : (φ (ξ a)).left p₀ = (φ (ξ a')).left p₀ := congrArg (fun q : Over.mk t ⟶ P.A => q.left p₀) h
      simpa only [hφ, Scheme.Hom.comp_apply] using h1)
    (fun u hu h1 => by
      haveI : PreconnectedSpace (𝟙_ (Over (Sp R))).left :=
        inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
      haveI : Nonempty (Over.mk t).left := ⟨p₀⟩
      apply Over.OverMorphism.ext
      refine eq_of_preconnected_of_unramified (Out.mulA P.A N).left ?_ (toUnit (Over.mk t)).left ?_
      · rw [← Over.comp_left, ← Over.comp_left, hmul, hmul, hu, one_pow]
      · rw [← hφ, ← hφ, h1, map_one])
    (fun j hj => (laws.mulN (Sp R) P j (Nat.pos_of_dvd_of_pos hj hN1)).2.2.2.2 k t (by
      obtain ⟨q, rfl⟩ := hj
      rw [Nat.cast_mul] at hNk
      exact left_ne_zero_of_mul hNk)) al hal
  refine ⟨fun I r => ξ (a I r), fun I I' hI p => ?_, fun I c => ?_⟩
  · obtain ⟨r, hr⟩ := Function.ne_iff.1 (ha.ne hI)
    exact ⟨r, hd _ _ hr p⟩
  · rw [List.prod_ofFn]
    exact ha' I c

theorem exists_kaVal_of_split :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι) (ξ : Fin (degProd x.P.g n l l' ^ (2 * x.P.g)) → Pt x), admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : R) → EtZ x s z ch → (∀ a, ξ a ^ degProd x.P.g n l l' = 1) → (∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p) → ∃ κ, KaVal x n l l' al s κ := by
  intro laws R _ _ _ _ x n l l' al d s z ch ξ ⟨hn, hl, hl', hal⟩ hu hz hξ hd
  have key : ∀ L : ℕ, x.P.g * n < L → (∀ j ≤ x.P.g, L - j * n ∣ degProd x.P.g n l l') →
      ∃ (b : ∀ j, Fin ((L - j * n) ^ x.P.g) → RR x (L - j * n)) (lam : ℕ → Rˣ),
        ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (L - j * n) (al (L - j * n)) (b j) (lam j) := by
    intro L hL hdv
    have h1 : ∀ j, ∃ (b : Fin ((L - j * n) ^ x.P.g) → RR x (L - j * n)) (lam : Rˣ),
        j ≤ x.P.g → IsBasis x b ∧ IsSquareDeterminantComparison x (L - j * n) (al (L - j * n)) b lam := by
      intro j
      by_cases hj : j ≤ x.P.g
      · have h2 : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
        obtain ⟨b, hb⟩ := (GlobalTheory.KeyBasis.main laws R x (L - j * n) (by omega)).1
        obtain ⟨ζ, h3, h4⟩ := exists_split_ker_of_split_torsion laws R x.P _ _ hu (hdv j hj) ξ hξ hd
          _ (hal (L - j * n))
        obtain ⟨lam, h5⟩ := _root_.GlobalTheory.SimilLocal.exists_l2Val laws R x _ _ b ζ
          (isUnit_of_dvd_unit (Nat.cast_dvd_cast (hdv j hj)) hu) (hal _) hb h3 h4
        exact ⟨b, lam, fun _ => ⟨hb, h5⟩⟩
      · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩, 1,
          fun h => absurd h hj⟩
    choose b lam h using h1
    exact ⟨b, lam, h⟩
  have hdv : ∀ j ≤ x.P.g, (l - j * n) * (l' - j * n) ∣ degProd x.P.g n l l' := fun j hj =>
    Finset.dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  obtain ⟨b, lam, hb⟩ := key l hl fun j hj => (dvd_mul_right _ _).trans (hdv j hj)
  obtain ⟨b', lam', hb'⟩ := key l' (hl.trans hl') fun j hj => (dvd_mul_left _ _).trans (hdv j hj)
  obtain ⟨rfl, t, ht⟩ := GlobalTheory.KeyKa.KoszulEx.exists_kosVal laws R x n l d s b z ch (by omega) hl (fun j hj => (hb j hj).1) hz
  obtain ⟨-, t', ht'⟩ := GlobalTheory.KeyKa.KoszulEx.exists_kosVal laws R x n l' _ s b' z ch (by omega) (hl.trans hl')
    (fun j hj => (hb' j hj).1) hz
  have hJ : IsUnit (∏ a, GlobalTheory.KeyKa.jac x s (z a) (ch a)) := IsUnit.prod_univ_iff.2 hz.2.2.1
  exact ⟨_, z, ch, b, b', t, t', hJ.unit, lam, lam', hz, hJ.unit_spec, hb, hb', ht, ht', rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsoOfSamePeriodMatrixLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.SamePeriod

theorem int_eq_of_exp {m m' : ℤ} (h : ∀ n : ℕ, 0 < n →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) = Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / n)) :
    m = m' := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((m' - m).natAbs + 1) (Nat.succ_pos _))
  have hn : (((m' - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : ((m' - m : ℤ) : ℂ) = ((((m' - m).natAbs + 1 : ℕ) : ℤ) * k : ℤ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((m' - m).natAbs + 1 : ℕ) : ℂ) = N at hk hn
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * Real.pi * Complex.I) * hk
  have e' : ((((m' - m).natAbs + 1 : ℕ) : ℤ)) ∣ m' - m := ⟨k, by exact_mod_cast e⟩
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs e' (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

noncomputable def imForm {g m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm (F z) (F w)).im)
    (fun z z' w => by simp [hermForm])
    (fun r z w => by simp [hermForm])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun r z w => by simp [hermForm, Matrix.mulVec_smul])

theorem hermForm_eq_of_im {g m m' : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (Hm' : Matrix (Fin m') (Fin m') ℂ) (F' : (Fin g → ℂ) →ₗ[ℂ] (Fin m' → ℂ)) {s : Set (Fin g → ℂ)}
    (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) (F w) = hermForm Hm' (F' z) (F' w) := by
  have e : imForm Hm F = imForm Hm' F' :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have k : ∀ z w, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im := fun z w =>
    LinearMap.congr_fun₂ e z w
  refine Complex.ext ?_ (k z w)
  simpa [hermForm] using k (Complex.I • z) w

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, (u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem ex_inv_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {z : Fin g → ℂ}
    (hz : z ∈ u.Λ) {n : ℕ} (hn : 0 < n) : u.ex ((n : ℂ)⁻¹ • z) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 hz

theorem exists_equiv (hL : Out.Laws) (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) {g : ℕ}
    (τ : Matrix (Fin g) (Fin g) ℂ) (u : HolUnif P.A P.L g) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a)
    (hW : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) :
    ∃ (u₀ : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u₀.Λ → ℂ)
      (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)), u₀.IsAH Hm χ ∧
      (∀ n : ℕ, (∀ s, ∃! θ, u₀.IsThetaFn Hm χ n θ ∧ u₀.IsFnPow n s θ) ∧
        ∀ θ, u₀.IsThetaFn Hm χ n θ → ∃! s, u₀.IsFnPow n s θ) ∧
      (∀ z, u₀.ex (F z) = u.ex z) ∧
      ∀ a b, (hermForm Hm (F (per τ a)) (F (per τ b))).im = omegaStd a b := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, Hm, χ, Ef, hAH, -, hv, hw, -, hθ, hE, -, hW₀⟩ := hU P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  haveI := u.discrete
  haveI := u₀.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u₀.ker 0).2 u₀.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u₀.ex w)
    refine ⟨⟨w - F z, (u₀.ker _).1 ?_⟩, z, by simp⟩
    have h := u₀.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  refine ⟨u₀, Hm, χ, LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩, hAH, hθ, hF, fun a b => ?_⟩
  have hm : ∀ a, per τ a ∈ u.Λ := fun a => (hΛ _).2 ⟨a, rfl⟩
  have hm₀ : ∀ a, F (per τ a) ∈ u₀.Λ := fun a => by
    rw [← u₀.ker, hF, u.ker]
    exact hm a
  have e : Ef ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ = omegaStd a b := int_eq_of_exp fun n hn => by
    have h₁ := hW₀ n ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
    have h₂ := hW n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
    rw [← map_smul, ← map_smul, hF, hF] at h₁
    have := ((hL.weil _ P n _).1 _ _ (ex_inv_pow u (hm a) hn) (ex_inv_pow u (hm b) hn)).unique h₁ h₂
    exact congrArg Units.val (H1.unitOn_injective this)
  rw [← e]
  exact (hE ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩).symm

theorem exists_hom (hL : Out.Laws) (hU : ThetaUnifAV) (P P' : Out.PolAV (Sp ℂ)) {g : ℕ}
    (τ : Matrix (Fin g) (Fin g) ℂ) (u : HolUnif P.A P.L g) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a)
    (hW : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c))
    (u' : HolUnif P'.A P'.L g) (hΛ' : ∀ z, z ∈ u'.Λ ↔ ∃ a, z = per τ a)
    (hW' : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P'.A P'.L n (u'.ex ((n : ℂ)⁻¹ • per τ a)) (u'.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u.ex z ≫ f = u'.ex z := by
  obtain ⟨v, Hm, χ, F, hA, hθ, hF, hE⟩ := exists_equiv hL hU P τ u hΛ hW
  obtain ⟨v', Hm', χ', F', hA', hθ', hF', hE'⟩ := exists_equiv hL hU P' τ u' hΛ' hW'
  have hH := hermForm_eq_of_im Hm' F'.toLinearMap Hm F.toLinearMap u.full fun z hz w hw => by
    obtain ⟨a, rfl⟩ := (hΛ z).1 hz
    obtain ⟨b, rfl⟩ := (hΛ w).1 hw
    exact (hE' a b).trans (hE a b).symm
  obtain ⟨f, hf, hfe⟩ := exists_hom_of_linear_scaling_hermForm P P' v v' Hm χ Hm' χ' hA hA'
    (fun k => (hθ k).2) (fun k => (hθ' k).1) (F.symm.trans F').toLinearMap 1
    (fun l hl => by
      obtain ⟨z, rfl⟩ := F.surjective l
      rw [← v.ker, hF, u.ker, hΛ, ← hΛ', ← u'.ker, ← hF', v'.ker] at hl
      simpa using hl)
    (fun z w => by
      obtain ⟨z, rfl⟩ := F.surjective z
      obtain ⟨w, rfl⟩ := F.surjective w
      simpa using hH z w)
  refine ⟨f, hf, fun z => ?_⟩
  rw [← hF, ← hfe, ← hF']
  simp

end GlobalTheory.KeyFam.SamePeriod

namespace GlobalTheory.KeyFam
open SamePeriod

theorem exists_iso_of_perLev : Out.Laws → ThetaUnifAV → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (P P' : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (lev' : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A)), PerLev P τ k lev → PerLev P' τ k lev' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ ∀ a, lev' a ≫ e.hom = lev a := by
  rintro hL hU g k τ P P' lev lev' ⟨-, -, -, u, hΛ, hW, hlev⟩ ⟨-, -, -, u', hΛ', hW', hlev'⟩
  obtain ⟨f, hf, hfe⟩ := exists_hom hL hU P' P τ u' hΛ' hW' u hΛ hW
  obtain ⟨f', -, hfe'⟩ := exists_hom hL hU P P' τ u hΛ hW u' hΛ' hW'
  haveI := P.isAb.smooth
  haveI := P'.isAb.smooth
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := P.isAb.comm
  haveI := P'.isAb.comm
  haveI := isReduced_of_smooth_complex _ P.A.hom inferInstance
  haveI := isReduced_of_smooth_complex _ P'.A.hom inferInstance
  let e : P'.A ≅ P.A :=
    { hom := f
      inv := f'
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← Category.assoc, hfe, hfe', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← Category.assoc, hfe', hfe, Category.comp_id] }
  have tors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A), 0 < n → x ^ n = 1 →
      ∃ a, x = u'.ex ((n : ℂ)⁻¹ • per τ a) := fun n x hn hx => by
    obtain ⟨z, rfl⟩ := u'.ex_onto x
    rw [← ex_nsmul, u'.ker, hΛ'] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [← ha, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]⟩
  have h₁ := lam_iso_of_weil_pairings hL ℂ P' P f 2 1 hf Nat.prime_two inferInstance
    fun n x y c hn _ hx hy h => by
      obtain ⟨a, ha⟩ := tors n x hn hx
      obtain ⟨b, hb⟩ := tors n y hn hy
      have h₂ := hW' n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
      rw [← ha, ← hb] at h₂
      rw [pow_one, ((hL.weil _ P' n _).1 _ _ hx hy).unique h h₂, ha, hb, hfe, hfe]
      exact hW n a b _ hn rfl
  have hp : IsGrpPullback P'.A P.A (𝟙 _) f.left := @isGrpPullback_of_iso _ _ _ _ _ e hf
  have hq := LamPull.exists_isSquare hp.1.w
  have hfL : (P.L.pull f.left).IsLB := pull_isLB P.isLB _
  have h₂ := LamPull.lbIso_lam_pull hp P.isLB hfL ⟨idIso _, idIso_isGen hfL⟩ hq
  have h₀ : LBIso (abelian₂ P'.A (lbPow P'.L 1)) (abelian₂ P'.A P'.L) := by
    obtain ⟨w, hw⟩ := lbIso_lbPow_one P'.isLB
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  have l₀ : (abelian₂ P'.A P'.L).IsLB := DVR.linComb_isLB _ P'.isLB _ _
  have l₁ : (abelian₂ P'.A (lbPow P'.L 1)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ P'.isLB _ _) _ _
  have l₂ : (abelian₂ P'.A (P.L.pull f.left)).IsLB := DVR.linComb_isLB _ hfL _ _
  have l₃ : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  refine ⟨e, hf, ⟨_, hq, LBIso.trans l₀ l₂ (pull_isLB l₃ _) (LBIso.trans l₀ l₁ l₂ h₀.symm h₁) h₂⟩, fun a => ?_⟩
  rw [hlev, hlev']
  exact hfe _

end GlobalTheory.KeyFam
end

