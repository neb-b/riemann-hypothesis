module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LatticeTorsion

variable {S : Scheme.{0}}

theorem prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] (X : Over S) (hX : P X.hom) : ∀ k, P (Out.powObj X k).hom
  | 0 => P.id_mem S
  | k + 1 => by
    change P (pullback.fst X.hom (Out.powObj X k).hom ≫ X.hom)
    exact P.comp_mem _ _ (P.pullback_fst _ _ (prop_powObj P X hX k)) hX

theorem existsUnique_torsion (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (x : T ⟶ G)
    (hx : x ^ n = 1) : ∃! y : T ⟶ torsion G n, y ≫ torsion.ι G n = x := by
  refine ⟨pullback.lift x (toUnit T) ((GrpTangent.comp_mulN x n).trans hx),
    pullback.lift_fst _ _ _, fun y hy => ?_⟩
  exact pullback.hom_ext (hy.trans (pullback.lift_fst _ _ _).symm) (toUnit_unique _ _)

theorem torsionι_pow_eq_one (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GrpTangent.comp_mulN]
  refine pullback.condition.trans ?_
  rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
  rfl

theorem eq_prod_zpow {La I A : Type} [AddCommGroup La] [Fintype I] [CommGroup A]
    (b : Module.Basis I ℤ La) (f : La → A) (hf : ∀ a c, f (a + c) = f a * f c) (a : La) :
    f a = ∏ i, f (b i) ^ (b.repr a i) := by
  let φ : Multiplicative La →* A := MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _
  have h : ∀ x, f x = φ (Multiplicative.ofAdd x) := fun _ => rfl
  conv_lhs => rw [← b.sum_repr a]
  simp only [h, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]

end GlobalTheory.LatticeTorsion

namespace GlobalTheory


open LatticeTorsion in
theorem exists_finiteEtale_latticeTorsionHom :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a := by
  intro S G _ _ n La _ _ _ hG hn
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  let b := Module.finBasis ℤ La
  let r := Module.finrank ℤ La
  let Z := Out.powObj (torsion G n) r
  let x : Fin r → (Z ⟶ G) := fun i => Out.powPr (torsion G n) i ≫ torsion.ι G n
  have hx : ∀ i, x i ^ n = 1 := fun i => by
    rw [← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
  let et : La → (Z ⟶ G) := fun a => ∏ i, x i ^ (b.repr a i)
  have hadd : ∀ a c, et (a + c) = et a * et c := fun a c => by
    simp only [et, map_add (f := _), Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et (b i) = x i := fun i => by
    simp only [et, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  refine ⟨Z, et, prop_powObj @IsFinite _ hfin r, prop_powObj @Etale _ het r, hadd, fun a => ?_,
    fun T et' hadd' hpow' => ?_⟩
  · simp only [et, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  · choose y hy hyu using fun i : Fin r => existsUnique_torsion G n (et' (b i)) (hpow' _)
    let h : T ⟶ Z := (Out.powIsLimit (torsion G n) r).lift (Fan.mk T y)
    have hh : ∀ i, h ≫ Out.powPr (torsion G n) i = y i := fun i =>
      (Out.powIsLimit (torsion G n) r).fac (Fan.mk T y) ⟨i⟩
    refine ⟨h, fun a => ?_, fun h' hh' => ?_⟩
    · rw [eq_prod_zpow b (fun a => h ≫ et a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
        eq_prod_zpow b et' hadd' a]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hb, ← hy i, ← hh i, Category.assoc]
    · refine (Out.powIsLimit (torsion G n) r).hom_ext fun ⟨i⟩ => ?_
      refine (hyu i _ ?_).trans (hh i).symm
      have := hh' (b i)
      rw [hb] at this
      exact (Category.assoc _ _ _).trans this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

theorem baseChange_appLE_chartAlgEquiv {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (i : Fin (N + 1)) (q : MvPolynomial {j // j ≠ i} R) :
    ((baseChange N φ).appLE (chart R N i) (chart R' N i) (baseChange_preimage_chart N φ i).ge).hom
      (chartAlgEquiv R N i q) = chartAlgEquiv R' N i (MvPolynomial.map φ q) := by
  have h : ((baseChange N φ).appLE (chart R N i) (chart R' N i)
      (baseChange_preimage_chart N φ i).ge).hom.comp (RingHomClass.toRingHom (chartAlgEquiv R N i)) =
      (RingHomClass.toRingHom (chartAlgEquiv R' N i)).comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_C]
      have h1 : chartAlgEquiv R N i (MvPolynomial.C r) = _ := (chartAlgEquiv R N i).commutes r
      have h2 : chartAlgEquiv R' N i (MvPolynomial.C (φ r)) = _ := (chartAlgEquiv R' N i).commutes (φ r)
      rw [h1, h2, ← formOn_C (i := i) (hi := le_rfl), ← formOn_C (i := i) (hi := le_rfl)]
      have h3 := baseChange_app_formOn φ (le_refl (chart R N i)) (MvPolynomial.isHomogeneous_C _ r)
      refine (congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3).trans ?_
      rw [resG_formOn]
      congr 1
      exact MvPolynomial.map_C _ _
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, chartAlgEquiv_X]
      have h3 := baseChange_app_ratioOn φ (le_refl (chart R N i)) j.1
      exact congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3
  exact congrArg (fun ψ => ψ q) h


set_option backward.isDefEq.respectTransparency false in
theorem comap_map_baseChange {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (I : (PSpace R' N).IdealSheafData) (T : ∀ i : Fin (N + 1), Set (MvPolynomial {j // j ≠ i} R'))
    (hT : ∀ i, Ideal.span (chartAlgEquiv R' N i '' T i) = I.ideal ⟨_, isAffineOpen_chart R' N i⟩)
    (hφ : ∀ i, T i ⊆ Set.range (MvPolynomial.map φ)) :
    (I.map (baseChange N φ)).comap (baseChange N φ) = I := by
  have : IsAffineHom (baseChange N φ) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChange N φ).flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_chart R' N i⟩) (iSup_chart R' N) fun i => ?_
  rw [← hT, Ideal.span_le]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨q, rfl⟩ := hφ i ht
  have h0 : chartAlgEquiv R' N i (MvPolynomial.map φ q) ∈ I.ideal ⟨_, isAffineOpen_chart R' N i⟩ := by
    rw [← hT]
    exact Ideal.subset_span ⟨_, ht, rfl⟩
  rw [← baseChange_appLE_chartAlgEquiv] at h0 ⊢
  refine GlobalTheory.GaloisDescent.ideal_le_comap_appLE (baseChange N φ) le_rfl ⟨_, isAffineOpen_chart R N i⟩
    ⟨_, isAffineOpen_chart R' N i⟩ (baseChange_preimage_chart N φ i).ge ?_
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, Ideal.mem_comap]
  have h1 := I.ideal_le_comap_ideal
    (U := ⟨_, (isAffineOpen_chart R N i).preimage (baseChange N φ)⟩)
    (V := ⟨_, isAffineOpen_chart R' N i⟩) (baseChange_preimage_chart N φ i).le h0
  rw [Ideal.mem_comap, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h1
  rw [Scheme.Hom.app_eq_appLE]
  exact h1

end GlobalTheory.ProjSpace

namespace GlobalTheory


open ProjSpace in
theorem exists_finset_isProjOver_descends : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  classical
  rintro K _ K₀ X p ⟨N, e, he, rfl⟩
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} K),
      Ideal.span (chartAlgEquiv K N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩).comap (chartAlgEquiv K N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv K N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv K N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun K₁ _ hs => ?_⟩
  have key := comap_map_baseChange N K₁.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  refine ⟨(e ≫ baseChange N K₁.subtype).image, (e ≫ baseChange N K₁.subtype).imageι ≫ PSpace.str K₁ N,
    (e ≫ baseChange N K₁.subtype).toImage, ⟨N, _, inferInstance, rfl⟩, ?_⟩
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N K₁.subtype).imageι
    (e ≫ baseChange N K₁.subtype).toImage (baseChange N K₁.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N K₁.subtype)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SimAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem modN_zero (n : ℕ) : D.ModN n 0 := ⟨0, by simp⟩

theorem modN_add {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [smul_add]⟩

theorem modN_neg {n : ℕ} {x : D.La} (hx : D.ModN n x) : D.ModN n (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by rw [smul_neg]⟩

theorem modN_map {n : ℕ} {x : D.La} (f : D.La →ₗ[𝓞 E] D.La) (hx : D.ModN n x) : D.ModN n (f x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨f a, by rw [map_nsmul]⟩

theorem modN_of_mul {n m : ℕ} {x : D.La} (hx : D.ModN (n * m) x) : D.ModN n x := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨m • a, by rw [mul_smul]⟩

theorem dvd_form_sub {n : ℕ} {x x' y y' : D.La} (hx : D.ModN n (x - x')) (hy : D.ModN n (y - y')) :
    (n : ℤ) ∣ D.EF x y - D.EF x' y' := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h1 : x = x' + n • a := by rw [← ha]; abel
  have h2 : y = y' + n • b := by rw [← hb]; abel
  refine ⟨D.EF x' b + D.EF a y' + n * D.EF a b, ?_⟩
  rw [h1, h2]
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  ring

theorem exists_form_eq_one (h : 1 ≤ D.p + D.q) : ∃ a b : D.La, D.EF a b = 1 := by
  haveI := D.fin
  haveI := D.proj
  haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree ℤ D.La :=
    Function.Injective.moduleIsTorsionFree D.EF D.unimod.1 (fun r x => map_smul _ r x)
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem dvd_mult_inv (g : Sim D) {n : ℕ} (hn : 0 < n) {a b : D.La} (hab : D.EF a b = 1)
    (h : D.La →ₗ[𝓞 E] D.La) (hh : ∀ x, D.ModN n (g.f n (h x) - x)) :
    (n : ℤ) ∣ g.ν n * D.EF (h a) (h b) - 1 := by
  have h1 := g.mult n hn (h a) (h b)
  have h2 := dvd_form_sub (hh a) (hh b)
  rw [hab] at h2
  obtain ⟨c, hc⟩ := dvd_sub h2 h1
  exact ⟨c, by linear_combination hc⟩

theorem dvd_mult_tower (g : Sim D) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a b : D.La} (hab : D.EF a b = 1) :
    (n : ℤ) ∣ g.ν (n * m) - g.ν n := by
  have h1 := g.mult n hn a b
  have h2 : (n : ℤ) ∣ _ := Dvd.dvd.trans (by push_cast; exact Dvd.intro _ rfl) (g.mult (n * m) (Nat.mul_pos hn hm) a b)
  have h3 := dvd_form_sub (g.tower n m hn hm a) (g.tower n m hn hm b)
  rw [hab] at h1 h2
  obtain ⟨c, hc⟩ := dvd_add (dvd_sub h3 h2) h1
  exact ⟨c, by linear_combination hc⟩

def one (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := by simpa using modN_zero n
  inv n _ := ⟨LinearMap.id, fun a => by simpa using modN_zero n⟩
  mult n _ a b := by simp

def mul (g g' : Sim D) : Sim D where
  f n := g.f n ∘ₗ g'.f n
  ν n := g.ν n * g'.ν n
  tower n m hn hm a := by
    have h1 := g.tower n m hn hm (g'.f (n * m) a)
    have h2 := modN_map (g.f n) (g'.tower n m hn hm a)
    convert modN_add h1 h2 using 1
    simp
  inv n hn := by
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨h', hh'⟩ := g'.inv n hn
    refine ⟨h' ∘ₗ h, fun a => ⟨?_, ?_⟩⟩
    · convert modN_add (modN_map h' (hh (g'.f n a)).1) (hh' a).1 using 1
      simp
    · convert modN_add (modN_map (g.f n) (hh' (h a)).2) (hh a).2 using 1
      simp
  mult n hn a b := by
    have h1 := g.mult n hn (g'.f n a) (g'.f n b)
    have h2 := Dvd.dvd.mul_left (g'.mult n hn a b) (g.ν n)
    obtain ⟨c, hc⟩ := dvd_add h1 h2
    exact ⟨c, by simp only [LinearMap.comp_apply]; linear_combination hc⟩

theorem exists_inv (g : Sim D) {a b : D.La} (hab : D.EF a b = 1) :
    ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧
      (n : ℤ) ∣ g.ν n * g'.ν n - 1 := by
  have hex : ∀ n : ℕ, ∃ h : D.La →ₗ[𝓞 E] D.La, 0 < n →
      ∀ a, D.ModN n (h (g.f n a) - a) ∧ D.ModN n (g.f n (h a) - a) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨h, hh⟩ := g.inv n hn
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose h hh using hex
  have hν : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n * D.EF (h n a) (h n b) - 1 := fun n hn =>
    dvd_mult_inv g hn hab (h n) fun x => (hh n hn x).2
  refine ⟨⟨h, fun n => D.EF (h n a) (h n b), ?_, ?_, ?_⟩, fun n hn => ⟨hh n hn, hν n hn⟩⟩
  · intro n m hn hm x
    have h1 := modN_neg (hh n hn (h (n * m) x)).1
    have h2 := modN_neg (modN_map (h n) (g.tower n m hn hm (h (n * m) x)))
    have h3 := modN_map (h n) (modN_of_mul (hh (n * m) (Nat.mul_pos hn hm) x).2)
    convert modN_add (modN_add h1 h2) h3 using 1
    simp only [map_sub]
    abel
  · intro n hn
    exact ⟨g.f n, fun x => ⟨(hh n hn x).2, (hh n hn x).1⟩⟩
  · intro n hn x y
    have h1 := Dvd.dvd.mul_left (g.mult n hn (h n x) (h n y)) (D.EF (h n a) (h n b))
    have h2 := Dvd.dvd.mul_left (dvd_form_sub (hh n hn x).2 (hh n hn y).2) (D.EF (h n a) (h n b))
    have h3 := Dvd.dvd.mul_right (hν n hn) (D.EF (h n x) (h n y))
    obtain ⟨c, hc⟩ := dvd_sub (dvd_sub h2 h1) h3
    exact ⟨c, by linear_combination hc⟩

theorem sim_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1) := by
  intro E _ _ _ H D hpq
  obtain ⟨a, b, hab⟩ := exists_form_eq_one hpq
  refine ⟨fun g n m hn hm => ⟨dvd_mult_tower g hn hm hab, ?_⟩, ⟨one D, fun _ => ⟨rfl, rfl⟩⟩,
    fun g g' => ⟨mul g g', fun _ => ⟨rfl, rfl⟩⟩, fun g => exists_inv g hab⟩
  obtain ⟨h, hh⟩ := g.inv n hn
  obtain ⟨c, hc⟩ := dvd_mult_inv g hn hab h fun x => (hh x).2
  exact ⟨D.EF (h a) (h b), -c, by linear_combination hc⟩

end GlobalTheory.SimAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenIsValueAtOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.OriginValue

theorem eq_of_valAt'_eq_of_isIso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) [IsIso x] (W : X.Opens) (f g : Γ(X, W))
    (h : ⊤ ≤ x ⁻¹ᵁ W → valAt' x W f = valAt' x W g) : f = g := by
  by_cases hW : ⊤ ≤ x ⁻¹ᵁ W
  · have h1 := h hW
    rw [valAt'_eq_valAt x hW, valAt'_eq_valAt x hW, valAt, valAt] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have e : (⊤ : (Sp ℂ).Opens) = x ⁻¹ᵁ W := le_antisymm hW le_top
    have : IsIso (homOfLE hW) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
    have : IsIso (x.appLE W ⊤ hW) := by
      unfold Scheme.Hom.appLE
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso (x.appLE W ⊤ hW)).1 h2
  · have hb : W = ⊥ := by
      rw [top_le_preimage_iff_mem] at hW
      refine le_bot_iff.1 fun y hy => ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      have : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact (hW hy).elim
    subst hb
    exact Subsingleton.elim _ _

def constFnHom {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : ℂ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom

theorem top_le_preimage_wchart_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : Fin 1 → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j) : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j 0) :=
  (top_le_preimage_comp x φ _).2 (top_le_preimage_mono x (LB.wchart_le L (fun _ : Fin 1 => φ) j 0) h)

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : u.ex 0 = 1 :=
  (u.ker 0).2 u.Λ.zero_mem


open Classical in
def unitOrOne (c : ℂ) : ℂˣ := if h : c ≠ 0 then Units.mk0 c h else 1

theorem unitOrOne_val {c : ℂ} (h : c ≠ 0) : (unitOrOne c : ℂ) = c := by
  rw [unitOrOne, dite_eq_left h]; rfl

theorem exists_gen_isValueAt_origin : ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a : ℤ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)), τ.IsGen ∧ ∀ (s : LB.Sec (Out.LPow P.A P.L a T)) (f : (Fin P.g → ℂ) → ℂ), (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L a T).U j) (s.f j) = f z * u.fr (j 0) z ^ (a : ℤ)) → Out.IsValueAt P.A P.L a s 1 τ (constFn T.hom ⊤ (f 0)) := by
  intro P u a T _ p
  let x : Sp ℂ ⟶ T.left := p.left
  have hx : x ≫ T.hom = 𝟙 _ := Over.w p
  have : IsIso x := by
    have : x = inv T.hom := IsIso.eq_inv_of_inv_hom_id hx
    rw [this]; infer_instance
  have h1 : p ≫ (1 : T ⟶ P.A) = u.ex 0 := by
    rw [ex_zero, MonObj.comp_one]
  have h1' : x ≫ (1 : T ⟶ P.A).left = (u.ex 0).left := congrArg CommaMorphism.left h1
  have hch : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U (j 0) := fun j h => by
    have := top_le_preimage_wchart_one P.L _ x j h
    rwa [h1'] at this
  let τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)) :=
    ⟨fun j => Units.map (constFnHom T.hom _).toMonoidHom (unitOrOne (u.fr (j 0) 0) ^ a)⟩
  have hτ : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      valAt' x (LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j) (τ.s j).val = u.fr (j 0) 0 ^ a := fun j h => by
    refine (valAt'_constFn x T.hom hx _ _ h).trans ?_
    rw [Units.val_zpow_eq_zpow_val, unitOrOne_val (u.fr_ne _ _ (hch j h))]
  refine ⟨τ, fun i j => ?_, fun s f hs j => ?_⟩
  · apply Units.ext
    refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x _ _).1 h
    rw [Units.val_mul, valAt'_mul]
    refine ((valAt'_res x inf_le_left _ h).trans (hτ i hi)).trans ?_
    have e2 := (valAt'_res x inf_le_right _ h).trans (hτ j hj)
    refine Eq.trans ?_ (congrArg _ e2.symm)
    have hij : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.U (i 0) ⊓ P.L.U (j 0)) :=
      (top_le_preimage_inf (u.ex 0).left _ _).2 ⟨hch i hi, hch j hj⟩
    rw [u.fr_compat _ _ _ hij, mul_zpow]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one]
    refine Eq.trans ?_ (valAt'_zpow x h _ a).symm
    congr 1
    refine Eq.trans ?_ (valAt'_res x _ _ h).symm
    refine Eq.trans ?_ (valAt'_comp x (1 : T ⟶ P.A).left (P.L.U (i 0) ⊓ P.L.U (j 0)) (P.L.g (i 0) (j 0)).val).symm
    rw [h1']
  · refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    rw [valAt'_mul, hτ j h, valAt'_map x _ _ h, valAt'_map x _ _ h, valAt'_constFn x T.hom hx _ _ le_top]
    refine (valAt'_comp x _ _ _).trans ?_
    have h2 : p ≫ Out.ptSecT P.A (1 : T ⟶ P.A) = lift p (u.ex 0) := by
      rw [Out.ptSecT, comp_lift, Category.comp_id, h1]
    have h2' : x ≫ (Out.ptSecT P.A (1 : T ⟶ P.A)).left = (lift p (u.ex 0)).left := congrArg CommaMorphism.left h2
    rw [h2']
    exact hs j 0 (hch j h)

end GlobalTheory.OriginValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTypeFnOfRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_isTypeFn_of_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ), Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) → ∃ ty : Fin g → (E →+* ℂ), IsTypeFn H D.p D.q ty := by
  intro E _ _ _ H D g ⟨e⟩
  obtain ⟨g', ty, h, -, P, -, hinj, hdisc, hspan, -⟩ := GlobalTheory.PeriodExists.exists_typeFn_period H D
  let L : Submodule ℤ (Fin g' → ℂ) := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology L := hdisc
  have : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g' → ℂ)) = Set.range P := by ext; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have h2 : Module.finrank ℤ L = 2 * g := by
    rw [← (e.trans (LinearEquiv.ofInjective P.toIntLinearMap hinj)).finrank_eq]
    simp
  have h3 : Module.finrank ℝ (Fin g' → ℂ) = 2 * g' := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  obtain rfl : g' = g := by omega
  exact ⟨ty, h⟩

end GlobalTheory
end

