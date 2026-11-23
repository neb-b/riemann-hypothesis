module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PowSec

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

theorem appLE_bijective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Bijective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (ρ.app U)

theorem down_surjective [IsIso ρ] : Function.Surjective (down L σ ρ e n) := by
  intro t
  choose u hu using fun k : L.ι =>
    (appLE_bijective ρ _ _ (chart_eq L σ ρ e (fun _ => k))).2 (t.f (fun _ => k))
  let F : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => σ) j) := fun j =>
    (Y.presheaf.map (eqToHom (congrArg (LB.wchart L (fun _ : Fin 1 => σ))
      (funext fun q => congrArg j (Subsingleton.elim q 0) : j = fun _ => j 0))).op).hom (u (j 0))
  have hF : ∀ k, F (fun _ => k) = u k := fun k => by
    show (Y.presheaf.map (𝟙 _)).hom (u k) = u k
    rw [Y.presheaf.map_id]; rfl
  have hF' : ∀ j : PUnit → L.ι,
      (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit)) = t.f j := fun j => by
    rw [hF]; exact hu (j PUnit.unit)
  refine ⟨⟨F, fun i' j' => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i : PUnit → L.ι, i' = fun _ => i PUnit.unit :=
      ⟨fun _ => i' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    obtain ⟨j, rfl⟩ : ∃ j : PUnit → L.ι, j' = fun _ => j PUnit.unit :=
      ⟨fun _ => j' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have heq : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j =
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      congrArg₂ (· ⊓ ·) (chart_eq L σ ρ e i) (chart_eq L σ ρ e j)
    have hle := heq.le
    refine (appLE_bijective ρ _ _ heq).1 ?_
    refine Eq.trans ?_ (map_mul (ρ.appLE _ _ hle).hom _ _).symm
    have := t.compat i j
    rw [← hF' i, ← hF' j] at this
    refine Eq.trans (Eq.symm ?_) (this.trans (Eq.symm (congrArg₂ (· * ·) ?_ ?_)))
    · exact (congrArg (fun φ => φ.hom (F fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (F fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)
  · obtain ⟨tf, tc⟩ := t
    have : (fun j : PUnit → L.ι => (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit))) = tf :=
      funext hF'
    subst this
    rfl

end Transport

theorem exists_basis_of_isField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (hR : IsField R)
    {m : ℕ} (hm : 0 < m) (h : Module.finrank R M = m) : Nonempty (Module.Basis (Fin m) R M) := by
  letI := hR.toField
  haveI : Module.Finite R M := Module.finite_of_finrank_pos (h ▸ hm)
  exact ⟨Module.finBasisOfFinrankEq R M h⟩

attribute [local instance] Over.cartesianMonoidalCategory


open Out in
theorem exists_basis_sections (H : Out.GlobalSectionsRankAlgClosed) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ t : (lbPow P.L n).Sec,
      ∃! a : Fin (n ^ P.g) → K, ∀ j, t.f j = ∑ i, constFn P.A.hom _ (a i) * (s i).f j := by
  have hr := H K P n hn
  let T : Over (Sp K) := ReciprocityTheory.ChartRestriction.G.Out.baseOver (Sp K)
  let c : Γ(T.left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hfield : IsField Γ(T.left, ⊤) := c.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨b⟩ := exists_basis_of_isField (R := Γ(T.left, ⊤))
    (M := ReciprocityTheory.ChartRestriction.G.Out.SecM P.A P.L n T) hfield (pow_pos hn _) hr
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  let D : ReciprocityTheory.ChartRestriction.G.Out.SecM P.A P.L n T → (lbPow P.L n).Sec := fun v =>
    down P.L (snd T P.A).left ρ.left ρ₂ n (ReciprocityTheory.ChartRestriction.G.Out.SecM.toSec P.A v)
  have hlin : ∀ (a : Fin (n ^ P.g) → K) j,
      (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j := by
    intro a j
    show (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom
      ((∑ i, c.symm (a i) • b i : ReciprocityTheory.ChartRestriction.G.Out.SecM P.A P.L n T).1
        (fun _ => j PUnit.unit)) = _
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (ReciprocityTheory.ChartRestriction.G.Out.liftHom P.A _ (c.symm (a i)))
      ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  have hinj : ∀ v w, (∀ j, (D v).f j = (D w).f j) → v = w := by
    intro v w h
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    exact appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) (h fun _ => k)
  refine ⟨fun i => D (b i), fun t => ?_⟩
  obtain ⟨w, hw⟩ := down_surjective P.L (snd T P.A).left ρ.left ρ₂ n t
  have hw' : D (ReciprocityTheory.ChartRestriction.G.Out.SecM.ofSec P.A w) = t := hw
  refine ⟨fun i => c (b.repr (ReciprocityTheory.ChartRestriction.G.Out.SecM.ofSec P.A w) i),
    fun j => ?_, fun a ha => ?_⟩
  · rw [← hlin]
    simp only [RingEquiv.symm_apply_apply]
    rw [b.sum_repr, hw']
  · have h0 : ReciprocityTheory.ChartRestriction.G.Out.SecM.ofSec P.A w = ∑ i, c.symm (a i) • b i :=
      hinj _ _ fun j => by rw [hw', hlin]; exact ha j
    funext i
    rw [h0, b.repr_sum_self]
    exact (c.apply_symm_apply _).symm

end GlobalTheory.PowSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isIntegral_of_isAbelianScheme_field (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) : IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem polAV_isIntegral_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), IsIntegral P.A.left :=
  fun K _ _ P => isIntegral_of_isAbelianScheme_field K P.A P.isAb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDim

theorem isMaximal_under_of_finiteType (K R B : Type*) [Field K] [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] [Algebra R B] [IsScalarTower K R B] [Algebra.FiniteType K B]
    (m : Ideal B) [m.IsMaximal] : (m.under R).IsMaximal := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  haveI : Algebra.IsIntegral R (B ⧸ m) := Algebra.IsIntegral.tower_top K
  have h := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (⊥ : Ideal (B ⧸ m))
  change (Ideal.comap (algebraMap R (B ⧸ m)) ⊥).IsMaximal at h
  rwa [IsScalarTower.algebraMap_eq R B (B ⧸ m), ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h

theorem ringKrullDim_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] [Nontrivial B]
    (g : ℕ) [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] :
    ringKrullDim B = g := by
  have hR : ringKrullDim (MvPolynomial (Fin g) K) = g := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  apply le_antisymm
  · rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin g) K) B)) fun P Q hPQ => ?_
    refine lt_of_le_of_ne (Ideal.comap_mono hPQ.le) fun h => hPQ.ne ?_
    exact PrimeSpectrum.ext (Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := MvPolynomial (Fin g) K) _ _ hPQ.le (congrArg PrimeSpectrum.asIdeal h))
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
      (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
    haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
      (S := MvPolynomial (Fin g) K) inferInstance inferInstance
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
    haveI hp := isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
    have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
      (m.under (MvPolynomial (Fin g) K))
    letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
    rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
    have h2 : (m.under (MvPolynomial (Fin g) K)).height ≤ m.height := by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
        (m.under (MvPolynomial (Fin g) K)) m]
      exact le_self_add
    rw [← h1]
    exact (WithBot.coe_le_coe.mpr h2).trans Ideal.height_le_ringKrullDim_of_isPrime

theorem ringKrullDim_of_isStandardSmooth {K B : Type*} [CommRing K] (hK : IsField K) [CommRing B]
    [Nontrivial B] {g : ℕ} {f : K →+* B} (hf : f.IsStandardSmoothOfRelativeDimension g) :
    ringKrullDim B = g := by
  letI := hK.toField
  obtain ⟨φ, -, hφ⟩ := hf.exists_etale_mvPolynomial
  algebraize [φ]
  exact ringKrullDim_of_etale_mvPolynomial K B g

theorem ringKrullDim_eq_of_span_eq_top {A : Type*} [CommRing A] [Nontrivial A] (s : Set A)
    (hs : Ideal.span s = ⊤) (d : WithBot ℕ∞)
    (h : ∀ t ∈ s, Nontrivial (Localization.Away t) → ringKrullDim (Localization.Away t) = d) :
    ringKrullDim A = d := by
  have key : ∀ q : Ideal A, q.IsPrime → ∃ t : A, Disjoint (Submonoid.powers t : Set A) q ∧
      ringKrullDim (Localization.Away t) = d := by
    intro q hq
    obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q := by
      by_contra hc
      push Not at hc
      exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
    have disj : Disjoint (Submonoid.powers t : Set A) (q : Set A) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr htq
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq
      disj
    refine ⟨t, disj, h t hts ?_⟩
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hP.ne_top (Subsingleton.elim _ _)
  apply le_antisymm
  · refine (ringKrullDim_le_iff_height_le d).mpr fun q hq => ?_
    obtain ⟨t, disj, ht⟩ := key q hq
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq
      disj
    rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away t) _ q disj, ← ht]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨t, -, ht⟩ := key m hm.isPrime
    rw [← ht]
    refine (ringKrullDim_le_iff_height_le _).mpr fun q hq => ?_
    rw [← IsLocalization.height_under (R := A) (.powers t) q]
    exact Ideal.height_le_ringKrullDim_of_isPrime

theorem ringKrullDim_affineOpen :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (g : ℕ),
      SmoothOfRelativeDimension g p → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
        ringKrullDim Γ(X, U) = g := by
  intro K _ X p g hp U hU hne
  haveI : Nonempty U := hne.to_subtype
  have hK : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨s, hs, h⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  exact ringKrullDim_eq_of_span_eq_top s hs _ fun t ht _ =>
    ringKrullDim_of_isStandardSmooth hK (h t ht)

end GlobalTheory.SmoothDim
end

