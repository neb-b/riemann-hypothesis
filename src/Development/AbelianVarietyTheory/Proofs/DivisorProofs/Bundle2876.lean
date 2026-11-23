module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectExtensionAbelianLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBound
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.FDimField

theorem cechLB_triv_finite_finrank_one_le : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Module.Finite K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ∧ Module.finrank K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ≤ g := by
  intro K _ A _ g hA hsm κ _ _ D hD hcov
  let L := AlgebraicClosure K
  let f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  let A' : Over (Sp L) := (Over.pullback f).obj A
  let π : A'.left ⟶ A.left := pullback.fst A.hom f
  have hGP : IsGrpPullback A' A (spMap (algebraMap K L)) π := isGrpPullback_pullback A f
  have H : IsPullback π A'.hom A.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) := hGP.1
  obtain ⟨hA', hg'⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback (algebraMap K L) A A' π g hGP hA hsm
  haveI := hA.proper
  haveI := GlobalTheory.isAffineHom_diagonal_of_isSeparated A.hom
  have hDs := GlobalTheory.isAffineOpen_finset_biInf hD
  let D' : κ → A'.left.Opens := fun i => π ⁻¹ᵁ D i
  have hD' : ∀ i, IsAffineOpen (D' i) := fun i => GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H (hD i)
  have hcov' : ⨆ i, D' i = ⊤ := by
    show ⨆ i, π ⁻¹ᵁ D i = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  obtain ⟨hfin', hrank', -⟩ :=
    GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two L A' g hA' hg' κ D' hD' hcov'

  obtain ⟨c, hc⟩ := (GlobalTheory.CechPic.iso_triv_iff (LB.triv A.left)).1 ((GlobalTheory.CechPic.setoid A.left).iseqv.refl ⟨LB.triv A.left, LB.isLB_triv A.left⟩)
  obtain ⟨w, hw⟩ := (GlobalTheory.CechPic.iso_triv_iff ((LB.triv A.left).pull π)).2
    ⟨LB.genPull (LB.triv A.left) c π, LB.isGen_genPull (LB.triv A.left) c hc π⟩
  let C := GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D
  obtain ⟨e₃⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv L C 1
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ 1).mapIso
    (GlobalTheory.AbLaw.cechLBBaseChangeIso (LB.isLB_triv A.left) H (fun s hs => hDs s hs))).toLinearEquiv
  have e₅ := (HomologicalComplex.homologyMapIso
    (GlobalTheory.AbLaw.cechLBCongr A'.hom D' (LB.isLB_triv A'.left) (LB.isLB_pull (LB.isLB_triv A.left) π) w hw) 1).toLinearEquiv
  let E : (L ⊗[K] C.homology 1) ≃ₗ[L] (GlobalTheory.AbLaw.cechLB A'.hom (LB.triv A'.left) D').homology 1 :=
    e₃.symm ≪≫ₗ e₄ ≪≫ₗ e₅.symm
  haveI := hfin' 1
  haveI : Module.Finite L (L ⊗[K] C.homology 1) := Module.Finite.equiv E.symm
  have hfinK : Module.Finite K (C.homology 1) := by
    have h1 : Module.rank L (L ⊗[K] C.homology 1) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [Module.rank_baseChange, Cardinal.lift_id] at h1
    exact Module.rank_lt_aleph0_iff.1 h1
  refine ⟨hfinK, le_of_eq ?_⟩
  rw [← Module.finrank_baseChange (R := L), E.finrank_eq]
  exact hrank'

end GlobalTheory.AbCoh.FDimField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbChart

theorem exists_siegPre_localization : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := fun g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ p _ hp κ s' hκ hs =>
  _root_.GlobalTheory.SiegExtend.exists_principal_extension g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p (_root_.GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization R G₁ hG p hp) κ s' hκ hs

theorem exists_spMap_ext : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (b : cycAway n →+* R) (x : Sp (FractionRing R) ⟶ Sp (cycAway n)), ∃ s : Sp R ⟶ Sp (cycAway n), jK R ≫ s = x := by
  intro n R _ _ _ b x
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* FractionRing R, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  let A := algebraMap R (FractionRing R)
  have hAi : Function.Injective A := IsFractionRing.injective R (FractionRing R)
  have hgen : ∀ (w : ℂ) (hw : w ∈ cycAway n), φ ⟨w, hw⟩ ∈ A.range := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨zeta 0, Subring.subset_closure (Or.inl rfl)⟩ : cycAway 0) = 1 := Subtype.ext (by simp [zeta])
          rw [this, map_one]; exact A.range.one_mem
        · have hpow : (⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩ : cycAway n) ^ n = 1 :=
            Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one)
          have hI : IsIntegral R (φ ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩) := by
            refine IsIntegral.of_pow hn ?_
            rw [← map_pow, hpow, map_one]; exact isIntegral_one
          obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
          exact ⟨r, hr⟩
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway 0) = 0 := Subtype.ext (by simp)
          rw [this, map_zero]; exact A.range.zero_mem
        · set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
          have hu : u * (n : cycAway n) = 1 := Subtype.ext (by simp [u, hn.ne'])
          have e1 : φ u * (n : FractionRing R) = 1 := by rw [← map_natCast φ, ← map_mul, hu, map_one]
          have e2 : A (b u) * (n : FractionRing R) = 1 := by rw [← map_natCast A, ← map_mul, ← map_natCast b, ← map_mul, hu, map_one, map_one]
          have hn0 : (n : FractionRing R) ≠ 0 := right_ne_zero_of_mul_eq_one e1
          exact ⟨b u, mul_right_cancel₀ hn0 (e2.trans e1.symm)⟩
    | zero => exact ⟨0, by rw [map_zero]; exact (map_zero φ).symm⟩
    | one => exact ⟨1, by rw [map_one]; exact (map_one φ).symm⟩
    | add w v hw hv ihw ihv =>
      have : (⟨w + v, add_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ + ⟨v, hv⟩ := rfl
      rw [this, map_add (f := _)]; exact A.range.add_mem ihw ihv
    | neg w hw ih =>
      have : (⟨-w, neg_mem hw⟩ : cycAway n) = -⟨w, hw⟩ := rfl
      rw [this, map_neg]; exact A.range.neg_mem ih
    | mul w v hw hv ihw ihv =>
      have : (⟨w * v, mul_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ * ⟨v, hv⟩ := rfl
      rw [this, map_mul]; exact A.range.mul_mem ihw ihv
  let e : R ≃+* A.range := RingEquiv.ofBijective A.rangeRestrict ⟨fun a a' h => hAi (congrArg Subtype.val h), A.rangeRestrict_surjective⟩
  let ψ : cycAway n →+* R := (e.symm : A.range →+* R).comp (φ.codRestrict A.range fun z => hgen z.1 z.2)
  have hψ : A.comp ψ = φ := by
    ext z
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hgen z.1 z.2⟩)
    exact h
  refine ⟨spMap ψ, ?_⟩
  exact (spMap_comp ψ A).symm.trans (congrArg spMap hψ)

theorem asIdeal_eq_bot_of_charZero : ∀ (n : ℕ) (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ Sp (cycAway n)) (q : Sp K), (x q).asIdeal = ⊥ := by
  intro n K _ _ x q
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* K, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  change Ideal.comap φ q.asIdeal = ⊥
  rw [hq, ← RingHom.ker_eq_comap_bot]
  by_contra hne
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have halg : IsAlgebraic ℤ a := by
    have hC : ∀ z ∈ cycAway n, IsIntegral ℚ z := by
      intro z hz
      refine Subring.closure_le (t := (integralClosure ℚ ℂ).toSubring) |>.2 ?_ hz
      rintro w (rfl | rfl)
      · show IsIntegral ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n))
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using (isIntegral_one : IsIntegral ℚ (1 : ℂ))
        · exact ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top
      · show IsIntegral ℚ ((n : ℂ)⁻¹)
        simpa using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := ((n : ℚ)⁻¹)))
    have h1 : IsAlgebraic ℚ (a : ℂ) := (hC a a.2).isAlgebraic
    have h2 : IsAlgebraic ℤ (a : ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 h1
    exact (isAlgebraic_algHom_iff ((cycAway n).subtype.toIntAlgHom) Subtype.val_injective).1 h2
  have := Ideal.comap_ne_bot_of_algebraic_mem ha0 ha halg
  apply this
  rw [eq_bot_iff]
  intro m hm
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hm
  exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 hm)

theorem mem_range_of_mem_abLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy p hp
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  have hu : ∀ x : p.asIdeal.primeCompl, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R)
      (⟨x.1, mem_nonZeroDivisors_of_ne_zero (fun h => x.2 (h ▸ p.asIdeal.zero_mem))⟩ : nonZeroDivisors R)
  let lf : Localization.AtPrime p.asIdeal →+* FractionRing R := IsLocalization.lift hu
  let ιp := spMap (algebraMap R (Localization.AtPrime p.asIdeal))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal) := spMap lf
  have hκ : κ ≫ ιp = jK R := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hnorm := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨s, hs⟩ := exists_spMap_ext n R b (y ≫ F.s)
  have hs' : κ ≫ ιp ≫ s = y ≫ F.s := by rw [← Category.assoc, hκ, hs]
  obtain ⟨c, c', hc, m₁, m₂⟩ := exists_siegPre_localization g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p hp κ (ιp ≫ s) hκ hs'
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.AtPrime p.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors p.asIdeal)).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hdense : Dense {x : Sp (Localization.AtPrime p.asIdeal) | ((ιp ≫ s) x).asIdeal = ⊥} := by
    refine Dense.mono ?_ hdom.denseRange
    rintro _ ⟨q, rfl⟩
    show ((ιp ≫ s) (κ q)).asIdeal = ⊥
    rw [← Scheme.Hom.comp_apply, hs']
    exact asIdeal_eq_bot_of_charZero n (FractionRing R) (y ≫ F.s) q
  obtain ⟨f, hfs, hf⟩ := F.rep _ (ιp ≫ s) c inferInstance hdense hc
  have hfy : κ ≫ f = y := F.inj (FractionRing R) (κ ≫ f) y (y ≫ F.s) c'
    (by rw [Category.assoc, hfs, hs']) (GlobalTheory.SiegelPullComp.pb_comp hf m₁) m₂
  have hξ : ιp ≫ ξ = f ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hfy]
  refine ⟨f (closedPoint (Localization.AtPrime p.asIdeal)), ?_⟩
  change (f ≫ j) (closedPoint _) = ξ p
  rw [← hξ]
  change ξ (ιp (closedPoint _)) = ξ p
  congr 1
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.AbChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.KilledInverse

open GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart GlobalTheory.AV.AbVar.InvDegInverse

variable {k : Type} [Field k]

theorem exists_kerPow_finrank_ne_zero {A B : AbVar k} (f : A ⟶ B) (e : ℕ) (he : IsUnit (e : k)) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f e H i ∧ ((Module.finrank k H : ℕ) : k) ≠ 0 := by
  have he0 : (e : k) ≠ 0 := he.ne_zero
  have hepos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; exact he0 Nat.cast_zero)

  have key : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ e ∧ ∀ n : ℕ, ¬ p ∣ n → (n : k) ≠ 0 := by
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp0
    · refine ⟨ringChar k, hp, fun h => he0 ((ringChar.spec k e).2 h), fun n hn h0 => hn ((ringChar.spec k n).1 h0)⟩
    · obtain ⟨p, hpe, hp⟩ := Nat.exists_infinite_primes (e + 1)
      refine ⟨p, hp, fun h => ?_, fun n hn h0 => ?_⟩
      · have := Nat.le_of_dvd hepos h
        omega
      · have h1 := (ringChar.spec k n).1 h0
        rw [hp0, zero_dvd_iff] at h1
        exact hn (h1 ▸ dvd_zero p)
  obtain ⟨p, hp, hpe, hpk⟩ := key
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, _, _, i, hi, hH⟩ := exists_kerPow_not_dvd p k A B f e hepos hpe
  exact ⟨H, inferInstance, inferInstance, i, hi, hpk _ hH⟩

theorem finite_ker_of_kerPow {A B : AbVar k} (f : A ⟶ B) (e : ℕ) {H : Type} [CommRing H] [Algebra k H]
    {i : ptOver k H ⟶ A.X} (hi : KerPow f e H i) (hH : Module.finrank k H ≠ 0)
    (hkill : ∀ (T : Over (Sp k)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ e = 1) : Finite (ptMap f).ker := by
  haveI : Module.Finite k H := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hH)
  have hx : ∀ x : (ptMap f).ker, x.1 ≫ f.hom = 1 := fun x => MonoidHom.mem_ker.mp x.2
  let φ : (ptMap f).ker → (H →ₐ[k] AlgebraicClosure k) := fun x =>
    (hi.2 (AlgebraicClosure k) x.1 (hx x) (hkill _ x.1 (hx x))).exists.choose
  have hφ : ∀ x, spMap (φ x).toRingHom ≫ i.left = x.1.left := fun x =>
    (hi.2 (AlgebraicClosure k) x.1 (hx x) (hkill _ x.1 (hx x))).exists.choose_spec
  refine Finite.of_injective φ fun x y hxy => ?_
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← hφ x, ← hφ y, hxy]

theorem exists_comp_eq_nsmul (A B : AbVar k) (f : A ⟶ B) (hdim : A.dim = B.dim) (e : ℕ) (he : IsUnit (e : k))
    (hkill : ∀ (T : Over (Sp k)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ e = 1) :
    ∃ m : B ⟶ A, f ≫ m = e • 𝟙 A := by
  obtain ⟨H, _, _, i, hi, hH⟩ := exists_kerPow_finrank_ne_zero f e he
  have hH0 : Module.finrank k H ≠ 0 := fun h0 => hH (by rw [h0, Nat.cast_zero])
  have hfin : IsFinite f.hom.left :=
    (isFinite_iff_finite_ker k A B f).2 (finite_ker_of_kerPow f e hi hH0 hkill)
  have hf : IsIsogeny f := ⟨hfin, surjective_of_isFinite_of_dim_eq k A B f hdim hfin⟩
  have hd : ((deg f : ℕ) : k) ≠ 0 := by
    obtain ⟨H0, _, _, i0, hi0, h0⟩ := exists_kerPow_zero_finrank_eq_deg k A B f hf
    rw [← h0, finrank_eq_of_kerPow hi0 hi (fun R _ _ x hx => ⟨fun _ => hkill _ x hx, fun _ => pow_zero x⟩)]
    exact hH
  haveI hGfin := finite_invKer f hf
  obtain ⟨C, q, hq, hdq, hker, huniv⟩ := GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup k A (invKer f) hGfin (card_invKer_ne_zero f hf)
    (galPts_mem_invKer f)
  obtain ⟨h, hqh⟩ := huniv B f (fun x hx => hx.1)
  have hdimAC := (GlobalTheory.AV.AbVar.isogeny_flat_finrank k A C q hq).1
  have hdimAB := (GlobalTheory.AV.AbVar.isogeny_flat_finrank k A B f hf).1
  have hcomp := GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp k A C B q h hdimAC (hdimAC.symm.trans hdimAB)
  rw [hqh] at hcomp
  have hdeg : deg f = deg q * deg h := hcomp.2
  have hv : ∀ l : ℕ, l.Prime → (l : k) ≠ 0 → padicValNat l (deg f) = padicValNat l (deg q) := by
    intro l hl hlK
    haveI := Fact.mk hl
    have e1 := GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree k l hlK A B f hf
    have e2 := GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree k l hlK A C q hq
    have hset : Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} =
        Nat.card {x : A.Pt // x ≫ q.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨h1, n, hn⟩
        refine ⟨?_, n, hn⟩
        have hm : x ∈ invKer f := ⟨h1, l ^ n, by push_cast; exact pow_ne_zero _ hlK, hn⟩
        rw [← hker] at hm
        exact hm
      · rintro ⟨h1, n, hn⟩
        refine ⟨?_, n, hn⟩
        rw [← hqh, comp_hom, ← Category.assoc, h1]
        exact (ptMap h).map_one
    rw [e1, e2] at hset
    exact Nat.pow_right_injective hl.two_le hset
  have hd0 : deg f ≠ 0 := by
    intro h0; apply hd; rw [h0]; simp
  have hq0 : deg q ≠ 0 := by
    intro h0; apply hd0; rw [hdeg, h0, zero_mul]
  have hh0 : deg h ≠ 0 := by
    intro h0; apply hd0; rw [hdeg, h0, mul_zero]
  have hh1 : deg h = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro l hl hdvd
    by_cases hlK : (l : k) = 0
    · apply hd
      obtain ⟨c, hc⟩ : l ∣ deg f := hdeg ▸ dvd_mul_of_dvd_right hdvd _
      rw [hc]; push_cast; rw [hlK, zero_mul]
    · haveI := Fact.mk hl
      have e' := hv l hl hlK
      rw [hdeg, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hq0 hh0] at e'
      have h1 := one_le_padicValNat_of_dvd hh0 hdvd
      rw [← Nat.padicValNat_def] at h1
      omega
  have hiso : IsIso h := (GlobalTheory.AV.AbVar.isIso_iff_deg_eq_one k C B h).2 hh1
  obtain ⟨r, hr⟩ := huniv A (e • 𝟙 A) (fun x hx => by
    change x ≫ (e • 𝟙 A).hom = 1
    rw [nsmul_hom, id_hom, GlobalTheory.AV.DegSep.comp_pow_id]
    exact hkill _ x hx.1)
  refine ⟨inv h ≫ r, ?_⟩
  rw [← hqh, Category.assoc, IsIso.hom_inv_id_assoc, hr]

end GlobalTheory.AV.AbVar.KilledInverse

namespace GlobalTheory.AV

theorem exists_comp_eq_pow_of_ker_killed : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (l : A ⟶ B), IsMonHom l → ∀ e : ℕ, IsUnit (e : k) → (∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → x ^ e = 1) → ∃ m : B ⟶ A, IsMonHom m ∧ l ≫ m = 𝟙 A ^ e := by
  intro k _ A B _ _ _ _ g hA hB sA sB l hl e he hkill
  let A' : AbVar k := { X := A, ab := hA, dim := g, smooth := sA }
  let B' : AbVar k := { X := B, ab := hB, dim := g, smooth := sB }
  obtain ⟨m, hm⟩ := AbVar.KilledInverse.exists_comp_eq_nsmul A' B' (AbVar.Hom.mk (A := A') (B := B') l) rfl e he
    (fun T x hx => hkill T x hx)
  refine ⟨m.hom, inferInstance, ?_⟩
  have h2 := congrArg AbVar.Hom.hom hm
  rw [AbVar.comp_hom, AbVar.mk_hom, AbVar.nsmul_hom, AbVar.id_hom] at h2
  exact h2

end GlobalTheory.AV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatements
section
theorem GlobalTheory.SqLift.abelianLifting_of_known_theorems :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a b c d e =>
    GlobalTheory.SqLift.abelianLifting_of_schemeLifts (_root_.GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare a b c d) (_root_.GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham a) e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoinStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_locally_constant_geomPoint : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 → ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left), IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  first | (exact @GlobalTheory.TorsLocConst.locally_const_torsion) | (exact GlobalTheory.TorsLocConst.locally_const_torsion) | (intros; apply GlobalTheory.TorsLocConst.locally_const_torsion  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleAbelianSchemeOfRelDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBasisDim


open ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem basis_tanM_of_dim {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (d : ℕ) (hG : SmoothOfRelativeDimension d G.hom) :
    Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  have hS := isGrpPullback_pullback G (𝟙 (Sp R))
  have hsm : SmoothOfRelativeDimension d ((Over.pullback (𝟙 (Sp R))).obj G).hom := by
    show SmoothOfRelativeDimension d (pullback.snd _ _)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm
  let b : Fin d → TanM (𝟙 (Sp R)) G := fun i =>
    mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))
  have hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin d → R, m = ∑ i, a i • b i := fun m => by
    obtain ⟨w', hw'⟩ := push_surj hS (tv m)
    have htan : IsTangent w' := (isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)
    have key : ∀ a : Fin d → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i := by
      intro a
      rw [isLieComb_iff hS, hw']
      constructor
      · intro h
        apply tanM_ext
        rw [h, GlobalTheory.RayBasis.tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
      · intro h
        rw [h, GlobalTheory.RayBasis.tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
    obtain ⟨C, hC, hCu⟩ := hv.2 w' htan
    exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩
  refine ⟨Module.Basis.mk (v := b) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i
  · intro m _
    obtain ⟨a, ha, -⟩ := hb m
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem basis_tanM_abelian : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (d : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension d G.hom → Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  intro R _ _ _ G _ _ d _ hG
  exact basis_tanM_of_dim G d hG

end GlobalTheory.TanBasisDim
end
end

