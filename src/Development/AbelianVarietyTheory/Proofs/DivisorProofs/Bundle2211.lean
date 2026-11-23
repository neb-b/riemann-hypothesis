module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ClosureFromSpecMemCompsH
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequencePrimeDivisors
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.RegParPrime

open ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

theorem exists_mul_eq_of_mem_span {A : Type} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (R : Type) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p] {b x : A}
    (h : algebraMap A R x ∈ Ideal.span {algebraMap A R b}) : ∃ t ∉ p, ∃ s, t * x = s * b := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl (S := R) r
  refine ⟨t, t.2, s, ?_⟩
  apply IsLocalization.injective R (M := p.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors p)
  rw [map_mul, map_mul, ← hr, ← mul_assoc, IsLocalization.mk'_spec']

theorem exists_primeDivisors_of_regularParams : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (c : ℕ) (a : Fin c → Γ(Y, U)), IsRegularLocalRing (Y.presheaf.stalk y) → FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U y hy (a i)) → ∃ (w : Fin c → Y) (u : Fin c → Y.functionFieldˣ), Function.Injective w ∧ ∀ j, (u j : Y.functionField) = fnOf U (gen_mem hy) (a j) ∧ w j ⤳ y ∧ Order.coheight (w j) = 1 ∧ w j ∉ Y.basicOpen (a j) ∧ Scheme.ord (u j : Y.functionField) (w j) = 1 ∧ ∀ v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → v ∈ Y.basicOpen (a j) := by
  intro Y _ _ y U hy c a hreg hrsp
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  have hVU' : V ≤ U := hVU
  let b : Fin c → Γ(Y, V) := fun i => resG Y hVU' (a i)
  have hgerm : ∀ i, Y.presheaf.germ V y hyV (b i) = Y.presheaf.germ U y hy (a i) := fun i =>
    Y.presheaf.germ_res_apply (homOfLE hVU') y hyV (a i)
  have hrsp' : FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ V y hyV (b i)) := by
    simpa only [hgerm] using hrsp
  haveI := hreg
  obtain ⟨q, hq⟩ := exists_parPrimes hV hyV b hrsp'
  have hprime : ∀ i, Prime (Y.presheaf.germ V y hyV (b i)) :=
    prime_of_regular_params _ hrsp'.1 hrsp'.2
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hb0 : ∀ i, b i ≠ 0 := fun i h => (hprime i).ne_zero (by rw [h, map_zero])
  have hfn : ∀ i, fnOf U (gen_mem hy) (a i) = fnOf V (gen_mem hyV) (b i) := fun i =>
    (fnOf_resG hVU' (gen_mem hyV) (a i)).symm
  have ha0 : ∀ i, fnOf U (gen_mem hy) (a i) ≠ 0 := fun i h =>
    hb0 i (fnOf_injective V (gen_mem hyV) (by rw [← hfn, h, map_zero]))
  have hbas : ∀ i, Y.basicOpen (b i) ≤ Y.basicOpen (a i) := fun i => by
    have := Scheme.basicOpen_res Y (a i) (homOfLE hVU').op
    intro z hz
    have hz' : z ∈ V ⊓ Y.basicOpen (a i) := by rw [← this]; exact hz
    exact hz'.2

  have hq1 : ∀ j, (q j).asIdeal.height = 1 := by
    intro j
    have hmin : (q j).asIdeal ∈ (Ideal.span {b j}).minimalPrimes := by
      refine ⟨⟨(q j).2, (Ideal.span_singleton_le_iff_mem _).2 (hq.2.1 j)⟩, ?_⟩
      rintro Q ⟨hQp, hQb⟩ hQle
      exact (hq.2.2.1 j ⟨Q, hQp⟩ (le_trans (show (⟨Q, hQp⟩ : PrimeSpectrum Γ(Y, V)) ≤ q j from hQle)
        (hq.1 j))).mp (hQb (Ideal.mem_span_singleton_self _))
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin) ?_
    refine ENat.one_le_iff_ne_zero.2 fun h0 => hb0 j ?_
    have hmin0 := Ideal.height_eq_zero_iff.1 h0
    have hbot : (q j).asIdeal ≤ ⊥ := hmin0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    exact hbot (hq.2.1 j)
  let w : Fin c → Y := fun j => hV.fromSpec (q j)
  have hwV : ∀ j, w j ∈ V := fun j => fromSpec_mem hV (q j)
  have hpw : ∀ j, hV.primeIdealOf ⟨w j, hwV j⟩ = q j := fun j => pOf_fromSpec hV (q j)
  have hcoh : ∀ j, Order.coheight (w j) = 1 := by
    intro j
    letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI := hV.isLocalization_stalk ⟨w j, hwV j⟩
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨w j, hwV j⟩).asIdeal
      (Y.presheaf.stalk (w j))
    rw [ringKrullDim_stalk_eq_coheight, hpw, hq1] at this
    exact_mod_cast this
  refine ⟨w, fun j => Units.mk0 _ (ha0 j), ?_, fun j => ?_⟩
  · intro i j h
    have key : ∀ {z z' : Y} (hz : z ∈ V) (hz' : z' ∈ V), z = z' →
        hV.primeIdealOf ⟨z, hz⟩ = hV.primeIdealOf ⟨z', hz'⟩ := by
      rintro z z' hz hz' rfl
      rfl
    have h2 : q i = q j := (hpw i).symm.trans ((key (hwV i) (hwV j) h).trans (hpw j))
    exact (hq.2.2.2 i j (h2 ▸ hq.2.1 j)).symm
  have hwb : w j ∉ Y.basicOpen (b j) := by
    intro h'
    have h1 : q j ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := h'
    rw [hV.fromSpec_preimage_basicOpen] at h1
    exact h1 (hq.2.1 j)
  refine ⟨rfl, fromSpec_specializes hq j, hcoh j, ?_, ?_, ?_⟩
  · intro h'
    exact hwb ((Y.basicOpen_res (a j) (homOfLE hVU').op).symm ▸ ⟨hwV j, h'⟩ : w j ∈ Y.basicOpen (b j))
  · letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI hloc0 := hV.isLocalization_stalk ⟨w j, hwV j⟩
    haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk (w j)) (q j).asIdeal := by
      rw [← hpw j]; exact hloc0
    have hgalg : Y.presheaf.germ V (w j) (hwV j) (b j) = algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := rfl
    have hg0 : Y.presheaf.germ V (w j) (hwV j) (b j) ≠ 0 := fun h0 =>
      ha0 j (by rw [hfn, ← algebraMap_germ (hwV j), h0, map_zero])
    have hmax : Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)} =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (w j)) := by
      refine le_antisymm ?_ ?_
      · rw [Ideal.span_singleton_le_iff_mem,
          ← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)), hgalg]
        exact Ideal.mem_map_of_mem _ (hq.2.1 j)
      · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)),
          Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        letI := Y.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
        haveI := hV.isLocalization_stalk ⟨y, hyV⟩
        haveI : (Ideal.span {Y.presheaf.germ V y hyV (b j)}).IsPrime :=
          (Ideal.span_singleton_prime (hprime j).ne_zero).2 (hprime j)
        let P : Ideal Γ(Y, V) := Ideal.comap (algebraMap Γ(Y, V) (Y.presheaf.stalk y))
          (Ideal.span {Y.presheaf.germ V y hyV (b j)})
        have hPp : P.IsPrime := Ideal.IsPrime.comap _
        have hPle : P ≤ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
          intro z hz
          have hz' : algebraMap Γ(Y, V) (Y.presheaf.stalk y) z ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
            (Ideal.span_singleton_le_iff_mem _).2
              ((IsLocalRing.mem_maximalIdeal _).2 (hprime j).not_unit) hz
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y)
            (hV.primeIdealOf ⟨y, hyV⟩).asIdeal z).1 hz'
        have hbP : b j ∈ P := Ideal.mem_span_singleton_self _
        have hqP : q j ≤ ⟨P, hPp⟩ := (hq.2.2.1 j ⟨P, hPp⟩ hPle).mp hbP
        obtain ⟨t, ht, s, hts⟩ := exists_mul_eq_of_mem_span (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
          (Y.presheaf.stalk y) (hqP hx)
        have htq : t ∉ (q j).asIdeal := fun h => ht (hq.1 j h)
        have hu : IsUnit (algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t) :=
          IsLocalization.map_units (Y.presheaf.stalk (w j)) (⟨t, htq⟩ : (q j).asIdeal.primeCompl)
        have e : algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) x =
            algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := by
          rw [← map_mul, ← map_mul, hts]
        refine Ideal.mem_span_singleton'.2 ⟨↑hu.unit⁻¹ * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s, ?_⟩
        rw [hgalg, mul_assoc, ← e, ← mul_assoc, hu.val_inv_mul, one_mul]
    have hlen : Module.length (Y.presheaf.stalk (w j))
        (Y.presheaf.stalk (w j) ⧸ Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)}) = 1 := by
      rw [hmax, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal _)
    show Scheme.ord (fnOf U (gen_mem hy) (a j)) (w j) = 1
    rw [hfn, ← algebraMap_germ (hwV j), GlobalTheory.Cartier.ord_algebraMap (hcoh j) hg0, hlen]
    rfl
  · intro v hvy hv1 hvw
    by_contra hva
    have hvV : v ∈ V := hvy.mem_open V.isOpen hyV
    have hbQ : b j ∈ (hV.primeIdealOf ⟨v, hvV⟩).asIdeal := by
      by_contra hn
      apply hva
      have h1 : hV.primeIdealOf ⟨v, hvV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := by
        rw [hV.fromSpec_preimage_basicOpen]; exact hn
      have h3 : hV.fromSpec (hV.primeIdealOf ⟨v, hvV⟩) ∈ Y.basicOpen (b j) := h1
      rw [hV.fromSpec_primeIdealOf] at h3
      exact hbas j h3
    have hle : q j ≤ hV.primeIdealOf ⟨v, hvV⟩ :=
      (hq.2.2.1 j _ ((specializes_iff_pOf hV hvV hyV).mp hvy)).mp hbQ
    have hQv1 : (hV.primeIdealOf ⟨v, hvV⟩).asIdeal.height = 1 := by
      letI := Y.presheaf.algebra_section_stalk (⟨v, hvV⟩ : V)
      haveI := hV.isLocalization_stalk ⟨v, hvV⟩
      have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨v, hvV⟩).asIdeal
        (Y.presheaf.stalk v)
      rw [ringKrullDim_stalk_eq_coheight, hv1] at this
      exact_mod_cast this.symm
    have heq : q j = hV.primeIdealOf ⟨v, hvV⟩ := by
      by_contra hne
      haveI : (q j).asIdeal.FiniteHeight :=
        (q j).asIdeal.finiteHeight_iff.mpr (Or.inr (by rw [hq1 j]; exact ENat.one_ne_top))
      have hlt : (q j).asIdeal < (hV.primeIdealOf ⟨v, hvV⟩).asIdeal :=
        lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1 j, hQv1] at this
      exact lt_irrefl _ this
    exact hvw (eq_of_pOf_eq hV hvV (hwV j) (by rw [hpw j]; exact heq.symm))

end GlobalTheory.RegParPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FibreTransfer

theorem exists_residueField_factor (S : Scheme.{0}) (p : S) (K : Type) [Field K] (x : Sp K ⟶ S)
    (hx : x (closedPoint K) = p) :
    ∃ θ : S.residueField p ⟶ CommRingCat.of K, Spec.map θ ≫ S.fromSpecResidueField p = x := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x⟩

theorem isGrpPullback_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    IsGrpPullback ((Over.pullback (Spec.map θ ≫ S.fromSpecResidueField p)).obj G)
      ((Over.pullback (S.fromSpecResidueField p)).obj G) (Spec.map θ)
      (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
        (by rw [pullback.condition, Category.assoc])) := by
  refine (isGrpPullback_pullback G (S.fromSpecResidueField p)).cancel
    ((isGrpPullback_pullback G (Spec.map θ ≫ S.fromSpecResidueField p)).congr rfl
      (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

theorem lbIso_fibre {S : Scheme.{0}} (G : Over S) {L : LB G.left} (hL : L.IsLB) (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    LBIso (L.pull (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p)))
      ((L.pull (pullback.fst G.hom (S.fromSpecResidueField p))).pull
        (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
          (by rw [pullback.condition, Category.assoc]))) := by
  have e := GlobalTheory.FibreAmple.lbIso_pull_pull hL
    (pullback.lift (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p))
      (pullback.snd G.hom _ ≫ Spec.map θ) (by rw [pullback.condition, Category.assoc]))
    (pullback.fst G.hom (S.fromSpecResidueField p))
  rw [pullback.lift_fst] at e
  exact e.symm

end GlobalTheory.FibreTransfer


open GlobalTheory.FibreTransfer in
theorem GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  intro S G _ hqc hsep hsm L hL K₁ _ z hP hA hK K _ x hx
  generalize hy : z (closedPoint K₁) = y at hx
  obtain ⟨θ₁, hz⟩ := exists_residueField_factor S y K₁ z hy
  obtain ⟨θ, rfl⟩ := exists_residueField_factor S y K x hx
  clear hy
  subst hz
  haveI := hqc; haveI := hsep; haveI := hsm
  have hLy := pull_isLB hL (pullback.fst G.hom (S.fromSpecResidueField y))
  have i₁ : QuasiCompact ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show QuasiCompact (pullback.snd G.hom _) from inferInstance
  have i₂ : IsSeparated ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show IsSeparated (pullback.snd G.hom _) from inferInstance
  have i₃ : Smooth ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show Smooth (pullback.snd G.hom _) from inferInstance
  have hd := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (S.residueField y) K₁ θ₁.hom
    ((Over.pullback (S.fromSpecResidueField y)).obj G) ((Over.pullback (Spec.map θ₁ ≫ S.fromSpecResidueField y)).obj G) _
    (isGrpPullback_fibre G y K₁ θ₁) _ _ hLy (pull_isLB hL _) (lbIso_fibre G hL y K₁ θ₁) hP hA hK
  have h₂ := isGrpPullback_fibre G y K θ
  obtain ⟨w, hw⟩ := lbIso_fibre G hL y K θ
  exact ⟨relAmple_pull h₂.1 hLy (pull_isLB hL _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hd.2.1,
    kTriv_pull h₂ hLy (pull_isLB hL _) ((isGen_iff w).1 hw) hd.2.2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleNilThickening

theorem exists_pow_eq_bot_of_isNilDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I}
    (h : IsNilDP κ) : ∃ N : ℕ, I ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := h
  have hlen : ∀ l : List R, ((l.map fun x => ((1 : ℕ), x)).map Prod.fst).sum = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
  have hprod : ∀ l : List R, (∀ x ∈ l, x ∈ I) →
      ((l.map fun x => ((1 : ℕ), x)).map fun p => κ.dpow p.1 p.2).prod = l.prod := by
    intro l hl; induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [κ.dpow_one (hl a (by simp)), ih fun x hx => hl x (by simp [hx])]
  have hl : ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ l.length → l.prod = 0 := by
    intro l hl' hle
    rw [← hprod l hl']
    exact hN _ (by simpa using hl') (by rw [hlen]; exact hle)
  have key : ∀ k : ℕ, ∀ y ∈ I ^ k, ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ k + l.length → l.prod * y = 0 := by
    intro k
    induction k with
    | zero => intro y _ l hl' hle; rw [hl l hl' (by omega), zero_mul]
    | succ k ih =>
      intro y hy l hl' hle
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on (C := fun y => l.prod * y = 0) hy ?_ ?_
      · intro a ha b hb
        have := ih a ha (b :: l) (by simpa [hb] using hl') (by simp; omega)
        rw [List.prod_cons] at this
        rw [← this]; ring
      · intro y z hy hz; rw [mul_add, hy, hz, add_zero]
  refine ⟨N, eq_bot_iff.2 fun y hy => ?_⟩
  have := key N y hy [] (fun x hx => by cases hx) (Nat.le_add_right N _)
  simpa using this

end GlobalTheory.AmpleNilThickening

namespace GlobalTheory.AmpleNilThickening

theorem relAmple_of_pow_eq_bot : ∀ (n : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ n = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    by_cases h0 : n = 0
    · subst h0
      have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
    set I := RingHom.ker π with hI
    let J : Ideal R := I ^ n
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self h0
    let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π fun a ha => (RingHom.mem_ker).1 (hJI ha)
    have hfac : π = π₁.comp q := RingHom.ext fun _ => rfl
    have hπ₁ : Function.Surjective π₁ := fun y => by
      obtain ⟨x, hx⟩ := hπ y
      exact ⟨q x, hx⟩
    have hker₁ : RingHom.ker π₁ ^ n = ⊥ := by
      have hle : RingHom.ker π₁ ≤ I.map q := by
        intro z hz
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hx : x ∈ I := RingHom.mem_ker.2 (RingHom.mem_ker.1 hz)
        exact Ideal.mem_map_of_mem q hx
      refine eq_bot_iff.2 ((Ideal.pow_right_mono hle n).trans ?_)
      rw [← Ideal.map_pow]
      exact (Ideal.map_quotient_self J).le
    have hsq : RingHom.ker q ^ 2 = ⊥ := by
      rw [Ideal.mk_ker, ← pow_mul]
      exact eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    have hcomp : spMap π = spMap π₁ ≫ spMap q := by
      rw [hfac]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let f : Sp (R ⧸ J) ⟶ Sp R := spMap q
    let X₁ : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom f)
    have hw' : β ≫ X.hom = (X₀.hom ≫ spMap π₁) ≫ f := by
      rw [hβ.w, hcomp, Category.assoc]
    let β₀ : X₀.left ⟶ X₁.left := pullback.lift β (X₀.hom ≫ spMap π₁) hw'
    have hβ₀ : β₀ ≫ pullback.fst X.hom f = β := pullback.lift_fst _ _ _
    have hpb : IsPullback β₀ X₀.hom X₁.hom (spMap π₁) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom f) (h₂₂ := f) (v₁₃ := X.hom) ?_
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback X.hom f)
      rw [hβ₀, ← hcomp]
      exact hβ
    have hX₁ : LocallyOfFiniteType X₁.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom f))
    let L₁ : LB X₁.left := L.pull (pullback.fst X.hom f)
    have hL₁ : L₁.IsLB := LB.isLB_pull hL _
    have hw₁ : LBIso L₀ (L₁.pull β₀) :=
      LBIso.trans hL₀ (LB.isLB_pull hL β) (LB.isLB_pull hL₁ β₀) hw
        (GlobalTheory.GenSpread.lbIso_pull_pull hL β₀ hβ₀.symm)
    have hA₁ : Out.RelAmple X₁ L₁ := ih (R ⧸ J) R₀ π₁ hπ₁ hker₁ X₁ X₀ β₀ hpb hX₁ L₁ L₀ hL₁ hL₀ hw₁ hA
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R (R ⧸ J) q Ideal.Quotient.mk_surjective hsq X X₁
      (pullback.fst X.hom f) (IsPullback.of_hasPullback X.hom f) hX L L₁ hL hL₁
      (lbIso_refl hL₁) hA₁

theorem relAmple_of_isNilDP : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro R R₀ _ _ I κ hκ π hπ hker X X₀ β hβ hX L L₀ hL hL₀ hw hA
  obtain ⟨N, hN⟩ := exists_pow_eq_bot_of_isNilDP hκ
  exact relAmple_of_pow_eq_bot N R R₀ π hπ (hker ▸ hN) X X₀ β hβ hX L L₀ hL hL₀ hw hA

end GlobalTheory.AmpleNilThickening
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfClosedProper
section
open GlobalTheory.AbLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SharpLift

theorem relAmple_of_closed_proper (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [IsProper B.hom] [Flat B.hom] (M : LB B.left) (hM : M.IsLB)
    (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀) (hg : Function.Surjective g)
    (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)))
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hA : RelAmple Y₀ N₀) : RelAmple B M := by
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine GlobalTheory.AmpleLocalBase.relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

theorem kTriv_of_localHom (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R]
    (π : R₁ →+* R) [IsLocalHom π] (B : Over (Sp R₁)) [GrpObj B] (hB : IsAbelianScheme B) (M : LB B.left) (hM : M.IsLB)
    (hA : RelAmple B M) (Y₀ : Over (Sp R)) [GrpObj Y₀] (b : Y₀.left ⟶ B.left) (hb : IsGrpPullback Y₀ B (spMap π) b)
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hK : KTriv Y₀ N₀) : KTriv B M := by
  obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb hiso hK (IsLocalRing.closedPoint R)
  have hcl : (spMap π) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R₁ := by
    exact IsLocalRing.comap_closedPoint π
  have htop : U = ⊤ := by
    rw [hcl] at hU
    exact top_le_iff.1 fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open U.2 hU
  subst htop
  have hL := pull_isLB hM (pullback.fst B.hom (⊤ : (Sp R₁).Opens).ι)
  have hPB := isGrpPullback_pullback B (⊤ : (Sp R₁).Opens).ι
  have hAb : IsAbelianScheme ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) := by
    have := hB.comm
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hPB.1 hB.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hPB.1 hB.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hPB.1 hB.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hPB.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hPB.2 T x y (pushPt hPB.1.w x) (pushPt hPB.1.w y) rfl rfl,
      ← hPB.2 T y x (pushPt hPB.1.w y) (pushPt hPB.1.w x) rfl rfl, _root_.mul_comm]
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ PUnit (fun _ => ⊤) B _ _ (by simp)
    (fun _ => isGrpPullback_pullback B _) _ _ hM (fun _ => hL) (fun _ => GlobalTheory.lbIso_refl hL) hB
    (fun _ => hAb) (fun _ => H)

end GlobalTheory.SharpLift
end

