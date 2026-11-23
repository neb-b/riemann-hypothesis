module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericDim

open GlobalTheory.CoordChart

theorem exists_secCoord_field {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {σ : Type} (th : σ → M.Sec)
    {K : Type} [Field K] (x : Sp K ⟶ X) : ∃ v, SecCoord M th x v := by
  let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h : x p₀ ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  have : y = p₀ := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]; exact hk

theorem exists_common_field {R L : Type} [CommRing R] [CommRing L] [IsDomain L] (q : Ideal R) [q.IsPrime]
    (φ : R →+* L) (h : RingHom.ker φ = q) :
    ∃ (K : Type) (_ : Field K) (lam : L →+* K) (j : FractionRing (R ⧸ q) →+* K), Function.Injective lam ∧
      j.comp ((algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)) = lam.comp φ := by
  have hl := IsFractionRing.injective L (FractionRing L)
  have hχ : Function.Injective ((algebraMap L (FractionRing L)).comp (Ideal.Quotient.lift q φ fun a ha => h.ge ha)) :=
    hl.comp ((Ideal.injective_lift_iff fun a ha => h.ge ha).2 h)
  refine ⟨FractionRing L, inferInstance, algebraMap L (FractionRing L),
    IsFractionRing.lift (A := R ⧸ q) (K := FractionRing (R ⧸ q)) hχ, hl, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap hχ, RingHom.comp_apply,
    RingHom.comp_apply]
  exact congrArg _ (Ideal.Quotient.lift_mk q φ _)

theorem exists_extension {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) [IsOpenImmersion x]
    (hx : x ≫ Y.s = spMap β) (q : Ideal R) [q.IsPrime] (hmin : q ∈ minimalPrimes R)
    (y : R →+* FractionRing (R ⧸ q)) (hy : y = (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q))
    (v : Ix g (N' ^ 2) → FractionRing (R ⧸ q)) (hv : SecCoord Y.de Y.th (spMap y ≫ x) v)
    (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (hP : P.IsPrime) (hI : I ≤ P)
    (hle : P ≤ RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) v)) :
    ∃ (K : Type) (_ : Field K) (j : FractionRing (R ⧸ q) →+* K) (u : Kˣ),
      RingHom.ker (MvPolynomial.eval₂Hom (j.comp (y.comp β)) (fun a => u * j (v a))) = P := by
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc _ _ _ _ h3 hv
  set ev := MvPolynomial.eval₂Hom (y.comp β) v with hev
  let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* FractionRing (R ⧸ q) :=
    Ideal.Quotient.lift P ev fun a ha => hle ha
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let L := Localization.AtPrime (RingHom.ker e)
  have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
  let ψ : L →+* FractionRing (R ⧸ q) := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
  let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
  have hπ : ∀ F, ψ (π F) = ev F := fun F => by
    simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
    conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
    rfl
  have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
  have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
    intro l hl
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
    intro ha
    apply hl
    change ψ (IsLocalization.mk' L a s) = 0
    rw [IsLocalization.lift_mk'_spec, mul_zero]
    exact ha
  have hw : ∀ a, ψ (π (MvPolynomial.X a)) = v a := fun a => by rw [hπ]; simp [hev]
  have hβ : ψ.comp (π.comp MvPolynomial.C) = y.comp β := by ext t; simp [hπ, hev]
  have hL : InMM n N' I (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) := by
    refine ⟨fun F hF => by rw [hπe, hπ0]; exact hI hF, fun r hr a => ?_⟩
    obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨c, fun hm => hr.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hc
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L _ _ hL
  have h4 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts _ _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, hv⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp (FractionRing (R ⧸ q)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing (R ⧸ q)))
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal _)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  have hφy : ψ.comp φ = y := sp_inj (by rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq])
  have hφβ : φ.comp β = π.comp MvPolynomial.C := sp_inj (by rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1])
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    rw [hy, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) _),
      Ideal.Quotient.eq_zero_iff_mem]
  have hk1 : RingHom.ker φ ≤ q := fun r hr => by
    rw [RingHom.mem_ker] at hr
    rw [← hy0, ← hφy, RingHom.comp_apply, hr, map_zero]
  have hk2 : q ≤ RingHom.ker φ := hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ hk1
  haveI : IsDomain L := IsLocalization.isDomain_localization (RingHom.ker e).primeCompl_le_nonZeroDivisors
  obtain ⟨K, _, lam, j, hl, hj⟩ := exists_common_field q φ (le_antisymm hk1 hk2)
  rw [← hy] at hj
  have h6 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 _ j
  have h7 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ lam
  rw [← Category.assoc, sp_comp, hj, ← sp_comp, Category.assoc, hz] at h6
  obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 _ h7
  refine ⟨K, inferInstance, j, u, ?_⟩
  ext F
  rw [RingHom.mem_ker, ← hπ0, ← map_eq_zero_iff lam hl, ← hπe, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hj,
    RingHom.comp_assoc, hφβ, MvPolynomial.coe_eval₂Hom, ← funext hu']
  rfl

theorem le_ringKrullDim_of_independent {o : Type} [CommRing o] [IsDomain o] {R : Type} [CommRing R] [Algebra o R]
    [Algebra.FiniteType o R] {d : ℕ}
    (h : ∀ (q : Ideal R) [q.IsPrime], q ∈ minimalPrimes R → ∃ y : Fin d → FractionRing (R ⧸ q), AlgebraicIndependent o y)
    (q : Ideal (FractionRing o ⊗[o] R)) (hq : q ∈ minimalPrimes (FractionRing o ⊗[o] R)) :
    (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  have hqp : q.IsPrime := hq.1.1
  let f : R →ₐ[o] FractionRing o ⊗[o] R := Algebra.TensorProduct.includeRight
  have hmin : q.comap f ∈ minimalPrimes R := by
    letI : Algebra R (FractionRing o ⊗[o] R) := Algebra.TensorProduct.rightAlgebra
    have h1 := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))
      (FractionRing o ⊗[o] R) ⊥
    rw [Ideal.map_bot] at h1
    have h2 : q ∈ (⊥ : Ideal (FractionRing o ⊗[o] R)).minimalPrimes := hq
    rw [h1] at h2
    exact h2
  obtain ⟨y, hy⟩ := h (q.comap f) hmin
  let B := (FractionRing o ⊗[o] R) ⧸ q
  let f' : (R ⧸ q.comap f) →ₐ[o] FractionRing B :=
    (IsScalarTower.toAlgHom o B (FractionRing B)).comp (Ideal.quotientMapₐ q f le_rfl)
  have hf' : Function.Injective f' :=
    (IsFractionRing.injective B (FractionRing B)).comp (Ideal.quotientMap_injective' (f := f.toRingHom) (H := le_rfl) le_rfl)
  let j : FractionRing (R ⧸ q.comap f) →ₐ[o] FractionRing B := IsFractionRing.liftAlgHom hf'
  have h1 : AlgebraicIndependent o (j ∘ y) := hy.map' j.toRingHom.injective
  have : Algebra.IsAlgebraic o (FractionRing o) := IsLocalization.isAlgebraic _ (nonZeroDivisors o)
  have h2 := (h1.extendScalars (FractionRing o)).cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (FractionRing o) B
  have : FaithfulSMul (FractionRing o) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (FractionRing o) B).injective
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top (FractionRing o) B (FractionRing B), hs2] at h2
  have h3 : d ≤ s := by simpa using h2
  rw [hs1]
  exact_mod_cast h3

theorem le_ringKrullDim_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hN _ hb hC R _ _ x hox hx
  have : IsDedekindDomain o := hb.1
  have hx' : (x ≫ F.U.ι) ≫ F.Y.s = spMap (algebraMap o R) := by rw [Category.assoc, hx]
  have : Algebra.FiniteType o R := by
    obtain ⟨N, i, hi, -, hs⟩ := F.Y.qproj
    have := isProper_str o N
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
      rw [← hx', ← hs]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
    exact RingHom.finiteType_algebraMap.mp h
  refine le_ringKrullDim_of_independent fun q _ hq => ?_
  let y : R →+* FractionRing (R ⧸ q) := (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)
  have hy : y.comp (algebraMap o R) = algebraMap o _ := by
    rw [IsScalarTower.algebraMap_eq o (R ⧸ q) (FractionRing (R ⧸ q))]; rfl
  obtain ⟨v, hv⟩ := exists_secCoord_field F.Y.isLB F.Y.th (spMap y ≫ x ≫ F.U.ι)
  have hK := F.Y.loc _ (y.comp (algebraMap o R)) _ _ (by rw [Category.assoc, hx', sp_comp]) hv
  obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot 0
  obtain ⟨P, a₀, a, hP, hI, hle, -, hind⟩ := _root_.GlobalTheory.ThetaPrime.exists_prime_independent_ratios h1 h2 g N' J Mat κ w w' o b em C d hb hC
    (RingHom.ker (MvPolynomial.eval₂Hom (y.comp (algebraMap o R)) v)) _ (by omega) (RingHom.ker_isPrime _)
    (fun G hG => hK.1 G hG) (by rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X']; simpa using hc)
  obtain ⟨K, _, j, u, hker⟩ := exists_extension F.Y _ (x ≫ F.U.ι) hx' q hq y rfl v hv P hP hI hle
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K _ _ hker G ?_⟩
  have := congrArg j hG
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, ← hy] at this
  convert this using 2
  ext i
  simp [mul_div_mul_left]

end GlobalTheory.ZM.GenericDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleGenericFibreSpreadsOut
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

theorem algHom_eq_val {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) (u : S →ₐ[R] K) (x : S) : u x = x := by
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) (x : K)
  have hb : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hS : x * algebraMap R S (b : R) = algebraMap R S a := by
    apply Subtype.ext
    simpa using hx
  have hu : u x * algebraMap R K (b : R) = algebraMap R K a := by
    simpa only [map_mul, AlgHom.commutes] using congrArg u hS
  exact mul_right_cancel₀ hb (hu.trans hx.symm)

theorem mono_fst_localization {R : Type} [CommRing R] (M : Submonoid R) (A : Type) [CommRing A] [Algebra R A]
    [IsLocalization M A] {B : Scheme.{0}} (pB : B ⟶ Sp R) :
    Mono (pullback.fst pB (spMap (algebraMap R A))) := by
  haveI hepi : Epi (CommRingCat.ofHom (algebraMap R A)) :=
    ⟨fun g h e => CommRingCat.hom_ext (IsLocalization.ringHom_ext M (by
      simpa using congrArg CommRingCat.Hom.hom e))⟩
  haveI hsp : Mono (spMap (algebraMap R A)) :=
    (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op))
  infer_instance

end GenericLB

theorem lb_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M : LB (pullback pB (spMap (algebraMap R K)))), QuasiCompact pB → QuasiSeparated pB → M.IsLB → ∃ (f : R) (_ : f ≠ 0) (M' : LB (pullback pB (spMap (algebraMap R (Localization.Away f))))), M'.IsLB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → LBIso M (M'.pull j) := by
  intro R K _ _ _ _ _ _ B pB M hqc hqs hM
  classical
  haveI := hqc
  haveI := hqs
  obtain ⟨s, M₀, hM₀, -, hfac⟩ := LBLimit.exists_lb_of_isLimit (Spread.bcDiagram pB K)
    (fun i => (Spread.bcCone pB K).π.app i) (fun g => (Spread.bcCone pB K).w g)
    (Spread.isLimitBcCone pB K) M hM
  obtain ⟨f, hf0, hlift⟩ := GenericLB.exists_denom (R := R) (K := K) s.unop
  obtain ⟨ψ, hψ⟩ := hlift (Localization.Away f) (algebraMap R (Localization.Away f))
    (IsLocalization.Away.algebraMap_isUnit f)
  let ψa : Algebra.adjoin R (s.unop : Set K) →ₐ[R] Localization.Away f :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  refine ⟨f, hf0, M₀.pull (Spread.bcMap pB ψa), pull_isLB hM₀ _, fun jm hjm => ?_⟩
  have hfK : IsUnit (algebraMap R K f) :=
    isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0))
  let χ : Localization.Away f →ₐ[R] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => IsLocalization.lift_eq _ r }
  haveI := GenericLB.mono_fst_localization (Submonoid.powers f) (Localization.Away f) pB
  have hj : jm = Spread.bcMap pB χ := by
    rw [← cancel_mono (pullback.fst pB (spMap (algebraMap R (Localization.Away f)))), hjm,
      Spread.bcMap_fst]
  have hcomp : jm ≫ Spread.bcMap pB ψa = (Spread.bcCone pB K).π.app s := by
    rw [hj, Spread.bcMap_comp]
    show _ = Spread.bcMap pB (Algebra.adjoin R (s.unop : Set K)).val
    congr 1
    exact AlgHom.ext fun x => GenericLB.algHom_eq_val _ _ x
  exact hfac _ jm (Spread.bcMap pB ψa) hcomp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.AmpleFibre

open TopologicalSpace GlobalTheory.MulFinite

theorem exists_fn {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1))) (r : Z ⟶ X)
    (t : (L.pull r).Gen) (ht : t.IsGen) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ Out.nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j)) *
        ((gm (𝟙 Z) z (LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j)) (t.s (fun _ => j)))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) *
      (Z.presheaf.map (homOfLE (l₂ j)).op).hom ((t.s (fun _ => j))⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) (gs_appLE r z _ _ _ hz _)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    erw [gs_res (𝟙 Z) z (l₂ j) hz, gs_unit (𝟙 Z) z _ (l₂ j hz)]
    exact congrArg (fun x : (Z.presheaf.stalk z)ˣ => x.val ^ N)
      (map_inv (gm (𝟙 Z) z _ ) (t.s (fun _ => j)))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans ht (𝟙 Z) z (l₂ j hz.1) (l₂ j' hz.2)]
      have t₁ : trF (L := L) (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := PUnit) (fun _ => r) (fun _ => 1) (𝟙 Z) z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') := by simp [trF]
      rw [t₁, t₂]
      simpa only [pow_one] using pow_aux _ _ _ 1 N)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ Out.nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) k := X.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isAffineHom_of_field {k : Type} [Field k] {Y : Scheme.{0}} (y : Sp k ⟶ Y) : IsAffineHom y := by
  refine ⟨fun U _ => ?_⟩
  have : Subsingleton ↥(Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  by_cases h : ∃ p, p ∈ y ⁻¹ᵁ U
  · obtain ⟨p, hp⟩ := h
    have : y ⁻¹ᵁ U = ⊤ := top_unique fun x _ => by rwa [Subsingleton.elim x p]
    rw [this]; exact isAffineOpen_top _
  · have : y ⁻¹ᵁ U = ⊥ := bot_unique fun x hx => (h ⟨x, hx⟩).elim
    rw [this]; exact isAffineOpen_bot _

theorem exists_integral_closedImmersion {P : Scheme.{0}} (Z : Set P) (hc : IsClosed Z)
    (hi : IsIrreducible Z) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (i : C ⟶ P), IsClosedImmersion i ∧ Set.range i = Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨Z, hc⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace I.subscheme := by
    have e := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hr]; exact Subtype.irreducibleSpace hi
    exact e.irreducibleSpace_iff.2 this
  exact ⟨I.subscheme, isIntegral_of_irreducibleSpace_of_isReduced _, I.subschemeι, inferInstance, hr⟩

theorem locallyQuasiFinite_of_trivial_on_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (A : LB X), IsProper f → A.IsLB → (∀ x : X, ∃ (d : ℕ) (s : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (C : Scheme.{0}) [IsIntegral C] (i : C ⟶ pullback f y), IsFinite i → ∃ t : (A.pull (i ≫ pullback.fst f y)).Gen, t.IsGen) → LocallyQuasiFinite f := by
  intro X Y f A hf hA hs ht
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Sp Ω ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have hy' := isAffineHom_of_field y'
  have h₁ : IsAffineHom (pullback.fst f y') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback f y').flip hy'
  have h₂ : IsLocallyNoetherian (pullback f y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y')
  have h₃ : CompactSpace ↥(pullback f y') := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f y')
  have h₄ : IsNoetherian (pullback f y') := {}
  have hP : (Set.univ : Set ↥(pullback f y')).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine NoetherianSpace.finite_irreducibleComponents.sUnion fun Z hZ => ?_
    obtain ⟨C, _, i, hi, rfl⟩ := exists_integral_closedImmersion Z
      (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
    obtain ⟨t, ht⟩ := ht Ω y' C i inferInstance
    choose d s hx ha using hs
    choose a ha' using fun x => exists_fn A hA (d x) (s x) _ t ht
    have : LocallyQuasiFinite (i ≫ pullback.snd f y') := by
      refine locallyQuasiFinite_of_cover (K := Ω) _ a (top_unique fun c _ => ?_) fun x => ?_
      · refine Opens.mem_iSup.2 ⟨(i ≫ pullback.fst f y') c, ?_⟩
        rw [ha']
        exact hx _
      · rw [ha']
        exact (ha x).preimage _
    have : Subsingleton ↥(Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain ⟨p⟩ : Nonempty ↥(Sp Ω) := inferInstance
    have hC : Finite C := Set.finite_univ_iff.1
      (((i ≫ pullback.snd f y').finite_preimage_singleton p).subset fun c _ => Subsingleton.elim _ _)
    exact Set.finite_range i
  have := Set.finite_univ_iff.1 hP
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

end GlobalTheory.AmpleFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.AmpleDescent

theorem relAmple_of_faithfullyFlat : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (B : Over (Sp R)) (B' : Over (Sp R')) [GrpObj B] [GrpObj B'] (φ : B'.left ⟶ B.left) (L : LB B.left) (L' : LB B'.left), IsAbelianScheme B → IsGrpPullback B' B (spMap (algebraMap R R')) φ → L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → RelAmple B' L' → RelAmple B L := by
  intro R R' _ _ _ _ _ _ _ B B' _ _ φ L L' hB h hL hL' hw hA
  have : Flat (Out.specOf (algebraMap R R')) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Out.specOf (algebraMap R R')) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')⟩
  have : IsProper B.hom := hB.proper
  have : IsProper B'.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) h.1 inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  refine (relAmple_iff_isAmpleLB_of_isAffine B hL).2 (isAmpleLB_of_pull (algebraMap R R') h.1 hL ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine B' hL' hA).of_lbIso (LB.isLB_pull hL φ) hw.symm

end GlobalTheory.AmpleDescent
end

