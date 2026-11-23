module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrpSchemeAbsoluteFrobeniusKillsHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackCoordinateCombinationRatioAndVanish
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.PullCoordComb

def evalF {X : Scheme.{0}} (L : LB X) (i : L.ι) : LB.Sec L →+ Γ(X, L.U i) where
  toFun s := s.f i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (s : Fin n → LB.Sec L)
    (i : L.ι) : (∑ k, a k • s k).f i = ∑ k, resG X le_top (a k) * (s k).f i := by
  change evalF L i (∑ k, a k • s k) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

theorem linComb_ratio_and_vanish : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    (∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
          ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i)) ∧
    (y ≠ 0 → ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, algebraMap K Ω (lam k : K) * y k = 0 →
        ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) := by
  intro K Ω _ _ _ _ m y X _ p g ψ hbase hratio
  have hA : ∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι)
      (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
      ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
        ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) := by
    intro lam l i h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_smul_f, map_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, fnOf_resG, ← hbase, map_mul, mul_left_comm (ψ (y l)), hratio l k i h]
    ring
  refine ⟨hA, fun hy lam hsum => ?_⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, y k₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  apply GlobalTheory.LB.f_injective
  funext i
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have e := hA lam k₀ i hU
  rw [hsum, map_zero, zero_mul] at e
  have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
  rw [GlobalTheory.LB.zero_f, map_zero]
  exact (mul_eq_zero.1 e).resolve_left hψ

end GlobalTheory.PullCoordComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotGlobalHolds
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem quotGlobal_holds : QuotGlobal := by
  intro S _ A _ H _ i hA hi hm hf hfl
  have := hA.comm
  choose B instB q hq using GlobalTheory.T.exists_abelianQuotient_affineCover S A H i hA hi hm hf hfl
  have hfin : ∀ j, IsFinite (q j).left := fun j => (hq j).2.2.1
  have hflat : ∀ j, Flat (q j).left := fun j => (hq j).2.2.2.1
  have hsurj : ∀ j, Surjective (q j).left := fun j => (hq j).2.2.2.2.1
  have hqc : ∀ j, QuasiCompact (q j).left := fun j => by have := hfin j; infer_instance
  have hsq : ∀ j, _ := fun j => (hq j).2.2.2.2.2
  obtain ⟨b, hb1, hb2, hchar⟩ := _root_.GlobalTheory.QuotTransition.exists_transition S S.affineCover A H i B q hflat hsurj hqc hsq
  have hcoc := GlobalTheory.T.local_quotient_transition_cocycle S S.affineCover A H i B q b hflat hsurj hqc hb1 hchar
  obtain ⟨G0, F, ψ, hψ, hψ2⟩ := GlobalTheory.CocycleGlue.exists_glue (fun j => S.affineCover.X j) (fun j => (B j).left)
    (fun j => S.affineCover.f j) (fun j => inferInstance) (fun j => (B j).hom)
    (fun j k => pullback ((B j).hom ≫ S.affineCover.f j) (S.affineCover.f k)) (fun j k => pullback.fst _ _) b
    (fun j k => by rw [hb1]; exact IsPullback.of_hasPullback _ _) hb2 hcoc
  obtain ⟨Qm, hQF, hQm⟩ := GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients S S.affineCover A H i B q b G0 F ψ hchar (fun j k => (hψ2 j k).w)
    (fun j => (hψ j).w)
  let G : Over S := Over.mk F
  let Q : A ⟶ G := Over.homMk Qm hQF
  have hpb : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q :=
    _root_.GlobalTheory.GlueQuotPB.isPullback_translation_of_cover S S.affineCover A H G i Q B ψ q hψ hQm hsq
  obtain ⟨hQfin, hQfl, hQs⟩ := GlobalTheory.T.gluedQuotientMap_finite_flat_surjective S S.affineCover A G Q B ψ q hψ hQm hfin hflat hsurj
  have : IsCommMonObj A := hA.comm
  have : IsMonHom i := hi
  have : QuasiCompact Q.left := inferInstance
  obtain ⟨instG, hcomm, hhom, -⟩ := GlobalTheory.AbelianQuotient.exists_grpObj i Q hpb
  exact ⟨G, instG, Q, _root_.GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective S S.affineCover A G Q B ψ hA hcomm hQs hψ (fun j => (hq j).1), hhom, hQfin, hQfl, hQs, hpb⟩

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

namespace GlobalTheory.PDForm

theorem quot_fil_rel : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  intro R B _ _ _ J δ G _ _ J' δ' q h n hd hq hJ hk
  obtain ⟨-, -, hsurj, hker⟩ := _root_.GlobalTheory.CechDR.semiHom_quotient_surjective_ker R B G q h hq
  obtain ⟨-, -, hmul, -, -, hanti, -⟩ := (_root_.GlobalTheory.PDForm.rel_two_sided_and_bot).1 R B J δ
  have hv : ∀ m, ∀ a ∈ J, (0 : Derivation R B B) (δ.dpow (m + 1) a) = δ.dpow m a * (0 : Derivation R B B) a := by
    intro m a _; simp
  have hd0 := ((_root_.GlobalTheory.PDForm.ctr_lie_rel_filDR).2 R B J δ 0 hv n).2.1
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  ·
    have hle : rel R δ' ≤ (rel R δ).map h.mDR := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨m, a', ha', rfl⟩
      rw [hJ, Ideal.mem_map_iff_of_surjective _ hq] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      have e : ι1 (D R G (δ'.dpow (m + 1) (q a)) - δ'.dpow m (q a) • D R G (q a)) =
          h.mDR (ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a)) := by
        rw [h.mDR_ι, map_sub h.m1, h.m1_D, h.oneFormMap_smul_semilinear, h.m1_D, hd.2 a ha, hd.2 a ha]
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, a, ha, rfl⟩)
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 (hle hx)
    have hK : x - y ∈ filDR R δ n := by
      refine hker (filDR R δ n) (hmul n) (fun b hb ↦ ?_) (x - y) (by rw [map_sub, hxy, sub_self])
      have hb1 : algebraMap B (DR R B) b ∈ filDR R δ (n + 1) :=
        Ideal.mem_sup_left (Ideal.subset_span ⟨b, (hk b).1 hb, rfl⟩)
      refine ⟨hanti n (n + 1) (Nat.le_succ n) hb1, ?_⟩
      rw [← dDR_algebraMap]
      exact hd0 _ hb1
    have hyn : y ∈ filDR R δ n := Ideal.mem_sup_right hy
    simpa using add_mem hK hyn
  · have hle : filDR R δ (n + 1) ≤ (rel R δ').comap h.mDR := by
      refine sup_le (Ideal.span_le.2 ?_) (fun z hz ↦ mDR_mem_rel h hd hz)
      rintro _ ⟨b, hb, rfl⟩
      change h.mDR (algebraMap B _ b) ∈ rel R δ'
      rw [h.mDR_algebraMap, (hk b).2 hb, map_zero]
      exact zero_mem _
    exact hle hx

end GlobalTheory.PDForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugate
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem span_pull_baseChange (H : GlobalTheory.Published.AbelianDeRham.BaseChange) {R R' : Type} [CommRing R]
    [CommRing R'] (σ : R →+* R') {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap σ) φ) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    Submodule.span R' (Set.range (GlobalTheory.PDiv.grpMor_of_isGrpPullback h).pull) = ⊤ ∧
      PrimitiveSubmodule A' = Submodule.span R' ((GlobalTheory.PDiv.grpMor_of_isGrpPullback h).pull '' PrimitiveSubmodule A) := by
  letI := σ.toAlgebra
  obtain ⟨hbc, hF⟩ := H R A g hA hg R' A' φ h
  refine ⟨Submodule.eq_top_iff'.2 fun x ↦ ?_, hF⟩
  obtain ⟨z, rfl⟩ := hbc.2 x
  induction z with
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | tmul r c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ r (Submodule.subset_span ⟨c, rfl⟩)

theorem range_primPull_relFrob : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  intro H p _ R _ hR A A₁ _ _ π hπ F _ hF g hA hg
  obtain ⟨h1, h2⟩ := span_pull_baseChange H _ hπ hA hg
  have key : ∀ c, primPull (dp0 R) (𝟙 _) F ((GlobalTheory.PDiv.grpMor_of_isGrpPullback hπ).pull c) =
      frobDR p R hR A c := fun c ↦
    GrpMor.pull_pull (GlobalTheory.PDiv.grpMor_of_isGrpPullback hπ) (homMor (dp0 R) (𝟙 _) F)
      (frobMor p R hR A (cast_left p R hR A)) (fun _ ↦ rfl) hF c
  refine ⟨?_, ?_⟩
  · rw [LinearMap.range_eq_map, ← h1, Submodule.map_span, ← Set.range_comp, conjDR]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, key]
  · rw [h2, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, key]
    exact GlobalTheory.Published.ConjugateFiltration.Test.grpScheme_absoluteFrobenius_kills_hodgeFiltration p hR A (cast_left p R hR A)
      (frobMor p R hR A (cast_left p R hR A)) c hc

end GlobalTheory.ConjSeq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := _root_.GlobalTheory.Cartier.exists_ratOn_twist Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := _root_.GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsCommonGenericFibreOfCommonThird
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.SameComb

theorem sp_endo_eq_id {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp K ⟶ Sp K)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  rw [← Spec.map_preimage g] at h ⊢
  set ψ := Spec.preimage g
  have h' : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]; exact h
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    have ea := congrArg (fun f => f.hom ⟨a, ha⟩) h'
    have eb := congrArg (fun f => f.hom ⟨b, hb⟩) h'
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at ea eb
    change ψ.hom (a / b) = a / b
    rw [map_div₀]
    exact congrArg₂ (· / ·) ea eb
  rw [hψ, Spec.map_id]

theorem lbIso_pull_along {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso M (L.pull φ)) (r : Z ⟶ Y)
    {ψ : Z ⟶ X} (e : ψ = r ≫ φ) : LBIso (M.pull r) (L.pull ψ) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M r r rfl) (chartPullSame L (fun _ => ψ) (fun _ => φ) _ r fun _ => e)

theorem sec_of_pt {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) {Q : PolAV (Sp K)} {P : PolAV (Sp R)} {a : Q.A.left ⟶ P.A.left}
    (ha : IsGrpPullback Q.A P.A (spMap R.val.toRingHom) a) (t : baseOver (Sp R) ⟶ P.A) (w : Sp K ⟶ Q.A.left)
    (hw : w ≫ a = spMap R.val.toRingHom ≫ t.left) : w ≫ Q.A.hom = 𝟙 _ := by
  apply sp_endo_eq_id R frac
  have e := congrArg (· ≫ P.A.hom) hw
  simp only [Category.assoc, ha.1.w, Over.w t] at e
  simpa using e

theorem combine : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  intro o Ω o₁ o₂ Ω' _ _ _ _ _ _ _ _ S S₁ S₂ ρ ρ₁ ρ₂ ε ε₁ ε₂ lab₁ lab₂ φ h₁ h₂
  obtain ⟨P₀, a, a₁, ε₀, ha, ha₁, hLa, hLa₁, hε, hw⟩ := h₁
  obtain ⟨P₀', b, b₂, ε₀', hb, hb₂, hLb, hLb₂, hε', hw'⟩ := h₂
  obtain ⟨θ, hθm, hθ⟩ := grpPullback_iso ha hb
  haveI := hθm

  have ext : ∀ {T : Scheme.{0}} (u v : T ⟶ P₀'.A.left), u ≫ b = v ≫ b → u ≫ P₀'.A.hom = v ≫ P₀'.A.hom → u = v :=
    fun u v e₁ e₂ => hb.1.hom_ext e₁ e₂
  refine ⟨P₀, a₁, θ.hom.left ≫ b₂, ha₁, ((isGrpPullback_of_iso θ).comp hb₂).congr (Category.id_comp _) rfl, hLa₁, ?_,
    fun E => ⟨ε₀ E, (hε E).2, ?_⟩, fun x => ?_⟩
  · refine LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB ρ₂.P.isLB _) hLa ?_
    refine LBIso.trans (pull_isLB ρ.P.isLB _) (pull_isLB P₀'.isLB θ.hom.left) (pull_isLB ρ₂.P.isLB _)
      (lbIso_pull_along hLb θ.hom.left hθ.symm).symm (lbIso_pull_along hLb₂ θ.hom.left rfl)
  · have key : (ε₀ E).left ≫ θ.hom.left = θ.hom.left ≫ (ε₀' E).left := by
      apply ext
      · rw [Category.assoc, hθ, (hε E).1, Category.assoc, (hε' E).1, ← Category.assoc, hθ]
      · simp only [Category.assoc, Over.w]
    rw [← Category.assoc, key, Category.assoc, (hε' E).2, Category.assoc]
  · obtain ⟨w, hwa, hwa₁⟩ := hw x
    obtain ⟨w', hwb, hwb₂⟩ := hw' x
    refine ⟨w, hwa₁, ?_⟩
    have s₁ := sec_of_pt S₁.R S₁.frac ha₁ _ w hwa₁
    have s₂ := sec_of_pt S₂.R S₂.frac hb₂ _ w' hwb₂
    have hww : w ≫ θ.hom.left = w' := by
      apply ext
      · rw [Category.assoc, hθ, hwa, hwb]
      · rw [Category.assoc, Over.w, s₁, s₂]
    rw [← Category.assoc, hww, hwb₂]

end GlobalTheory.Poinc.SameComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFibreOfLiftedPartialDerivations
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regularFibre_of_liftedPartialDerivations :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  intro Λ _ _ _ _ σ _ B K _ _ _ _ _ _ hΛ hlift
  obtain ⟨F, hF⟩ := (Algebra.essFiniteType_iff (R := MvPolynomial σ Λ) (S := K)).1 inferInstance
  let φ : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ) →ₐ[MvPolynomial σ Λ] K :=
    MvPolynomial.aeval (fun z : ↥(F : Set K) => (z : K))
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial σ Λ) (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) (MvPolynomial (↥(F : Set K)) B) :=
    (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B)).toAlgebra
  have hC : ∀ x, algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K (MvPolynomial.C x) =
      algebraMap (MvPolynomial σ Λ) K x := fun x => MvPolynomial.aeval_C _ _
  set Q := RingHom.ker (algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  have hfrac : ∀ y : K, ∃ a b : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ), b ∉ Q ∧
      y * algebraMap _ K b = algebraMap _ K a := by
    intro y
    obtain ⟨t, ht, htu, hyt⟩ := hF y
    rw [Algebra.adjoin_eq_range] at ht hyt
    obtain ⟨b, hb⟩ := ht
    obtain ⟨a, ha⟩ := hyt
    refine ⟨a, b, ?_, ?_⟩
    · rw [hQdef, RingHom.mem_ker]
      change φ b ≠ 0
      rw [show φ b = t from hb]
      exact htu.ne_zero
    · change y * φ b = φ a
      rw [show φ b = t from hb, show φ a = y * t from ha]
  have hΛQ : ∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0 := by
    intro a ha
    rw [hQdef, RingHom.mem_ker, hC] at ha
    exact hΛ a ha
  choose Dσ hDσ using hlift
  choose dσ hdσC hdσX using fun s : σ => _root_.GlobalTheory.derivation_extend_mvPolynomial (MvPolynomial σ Λ) (↥(F : Set K))
    ((MvPolynomial.pderiv s : Derivation Λ (MvPolynomial σ Λ) (MvPolynomial σ Λ)).restrictScalars ℤ)
  choose Eσ hEσC hEσX using fun s : σ => _root_.GlobalTheory.derivation_extend_mvPolynomial B (↥(F : Set K)) (Dσ s)
  let d : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ))
      (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) dσ
  let D : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) B) (MvPolynomial (↥(F : Set K)) B) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) Eσ
  have hcompat : ∀ u x, D u (algebraMap _ (MvPolynomial (↥(F : Set K)) B) x) =
      algebraMap _ (MvPolynomial (↥(F : Set K)) B) (d u x) := by
    intro u x
    change D u (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) x) =
      MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) (d u x)
    rcases u with t | s
    · exact MvPolynomial.pderiv_map
    · change Eσ s _ = MvPolynomial.map _ (dσ s x)
      induction x using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.map_C, hEσC, hDσ, hdσC, MvPolynomial.map_C]
        rfl
      | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
      | mul_X p t ih =>
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, MvPolynomial.map_X, hEσX, hdσX, ih]
        simp [smul_eq_mul]
  obtain ⟨h, f, s, g, hg, hfQ, hQspan, hdet⟩ :=
    _root_.GlobalTheory.exists_generic_jacobian_data_iterated Λ σ (↥(F : Set K)) Q hΛQ d (fun t x => rfl) (fun s x => hdσC s x) (fun s t => hdσX s t)
  have hreg : IsRegularRing (MvPolynomial (↥(F : Set K)) B ⊗[MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)] K) :=
    _root_.GlobalTheory.regular_fibre_of_jacobian _ _ K Q rfl hfrac h f g (fun i => d (s i)) (fun i => D (s i))
      (fun i x => hcompat (s i) x) hg hfQ hQspan hdet
  obtain ⟨e⟩ := GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' (MvPolynomial σ Λ) B K (↥(F : Set K))
  exact IsRegularRing.of_ringEquiv e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPairInjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs.PairInj

theorem pull2_pairRes_restrict (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {X₀ Z₀ : Scheme.{0}}
    (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) {D : Type} [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ)
    (c : CatCoh.H2 (ext R₁ (OAff t₀))) :
    (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀))).pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' T'' a b
  show extHom R₁ (coefHom (CoefMap.restrict (OPair f₀ t₀) K) T'')
      (extHom R₁ (coefHom (pairRes f₀ t₀) (K.obj T'')) _) =
    extHom R₁ (coefHom (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀)) T'') _
  exact (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans ((PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans
    (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).symm)

theorem restrict_pair_injective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ Z₀ : Scheme.{0}) (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) (D : Type) [Category.{0} D] [Quiver.IsThin D] (K : D ⥤ (Pair f₀)ᵒᵖ), IsBas (opOf (K ⋙ pairFst f₀)) → Function.Injective (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 := by
  intro R₀ R₁ _ _ _ X₀ Z₀ t₀ f₀ D _ _ K hB x y e
  have hG := (BasisExt.restrict_ext_bijective R₀ R₁ Z₀ t₀ D (K ⋙ pairFst f₀) hB.1 hB.2).2.1
  have hP := ((PairExt.pairRes_ext_bijective R₀ R₁ X₀ Z₀ t₀ f₀).1.2).2
  obtain ⟨x0, rfl⟩ := hP x
  obtain ⟨y0, rfl⟩ := hP y
  rw [pull2_pairRes_restrict, pull2_pairRes_restrict] at e
  rw [hG e]

end GlobalTheory.LBObs.PairInj
end
end

