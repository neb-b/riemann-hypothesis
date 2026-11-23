module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeFrameUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsNonarchimedeanLocalField
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.NonGenericCompare
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.LocFieldOfDVR

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

theorem exists_pow_lt_of_lt_one (a c : ℤᵐ⁰) (ha : a ≠ 0) (ha1 : a < 1) (hc : c ≠ 0) :
    ∃ n : ℕ, a ^ n < c := by
  obtain ⟨a', rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  obtain ⟨c', rfl⟩ := WithZero.ne_zero_iff_exists.mp hc
  refine ⟨(Multiplicative.toAdd c').natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha1
  rw [← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at ha1
  push_cast
  have ha2 : Multiplicative.toAdd a' ≤ -1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℤ) ≤ |Multiplicative.toAdd c'| + 1),
    neg_abs_le (Multiplicative.toAdd c')]

variable (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

abbrev val : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal o).valuation F

abbrev valued : Valued F ℤᵐ⁰ := Valued.mk' (val o F)

def equivInt : o ≃+* (val o F).integer :=
  RingEquiv.ofBijective
    ((algebraMap o F).codRestrict (val o F).integer (fun a => valuation_le_one _ a))
    ⟨fun a b h => IsFractionRing.injective o F (congrArg Subtype.val h),
     fun x => by
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one x.2
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem equivInt_val (a : o) : ((equivInt o F a : (val o F).integer) : F) = algebraMap o F a := rfl

variable {o F}

theorem mem_pow_iff {ϖ : o} (hϖ : Irreducible ϖ) (n : ℕ) (x : (val o F).integer) :
    x ∈ ((IsLocalRing.maximalIdeal o).map (equivInt o F)) ^ n ↔
      val o F (x : F) ≤ val o F (algebraMap o F ϖ) ^ n := by
  rw [← Ideal.map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton, (Valuation.integer.integers _).dvd_iff_le]
  simp only [map_pow, equivInt_val]
  exact Iff.rfl

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

theorem isAdic_map {ϖ : o} (hϖ : Irreducible ϖ) :
    letI := valued o F
    IsAdic ((IsLocalRing.maximalIdeal o).map (equivInt o F)) := by
  letI := valued o F
  set J := (IsLocalRing.maximalIdeal o).map (equivInt o F)
  set π := algebraMap o F ϖ
  have hπ0 : val o F π ≠ 0 := by
    simp only [π, ne_eq, map_eq_zero]
    exact (IsFractionRing.injective o F).ne_iff' (map_zero _) |>.mpr hϖ.ne_zero
  have hπ1 : val o F π < 1 := (valuation_lt_one_iff_mem _ ϖ).mpr
    (by simpa [IsDiscreteValuationRing.maximalIdeal] using hϖ.not_isUnit)
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds (J ^ n).toAddSubgroup (g := 0) ?_
    rw [mem_nhds_subtype]
    refine ⟨{y | val o F y < val o F π ^ n}, ?_, fun y hy => ?_⟩
    · change _ ∈ 𝓝 (0 : F)
      rw [Valued.mem_nhds_zero]
      have hπne : π ≠ 0 := by rintro h; simp [h] at hπ0
      refine ⟨Units.mk0 ((val o F).restrict (π ^ n)) (by simp [hπne]), fun y hy => ?_⟩
      simp only [Units.val_mk0, Set.mem_setOf_eq] at hy ⊢
      have hy' : (val o F).restrict y < (val o F).restrict (π ^ n) := hy
      rw [Valuation.restrict_lt_iff] at hy'
      simpa [map_pow] using hy'
    · exact (mem_pow_iff hϖ n y).mpr (le_of_lt hy)
  · obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).mp hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one _ _ hπ0 hπ1 hγ0
    refine ⟨n, fun y hy => hus (hγ ?_)⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact ((mem_pow_iff hϖ n y).mp hy).trans_lt hn

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

theorem compactSpace_integer [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    CompactSpace (Valued.integer F) := by
  letI := valued o F
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible o
  letI : (Valued.v : Valuation F ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (val o F) (e := 2) one_lt_two
  have hI := isAdic_map (F := F) hϖ
  have hpre : IsPrecomplete ((IsLocalRing.maximalIdeal o).map (equivInt o F)) (val o F).integer :=
    (IsPrecomplete.congr_ringEquiv _ _).mpr inferInstance
  haveI : IsUniformAddGroup (val o F).integer :=
    inferInstanceAs (IsUniformAddGroup (val o F).integer.toAddSubgroup)
  have hcomp : CompleteSpace (val o F).integer := (IsAdic.isPrecomplete_iff hI).mp hpre
  have hdvr : IsDiscreteValuationRing (Valued.integer F) :=
    inferInstanceAs (IsDiscreteValuationRing (val o F).integer)
  have hfin : Finite (IsLocalRing.ResidueField (Valued.integer F)) :=
    Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (equivInt o F)).toEquiv
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomp, hdvr, hfin⟩

theorem locallyCompactSpace [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    LocallyCompactSpace F := by
  letI := valued o F
  have := compactSpace_integer (o := o) (F := F)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isCompact_iff_compactSpace.mpr this) ((Valued.isOpen_integer F).mem_nhds (zero_mem _))

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

theorem exists_isNonarchimedeanLocalField : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [IsAdicComplete (IsLocalRing.maximalIdeal o) o] [Finite (IsLocalRing.ResidueField o)] [Field F] [Algebra o F] [IsFractionRing o F], ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F), IsNonarchimedeanLocalField F ∧ ∀ x : F, x ∈ 𝒪[F] ↔ ∃ a : o, algebraMap o F a = x := by
  intro o F _ _ _ _ _ _ _ _
  letI := valued o F
  letI vr : ValuativeRel F := .ofValuation (val o F)
  haveI : (val o F).Compatible := .ofValuation _
  refine ⟨vr, inferInstance, ?_, fun x => ?_⟩
  · have h1 : IsValuativeTopology F :=
      IsValuativeTopology.of_mem_nhds_iff_vle (val o F) (fun {s x} => Valued.mem_nhds)
    have h2 : ValuativeRel.IsNontrivial F :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (val o F)).mpr inferInstance
    have h3 : LocallyCompactSpace F := locallyCompactSpace (o := o) (F := F)
    exact {}
  · rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation F).vle_one_iff, (val o F).vle_one_iff]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨a, ha⟩ => ha ▸ valuation_le_one _ a⟩

end GlobalTheory.LocFieldOfDVR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealBasisTransportMeasurePreserving
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem fractionalIdeal_basis_transport (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W)
    (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W) (he : MeasurePreserving e volume μ)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W),
      (Submodule.span ℤ (Set.range b) : Set W) =
        (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧
      μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm
        (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(discr K : ℝ)|) := by
  set b₀ := mixedEmbedding.fractionalIdealLatticeBasis K J with hb₀
  refine ⟨_, inferInstance, b₀.map e.toLinearEquiv, ?_, ?_⟩
  · let f : mixedEmbedding.mixedSpace K →ₗ[ℤ] W := e.toLinearEquiv.toLinearMap.restrictScalars ℤ
    have hr : Set.range (b₀.map e.toLinearEquiv) = f '' Set.range b₀ := by
      rw [← Set.range_comp]; rfl
    have h0 : (Submodule.span ℤ (Set.range b₀) : Set (mixedEmbedding.mixedSpace K)) =
        mixedEmbedding K '' (J : Set K) := by
      ext x
      exact mixedEmbedding.mem_span_fractionalIdealLatticeBasis K J
    rw [hr, Submodule.span_image, Submodule.map_coe, h0, Set.image_image]
    rfl
  · have hfd : ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv) =
        e '' ZSpan.fundamentalDomain b₀ := (ZSpan.map_fundamentalDomain b₀ e.toLinearEquiv).symm
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : MeasurePreserving E volume μ := he
    have h1 : μ (ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv)) =
        volume (ZSpan.fundamentalDomain b₀) := by
      rw [← hE.measure_preimage_equiv, hfd]
      congr 1
      exact Set.preimage_image_eq _ e.injective
    rw [h1]
    have hfin : volume (ZSpan.fundamentalDomain b₀) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, ← mixedEmbedding.covolume_idealLattice K J,
      ZLattice.covolume_eq_measure_fundamentalDomain _ _
        (mixedEmbedding.fundamentalDomain_idealLattice K J), measureReal_def]

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChange
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.WitChange

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext v
  simp only [img, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨k u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

lemma prF_e (Fr : FrameD H r) (a : Fin r) : Fr.prF (Fr.f a.castSucc) = 0 := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f a.castSucc) (Fr.es c) • Fr.e c = Fr.f a.castSucc := by
    rw [Finset.sum_eq_single a]
    · rw [Fr.h_es, if_pos rfl, one_smul]; rfl
    · intro c _ hc; rw [Fr.h_es, if_neg (Ne.symm hc), zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h2 : ∑ c, H.h (Fr.f a.castSucc) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_projection_last_eq_self (Fr : FrameD H r) : Fr.prF (Fr.f (Fin.last r)) = Fr.f (Fin.last r) := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.es c) • Fr.e c = 0 :=
    Finset.sum_eq_zero (fun c _ => by rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero, zero_smul])
  have h2 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_mem (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) (b : Fin (r + 1)) :
    Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  rcases Fin.eq_castSucc_or_eq_last b with ⟨a, rfl⟩ | rfl
  · refine ⟨fun c => ?_, fun c => ?_, ⟨0, ?_, ?_⟩⟩
    · rw [Fr.h_es]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) ∈ _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)]; exact M.L.O.zero_mem
    · exact (prF_e Fr a).symm
    · rw [map_zero]; exact L.zero_mem
  · obtain ⟨xz, hxz, hxL, _⟩ := hL.2.2
    refine ⟨fun c => ?_, fun c => ?_, ⟨xz, ?_, hxL⟩⟩
    · rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero]; exact M.L.O.zero_mem
    · show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) ∈ _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne)]; exact M.L.O.zero_mem
    · rw [hxz]; exact (frame_projection_last_eq_self Fr).symm

end

theorem integral_change {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} (hOK : M.OK) {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : Uni A) (hAO : ∀ a b, A a b ∈ M.L.O) :
    ∃ k ∈ Fr.N, (∀ b, k (Fr.f b) = ∑ a, A a b • Fr.f a) ∧ img k (Fr.LamStd L) = Fr.LamStd L := by
  obtain ⟨kl, hkl, hkle, hklz, hklL⟩ := _root_.GlobalTheory.LocOver.UnipLevi.levi_integral M hOK H r Fr L A hA hAO
  obtain ⟨y, hyL, hyz, hyes⟩ := GlobalTheory.T.exists_inner_lattice_vector_anisotropic M hOK H r Fr L hL
  have hx : ∑ a : Fin r, A a.castSucc (Fin.last r) • Fr.f a.castSucc ∈
      Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc) :=
    Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ (⟨A a.castSucc (Fin.last r), hAO _ _⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨kz, hkz, hkzz, hkzX, hkzL⟩ := _root_.GlobalTheory.LocOver.ZStep.zstep M hOK H r Fr L hL y hyL hyz hyes _ hx
  refine ⟨kz * kl, mul_mem hkz hkl, fun b => ?_, by rw [img_mul, hklL, hkzL]⟩
  induction b using Fin.lastCases with
  | last =>
    rw [LinearEquiv.mul_apply, hklz, hkzz, Fin.sum_univ_castSucc, hA.2, one_smul, add_comm]
  | cast c =>
    rw [LinearEquiv.mul_apply, hkle c]
    apply hkzX
    rw [Fin.sum_univ_castSucc, hA.1 _ _ (Fin.castSucc_lt_last c), zero_smul, add_zero]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem witness_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hk hrel d t ht A A' g g' hA hA' hAA hg hg'
  obtain ⟨hT, hT', ⟨n, hn, hf, hLam⟩, ⟨n', hn', hf', hLam'⟩, hadm⟩ := ht
  obtain ⟨kA, hkA, hkAf, hkAL⟩ := integral_change hOK P.A d.L d.hL A hA (fun a b => (hAA a b).1)
  obtain ⟨kB, hkB, hkBf, hkBL⟩ := integral_change hOK P.B d.L' d.hL' A' hA' (fun a b => (hAA a b).2.1)
  have hfΛ : ∀ a, t.f a ∈ t.abelian₂ := by
    intro a; rw [hf, hLam]; exact ⟨P.A.f a, frame_mem P.A d.hL a, rfl⟩
  refine ⟨hT, hT', ⟨n * kA, mul_mem hn hkA, ?_, ?_⟩, ⟨n' * kB, mul_mem hn' hkB, ?_, ?_⟩, ?_⟩
  · funext b
    show g b = n (kA (P.A.f b))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hg b, hkAf b, map_sum, hf]
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkAL, hLam]
  · funext b
    show g' b = n' (kB (P.B.f b))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hg' b, hkBf b, map_sum, hf']
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkBL, hLam']
  · intro gg hgg
    obtain ⟨had, hio⟩ := hadm gg hgg
    refine ⟨fun b => ?_, hio⟩
    have hθ : theta M = (gg.q : F) := by simp [theta, hgg]
    show g' b - g b ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂
    have e1 : g' b - g b = ∑ a, (A' a b • (t.f' a - t.f a) - (A a b - A' a b) • t.f a) := by
      rw [hg b, hg' b, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [smul_sub, sub_smul]; abel
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ (⟨A' a b, (hAA a b).2.1⟩ : M.L.O) (had a)
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hAA a b).2.2
      rw [hθ] at hc
      rw [← hc]
      have h1 : algebraMap F E (gg.q : F) • t.f a ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂ :=
        Submodule.subset_span ⟨t.f a, hfΛ a, rfl⟩
      rw [smul_assoc]
      exact Submodule.smul_mem _ c h1

end GlobalTheory.LocOver.WitChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerBesselFunctionalEqIntegralSubgroup
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem afun_inner_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ = ∫ s, coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of (lmulM (Matrix.of s) x)), ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hzb : inWb k r z := hSide.1
  have hTz : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hμS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hstab := (_root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hσ).1
  have hSsub : Sset k r z ⊆ GG k r := (_root_.GlobalTheory.SgInf.closedSub_groups k r z hzb hTz).2.2.2.1.1
  have hD1 := _root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDec
  have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
  have hxu₁ : σ (Matrix.of x) u₁ ∈ DD σ w := hstab _ hx u₁ hu₁
  obtain ⟨hint, -, -, -⟩ := hD1 _ hxu v hv
  obtain ⟨-, heq₁, -, -⟩ := hD1 _ hxu₁ v hv
  have hPi := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hzb hTz hπ
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by rw [ae_iff]; exact hμS.2.2.1
  show ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v ξ⟫_ℂ = _
  rw [be, ContinuousLinearMap.integral_apply hint, ← integral_inner (hint.apply_continuousLinearMap ξ)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  have hsG : Matrix.of s ∈ GG k r := hSsub hs
  have hmul : σ (Matrix.of s * Matrix.of x) = (σ (Matrix.of s)).comp (σ (Matrix.of x)) :=
    hσ.1.2 _ hsG _ hx
  have hcoef : coef σ (σ (Matrix.of x) u) v (Matrix.of s) =
      coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) := by
    show ⟪v, σ (Matrix.of s) (σ (Matrix.of x) u)⟫_ℂ = ⟪v, σ (Matrix.of s * Matrix.of x) u⟫_ℂ
    rw [hmul]; rfl
  have hadj := ((hPi.2.2.1) _ hs).2
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hcoef]
  congr 1
  rw [← hadj, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  show PiS (psiGen k r z c) π (Matrix.of s) (be (psiGen k r z c) π μS σ (σ (Matrix.of x) u₁) v ξ) =
    be (psiGen k r z c) π μS σ (σ (Matrix.of s * Matrix.of x) u₁) v ξ
  rw [hmul, ContinuousLinearMap.comp_apply, (heq₁ _ hs).1]
  rfl

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundPrimedOfUnprimed
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TypeAsm

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem tailBd_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  intro D τ w θ lam q H₁ h W hW A hA
  exact h (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA)

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepthStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r), x ∈ Nset k r → Dep k r (2 * r - 2 * a.val) (x - 1) → (x (eI k r a) (esI k r a)).re = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.re_corner_eq_zero | exact GlobalTheory.SnMass.VolN.re_corner_eq_zero | (intros; apply GlobalTheory.SnMass.VolN.re_corner_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEqStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictFundamentalDomain_measure_eq : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.SnMass.VolN.strictFD_measure_eq | exact GlobalTheory.SnMass.VolN.strictFD_measure_eq | (intros; apply GlobalTheory.SnMass.VolN.strictFD_measure_eq <;> assumption)
end

