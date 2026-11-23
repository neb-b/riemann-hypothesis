module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreRepresentatives

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (map φ f : MRingOver S ι) a :=
  fun m hm => hf m (support_map_subset φ f hm)


omit [Fintype K] in
theorem isMultiHomog_lincomb {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) (c d : ℂ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C c * f - C d * g) a := by
  classical
  intro m hm
  rw [C_mul', C_mul'] at hm
  rcases Finset.mem_union.1 (support_sub _ _ _ hm) with h | h
  · exact hf m (support_smul h)
  · exact hg m (support_smul h)

theorem eval_smul {s : MRingOver ℂ ι} {a : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (r : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : eval (fun p => r p.1 * z p) s = (∏ k, r k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ p : (Σ k, ι k), r p.1 ^ d p) = ∏ k, r k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, r k ^ d ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_eq_zero_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, (∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) → eval z (map (Int.castRingHom ℂ) f) = 0)
    (f : MRing ι) (hf : f ∈ mCoordIdeal y) : eval z (map (Int.castRingHom ℂ) f) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_multihomogeneous_components f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun b _ => hz _ ?_ ⟨b, isMultiHomog_i2comp b f⟩
  exact i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal y) b hf

end FibreRepresentatives


open FibreRepresentatives in
theorem FibreRepresentatives.proof (h : AvoidFormFinite.Statement) : FibreRepresentatives.Statement := by
  intro K _ ι _ Ω _ y D e L he hL hL0 ζ
  classical
  set Lc : Fin (D + 1) → MRingOver ℂ ι := fun j => map (Int.castRingHom ℂ) (L j) with hLc
  by_cases hζ : ζ = 0
  · refine ⟨∅, by simp, fun z hz ⟨t, ht⟩ => ?_⟩
    obtain ⟨j, hj⟩ := hL0 z hz
    exact absurd (by simpa [hζ] using ht j) hj
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ζ j₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hζ (funext hne)
  let S : Set (MRingOver ℂ ι) :=
    {g | ∃ f ∈ mCoordIdeal y, (∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) ∧ g = map (Int.castRingHom ℂ) f} ∪
      Set.range fun j => C (ζ j₀) * Lc j - C (ζ j) * Lc j₀

  have key : ∀ z : (Σ k, ι k) → ℂ, ((∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0) ↔
      (z ∈ mcPts (mCoordIdeal y) ∧ ∃ t : ℂ, ∀ j, eval z (Lc j) = t * ζ j) := by
    intro z
    constructor
    · rintro ⟨hb, hS⟩
      refine ⟨⟨hb, eval_eq_zero_of_homog y z fun f hf ha => hS _ (Or.inl ⟨f, hf, ha, rfl⟩)⟩,
        eval z (Lc j₀) / ζ j₀, fun j => ?_⟩
      have h1 := hS _ (Or.inr ⟨j, rfl⟩)
      simp only [map_sub, map_mul, eval_C] at h1
      field_simp
      linear_combination h1
    · rintro ⟨hz, t, ht⟩
      refine ⟨hz.1, fun s hs => ?_⟩
      rcases hs with ⟨f, hf, -, rfl⟩ | ⟨j, rfl⟩
      · exact hz.2 f hf
      · simp only [map_sub, map_mul, eval_C, ht]
        ring
  have hSh : ∀ s ∈ S, ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a := by
    rintro s (⟨f, -, ⟨a, ha⟩, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨a, isMultiHomog_map _ ha⟩
    · exact ⟨e, isMultiHomog_lincomb (isMultiHomog_map _ (hL j)) (isMultiHomog_map _ (hL j₀)) _ _⟩
  have hG : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) →
      eval z (Lc j₀) ≠ 0 := by
    intro z hb hS h0
    obtain ⟨hz, t, ht⟩ := (key z).1 ⟨hb, hS⟩
    have ht0 : t = 0 := by
      have := ht j₀
      rw [h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hj₀
    obtain ⟨j, hj⟩ := hL0 z hz
    exact hj (by simpa [hLc, ht0] using ht j)
  obtain ⟨T, hT⟩ := h K ι S (Lc j₀) e he (isMultiHomog_map _ (hL j₀)) hSh hG
  refine ⟨T.filter fun t => (∀ k, ∃ i, t ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval t s = 0, fun z hz => ?_,
    fun z hz hfib => ?_⟩
  · exact (key z).1 (Finset.mem_filter.1 hz).2
  · obtain ⟨hb, hS⟩ := (key z).2 ⟨hz, hfib⟩
    obtain ⟨t, htT, r, hr, rfl⟩ := hT z hb hS
    have hinv : t = fun p => (r p.1)⁻¹ * (r p.1 * t p) := by
      funext p
      rw [← mul_assoc, inv_mul_cancel₀ (hr p.1), one_mul]
    refine ⟨t, Finset.mem_filter.2 ⟨htT, fun k => ?_, fun s hs => ?_⟩, r, hr, rfl⟩
    · obtain ⟨i, hi⟩ := hb k
      exact ⟨i, fun h0 => hi (by simp [h0])⟩
    · obtain ⟨a, ha⟩ := hSh s hs
      rw [hinv, eval_smul ha (fun k => (r k)⁻¹), hS s hs, mul_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


set_option maxHeartbeats 1000000 in
theorem FibreSectionLift.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hsq : KH.CechDSqStatement) (hdg : KH.CechDDegStatement) (hR : ReductionComplex.Statement)
    (hZ : ZeroCocycleSection.Statement) (hC : SecCochReduce.Statement) : FibreSectionLift.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp hH1
  have hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) := hH1
  show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0,
    ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z
  intro z hz'

  let instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) := fun n =>
    (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i)
      (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)
  let instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := Submodule.module _
  let instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n) :=
    fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i)
      (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)
  let instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) :=
    Submodule.module _
  let instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) :=
    Submodule.Quotient.module _
  obtain ⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩ := hR K ι Ω y D p a hV hp

  have hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w' := by
    intro n w hw h0
    obtain ⟨w', h1, h2⟩ := hker₀ n w hw h0
    exact ⟨w', h1, by convert h2 using 2⟩
  have hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      (p : ℤ) • w = 0 → w = 0 := fun n w h => hnzd₀ n w (by convert h using 2)
  have hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0 := fun n w => by convert hkill₀ n w using 3
  have hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) :=
    hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)
  have hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := by
    exact (hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1
  have dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0 := fun n w =>
    LinearMap.congr_fun (hsq ℤ K ι _ n) w
  have dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w := fun n w =>
    map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w
  have memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 →
        w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n := fun n w hC hD =>
    Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩

  let f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ]
      KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 := LinearMap.lsmul ℤ _ (p : ℤ)
  have hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1,
      f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x) := fun x => by
    rw [LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]
    exact int_smul_eq_zsmul instH (p : ℤ) _
  have hsurj : Function.Surjective f := by
    intro h
    induction h using Submodule.Quotient.induction_on with
    | H x =>
    have hx := Submodule.mem_inf.mp x.2
    have hxd : KH.cechD ℤ ι _ 1 x.1 = 0 := by
      have := hx.2
      rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
    have hrx : FibreReduction.redCoch y p 1 x.1 ∈
        KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1 :=
      Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩
    have h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ :
        KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0 := Subsingleton.elim _ _
    have h0 := (Submodule.Quotient.mk_eq_zero _).mp h0'
    obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp h0)
    obtain ⟨u', hu', hru'⟩ := hon 0 u hu
    have hdu' := hdg ℤ K ι _ _ a 0 u' hu'
    obtain ⟨x', hx'C, hx'eq⟩ := hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by
      rw [map_sub, hd, hru']
      exact sub_eq_zero.mpr hdu.symm)
    have hx'Z := memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))
    refine ⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩
    rw [hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]
    refine Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩
    rw [LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]
    show _ = (p : ℤ) • x' - x.1
    rw [← hx'eq]
    abel
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj

  obtain ⟨w, hwC, hrw⟩ := hon 0 z (Submodule.mem_inf.mp hz').1
  have hzd : KH.cechD (ZMod p) ι _ 0 z = 0 := by
    have := (Submodule.mem_inf.mp hz').2
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
  obtain ⟨w', hw'C, hw'eq⟩ := hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])
  have hw'Z := memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))
  have hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0 := by
    apply hinj
    rw [map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]
    exact Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩
  obtain ⟨v, hvC, hdv⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))
  have hv0 := memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by
    rw [map_sub, dsmul]
    rw [LinearMap.restrictScalars_apply] at hdv
    rw [hdv]
    exact sub_eq_zero.mpr hw'eq)
  obtain ⟨s, hs, hsv⟩ := hZ K ι Ω y a _ hv0
  refine ⟨s, hs, ?_⟩
  rw [← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubmodules
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubmodules

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_of_weighted {q : MRingOver S ι} {c : K → ℤ}
    (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q (fun k => (c k).toNat) := by
  by_cases h0 : q = 0
  · intro m hm
    simp [h0] at hm
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    refine (QuotPartGraded.isMultiHomog_iff q _).2 ?_
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rw [hcc]
    exact hq

theorem smul_mem_of_weighted {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    {c e : K → ℤ} (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) {m : M} (hm : m ∈ 𝓜 e) :
    q • m ∈ 𝓜 (e + c) := by
  by_cases h0 : q = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    have h := hM.2 _ e q m (isMultiHomog_of_weighted hq) hm
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open Classical in
theorem component_smul_eq_zero {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜)
    {f : MRingOver S ι} (hf : f ∈ Module.annihilator (MRingOver S ι) M) (i : K → ℤ) {e : K → ℤ} {m : M}
    (hm : m ∈ 𝓜 e) :
    ((DirectSum.decompose (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)) f i :
      MRingOver S ι)) • m = 0 := by
  set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
  set s := (DirectSum.decompose 𝒜 f).support
  have hsum : ∑ c ∈ s, ((DirectSum.decompose 𝒜 f c : MRingOver S ι)) • m = 0 := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 f]
    exact Module.mem_annihilator.1 hf m
  obtain ⟨g, hg⟩ : ∃ g : (K → ℤ) → MRingOver S ι, ∀ c, g c = (DirectSum.decompose 𝒜 f c : MRingOver S ι) :=
    ⟨_, fun _ => rfl⟩
  have hgm : ∀ c, g c ∈ 𝒜 c := fun c => (hg c).symm ▸ (DirectSum.decompose 𝒜 f c).2
  simp only [← hg] at hsum
  suffices h : g i • m = 0 by rw [hg] at h; exact h
  by_cases hi : i ∈ s
  · have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝓜).1 hM.1.submodule_iSupIndep
    have hinj : Set.InjOn (fun c : K → ℤ => e + c) s := fun a _ b _ h => add_left_cancel h
    have key := hind (s.image fun c => e + c)
      (fun d => g (d - e) • m)
      (by
        intro d hd
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hd
        rw [add_sub_cancel_left]
        exact smul_mem_of_weighted hM ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (hgm c)) hm)
      (by
        rw [Finset.sum_image hinj]
        simpa only [add_sub_cancel_left] using hsum)
      (e + i) (Finset.mem_image_of_mem _ hi)
    simpa only [add_sub_cancel_left] using key
  · rw [hg, DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, zero_smul]

theorem mem_annihilator_of_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    (hq : ∀ e, ∀ m ∈ 𝓜 e, q • m = 0) : q ∈ Module.annihilator (MRingOver S ι) M := by
  refine Module.mem_annihilator.2 fun m => ?_
  have hm : m ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction 𝓜 (motive := fun x => q • x = 0) hm (fun e x hx => hq e x hx) (smul_zero q) ?_
  intro x y hx hy
  rw [smul_add, hx, hy, add_zero]

def prodSet (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) : Set M :=
  {y | ∃ (p : MRingOver S ι) (a : K → ℕ) (m : M) (c : K → ℤ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a ∧ p ∈ P ∧ m ∈ 𝓜 c ∧ y = p • m}

theorem prodSet_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) :
    ∀ y ∈ prodSet 𝓜 P, ∃ c, y ∈ 𝓜 c := by
  rintro _ ⟨p, a, m, c, hp, -, hm, rfl⟩
  exact ⟨_, hM.2 a c p m hp hm⟩

theorem smul_top_eq_span {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)}
    (hP : IsMultiHomogIdeal P) :
    (P • ⊤ : Submodule (MRingOver S ι) M) = Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
  apply le_antisymm
  · obtain ⟨T, hT, hPT⟩ := hP
    rw [Submodule.smul_le]
    intro r hr n _
    rw [hPT] at hr
    induction hr using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha⟩ := hT t ht
      have htP : t ∈ P := hPT ▸ Ideal.subset_span ht
      have hn : n ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
      have h0 : t • (0 : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
        rw [smul_zero]
        exact Submodule.zero_mem _
      refine Submodule.iSup_induction 𝓜
        (motive := fun x => t • x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P))
        hn (fun e x hx => Submodule.subset_span ⟨t, a, x, e, ha, htP, hx, rfl⟩) h0 ?_
      intro x y hx hy
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, a, m, c, -, hp, -, rfl⟩
    exact Submodule.smul_mem_smul hp Submodule.mem_top

theorem mem_iSup_span_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {x : M} (hx : x ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, (Submodule.span (MRingOver S ι) H).restrictScalars S ⊓ 𝓜 c := by
  have hx' := GradedSubquot.span_le_span_monTimes (S := S) (ι := ι) H hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := GradedSubquot.monTimes_homog hM hH hy
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.2 ⟨GradedSubquot.monTimes_subset_span H hy, hc⟩)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul s y _ hy => exact Submodule.smul_mem _ s hy

end GradedSubmodules


open GradedSubmodules in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
open Classical in
theorem GradedSubmodules.proof : GradedSubmodules.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hM
  refine ⟨?_, fun P hP => ?_⟩
  ·
    set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
    refine ⟨{q | (∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q a) ∧ q ∈ Module.annihilator (MRingOver S ι) M}, fun q hq => hq.1, ?_⟩
    apply le_antisymm
    · intro f hf
      rw [← DirectSum.sum_support_decompose 𝒜 f]
      refine Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨⟨_, isMultiHomog_of_weighted
        ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (DirectSum.decompose 𝒜 f i).2)⟩, ?_⟩
      exact mem_annihilator_of_homog hM fun e m hm => component_smul_eq_zero hM hf i hm
    · exact Ideal.span_le.2 fun q hq => hq.2
  · have hspan := smul_top_eq_span hM hP
    refine ⟨?_, ?_⟩
    · have hind1 : iSupIndep (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) :=
        GradedSubquot.iSupIndep_comap hM.1.submodule_iSupIndep
          ((P • ⊤ : Submodule (MRingOver S ι) M).subtype.restrictScalars S) (fun a b h => Subtype.ext h)
      have hsup1 : ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        have hx : (x : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ x.2
        have h := GradedSubquot.mem_iSup_inf hM (prodSet_homog hM P) hspan.ge x hx
        exact (show (⨆ c, ((Submodule.span (MRingOver S ι) (prodSet 𝓜 P)).comap
            (P • ⊤ : Submodule (MRingOver S ι) M).subtype).restrictScalars S ⊓
            subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c) ≤
              ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c from
          iSup_mono fun c => inf_le_right) h
      exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind1 hsup1,
        fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩
    · set L := (P • ⊤ : Submodule (MRingOver S ι) M) with hLdef
      set f := L.mkQ.restrictScalars S with hfdef
      have hker : LinearMap.ker f = L.restrictScalars S := by
        ext x
        simp [hfdef]
      have hind := hM.1.submodule_iSupIndep
      have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ 𝓜 c) := by
        rw [hker]
        intro x hx
        have hx' : x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ hx
        have := mem_iSup_span_inf hM (prodSet_homog hM P) hx'
        rwa [← hspan] at this
      have hind2 := GradedSubquot.iSupIndep_map_of_ker_le hind f hL
      have hsup2 : ⨆ c, quotGrading 𝓜 L c = ⊤ := by
        change ⨆ c, (𝓜 c).map f = ⊤
        rw [← Submodule.map_iSup, hM.1.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact Submodule.mkQ_surjective L
      refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
      rintro a c p _ hp ⟨x, hx, rfl⟩
      exact ⟨p • x, hM.2 a c p x hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtChartUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtChartUnit.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRingOver S ι)), IsClosedMultiPt P →
    ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, ∀ i ∈ I k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ (f : MRingOver S ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a → f ∉ P →
      ∃ t ∈ KH.cellMon S I, ∃ (g : MRingOver S ι) (b : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t (a + b) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b ∧ t - g * f ∈ P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

