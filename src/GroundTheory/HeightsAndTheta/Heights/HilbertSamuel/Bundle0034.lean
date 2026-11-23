module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace SectionsRank

theorem sec_eq_span (o : Type*) [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
    (x : ι → Ω) (n : ℕ) : sec o x n = Submodule.span o (Set.range x ^ n) := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Submodule.span_pow]
  congr 3
  ext i
  simp

theorem exists_int_multiple {ι : Type*} (f : MvPolynomial ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : MvPolynomial ι ℤ, map (Int.castRingHom ℚ) p = (N : ℚ) • f := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, C q.num, ?_⟩
    rw [map_C, smul_eq_C_mul, ← C_mul, Rat.den_mul_eq_num]
    rfl
  | add f g hf hg =>
    obtain ⟨a, ha, p, hp⟩ := hf
    obtain ⟨b, hb, r, hr⟩ := hg
    refine ⟨a * b, Nat.mul_pos ha hb, (b : ℤ) • p + (a : ℤ) • r, ?_⟩
    rw [map_add (f := _), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, hp, hr, map_C, map_C]
    simp only [smul_eq_C_mul, eq_intCast, Int.cast_natCast, Nat.cast_mul, map_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨a, ha, p, hp⟩ := hf
    refine ⟨a, ha, p * X i, ?_⟩
    rw [map_mul, hp, map_X, smul_mul_assoc]

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type}

theorem mem_map_coordIdeal_iff [Fintype J] (x : J → Ω) {n : ℕ} {f : MvPolynomial J ℚ}
    (hf : f.IsHomogeneous n) :
    f ∈ (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ aeval x f = 0 := by
  constructor
  · intro h
    have hle : (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤
        RingHom.ker (aeval x : MvPolynomial J ℚ →ₐ[ℚ] Ω) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval x (MvPolynomial.map (algebraMap ℤ ℚ) p) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem_coordIdeal hp
    exact hle h
  · intro h
    obtain ⟨N, hN, p, hp⟩ := exists_int_multiple f
    have hpn : p.IsHomogeneous n := by
      refine IsHomogeneous.of_map (f := Int.castRingHom ℚ) (RingHom.injective_int _) ?_
      rw [hp]
      exact (mem_homogeneousSubmodule n _).mp
        (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule n f).mpr hf))
    have hp0 : aeval x p = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, hp, map_smul, h, smul_zero]
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℚ))
      (mem_coordIdeal_of_isHomogeneous ℤ x hpn hp0)
    rw [hp, smul_eq_C_mul] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have := Ideal.mul_mem_left _ (C (N : ℚ)⁻¹) hmem
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hN', C_1, one_mul] at this

theorem finrank_map_eq {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] (V : Submodule K M)
    (f : M →ₗ[K] N) (g : M →ₗ[K] N') (h : ∀ v ∈ V, f v = 0 ↔ g v = 0) :
    Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have ef : V.map f = LinearMap.range (f ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eg : V.map g = LinearMap.range (g ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (f ∘ₗ V.subtype) = LinearMap.ker (g ∘ₗ V.subtype) := by
    ext v
    simpa using h v v.2
  rw [ef, eg]
  exact ((f ∘ₗ V.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g ∘ₗ V.subtype).quotKerEquivRange)).finrank_eq

theorem finrank_sec_int [Fintype J] (x : J → Ω) (n : ℕ) :
    Module.finrank ℤ (sec ℤ x n) = Module.finrank ℚ (sec ℚ x n) := by
  have : Module.Finite ℤ (sec ℤ x n) := Module.Finite.iff_fg.mpr (sec_fg x n)
  let b := Module.Free.chooseBasis ℤ (sec ℤ x n)
  let v : Module.Free.ChooseBasisIndex ℤ (sec ℤ x n) → Ω := fun i => (b i : Ω)
  have hli : LinearIndependent ℤ v :=
    b.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hspanZ : Submodule.span ℤ (Set.range v) = sec ℤ x n := by
    have : Set.range v = (sec ℤ x n).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspanQ : Submodule.span ℚ (Set.range v) = sec ℚ x n := by
    rw [← Submodule.span_span_of_tower ℤ, hspanZ, sec_eq_span ℤ, sec_eq_span ℚ,
      Submodule.span_span_of_tower]
  rw [Module.finrank_eq_card_chooseBasisIndex, ← hspanQ, finrank_span_eq_card hliQ]

end SectionsRank


open SectionsRank in
theorem SectionsRank.proof : SectionsRank.Statement := by
  intro Ω _ _ κ _ x n
  set q := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ) = fun _ _ => 1 := by
    funext v u
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  have hV : weightedHomogeneousSubmodule ℚ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ))
      (fun _ => n) = homogeneousSubmodule (Ix κ) ℚ n := by
    ext f
    rw [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, hw]
    have hwt : ∀ d : Ix κ →₀ ℕ,
        Finsupp.weight (fun _ _ => (1 : ℕ) : Ix κ → Unit → ℕ) d = fun _ => Finsupp.weight 1 d := by
      intro d
      funext u
      simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    simp only [IsHomogeneous, IsWeightedHomogeneous, hwt, funext_iff, forall_const]
  have hg : ∀ m : Unit → ℕ, m = (fun _ => n) →
      GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece q m =
        (homogeneousSubmodule (Ix κ) ℚ n).map (Ideal.Quotient.mkₐ ℚ q).toLinearMap := by
    rintro m rfl
    unfold GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece
    rw [hV]
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
  rw [if_pos (fun _ => Int.natCast_nonneg n), hg _ (by funext; simp), finrank_sec_int]
  congr 1
  refine finrank_map_eq _ _ _ fun f hf => ?_
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    AlgHom.toLinearMap_apply]
  exact mem_map_coordIdeal_iff x ((mem_homogeneousSubmodule n f).mp hf)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfIntegralMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter NumberField Topology

noncomputable section

set_option linter.unusedSectionVars false

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isClosed_liesOver {F : Type} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ) :
    IsClosed {z | LiesOver y sg z} := by
  have : {z | LiesOver y sg z} = ⋂ (d : K → ℕ) (g : MRing ι) (h : MRing ι) (θ : F)
      (_ : IsMultiHomog g d) (_ : IsMultiHomog h d) (_ : aeval y g = algebraMap F Ω θ * aeval y h),
      {z : (Σ k, ι k) → ℂ | eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun d => isClosed_iInter fun g => isClosed_iInter fun h => isClosed_iInter fun θ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  exact isClosed_eq (MvPolynomial.continuous_eval _) (continuous_const.mul (MvPolynomial.continuous_eval _))

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem not_mem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  rw [mCoordIdeal, RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hf] at hmem
  rcases mul_eq_zero.1 hmem with h | h
  · exact h0 (MvPolynomial.C_eq_zero.1 h)
  · exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

theorem isMultiHomog_mul {f g : MRing ι} {df dg : K → ℕ} (hf : IsMultiHomog f df)
    (hg : IsMultiHomog g dg) : IsMultiHomog (f * g) (df + dg) := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf a ha k, hg b hb k]

theorem norm_le_of_isSmallH {F : Type} [Field F] [Fintype (F →+* ℂ)] [Algebra F Ω]
    (hND : NonvanishingDense.Statement) {y : (Σ k, ι k) → Ω} {d : ℕ} {A : HermLine ι} {τ : ℕ} {s : Ω}
    (θ : F) (har : IsArithVar (mCoordIdeal y) d) (hb : Birational y) (hA : IsSmoothHerm A)
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z)
    (hs : IsSmallH (mCoordIdeal y) y A τ s)
    {dg dh : K → ℕ} {g h : MRing ι} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) (hgh : aeval y g = algebraMap F Ω θ * s * aeval y h)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {sg : F →+* ℂ} (hzs : LiesOver y sg z) :
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
      ‖sg θ‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
  obtain ⟨e, g1, h1, hg1, hh1, hne, hrep⟩ := hb (algebraMap F Ω θ)
  set ev : MRing ι → ((Σ k, ι k) → ℂ) → ℂ := fun f z => eval z (map (Int.castRingHom ℂ) f) with hev

  have hpt : ∀ z' ∈ mcPts (mCoordIdeal y), LiesOver y sg z' → ev h1 z' ≠ 0 →
      ‖ev g z'‖ ≤ ‖sg θ‖ * ‖ev h z'‖ * A.h z' ^ τ := by
    intro z' hz' hl hh0
    have hsm := hs (dg + e) (e + dh) (g * h1) (g1 * h) z' (isMultiHomog_mul hg hh1)
      (isMultiHomog_mul hg1 hh) (fun k => by simp only [Pi.add_apply, Nat.cast_add, hdeg k]; ring)
      (by rw [map_mul, map_mul, hgh, hrep]; ring) hz'
    have hrel := hl e g1 h1 θ hg1 hh1 hrep
    simp only [map_mul, norm_mul] at hsm
    change ‖ev g z'‖ * ‖ev h1 z'‖ ≤ ‖ev g1 z'‖ * ‖ev h z'‖ * A.h z' ^ τ at hsm
    rw [show ev g1 z' = sg θ * ev h1 z' from hrel, norm_mul] at hsm
    have hp : 0 < ‖ev h1 z'‖ := norm_pos_iff.2 hh0
    nlinarith [hsm, hp]

  set R : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  set U : Set ((Σ k, ι k) → ℂ) := R ∩ ⋂ sg' : {sg' : F →+* ℂ // sg' ≠ sg}, {z | LiesOver y sg'.1 z}ᶜ
  have hUo : IsOpen U := isOpen_blockNonzero.inter
    (isOpen_iInter_of_finite fun sg' => (isClosed_liesOver y sg'.1).isOpen_compl)
  have hzU : z ∈ U := ⟨hz.1, Set.mem_iInter.2 fun sg' hl => sg'.2 ((hex z hz).unique hl hzs)⟩
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z => ‖ev g z‖ - ‖sg θ‖ * ‖ev h z‖ * A.h z ^ τ
  have hφ : ContinuousAt φ z := by
    have hAc : ContinuousAt A.h z :=
      (hA.continuousOn).continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    exact ((MvPolynomial.continuous_eval _).norm.continuousAt).sub
      ((continuousAt_const.mul (MvPolynomial.continuous_eval _).norm.continuousAt).mul (hAc.pow τ))
  by_contra hcon
  have hpos : 0 < φ z := by simp only [φ]; linarith [not_le.1 hcon]
  have hnb : {z' | 0 < φ z'} ∩ U ∈ 𝓝 z :=
    Filter.inter_mem (hφ.eventually (lt_mem_nhds hpos)) (hUo.mem_nhds hzU)
  have hcl := hND K ι (mCoordIdeal y) d h1 har (not_mem_mCoordIdeal hh1 hne) hz
  obtain ⟨z', ⟨hφ', hU'⟩, hz'P, hz'h⟩ := mem_closure_iff_nhds.1 hcl _ hnb
  obtain ⟨sg'', hl'', -⟩ := hex z' hz'P
  have hsg : sg'' = sg := by
    by_contra hne'
    exact (Set.mem_iInter.1 hU'.2 ⟨sg'', hne'⟩) hl''
  subst hsg
  have := hpt z' hz'P hl'' hz'h
  simp only [Set.mem_ofPred_eq, φ] at hφ'
  linarith

theorem isSmallH_mul {F : Type} [Field F] [Fintype (F →+* ℂ)] [Algebra F Ω]
    (hND : NonvanishingDense.Statement) {y : (Σ k, ι k) → Ω} {d : ℕ} {A A' : HermLine ι} {τ : ℕ}
    (har : IsArithVar (mCoordIdeal y) d) (hb : Birational y) (hA : IsSmoothHerm A)
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) (ha : A'.a = A.a) (θ : F)
    (hkey : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ‖sg θ‖ * A.h z ^ τ ≤ A'.h z ^ τ)
    {s : Ω} (hs : IsSmallH (mCoordIdeal y) y A τ s) :
    IsSmallH (mCoordIdeal y) y A' τ (algebraMap F Ω θ * s) := by
  intro dg dh g h z hg hh hdeg hgh hz
  obtain ⟨sg, hsg, -⟩ := hex z hz
  have h1 := norm_le_of_isSmallH hND θ har hb hA hex hs hg hh (fun k => by rw [← ha]; exact hdeg k)
    (by rw [hgh]) hz hsg
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ ‖sg θ‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := h1
    _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (‖sg θ‖ * A.h z ^ τ) := by ring
    _ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * A'.h z ^ τ :=
        mul_le_mul_of_nonneg_left (hkey z hz sg hsg) (norm_nonneg _)

theorem mul_mem_chartLatNm {F : Type} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ)
    {θ : F} (hθ : IsIntegral ℤ θ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    algebraMap F Ω θ * s ∈ chartLatNm y a τ := by
  intro c hc
  have h := hs c hc
  rw [mul_assoc]
  have hθ' : IsIntegral (chartRingZ y c) (algebraMap F Ω θ) := (hθ.algebraMap).tower_top
  exact (integralClosure (chartRingZ y c) Ω).mul_mem hθ' h

theorem smallSectionCount_le_of_integral_mul {F : Type} [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {A A' : HermLine ι}
    (ha : A'.a = A.a) {τ : ℕ}
    (hfin : {s : chartLatNm y A'.a τ | IsSmallH (mCoordIdeal y) y A' τ (s : Ω)}.Finite)
    {θ : F} (hθ : IsIntegral ℤ θ) (hθ0 : θ ≠ 0)
    (hmul : ∀ s : Ω, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y A' τ (algebraMap F Ω θ * s)) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A') (chartLatNm y A'.a) τ := by
  unfold smallSectionCount
  have : Finite {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} := hfin.to_subtype
  have hθ0' : algebraMap F Ω θ ≠ 0 := (map_ne_zero _).2 hθ0
  have hc : Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} ≤
      Nat.card {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨algebraMap F Ω θ * (s.1 : Ω), by rw [ha]; exact mul_mem_chartLatNm y A.a τ hθ s.1.2⟩,
        hmul _ s.2⟩ : {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)})) ?_
    intro s t hst
    have h := congrArg (fun u : {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} =>
      ((u.1 : chartLatNm y A'.a τ) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hθ0' h))
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

end Lemmas

theorem ArithmeticVolumeNefDual.proof (hG7p : ArithmeticVolumeNef.Statement) (hPk : PackingStatement) (hU : UnitApprox.Statement)
    (hND : NonvanishingDense.Statement) (hTw : TwistMetric.Statement) : ArithmeticVolumeNefDual.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D a A P0 Λ II hD hII har hb ha hP0 hsp hconj hΛpos hΛconj hΛsum hex hmon

  have hn : (0 : ℝ) < Fintype.card (F →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
  set m : ℝ := (∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ) with hm_def
  have hm : m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hΛsum hn.le
  set u : (F →+* ℂ) → ℝ := fun sg => Real.log (Λ sg) - m with hu_def
  have hu_conj : ∀ sg, u (ComplexEmbedding.conjugate sg) = u sg := fun sg => by simp only [u, hΛconj]
  have hu_sum : ∑ sg, u sg = 0 := by
    simp only [u]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm_def,
      mul_div_cancel₀ _ hn.ne', sub_self]
  obtain ⟨C, hC⟩ := hU F u hu_conj hu_sum
  obtain ⟨c, hc⟩ := hTw K ι Ω F y D A P0 II u hD hII har hb hP0 hsp hconj hex hu_conj hu_sum
  have hden : ∀ τ : ℕ, 0 ≤ ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun τ => by positivity

  have hδ : ∀ δ : ℝ, 0 < δ →
      limsup (fun τ : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
        ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
        II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ := by
    intro δ hδ
    obtain ⟨A', ha', hsp', hconj', hpt, hII'⟩ := hc δ hδ
    have ha'' : A'.a = fun k => (a k : ℤ) := ha'.trans ha

    have hmon' : MonomialsBounded (mCoordIdeal y) A' a := by
      intro z hz μ hμ
      obtain ⟨sg, hsg, -⟩ := hex z hz
      have hAz : 0 < A.h z := A.pos z hz.1
      rw [hpt z hz sg hsg]
      calc ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z := hmon z hz sg hsg μ hμ
        _ = Real.exp (u sg + m) * A.h z := by
            rw [show u sg + m = Real.log (Λ sg) by simp only [u]; ring, Real.exp_log (hΛpos sg)]
        _ ≤ Real.exp (u sg + δ) * A.h z :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hAz.le
    have hG := hG7p K ι Ω y D a A' P0 II hD hII har hb ha'' hP0 hsp' hmon' hconj'
    obtain ⟨hfin, C', hC'⟩ := hPk K ι Ω y D A' (chartLatNm y A'.a) har hb hsp'.1 (fun _ => le_rfl)
    refine le_trans ?_ (hG.trans hII')
    refine limsup_le_limsup ?_ ?_ ?_
    ·
      refine eventually_atTop.2 ⟨⌈C / δ⌉₊, fun τ hτ => div_le_div_of_nonneg_right ?_ (hden τ)⟩
      obtain ⟨ε, hε⟩ := hC τ
      have hCτ : C ≤ τ * δ := (div_le_iff₀ hδ).1 (Nat.ceil_le.1 hτ)
      have hε0 : ((ε : 𝓞 F) : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ε.ne_zero
      refine smallSectionCount_le_of_integral_mul ha' (hfin τ) (RingOfIntegers.isIntegral_coe _) hε0 fun s hs => ?_
      refine isSmallH_mul hND har hb hsp.1 hex ha' _ ?_ hs
      intro z hz sg hsg
      have hAz : 0 < A.h z := A.pos z hz.1
      have hpos : 0 < ‖sg ((ε : 𝓞 F) : F)‖ := norm_pos_iff.2 ((map_ne_zero sg).2 hε0)
      have hlog : Real.log ‖sg ((ε : 𝓞 F) : F)‖ ≤ τ * u sg + τ * δ := by
        linarith [(abs_le.1 (hε sg)).2]
      rw [← mul_add, Real.log_le_iff_le_exp hpos, Real.exp_nat_mul] at hlog
      rw [hpt z hz sg hsg, mul_pow]
      exact mul_le_mul_of_nonneg_right hlog (pow_nonneg hAz.le τ)
    · exact isCoboundedUnder_le_of_le atTop (fun k => div_nonneg (Real.log_natCast_nonneg _) (hden k))
    · refine isBoundedUnder_of_eventually_le (a := |C'| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ))
        (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hkp : (0 : ℝ) < (k : ℝ) ^ (D + 1) := by positivity
      rw [div_le_iff₀ (by positivity)]
      have h2 : C' * ((k : ℝ) + 1) ^ (D + 1) ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) :=
        calc C' * ((k : ℝ) + 1) ^ (D + 1) ≤ |C'| * ((k : ℝ) + 1) ^ (D + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity)
          _ ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C')
      calc smallSectionCount (IsSmallH (mCoordIdeal y) y A') (chartLatNm y A'.a) k
          ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) := (hC' k).trans h2
        _ = |C'| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
              ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
            rw [mul_pow]; field_simp

  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hδ0 : 0 < η / (|c| + 1) := by positivity
  have hcη : c * (η / (|c| + 1)) < η := by
    calc c * (η / (|c| + 1)) ≤ |c| * (η / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hδ0.le
      _ < (|c| + 1) * (η / (|c| + 1)) := mul_lt_mul_of_pos_right (by linarith) hδ0
      _ = η := by field_simp
  linarith [hδ _ hδ0]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenTwistGenerated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (m n : ℕ),
    KH.GeneratedV S V α → KH.GeneratedV S V ((m : ℤ) • α + fun _ => (n : ℤ))

def GenTwistVanish.Statement : Prop :=
  ∀ (S : Type) [Field S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α →
    ∀ e : K → ℤ, ∃ c₀ : ℕ, ∀ m n : ℕ, c₀ ≤ n →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + (m : ℤ) • α + fun _ => (n : ℤ)) 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResNullForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def AnResNullForm.Statement : Prop :=
  ∀ (e : ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι))
    (R : AnRes P J e) (G : MRing ι) (dG : K → ℕ),
    IsArithVar P (e + 1) → IsMultiHomog G dG → G ∉ P →
      ∀ j, volume ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' {a | eval (R.lift a a) (map (Int.castRingHom ℂ) G) = 0}) = 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def BergmanDensIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), Integrable (bergmanDens W dV) dV.μ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

