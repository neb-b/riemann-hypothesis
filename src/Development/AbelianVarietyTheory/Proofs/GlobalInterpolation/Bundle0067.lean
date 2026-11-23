module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayCountThetaFibreCount
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConvRealChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralOfMemRayI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Bundle0001
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRay
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

section

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

theorem aRay_norm_zero (g : D.G) : aRay D g 0 = 0 := by
  have : idealsIn D g 0 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, -, h2, -⟩
    exact h1 (Ideal.absNorm_eq_zero_iff.1 h2)
  simp [aRay, this]

theorem aRay_one_norm_one : aRay D 1 1 = 1 := by
  have : idealsIn D 1 1 = {⊤} := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, -, h2, -⟩
      exact Ideal.absNorm_eq_one_iff.1 h2
    · rintro rfl
      refine ⟨top_ne_bot, ?_, Ideal.absNorm_eq_one_iff.2 rfl, D.cls_top⟩
      rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  simp [aRay, this]

theorem aRay_norm_one_of_ne {g : D.G} (hg : g ≠ 1) : aRay D g 1 = 0 := by
  have : idealsIn D g 1 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, h2, h3⟩
    rw [Ideal.absNorm_eq_one_iff.1 h2, D.cls_top] at h3
    exact hg h3.symm
  simp [aRay, this]

theorem card_ray_le (hK : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    (Fintype.card D.G : ℝ) ≤ 4 * |(discr K : ℝ)| * (M : ℝ) ^ 2 := by
  have h1 := RayData.card_eq_rayNo K M hM D
  have h2 := (RayNo.rayNo_bounds K (Ideal.span {(M : 𝓞 K)})
    (by simpa [Ideal.span_singleton_eq_bot] using hM)).2.1
  have h3 : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton, show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) M by simp, Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK]
    simp [Int.natAbs_pow]
  have h4 : (classNumber K : ℝ) ≤ 4 * |(discr K : ℝ)| := by
    exact_mod_cast GlobalTheory.classNumber_le_four_mul_abs_discr K hK
  rw [h3, ← h1] at h2
  have h5 : (Fintype.card D.G : ℝ) ≤ (classNumber K : ℝ) * (M : ℝ) ^ 2 := by exact_mod_cast h2
  exact h5.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

end

theorem addChar_eq_one_or_neg_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    rw [← AddChar.mul_apply, h, AddChar.one_apply]
  exact mul_self_eq_one_iff.1 this

theorem exists_lFam_ray : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧
    ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro d M hd hd4 hd100 hM
  obtain ⟨K, _, _, ω, -, hK, hdisc, hω, -, -⟩ := GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hd hd4
  have hx : (((2 * ω - 1 : 𝓞 K) : K)) ^ 2 = -(d : K) := by
    have := congrArg (algebraMap (𝓞 K) K) hω
    simpa using this
  have hM0 : M ≠ 0 := by omega
  let D : RayData K M := rayData K M hM0
  have hc := GlobalTheory.Hk.rayCountTheta K d M _ hd hd4 hd100 hx hK hM D
  have hl := GlobalTheory.Hk.LamRay.lamRay_props K d M _ hd hd4 hd100 hx hK hM D
  have hcard := card_ray_le D hK hM0
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hs : (10 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith)
  have hsd : Real.sqrt d ≤ d := by nlinarith
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rw [hdisc] at hcard
  have habs : |(((-(d : ℤ) : ℤ)) : ℝ)| = d := by
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]
  rw [habs] at hcard
  refine ⟨{
    G := Additive D.G
    ft := D.fin
    B := 4 * (d : ℝ) * (M : ℝ) ^ 2
    κ := 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2)
    a := fun g n => aRay D g.toMul n
    lam := fun g n => lamRay D g.toMul n
    B_ge := by nlinarith
    card_le := hcard
    κ_ge := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : Real.sqrt d * (M : ℝ) ^ 2 ≤ d * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsd (by positivity)
      have h2 : (0 : ℝ) ≤ d * (M : ℝ) ^ 2 := by positivity
      nlinarith
    κ_le := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    a_nonneg := fun g n => Nat.cast_nonneg _
    a_zero := fun g => aRay_norm_zero D _
    a_one := aRay_one_norm_one D
    a_one_ne := fun g hg => aRay_norm_one_of_ne D hg
    count := fun g => (hc g.toMul).1
    theta := fun g => (hc g.toMul).2
    lam_nonneg := fun g n => hl.1 _ n
    lam_le := hl.2.1
    conv := fun g n => GlobalTheory.Hk.aRay_mul_log K M (by omega) D g.toMul n
    sq := fun χ hχ n => GlobalTheory.Hk.RaySq.conv_real_char K M (by omega) D (fun g => (χ (Additive.ofMul g)).re) (by simp) ?_ ?_ n }, rfl, hl.2.2⟩
  · intro g h
    rw [ofMul_mul, AddChar.map_add_eq_mul]
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]
  · intro g
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_even_between (A : ℝ) (hA : 2 ≤ A) : ∃ m : ℕ, Even m ∧ A ≤ m ∧ (m : ℝ) ≤ 2 * A := by
  refine ⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩
  · have := Nat.le_ceil (A / 2)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (a := A / 2) (by linarith)
    push_cast; linarith

theorem exists_ranks_of_frame (φ : Formalism.HC.Frame) (k m T W : ℕ) (hk : Even k) (hm : Even m) (h2 : 2 ≤ m) (h3 : m + 3 ≤ k)
    (hmf : m ≤ 2 * φ.ord) (hfk : 2 * φ.ord ≤ k) :
    ∃ R : Ranks, R.toFrame = φ ∧ R.k = k ∧ R.m = m ∧ R.r + R.t = 8 * R.f * R.r + 4 + T * (8 * W) := by
  obtain ⟨r, hr⟩ : ∃ r, r = k + m - 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = 2 * φ.ord := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = f * r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = T * W := ⟨_, rfl⟩
  have hpr : r ≤ p := by
    rw [hp]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hmt : m ≤ 8 * p + 4 + 8 * q - r + 1 := by omega
  refine ⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · rw [Nat.odd_iff]; omega
  · rw [sq]
    exact (Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)
  · show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)
    rw [← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]
    omega

theorem exists_ranks_rankVal_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∀ φ : Formalism.HC.Frame, s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
      ∃ R : Ranks, R.toFrame = φ ∧ RankVal s R := by
  intro eps h0 h1
  refine ⟨16, fun s hs hx φ he1 hp2 => ?_⟩
  subst hs
  have hx1 : (1 : ℝ) ≤ s.x := by linarith
  have hx0 : (0 : ℝ) < s.x := by linarith
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3 := by linarith
  have hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hA1 : 2 ≤ Real.sqrt (s.x * s.delta1) := by
    apply Real.le_sqrt_of_sq_le
    rw [hd]
    have h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
    rw [Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have p2 : 16 * s.x ≤ s.x ^ 2 := by nlinarith
  have p3 : 16 * s.x ^ 2 ≤ s.x ^ 3 := by nlinarith
  have p4 : 16 * s.x ^ 3 ≤ s.x ^ 4 := by nlinarith
  obtain ⟨m, hm, hm1, hm2⟩ := exists_even_between _ hA1
  obtain ⟨k, hk, hk1, hk2⟩ := exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)
  have a1 : 2 ≤ m := by
    have : ((2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m + 3 ≤ k := by
    have : (m : ℝ) + 3 ≤ k := by linarith
    exact_mod_cast this
  have a3 : m ≤ 2 * φ.ord := by
    have : (m : ℝ) ≤ 2 * (φ.ord : ℝ) := by linarith
    exact_mod_cast this
  have a4 : 2 * φ.ord ≤ k := by
    have : 2 * (φ.ord : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨R, rfl, rfl, rfl, hR⟩ := exists_ranks_of_frame φ k m (TOv s)
    ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) +
      ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4
  exact ⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmulMemOfMemLocW
section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem exists_smul_mem_of_mem_locW (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : x ∈ locW D.what₂.places w L) : ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧ d • x ∈ L := by
  have h1 : (1 : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal :=
    fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  unfold locW at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by simpa using hy⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hy⟩ := hy
    obtain ⟨e, he, hz⟩ := hz
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hy
    · rw [mul_smul]; exact L.smul_mem _ hz
  | smul r y _ hy =>
    obtain ⟨d, hd, hy⟩ := hy
    have hr : (D.plEq w).valuation D.what₂.LL (r : D.what₂.LL) ≤ 1 := (D.val_nonneg_iff w r).1 r.2
    obtain ⟨n, e, hne⟩ := (D.plEq w).exists_primeCompl_mul_eq_of_integer (r : D.what₂.LL) hr
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd e.2, ?_⟩
    have : (d * (e : 𝓞 D.what₂.LL)) • r • y = n • d • y := by
      rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL (d * (e : 𝓞 D.what₂.LL)), ← algebraMap_smul D.what₂.LL n,
        ← algebraMap_smul D.what₂.LL d y, smul_smul, smul_smul, ← hne, map_mul]
      congr 1; ring
    rw [this]; exact L.smul_mem _ hy

theorem mem_of_forall_locW (D : D7) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : ∀ w, x ∈ locW D.what₂.places w L) : x ∈ L := by
  let I : Ideal (𝓞 D.what₂.LL) := L.comap (LinearMap.toSpanSingleton (𝓞 D.what₂.LL) V x)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_locW D (D.plEq.symm v) L (hx _)
    rw [Equiv.apply_symm_apply] at hd
    exact hd (hIM (show d ∈ I from hdx))
  have h1 : (1 : 𝓞 D.what₂.LL) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

end GlobalTheory.LvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSplittingOfCharacter
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OverSplit

theorem ker_isMaximal {A : Type} [CommRing A] {T : ℕ} [Fact T.Prime] (ψ : A →+* ZMod T) :
    (RingHom.ker ψ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ψ (ZMod.ringHom_surjective ψ)

theorem exists_roots {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {T : ℕ} [Fact T.Prime] (ψ : O →+* ZMod T)
    (p n : O) (x y : ZMod T) (hp : ψ p = x + y) (hn : ψ n = x * y) (hxy : x ≠ y) :
    ∃ r r' : O, r + r' = p ∧ r * r' = n ∧ ψ r = x ∧ ψ r' = y ∧ IsUnit (r - r') := by
  have hk : ∀ z, z ∈ IsLocalRing.maximalIdeal O ↔ ψ z = 0 := fun z => by
    rw [← IsLocalRing.eq_maximalIdeal (ker_isMaximal ψ), RingHom.mem_ker]
  have hu : ∀ z, ψ z ≠ 0 → IsUnit z := fun z hz => by
    by_contra h
    exact hz ((hk z).1 h)
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective ψ x
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  obtain ⟨r, hr, hra⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O)
    (Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X + Polynomial.C n) (by monicity!) a
    (by rw [hk]; simp [ha, hp, hn]; ring)
    (by
      refine IsUnit.map _ (hu _ ?_)
      have : ψ (Polynomial.eval a (Polynomial.derivative
          (Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X + Polynomial.C n))) = x - y := by
        simp [ha, hp]; ring
      rwa [this])
  have hrx : ψ r = x := by
    rw [hk, map_sub, ha, sub_eq_zero] at hra; exact hra
  have hr' : r ^ 2 - p * r + n = 0 := by simpa using hr
  have hry : ψ (p - r) = y := by rw [map_sub, hp, hrx]; ring
  refine ⟨r, p - r, by ring, by linear_combination -hr', hrx, hry, hu _ ?_⟩
  rwa [map_sub, hrx, hry]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def inclO (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F →+* intV E v :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)).toRingHom.comp
      (v.adicCompletionIntegers F).subtype) _
    fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)

theorem coe_inclO (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletionIntegers F) :
    ((inclO E v a : intV E v) : E ⊗[F] v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] (a : v.adicCompletion F) := rfl

theorem exists_inclO_eq (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 E)
    (hx : (x : E) ∈ (algebraMap F E).range) :
    ∃ p : v.adicCompletionIntegers F, inclO E v p = GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v x := by
  obtain ⟨b, hb⟩ := hx
  have hi : IsIntegral ℤ b := by
    rw [← isIntegral_algebraMap_iff (B := E) , hb]
    exact x.isIntegral_coe
  let b' : 𝓞 F := ⟨b, hi⟩
  have hx' : x = algebraMap (𝓞 F) (𝓞 E) b' := by
    apply Subtype.ext
    exact hb.symm
  refine ⟨algebraMap (𝓞 F) _ b', Subtype.ext ?_⟩
  rw [coe_inclO, GlobalTheory.OverCompare.coe_toIntV, hx', GlobalTheory.OverCompare.tmul_algebraMap]
  rfl

end GlobalTheory.OverSplit


open GlobalTheory.OverSplit in
theorem GlobalTheory.OverSplit.exists_splitting_of_character :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) → ∀ (v : HeightOneSpectrum (𝓞 F)) (T : ℕ), T.Prime → ∀ χ : intV E v →+* ZMod T, ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, IsSplitting σ v s ∧ ∀ a : intV E v, Valued.v (prP s a) < 1 → χ a = 0 := by
  intro F E _ _ _ _ _ σ hdeg hσ hfix hunr v T hT χ
  have : Fact T.Prime := ⟨hT⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set ι := GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v with hι
  obtain ⟨θ, t, ht, hθt⟩ := hunr _ (ker_isMaximal (χ.comp ι))
  have hxy : χ (ι θ) ≠ χ (ι t) := by
    intro h
    apply hθt
    rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, RingHom.comp_apply, h, sub_self]
  have e1 : ((θ + t : 𝓞 E) : E) = θ + σ θ := by rw [← ht]; rfl
  have e2 : ((θ * t : 𝓞 E) : E) = θ * σ θ := by rw [← ht]; rfl
  obtain ⟨p, hp⟩ := exists_inclO_eq v (θ + t) (hfix _ (by rw [e1, map_add (f := _), hσ, add_comm]))
  obtain ⟨n, hn⟩ := exists_inclO_eq v (θ * t) (hfix _ (by rw [e2, map_mul, hσ, mul_comm]))
  obtain ⟨r, r', hs, hm, hr, hr', hu⟩ := exists_roots (χ.comp (inclO E v)) p n (χ (ι θ)) (χ (ι t))
    (by rw [RingHom.comp_apply, hp, map_add (f := _), map_add (f := _)])
    (by rw [RingHom.comp_apply, hn, map_mul, map_mul]) hxy
  obtain ⟨s, hsp, hsθ⟩ := GlobalTheory.RootSplitting.exists_isSplitting F E σ hdeg hσ hfix v θ r r' θ.isIntegral_coe hu
    (by
      have := congrArg Subtype.val hp
      rw [← e1]
      refine this.symm.trans ?_
      rw [← hs]; rfl)
    (by
      have := congrArg Subtype.val hn
      rw [← e2]
      refine this.symm.trans ?_
      rw [← hm]; rfl)
  refine ⟨s, hsp, fun a ha => ?_⟩
  let a₁ : v.adicCompletionIntegers F := ⟨(s a).1, ((hsp.2.2 a).1 a.2).1⟩
  have ha₁ : χ (inclO E v a₁) = 0 := by
    have h1 : a₁ ∈ IsLocalRing.maximalIdeal _ :=
      (ValuationSubring.valuation_lt_one_iff _ _).2
        ((Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.1 ha)
    rw [← IsLocalRing.eq_maximalIdeal (ker_isMaximal (χ.comp (inclO E v)))] at h1
    exact h1
  have key : (ι θ - inclO E v r') * a = (ι θ - inclO E v r') * inclO E v a₁ := by
    apply Subtype.ext
    apply s.injective
    have h0 : s ((ι θ - inclO E v r' : intV E v) : E ⊗[F] v.adicCompletion F) =
        ((r : v.adicCompletion F) - r', 0) := by
      rw [AddSubgroupClass.coe_sub, map_sub, coe_inclO, hsp.1, hι, GlobalTheory.OverCompare.coe_toIntV, hsθ]
      simp
    rw [Subring.coe_mul, Subring.coe_mul, map_mul, map_mul, h0, coe_inclO, hsp.1]
    ext <;> simp [a₁]
  have := congrArg χ key
  rw [map_mul, map_mul, ha₁, mul_zero, map_sub] at this
  have hr'' : χ (inclO E v r') = χ (ι t) := hr'
  rw [hr''] at this
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hxy)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsOpenOhat
section
open NumberField IsDedekindDomain Matrix Topology

namespace GlobalTheory.CuspNF.KprOpen

theorem mem_map_ker {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n] (S : Subring A) (m : S) (g : GL n A)
    (h1 : ∀ i j, (g : Matrix n n A) i j ∈ S) (h2 : ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S)
    (h3 : ∀ i j, ∃ y ∈ S, y * (m : A) = (g : Matrix n n A) i j - (1 : Matrix n n A) i j) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {m}))).ker.map
      (Matrix.GeneralLinearGroup.map S.subtype) := by
  let P : Matrix n n S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix n n S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hinj : Function.Injective (S.subtype.mapMatrix : Matrix n n S →+* Matrix n n A) := fun x y h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hP : S.subtype.mapMatrix P = (g : Matrix n n A) := rfl
  have hQ : S.subtype.mapMatrix Q = ((g⁻¹ : GL n A) : Matrix n n A) := rfl
  let u : GL n S := ⟨P, Q, hinj (by rw [map_mul, hP, hQ, map_one, Units.mul_inv]),
    hinj (by rw [map_mul, hP, hQ, map_one, Units.inv_mul])⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  refine Units.ext ?_
  ext i j
  obtain ⟨y, hy, e⟩ := h3 i j
  have key : Ideal.Quotient.mk (Ideal.span {m}) (P i j) = Ideal.Quotient.mk (Ideal.span {m}) ((1 : Matrix n n S) i j) := by
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    change y * (m : A) = (g : Matrix n n A) i j - _
    rw [e]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Ideal.Quotient.mk (Ideal.span {m}) (P i j) = (1 : Matrix n n _) i j
  rw [key]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end GlobalTheory.CuspNF.KprOpen
end

