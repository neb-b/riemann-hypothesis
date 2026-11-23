module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Asm

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Gen

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem cJ_le (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : cJ h X L 𝔭 ≤ finrank K X := by
  unfold cJ
  by_cases hS : ∃ b a, IsJordanIn h X L 𝔭 b a
  · obtain ⟨b, a, hJ⟩ := hS
    refine (Nat.sInf_le (show cJof 𝔭 a ∈ {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} from
      ⟨b, a, hJ, rfl⟩)).trans ?_
    unfold cJof
    exact (Finset.card_filter_le _ _).trans (by simp)
  · have he : {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨b, a, hJ, -⟩
      exact hS ⟨b, a, hJ⟩
    rw [he, Nat.sInf_empty]
    exact Nat.zero_le _

theorem integral_of_unimod {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : Submodule (𝓞 K) V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h Λ) : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ := by
  intro x hx y hy
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual h Λ := by rw [hU]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx

theorem glueSet_eq_empty {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : ¬ Formalism.HermitianLatticesTheory.IsIntegralLat h M) : GlueSet h U M = ∅ := by
  ext Λ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hU, hΛ⟩
  apply hM
  intro x hx y hy
  rw [← hΛ] at hx hy
  exact integral_of_unimod hU x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).1

theorem isGlueReps_empty {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hE : GlueSet h U M = ∅) : IsGlueReps h U M ∅ := by
  refine ⟨fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ), fun Λ hΛ => ?_,
    fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ)⟩
  rw [hE] at hΛ
  exact absurd hΛ (Set.notMem_empty Λ)

end Gen

section Mass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cOne_spec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    0 < cOne K F ∧ MassConst K F 1 (cOne K F) := by
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have he : Finset.Icc 2 1 = ∅ := Finset.Icc_eq_empty (by norm_num)
  have h1 := hall 1 le_rfl
  rw [he, Finset.prod_empty, mul_one] at h1
  have hex : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := ⟨c₁, hc₁, h1⟩
  unfold cOne
  rw [dite_eq_left hex]
  exact hex.choose_spec

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cMass_spec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∀ m : ℕ, 1 ≤ m → 0 < cMass K F m ∧ MassConst K F m (cMass K F m) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have he : Finset.Icc 2 (0 + 1) = ∅ := Finset.Icc_eq_empty (by norm_num)
      unfold cMass
      rw [he, Finset.prod_empty, mul_one]
      exact cOne_spec hK hF
    · obtain ⟨h0, hc⟩ := ih hpos
      have hstep := massConst_succ hermRepUnram liStat hK hF (m := m + 1) (by omega) h0
        (by simpa using hc)
      have hr := massRatio_pos hK (m + 1) (by omega)
      have heq : cMass K F (m + 1) = cMass K F m * Formalism.HermitianLatticesTheory.massRatioRightSide K (m + 1) := by
        unfold cMass
        rw [Finset.prod_Icc_succ_top (by omega), mul_assoc]
      rw [heq]
      exact ⟨mul_pos h0 hr, hstep⟩

theorem hasProd_lF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (i : ℕ) (hi : 2 ≤ i) :
    HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
      (1 - etaF K F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹) (lValEtaF K F i) := by
  let π := fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
    (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
      {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
  have hf := multipliable_eulerFac hK i hi
  have h1 : HasProd (fun p : (Σ b, {x // π x = b}) =>
      Formalism.HermitianLatticesTheory.eulerFac K i (Equiv.sigmaFiberEquiv π p).1) (Formalism.HermitianLatticesTheory.lValEta K i) :=
    (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  have h2 := HasProd.sigma h1 (Regroup.hasProd_fibre hK hF i (by omega))
  rw [← lValEta_eq_lValEtaF hK hF i hi]
  exact h2

theorem alpha_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k r : ℕ} (hk : 1 ≤ k) (hkr : k - 1 ≤ r) :
    alphaStd K 𝔭 (k - 1) = alphaStd K 𝔭 r *
      ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))⁻¹ := by
  have hsplit : alphaStd K 𝔭 r = alphaStd K 𝔭 (k - 1) *
      ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
    unfold alphaStd
    rw [← Finset.prod_union]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_Icc] at hi hi'
      omega
  have hpos := alphaStd_pos hK hF h𝔭 r
  have hne : (∏ i ∈ Finset.Icc k r,
      (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))) ≠ 0 := by
    intro h0
    rw [hsplit, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [hsplit, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hne, mul_one]

def plEquiv : IsDedekindDomain.HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} where
  toFun P := ⟨P.asIdeal, P.isMaximal⟩
  invFun 𝔭 := ⟨𝔭.1, 𝔭.2.isPrime, fun h =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h ▸ 𝔭.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Mass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.SG.Pf.Asm

namespace Formalism.L2.SG.Pf

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CuspDecayShortRowColumn
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_over (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  refine Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 ?_
  intro t ht
  rw [RingHom.mem_ker] at ht
  have h1 : algebraMap F K (t : F) = 0 := by
    have h2 := congrArg (algebraMap (𝓞 K) K) ht
    rw [map_zero] at h2
    exact h2
  have h3 : (t : F) = 0 := (algebraMap F K).injective (by rw [h1, map_zero])
  have h4 : t = 0 := by exact_mod_cast h3
  rw [h4]
  exact 𝔭.zero_mem

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem spanS_le_of {S : Subring K} {n : ℕ} {x : Fin n → V} {X : Submodule K V} (hx : ∀ i, x i ∈ X) :
    ∀ v ∈ spanS S x, v ∈ X := fun v hv =>
  spanS_induction (p := fun v => v ∈ X) X.zero_mem (fun a b ha hb => X.add_mem ha hb)
    (fun c _ a ha => X.smul_mem c ha) hx v hv

theorem jordan_exists (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (X : Submodule K V) (L : Submodule (𝓞 K) V) (hnd : Cnt.NondegOn h X)
    (hL : Cnt.IsLatIn X L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) : ∃ b a, Cnt.IsJordanIn h X L 𝔭 b a := by
  have inj := IsFractionRing.injective (𝓞 K) K
  have hcomp : ∀ t : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) :=
    fun t => rfl
  have hconj_conj : ∀ a : 𝓞 K, conjO K (conjO K a) = a := fun a =>
    inj (by rw [algebraMap_conjO, algebraMap_conjO, star_star])
  obtain ⟨P, hP, rfl⟩ := exists_over (K := K) 𝔭 h𝔭
  obtain ⟨π, hπ, hfin⟩ := exists_unif_fin hF hP
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨x, hxL, hli, hsp, hloc⟩ := exists_basis_in hL h𝔭
  have hdet0 : (U0.gram h x).det ≠ 0 := det_gram_ne_zero hnd hli hsp
  obtain ⟨N, hN⟩ := hfin _ hdet0
  have hint : ∀ r : 𝓞 K, algebraMap (𝓞 K) K r ∈ locRing P := by
    intro r
    change _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
  have hxS : ∀ i j, h (x i) (x j) ∈ locRing P := by
    intro i j
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hLi _ (hxL i) _ (hxL j))
    rw [← hr]
    exact hint r
  obtain ⟨y, hyo, hys⟩ := exists_orth_gen hS hπ _ N h hs x hxS hN
  have hxy : ∀ i, x i ∈ spanS (locRing P) y := fun i => by rw [hys]; exact mem_spanS x i
  obtain ⟨c, -, hc⟩ := gram_det_of_le (h := h) hS hxy
  have hdety : (U0.gram h y).det ≠ 0 := fun h0 => hdet0 (by rw [hc, h0, mul_zero])
  have hdiag : U0.gram h y = Matrix.diagonal (fun i => h (y i) (y i)) := by
    ext i j
    show h (y i) (y j) = Matrix.diagonal (fun i => h (y i) (y i)) i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hyo i j hij
  have hyy : ∀ i, h (y i) (y i) ≠ 0 := by
    rw [hdiag, Matrix.det_diagonal] at hdety
    exact fun i => Finset.prod_ne_zero_iff.mp hdety i (Finset.mem_univ i)

  have hgen : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, ∃ w : 𝓞 K, ∃ t : 𝓞 F,
      t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ w * s = algebraMap (𝓞 F) (𝓞 K) t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      have hfix : conjO K (conjO K s * s) = conjO K s * s := by
        rw [map_mul, hconj_conj, mul_comm]
      obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF _).mp hfix
      refine ⟨conjO K s, t, ?_, ht.symm⟩
      show algebraMap (𝓞 F) (𝓞 K) t ∉ P
      rw [ht]
      intro h0
      rcases hP.isPrime.mem_or_mem h0 with h1 | h1
      · exact hs.2 (conjO K s) (algebraMap_conjO s) h1
      · exact hs.1 h1
    | one =>
      refine ⟨1, 1, ?_, by rw [one_mul, map_one]⟩
      show algebraMap (𝓞 F) (𝓞 K) 1 ∉ P
      rw [map_one]
      exact fun h0 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h0)
    | mul x y _ _ hx hy =>
      obtain ⟨wx, tx, htx, hx⟩ := hx
      obtain ⟨wy, ty, hty, hy⟩ := hy
      refine ⟨wx * wy, tx * ty, ?_, ?_⟩
      · show algebraMap (𝓞 F) (𝓞 K) (tx * ty) ∉ P
        rw [map_mul]
        exact fun h0 => (hP.isPrime.mem_or_mem h0).elim htx hty
      · rw [map_mul, ← hx, ← hy]
        ring
  have hclaim : ∀ c ∈ locRing P, star c = c → ∃ t : 𝓞 F, t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧
      ∃ a : 𝓞 F, algebraMap F K (a : F) = (algebraMap F K (t : F)) ^ 2 * c := by
    intro c hc hcs
    obtain ⟨s, hs, hsc⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P c).mp hc
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hsc
    obtain ⟨w, t, ht, hwt⟩ := hgen s hs
    have e1 : algebraMap F K (t : F) * c = algebraMap (𝓞 K) K (w * r) := by
      rw [← hcomp, ← hwt, map_mul, map_mul, hr, mul_assoc]
    have hfixt : star (algebraMap F K (t : F)) = algebraMap F K (t : F) := (hF _).mpr ⟨_, rfl⟩
    have hfix : conjO K (w * r) = w * r :=
      inj (by rw [algebraMap_conjO, ← e1, star_mul', hfixt, hcs])
    obtain ⟨a0, ha0⟩ := (conjO_eq_iff_mem_range hF _).mp hfix
    refine ⟨t, ht, t * a0, ?_⟩
    have e2 : algebraMap F K (a0 : F) = algebraMap F K (t : F) * c := by
      rw [← hcomp, ha0, ← e1]
    show algebraMap F K ((t : F) * (a0 : F)) = _
    rw [map_mul, e2]
    ring
  have hyS : ∀ i, h (y i) (y i) ∈ locRing P := fun i =>
    int_spanS hS hxS (y i) (by rw [← hys]; exact mem_spanS y i) (y i)
      (by rw [← hys]; exact mem_spanS y i)
  have hyfix : ∀ i, star (h (y i) (y i)) = h (y i) (y i) := fun i => hs.eq (y i) (y i)
  choose t ht a ha using fun i => hclaim _ (hyS i) (hyfix i)
  have hτ0 : ∀ i, algebraMap F K (t i : F) ≠ 0 := by
    intro i h0
    apply ht i
    have h1 : (t i : F) = 0 := (algebraMap F K).injective (by rw [h0, map_zero])
    have h2 : t i = 0 := by exact_mod_cast h1
    rw [h2]
    exact Submodule.zero_mem _
  have hτfix : ∀ i, star (algebraMap F K (t i : F)) = algebraMap F K (t i : F) :=
    fun i => (hF _).mpr ⟨_, rfl⟩
  have hτS : ∀ i, algebraMap F K (t i : F) ∈ locRing P := fun i => by
    rw [← hcomp]
    exact hint _
  have hτinv : ∀ i, (algebraMap F K (t i : F))⁻¹ ∈ locRing P := by
    intro i
    change _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    refine ⟨algebraMap (𝓞 F) (𝓞 K) (t i), Submonoid.subset_closure ⟨ht i, fun t' ht' => ?_⟩,
      Submodule.mem_one.mpr ⟨1, ?_⟩⟩
    · have e : t' = algebraMap (𝓞 F) (𝓞 K) (t i) := inj (by rw [ht', hcomp, hτfix])
      rw [e]
      exact ht i
    · rw [map_one, hcomp, mul_inv_cancel₀ (hτ0 i)]
  obtain ⟨b, hb⟩ : ∃ b : Fin (finrank K X) → V, ∀ i, b i = algebraMap F K (t i : F) • y i :=
    ⟨_, fun _ => rfl⟩
  have hyX : ∀ i, y i ∈ X := fun i => spanS_le_of (S := locRing P) (x := x)
    (fun j => by rw [← hsp]; exact Submodule.subset_span ⟨j, rfl⟩) (y i)
    (by rw [← hys]; exact mem_spanS y i)
  have hbS : spanS (locRing P) b = spanS (locRing P) y := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hb i]
      exact smul_mem_spanS (hτS i) (mem_spanS y i)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [show y i = (algebraMap F K (t i : F))⁻¹ • b i by rw [hb i, inv_smul_smul₀ (hτ0 i)]]
      exact smul_mem_spanS (hτinv i) (mem_spanS b i)
  refine ⟨b, a, fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hb i]
    exact X.smul_mem _ (hyX i)
  · rw [← hloc]
    ext v
    rw [mem_locF_span_iff hK hF hP b v, mem_locF_span_iff hK hF hP x v, hbS, hys]
  · rw [hb i, hb j]
    simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, hyo i j hij, smul_zero]
  · rw [hb i, ha i, map_smulₛₗ h, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, hτfix]
    ring
  · intro h0
    have h1 := ha i
    rw [h0] at h1
    have h2 : (algebraMap F K (t i : F)) ^ 2 * h (y i) (y i) = 0 := by
      rw [← h1]
      simp
    exact mul_ne_zero (pow_ne_zero 2 (hτ0 i)) (hyy i) h2

end Formalism.L2.SG.Pf.G1
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def skSet (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Set (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
  {X | Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a}

def udPre (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) : Type :=
  {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) //
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) ∧
    ∃ W, Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a}

def udSetoid (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Setoid (udPre K 𝔭 k a) where
  r Y Y' := ∃ Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Y.1 - Y'.1 = Z * diagQ K 𝔭 k a
  iseqv := {
    refl := fun Y => ⟨0, by simp⟩
    symm := fun ⟨Z, hZ⟩ => ⟨-Z, by rw [Matrix.neg_mul, ← hZ, neg_sub]⟩
    trans := fun ⟨Z, hZ⟩ ⟨Z', hZ'⟩ => ⟨Z + Z', by rw [Matrix.add_mul, ← hZ, ← hZ', sub_add_sub_cancel]⟩ }

def udQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) : Type :=
  Quotient (udSetoid K 𝔭 k a)

def UDModel : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → discAut h ⊤ L 𝔭 = Nat.card (udQ K 𝔭 k a)

def OrbitCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k →
      Nat.card (skSet K 𝔭 k a) = Nat.card (udQ K 𝔭 k a) * Nat.card (kerSet K 𝔭 k a)

section

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem linearIndependent_of_jordan {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) :
    LinearIndependent K b := by
  obtain ⟨-, -, horth, hdiag, hne⟩ := hb
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : h (b i) (∑ j ∈ s, g j • b j) = 0 := by rw [hg, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul, hdiag] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (by simpa using h2) (hne i)
  · intro j _ hji
    rw [map_smul, horth i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

variable [Fact (IsFixF K F)]

theorem akCount_eq_skSet {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card (skSet K 𝔭 k a) := by
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hB : ⇑(Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm)) = b :=
    Basis.coe_mk _ _
  have hH : ∀ i j, algebraMap (𝓞 K) K
      ((Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)) i j) =
      h (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) i)
        (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) j) := by
    intro i j
    rw [hB]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hb.2.2.2.1 i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero]
      exact (hb.2.2.1 i j hij).symm
  rw [integralBasisSpans.akCount_eq h h𝔭 _ (by
    have h2 := hb.2.1
    rw [← hB] at h2
    exact h2) hH k]
  have hd : (Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)).map
      (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = diagQ K 𝔭 k a := by
    rw [diagQ, Matrix.diagonal_map (map_zero _)]
  rw [hd]
  rfl

end

theorem discOnto_of (hU : UDModel) (hO : OrbitCount) : DiscOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk
  have ha : ∀ i, a i ≠ 0 := by
    obtain ⟨-, -, -, -, h5⟩ := hb
    exact h5
  rw [akCount_eq_skSet h𝔭 hb k, hO K F hK 𝔭 h𝔭 _ a ha k hk,
    hU K F V hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk]

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

