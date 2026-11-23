module

public import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.FrameCodeOfAdditive
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsF
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0005
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0007
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo
public import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
section
section Commens

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem mem_of_locally (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ v.asIdeal ∧ s • x ∈ M) : x ∈ M := by
  let I : Ideal (𝓞 K) := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : ∀ a : 𝓞 K, a ∈ I ↔ a • x ∈ M := fun a => Iff.rfl
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
    exact hs (hle ((hI s).2 hsx))
  have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; trivial
  have h2 := (hI 1).1 h1
  rwa [one_smul] at h2

theorem exists_common_mul (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (h : ∀ y ∈ M, ∃ s : 𝓞 K, s ≠ 0 ∧ s • y ∈ N) : ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  have hSM : ∀ y ∈ S, y ∈ M := fun y hy => by rw [← hS]; exact Submodule.subset_span hy
  let f : V → 𝓞 K := fun y => if hy : y ∈ M then (h y hy).choose else 1
  have hf0 : ∀ y, f y ≠ 0 := by
    intro y
    by_cases hy : y ∈ M
    · simp only [f, dif_pos hy]; exact (h y hy).choose_spec.1
    · simp only [f, dif_neg hy]; exact one_ne_zero
  have hfN : ∀ y ∈ M, f y • y ∈ N := by
    intro y hy
    simp only [f, dif_pos hy]; exact (h y hy).choose_spec.2
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), ?_⟩
  have hle : Submodule.span (𝓞 K) (S : Set V) ≤ N.comap (LinearMap.lsmul (𝓞 K) V (∏ y ∈ S, f y)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hy
    show (∏ y ∈ S, f y) • y ∈ N
    rw [hk, mul_comm, mul_smul]
    exact N.smul_mem _ (hfN y (hSM y hy))
  intro y hy
  rw [← hS] at hy
  exact hle hy

end General

theorem locLe_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {w : HeightOneSpectrum (𝓞 K)} {A B : Submodule (𝓞 K) V} (h : DV.LocLe w 0 A B) :
    ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ B := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := h x hx
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hsx
  exact ⟨s, hs, hsx⟩

theorem place_over' (D : D7) (p : ℕ) (hp : p.Prime) : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP, hlo⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.what₂.LL)))
  have hpP : ((p : ℕ) : 𝓞 D.what₂.LL) ∈ P := by
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hlo.over, Ideal.mem_comap] at h1
    simpa using h1
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  refine ⟨D.plEq.symm ⟨P, hP, hne⟩, ?_⟩
  set w := D.plEq.symm ⟨P, hP, hne⟩ with hw
  have hr := J.resChar_mem D w
  rw [hw, Equiv.apply_symm_apply] at hr
  rw [← hw] at hr
  by_contra hcon
  have hco : Nat.Coprime (D.what₂.places.resChar w) p :=
    (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).2 hcon
  have hb := Nat.gcd_eq_gcd_ab (D.what₂.places.resChar w) p
  rw [hco] at hb
  have h1 : (1 : 𝓞 D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) *
      ((Nat.gcdA (D.what₂.places.resChar w) p : ℤ) : 𝓞 D.what₂.LL) +
      ((p : ℕ) : 𝓞 D.what₂.LL) * ((Nat.gcdB (D.what₂.places.resChar w) p : ℤ) : 𝓞 D.what₂.LL) := by
    have := congrArg (fun z : ℤ => (z : 𝓞 D.what₂.LL)) hb
    simpa using this
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by
    rw [h1]; exact P.add_mem (P.mul_mem_right _ hr) (P.mul_mem_right _ hpP)))

def NuAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u)

theorem nuAtT_of {D : D7} {L : SizeData₂ D} (hAtT : NuAtTDef D L)
    (h5 : ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → LT.Nlam D u w ≤ LT.Sram D u w) : NuAtT D L := by
  intro u w hw x hx
  have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
    ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
  have h2 : D.nuIn u x ∈ LT.Nlam D u w := (hAtT u w hw x).mp h1
  have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := (h5 u w hw h2).1
  obtain ⟨s, hs, hsx⟩ := D.locSpan u w _ h3
  refine ⟨s, hs, ?_⟩
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  show (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
  rw [map_smul]
  exact hsx

theorem nu_le_mram {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtT D L) (u : D.what₂.Word) :
    L.NuLat u ≤ DV.MramL D u := by
  intro x hx
  refine mem_of_locally _ x (fun v => ?_)
  have hv : D.plEq (D.plEq.symm v) = v := Equiv.apply_symm_apply _ _
  by_cases hw : D.what₂.places.resChar (D.plEq.symm v) = (D.mem u).A.T
  · have := locLe_zero (hT u _ hw) x hx
    rwa [hv] at this
  · have := locLe_zero (hNu.1 u _ hw) x hx
    rwa [hv] at this

theorem exists_free_prime (D : D7) (u : D.what₂.Word) :
    ∃ p : ℕ, p.Prime ∧ p ≠ (D.mem u).A.T ∧ ¬ DV.InertK D p := by
  have hq2 : D.host.q ≠ 2 := by
    have := D.host.hyp.2.2.1
    omega
  by_cases hT : (D.mem u).A.T = 2
  · refine ⟨D.host.q, D.host.hyp.1, by rw [hT]; exact hq2, ?_⟩
    unfold DV.InertK Host.cls primeClass
    rw [if_neg D.host.q_notMem_small, if_pos rfl]
    simp
  · refine ⟨2, Nat.prime_two, fun h => hT h.symm, ?_⟩
    unfold DV.InertK Host.cls primeClass
    rw [if_pos D.host.two_mem_small]
    simp

theorem nuCommens_of {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtT D L) : NuCommens D L := by
  intro u
  have hle := nu_le_mram hNu hT u
  constructor
  · have : Module.Finite (𝓞 D.what₂.LL) (DV.MramL D u) := Module.Finite.iff_fg.2 (D.MramL_fg u)
    have : IsNoetherian (𝓞 D.what₂.LL) (DV.MramL D u) := inferInstance
    have h2 := (IsNoetherian.noetherian ((L.NuLat u).comap (DV.MramL D u).subtype)).map (DV.MramL D u).subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
    exact h2
  · obtain ⟨p, hp, hpT, hin⟩ := exists_free_prime D u
    obtain ⟨w, hw⟩ := place_over' D p hp
    have hEq := hNu.2.1 u w (by rw [hw]; exact hpT) (Or.inr (by rw [hw]; exact hin))
    refine exists_common_mul _ _ (D.MramL_fg u) (fun y hy => ?_)
    obtain ⟨s, hs, hsy⟩ := locLe_zero hEq.2 y hy
    exact ⟨s, fun h0 => hs (by rw [h0]; exact Ideal.zero_mem _), hsy⟩

theorem nuCommensF_of {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : SettingEventually Fm) :
    NuCommensF Fm := by
  obtain ⟨a0, h10⟩ := h10
  obtain ⟨a1, hS⟩ := hS
  refine ⟨max (max a0 a1) (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : Fm.x1 < x := by have := le_trans (le_max_right (max a0 a1) (Fm.x1 + 1)) hx; linarith
  exact nuCommens_of (Fm.nuDef x e2 i) (nuAtT_of (Fm.ex x e2 i).lat.atT
    (fun u w hw => ((h10 x e0 i u (hS x e1 e2 i u)).2.2.2.2.1 w hw).1))

end Formalism.MainNotions.Lnk

end

end Commens

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory


end Formalism.MainNotions

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.PlugDgt
section
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Pk

theorem eventually_level_prime_coprime_stabiliser_of_design {𝒞 : FamClass} {C0 eps : ℝ} {Fm : FamP eps} (hc : Des 𝒞 C0 Fm) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i) := by
  unfold Des at hc
  obtain ⟨⟨⟨_, hsm⟩, _⟩, _, hTu, _⟩ := hc
  obtain ⟨xs, hs⟩ := hsm
  obtain ⟨xt, ht⟩ := hTu
  refine ⟨max xs xt, fun x hx hx1 i => ?_⟩
  unfold WeightDegreeSizes.LevelPrimeCoprimeStabiliser
  intro u hdvd

  have hTp := ((Fm.D x i).mem u).A.T_prime
  have hle := hs x (le_of_max_le_left hx) i u _ hTp hdvd

  have hge := (ht x (le_of_max_le_right hx) i).1 u

  have hsz : SizesAt (Fm.L x i) := Fm.sizes x hx1 i
  unfold SizesAt at hsz
  obtain ⟨_, _, _, _, _, hC, _⟩ := hsz
  unfold SizeCond szCond at hC

  have h3m := (Fm.D x i).R.three_m_lt_t
  have hkt := (Fm.D x i).R.rank_add_five_le
  have hm2 := (Fm.D x i).R.two_le_m
  have hf : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := (Fm.D x i).R.f_le_k
  have hN : (Fm.D x i).R.N (Fm.D x i).R.m =
      (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + 1) := rfl
  have hf' : (Fm.D x i).R.f ≤ (Fm.D x i).R.t := by omega
  have hm' : (Fm.D x i).R.m ≤ (Fm.D x i).R.t := by omega
  have hk' : (Fm.D x i).R.k ≤ (Fm.D x i).R.t := by omega
  have ht7 : 7 ≤ (Fm.D x i).R.t := by omega

  have key : 2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1 < (Fm.D x i).R.t ^ 5 := by
    rw [hN]
    have e1 : (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + 1) ≤
        (Fm.D x i).R.t + (Fm.D x i).R.t * ((Fm.D x i).R.t + 1) :=
      Nat.add_le_add hk' (Nat.mul_le_mul_right _ hm')
    have e2 : 2 * (Fm.D x i).R.f * ((Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + 1)) ≤
        2 * (Fm.D x i).R.t * ((Fm.D x i).R.t + (Fm.D x i).R.t * ((Fm.D x i).R.t + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf') e1
    have e3 : 2 * (Fm.D x i).R.t * ((Fm.D x i).R.t + (Fm.D x i).R.t * ((Fm.D x i).R.t + 1)) + 1 <
        (Fm.D x i).R.t ^ 5 := by
      generalize (Fm.D x i).R.t = s at ht7 ⊢
      have h49 : 49 ≤ s ^ 2 := by nlinarith
      have h5 : 49 * s ^ 3 ≤ s ^ 5 := by
        calc 49 * s ^ 3 ≤ s ^ 2 * s ^ 3 := Nat.mul_le_mul_right _ h49
          _ = s ^ 5 := by ring
      have h23 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h13 : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    exact lt_of_le_of_lt (Nat.add_le_add_right e2 1) e3

  have hQS : (Fm.D x i).host.QS ≠ 0 := by
    intro h0
    have hcop := (Fm.D x i).host.level_coprimeS _ ((Fm.D x i).T_level u)
    rw [h0, Nat.coprime_zero_right] at hcop
    exact hTp.one_lt.ne' hcop
  have hqd := (Fm.D x i).host.qd_big
  have hq1 : (1 : ℝ) ≤ (Fm.D x i).host.q := by exact_mod_cast (show 1 ≤ (Fm.D x i).host.q by omega)
  have hd1 : (1 : ℝ) ≤ (Fm.D x i).host.d := by exact_mod_cast (show 1 ≤ (Fm.D x i).host.d by omega)
  have hQ1 : (1 : ℝ) ≤ (Fm.D x i).host.QS := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQS
  have hsc : (1 : ℝ) ≤ ((Fm.D x i).host.QS : ℝ) * (Fm.D x i).host.q * (Fm.D x i).host.d :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ1 hq1) hd1
  have hsc36 : (1 : ℝ) ≤ (((Fm.D x i).host.QS : ℝ) * (Fm.D x i).host.q * (Fm.D x i).host.d) ^ 36 :=
    one_le_pow₀ hsc
  have htR : (7 : ℝ) ≤ (Fm.D x i).R.t := by exact_mod_cast ht7
  have ht150 : ((Fm.D x i).R.t : ℝ) ^ 150 ≤ Real.sqrt (Fm.L x i).sc.b :=
    le_trans (le_mul_of_one_le_left (by positivity) hsc36) hC
  have hbpos : 0 < (Fm.L x i).sc.b := Real.sqrt_pos.mp (lt_of_lt_of_le (by positivity) ht150)
  have ht300 : ((Fm.D x i).R.t : ℝ) ^ 300 ≤ (Fm.L x i).sc.b := by
    have hmul := mul_le_mul ht150 ht150 (by positivity) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hbpos.le] at hmul
    calc ((Fm.D x i).R.t : ℝ) ^ 300 = ((Fm.D x i).R.t : ℝ) ^ 150 * ((Fm.D x i).R.t : ℝ) ^ 150 := by ring
      _ ≤ (Fm.L x i).sc.b := hmul
  have ht5 : ((Fm.D x i).R.t : ℝ) ^ 5 ≤ ((Fm.D x i).R.t : ℝ) ^ 300 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb1 : (1 : ℝ) ≤ (Fm.L x i).sc.b := by
    have : (1 : ℝ) ≤ ((Fm.D x i).R.t : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    linarith
  have hm2R : (2 : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hm2
  have hbm : (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) := by
    calc (Fm.L x i).sc.b = (Fm.L x i).sc.b ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  have hleR : (((Fm.D x i).mem u).A.T : ℝ) ≤
      ((2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
  have hkeyR : ((2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1 : ℕ) : ℝ) <
      ((Fm.D x i).R.t : ℝ) ^ 5 := by
    have := Nat.cast_lt (α := ℝ) |>.mpr key
    rw [Nat.cast_pow] at this
    exact this
  linarith

theorem closed_eventually_levelPrimeCoprimeStabiliser (𝒞 : FamClass) (C0 : ℝ) :
    Closed (Des 𝒞 C0) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i) := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩⟩
  intro Fm CH hc _
  exact eventually_level_prime_coprime_stabiliser_of_design hc

end Formalism.MainNotions

end
end

