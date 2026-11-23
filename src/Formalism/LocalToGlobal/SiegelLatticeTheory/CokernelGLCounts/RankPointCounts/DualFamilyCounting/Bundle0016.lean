module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormalizingConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLocal
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zmult_of_span (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hnx m
    · rw [mul_smul]; exact zsmul_mem hmy n
  | smul a x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨k, hk, α, hα⟩ := Formalism.HermitianLatticesTheory.traceReal_den a
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : (k * n) • (a • x) = α • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul K (k * n), ← algebraMap_smul K α (n • x),
        ← Int.cast_smul_eq_zsmul K n, smul_smul, smul_smul]
      congr 1
      rw [show algebraMap (NumberField.RingOfIntegers K) K α = (α : K) from rfl, ← hα]
      push_cast
      ring
    rw [e1]
    exact M.smul_mem α hnx

def zdiv (B : Submodule (𝓞 K) V) (n : ℤ) : Submodule (𝓞 K) V where
  carrier := {x | n • x ∈ B}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show n • (a + b) ∈ B
    rw [smul_add]
    exact B.add_mem ha hb
  smul_mem' := by
    intro c x hx
    show n • (c • x) ∈ B
    rw [smul_comm]
    exact B.smul_mem c hx

theorem exists_zsmul_of_fg {A B : Submodule (𝓞 K) V} (hA : A.FG)
    (hAB : ∀ y ∈ A, ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! m hm hmy using fun y (hy : y ∈ S) => hAB y (Submodule.subset_span hy)
  refine ⟨∏ y ∈ S, m y, Finset.prod_ne_zero_iff.2 hm, fun x hx => ?_⟩
  show x ∈ zdiv B (∏ y ∈ S, m y)
  refine (Submodule.span_le.2 ?_) hx
  intro y hy
  show (∏ y ∈ S, m y) • y ∈ B
  rw [← Finset.prod_erase_mul S m hy, mul_smul]
  exact zsmul_mem (hmy y hy) _

theorem locF_le_of_zsmul {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (n : ℤ)
    (hn : (n : 𝓞 F) ∉ 𝔭) (hAB : ∀ x ∈ A, n • x ∈ B) : locF 𝔭 A ≤ locF 𝔭 B := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
  refine (LocF.mem_locF_iff hp B x).2 ⟨(n : 𝓞 F) * t, fun hm => (hp.mem_or_mem hm).elim hn ht, ?_⟩
  rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  exact hAB _ htx

theorem badFinite {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Submodule.IsFullLattice K Λ₀)
    {U : Submodule K V} {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) :
    ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s,
      locF 𝔭.1 (Λ₀ ⊓ U.restrictScalars (𝓞 K)) = locF 𝔭.1 M := by
  classical
  set N : Submodule (𝓞 K) V := Λ₀ ⊓ U.restrictScalars (𝓞 K) with hN
  have hMU : ∀ y ∈ M, y ∈ U := fun y hy => by
    rw [← hM.2]; exact Submodule.subset_span hy
  obtain ⟨n₁, hn₁, h₁⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ M, n • x ∈ N := by
    refine exists_zsmul_of_fg hM.1 fun y hy => ?_
    obtain ⟨m, hm, hmy⟩ := Formalism.HermitianLatticesTheory.traceReal_mult Λ₀ hΛ₀ y
    exact ⟨m, hm, Submodule.mem_inf.2 ⟨hmy, zsmul_mem (hMU y hy) m⟩⟩
  have hNfg : N.FG := Submodule.FG.of_le hΛ₀.fg inf_le_left
  obtain ⟨n₂, hn₂, h₂⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ N, n • x ∈ M := by
    refine exists_zsmul_of_fg hNfg fun y hy => zmult_of_span M y ?_
    rw [hM.2]
    exact (Submodule.mem_inf.1 hy).2
  set a : 𝓞 F := ((n₁ * n₂ : ℤ) : 𝓞 F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Int.cast_ne_zero]
    exact mul_ne_zero hn₁ hn₂
  have hD : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | a ∈ 𝔭.1}.Finite := by
    refine ((Ideal.finite_factors hD).image (fun v =>
      (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
    intro 𝔭 h𝔭
    have hne : 𝔭.1 ≠ ⊥ := fun e => ha0 (by
      have : a ∈ 𝔭.1 := h𝔭
      rwa [e, Ideal.mem_bot] at this)
    refine ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, ?_, rfl⟩
    show 𝔭.1 ∣ Ideal.span {a}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔭
  refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
  have haP : a ∉ 𝔭.1 := fun h => h𝔭 (hfin.mem_toFinset.2 h)
  have e : a = (n₁ : 𝓞 F) * (n₂ : 𝓞 F) := by rw [ha]; push_cast; ring
  have h1P : (n₁ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_right _ _ h)
  have h2P : (n₂ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_left _ _ h)
  exact le_antisymm (locF_le_of_zsmul 𝔭.2.isPrime n₂ h2P h₂)
    (locF_le_of_zsmul 𝔭.2.isPrime n₁ h1P h₁)

private theorem span_dual_eq_top (h : V →ₗ⋆[K] V →ₗ[K] K)
    {L : Submodule (𝓞 K) V} (hL : L.FG) :
    Submodule.span K (Formalism.HermitianLatticesTheory.dual h L : Set V) = ⊤ := by
  classical
  obtain ⟨S, rfl⟩ := hL
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨n, hn, hint⟩ :=
    exists_integral_multiples ℤ ℚ (L := K) (S.image fun y => h y x)
  have hx : n • x ∈ Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (S : Set V)) := by
    rw [mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [map_zsmul]
      exact Submodule.mem_one.mpr ⟨⟨_, hint _ (Finset.mem_image_of_mem _ hy)⟩, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
      rw [← algebraMap_smul K c y, map_smulₛₗ h (algebraMap (𝓞 K) K c) y, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul, algebraMap_smul]
      exact Submodule.smul_mem _ r hy
  refine (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr hn : (n : K) ≠ 0)).mp ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.subset_span hx

private theorem span_locF_eq (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    Submodule.span K (locF 𝔭 L : Set V) = Submodule.span K (L : Set V) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono (LocF.le_locF 𝔭 L))
  show locF 𝔭 L ≤ (Submodule.span K (L : Set V)).restrictScalars (𝓞 K)
  rw [← locF_subspace (Submodule.span K (L : Set V)) hp]
  exact LocF.locF_mono 𝔭 (fun _ hx => Submodule.subset_span hx)

theorem glueExists_of_local (hloc : GlueLocal) : GlueExists := by
  classical
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀' M hM hMi hc
  obtain ⟨Λ₀, hΛ₀, hΛ₀u⟩ := hΛ₀'
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀, span_eq_top := hΛ₀u ▸ span_dual_eq_top h hΛ₀.fg }
  obtain ⟨s, hsM⟩ := badFinite (F := F) hΛ₀full hM
  choose T hT hTd hTm using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    hloc K F V hK hF h hs hnd U hUc hpos ⟨Λ₀, hΛ₀, hΛ₀u⟩ M hM hMi 𝔭.1 𝔭.2 (hc 𝔭.1 𝔭.2)
  choose A hA hAT using hT
  have hAfull (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : Submodule.IsFullLattice K (A 𝔭) := by
    refine { toIsLattice := hA 𝔭, span_eq_top := ?_ }
    rw [← span_locF_eq (A 𝔭) 𝔭.2.isPrime, hAT 𝔭, ← hTd 𝔭, ← hAT 𝔭,
      ← locF_dual hF h (hA 𝔭).fg 𝔭.2.isPrime, span_locF_eq _ 𝔭.2.isPrime]
    exact span_dual_eq_top h (hA 𝔭).fg
  let B := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => if 𝔭 ∈ s then A 𝔭 else Λ₀
  have hB (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : Submodule.IsFullLattice K (B 𝔭) := by
    by_cases hp : 𝔭 ∈ s
    · simpa only [B, ite_eq_left hp] using hAfull 𝔭
    · simpa only [B, ite_eq_right hp] using hΛ₀full
  have hBs : ∀ 𝔭 ∉ s, B 𝔭 = Λ₀ := fun 𝔭 hp => ite_eq_right hp
  let Λ := ⨅ 𝔭, locF 𝔭.1 (B 𝔭)
  obtain ⟨hΛ, hΛloc⟩ : Submodule.IsLattice K Λ ∧ ∀ 𝔭, locF 𝔭.1 Λ = locF 𝔭.1 (B 𝔭) :=
    LocF.patch hΛ₀full s B hB hBs
  have key (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
      locF 𝔭.1 Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭.1 M ∧
        dualF h 𝔭.1 (locF 𝔭.1 Λ) = locF 𝔭.1 Λ := by
    rw [hΛloc 𝔭]
    by_cases hp : 𝔭 ∈ s
    · rw [show B 𝔭 = A 𝔭 from ite_eq_left hp, hAT 𝔭]
      exact ⟨hTm 𝔭, hTd 𝔭⟩
    · rw [hBs 𝔭 hp]
      refine ⟨?_, ?_⟩
      · rw [← hsM 𝔭 hp, LIOrb.locF_inf_locF 𝔭.2, locF_subspace U 𝔭.2.isPrime]
      · rw [← locF_dual hF h hΛ₀.fg 𝔭.2.isPrime]
        exact congrArg (locF 𝔭.1) hΛ₀u
  refine ⟨Λ, hΛ, ?_, ?_⟩
  · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
    apply eq_of_locF (F := F)
    intro 𝔭 h𝔭
    rw [locF_dual hF h hΛ.fg h𝔭.isPrime]
    exact (key ⟨𝔭, h𝔭⟩).2
  · apply eq_of_locF (F := F)
    intro 𝔭 h𝔭
    rw [LIOrb.locF_inf_locF h𝔭, locF_subspace U h𝔭.isPrime]
    exact (key ⟨𝔭, h𝔭⟩).1

end Formalism.L2.SG.Pf.G7
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IncOInjective
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Transport

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def resF (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (fun x x' y => by simp) (fun c x y => by simp) (fun x y y' => by simp) (fun c x y => by simp)

@[simp] theorem resF_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (x y : W) :
    resF h W x y = h x y := rfl

abbrev incO (W : Submodule K V) : W →ₗ[𝓞 K] V := W.subtype.restrictScalars (𝓞 K)

abbrev latW (W : Submodule K V) (T : Submodule (𝓞 K) V) : Submodule (𝓞 K) W := T.comap (incO W)

theorem map_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    (latW W T).map (incO W) = T := by
  rw [Submodule.map_comap_eq, inf_eq_right]
  intro x hx
  exact ⟨⟨x, hT.2 ▸ Submodule.subset_span hx⟩, rfl⟩

theorem incO_injective (W : Submodule K V) : Function.Injective (incO W) := Subtype.val_injective

theorem isLattice_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    Submodule.IsFullLattice K (latW W T) := by
  have hfg : (latW W T).FG :=
    Submodule.fg_of_fg_map_injective _ (incO_injective W) (by rw [map_latW hT]; exact hT.1)
  refine { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }
  apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
  have himg : (Subtype.val '' ((latW W T : Submodule (𝓞 K) W) : Set W)) = (T : Set V) := by
    have e := congrArg (fun S : Submodule (𝓞 K) V => (S : Set V)) (map_latW hT)
    simpa [Submodule.map_coe] using e
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Submodule.coe_subtype, himg, hT.2]

private lemma mem_of_algebraMap_smul_mem (W : Submodule K V) {t : 𝓞 F} (ht : t ≠ 0) {x : V}
    (h : algebraMap (𝓞 F) (𝓞 K) t • x ∈ W) : x ∈ W := by
  have hs : algebraMap (𝓞 F) (𝓞 K) t ≠ 0 := fun h0 =>
    ht (NumberField.RingOfIntegers.algebraMap.injective F K (h0.trans (map_zero _).symm))
  have hsK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact_mod_cast hs
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x] at h
  have h2 := W.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hsK, one_smul] at h2

private lemma map_incO_locF (W : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (A : Submodule (𝓞 K) W) : (locF 𝔭 A).map (incO W) = locF 𝔭 (A.map (incO W)) := by
  ext x
  simp only [Submodule.mem_map, Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
  constructor
  · rintro ⟨y, ⟨t, ht, hy⟩, rfl⟩
    exact ⟨t, ht, _, hy, by simp⟩
  · rintro ⟨t, ht, z, hz, hzx⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hxW : x ∈ W := by
      apply mem_of_algebraMap_smul_mem W ht0
      rw [← hzx]
      exact z.2
    refine ⟨⟨x, hxW⟩, ⟨t, ht, ?_⟩, rfl⟩
    convert hz using 1
    exact Subtype.ext hzx.symm

theorem locF_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) (𝔭 : Ideal (𝓞 F))
    [𝔭.IsPrime] : (locF 𝔭 (latW W T)).map (incO W) = locF 𝔭 T := by
  rw [map_incO_locF, map_latW hT]

theorem isJordanIn_res {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {T : Submodule (𝓞 K) V}
    (hT : IsLatIn W T) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {b : Fin (finrank K W) → V} {a : Fin (finrank K W) → 𝓞 F}
    (hb : IsJordanIn h W T 𝔭 b a) :
    IsJordanIn (resF h W) ⊤ (latW W T) 𝔭
      (fun i => ⟨b (finCongr (finrank_top K W) i), hb.1 _⟩) (fun i => a (finCongr (finrank_top K W) i)) := by
  obtain ⟨hbW, hloc, horth, hdiag, hne⟩ := hb
  refine ⟨fun i => Submodule.mem_top, ?_, ?_, ?_, fun i => hne _⟩
  · apply Submodule.map_injective_of_injective (incO_injective W)
    have himg : ⇑(incO W) '' Set.range (fun i : Fin (finrank K (⊤ : Submodule K W)) =>
        (⟨b (finCongr (finrank_top K W) i), hbW _⟩ : W)) = Set.range b := by
      ext v
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨(finCongr (finrank_top K W)).symm i, rfl⟩, by simp⟩
    rw [map_incO_locF, locF_latW hT, Submodule.map_span, himg, hloc]
  · intro i j hij
    simp only [resF_apply]
    exact horth _ _ ((finCongr (finrank_top K W)).injective.ne hij)
  · intro i
    simp only [resF_apply]
    exact hdiag _

end Transport

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSpanHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem jordan_span_holds :
    ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
      [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
      (L : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → ∀ 𝔭 : Ideal (𝓞 F),
      𝔭.IsMaximal → ∀ (n : ℕ) (b : Fin n → V),
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
        Submodule.span K (Set.range b) = ⊤ := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  letI : Submodule.IsFullLattice K L := hL
  rw [eq_top_iff, ← Submodule.IsFullLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcTieCOf
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcAsm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def NcValueC : Prop :=
  Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂ * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al =
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' *
      ((bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ) *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * ngFac D

theorem ncTieC_of
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hCoo : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Coo =
      Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0)
    (hval : NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) := by
  unfold NcTieC
  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  rw [Formalism.L2.SG.Pf.NcCut.nc_iff B hP hM hMs hL hO hT ⟨hV.2.1, hV.2.2⟩ _ (ngFac D) (Formalism.L2.SG.MassDataConc.kapN D) hkap]
  have hG : 0 < B.volG := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hHa : 0 < B.volHa := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBH : B.volB / B.volHa = 1 := by
    have h1 := hV.1
    rw [hVG] at h1
    have : B.volB = B.volHa := by
      have := mul_right_cancel₀ hG.ne' h1
      exact this
    rw [this, div_self hHa.ne']
  rw [hBH, hCoo]
  unfold NcValueC at hval
  rw [← hB] at hval
  linear_combination (Formalism.L2.SG.MassDataConc.kapN D) * hval

theorem kapN_ne (D : D7) : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have h1 := (Formalism.BasicNotions.rdE_pos_le D).1
  have hg : (0 : ℝ) < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    unfold Formalism.MainNotions.S.Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  exact mul_ne_zero (pow_ne_zero _ h1.ne') (inv_ne_zero (pow_ne_zero _ hg.ne'))

theorem coo_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Coo =
    Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := rfl

theorem ncTieC_of'
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hval : NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  ncTieC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (coo_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) (kapN_ne D) hval

end Formalism.L2.SG.Pf.NcAsm
end
end

