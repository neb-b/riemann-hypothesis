module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HermitianCoefficientIdentityOne
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GramComb
section
noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TotPosAll : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), star x = x → Formalism.MainNotions.S.LocalSplitGroups.TotPos x → Formalism.HermitianLattices.Ext.L3.TotPos x

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gram_comb' {ι : Type} [Fintype ι] (p : ι → S.V) (A : Matrix ι ι E) (b c : ι) :
    S.hT (∑ a, A a b • p a) (∑ a, A a c • p a) =
      (A.conjTranspose * Matrix.of (fun a a' => S.hT (p a) (p a')) * A) b c := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, starRingEnd_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
    | (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)

variable {r : ℕ}

def gv (y : Fin r → S.V) (z : S.V) (N : ℕ) : Fin (r + 1) → S.V :=
  Fin.snoc (α := fun _ => S.V) y ((-((N : E)⁻¹)) • z)


variable (E) in
def Gam (r N' : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -(N' : E) else 0

def Gam' (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  (Z⁻¹).conjTranspose * Gam E r N' * Z⁻¹

def Psi (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (d : Fin r) (a : Fin (r + 1)) : E :=
  if a = Fin.last r then Gam' N' Z (Fin.castSucc d) (Fin.last r) else Gam' N' Z (Fin.castSucc d) a / 2

def pv (e y : Fin r → S.V) (z : S.V) (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w0 : S.V)
    (a : Fin (r + 1)) : S.V :=
  gv y z N a + ∑ d, Psi N' Z d a • e d + (if a = Fin.last r then (1 : E) else 0) • w0

def tv (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Gam' N' Z (Fin.last r) (Fin.last r) + (N : E)⁻¹

theorem gam_herm (N' : ℕ) (a b : Fin (r + 1)) : star (Gam E r N' a b) = Gam E r N' b a := by
  simp only [Gam, Matrix.of_apply]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem gam'_herm (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    star (Gam' N' Z a b) = Gam' N' Z b a := by
  have hG : (Gam E r N').conjTranspose = Gam E r N' := by
    ext a b; rw [Matrix.conjTranspose_apply, gam_herm]
  have h1 : (Gam' N' Z).conjTranspose = Gam' N' Z := by
    simp only [Gam', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  have := congrFun (congrFun h1 b) a
  rwa [Matrix.conjTranspose_apply] at this

variable {e y : Fin r → S.V} {z : S.V} {N : ℕ} (h : Dual e y z N) (hN : 0 < N)
include h hN

theorem hgv_e (a : Fin (r + 1)) (d : Fin r) :
    S.hT (gv y z N a) (e d) = if a = Fin.castSucc d then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last d).ne']
    simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hsw0 S (h.ez d), smul_zero]
  | cast a =>
    simp only [gv, Fin.snoc_castSucc, Fin.castSucc_inj, h.ye]
    by_cases had : a = d
    · subst had; simp
    · simp [had, Ne.symm had]

theorem he_gv (d : Fin r) (a : Fin (r + 1)) :
    S.hT (e d) (gv y z N a) = if a = Fin.castSucc d then 1 else 0 := by
  rw [hsw, hgv_e h hN]; split_ifs <;> simp

theorem hz_gv (a : Fin (r + 1)) : S.hT z (gv y z N a) = if a = Fin.last r then 1 else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    simp only [gv, Fin.snoc_last, map_smul, smul_eq_mul, h.zz, if_true]
    field_simp
  | cast a =>
    rw [if_neg (Fin.castSucc_lt_last a).ne]
    simp only [gv, Fin.snoc_castSucc]
    exact hsw0 S (h.yz a)

theorem hgv_gv (a a' : Fin (r + 1)) : S.hT (gv y z N a) (gv y z N a') =
    if a = Fin.last r ∧ a' = Fin.last r then -((N : E)⁻¹) else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, h.zz,
        starRingEnd_apply, star_neg, star_inv₀, star_natCast, and_self, if_true]
      field_simp
    | cast a' =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        hsw0 S (h.yz a'), smul_zero]
      simp [(Fin.castSucc_lt_last a').ne]
  | cast a =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, map_smul, h.yz, smul_zero]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast a' =>
      simp only [gv, Fin.snoc_castSucc, h.yy]
      simp [(Fin.castSucc_lt_last a).ne]

variable {N' : ℕ} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {w0 : S.V} (hw : IsW e y z w0)
include hw

theorem hf_pv (a a' : Fin (r + 1)) :
    S.hT (Fin.snoc (α := fun _ => S.V) e z a) (pv e y z N N' Z w0 a') = if a = a' then 1 else 0 := by
  obtain ⟨hwe, -, hwz⟩ := hw
  induction a using Fin.lastCases with
  | last =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pv, Fin.snoc_last, map_add (f := _), map_sum, map_smul, smul_eq_mul, hsw0 S (h.ez _), mul_zero,
      Finset.sum_const_zero, add_zero, hwz, hz_gv h hN]
    simp [eq_comm]
  | cast a =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pv, Fin.snoc_castSucc, map_add (f := _), map_sum, map_smul, smul_eq_mul, h.ee, mul_zero,
      Finset.sum_const_zero, add_zero, hwe, he_gv h hN]
    simp [eq_comm]

theorem hpv_pv (ht : S.hT w0 w0 = tv N N' Z) (a a' : Fin (r + 1)) :
    S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') = Gam' N' Z a a' := by
  obtain ⟨hwe, hwy, hwz⟩ := hw
  have hgw : ∀ b, S.hT (gv y z N b) w0 = 0 := by
    intro b
    induction b using Fin.lastCases with
    | last => simp [gv, hwz]
    | cast b => simp [gv, hwy]
  have hwg : ∀ b, S.hT w0 (gv y z N b) = 0 := fun b => hsw0 S (hgw b)
  have hwe' : ∀ d, S.hT w0 (e d) = 0 := fun d => hsw0 S (hwe d)
  have key : S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') =
      S.hT (gv y z N a) (gv y z N a') +
      ∑ d, Psi N' Z d a' * S.hT (gv y z N a) (e d) +
      ∑ d, star (Psi N' Z d a) * S.hT (e d) (gv y z N a') +
      star (if a = Fin.last r then (1 : E) else 0) * (if a' = Fin.last r then (1 : E) else 0) * S.hT w0 w0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pv, map_add (f := _), LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, h.ee, mul_zero, Finset.sum_const_zero, hgw, hwg,
      hwe, hwe', add_zero, zero_add]
    ring
  rw [key, hgv_gv h hN, ht]
  simp only [hgv_e h hN, he_gv h hN, mul_ite, mul_one, mul_zero]
  have hne : ∀ d : Fin r, Fin.last r ≠ Fin.castSucc d := fun d => (Fin.castSucc_lt_last d).ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last => simp [tv, hne]
    | cast a' => simp [hne, Psi, gam'_herm]
  | cast a =>
    induction a' using Fin.lastCases with
    | last => simp [hne, (Fin.castSucc_lt_last a).ne, Psi]
    | cast a' =>
      simp [(Fin.castSucc_lt_last a).ne, (Fin.castSucc_lt_last a').ne, Psi, star_div₀, gam'_herm]

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsAlt
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

private theorem unit_mul_lemma {a c : K} (ha : IsUnitIn S a) (hc : IsUnitIn S c) :
    IsUnitIn S (a * c) :=
  And.intro (mul_ne_zero ha.1 hc.1)
    (And.intro (S.mul_mem ha.2.1 hc.2.1) (by rw [mul_inv]; exact S.mul_mem ha.2.2 hc.2.2))

theorem absorb (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {e : ι → ℕ} {i₀ : ι} (x : ι → K) (hx : ∀ i, x i ∈ S) :
    ∀ T : Finset ι, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : ι → V,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧
      (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro _ _ b ho hu
    exact ⟨b, ho, hu, by simp, fun _ _ _ => rfl, rfl, fun _ => Iff.rfl⟩
  · intro a T haT ih hi₀ hlt b ho hu
    have hi₀T : i₀ ∉ T := fun hm => hi₀ (Finset.mem_insert_of_mem hm)
    have hai₀ : i₀ ≠ a := by
      intro h'
      apply hi₀
      rw [h']
      exact Finset.mem_insert_self a T
    obtain ⟨c', ho', hu', hc'0, hc'k, hsp', hiff'⟩ :=
      ih hi₀T (fun j hj => hlt j (Finset.mem_insert_of_mem hj)) b ho hu
    have hc'a : c' a = b a := hc'k a (Ne.symm hai₀) haT
    have hlta : e i₀ < e a := hlt a (Finset.mem_insert_self a T)
    have hu0 : h (c' i₀) (c' i₀) ≠ 0 := unit_ne (hu' i₀)
    have hπ0 : π ≠ 0 := hπ.ne
    obtain ⟨d, hd⟩ : ∃ d, e a = e i₀ + d + 1 := ⟨e a - e i₀ - 1, by omega⟩
    have hs0 : (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹)⁻¹
        * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d) ∈ S :=
      S.mul_mem (hu' i₀).2.2 (S.mul_mem (S.mul_mem (S.mul_mem (hS.star_mem _ (hx a)) (hx a))
        (hu' a).2.1) (S.pow_mem hπ.mem d))
    have hY : IsUnitIn S (h ((1 : K) • c' i₀ + x a • c' a) ((1 : K) • c' i₀ + x a • c' a)
        * (π ^ e i₀)⁻¹) := by
      rw [form_pair (c' i₀) (c' a) (ho' i₀ a hai₀) (ho' a i₀ (Ne.symm hai₀))]
      have eq : (star (1 : K) * 1 * h (c' i₀) (c' i₀) + star (x a) * x a * h (c' a) (c' a))
          * (π ^ e i₀)⁻¹ = (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹) * (1 + π * ((h (c' i₀) (c' i₀)
          * (π ^ e i₀)⁻¹)⁻¹ * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d))) := by
        rw [hd, star_one]
        field_simp
        ring
      rw [eq]
      exact unit_mul_lemma (hu' i₀) (hπ.rad _ hs0)
    obtain ⟨c, ho2, hu2, hc0, hck, hsp2, hiff2⟩ :=
      rot2 hS hπ hs ho' hu' hai₀ hlta.le S.one_mem (hx a) hY
    refine ⟨c, ho2, hu2, ?_, ?_, hsp2.trans hsp', fun v => (hiff2 v).trans (hiff' v)⟩
    · rw [hc0, hc'0, hc'a, one_smul, Finset.sum_insert haT]
      abel
    · intro k hk0 hkT
      have hka : k ≠ a := by
        intro h'
        apply hkT
        rw [h']
        exact Finset.mem_insert_self a T
      have hkT' : k ∉ T := fun h' => hkT (Finset.mem_insert_of_mem h')
      rw [hck k hk0 hka, hc'k k hk0 hkT']

end

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem jι_eq' (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  have e := UnimodularLocalization.algebraMap_smul_K (K := K) t (1 : K)
  rwa [Algebra.smul_def, mul_one, mul_one] at e

theorem inP_of_mem_pow {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {t : 𝓞 F} (ht : t ∈ 𝔭 ^ k) :
    InP 𝔭 k (algebraMap F K (t : F)) := by
  rw [← jι_eq']
  apply inP_jK
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ht

theorem inP_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ≠ 0) :
    InP 𝔭 (vF 𝔭 t) (algebraMap F K (t : F)) := by
  have := h𝔭.isPrime
  exact inP_of_mem_pow ((G1.mem_pow_iff h𝔭 ht _).2 le_rfl)

theorem mem_SP_of_inP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {k : ℕ}
    {x : K} (hx : InP 𝔭 k x) : (algebraMap F K (π : F))⁻¹ ^ k * x ∈ SP K 𝔭 := by
  obtain ⟨s, hs, rfl⟩ := (mem_noncompactPart_iff hu k x).1 hx
  have h0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  rw [jι_eq', ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_mul]
  exact hs

theorem star_fix (hF : IsFixF K F) (x : F) : star (algebraMap F K x) = algebraMap F K x :=
  (hF _).2 ⟨x, rfl⟩

theorem star_inv_pow (hF : IsFixF K F) (x : F) (k : ℕ) :
    star ((algebraMap F K x)⁻¹ ^ k) = (algebraMap F K x)⁻¹ ^ k := by
  rw [← map_inv₀, ← map_pow]; exact star_fix hF _

theorem form_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h (r • x) y = star r * h x y := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem form_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h x (r • y) = r * h x y := by
  rw [map_smul, smul_eq_mul]

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (r r' : K) (x y : V) :
    h (r • x) (r' • y) = star r * r' * h x y := by
  rw [form_smul_left, form_smul_right]; ring

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IndexTypC
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcIdx

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets MeasureTheory

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

def IndexTypC : Prop :=
  ∀ p : TypX X,
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
      (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
        aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)

end Formalism.L2.SG.Pf.NcIdx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVTop
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

