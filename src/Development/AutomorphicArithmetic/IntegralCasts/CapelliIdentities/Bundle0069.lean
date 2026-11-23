module

public import Mathlib
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.WeaklyAdmissibleFiltrations.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0068

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FgZ1T
section
open Formalism.WeaklyAdmissibleFiltrations in
/-- Apply compact-quotient finite generation to the lattice cocycles, using reduction modulo `ϖ`. -/
theorem UpperTheory.Reformulated.B.Gub2.fg_Z1T
    {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    {LL O V : Type} [inst_2 : Field LL] [inst_3 : CommRing O] [inst_4 : Algebra O LL]
    [inst_5 : AddCommGroup V] [inst_6 : Module LL V] [inst_7 : Module O V]
    [inst_8 : IsScalarTower O LL V] {ρ : Representation LL G V}
    [inst_9 : TopologicalSpace V] [inst_10 : ContinuousAdd V] [inst_11 : ContinuousConstSMul LL V]
    [inst_12 : TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V]
    (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : algebraMap O LL ϖ ≠ 0)
    (hb : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hc : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T))
    (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG := by
  have hmem : ∀ x : L.T, x ∈ (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T)) ↔
      ∃ y ∈ L.T, ϖ • y = (x : V) := by
    intro x
    rw [pow_one, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  have hred : ∀ c : latticeCocycles L, redT L _ c ∈ quotientCocycles L _ hI := by
    intro c
    have hcont : Continuous (c : G → V) := c.2.1.1
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, fun g h => ?_⟩
    · have h0 : Filter.Tendsto (fun y => (c : G → V) y - (c : G → V) g) (nhds g) (nhds 0) := by
        have := (hcont.sub (continuous_const (y := (c : G → V) g))).tendsto g
        rw [Pi.sub_apply, sub_self] at this
        exact this
      filter_upwards [h0 (hb.mem_of_mem (i := 1) trivial)] with y hy
      obtain ⟨v, hv, hvy⟩ := hy
      refine (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨v, hv, ?_⟩)
      rw [← pow_one ϖ]
      exact hvy
    · have : evT L (g * h) c = evT L g c + actT L g (evT L h c) :=
        Subtype.ext (c.2.1.2 g h)
      change Submodule.mkQ _ (evT L (g * h) c) = _
      rw [this, map_add (f := _)]
      rfl
  refine UpperTheory.compact_quotient_submodule (LL := LL) (latticeCocycles L) ϖ
    ((redT L _).codRestrict (quotientCocycles L _ hI) hred) hc ?_ ?_
  · intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIf, t, ht, hsub⟩ := hU
    obtain ⟨n, -, hn⟩ := hb.mem_iff.1 ((Filter.biInter_mem hIf).2 fun i _ => ht i)
    refine ⟨n, fun z hz => hsub fun i hi => ?_⟩
    exact Set.mem_iInter₂.1 (hn ⟨z i, hz.2 i trivial, rfl⟩) i hi
  · intro z hz
    have hz' : ∀ g, ∃ y ∈ L.T, ϖ • y = (z : G → V) g := fun g =>
      (hmem (evT L g z)).1
        ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Subtype.val hz) g))
    refine ⟨(algebraMap O LL ϖ)⁻¹ • (z : G → V),
      ⟨(continuousCocycles ρ).smul_mem _ z.2.1, fun g _ => ?_⟩, ?_⟩
    · obtain ⟨y, hy, h⟩ := hz' g
      have : ((algebraMap O LL ϖ)⁻¹ • (z : G → V)) g = y := by
        rw [Pi.smul_apply, ← h, ← algebraMap_smul LL ϖ y, inv_smul_smul₀ hϖ]
      rw [this]
      exact hy
    · rw [← algebraMap_smul LL ϖ, smul_inv_smul₀ hϖ]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevelOfCongruence
section
private theorem UpperTheory.Reformulated.B.LevelOfCongruence.level {C R T : Type} [CommRing C] [CommRing R] [CommRing T]
    (a : C →+* R) (f : C →+* T) (M : Ideal R) (K : Ideal T)
    (hd : ∀ r : R, ∃ c, r - a c ∈ M) (hk : ∀ c, a c ∈ M → f c ∈ K) :
    ∃ g : R →+* T ⧸ K, ∀ r c, r - a c ∈ M → g r = Ideal.Quotient.mk K (f c) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk M).comp a) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hd r
    exact ⟨c, (Ideal.Quotient.eq.2 hc).symm⟩
  have hker : RingHom.ker ((Ideal.Quotient.mk M).comp a) ≤
      RingHom.ker ((Ideal.Quotient.mk K).comp f) := by
    intro c hc
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
    exact hk c hc
  refine ⟨(RingHom.liftOfSurjective _ hs ⟨_, hker⟩).comp (Ideal.Quotient.mk M), ?_⟩
  intro r c hc
  rw [RingHom.comp_apply, Ideal.Quotient.eq.2 hc]
  exact RingHom.liftOfSurjective_comp_apply _ hs ⟨_, hker⟩ c

theorem UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex :
    ∀ {C R : Type} [inst : CommRing C] [inst_1 : CommRing R] [inst_2 : Algebra C R] [inst_3 : IsLocalRing R] {x : Ideal C},
      UpperTheory.V.CA.IsCplAt x R →
        ∀ {T : Type} [inst_4 : CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T),
          x ≤ Ideal.comap f J →
            ∃ (F : R →+* T), F.comp (Algebra.algebraMap C R) = f ∧ IsLocalRing.maximalIdeal R ≤ Ideal.comap F J := by
  intro C R _ _ _ _ x h T _ J _ f hx
  have hk : ∀ (n : ℕ) (c : C), algebraMap C R c ∈ IsLocalRing.maximalIdeal R ^ n → f c ∈ J ^ n := by
    intro n c hc
    have h1 : c ∈ x ^ n := by
      rw [← h.comap_pow n]
      exact hc
    exact Ideal.le_comap_pow f n (Ideal.pow_right_mono hx n h1)
  choose g hg using fun n : ℕ => UpperTheory.Reformulated.B.LevelOfCongruence.level (algebraMap C R) f
    (IsLocalRing.maximalIdeal R ^ n) (J ^ n) (h.dense n) (hk n)
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (g n) = g m := by
    intro m n hle
    ext r
    obtain ⟨c, hc⟩ := h.dense n r
    rw [RingHom.comp_apply, hg n r c hc, hg m r c (Ideal.pow_le_pow_right hle hc)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J g hc, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' J
    intro n c
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom]
    exact hg n _ c (by simp)
  · intro r hr
    have h0 := IsAdicComplete.mk_liftRingHom J g hc 1 r
    rw [hg 1 r 0 (by simpa using hr), map_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      pow_one] at h0
    exact h0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Parity
section
open ReciprocityTheory.ChartRestriction.G.FD in
private theorem UpperTheory.Reformulated.B.Ue6.herm_smul_right {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (w0 : NumberField.RingOfIntegers E),
      ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E) = (1 : E) - (↑w0 : E) →
        ∀ u ∈ X.Λ,
          ∀ v ∈ X.Λ,
            ∃ (k : ℤ),
              (Algebra.trace ℚ E : E → ℚ)
                    (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u (((↑w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E)) • v)) -
                  (Algebra.trace ℚ E : E → ℚ) (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) =
                (2 : ℚ) * (↑k : ℚ) := by
  intro E _ _ _ r X w0 hw u hu v hv
  have hwv : (w0 : E) • v ∈ X.Λ := X.Λ.smul_mem w0 hv
  obtain ⟨a, ha⟩ := X.EF_int u hu _ hwv
  obtain ⟨b, hb⟩ := X.EF_int u hu v hv
  have hc : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) = 1 - 2 * (w0 : E) := by
    have h1 : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - (1 - (w0 : E))) =
        ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) - (1 - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_sub, map_one]
    rw [hw, h1, hw]
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.EFf at ha hb
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hw] at ha
  refine ⟨b - a, ?_⟩
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hc, Int.cast_sub, ← ha, ← hb, ← map_sub, ← map_sub,
    two_mul ((Algebra.trace ℚ E) _), ← map_add]
  congr 1
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RelativeK1Module
section
noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.Stab :
    {S E : Type} →
      [inst : CommRing S] →
        [inst_1 : Algebra ℂ S] →
          [inst_2 : AddCommGroup E] →
            [inst_3 : _root_.Module ℂ E] → (S →ₐ[ℂ] Module.End ℂ E) → Subalgebra ℂ S → Submodule ℂ E → Prop :=
    fun {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [_root_.Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
        (R : Subalgebra ℂ S) (M : Submodule ℂ E) ↦
      ∀ r ∈ R, ∀ m ∈ M, ((act : S → Module.End ℂ E) r : E → E) m ∈ M

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.wd :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] → (ι → Module.End k E) → (Finset ι → E) →ₗ[k] Finset ι → E :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (w : ι → Module.End k E) ↦
      LinearMap.pi fun (t : Finset ι) ↦ ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ∘ₗ LinearMap.proj (t.erase i)

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.acx :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] →
                  (Finset ι → Submodule k E) → (ι → Module.End k E) → GlobalTheory.PD.Cx k (Finset ι → E) :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (A : Finset ι → Submodule k E) (w : ι → Module.End k E) ↦
      { C := fun (n : ℤ) ↦ Submodule.pi Set.univ fun (s : Finset ι) ↦ if (↑s.card : ℤ) = n then A s else ⊥,
        D := UpperTheory.Reformulated.B.KoszulComplexHomotopy.wd w : GlobalTheory.PD.Cx k (Finset ι → E) }

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos :
    {S E : Type} →
      [inst : CommRing S] →
        [inst_1 : Algebra ℂ S] →
          [inst_2 : AddCommGroup E] →
            [inst_3 : _root_.Module ℂ E] →
              (S →ₐ[ℂ] Module.End ℂ E) → {κ : Type} → [LinearOrder κ] → Submodule ℂ E → (κ → S) → GlobalTheory.PD.Cx ℂ (Finset κ → E) :=
    fun {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [_root_.Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
        {κ : Type} [LinearOrder κ] (M : Submodule ℂ E) (r : κ → S) ↦
      UpperTheory.Reformulated.B.KoszulComplexHomotopy.acx (fun (x : Finset κ) ↦ M) fun (l : κ) ↦ (act : S → Module.End ℂ E) (r l)

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp :
    {S κ : Type} → [inst : CommRing S] → [inst_1 : Algebra ℂ S] → [Fintype κ] → Subalgebra ℂ S → (κ → S) → S → Prop :=
    fun {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] (R : Subalgebra ℂ S) (r : κ → S) (g : S) ↦
      ∃ (a : κ → S), (∀ (l : κ), a l ∈ R) ∧ g = ∑ l : κ, a l * r l

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.Htpy :
    Prop :=
    ∀ (S E : Type) [inst : CommRing S] [inst_1 : Algebra ℂ S] [inst_2 : AddCommGroup E] [inst_3 : _root_.Module ℂ E]
      (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [inst_4 : LinearOrder κ] [inst_5 : Fintype κ] (R : Subalgebra ℂ S)
      (M : Submodule ℂ E) (r : κ → S),
      UpperTheory.Reformulated.B.KoszulComplexHomotopy.Stab act R M →
        ∀ (n : ℤ),
          ∀ c ∈ (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos act M r).Z n,
            ∀ (g : S),
              UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp R r g →
                (fun (L : Finset κ) ↦ ((act : S → Module.End ℂ E) g : E → E) (c L)) ∈ (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos act M r).B n

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.KE :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → GlobalTheory.PD.Cx ℂ M → ℤ → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (C : GlobalTheory.PD.Cx ℂ M) (d : ℤ) ↦ ∀ m < d, C.Z m ≤ C.B m

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.KoszulExactBelowLengthOfWeaklyRegular :
    Prop :=
    ∀ (d : ℕ) (R N : Type) [inst : CommRing R] [inst_1 : Algebra ℂ R] [inst_2 : AddCommGroup N] [inst_3 : _root_.Module R N]
      [inst_4 : _root_.Module ℂ N] [inst_5 : IsScalarTower ℂ R N] (κ : Type) [inst_6 : LinearOrder κ] [inst_7 : Fintype κ]
      (r : κ → R) (f : List R),
      f.length = d →
        RingTheory.Sequence.IsWeaklyRegular N f →
          (∀ g ∈ f, UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp ⊤ r g) →
            UpperTheory.Reformulated.B.KoszulComplexHomotopy.KE (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos (Algebra.lsmul ℂ ℂ N) ⊤ r) (↑d : ℤ)

namespace UpperTheory.Reformulated.B.KoszulComplexHomotopy

section Helpers

variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {κ : Type} [LinearOrder κ]

private def dd (r : κ → R) (c : Finset κ → N) : Finset κ → N :=
  fun t => ∑ i ∈ t, GlobalTheory.cubeSign t i • r i • c (t.erase i)

private theorem dd_map {N' : Type} [AddCommGroup N'] [Module R N'] (φ : N →ₗ[R] N') (r : κ → R)
    (c : Finset κ → N) (t : Finset κ) : dd r (fun s => φ (c s)) t = φ (dd r c t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dd, map_sum]

private theorem dd_add (r : κ → R) (a b : Finset κ → N) (t : Finset κ) :
    dd r (fun s => a s + b s) t = dd r a t + dd r b t := by
  simp [dd, Finset.sum_add_distrib]

private theorem dd_deg (r : κ → R) (c : Finset κ → N) (n : ℤ)
    (hc : ∀ s : Finset κ, (s.card : ℤ) ≠ n - 1 → c s = 0) (t : Finset κ) (ht : (t.card : ℤ) ≠ n) :
    dd r c t = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := Finset.card_erase_add_one hi
  rw [hc _ (by omega), smul_zero, smul_zero]

private theorem dd_dd [Module ℂ N] (r : κ → R) (c : Finset κ → N) (t : Finset κ) :
    dd r (dd r c) t = 0 := by
  let F : κ → κ → N := fun i j =>
    if j ≠ i then (GlobalTheory.cubeSign t i * GlobalTheory.cubeSign (t.erase i) j) • (r i * r j) • c ((t.erase i).erase j)
    else 0
  have h1 : dd r (dd r c) t = ∑ i ∈ t, ∑ j ∈ t, F i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F]
    rw [← Finset.sum_filter, Finset.filter_ne', dd, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, mul_smul, smul_comm (r i)]
  have h2 : ∀ i ∈ t, ∀ j ∈ t, F i j + F j i = 0 := by
    intro i hi j hj
    by_cases h : j = i
    · simp [F, h]
    · simp only [F]
      rw [if_pos h, if_pos (Ne.symm h), GlobalTheory.cubeSign_mul_erase hi hj (Ne.symm h), mul_comm (r j),
        Finset.erase_right_comm (a := j), neg_smul, neg_add_cancel]
  have h3 : (∑ i ∈ t, ∑ j ∈ t, F i j) + ∑ i ∈ t, ∑ j ∈ t, F j i = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j hj => h2 i hi j hj
  rw [Finset.sum_comm (f := fun i j => F j i), ← two_smul ℂ] at h3
  rw [h1]
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable [Algebra ℂ R] [Module ℂ N] [IsScalarTower ℂ R N]

private theorem kos_D (r : κ → R) (c : Finset κ → N) :
    (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).D c = dd r c := by
  funext t
  simp [kos, acx, wd, dd]

private theorem kos_C (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).C n ↔ ∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0 := by
  simp only [kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n <;> simp [h]

private theorem kos_Z (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).Z n ↔
      (∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0) ∧ dd r c = 0 := by
  rw [GlobalTheory.PD.Cx.Z, Submodule.mem_inf, kos_C, LinearMap.mem_ker, kos_D]

private theorem kos_B (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).B n ↔
      ∃ b : Finset κ → N, (∀ s : Finset κ, (s.card : ℤ) ≠ n - 1 → b s = 0) ∧ dd r b = c := by
  simp only [GlobalTheory.PD.Cx.B, Submodule.mem_map, kos_C, kos_D]

end Helpers

end UpperTheory.Reformulated.B.KoszulComplexHomotopy

open scoped Pointwise in
theorem UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    UpperTheory.Reformulated.B.KoszulComplexHomotopy.Htpy → UpperTheory.Reformulated.B.KoszulComplexHomotopy.KoszulExactBelowLengthOfWeaklyRegular := by
  intro H d
  induction d with
  | zero =>
    intro R N _ _ _ _ _ _ κ _ _ r f _ _ _ m hm c hc
    have h0 : c = 0 := funext fun s => ((kos_Z r c m).1 hc).1 s (by omega)
    rw [h0]
    exact Submodule.zero_mem _
  | succ d ih =>
    intro R N _ _ _ _ _ _ κ _ _ r f hlen hreg hsp m hm c hc
    obtain _ | ⟨g, f⟩ := f
    · simp at hlen
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hg, hf⟩ := hreg
    have hB := H R N (Algebra.lsmul ℂ ℂ N) κ ⊤ ⊤ r (fun _ _ _ _ => Submodule.mem_top) m c hc g
      (hsp g List.mem_cons_self)
    obtain ⟨b, hb, hbc⟩ := (kos_B r _ m).1 hB
    have hbc' : ∀ s, dd r b s = g • c s := fun s => congrFun hbc s
    let P : Submodule R N := g • (⊤ : Submodule R N)
    have hP : ∀ x : N, P.mkQ x = 0 ↔ ∃ y, g • y = x := by
      intro x
      simp [P, Submodule.mem_smul_pointwise_iff_exists]
    have IH := ih R (N ⧸ P) κ r f (by simpa using hlen) hf
      (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) (m - 1) (by omega)
    have hZ : (fun s => P.mkQ (b s)) ∈ (kos (Algebra.lsmul ℂ ℂ (N ⧸ P)) ⊤ r).Z (m - 1) := by
      rw [kos_Z]
      refine ⟨fun s hs => by rw [hb s hs, map_zero], funext fun s => ?_⟩
      rw [dd_map, hbc']
      exact (hP _).2 ⟨_, rfl⟩
    obtain ⟨a, ha, hab⟩ := (kos_B r _ _).1 (IH hZ)
    have hlift : ∀ s : Finset κ, ∃ x : N, P.mkQ x = a s ∧ ((s.card : ℤ) ≠ m - 1 - 1 → x = 0) := by
      intro s
      by_cases hs : (s.card : ℤ) = m - 1 - 1
      · obtain ⟨x, hx⟩ := P.mkQ_surjective (a s)
        exact ⟨x, hx, fun h => absurd hs h⟩
      · exact ⟨0, by rw [ha s hs, map_zero], fun _ => rfl⟩
    choose a' ha' ha0 using hlift
    have hdiv : ∀ s, ∃ y, g • y = b s - dd r a' s := by
      intro s
      rw [← hP, map_sub, ← dd_map, funext ha', hab, sub_self]
    choose y hy using hdiv
    rw [kos_B]
    refine ⟨y, fun s hs => hg ?_, funext fun s => hg ?_⟩
    · show g • y s = g • (0 : N)
      rw [hy, hb s hs, dd_deg r a' _ ha0 s hs, sub_zero, smul_zero]
    · show g • dd r y s = g • c s
      have e : b = fun s => dd r a' s + (LinearMap.lsmul R N g) (y s) := by
        funext s
        rw [LinearMap.lsmul_apply, hy, add_sub_cancel]
      rw [← hbc', e, dd_add, dd_dd, dd_map, zero_add, LinearMap.lsmul_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StationaryPhaseModel
section
theorem UpperTheory.Reformulated.B.StationaryPhaseModel.matIrr_conj :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {U : Subgroup Γ} {a a' : Γ → Matrix (Fin n) (Fin n) k},
      UpperTheory.V.U3.MatIrr U a →
        ∀ (h : GL (Fin n) k),
          (∀ g ∈ U, a' g = (↑h : Matrix (Fin n) (Fin n) k) * a g * (↑h⁻¹ : Matrix (Fin n) (Fin n) k)) →
            UpperTheory.V.U3.MatIrr U a' := by
  intro Γ k _ _ n U a a' hirr h hconj
  refine UpperTheory.Reformulated.B.G5.matIrr_conj h (fun g hg => ?_) hirr
  rw [hconj g hg, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
end

