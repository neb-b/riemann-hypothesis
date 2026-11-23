module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfPadicCoeff
section
open ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory

theorem isPrecomplete_of_compact_isAdic {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (h : IsAdic I) : IsPrecomplete I O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := exists_clusterPt_of_compactSpace (Filter.map f Filter.atTop)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((I ^ n : Ideal O) : Set O) := (isAdic_iff.mp h).1 n
  have hclosed : IsClosed ((I ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen
  have hc : IsClosed {x : O | f n - x ∈ I ^ n} :=
    hclosed.preimage (f := fun x => f n - x) (continuous_const.sub continuous_id)
  have hmem : {x : O | f n - x ∈ I ^ n} ∈ Filter.map f Filter.atTop := by
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hLm : L ∈ {x : O | f n - x ∈ I ^ n} := by
    rw [← hc.closure_eq]
    exact mem_closure_iff_clusterPt.mpr (hL.mono (Filter.le_principal_iff.mpr hmem))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hLm

theorem isAdicComplete_of_padicCoeff {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (h : PadicCoeff p O) : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  haveI := h.ring
  haveI := h.compact
  haveI := isPrecomplete_of_compact_isAdic _ h.adic
  haveI : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  exact ⟨⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFGTopPPowInverseLattice
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem fractionRing_t2_of_openEmbedding {O : Type} [CommRing O] [IsDomain O]
    [TopologicalSpace O] [T2Space O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)]
    (he : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) : T2Space (FractionRing O) := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  set ι := algebraMap O (FractionRing O)
  have hsub : (ι ⁻¹' {x}).Subsingleton := fun a ha b hb => he.injective (ha.trans hb.symm)
  have hcl : IsClosed (ι ⁻¹' {x}) := hsub.isClosed
  refine ⟨ι '' (ι ⁻¹' {x})ᶜ, ?_, ?_⟩
  · refine (he.isOpenMap _ hcl.isOpen_compl).mem_nhds ⟨0, ?_, map_zero ι⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, map_zero]
    exact fun h => hx h.symm
  · rintro ⟨a, ha, hax⟩
    exact ha hax

theorem isFGTop_comap_lsmul_one : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  intro p O _ _ _ _ _ _ _ hO hF n
  haveI := hO.t2
  haveI := fractionRing_t2_of_openEmbedding hF.emb
  set S := (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  refine ⟨?_, inferInstance, inferInstance⟩
  haveI : Module.Finite O (1 : Submodule O (FractionRing O)) := by
    rw [Module.Finite.iff_fg, Submodule.one_eq_span]
    exact Submodule.fg_span (Set.finite_singleton _)
  haveI : IsNoetherian O (1 : Submodule O (FractionRing O)) := inferInstance
  let f : S →ₗ[O] (1 : Submodule O (FractionRing O)) :=
    (LinearMap.lsmul O (FractionRing O) ((p : O) ^ n)).restrict (fun x hx => hx)
  refine Module.Finite.of_injective f ?_
  intro a b hab
  have h := congrArg Subtype.val hab
  simp only [f, LinearMap.restrict_apply, LinearMap.lsmul_apply] at h
  have hp : ((p : O) ^ n) ≠ 0 := pow_ne_zero _ hO.p_ne
  exact Subtype.ext (smul_right_injective (FractionRing O) hp h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapH2SubtypeInjective
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem map_H2_subtype_injective_of_union : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ (hfg : ∀ n, IsFGTop O (N n)) (n : ℕ),
      Function.Injective (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)) := by
  intro O _ _ G _ _ _ ε Θ M _ _ _ _ _ N hmono hopen hcov hfg n
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H f =>
  unfold mapH2 at hz
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz

  have hK : IsCompact (Set.range c) := isCompact_range hc
  obtain ⟨i, hi⟩ := hK.elim_directed_cover (fun k => (N k : Set M)) hopen
    (fun x _ => Set.mem_iUnion.2 (hcov x)) (hmono.directed_le)
  set m := max n i with hm
  have hnm : N n ≤ N m := hmono (le_max_left n i)
  have him : ∀ g, c g ∈ N m := fun g => hmono (le_max_right n i) (hi ⟨g, rfl⟩)
  have hincl : Continuous (Submodule.inclusion hnm) := continuous_inclusion hnm
  have hzero : mapH2 (twist ε (N n)) (twist ε (N m)) (Submodule.inclusion hnm) hincl
      (twist_map ε (Submodule.inclusion hnm)) (Submodule.Quotient.mk f) = 0 := by
    unfold mapH2
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => ⟨c g, him g⟩, hc.subtype_mk him, ?_⟩
    funext p
    apply Subtype.ext
    have e := congrFun hcf p
    simp [d1, twist] at e ⊢
    rw [e]
    rfl
  have hnat := Θ.nat (N n) (N m) (hfg n) (hfg m) (Submodule.inclusion hnm) hincl (Submodule.Quotient.mk f)
  rw [hzero, (Θ.θ (N m) (hfg m)).map_zero] at hnat
  have h0 : Θ.θ (N n) (hfg n) (Submodule.Quotient.mk f) = 0 := by
    have := hnat.symm
    rw [← (Submodule.inclusion hnm).map_zero] at this
    exact Submodule.inclusion_injective hnm this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHom
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SubModel

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hg : IsHom A B g) :
    ∃ (K : Ob k G) (i : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A i ∧ Function.Injective i ∧ Function.Exact i g := by
  have hst : ∀ s : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (A.ρ s) := by
    intro s x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
    rw [hg, hx, map_zero]
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker g) hst)
  refine ⟨K, (LinearMap.ker g).subtype ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro s x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he]
    simp [Representation.subrepresentation]
  · exact (LinearMap.ker g).injective_subtype.comp e.symm.injective
  · intro y
    constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact f q := by
  have hst : ∀ s : G, LinearMap.range f ≤ (LinearMap.range f).comap (B.ρ s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨A.ρ s x, hf s x⟩
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range f) hst)
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range f).mkQ, ?_, ?_, ?_⟩
  · intro s x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    simp [Representation.quotient]
  · exact e.surjective.comp (LinearMap.range f).mkQ_surjective
  · intro y
    simp [Submodule.Quotient.mk_eq_zero]

theorem IsHom.comp' {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) := by
  intro s x
  simp only [LinearMap.comp_apply]
  rw [hf, hg]

theorem model_pre : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  intro k G _ _ l n _ _ _ R F r Dt M A B f N hf hfi hN
  obtain ⟨C, Nb, A₁, j, p, hb, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨Q, q, hq, hqs, hfq⟩ := exists_coker A B f hf
  have hqp : IsHom A₁ Q (q ∘ₗ p) := IsHom.comp' hp hq
  obtain ⟨K, i, hi, hii, hex⟩ := exists_ker A₁ Q (q ∘ₗ p) hqp
  have hr : ∀ x, (p ∘ₗ i) x ∈ LinearMap.range f := fun x => (hfq _).1 ((hex _).2 ⟨x, rfl⟩)
  let p' : (Fin K.m → k) →ₗ[k] (Fin A.m → k) :=
    (LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (p ∘ₗ i) hr
  have hfp : ∀ x, f (p' x) = p (i x) := by
    intro x
    have := congrArg Subtype.val ((LinearEquiv.ofInjective f hfi).apply_symm_apply
      (LinearMap.codRestrict _ (p ∘ₗ i) hr x))
    exact this
  have hp' : IsHom K A p' := by
    intro s x
    apply hfi
    rw [hfp, hf, hfp, hi, hp]
  have hp's : Function.Surjective p' := by
    intro a
    obtain ⟨y, hy⟩ := hps (f a)
    have : (q ∘ₗ p) y = 0 := by
      rw [LinearMap.comp_apply, hy]
      exact (hfq _).2 ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (hex _).1 this
    exact ⟨x, hfi (by rw [hfp, hy])⟩
  have oC : F.Obj C := M.base_obj _ _ hb
  have o1 : F.Obj A₁ := F.obj_sub _ _ _ hj hji oC
  have oB : F.Obj B := F.obj_quot _ _ _ hp hps o1
  have oA : F.Obj A := F.obj_sub _ _ _ hf hfi oB
  have oK : F.Obj K := F.obj_sub _ _ _ hi hii o1
  have oQ : F.Obj Q := F.obj_quot _ _ _ hq hqs oB
  have hcomm : f ∘ₗ p' = p ∘ₗ i := LinearMap.ext hfp
  have hsq : ∀ a x, F.map A B f a (F.map K A p' a x) = F.map A₁ B p a (F.map K A₁ i a x) := by
    intro a x
    have h1 := F.map_comp K A B p' f oK oA oB hp' hf a
    have h2 := F.map_comp K A₁ B i p oK o1 oB hi hp a
    rw [hcomm, h2] at h1
    exact (LinearMap.congr_fun h1 x).symm
  have e1 := GlobalTheory.T.exact_map_of_exact F A B Q f q oB hf hq hfi hqs hfq
  have e2 := GlobalTheory.T.exact_map_of_exact F K A₁ Q i (q ∘ₗ p) o1 hi hqp hii (hqs.comp hps) hex
  refine ⟨C, Nb, K, j ∘ₗ i, p', hb, IsHom.comp' hi hj, hji.comp hii, hp', hp's, ?_⟩
  funext a
  ext x
  simp only [DFun.pre, DFun.push, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    F.map_comp K A₁ C i j oK o1 oC hi hj a, LinearMap.comp_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : F.map A₁ Q (q ∘ₗ p) a y = 0 := by
      rw [F.map_comp A₁ B Q p q o1 oB oQ hp hq a, LinearMap.comp_apply, hyx]
      exact (e1 a _).2 ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (e2 a _).1 this
    exact ⟨z, hy, F.map_inj A B f oA oB hf hfi a (by rw [hsq, hyx])⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, (hsq a z).symm⟩

end GlobalTheory.Models.SubModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquiv
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.TransportH2

variable {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ]
  [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem apply_symm' (i : G ≃ₜ* Γ) (y : Γ) : i (i.symm y) = y := i.apply_symm_apply y

theorem symm_apply' (i : G ≃ₜ* Γ) (x : G) : i.symm (i x) = x := i.symm_apply_apply x

noncomputable def cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Z2 rho ≃ₗ[R] Z2 (rho.comp i.toMulEquiv.toMonoidHom) :=
  { restrictCocycles2 rho i.toMulEquiv.toMonoidHom i.continuous with
    invFun := fun f => ⟨fun p => f.1 (i.symm p.1, i.symm p.2),
      f.2.1.comp (i.symm.continuous.prodMap i.symm.continuous), fun g h k => by
        have e := f.2.2 (i.symm g) (i.symm h) (i.symm k)
        have e' : (rho.comp i.toMulEquiv.toMonoidHom) (i.symm g) = rho g := by
          show rho (i (i.symm g)) = rho g
          rw [apply_symm']
        rw [e'] at e
        show rho g (f.1 (i.symm h, i.symm k)) - f.1 (i.symm (g * h), i.symm k) +
          f.1 (i.symm g, i.symm (h * k)) - f.1 (i.symm g, i.symm h) = 0
        rw [map_mul, map_mul]
        exact e⟩
    left_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i (i.symm p.1), i (i.symm p.2)) = f.1 p
      rw [apply_symm', apply_symm']
    right_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i.symm (i p.1), i.symm (i p.2)) = f.1 p
      rw [symm_apply', symm_apply'] }

theorem map_cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    ((B2 rho).comap (Z2 rho).subtype).map (cocycleEquiv i rho : Z2 rho →ₗ[R] _) =
      (B2 (rho.comp i.toMulEquiv.toMonoidHom)).comap
        (Z2 (rho.comp i.toMulEquiv.toMonoidHom)).subtype := by
  ext f
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf'
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ i, hc.comp i.continuous, ?_⟩
    funext p
    have e := congrFun hcf (i p.1, i p.2)
    change _ = f'.1 (i p.1, i p.2)
    rw [← e]
    simp [d1]
    rfl
  · intro hf
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hf
    refine ⟨(cocycleEquiv i rho).symm f, (separated_dvr_second_cohomology_mem rho _).2
      ⟨c ∘ i.symm, hc.comp i.symm.continuous, ?_⟩, (cocycleEquiv i rho).apply_symm_apply f⟩
    funext p
    have e := congrFun hcf (i.symm p.1, i.symm p.2)
    change _ = f.1 (i.symm p.1, i.symm p.2)
    rw [← e]
    simp [d1, symm_apply']
    exact congrArg (fun g => rho g (c (i.symm p.2))) (apply_symm' i p.1).symm

theorem natCard_H2_comp (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) :=
  (Nat.card_congr (Submodule.Quotient.equiv _ _ (cocycleEquiv i rho)
    (map_cocycleEquiv i rho)).toEquiv).symm

end GlobalTheory.TransportH2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumberFieldPrimeZetaSumAddLogIsBigO
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.ChebCyc

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_add_log_sub_one_isBigO_one (K : Type) [Field K] [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) + Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hT := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hr : ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ ≠ 0 := by
    simp [dedekindZeta_residue_ne_zero]
  have hL := ((Real.continuousAt_log hr).tendsto.comp hT).isBigO_one ℝ
  refine hL.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  rw [norm_mul, _root_.GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp K hs]
  have hs1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hs1, Real.log_mul (sub_ne_zero.2 hs.ne') (Real.exp_pos _).ne', Real.log_exp]
  ring

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one (K : Type) [Field K]
    [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hN : ∀ P : HeightOneSpectrum (𝓞 K), 2 ≤ Ideal.absNorm P.asIdeal :=
    fun P => _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
  have hC := _root_.GlobalTheory.Mem.RayPrimes.logSum_sub_bounded (fun P : HeightOneSpectrum (𝓞 K) =>
    Ideal.absNorm P.asIdeal) hN (fun _ => 1) (fun _ => by simp)
    (fun s hs => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2)
  have hC' : (fun s : ℝ => (((∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hC.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
    congr 1
    · refine tsum_congr fun P => ?_
      rw [_root_.GlobalTheory.Mem.ZetaPole.ofReal_logFactor (by linarith [hN P]) (by linarith), one_mul]
    · refine tsum_congr fun P => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _), one_mul, Complex.ofReal_natCast,
        Complex.ofReal_neg]
  rw [← isBigO_norm_left]
  exact hC'.norm_left.congr_left fun s => Complex.norm_real _


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.ChebCyc.primeSum_add_log_isBigO : ∀ (K : Type) [Field K] [NumberField K], (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  intro K _ _
  refine ((tsum_logFactor_add_log_sub_one_isBigO_one K).sub
    (tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one K)).congr_left fun s => ?_
  ring

end GlobalTheory.ChebCyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem quot_pow_maximalIdeal_discrete_finite :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ,
      DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p O _ _ _ _ _ hO k
  haveI : CompactSpace O := hO.compact
  set I : Ideal O := IsLocalRing.maximalIdeal O ^ k with hI
  have hopen : IsOpen ((I : Ideal O) : Set O) := (isAdic_iff.mp hO.adic).1 k
  have hdisc : DiscreteTopology (O ⧸ I) := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : (Ideal.Quotient.mk I) '' (I : Set O) = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
      · rintro rfl
        exact ⟨0, I.zero_mem, map_zero _⟩
    rw [← himg]
    exact QuotientRing.isOpenMap_coe I _ hopen
  refine ⟨hdisc, ?_⟩
  haveI : CompactSpace (O ⧸ I) := Quotient.compactSpace
  exact finite_of_compact_of_discrete

end GlobalTheory.NatQuot
end

