module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDuality
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.InvColim

theorem colim_equiv {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G]
    [CompactSpace G] {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M) (hmono : Monotone N)
    (hopen : ∀ n, IsOpen (N n : Set M)) (hcov : ∀ x, ∃ n, x ∈ N n) (hfg : ∀ n, IsFGTop O (N n)) :
    ∃ e : H2 (twist ε M) ≃ₗ[O] M, ∀ n (z : H2 (twist ε (N n))),
      e (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val
        (twist_map ε (N n).subtype) z) = Θ.θ (N n) (hfg n) z := by
  have hinj := _root_.GlobalTheory.map_H2_subtype_injective_of_union Θ N hmono hopen hcov hfg
  have hsurj := _root_.GlobalTheory.h2_twist_exists_of_iUnion_open ε N hmono hopen hcov
  let ι : ∀ n, H2 (twist ε (N n)) →ₗ[O] H2 (twist ε M) := fun n =>
    mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)
  let ψ : ∀ n, N n →ₗ[O] H2 (twist ε M) := fun n => ι n ∘ₗ (Θ.θ (N n) (hfg n)).symm.toLinearMap
  have hup : ∀ n m (h : n ≤ m) (y : N n), ψ m (Submodule.inclusion (hmono h) y) = ψ n y := by
    intro n m h y
    let inc := Submodule.inclusion (hmono h)
    have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
    have hι : ∀ w, ι m (mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc) w) = ι n w := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H w => rfl
    have hw : (Θ.θ (N m) (hfg m)).symm (inc y) = mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc)
        ((Θ.θ (N n) (hfg n)).symm y) := by
      rw [LinearEquiv.symm_apply_eq, Θ.nat _ _ (hfg n) (hfg m) inc hinc, LinearEquiv.apply_symm_apply]
    show ι m ((Θ.θ (N m) (hfg m)).symm (inc y)) = ι n ((Θ.θ (N n) (hfg n)).symm y)
    rw [hw, hι]
  have hind : ∀ n m (y : M) (hn : y ∈ N n) (hm : y ∈ N m), ψ n ⟨y, hn⟩ = ψ m ⟨y, hm⟩ := by
    intro n m y hn hm
    rw [← hup n (max n m) (le_max_left _ _), ← hup m (max n m) (le_max_right _ _)]
    rfl
  let nn : M → ℕ := fun y => (hcov y).choose
  have hnn : ∀ y, y ∈ N (nn y) := fun y => (hcov y).choose_spec
  let Ψ : M →ₗ[O] H2 (twist ε M) :=
    { toFun := fun y => ψ (nn y) ⟨y, hnn y⟩
      map_add' := fun y y' => by
        have hy : y ∈ N (max (nn y) (nn y')) := hmono (le_max_left _ _) (hnn y)
        have hy' : y' ∈ N (max (nn y) (nn y')) := hmono (le_max_right _ _) (hnn y')
        refine (hind _ _ (y + y') (hnn _) (add_mem hy hy')).trans ?_
        rw [hind _ _ y (hnn y) hy, hind _ _ y' (hnn y') hy', ← map_add (f := _)]
        rfl
      map_smul' := fun c y => by
        refine (hind _ (nn y) (c • y) (hnn _) (Submodule.smul_mem _ c (hnn y))).trans ?_
        rw [RingHom.id_apply, ← map_smul]
        rfl }
  have hΨ : ∀ n (y : N n), Ψ y = ψ n y := fun n y => hind _ n y (hnn _) y.2
  have hΨi : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, hn⟩ := hcov y
    have h1 : ψ n ⟨y, hn⟩ = 0 := (hΨ n ⟨y, hn⟩).symm.trans hy
    have h2 : (Θ.θ (N n) (hfg n)).symm ⟨y, hn⟩ = 0 := hinj n (by rw [map_zero]; exact h1)
    have h3 : (⟨y, hn⟩ : N n) = 0 := by simpa using h2
    exact congrArg Subtype.val h3
  have hΨs : Function.Surjective Ψ := by
    intro z
    obtain ⟨n, z', hz'⟩ := hsurj z
    refine ⟨(Θ.θ (N n) (hfg n) z' : M), ?_⟩
    rw [hΨ n]
    show ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z')) = z
    rw [LinearEquiv.symm_apply_apply]
    exact hz'
  refine ⟨(LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩).symm, fun n z => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  show _ = Ψ _
  rw [hΨ n]
  show _ = ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z))
  rw [LinearEquiv.symm_apply_apply]

section Lat
variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]

theorem frac_isFGTop (hO : PadicCoeff p O) (hF : FracTop O) (n : ℕ) :
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := _root_.GlobalTheory.isFGTop_comap_lsmul_one hO hF n

theorem frac_cover (hO : PadicCoeff p O) (y : FractionRing O) :
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := _root_.GlobalTheory.padicCoeff_exists_pow_smul_mem_one hO y

theorem ko_discrete (hF : FracTop O) : DiscreteTopology (KO O) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have h1 : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext y; simp [Submodule.mem_one]
  have h2 : ({0} : Set (KO O)) =
      (1 : Submodule O (FractionRing O)).mkQ '' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext x
    constructor
    · rintro rfl
      exact ⟨0, zero_mem _, map_zero _⟩
    · rintro ⟨y, hy, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 hy
  rw [h2]
  exact (Submodule.isOpenQuotientMap_mkQ _).isOpenMap _ (h1 ▸ hF.emb.isOpen_range)

end Lat

theorem inv_iso (hT : Formalism.GaloisCohomology.LocalTateDualityK) : InvIso := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hε
  obtain ⟨Θ⟩ := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT hK hO i hε
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI := ko_discrete hF
  let F : ℕ → Submodule O (FractionRing O) := fun n =>
    (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  let T : ℕ → Submodule O (KO O) := fun n => LinearMap.ker (LinearMap.lsmul O (KO O) ((p : O) ^ n))
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun n y hy => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hy
    refine Submodule.mem_one.2 ⟨(p : O) * a, ?_⟩
    simp only [LinearMap.lsmul_apply] at ha ⊢
    rw [map_mul, ha, pow_succ, mul_comm _ (p : O), mul_smul, Algebra.smul_def (p : O) (((p : O) ^ n) • y)]
  have hFo : ∀ n, IsOpen (F n : Set (FractionRing O)) := fun n => by
    have : (F n : Set (FractionRing O)) =
        (fun y : FractionRing O => ((p : O) ^ n) • y) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
      ext y; simp [F, Submodule.mem_one]
    rw [this]
    exact hF.emb.isOpen_range.preimage (continuous_const_smul _)
  have hFfg := frac_isFGTop hO hF
  have hred : ∀ n, ∀ y ∈ F n, toKO O y ∈ T n := fun n y hy => by
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply, F, Submodule.mem_comap] at hy ⊢
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hy
  have hTm : Monotone T := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [pow_succ, mul_comm, mul_smul, hx, smul_zero]
  have hTo : ∀ n, IsOpen (T n : Set (KO O)) := fun n => isOpen_discrete _
  have hTc : ∀ x, ∃ n, x ∈ T n := fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := frac_cover hO y
    exact ⟨n, hred n y hn⟩
  have hTsurj : ∀ n, (F n).map (toKO O) = T n := fun n => by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun y hy => hred n y hy) fun x hx => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨y, ?_, rfl⟩
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    exact hx
  have hTfg : ∀ n, IsFGTop O (T n) := fun n => by
    refine ⟨?_, inferInstance, inferInstance⟩
    have := (hFfg n).fg
    rw [← hTsurj n, Module.Finite.iff_fg]
    exact Submodule.FG.map _ (Module.Finite.iff_fg.1 this)
  obtain ⟨eF, heF⟩ := colim_equiv Θ F hFm hFo (frac_cover hO) hFfg
  obtain ⟨eT, heT⟩ := colim_equiv Θ T hTm hTo hTc hTfg
  refine ⟨eT, eF, fun z => ?_⟩
  obtain ⟨n, hn⟩ := frac_cover hO (eF z)
  set z' := (Θ.θ (F n) (hFfg n)).symm ⟨eF z, hn⟩
  have hz : mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val
      (twist_map ε (F n).subtype) z' = z := eF.injective (by rw [heF, LinearEquiv.apply_symm_apply])
  let red : F n →ₗ[O] T n := ((toKO O).comp (F n).subtype).codRestrict (T n) fun y => hred n y y.2
  have hredc : Continuous red := (toKO_cont.comp continuous_subtype_val).subtype_mk _
  have e3 : mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε)
      (mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val (twist_map ε _) z') =
      mapH2 (twist ε (T n)) (twist ε (KO O)) (T n).subtype continuous_subtype_val (twist_map ε _)
        (mapH2 (twist ε (F n)) (twist ε (T n)) red hredc (twist_map ε red) z') := by
    induction z' using Submodule.Quotient.induction_on with
    | H w => rfl
  rw [← hz, e3, heT, Θ.nat _ _ (hFfg n) (hTfg n) red hredc]
  refine Eq.trans ?_ (congrArg (toKO O) (heF n z')).symm
  rfl

end GlobalTheory.InvColim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Matrix

namespace GlobalTheory.ThetaUnfold

section Abstract

variable {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_unfold (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → ℝ≥0∞) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEMeasurable f μ) :
    ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫⁻ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Δ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) ∩ 𝓕' : Set G) = 𝓕' ∩ e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    rw [and_comm]
    refine and_congr_right fun _ => ?_
    rw [he]
    simp [mul_assoc]
  calc ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∑' i, ∫⁻ g in 𝓕, f (r i * g) ∂μ :=
        lintegral_tsum fun i => (hm.comp_quasiMeasurePreserving
          (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
    _ = ∑' i, ∫⁻ g in r i • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [(measurePreserving_mul_left μ (r i)).setLIntegral_comp_emb
          (measurableEmbedding_mulLeft (r i)) f 𝓕]
        rfl
    _ = ∑' i, ∑' δ : Δ, ∫⁻ g in 𝓕' ∩ e (δ, i) • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [h𝓕'.setLIntegral_eq_tsum' f (r i • 𝓕)]
        refine tsum_congr fun δ => ?_
        rw [hset]
        congr 1
        funext g
        exact hf _ (δ⁻¹).2 g
    _ = ∑' p : Δ × ι, ∫⁻ g in 𝓕' ∩ e p • 𝓕, f g ∂μ := by
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = ∑' γ : Γ, ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ := e.tsum_eq (fun γ => ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ)
    _ = ∫⁻ g in 𝓕', f g ∂μ := (h𝓕.setLIntegral_eq_tsum f 𝓕').symm

theorem isFundamentalDomain_iUnion (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : IsFundamentalDomain Δ (⋃ i, r i • 𝓕) μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) : Set G) = e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
    rw [he]
    simp [mul_assoc]
  refine ⟨.iUnion fun i => h𝓕.nullMeasurableSet.smul (r i), h𝓕.ae_covers.mono ?_, fun δ δ' hδ => ?_⟩
  · rintro x ⟨γ, hγ⟩
    refine ⟨(e.symm γ⁻¹).1⁻¹, Set.mem_iUnion.2 ⟨(e.symm γ⁻¹).2, ?_⟩⟩
    rw [← Set.mem_smul_set_iff_inv_smul_mem, hset, Prod.mk.eta, e.apply_symm_apply,
      Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  · simp only [Function.onFun, Set.smul_set_iUnion, hset, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    exact fun i j => h𝓕.aedisjoint fun h => hδ (by simpa using congrArg Prod.fst (e.injective h))

theorem integral_unfold {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → V) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ g in 𝓕, ∑' i, ‖f (r i * g)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun i => ‖f (r i * g)‖) ∧ IntegrableOn (fun g => ∑' i, f (r i * g)) 𝓕 μ ∧
      IntegrableOn f 𝓕' μ ∧ ∫ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hS := isFundamentalDomain_iUnion μ Γ Δ r e he h𝓕
  have hf' : ∀ (δ : Δ) (g : G), f (δ • g) = f g := fun δ g => hf δ δ.2 g
  have hmi : ∀ i, AEStronglyMeasurable (fun g => f (r i * g)) (μ.restrict 𝓕) := fun i =>
    (hm.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
  have hI : IntegrableOn f 𝓕' μ := ⟨hm.restrict, by
    have := lintegral_unfold μ Γ Δ r e he h𝓕 h𝓕' (fun g => ‖f g‖ₑ) (fun δ h g => by rw [hf δ h]) hm.enorm
    exact lt_top_iff_ne_top.2 (this ▸ hfin)⟩
  have hr : ∀ i, (r i • 𝓕 : Set G) = e (1, i) • 𝓕 := fun i => by
    rw [Subgroup.smul_def, he]; simp
  refine ⟨?_, ⟨AEStronglyMeasurable.tsum hmi, ?_⟩, hI, ?_⟩
  · filter_upwards [ae_lt_top' (AEMeasurable.tsum fun i => (hmi i).enorm) hfin] with g hg
    have := ENNReal.summable_toReal hg.ne
    simpa using this
  · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) hfin.lt_top
  · rw [integral_tsum hmi (by rwa [← lintegral_tsum fun i => (hmi i).enorm]), h𝓕'.setIntegral_eq hS hf',
      integral_iUnion_ae (fun i => h𝓕.nullMeasurableSet.smul (r i))
        (fun i j hij => by
          simp only [Function.onFun, hr]
          exact h𝓕.aedisjoint fun h => hij (by simpa using congrArg Prod.snd (e.injective h)))
        ((h𝓕'.integrableOn_iff hS hf').1 hI)]
    refine tsum_congr fun i => ?_
    exact ((measurePreserving_mul_left μ (r i)).setIntegral_image_emb (measurableEmbedding_mulLeft (r i)) f 𝓕).symm

end Abstract

section Concrete

open GlobalTheory.CuspRep

variable {E : Type} [Field E] {a : ℕ}

theorem exists_vecMul_eq {v ξ : Fin a → E} (hv : v ≠ 0) (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin a) E, v ᵥ* (γ : Matrix (Fin a) (Fin a) E) = ξ := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton E _ v hv).symm.trans (LinearEquiv.toSpanNonzeroSingleton E _ ξ hξ))
  have h1 := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one E _ v hv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set A := LinearMap.toMatrix' g.toLinearMap
  set B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  have hBA : B * A = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Aᵀ, Bᵀ, by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]⟩, ?_⟩
  change v ᵥ* Aᵀ = ξ
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  first | exact h1 | exact h1.symm

variable [NumberField E]

theorem vecMul_ratGL_mul (ξ : Fin a → E) (γ : GL (Fin a) E) (g : GA E a) :
    (algebraMap E (Ad E) ∘ ξ) ᵥ* (ratGL E a γ * g).val = (algebraMap E (Ad E) ∘ (ξ ᵥ* γ.val)) ᵥ* g.val := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ratGL, Matrix.vecMul, dotProduct, map_sum]

theorem ratGL_injective : Function.Injective (ratGL E a) := fun _ _ h => by
  ext i j
  exact NumberField.AdeleRing.algebraMap_injective _ E
    (congrArg (fun z : GA E a => (z : Matrix (Fin a) (Fin a) (Ad E)) i j) h)

theorem countable_range_ratGL : Countable (ratGL E a).range := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
  haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
  exact (ratGL E a).rangeRestrict_surjective.countable

theorem exists_transversal {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)}
    (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v) :
    ∃ (γ : {ξ : Fin a → E // ξ ≠ 0} → GL (Fin a) E) (e : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} ≃ (ratGL E a).range),
      (∀ ξ, v ᵥ* (γ ξ).val = ξ.1) ∧ ∀ p, (e p : GA E a) = p.1 * ratGL E a (γ p.2) := by
  choose γ hγ using fun ξ : {ξ : Fin a → E // ξ ≠ 0} => exists_vecMul_eq hv ξ.2
  let φ : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} → (ratGL E a).range := fun p =>
    ⟨p.1 * ratGL E a (γ p.2), mul_mem (Subgroup.map_le_range _ _ p.1.2) ⟨_, rfl⟩⟩
  refine ⟨γ, Equiv.ofBijective φ ⟨?_, ?_⟩, hγ, fun _ => rfl⟩
  · rintro ⟨⟨_, δ, hδ, rfl⟩, ξ⟩ ⟨⟨_, δ', hδ', rfl⟩, ξ'⟩ h
    have h1 : δ * γ ξ = δ' * γ ξ' := ratGL_injective (by simpa only [map_mul] using congrArg Subtype.val h)
    have h2 : ξ = ξ' := Subtype.ext (by
      have := congrArg (fun x : GL (Fin a) E => v ᵥ* x.val) h1
      simpa only [Units.val_mul, ← Matrix.vecMul_vecMul, (hP _).1 hδ, (hP _).1 hδ', hγ] using this)
    subst h2
    obtain rfl := mul_right_cancel h1
    rfl
  · rintro ⟨_, x, rfl⟩
    have h0 : v ᵥ* x.val ≠ 0 := fun h => hv (by
      have := congrArg (· ᵥ* (x⁻¹).val) h
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)
    have h1 : x * (γ ⟨_, h0⟩)⁻¹ ∈ P := (hP _).2 (by
      have h2 : v ᵥ* (γ ⟨_, h0⟩).val = v ᵥ* x.val := hγ _
      generalize γ ⟨_, h0⟩ = y at h2 ⊢
      rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h2, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one])
    refine ⟨⟨⟨_, _, h1, rfl⟩, ⟨_, h0⟩⟩, Subtype.ext ?_⟩
    change ratGL E a _ * ratGL E a _ = _
    rw [← map_mul, inv_mul_cancel_right]

section Stabiliser

variable [MeasurableSpace (GA E a)] [MeasurableMul (GA E a)] (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]
  {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)} (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v)
  {𝓕 𝓕' : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
  (h𝓕' : IsFundamentalDomain (P.map (ratGL E a)) 𝓕' μ)

include hv hP h𝓕 h𝓕'

theorem lintegral_tsum_vecMul (F : GA E a → (Fin a → Ad E) → ℝ≥0∞) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ) :
    ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫⁻ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := lintegral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

theorem integral_tsum_vecMul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : GA E a → (Fin a → Ad E) → V) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEStronglyMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ)
    (hfin : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖) ∧
    IntegrableOn (fun g => ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)) 𝓕 μ ∧
    IntegrableOn (fun g => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) 𝓕' μ ∧
    ∫ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := integral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
    (by simpa only [vecMul_ratGL_mul, hF, hγ] using hfin)
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

end Stabiliser

end Concrete

end GlobalTheory.ThetaUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDegPosAndSumLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.LocDegPos

theorem locDeg_pos_and_sum_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → (∀ v : HeightOneSpectrum (𝓞 E), 0 < Formalism.MainNotions.N.locDeg E v) ∧ ∀ s : Finset (HeightOneSpectrum (𝓞 E)), (∀ v ∈ s, v ∈ placesOver E l) → ∑ v ∈ s, Formalism.MainNotions.N.locDeg E v ≤ Module.finrank ℚ E := by
  intro E _ _ l hl
  refine ⟨fun v => ?_, fun s hs => ?_⟩
  · haveI := v.isPrime
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  · classical
    haveI : Fact l.Prime := ⟨hl⟩
    have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
      have hf : ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).Finite :=
        IsDedekindDomain.primesOver_finite _ _
      refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
        (hf.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ?_⟩
      rw [Ideal.liesOver_span_iff v.isPrime.ne_top (Nat.prime_iff_prime_int.1 hl)]
      simpa using hv
    letI : Fintype {v : HeightOneSpectrum (𝓞 E) // ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := hfin.fintype
    have hsum := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg E l
    rw [← hsum, ← Finset.sum_subtype_of_mem (fun v => Formalism.MainNotions.N.locDeg E v) (p := fun v : HeightOneSpectrum (𝓞 E) => ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (fun v hv => hs v hv)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end GlobalTheory.Proof.LocDegPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibniz
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal.Conn

theorem pow_apply_smul_nsmul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      k.choose p • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_choose_succ_nsmul
        (fun i j => (fun τ => (⇑(PowerSeries.derivative (R := K)))^[i] (f τ)) • (C.nabla ^ j) v) k,
        pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [map_nsmul, C.leibniz, smul_add, add_comm]
    congr 2
    · rw [show k + 1 - p = k - p + 1 by omega, pow_succ', mul_apply_eq_comp]
    · congr 1
      funext τ
      rw [Function.iterate_succ_apply']

theorem pow_apply_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  rw [pow_apply_smul_nsmul]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm

end GlobalTheory.BKReal.Conn
end

