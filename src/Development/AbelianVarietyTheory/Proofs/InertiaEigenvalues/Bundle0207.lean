module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnramA

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardUnramifiedLevelTrivialAction
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def LCHomLev {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (M : Type)
    [AddCommGroup M] [Module O M] (c : O) (I : Subgroup G) : Type :=
  {f : G → Lev M c // IsLocallyConstant f ∧ (∀ a b, f (a * b) = f a + f b) ∧ ∀ g ∈ I, f g = 0}

section Triv

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

theorem mem_coboundaries_of_trivial {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m) (x : G → M) :
    x ∈ Formalism.NG.coB1 ρ ↔ x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    funext g
    show ρ g v - v = 0
    rw [hρ, sub_self]
  · rintro rfl
    exact zero_mem _

theorem mk_eq_zero_of_triv {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m)
    (z : Formalism.NG.coZ1s ρ) : (Submodule.Quotient.mk z : Formalism.NG.H1z ρ) = 0 ↔ (z : G → M) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    mem_coboundaries_of_trivial hρ]

variable [TopologicalSpace G]

theorem card_torsion_eq_locConstHom_trivial_action (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m)
    (I : Subgroup G) (c : O) :
    Nat.card (LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (LCHomLev M c I) := by
  have hres : ∀ (g : I) (m : M), Formalism.NG.resRep ρ I g m = m := fun g m => hρ g m
  let coc : LCHomLev M c I → Formalism.NG.coZ1s ρ := fun f =>
    ⟨fun g => (f.1 g).val, fun a b => by
      show (f.1 (a * b)).val = (f.1 a).val + ρ a (f.1 b).val
      rw [hρ, f.2.2.1, Lev.val_add]⟩
  let F : LCHomLev M c I → LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype)) := fun f =>
    ⟨⟨⟨Submodule.Quotient.mk (coc f),
        Submodule.mem_map.2 ⟨coc f, f.2.1.comp Lev.val, rfl⟩⟩,
      by
        change (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I (coc f)) :
          Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0
        rw [mk_eq_zero_of_triv hres]
        funext g
        show (f.1 g.1).val = 0
        rw [f.2.2.2 g.1 g.2]
        rfl⟩,
      by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
        apply Subtype.ext
        apply Subtype.ext
        show c • (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) = 0
        rw [← Submodule.Quotient.mk_smul, mk_eq_zero_of_triv hρ]
        funext g
        exact Lev.smul_val (f.1 g)⟩
  have hinj : ∀ f f' : LCHomLev M c I, (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) =
      Submodule.Quotient.mk (coc f') → f = f' := by
    intro f f' h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_of_triv hρ] at h
    apply Subtype.ext
    funext g
    apply Lev.ext
    have h1 : (f.1 g).val - (f'.1 g).val = 0 := congrFun h g
    exact sub_eq_zero.1 h1
  refine (Nat.card_eq_of_bijective F ⟨fun f f' h => hinj f f' ?_, fun y => ?_⟩).symm
  · exact congrArg (fun y => y.1.1.1) h
  · obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.1.1.2
    have hk : (Submodule.Quotient.mk (c • z) : Formalism.NG.H1z ρ) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      change c • Submodule.mkQ _ z = 0
      rw [hzy]
      exact congrArg (fun w => w.1.1) (LinearMap.mem_ker.1 y.2)
    rw [mk_eq_zero_of_triv hρ] at hk
    have hz0 : ∀ g, c • (z : G → M) g = 0 := fun g => congrFun hk g
    have hu : Formalism.NG.resH1 ρ I (Submodule.mkQ _ z) = 0 := by
      rw [hzy]
      exact y.1.2
    have hu' : (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I z) :
        Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0 := hu
    rw [mk_eq_zero_of_triv hres] at hu'
    have hI0 : ∀ g ∈ I, (z : G → M) g = 0 := fun g hg => congrFun hu' ⟨g, hg⟩
    let f : LCHomLev M c I := ⟨fun g => Lev.mk ((z : G → M) g) (hz0 g),
      IsLocallyConstant.desc _ Lev.val hz (fun a b h => Lev.ext h),
      fun a b => Lev.ext (by rw [Lev.val_add, Lev.val_mk, Lev.val_mk, Lev.val_mk, z.2 a b, hρ]),
      fun g hg => Lev.ext (by rw [Lev.val_mk, hI0 g hg]; rfl)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.Quotient.mk (coc f) = y.1.1.1
    rw [← hzy]
    rfl

end Triv

section H1Triv

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {N : Type}
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

theorem H1_mk_eq_zero_iff_of_trivial {rho : Representation R Γ N} (hrho : ∀ g m, rho g m = m)
    (z : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = 0 ↔ z = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    funext g
    rw [hm g, hrho, sub_self]
    rfl
  · rintro rfl
    exact ⟨0, fun g => by rw [map_zero, sub_zero]; rfl⟩

theorem mk_mem_H1ur_of_vanish (rho : Representation R Γ N) (J : Subgroup Γ) (z : Z1 rho)
    (hz : ∀ g ∈ J, z.1 g = 0) : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J := by
  change (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
    H1 (rho.comp J.subtype)) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  exact (mem_coboundaries1 _ _).2 ⟨0, fun g => by rw [map_zero, sub_zero]; exact hz g.1 g.2⟩

theorem vanish_of_mk_mem_H1ur (rho : Representation R Γ N) (J : Subgroup Γ)
    (hJ : ∀ g ∈ J, ∀ m, rho g m = m) (z : Z1 rho)
    (hz : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J) (g : Γ) (hg : g ∈ J) : z.1 g = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
      H1 (rho.comp J.subtype)) = 0 := hz
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
  have h3 : z.1 g = rho g m - m := hm ⟨g, hg⟩
  rw [h3, hJ g hg, sub_self]

end H1Triv

theorem card_LCHomLev_eq_unrK {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m) (I : Subgroup G)
    (hI : ∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) (r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    letI := levZ (M := M) p r h
    Nat.card (LCHomLev M c I) =
      Nat.card (Formalism.GaloisCohomology.unrK (levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  letI := levZ (M := M) p r h
  let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  let F : LCHomLev M c I → Formalism.GaloisCohomology.unrK ρ' := fun f =>
    ⟨Submodule.Quotient.mk ⟨f.1 ∘ i.symm, (f.2.1.comp_continuous i.symm.continuous).continuous,
        fun a b => by
          show f.1 (i.symm (a * b)) = f.1 (i.symm a) + ρ' a (f.1 (i.symm b))
          rw [hρ', map_mul, f.2.2.1]⟩,
      mk_mem_H1ur_of_vanish ρ' _ _ fun g hg => by
        show f.1 (i.symm g) = 0
        exact f.2.2.2 _ ((hI _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hg))⟩
  refine Nat.card_eq_of_bijective F ⟨fun f f' hff => ?_, fun x => ?_⟩
  · have h1 := congrArg Subtype.val hff
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, H1_mk_eq_zero_iff_of_trivial hρ', sub_eq_zero] at h1
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    funext g
    have h3 := congrFun h2 (i g)
    simpa only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] using h3
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx : (Submodule.Quotient.mk z : H1 ρ') ∈ H1ur ρ' (Formalism.GaloisCohomology.inertiaK p K) := by
      rw [hz]; exact x.2
    let f : LCHomLev M c I := ⟨fun g => z.1 (i g),
      ((IsLocallyConstant.iff_continuous _).2 z.2.1).comp_continuous i.continuous,
      fun a b => by
        show z.1 (i (a * b)) = z.1 (i a) + z.1 (i b)
        rw [map_mul, z.2.2, hρ'],
      fun g hg => vanish_of_mk_mem_H1ur ρ' _ (fun σ _ m => hρ' σ m) z hx (i g) ((hI g).1 hg)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change Submodule.Quotient.mk _ = x.1
    rw [← hz]
    congr 1
    apply Subtype.ext
    funext g
    show z.1 (i (i.symm g)) = z.1 g
    rw [ContinuousMulEquiv.apply_symm_apply]


open scoped ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem card_unramifiedClasses_eq_card_invariants_localGalois {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    [Finite N] [TopologicalSpace N] [DiscreteTopology N]
    (rho : Representation R (Formalism.GaloisCohomology.GK p K) N) (hrho : ReciprocityTheory.Gal.ContAction rho)
    (hI : ∀ σ ∈ Formalism.GaloisCohomology.inertiaK p K, ∀ m, rho σ m = m) :
    Nat.card (Formalism.GaloisCohomology.unrK rho) = Nat.card (H0 rho) := by
  change Nat.card (Neutral.B1.H1ur rho (Neutral.B1.inertiaK p K)) = Nat.card (Neutral.B1.H0 rho)
  replace hI : ∀ σ ∈ Neutral.B1.inertiaK p K, ∀ m, rho σ m = m := hI
  rw [← ReciprocityTheory.DiscreteGroups.LocalClassField.subG_Kur_eq_inertiaK hK] at hI ⊢
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles.card_H1ur hrho hI (s := ReciprocityTheory.DiscreteGroups.LocalClassField.frobK p K)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur hK)

theorem card_unr_lev_of_triv : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {ϖ : O},
    Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O G M), (∀ g m, ρ g m = m) →
    ∀ I : Subgroup G, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) → ∀ n : ℕ,
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro p _ K hK O _ _ _ _ ϖ hϖ hp G _ _ i M _ _ e ρ hρ I hI n
  have hpn : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} :=
    Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hp) n)
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI := levZ (M := M) p n hpn
  obtain ⟨hfin, hcard⟩ := levKO_card hϖ e n
  haveI := hfin
  let ρ' := levRepZ p n hpn (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  have hcont : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ']
    exact continuous_snd
  calc _ = Nat.card (LCHomLev M (ϖ ^ n) I) := card_torsion_eq_locConstHom_trivial_action ρ hρ I (ϖ ^ n)
    _ = Nat.card (Formalism.GaloisCohomology.unrK ρ') := card_LCHomLev_eq_unrK i ρ hρ I hI n (ϖ ^ n) hpn
    _ = Nat.card (H0 ρ') :=
        card_unramifiedClasses_eq_card_invariants_localGalois hK ρ' hcont (fun σ _ m => hρ' σ m)
    _ = Nat.card (Lev M (ϖ ^ n)) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x g => hρ' g x)
    _ = _ := hcard

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFiniteOverPadicTopologiesExist
section
noncomputable section

namespace GlobalTheory.PadicTop

open IsLocalRing Topology
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop TopEx)

theorem padicCoeff_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [TopologicalSpace O]
    [IsModuleTopology ℤ_[p] O] (hinj : Function.Injective (algebraMap ℤ_[p] O)) : PadicCoeff p O := by
  haveI : Module.IsTorsionFree ℤ_[p] O := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free ℤ_[p] O := inferInstance
  haveI hR : IsTopologicalRing O := IsModuleTopology.isTopologicalRing ℤ_[p] O
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set b := Module.Free.chooseBasis ℤ_[p] O
  set e : O ≃ₗ[ℤ_[p]] (Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) := b.equivFun with he_def
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : O ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hp0 : (p : O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[p] O), Ne, ← map_zero (algebraMap ℤ_[p] O), hinj.eq_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpm : (p : O) ∈ maximalIdeal O := by
    have hmax := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[p]) (maximalIdeal O)
    have hc : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
      IsLocalRing.eq_maximalIdeal hmax
    rw [← map_natCast (algebraMap ℤ_[p] O), ← Ideal.mem_comap, hc, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have key1 : ∀ (n : ℕ) (x : O), ‖e x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → x ∈ Ideal.span {(p : O) ^ n} := by
    intro n x hx
    have hc : ∀ i, e x i ∈ Ideal.span {(p : ℤ_[p]) ^ n} := fun i =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 ((norm_le_pi_norm (e x) i).trans hx)
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hc i)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ i, c i • b i, ?_⟩
    have hx' : x = ∑ i, e x i • b i := (b.sum_equivFun x).symm
    conv_rhs => rw [hx']
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i]
    simp only [Algebra.smul_def, map_mul, map_pow, map_natCast]
    ring
  have key2 : ∀ (n : ℕ) (x : O), x ∈ Ideal.span {(p : O) ^ n} → ‖e x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    intro n x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hy : y * (p : O) ^ n = ((p : ℤ_[p]) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    refine (pi_norm_le_iff_of_nonneg (zpow_pos hpR _).le).2 fun i => ?_
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, hy, map_smul, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton'.2 ⟨e y i, mul_comm _ _⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hsub1 : ∀ n : ℕ, Ideal.span {(p : O) ^ n} ≤ maximalIdeal O ^ n := fun n =>
    Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.pow_mem_pow hpm n))
  have hsub2 : ∀ n : ℕ, maximalIdeal O ^ (k * n) ≤ Ideal.span {(p : O) ^ n} := by
    intro n
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    have hk : ϖ ^ k = ↑u⁻¹ * (p : O) := by rw [hu, Units.inv_mul_cancel_left]
    rw [pow_mul, hk, mul_pow]
    exact Dvd.intro_left _ rfl
  refine ⟨hR, h.symm.compactSpace, h.symm.t2Space, ?_, hpm, hp0⟩
  refine isAdic_iff.2 ⟨fun n => ?_, fun s hs => ?_⟩
  · have hn : e ⁻¹' Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) ∈ 𝓝 (0 : O) :=
      he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact Metric.closedBall_mem_nhds 0 (zpow_pos hpR _))
    refine AddSubgroup.isOpen_of_mem_nhds (maximalIdeal O ^ n).toAddSubgroup (g := 0)
      (Filter.mem_of_superset hn fun x hx => hsub1 n (key1 n x ?_))
    simpa using hx
  · have ht : e.symm ⁻¹' s ∈ 𝓝 (0 : Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) :=
      he'.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hs)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    refine ⟨k * n, fun x hx => ?_⟩
    have h1 := key2 n x (hsub2 n hx)
    have h2 : e x ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      refine lt_of_le_of_lt h1 ?_
      rwa [zpow_neg, zpow_natCast, ← inv_pow]
    have := hball h2
    simpa using this

section FracTopology

variable {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

def fracB (ϖ : O') (i : ℕ) : Submodule O' (FractionRing O') :=
  Submodule.span O' {algebraMap O' (FractionRing O') (ϖ ^ i)}

theorem mem_fracB {ϖ : O'} {i : ℕ} {x : FractionRing O'} :
    x ∈ fracB ϖ i ↔ ∃ c : O', x = algebraMap O' (FractionRing O') (c * ϖ ^ i) := by
  rw [fracB, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩

theorem algebraMap_mem_fracB {ϖ : O'} {i : ℕ} {x : O'} :
    algebraMap O' (FractionRing O') x ∈ fracB ϖ i ↔ ϖ ^ i ∣ x := by
  rw [mem_fracB]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [IsFractionRing.injective O' (FractionRing O') hc, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mul_comm]⟩

theorem fracB_anti (ϖ : O') {i j : ℕ} (h : i ≤ j) : fracB ϖ j ≤ fracB ϖ i := by
  rw [fracB, Submodule.span_singleton_le_iff_mem, algebraMap_mem_fracB]
  exact pow_dvd_pow ϖ h

theorem exists_pow_mul_mem {ϖ : O'} (hϖ : Irreducible ϖ) (a : FractionRing O') :
    ∃ n : ℕ, ∃ c : O', algebraMap O' (FractionRing O') (ϖ ^ n) * a =
      algebraMap O' (FractionRing O') c := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O') a
  have hs : (s : O') ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨n, ↑u⁻¹ * r, ?_⟩
  have hn : ϖ ^ n = ↑u⁻¹ * (s : O') := by rw [hu, Units.inv_mul_cancel_left]
  rw [hn, map_mul, map_mul, mul_assoc, mul_comm (algebraMap O' (FractionRing O') (s : O')) a]
  exact congrArg _ h

theorem fracB_basis {ϖ : O'} (hϖ : Irreducible ϖ) : SubmodulesRingBasis (fracB ϖ) := by
  refine { inter := ?_, leftMul := ?_, mul := ?_ }
  · intro i j
    exact ⟨max i j, le_inf (fracB_anti ϖ (le_max_left _ _)) (fracB_anti ϖ (le_max_right _ _))⟩
  · intro a i
    obtain ⟨n, c, hc⟩ := exists_pow_mul_mem hϖ a
    refine ⟨i + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d, rfl⟩ := mem_fracB.1 hx
    refine mem_fracB.2 ⟨c * d, ?_⟩
    have e : algebraMap O' (FractionRing O') (d * ϖ ^ (i + n)) =
        algebraMap O' (FractionRing O') (d * ϖ ^ i) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
      rw [← map_mul, pow_add, mul_assoc]
    show a * _ = _
    rw [e, mul_comm (algebraMap O' (FractionRing O') (d * ϖ ^ i)), ← mul_assoc, mul_comm a, hc,
      ← map_mul]
    congr 1
    ring
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_fracB.1 hx
    obtain ⟨d, rfl⟩ := mem_fracB.1 hy
    exact mem_fracB.2 ⟨c * d * ϖ ^ i, by show _ * _ = _; rw [← map_mul]; congr 1; ring⟩

end FracTopology

theorem exists_fracTop (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [TopologicalSpace O'] (hA : IsAdic (IsLocalRing.maximalIdeal O')) :
    ∃ (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')), FracTop O' := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hm : ∀ n : ℕ, ((IsLocalRing.maximalIdeal O' ^ n : Ideal O') : Set O') = {x | ϖ ^ n ∣ x} := by
    intro n
    ext x
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      SetLike.mem_coe, Ideal.mem_span_singleton]
    rfl
  have hB := fracB_basis hϖ
  have hR := hB.toRing_subgroups_basis
  let τK : TopologicalSpace (FractionRing O') := hB.topology
  have hTR : IsTopologicalRing (FractionRing O') := hR.toRingFilterBasis.isTopologicalRing
  set f := algebraMap O' (FractionRing O') with hf
  have hnK := hR.hasBasis_nhds
  have hnO := hA.hasBasis_nhds
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    refine ((hnO x).tendsto_iff (hnK (f x))).2 fun i _ => ⟨i, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm] at hz
    show f (x + z) - f x ∈ fracB ϖ i
    rw [map_add (f := _), add_sub_cancel_left]
    exact algebraMap_mem_fracB.2 hz
  have hopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun x => ?_
    refine Filter.le_map fun s hs => ?_
    obtain ⟨n, -, hn⟩ := (hnO x).mem_iff.1 hs
    refine Filter.mem_of_superset ((hnK (f x)).mem_of_mem (i := n) trivial) ?_
    intro b hb
    obtain ⟨c, hc⟩ := mem_fracB.1 (show b - f x ∈ fracB ϖ n from hb)
    refine ⟨x + c * ϖ ^ n, hn ⟨c * ϖ ^ n, ?_, rfl⟩, ?_⟩
    · rw [hm]
      exact Dvd.intro_left c rfl
    · rw [map_add (f := _), ← hc, add_sub_cancel]
  refine ⟨τK, inferInstance, continuousSMul_of_algebraMap O' (FractionRing O') hcont, ⟨?_⟩⟩
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    (IsFractionRing.injective O' (FractionRing O')) hopen

theorem topEx : TopEx := by
  intro p _ O _ _ _ _ _ hinj
  letI τ : TopologicalSpace O := moduleTopology ℤ_[p] O
  haveI : IsModuleTopology ℤ_[p] O := ⟨rfl⟩
  have hO := padicCoeff_of_finite hinj
  obtain ⟨τK, h1, h2, h3⟩ := exists_fracTop O hO.adic
  exact ⟨τ, τK, h1, h2, hO, h3⟩

end GlobalTheory.PadicTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowPSmulMemOneFractionRing
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem padicCoeff_exists_pow_smul_mem_one :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    PadicCoeff p O → ∀ y : FractionRing O,
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := by
  intro p O _ _ _ _ hP y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ (p : O) := by
    have h := hP.p_mem
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
    exact h
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  dsimp only
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hbk : (b : O) ∣ (p : O) ^ k := by
    rw [hu]
    exact (Units.mul_left_dvd).mpr (pow_dvd_pow_of_dvd hdvd k)
  obtain ⟨c, hc⟩ := hbk
  refine ⟨k, ?_⟩
  rw [Submodule.mem_comap, LinearMap.lsmul_apply, Submodule.mem_one]
  refine ⟨c * a, ?_⟩
  rw [Algebra.smul_def, hc, map_mul, map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec']

end GlobalTheory
end

