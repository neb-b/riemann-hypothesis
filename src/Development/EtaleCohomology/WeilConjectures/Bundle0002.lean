module

public import Development.EtaleCohomology.WeilConjectures.Bundle0001
public import Development.EtaleCohomology.WeilConjectures.FermatCount
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Mathlib.NumberTheory.Padics.ProperSpace

@[expose] public section

-- bundled from Development.EtaleCohomology.WeilConjectures.AbsContPf
section
namespace LateralTheory.EWeil.AbsContPf

universe u v

open LateralTheory.EWeil.ContinCut

namespace AbsoluteContinuitySecondLemma

theorem goal1 (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]; rfl

end AbsoluteContinuitySecondLemma

theorem norm_smul_le (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ :=
  AbsoluteContinuitySecondLemma.goal1 l a q

namespace AbsoluteContinuityFirstLemma

namespace AbsoluteContinuitySmulBound

private lemma smul_bound (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ ≤ ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]
  have h : ‖(algebraMap ℤ_[l] ℚ_[l] a)‖ ≤ 1 := by
    have e : algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l]) := rfl
    rw [e, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one a
  calc ‖algebraMap ℤ_[l] ℚ_[l] a‖ * ‖q‖ ≤ 1 * ‖q‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖q‖ := one_mul _

end AbsoluteContinuitySmulBound

theorem goal1 (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] M).FG)
  refine ⟨∑ x ∈ s, ‖φ x‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro m
  have hm : m ∈ Submodule.span ℤ_[l] (s : Set M) := by rw [hs]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
      exact Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) hx
  | zero => simpa using Finset.sum_nonneg (fun (x : M) (_ : x ∈ s) => norm_nonneg (φ x))
  | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
  | smul a x _ hx =>
      rw [map_smul]
      exact (AbsoluteContinuitySmulBound.smul_bound l a (φ x)).trans hx

end AbsoluteContinuityFirstLemma

theorem bdd (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C :=
  AbsoluteContinuityFirstLemma.goal1 l M φ

theorem AbsCont_of (hC : Chev.{u}) : AbsCont.{u, v} := by
  intro l _ G _ _ _ M _ _ _ ρ K hK h0 hopen φ x
  obtain ⟨C, hC0, hCb⟩ := bdd l M φ
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0:ℝ) < C + 1))
    (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨k, hk⟩ := hC l M K hK h0 N
  set y := ρ g₀ x
  have hU : IsOpen {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} :=
    (hopen y k).preimage (continuous_id.mul continuous_const)
  have hmem : g₀ ∈ {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} := by
    simp [y]
  filter_upwards [hU.mem_nhds hmem] with g hg
  change ρ (g * g₀⁻¹) y - y ∈ K k at hg
  have hd : ρ g x - ρ g₀ x ∈ K k := by
    have : ρ (g * g₀⁻¹) y = ρ g x := by
      simp only [y]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [this] at hg; exact hg
  obtain ⟨z, hz⟩ := hk _ hd
  rw [dist_eq_norm, ← map_sub, hz, map_smul, norm_smul_le, PadicInt.norm_p_pow]
  have hzC := hCb z
  have hpow : (l : ℝ) ^ (-(N : ℤ)) = (l : ℝ)⁻¹ ^ N := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hpow]
  have hp0 : 0 ≤ (l : ℝ)⁻¹ ^ N := by positivity
  calc (l : ℝ)⁻¹ ^ N * ‖φ z‖ ≤ (l : ℝ)⁻¹ ^ N * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hp0
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_right hN (by linarith)
    _ = ε := div_mul_cancel₀ _ (by linarith)

end LateralTheory.EWeil.AbsContPf
end

-- bundled from Development.EtaleCohomology.WeilConjectures.AcycPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EWeil.AcycPf

def incl (S : Scheme.{0}) : S.Etale ⥤ Over S := MorphismProperty.Over.forget _ _ _

def RestrInj : Prop := ∀ (R : Type) [CommRing R] (S : Scheme.{0})
  (G : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))) [Injective G],
  ∃ h : Presheaf.IsSheaf S.smallEtaleTopology ((incl S).op ⋙ G.obj),
    Injective (⟨_, h⟩ : Sheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R)))

end LateralTheory.EWeil.AcycPf
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.ChevPf
section
namespace LateralTheory.EWeil.ChevPf

open Topology

theorem Chev_of : LateralTheory.EWeil.ContinCut.Chev := by
  intro l _ M _ _ _ K hK h0 N
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] M
  let V : ℕ → Set (Fin r → ℤ_[l]) := fun k => ((K k).comap π : Set (Fin r → ℤ_[l]))
  have hc : ∀ k, IsCompact (V k) := by
    intro k
    obtain ⟨s, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] ((K k).comap π)
    have : V k = Set.range (((K k).comap π).subtype.comp g) := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, ha⟩ := hg ⟨z, hz⟩
        exact ⟨a, by simp [ha]⟩
      · rintro ⟨a, rfl⟩
        exact (g a).2
    rw [this]
    exact isCompact_range (LinearMap.continuous_on_pi _)
  have hdir : Directed (· ⊇ ·) V := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · intro z hz; exact hK (le_max_left a b) hz
    · intro z hz; exact hK (le_max_right a b) hz
  let ε : ℝ := (l : ℝ) ^ (-(N : ℤ))
  have hε : 0 < ε := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  let U : Set (Fin r → ℤ_[l]) :=
    {z | ∃ c w, π c = 0 ∧ (∀ i, ‖w i‖ ≤ ε) ∧ z = c + w}
  have hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x := by
    intro x hx
    have hx0 : π x = 0 := h0 _ (fun k => Set.mem_iInter.1 hx k)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
    intro z hz
    refine ⟨x, z - x, hx0, fun i => ?_, by abel⟩
    have h1 : dist (z i) (x i) ≤ dist z x := dist_le_pi_dist z x i
    rw [Metric.mem_ball] at hz
    rw [Pi.sub_apply, ← dist_eq_norm]
    linarith
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hc (mem_nhdsSet_iff_forall.mpr hU)
  refine ⟨k, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  obtain ⟨c, w, hc0, hw, rfl⟩ := hk (show x ∈ V k from hy)
  have hu : ∀ i, ∃ u : ℤ_[l], w i = (l : ℤ_[l]) ^ N * u := by
    intro i
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (w i) N).1 (hw i)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨u, by rw [← hu, mul_comm]⟩
  choose u hu using hu
  refine ⟨π u, ?_⟩
  have : w = (l : ℤ_[l]) ^ N • u := funext fun i => by simp [hu i]
  rw [map_add (f := _), hc0, zero_add, this, map_smul]

end LateralTheory.EWeil.ChevPf
end

-- bundled from Development.EtaleCohomology.WeilConjectures.GlueOfSig
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨h⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.StabPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.StabPf

section Proj
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) {X : Scheme.{0}} (p : X ⟶ Sp K)

def proj : geom Ω p ⟶ geom L p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3)

theorem galMap_proj (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ L.fixingSubgroup) : galMap Ω p σ ≫ proj L p = proj L p := by
  apply pullback.hom_ext
  · simp only [proj, Category.assoc, pullback.lift_fst, galMap_fst]
  · simp only [proj, Category.assoc, pullback.lift_snd]
    rw [galMap_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    exact (mem_fixingSubgroup_iff _).1 hσ x x.2

end Proj

end LateralTheory.EWeil.StabPf
end
end

