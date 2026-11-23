module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ExpSum
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem summable_lat_wt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sz {κ : Type} [Fintype κ] (y : κ → AF F) : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j))

theorem norm_le_sz {κ : Type} [Fintype κ] (y : κ → AF F) : 1 + ‖fun j => evI F (y j)‖ ≤ sz y := by
  have h0 : ∀ j, 0 ≤ ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) := fun j =>
    Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
  refine add_le_add_right ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => h0 j)).2 fun j => ?_) 1
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j))
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (y j)))
    (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)

theorem sz_pos {κ : Type} [Fintype κ] (y : κ → AF F) : 0 < sz y := lt_of_lt_of_le (by positivity) (norm_le_sz y)

theorem summable_wt {κ : Type} [Fintype κ] {C : Set (κ → Af F)} (hC : IsCompact C) : ∃ N : ℕ, Summable fun ξ : κ → F =>
    if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then (sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 := by
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hC
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, ?_⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine if_neg fun h0 => hξ ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ h0 i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_)
      ((summable_lat_wt (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj)
    · simp only [Function.comp_apply]
      split_ifs
      · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
      · exact le_rfl
    · simp only [Function.comp_apply]
      split_ifs
      · rw [inv_pow]
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _)
        have h := norm_le_sz (fun i => algebraMap F (AF F) (ξ.1 i))
        have e : (fun i => evI F (algebraMap F (AF F) (ξ.1 i))) = fun i => mixedEmbedding F (ξ.1 i) :=
          funext fun i => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
        rw [e] at h
        exact h
      · positivity

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_bound (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    ∃ (wt : (Fin m → F) → ℝ) (P : SInf F (Fin n × Fin d) → ℝ), Summable wt ∧ Continuous P ∧ P 0 = 0 ∧
      ∀ y (f : SInf F (Fin n × Fin d)),
        ‖l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) (pureA F f φ)))‖ ≤ P f * wt y := by
  obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨N, hN⟩ := summable_wt hC
  choose T hT using fun i => hl (φ₁ i) (h1 i)
  choose p hp hq using fun i => h4 ((normSeminorm ℂ ℂ).comp (T i).toLinearMap) N (T i).continuous.norm
  refine ⟨_, fun f => ∑ i, p i f, hN, continuous_finsetSum _ fun i _ => hp i, by simp, fun y f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum]
  simp only [hT]
  split_ifs with hy
  · rw [Finset.sum_mul]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
    exact hq i i _ f
  · simp [h3 _ _ hy]

end PositivityTheory.ThKCT
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def StabDec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧ (p ∈ ratU σ Y.J → g₁ ∈ ratU σ Y₁.J)) ∧
    (∀ (ξ : Eˣ), ∀ g₁ ∈ ratU σ Y₁.J, ∀ m, IsLevi H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁ m → m ∈ ratU σ Y.J) ∧
    ∀ t (g₁ : UA σ Y₁.J) m, IsLevi H t g₁ m → ∀ u ∈ unip σ Y H, m⁻¹ * u * m ∈ unip σ Y H

def ConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ z : ℕ, 2 * n = d + 2 * z ∧ min r s + 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ schA F (Fin n × Fin d), KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftA H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ)) h₁

def ConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → ∀ z : ℕ, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ M.So B.ψ B.τ₁, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftB σ H H') χW z (om (1, h) Φ)) h₁

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.IntegrableProdOfBound
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem integrable_prod_of_bound {G N : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] (μ : Measure G) [SFinite μ] (ν : Measure N) [IsFiniteMeasure ν]
    {f : G × N → ℂ} (hf : Continuous f) {K : ℝ} (hK : ∀ u, ∫⁻ g, ‖f (g, u)‖ₑ ∂μ ≤ ENNReal.ofReal K) : Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono hK) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem ctFub_of (hU : UnipEx) (hT : ThetaBasic) (hG : GrpTop) (hE : EpsOf) : CTFub := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc
  obtain ⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH
  obtain ⟨b1, b2, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  obtain ⟨-, -, -, -, -, -, -, b3⟩ := hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1
  obtain ⟨t1, t2, -⟩ := (hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := hp.good.haar
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  have key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧
      Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕)) := by
    intro ν 𝓕 h1 h
    have hf : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hcont : Continuous fun u : unip σ W H' => u.1 * h := continuous_subtype_val.mul continuous_const
    obtain ⟨D, hD⟩ := b3 _ (hΩ.image hcont)
    refine ⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k)
      (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩
    obtain ⟨γ, hγ, hu⟩ := hcov u
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h) := fun g => by
      rw [← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]
    simp only [e]
    refine (hb _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D := hD _ ⟨_, hu, rfl⟩
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)
  refine ⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩
  · obtain ⟨_, hi⟩ := key ν₀ 𝓕₀ a3 h
    simp only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]
    exact hi.integral_prod_left
  · obtain ⟨_, hi⟩ := key ν 𝓕 c3 h
    simp only [fun g => hc g ν 𝓕 c1 c2 c3 h]
    exact integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi

end PositivityTheory.ThKCT
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SchInt
section
noncomputable section

namespace PositivityTheory.ThKCT

namespace SchI

open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cd (f : SchwartzMap V ℂ) (j : ℕ) : ContDiff ℝ j f := f.smooth j

def jet (k j : ℕ) (f : SchwartzMap V ℂ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
    ((continuous_norm.pow k).smul ((cd f j).continuous_iteratedFDeriv le_rfl)) (SchwartzMap.seminorm ℂ k j f) fun x => by
      rw [norm_smul, norm_pow, norm_norm]
      exact SchwartzMap.le_seminorm ℂ k j f x

theorem jet_apply (k j : ℕ) (f : SchwartzMap V ℂ) (x : V) : jet k j f x = ‖x‖ ^ k • iteratedFDeriv ℝ j f x := rfl

theorem norm_jet (k j : ℕ) (f : SchwartzMap V ℂ) : ‖jet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  refine le_antisymm (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _) ?_
  refine SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _) fun x => ?_
  have := (jet k j f).norm_coe_le_norm x
  rwa [jet_apply, norm_smul, norm_pow, norm_norm] at this

def J (k j : ℕ) : SchwartzMap V ℂ →L[ℂ] V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (jet k j)
    (fun f g => by
      ext1 x
      rw [BoundedContinuousFunction.add_apply, jet_apply, jet_apply, jet_apply, ← smul_add]
      exact congrArg _ (iteratedFDeriv_add_apply (cd f j).contDiffAt (cd g j).contDiffAt))
    (fun a f => by
      ext1 x
      rw [BoundedContinuousFunction.smul_apply, jet_apply, jet_apply, RingHom.id_apply, smul_comm a]
      exact congrArg _ (iteratedFDeriv_const_smul_apply (cd f j).contDiffAt))
    ⟨{(k, j)}, 1, zero_le_one, fun f => by rw [norm_jet, Finset.sup_singleton, one_mul]; rfl⟩

variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)

include hG hI

theorem int_J (k j : ℕ) : Integrable (fun a => J k j (G a)) μ :=
  (hI k j).mono' ((J k j).continuous.comp hG).aestronglyMeasurable (.of_forall fun a => (norm_jet k j _).le)

omit hI in
theorem cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by
  have := (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp ((J 0 j).continuous.comp hG)
  refine this.congr fun a => ?_
  change jet 0 j (G a) x = _
  rw [jet_apply, pow_zero, one_smul]

omit hG hI in
theorem bd_D (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  simpa using SchwartzMap.le_seminorm ℂ 0 j f x

theorem int_D (j : ℕ) (x : V) : Integrable (fun a => iteratedFDeriv ℝ j (G a) x) μ :=
  (hI 0 j).mono' (cont_D hG j x).aestronglyMeasurable (.of_forall fun a => bd_D _ j x)

theorem deriv_D (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Set.univ) (x₀ := x)
    (F := fun y a => iteratedFDeriv ℝ j (G a) y) (F' := fun y a => L (iteratedFDeriv ℝ (j + 1) (G a) y))
    (bound := fun a => SchwartzMap.seminorm ℂ 0 (j + 1) (G a)) univ_mem
    (.of_forall fun y => (cont_D hG j y).aestronglyMeasurable) (int_D hG hI j x)
    (L.continuous.comp (cont_D hG (j + 1) x)).aestronglyMeasurable
    (.of_forall fun a y _ => by rw [L.norm_map]; exact bd_D _ _ y) (hI 0 (j + 1))
    (.of_forall fun a y _ => ((cd (G a) (j + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j) y).hasFDerivAt)
  have e := L.toContinuousLinearEquiv.integral_comp_comm (μ := μ) fun a => iteratedFDeriv ℝ (j + 1) (G a) x
  exact h.congr_fderiv e

theorem taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ :=
  ⟨fun x => ((continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.integral_comp_comm (μ := μ)
      fun a => iteratedFDeriv ℝ 0 (G a) x).symm,
    fun j _ x => deriv_D hG hI j x,
    fun j _ => continuous_iff_continuousAt.2 fun x => (deriv_D hG hI j x).continuousAt⟩

theorem eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  rw [← (taylor hG hI).eq_iteratedFDeriv (by exact_mod_cast le_top) x, ← integral_smul]
  exact ((BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm (int_J hG hI k j)).symm

theorem exists_int : ∃ f : SchwartzMap V ℂ, ∀ k j, J k j f = ∫ a, J k j (G a) ∂μ := by
  refine ⟨⟨fun x => ∫ a, G a x ∂μ, (taylor hG hI).contDiff, fun k j => ⟨‖∫ a, J k j (G a) ∂μ‖, fun x => ?_⟩⟩, fun k j => ?_⟩
  · have := (∫ a, J k j (G a) ∂μ).norm_coe_le_norm x
    rwa [eval_int hG hI, norm_smul, norm_pow, norm_norm] at this
  · ext1 x
    rw [eval_int hG hI]
    rfl

omit hG hI in
theorem factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let j : SchwartzMap V ℂ →ₗ[ℂ] ∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ) := LinearMap.pi fun i => (J i.1.1 i.1.2).toLinearMap
  have hb : ∀ f, ‖T f‖ ≤ C * ‖j f‖ := fun f => by
    refine (h f).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2
    exact (norm_jet i.1 i.2 f).ge.trans (norm_le_pi_norm (j f) ⟨i, hi⟩)
  have hk : LinearMap.ker j ≤ LinearMap.ker T.toLinearMap := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let t : LinearMap.range j →ₗ[ℂ] ℂ := ((LinearMap.ker j).liftQ T.toLinearMap hk) ∘ₗ j.quotKerEquivRange.symm.toLinearMap
  have ht : ∀ f, t ⟨j f, f, rfl⟩ = T f := fun f => by
    simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [j.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]
    rfl
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range j) (t.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [ht]
    exact hb f))
  exact ⟨s, g, fun f => ((hg ⟨j f, f, rfl⟩).trans (ht f)).symm⟩

end SchI

theorem schInt : SchInt := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT⟩ := SchI.factor T
  have hi : MeasureTheory.Integrable (fun a (i : s) => SchI.J i.1.1 i.1.2 (G a)) μ :=
    MeasureTheory.Integrable.of_eval fun i => SchI.int_J hG hI _ _
  simp only [hT]
  refine ⟨T'.integrable_comp hi, ?_⟩
  rw [T'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hf]
  exact (ContinuousLinearMap.proj (R := ℂ) i).integral_comp_comm hi

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SoDefs
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def LinEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW t) = 0 → evFin F v (sy σ X W x u) =
        ((X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ)ᵀ * u.map (piW t)).trace

def SoZeroA' : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ → ∀ M₁ : Model σ X W₁, M₁.IsGood B.ψ →
    (∃ χX χW om₁ om₀ r₁ s₁ r₀ s₀ r₂ s₂, IsPair B M₁ χX χW om₁ r₁ s₁ r₂ s₂ ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₂ s₂) →
    ∀ e₀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ Ψ ∈ schA F _,
      e₀ Ψ ∈ M₁.So B.ψ B.τ₁ → e Ψ = 0

end PositivityTheory.ThKCT

end
end

