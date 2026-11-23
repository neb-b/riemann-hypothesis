module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToIdeleMulSelf
section
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RgEisAsm

open PositivityTheory.RgEis PositivityTheory.RgEis.TF
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem toIdele_mul_self {ω : HeckeCharacter k} (hω : ω * ω = 1) (x : IdeleGroup k) :
    ω.toIdele x * ω.toIdele x = 1 := by
  have h := congrArg (fun f : HeckeCharacter k => f (IdeleClassGroup.mk k x)) hω
  simpa [HeckeCharacter.toIdele_apply] using h

theorem tensor_eq (φ : 𝓢(ι → mixedSpace k, ℂ)) (g : (ι → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (x : ι → 𝔸[k]) :
    GJMatrix.schwartzBruhatTensorPi φ g x = rd φ (fun j => (x j).1) * g (fun j => (x j).2) := rfl

theorem norm_inv_units (a : (InfiniteAdeleRing k)ˣ) (ha : ∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1)
    (w : InfinitePlace k) : ‖((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) w‖ = 1 := by
  have h : (a : InfiniteAdeleRing k) w * ((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) w = 1 :=
    congrFun (Units.mul_inv a) w
  have h2 := congrArg norm h
  rw [norm_mul, ha w, one_mul, norm_one] at h2
  exact h2

theorem line_inv {ω : HeckeCharacter k} (hω : ω * ω = 1) (φ₁ : 𝓢(Unit → mixedSpace k, ℂ))
    (g₁ : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (hφ : ∀ a : (InfiniteAdeleRing k)ˣ, (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) →
      rd φ₁ (fun _ => (a : InfiniteAdeleRing k)) = ω.toIdele (ofInfinite a))
    (hg : ∀ u ∈ finiteIntegralUnits k, g₁ (fun _ => (u : FiniteAdeleRing (𝓞 k) k)) =
      ω.toIdele (ofFinite u))
    (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ)
    (ha : ∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) (hu : u ∈ finiteIntegralUnits k) :
    GJMatrix.schwartzBruhatTensorPi φ₁ g₁
        (fun _ => (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k])) =
      ω.toIdele (ofInfinite a * ofFinite u) := by
  have h1 : (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k]).1 =
      ((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) := by
    have : toInfinite k (ofInfinite a * ofFinite u)⁻¹ = a⁻¹ := by simp
    exact congrArg Units.val this
  have h2 : (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k]).2 =
      ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) := by
    have : toFinite k (ofInfinite a * ofFinite u)⁻¹ = u⁻¹ := by simp
    exact congrArg Units.val this
  rw [tensor_eq]
  simp only [h1, h2]
  rw [hφ _ (norm_inv_units a ha), hg _ (inv_mem hu), ← Circle.coe_mul, ← map_mul, map_inv, map_inv,
    ← mul_inv, map_inv]
  have h3 := toIdele_mul_self hω (ofInfinite a * ofFinite u)
  rw [inv_eq_of_mul_eq_one_left h3]

theorem near_one_nhds (hCol : ColLaw) (hTop : InMTop) (i₀ : ι) (M₀ : ℕ) (hM : M₀ ≠ 0)
    (U : Set ((adStd k).kGL ι)) (hU : U ∈ 𝓝 (1 : (adStd k).kGL ι)) :
    U ∩ {u : (adStd k).kGL ι | InM M₀ ((col i₀ u.1 i₀).2 - 1) ∧
      ∀ w, ‖(col i₀ u.1 i₀).1 w - 1‖ < 1} ∈ 𝓝 (1 : (adStd k).kGL ι) := by
  obtain ⟨-, hc, h1, -⟩ := hCol k ι i₀
  have hcc : Continuous fun u : (adStd k).kGL ι => col i₀ u.1 i₀ :=
    (continuous_apply i₀).comp (hc.comp continuous_subtype_val)
  refine inter_mem hU (IsOpen.mem_nhds ?_ ?_)
  · have o1 : IsOpen {u : (adStd k).kGL ι | InM M₀ ((col i₀ u.1 i₀).2 - 1)} :=
      ((hTop k).1 M₀ hM).1.preimage ((continuous_snd.comp hcc).sub continuous_const)
    have o2 : IsOpen {u : (adStd k).kGL ι | ∀ w, ‖(col i₀ u.1 i₀).1 w - 1‖ < 1} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_lt
        ((((continuous_apply w).comp (continuous_fst.comp hcc)).sub continuous_const).norm)
        continuous_const
    exact o1.inter o2
  · have e : col i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) i₀ = 1 := by
      have : col (k := k) i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) = Pi.single i₀ 1 := h1
      rw [this]; simp
    refine ⟨?_, fun w => ?_⟩
    · rw [e]
      exact ⟨0, (OH k).zero_mem, by
        show (1 : FiniteAdeleRing (𝓞 k) k) - 1 = _
        simp⟩
    · rw [e]
      simp

theorem asm : ColLaw → InMTop → Supp → ArchFun → FinFun → ZSplit → ZInf → ZFinPos → ZFinLim →
    StdGood → TestFun := by
  intro hCol hTop hSupp hArch hFin hZS hZI hZP hZL hStd k _ _ ι _ _ i₀ ω hω U hU
  obtain ⟨M₀, hM₀, hfin⟩ := hFin k ω
  have hU' := near_one_nhds hCol hTop i₀ M₀ hM₀ U hU
  obtain ⟨M, δ, hM, hdvd, hδ, hS⟩ := hSupp k ι i₀ ((hStd k).kcpt ι) _ hU' M₀ hM₀
  obtain ⟨g, g₁, hg, hg₁, hg1, hg₁u, hg₁b, hg₁p, hgV⟩ := hfin M hM hdvd ι i₀
  obtain ⟨φ, φ₁, hφ1, hφ₁u, hφ₁p, hφV⟩ := hArch k ι i₀ ω hω δ hδ
  obtain ⟨hcolK, hcc, hcol1, hcolP⟩ := hCol k ι i₀
  have hΨ := GJMatrix.schwartzBruhatTensorPi_mem φ hg
  have hΨ₁ := GJMatrix.schwartzBruhatTensorPi_mem φ₁ hg₁
  have hfac : ∀ (t : 𝔸[k]) (κ : (adStd k).kGL ι),
      GJMatrix.schwartzBruhatTensorPi φ g (t • col i₀ κ.1) =
        GJMatrix.schwartzBruhatTensorPi φ₁ g₁ (fun _ => t) *
          GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) := by
    intro t κ
    obtain ⟨hu, hp⟩ := hcolK κ.1 κ.2
    have a1 := (hφV _ hu).1 t.1
    have a2 := (hgV _ hp).1 t.2
    rw [tensor_eq, tensor_eq, tensor_eq]
    have e1 : (fun j => ((t • col i₀ κ.1) j).1) = t.1 • (fun j => (col i₀ κ.1 j).1) := rfl
    have e2 : (fun j => ((t • col i₀ κ.1) j).2) = t.2 • (fun j => (col i₀ κ.1 j).2) := rfl
    rw [e1, e2, a1, a2]
    ring
  have hequiv : ∀ p κ : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] {i₀} →
      GJMatrix.schwartzBruhatTensorPi φ g (col i₀ (p * κ).1) =
        ω.toIdele (bdet {i₀} p.1) * GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) := by
    intro p κ hp
    obtain ⟨hc, a, u, hb, ha, hu⟩ := hcolP p.1 p.2 hp
    have e : col i₀ (p * κ).1 = (((bdet {i₀} p.1)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • col i₀ κ.1 := hc κ.1
    rw [e, hfac, hb, line_inv hω φ₁ g₁ hφ₁u hg₁u a u ha hu]
  have hone : rd φ₁ (fun _ => (1 : InfiniteAdeleRing k)) ≠ 0 := by
    have h := hφ₁u 1 (fun w => by
      rw [Units.val_one]
      exact norm_one (α := w.Completion))
    rw [Units.val_one] at h
    rw [h]
    simp
  have hunit : ∀ x : ℝ, 1 < x → zInf φ₁ ω x ≠ 0 := hZI k φ₁ ω hφ₁p hone
  refine ⟨GJMatrix.schwartzBruhatTensorPi φ g, GJMatrix.schwartzBruhatTensorPi φ₁ g₁,
    fun κ => GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1), hΨ, hΨ₁,
    (GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ).comp (hcc.comp continuous_subtype_val),
    ?_, fun t κ => hfac t κ, ?_, fun p κ hp => hequiv p κ hp, ?_, ?_⟩
  · have e : col (k := k) i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) = Pi.single i₀ 1 := hcol1
    show GJMatrix.schwartzBruhatTensorPi φ g (col i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k])) = 1
    rw [e, tensor_eq]
    have e1 : (fun j => ((Pi.single i₀ (1 : 𝔸[k]) : ι → 𝔸[k]) j).1) = Pi.single i₀ 1 := by
      funext j
      by_cases h : j = i₀
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl
    have e2 : (fun j => ((Pi.single i₀ (1 : 𝔸[k]) : ι → 𝔸[k]) j).2) = Pi.single i₀ 1 := by
      funext j
      by_cases h : j = i₀
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl
    rw [e1, e2, hφ1, hg1, one_mul]
  · intro κ hne
    have hne' : GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) ≠ 0 := hne
    rw [tensor_eq] at hne'
    obtain ⟨n1, n2⟩ := mul_ne_zero_iff.1 hne'
    obtain ⟨hu, hpr⟩ := hcolK κ.1 κ.2
    obtain ⟨p, hp, u, huU, hκ⟩ := hS κ (fun j hj => (hgV _ hpr).2.1 n2 j hj) ((hφV _ hu).2.1 n1)
    refine ⟨p, hp, u, huU.1, hκ, ?_⟩
    obtain ⟨hu', hpr'⟩ := hcolK u.1 u.2
    have hreal : ∃ r : ℝ, 0 ≤ r ∧ GJMatrix.schwartzBruhatTensorPi φ g (col i₀ u.1) = r := by
      obtain ⟨r, hr, e⟩ := (hφV _ hu').2.2 huU.2.2
      rcases (hgV _ hpr').2.2 huU.2.1 with h | h
      · exact ⟨0, le_rfl, by rw [tensor_eq, h]; simp⟩
      · exact ⟨r, hr, by rw [tensor_eq, e, h, mul_one]⟩
    obtain ⟨r, hr, e⟩ := hreal
    have h1 : GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) = ω.toIdele (bdet {i₀} p.1) * r := by
      rw [hκ, hequiv p u hp, e]
    show GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) =
      ω.toIdele (bdet {i₀} p.1) * (‖GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1)‖ : ℂ)
    have h2 : ‖GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1)‖ = r := by
      rw [h1, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    rw [h2, h1]
  · have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
    have hcard' : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
    obtain ⟨x, hx, hz⟩ := hZL k g₁ ω hg₁ hg₁b (fun u hu => by
      rw [hg₁u u hu, ← Circle.coe_mul, toIdele_mul_self hω, Circle.coe_one]) ((Fintype.card ι : ℝ) + 1)
    refine ⟨x, by simpa using hx, ?_⟩
    rw [hZS k φ₁ g₁ ω x hg₁]
    exact mul_ne_zero (hunit x (by linarith)) hz
  · rintro rfl x hx
    rw [hZS k φ₁ g₁ 1 x hg₁]
    refine mul_ne_zero (hunit x hx) (hZP k g₁ hg₁ (hg₁p rfl) ?_ x hx)
    have h := hg₁u 1 (one_mem _)
    rw [Units.val_one] at h
    rw [h]
    simp

end GlobalTheory.CompanionTheory.RgEisAsm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
section
noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisUnfold

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem integrable_of_continuous (μ : Measure K) [IsProbabilityMeasure μ] {F : K → (W →L[ℂ] W)}
    (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem exists_avgCLM (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) :
    ∃ A : C(K, ℂ) →L[ℂ] (W →L[ℂ] W), ∀ f : C(K, ℂ), A f = avg μ ρ f := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • ρ κ) μ := fun f =>
    integrable_of_continuous μ (f.continuous.smul hρ)
  let A₀ : C(K, ℂ) →ₗ[ℂ] (W →L[ℂ] W) :=
    { toFun := fun f => avg μ ρ f
      map_add' := fun f g => by
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨A₀.mkContinuous C fun f => ?_, fun f => rfl⟩
  have h : ∀ᵐ κ ∂μ, ‖f κ • ρ κ‖ ≤ C * ‖f‖ := Eventually.of_forall fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (hC κ (Set.mem_univ _)) (f.norm_coe_le_norm κ) (norm_nonneg _)
      ((norm_nonneg _).trans (hC κ (Set.mem_univ _)))
  have := norm_integral_le_of_norm_le_const h
  simpa [avg, A₀] using this

theorem avg_translate (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) {φ : K → ℂ} (hφ : Continuous φ) (κ₁ : K) :
    avg μ ρ (fun κ => φ (κ₁ * κ)) = ρ κ₁⁻¹ * avg μ ρ φ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hc : Continuous fun κ : K => κ₁ * κ := continuous_const.mul continuous_id
  have hI : Integrable (fun κ => φ (κ₁ * κ) • ρ (κ₁ * κ)) μ :=
    integrable_of_continuous μ ((hφ.comp hc).smul (hρ.comp hc))
  have h1 : avg μ ρ φ = ∫ κ, φ (κ₁ * κ) • ρ (κ₁ * κ) ∂μ :=
    (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) κ₁).symm
  have h2 := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹)) hI
  rw [h1]
  refine Eq.trans ?_ h2
  unfold avg
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  have h3 : (ρ κ₁⁻¹).comp (ρ (κ₁ * κ)) = ρ κ := by
    change ρ κ₁⁻¹ * ρ (κ₁ * κ) = ρ κ
    rw [← map_mul, inv_mul_cancel_left]
  change φ (κ₁ * κ) • ρ κ = ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹) (φ (κ₁ * κ) • ρ (κ₁ * κ))
  rw [map_smul, ContinuousLinearMap.compL_apply, h3]

end SlopeTestRemainingChoices

theorem unfold : SecLaw → AvgMem → Unfold := by
  intro hSec hAvg G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hpr Γ P c hpar φ Λ T hφ hLaw hΛ hT g u hu
    hb w
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hsec := (hSec G W K ρ hK hρ Γ P c hpar).1
  have hmem := hAvg G W K ρ hK hρ μ hμ hpr Γ P c hpar φ hφ hLaw w
  have key : ∀ q : Cos P Γ, ∃ (p : G) (κ₁ : K), p ∈ P ∧ rep q * g = p * κ₁ := fun q => by
    obtain ⟨p, hp, k, hk, e⟩ := hpar.iwa (rep q * g)
    exact ⟨p, ⟨k, hk⟩, hp, e⟩
  choose p κ₁ hp hpk using key
  have hterm : ∀ q (κ : K), T (rep q * (g * κ)) =
      (c (p q) * Complex.exp (Λ (p q))) * φ (κ₁ q * κ) := fun q κ => by
    have e : rep q * (g * (κ : G)) = p q * ((κ₁ q * κ : K) : G) := by
      rw [← mul_assoc, hpk q, Subgroup.coe_mul, mul_assoc]
    rw [e]
    exact hT _ (hp q) _
  have hc : ∀ q, Continuous fun κ : K => φ (κ₁ q * κ) := fun q =>
    hφ.comp (continuous_const.mul continuous_id)
  let f' : Cos P Γ → C(K, ℂ) := fun q => ⟨fun κ => φ (κ₁ q * κ), hc q⟩
  let f : Cos P Γ → C(K, ℂ) := fun q => (c (p q) * Complex.exp (Λ (p q))) • f' q
  have hfa : ∀ q κ, f q κ = T (rep q * (g * κ)) := fun q κ => by
    rw [hterm]
    simp [f, f']
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hb q 1)
  have hsum : Summable f := Summable.of_norm_bounded hu fun q =>
    (ContinuousMap.norm_le _ (hu0 q)).2 fun κ => by
      rw [hfa]
      exact hb q κ
  obtain ⟨A, hA⟩ := exists_avgCLM μ hρ
  have hF : (fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ))) = ⇑(∑' q, f q) := by
    funext κ
    rw [← ContinuousMap.tsum_apply hsum]
    exact tsum_congr fun q => (hfa q κ).symm
  rw [hF, ← hA]
  have hL := ((ContinuousLinearMap.apply ℂ W w).comp A).map_tsum hsum
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hL
  rw [hL]
  unfold eis
  refine tsum_congr fun q => ?_
  have e1 : A (f q) w = (c (p q) * Complex.exp (Λ (p q))) • (ρ (κ₁ q)⁻¹ (avg μ ρ φ w)) := by
    have : A (f' q) = ρ (κ₁ q)⁻¹ * avg μ ρ φ := by
      rw [hA]
      exact avg_translate μ hρ hφ (κ₁ q)
    have e2 : A (f q) = (c (p q) * Complex.exp (Λ (p q))) • A (f' q) := map_smul A _ _
    rw [e2, this]
    rfl
  rw [e1, hpk q, hΛ _ _ (κ₁ q).2, hsec _ hmem _ (hp q), smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisUnfold
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValEqOneOfMulEq
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global

theorem val_eq_one_of_mul_eq {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation F Γ) {a b u u' m mi y : F} (ha : w a ≤ 1) (hb : w b ≤ 1) (hu : w u ≤ 1)
    (hu' : w u' ≤ 1) (huu : u * u' = 1) (hy : w y ≤ 1) (hm : m * mi = 1) (hmi : 1 < w mi)
    (h : a * b - u = m * y) : w a = 1 := by
  have key : ∀ {p q : Γ}, p ≤ 1 → q ≤ 1 → p * q = 1 → p = 1 := by
    intro p q hp hq hpq
    refine le_antisymm hp (not_lt.mp fun hc => ?_)
    have h2 : p * q < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' hq) hc
    rw [hpq] at h2
    exact lt_irrefl _ h2
  have hwu : w u = 1 := key hu hu' (by rw [← map_mul, huu, map_one])
  have hwm : w m < 1 := by
    refine not_le.mp fun hc => ?_
    have h1 : w m * w mi = 1 := by rw [← map_mul, hm, map_one]
    have h2 : w mi ≤ w m * w mi := le_mul_of_one_le_left' hc
    rw [h1] at h2
    exact absurd hmi (not_lt.mpr h2)
  have hmy : w (m * y) < w u := by
    rw [map_mul, hwu]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hwm
  have hab : a * b = m * y + u := sub_eq_iff_eq_add.mp h
  have hprod : w a * w b = 1 := by
    rw [← map_mul, hab, Valuation.map_add_eq_of_lt_right _ hmy, hwu]
  exact key ha hb hprod

theorem liftUnit : LiftUnit := by
  intro k _ _ M hM a ha b hb u hu hab
  obtain ⟨y, hy, hyeq⟩ := hab
  classical
  have hint : ∀ x : FiniteAdeleRing (𝓞 k) k, x ∈ OH k →
      ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (x v) ≤ 1 :=
    fun x hx v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (hx v)
  have hM0 : ∀ v : HeightOneSpectrum (𝓞 k), (M : v.adicCompletion k) ≠ 0 := by
    intro v
    rw [← map_natCast (algebraMap k (v.adicCompletion k)) M]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hM)
  have hMle : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) ≤ 1 := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (natCast_mem _ M)
  obtain ⟨huU1, huU2⟩ := Subgroup.mem_comap.mp hu
  have hu1 : (u : FiniteAdeleRing (𝓞 k) k) ∈ OH k := fun v => huU1 v
  have hu2 : ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) ∈ OH k :=
    fun v => huU2 v
  have hunit : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) < 1 →
      Valued.v (a v) = 1 := by
    intro v hv
    have hmul : (u : FiniteAdeleRing (𝓞 k) k) v *
        ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) (Units.mul_inv u)
    have hcomp : a v * b v - (u : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) * y v :=
      congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) hyeq
    exact val_eq_one_of_mul_eq Valued.v (hint a ha v) (hint b hb v) (hint _ hu1 v) (hint _ hu2 v)
      hmul (hint y hy v) (mul_inv_cancel₀ (hM0 v))
      ((Valuation.one_lt_val_iff Valued.v (inv_ne_zero (hM0 v))).mpr (by rwa [inv_inv])) hcomp
  let f : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then a v else 1
  let g : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then (a v)⁻¹ else 1
  have hf : ∀ v : HeightOneSpectrum (𝓞 k), f v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [f, if_pos hv]
      exact ha v
    · simp only [f, if_neg hv]
      exact one_mem _
  have hg : ∀ v : HeightOneSpectrum (𝓞 k), g v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [g, if_pos hv]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_inv₀, hunit v hv, inv_one]
    · simp only [g, if_neg hv]
      exact one_mem _
  let F : FiniteAdeleRing (𝓞 k) k := RestrictedProduct.mk f (Filter.Eventually.of_forall hf)
  let G : FiniteAdeleRing (𝓞 k) k := RestrictedProduct.mk g (Filter.Eventually.of_forall hg)
  have hFG : F * G = 1 := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    show f v * g v = 1
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [f, g, if_pos hv]
      refine mul_inv_cancel₀ fun h0 => ?_
      have h1 := hunit v hv
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    · simp only [f, g, if_neg hv, mul_one]
  have hGF : G * F = 1 := by
    rw [mul_comm]
    exact hFG
  let U : (FiniteAdeleRing (𝓞 k) k)ˣ := ⟨F, G, hFG, hGF⟩
  have hU : U ∈ finiteIntegralUnits k :=
    Subgroup.mem_comap.mpr
      (Submonoid.mem_units_of_val_mem_inv_val_mem _ (fun v => hf v) (fun v => hg v))
  refine ⟨U, hU, ?_⟩
  let Y : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then 0 else (a v - 1) * (M : v.adicCompletion k)⁻¹
  have hY : ∀ v : HeightOneSpectrum (𝓞 k), Y v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [Y, if_pos hv]
      exact zero_mem _
    · simp only [Y, if_neg hv]
      have hM1 : Valued.v (M : v.adicCompletion k) = 1 := le_antisymm (hMle v) (not_lt.mp hv)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_mul, map_inv₀, hM1, inv_one,
        mul_one]
      exact (Valuation.map_sub Valued.v (a v) 1).trans
        (max_le (hint a ha v) (Valuation.map_one Valued.v).le)
  refine ⟨RestrictedProduct.mk Y (Filter.Eventually.of_forall hY), fun v => hY v, ?_⟩
  refine RestrictedProduct.ext _ _ fun v => ?_
  show a v - f v = (M : v.adicCompletion k) * Y v
  by_cases hv : Valued.v (M : v.adicCompletion k) < 1
  · simp only [f, Y, if_pos hv, sub_self, mul_zero]
  · simp only [f, Y, if_neg hv]
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (hM0 v), mul_one]

end GlobalTheory.CompanionTheory.EisTF
end
end

