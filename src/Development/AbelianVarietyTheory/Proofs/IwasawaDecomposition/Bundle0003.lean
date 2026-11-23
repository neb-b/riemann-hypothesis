module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuationEqPow
section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped WithZeroTopology WithZero

namespace GlobalTheory.CompletionHomContinuous

theorem continuous_of_valuation_eq_pow {A B Γ : Type*} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [hA : Valued A Γ] [hB : Valued B Γ]
    (hs : Function.Surjective hA.v) (g : A →+* B) {e : ℕ} (he : 0 < e)
    (hg : ∀ x, hB.v (g x) = hA.v x ^ e) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero B Γ).tendsto_right_iff]
  intro γ _
  have hc : Continuous fun x : A => hA.v x ^ e :=
    (Valued.continuous_valuation_of_surjective hs).pow e
  have h0 : Tendsto (fun x : A => hA.v x ^ e) (𝓝 0) (𝓝 0) :=
    hc.tendsto' 0 0 (by simp [he.ne'])
  rw [WithZeroTopology.tendsto_zero] at h0
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  filter_upwards [h0 _ hγ] with x hx
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem exists_completion_hom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (RingOfIntegers K))
    (v' : HeightOneSpectrum (RingOfIntegers L)) (e : ℕ) (he : 0 < e)
    (h : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : adicCompletion K v →+* adicCompletion L v', Continuous f ∧
      (∀ x : K, f (algebraMap K (adicCompletion K v) x) =
        algebraMap L (adicCompletion L v') (algebraMap K L x)) ∧
      ∀ y : adicCompletion K v, (Valued.v (f y) : WithZero (Multiplicative ℤ)) = Valued.v y ^ e := by
  let g : WithVal (v.valuation K) →+* adicCompletion L v' :=
    (algebraMap L (adicCompletion L v')).comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  have hL : ∀ x : L, (Valued.v (algebraMap L (adicCompletion L v') x) : WithZero (Multiplicative ℤ))
      = v'.valuation L x := fun x => valuedAdicCompletion_eq_valuation' v' x
  have hK : ∀ x : K, (Valued.v (algebraMap K (adicCompletion K v) x) : WithZero (Multiplicative ℤ))
      = v.valuation K x := fun x => valuedAdicCompletion_eq_valuation' v x
  have hg : Continuous g := by
    refine continuous_of_valuation_eq_pow (Γ := WithZero (Multiplicative ℤ)) ?_ g he ?_
    · intro c
      obtain ⟨x, hx⟩ := v.valuation_surjective K c
      exact ⟨(WithVal.equiv (v.valuation K)).symm x, hx⟩
    · intro x
      exact (hL _).trans (h _)
  let f : adicCompletion K v →+* adicCompletion L v' :=
    (UniformSpace.Completion.extensionHom g hg).comp (adicCompletion.equiv K v).toRingHom
  have hf : Continuous f :=
    (UniformSpace.Completion.continuous_extension (f := g)).comp
      (adicCompletion.continuous_toCompletion K v)
  have hfx : ∀ x : K, f (algebraMap K (adicCompletion K v) x) =
      algebraMap L (adicCompletion L v') (algebraMap K L x) := fun x =>
    UniformSpace.Completion.extensionHom_coe g hg ((WithVal.equiv (v.valuation K)).symm x)
  refine ⟨f, hf, hfx, fun y => ?_⟩
  refine (denseRange_algebraMap K v).induction_on y ?_ ?_
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L v')).comp hf)
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)).pow e)
  · intro x
    rw [hfx, hL, hK, h]

end GlobalTheory.CompletionHomContinuous
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordsEqPairingsRationalSymplecticBasis
section
open Matrix

namespace GlobalTheory

theorem coords_in_rational_symplectic_basis :
    ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq →
      Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) →
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) →
      ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by
  intro g r Mq ε φ hr hskew hdet hεε hφφ hφε x
  rcases Nat.eq_zero_or_pos g with hg | hg
  · funext i
    exact absurd i.2 (by omega)
  have hsk : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hskew, dotProduct_comm, neg_mulVec, dotProduct_neg]
  have hεφ : ∀ i k, ε i ⬝ᵥ Mq *ᵥ φ k = -(if i = k then 1 else 0) := by
    intro i k
    rw [hsk, hφε]

  have pε : ∀ (a b : Fin g → ℚ) k,
      (∑ i, a i • ε i + ∑ j, b j • φ j) ⬝ᵥ Mq *ᵥ ε k = b k := by
    intro a b k
    simp [add_dotProduct, sum_dotProduct, smul_dotProduct, hεε, hφε]
  have pφ : ∀ (a b : Fin g → ℚ) k,
      (∑ i, a i • ε i + ∑ j, b j • φ j) ⬝ᵥ Mq *ᵥ φ k = -a k := by
    intro a b k
    simp [add_dotProduct, sum_dotProduct, smul_dotProduct, hφφ, hεφ]

  set v : Fin g ⊕ Fin g → Fin r → ℚ := Sum.elim ε φ with hv
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc s
    rw [Fintype.sum_sum_type] at hc
    simp only [hv, Sum.elim_inl, Sum.elim_inr] at hc
    rcases s with k | k
    · have := pφ (fun i => c (Sum.inl i)) (fun j => c (Sum.inr j)) k
      rw [hc, zero_dotProduct] at this
      linarith
    · have := pε (fun i => c (Sum.inl i)) (fun j => c (Sum.inr j)) k
      rw [hc, zero_dotProduct] at this
      linarith
  haveI : Nonempty (Fin g ⊕ Fin g) := ⟨Sum.inl ⟨0, hg⟩⟩
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Module.finrank_fin_fun]
    omega

  set z := x - (∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j) with hz
  let f : (Fin r → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun y => z ⬝ᵥ Mq *ᵥ y
      map_add' := by intro a b; simp [mulVec_add, dotProduct_add]
      map_smul' := by intro c a; simp [mulVec_smul, dotProduct_smul] }
  have hf : f = 0 := by
    apply LinearMap.ext_on_range hspan
    intro s
    rcases s with k | k
    · show z ⬝ᵥ Mq *ᵥ ε k = 0
      rw [hz, sub_dotProduct, pε]
      ring
    · show z ⬝ᵥ Mq *ᵥ φ k = 0
      rw [hz, sub_dotProduct, pφ]
      ring
  have hzM : z ᵥ* Mq = 0 := by
    funext j
    have h1 : f (Pi.single j 1) = 0 := by rw [hf]; rfl
    have h2 : f (Pi.single j 1) = (z ᵥ* Mq) j := by
      show z ⬝ᵥ Mq *ᵥ Pi.single j 1 = _
      rw [dotProduct_mulVec, dotProduct_single, mul_one]
    rw [← h2, h1]
    rfl
  have hz0 : z = 0 := eq_zero_of_vecMul_eq_zero hdet hzM
  exact sub_eq_zero.mp hz0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DescentJointEigenvectorsComplexReading
section
namespace GlobalTheory

open Module

theorem descent_joint_eigen : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  classical
  intro K V W ι κ _ _ _ _ _ f e G hinj T T' I hT Part s lam hPart hG v hv
  set M := ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) with hM
  have mono : ∀ S : Finset ι, (↑S : Set ι) ⊆ s → (⨆ σ ∈ S, Part σ) ≤ ⨆ σ ∈ s, Part σ := by
    intro S hS
    exact iSup₂_le fun σ hσ => le_iSup₂_of_le (f := fun σ (_ : σ ∈ s) => Part σ) σ (hS hσ) le_rfl
  have key : ∀ (S S'' : Finset ι), (↑S : Set ι) ⊆ s → ∀ k ∈ I, ∀ c : K,
      (∀ σ ∈ S, σ ∉ S'' → lam σ k = c) → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ →
      e (T k v - c • v) ∈ ⨆ σ ∈ S'', Part σ := by
    intro S S'' hS k hk c hc v hv
    have hrw : e (T k v - c • v) = (T' k - f c • (1 : Module.End ℂ W)) (e v) := by
      simp [map_sub, hT k hk, LinearMap.map_smulₛₗ]
    rw [hrw]
    suffices h : (⨆ σ ∈ S, Part σ) ≤ (⨆ σ ∈ S'', Part σ).comap (T' k - f c • (1 : Module.End ℂ W)) from h hv
    refine iSup₂_le fun σ hσ w hw => ?_
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hPart σ (hS hσ) k hk w hw, ← sub_smul]
    by_cases h : σ ∈ S''
    · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem h hw))
    · rw [hc σ hσ h, sub_self, zero_smul]; exact Submodule.zero_mem _
  have main : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n → (↑S : Set ι) ⊆ s → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → v ∈ M := by
    intro n
    induction n with
    | zero =>
      intro S hS hSs v hv
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hv
      have hvG : v ∈ G := hG v (by rw [hv]; exact Submodule.zero_mem _)
      rw [hinj v hvG hv]; exact Submodule.zero_mem _
    | succ n ih =>
      intro S hS hSs v hv
      rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
      · exact ih S (by simp [hS0]) hSs v hv
      by_cases hall : ∀ b ∈ S, ∀ k ∈ I, lam b k = lam a k
      · have hvG : v ∈ G := hG v (mono S hSs hv)
        have heig : v ∈ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam a k) := by
          refine Submodule.mem_iInf _ |>.mpr fun k => Submodule.mem_iInf _ |>.mpr fun hk => ?_
          have h0 := key S ∅ hSs k hk (lam a k) (fun σ hσ _ => hall σ hσ k hk) v hv
          simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at h0
          have hmG : T k v - lam a k • v ∈ G := hG _ (by rw [h0]; exact Submodule.zero_mem _)
          have := hinj _ hmG h0
          rw [Module.End.mem_eigenspace_iff]
          exact sub_eq_zero.mp this
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (hSs ha) (Submodule.mem_inf.mpr ⟨hvG, heig⟩))
      · push_neg at hall
        obtain ⟨b, hb, k, hk, hne⟩ := hall
        have hcb := Finset.card_erase_of_mem hb
        have hca := Finset.card_erase_of_mem ha
        have hsub : ∀ x, (↑(S.erase x) : Set ι) ⊆ s := fun x y hy => hSs (Finset.mem_of_mem_erase hy)
        have h1 := ih (S.erase b) (by omega) (hsub b) _
          (key S (S.erase b) hSs k hk (lam b k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have h2 := ih (S.erase a) (by omega) (hsub a) _
          (key S (S.erase a) hSs k hk (lam a k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have hv' : v = (lam a k - lam b k)⁻¹ • ((T k v - lam b k • v) - (T k v - lam a k • v)) := by
          rw [sub_sub_sub_cancel_left, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul]
        rw [hv']; exact M.smul_mem _ (M.sub_mem h1 h2)

  have hv2 : e v ∈ ⨆ σ, ⨆ (_ : σ ∈ s), Part σ := hv
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv2
  have hle : (⨆ σ ∈ S, ⨆ (_ : σ ∈ s), Part σ) ≤ ⨆ σ ∈ S.filter (· ∈ s), Part σ :=
    iSup₂_le fun σ hσ => iSup_le fun hs =>
      le_iSup₂_of_le (f := fun σ (_ : σ ∈ S.filter (· ∈ s)) => Part σ) σ (Finset.mem_filter.mpr ⟨hσ, hs⟩) le_rfl
  exact main _ _ le_rfl (fun x hx => (Finset.mem_filter.mp hx).2) v (hle hS)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtOneParameter
section
noncomputable section

open Filter Topology MeasureTheory

namespace GlobalTheory.LocWeil.DerComm

theorem _root_.GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter {A : Type} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (φ : ℝ → A) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hm : ∀ s t : ℝ, φ (s + t) = φ s * φ t) : DifferentiableAt ℝ φ 0 := by
  have hφ := hc
  have hadd := hm
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > (0 : ℝ), ∀ s : ℝ, |s| ≤ δ → ‖1 - φ s‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.mp hφ.continuousAt (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hs' : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero]; linarith
    have := h hs'
    rw [dist_eq_norm, h0, norm_sub_rev] at this
    exact this.le
  set E : A := δ⁻¹ • ∫ s in (0 : ℝ)..δ, (1 - φ s) with hE
  have hEn : ‖E‖ < 1 := by
    have hI : ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      apply hball
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [sub_zero, abs_of_pos hδ] at hI
    rw [hE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ δ⁻¹ * (1 / 2 * δ) := by gcongr
      _ < 1 := by field_simp; norm_num
  set G : ℝ → A := fun x => ∫ s in (0 : ℝ)..x, φ s with hG
  have hint : ∀ t : ℝ, φ t * (1 - E) = δ⁻¹ • (G (t + δ) - G t) := by
    intro t
    have hC : 1 - E = δ⁻¹ • ∫ s in (0 : ℝ)..δ, φ s := by
      rw [hE, intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul, inv_mul_cancel₀ hδ.ne',
        one_smul, sub_sub_cancel]
    rw [hC, mul_smul_comm, hG,
      intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)]
    congr 1
    have key := (ContinuousLinearMap.mul ℝ A (φ t)).intervalIntegral_comp_comm
      (hφ.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at key
    rw [← key]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun s => φ s) t]
    simp [add_comm]
  set u : Aˣ := Units.oneSub E hEn with hu
  have hrep : φ = fun t => (δ⁻¹ • (G (t + δ) - G t)) * ↑u⁻¹ := by
    funext t
    rw [← hint t]
    have : (1 - E : A) = ↑u := by rw [hu, Units.val_oneSub]
    rw [this, Units.mul_inv_cancel_right]
  have hGd : ∀ x : ℝ, DifferentiableAt ℝ G x := fun x =>
    (hφ.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  rw [hrep]
  have h1 : DifferentiableAt ℝ (fun t => G (t + δ)) 0 :=
    (hGd (0 + δ)).comp (0 : ℝ) (differentiableAt_id.add_const δ)
  have h2 : DifferentiableAt ℝ (fun t => δ⁻¹ • (G (t + δ) - G t)) 0 :=
    by
      have h3 := (h1.sub (hGd 0)).const_smul δ⁻¹
      exact h3
  exact h2.mul_const _

section Alg

variable {S U : Type} [AddCommGroup S] [Module ℂ S]

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)

variable {β b b'}

variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}

section Main

variable {Γ I : Type} [Group Γ] (ω : Γ →* Module.End ℂ S) (G : Γ →* (U →L[ℝ] U)) (ev : I → S →ₗ[ℂ] ℂ) {f : S}
  {N : Submodule ℂ S}
  (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) (hκ : κ ≠ 0)
  (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
  (hω : ∀ q u, ω q * d u = d (G q u) * ω q) (hG : ∀ q x y, β (G q x) (G q y) = β x y)
  (hN : ∀ Φ, Φ ∈ N ↔ ∃ a ∈ Algebra.adjoin ℂ (Set.range d), a f = Φ)
  (hvac : ∀ B ∈ Algebra.adjoin ℂ (Set.range d), (∀ u, B (d u f) = d u (B f)) → ∃ c : ℂ, B f = c • f)
  (hev : ∀ Φ Ψ, (∀ w, ev w Φ = ev w Ψ) → Φ = Ψ)
  (hline : ∀ w u, ∃ ℓ : ℝ → S →ₗ[ℂ] ℂ, ℓ 0 = ev w ∧ (∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (d u Ψ)) s) ∧
    ∀ s, ∃ (c : ℂ) (w' : I), ∀ Ψ, ℓ s Ψ = c * ev w' Ψ)

end Main

end Alg

end GlobalTheory.LocWeil.DerComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EntrySumMulLe
section
namespace GlobalTheory.EntrySumMulBound

theorem entrySum_mul_le :
    (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → ℝ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) ↦ ∑ i : n, ∑ j : n, ‖M i j‖); ∀ {n : Type} [inst : Fintype n] (A B : Matrix n n ℂ), d1 (A * B) ≤ d1 A * d1 B) := by
  intro d1 n inst A B
  show ∑ i : n, ∑ j : n, ‖(A * B) i j‖ ≤ (∑ i : n, ∑ k : n, ‖A i k‖) * (∑ l : n, ∑ j : n, ‖B l j‖)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : n, ‖(A * B) i j‖ ≤ ∑ j : n, ∑ k : n, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : n, ‖A i k‖ * ∑ j : n, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : n, ‖A i k‖ * ∑ l : n, ∑ j : n, ‖B l j‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : n, ‖B l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : n, ‖A i k‖) * ∑ l : n, ∑ j : n, ‖B l j‖ := (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntrySumMulBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPowEqOneOfValuationSubLtOne
section
universe u_1

namespace GlobalTheory.PowEqOneValuation

theorem val_eq_one_of_pow_eq_one {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {m : ℕ} (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : v x = 1 := by
  have h : v x ^ m = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_left hm).1 h

theorem val_one_sub_pow_lt {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {u : Ω} (hu : v u = 1) (h : v (1 - u) < 1) (i : ℕ) :
    v (1 - u ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - u ^ (i + 1) = (1 - u) + u * (1 - u ^ i) := by ring
    rw [e]
    refine v.map_add_lt h ?_
    rw [map_mul, hu, one_mul]
    exact ih

theorem eq_of_pow_eq_one_of_valuation_sub_lt_one {Ω : Type u_1} [inst : Field Ω]
    (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω} (h1 : ζ ^ m = 1) (h2 : ζ' ^ m = 1)
    (hm : ¬ A.valuation (m : Ω) < 1) (h : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simp
  have v1 := val_eq_one_of_pow_eq_one A.valuation hm0 h1
  have v2 := val_eq_one_of_pow_eq_one A.valuation hm0 h2
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp at v1
  by_contra hne
  set u : Ω := ζ' / ζ with hu
  have hu1 : u ≠ 1 := by
    intro e
    apply hne
    rw [hu, div_eq_one_iff_eq hz] at e
    exact e.symm
  have hum : u ^ m = 1 := by rw [hu, div_pow, h1, h2, div_one]
  have vu : A.valuation u = 1 := by rw [hu, map_div₀, v1, v2, div_one]
  have v1u : A.valuation (1 - u) < 1 := by
    have e : 1 - u = (ζ - ζ') / ζ := by rw [hu, sub_div, div_self hz]
    rw [e, map_div₀, v1, div_one]
    exact h
  have hs : ∑ i ∈ Finset.range m, u ^ i = 0 := by
    have g := geom_sum_mul u m
    rw [hum, sub_self] at g
    exact (mul_eq_zero.1 g).resolve_right (sub_ne_zero.2 hu1)
  have hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - u ^ i) := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  apply hm
  rw [hm']
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => val_one_sub_pow_lt A.valuation vu v1u i

end GlobalTheory.PowEqOneValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmEqOfPsumEq
section
namespace GlobalTheory.EsymmOfPowerSums

open MvPolynomial

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ d → ∑ i : Fin d, a i ^ k = ∑ i : Fin d, b i ^ k) :
    ∀ k ≤ d, (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k)
      = (MvPolynomial.aeval b : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    apply mul_left_cancel₀ hk0
    have key := MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k
    have ha := congrArg (MvPolynomial.aeval a) key
    have hb := congrArg (MvPolynomial.aeval b) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb
    rw [ha, hb]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [ih p.1 h2 (by omega)]
    congr 1
    have := h p.2 (by omega) (by omega)
    simpa [MvPolynomial.psum] using this

end GlobalTheory.EsymmOfPowerSums
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEntriesLeExp
section
namespace GlobalTheory.EntriesExpBound

theorem exists_nat_le_exp (x : WithZero (Multiplicative ℤ)) :
    ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log x).toNat, ?_⟩
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (Int.self_le_toNat _)

theorem exists_entries_le_exp {K : Type} [inst : Field K]
    [inst_1 : Valued K (WithZero (Multiplicative ℤ))] {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ (k : ℕ), ∀ (r s : Fin m),
      (Valued.v : K → WithZero (Multiplicative ℤ)) (A r s) ≤ WithZero.exp (↑k : ℤ) := by
  choose f hf using fun p : Fin m × Fin m =>
    exists_nat_le_exp ((Valued.v : K → WithZero (Multiplicative ℤ)) (A p.1 p.2))
  refine ⟨Finset.univ.sup f, fun r s => (hf (r, s)).trans ?_⟩
  exact WithZero.exp_le_exp.mpr
    (Int.ofNat_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ (r, s))))

end GlobalTheory.EntriesExpBound
end

