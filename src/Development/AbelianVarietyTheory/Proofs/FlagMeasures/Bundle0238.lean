module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.Cov

theorem covol_of_act {G α : Type} [Group G] [MeasurableSpace α] (act : G → α → α) (h1 : ∀ x, act 1 x = x)
    (h2 : ∀ s t x, act (s * t) x = act s (act t x)) (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α)
    (hm : ∀ s, Measurable (act s)) (cA : Countable A) (cB : Countable B) (hR : μ Rᶜ = 0)
    (hinv : ∀ s ∈ A ⊔ B, (∀ x ∈ R, act s x ∈ R) ∧ μ.map (act s) = μ) (hAB : A.relIndex B ≠ 0) (hBA : B.relIndex A ≠ 0)
    (hΩ : MeasurableSet Ω) (hK : MeasurableSet K) (fA : ∀ x ∈ R, ∃! s, s ∈ A ∧ act s x ∈ Ω)
    (fB : ∀ x ∈ R, ∃! s, s ∈ B ∧ act s x ∈ K) : μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  letI : MulAction G α := { smul := act, one_smul := h1, mul_smul := h2 }
  exact _root_.GlobalTheory.CovolIdx.measure_eq_invVol_mul G α μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB

theorem continuous_lmulM {k r : ℕ} (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem rset_mul {k r : ℕ} {γ : Mat k r} (hu : IsUnit γ.det) {a b : Mat k r} (ha : a ∈ Rset k r γ) (hb : b ∈ Rset k r γ) :
    a * b ∈ Rset k r γ := by
  refine ⟨WeylGroupFacts.mem_n_mul ha.1 hb.1, ?_⟩
  have e : γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := by
    have : (γ * a * γ⁻¹) * (γ * b * γ⁻¹) = γ * a * (γ⁻¹ * γ) * b * γ⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, nonsing_inv_mul _ hu, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact WeylGroupFacts.mem_n_mul ha.2 hb.2

theorem countable_aut (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Countable (V ≃ₗ[K] V) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable V := (Module.finBasis K V).equivFun.injective.countable
  let b := Module.finBasis K V
  refine Function.Injective.countable (f := fun s : V ≃ₗ[K] V => fun i => s (b i)) fun s t e => ?_
  exact LinearEquiv.toLinearMap_injective (b.ext fun i => congrFun e i)

theorem cov_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g hP hd hF hN hv gg Λ Kf hgg hT hKf
  obtain ⟨hex, hsep, hsub, -⟩ := RealMat.real_points K V H hK r N k ι σ β Φ z z' g hP hd hF
  have hι : Nonempty ι := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    exact ⟨(hP.2 w).choose⟩
  obtain ⟨v0⟩ := id hι
  choose m hm using fun s => (hex s).exists
  have hmu : ∀ (s : V ≃ₗ[K] V) (y : ι → Mt k r), (∀ v x, Matrix.of (y v) *ᵥ Φ v x = Φ v (s x)) → y = m s :=
    fun s y hy => (hex s).unique hy (hm s)
  have hH : ∀ v, IsHaarOn (Rset k r (g v)) (lebR0 k r N.j β) := fun v => by
    obtain ⟨-, hz, hz', hT0, ⟨c, hc⟩, -⟩ := hF v
    exact (GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r N.j N.j_le (z v) (z' v) (g v) β c hz hz' hT0 hc).1
  haveI : SigmaFinite (lebR0 k r N.j β) := (hH v0).1
  have hu : ∀ v, IsUnit (g v).det := fun v => RealMat.isUnit_det (hF v).2.2.2.2.1.choose_spec.1
  have hone : m 1 = fun _ => Matrix.of.symm (1 : Mat k r) :=
    (hmu 1 _ fun v x => by simp only [Equiv.apply_symm_apply, Matrix.one_mulVec]; rfl).symm
  have hmul : ∀ s t, m (s * t) = fun v => Matrix.of.symm (Matrix.of (m s v) * Matrix.of (m t v)) := fun s t =>
    (hmu (s * t) _ fun v x => by
      simp only [Equiv.apply_symm_apply]
      rw [← mulVec_mulVec, hm, hm]; rfl).symm
  have h1 : ∀ x : ι → Mt k r, mulP (m 1) x = x := fun x => by
    rw [hone]; funext v
    show (1 : Mat k r) * Matrix.of (x v) = x v
    rw [Matrix.one_mul]; rfl
  have h2 : ∀ s t (x : ι → Mt k r), mulP (m (s * t)) x = mulP (m s) (mulP (m t) x) := fun s t x => by
    rw [hmul]; funext v
    show (Matrix.of (m s v) * Matrix.of (m t v)) * Matrix.of (x v) = Matrix.of (m s v) * (Matrix.of (m t v) * Matrix.of (x v))
    rw [Matrix.mul_assoc]
  have hmeas : ∀ s, Measurable (mulP (k := k) (r := r) (m s)) := fun s =>
    Measurable.of_eval fun v => (continuous_lmulM _).measurable.comp (measurable_pi_apply v)
  have hmR : ∀ s ∈ N.R, m s ∈ RP k r g := fun s hs => hsub ⟨s, hs, hm s⟩
  have hnull : Measure.pi (fun _ : ι => lebR0 k r N.j β) (RP k r g)ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v, Function.eval v ⁻¹' {x : Mt k r | Matrix.of x ∉ Rset k r (g v)}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ (hH v).2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    exact Set.mem_iUnion.2 ⟨v, hv'⟩
  have hpres : ∀ s ∈ N.R, (Measure.pi fun _ : ι => lebR0 k r N.j β).map (mulP (m s)) =
      Measure.pi fun _ : ι => lebR0 k r N.j β := fun s hs => by
    have e : ∀ v, (lebR0 k r N.j β).map (lmulM (Matrix.of (m s v))) = lebR0 k r N.j β :=
      fun v => (hH v).2.2.2 _ (hmR s hs v)
    haveI : ∀ v, SigmaFinite ((lebR0 k r N.j β).map (lmulM (Matrix.of (m s v)))) := fun v => by rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => lebR0 k r N.j β)
      (f := fun v => lmulM (Matrix.of (m s v))) fun v => (continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  have conv : ∀ (Γ : Subgroup (V ≃ₗ[K] V)) (Ω : Set (ι → Mt k r)), IsFund (realPts Φ (Γ : Set (V ≃ₗ[K] V))) (RP k r g) Ω →
      ∀ x ∈ RP k r g, ∃! s, s ∈ Γ ∧ mulP (m s) x ∈ Ω := by
    intro Γ Ω h x hx
    obtain ⟨m0, ⟨⟨s, hs, hsm⟩, hΩ⟩, hun⟩ := h.2 x hx
    have e : m0 = m s := hmu s m0 hsm
    refine ⟨s, ⟨hs, e ▸ hΩ⟩, fun t ht => ?_⟩
    have e2 : m t = m0 := hun _ ⟨⟨t, ht.1, hm t⟩, ht.2⟩
    exact hsep t s hι fun v x => by rw [← hm t v x, ← hm s v x, e2, e]
  obtain ⟨hLU, -, hz1, -, hRefLat, -⟩ := GlobalTheory.DegCnt.InnerLat.main K V H hK r N gg Λ hgg hT
  have hzL : N.F.z ∈ latL N.F N.F' Λ := by
    have := (hz1 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    simpa using this
  have hΛdata := ((GlobalTheory.HermLat.isUnimod_iff H Λ).1 hT.1.1).1
  have hΛ : Submodule.IsFullLattice K Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg K hΛdata.1, span_eq_top := hΛdata.2 }
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    refine { toIsLattice := hRefLat, span_eq_top := ?_ }
    obtain ⟨-, -, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hP : N.Pi ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
      rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
      exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
        fun _ hx => Submodule.mem_sup_left hx)
    have hW : N.Wt ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
      intro x hx
      have hxW : x ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hx
      obtain ⟨c, hc, hcx⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛdata.2 x
      rw [← Submodule.smul_mem_iff _ hc]
      apply Submodule.subset_span
      apply Submodule.mem_sup_right
      refine ⟨⟨?_, Submodule.mem_sup_left hcx⟩, N.Wn.smul_mem c hxW⟩
      rw [hUp]
      exact Submodule.mem_sup_left (N.Wn.smul_mem c hxW)
    apply eq_top_iff.mpr
    rw [← hC.sup_eq_top]
    exact sup_le hW hP
  obtain ⟨Ω, hΩ, -, hΩle⟩ := _root_.GlobalTheory.DegVol.RefCov.covol_ref K V H hK r N k ι σ β Φ z z' g hP hd hF hN hv (latL N.F N.F' Λ) hLU hzL
  have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
  have hc1 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hRefFull hΛ).1
  have hc2 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hΛ hRefFull).1
  haveI := countable_aut K V
  have key := covol_of_act (fun s x => mulP (m s) x) h1 h2 (Measure.pi fun _ : ι => lebR0 k r N.j β) (RP k r g)
    (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) Ω Kf hmeas inferInstance inferInstance hnull
    (fun s hs => by
      have hsR : s ∈ N.R := (sup_le inf_le_left inf_le_left : _ ≤ N.R) hs
      exact ⟨fun x hx v => rset_mul (hu v) (hmR s hsR v) (hx v), hpres s hsR⟩)
    hc1 hc2 hΩ.1 hKf.1 (conv _ _ hΩ) (conv _ _ hKf)
  have hom : 0 ≤ N.om Λ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [key, ENNReal.ofReal_mul hom]
  exact mul_le_mul_right hΩle _

end GlobalTheory.DegVol.Cov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLattice
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

section Corner

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem form_smul_smul' (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : E) (u v : Fin n → E) :
    form σ J (y • u) (x • v) = σ x * y * form σ J u v := by
  simp only [form, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_mem_dInv_mul (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) (i j : ℕ) (u v : Fin n → E)
    (hu : ∀ y ∈ (dInv E j)⁻¹, y • u ∈ Λ) (hv : ∀ x ∈ (dInv E i)⁻¹, x • v ∈ Λ) :
    form σ J u v ∈ dInv E i * dInv E j := by
  have h0 : dInv E i * dInv E j ≠ 0 :=
    mul_ne_zero (FrameDual.dInv_ne_zero i) (FrameDual.dInv_ne_zero j)
  rw [← inv_inv (dInv E i * dInv E j), FractionalIdeal.mem_inv_iff (inv_ne_zero h0)]
  intro z hz
  rw [mul_inv] at hz
  refine FractionalIdeal.mul_induction_on hz (fun x hx y hy => ?_) (fun a b ha hb => ?_)
  · have hsx : σ x ∈ (dInv E i)⁻¹ :=
      FrameDual.Stab.inv hσ (FrameDual.stab_dInv hσ i) (FrameDual.dInv_ne_zero i) x hx
    have h1 := (hΛ.2 (y • u)).1 (hu y hy) ((σ x) • v) (hv _ hsx)
    rw [form_smul_smul', hσ] at h1
    obtain ⟨d, hd⟩ := h1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩
    rw [hd]; ring
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule ha hb

end Corner

theorem Hpk_esI_apply (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem Hpk_mulVec_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_esI_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem map_mulVec_comp {E : Type} [Field E] (φ : E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (v : Fin n → E) : (γ.map φ) *ᵥ (fun i => φ (v i)) = fun i => φ ((γ *ᵥ v) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem corner_entry {E : Type} [Field E] (σ : E →+* E) (φ : E →+* ℂ) (hφ : ∀ x, φ (σ x) = star (φ x))
    {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hJ : J.det ≠ 0)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : Mᴴ * Hpk k r * M = J.map φ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (a b : Fin r) (fa fb : Fin (2 * r + k + 1) → E)
    (sa sb : ℝ) (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (ha : M *ᵥ (fun i => φ (fa i)) = ((sa : ℂ)⁻¹) • bvec (esI k r a))
    (hb : M *ᵥ (fun i => φ (fb i)) = ((sb : ℂ)⁻¹) • bvec (esI k r b)) :
    (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = ((sa * sb : ℝ) : ℂ) * φ (form σ J (γ *ᵥ fb) fa) := by
  have hsa' : (sa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsa
  have hsb' : (sb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsb
  have hdet : (J.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hJ
  have hU : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h => hdet ?_
    rw [← hM, Matrix.det_mul, h, mul_zero]
  have hinv : M⁻¹ *ᵥ bvec (esI k r b) = (sb : ℂ) • fun i => φ (fb i) := by
    have e1 : M⁻¹ *ᵥ (M *ᵥ (fun i => φ (fb i))) = fun i => φ (fb i) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    rw [hb, Matrix.mulVec_smul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hsb', one_smul]
  have hreal : star (M *ᵥ (fun i => φ (fa i))) = M *ᵥ (fun i => φ (fa i)) := by
    rw [ha]; funext j
    simp only [Pi.star_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbv : bvec (esI k r a) = (sa : ℂ) • (M *ᵥ (fun i => φ (fa i))) := by
    rw [ha, smul_smul, mul_inv_cancel₀ hsa', one_smul]
  set X : Fin (2 * r + k + 1) → ℂ := fun i => φ ((γ *ᵥ fb) i) with hX
  have h1 : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = (sb : ℂ) * (M *ᵥ X) (eI k r a) := by
    have : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) =
        ((M * γ.map φ * M⁻¹) *ᵥ bvec (esI k r b)) (eI k r a) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul,
      map_mulVec_comp, Matrix.mulVec_smul]
    rfl
  have h2 : (M *ᵥ X) (eI k r a) = (sa : ℂ) * (star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X)) := by
    rw [← Hpk_mulVec_esI k r a (M *ᵥ X)]
    have e2 : (Hpk k r *ᵥ (M *ᵥ X)) (esI k r a) = bvec (esI k r a) ⬝ᵥ (Hpk k r *ᵥ (M *ᵥ X)) := by
      simp [bvec]
    rw [e2, hbv, smul_dotProduct, smul_eq_mul, ← hreal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have h3 : star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X) = φ (form σ J (γ *ᵥ fb) fa) := by
    rw [hX, map_mulVec_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [form, dotProduct, map_sum, map_mul, hφ]
  rw [h1, h2, h3]
  push_cast; ring

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem corner_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD γ hγ p
  obtain ⟨hCM, -, hJ, hΛ, -, -, hlat, hA, hs, had⟩ := hD
  obtain ⟨-, -, -, hcc⟩ := hCM
  obtain ⟨-, hγΛ⟩ := hγ
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    change τ (σ (σ x)) = τ x
    rw [hcc, hcc, star_star]
  have hcol : ∀ (b : Fin r) (y : E), y ∈ (dInv E (r - (b : ℕ)))⁻¹ → y • (fun i => f i b) ∈ Λ := by
    intro b y hy
    refine hlat (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, y, ?_, ?_⟩)
    · simpa [id1] using hy
    · funext i; simp [sideM]
  have hmap : ∀ v ∈ Λ, γ *ᵥ v ∈ Λ := by
    intro v hv
    have : γ *ᵥ v ∈ latMap γ Λ := ⟨v, hv, rfl⟩
    rwa [hγΛ] at this
  have hc : form (σ : E →+* E) J (γ *ᵥ fun i => f i p.1.2) (fun i => f i p.1.1) ∈
      dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val) := by
    refine form_mem_dInv_mul (σ : E →+* E) hσ J Λ hΛ _ _ _ _ (fun y hy => ?_) (fun x hx => hcol _ x hx)
    rw [← Matrix.mulVec_smul]
    exact hmap _ (hcol _ y hy)
  refine ⟨_, hc, fun w => ?_⟩
  have hJ0 : J.det ≠ 0 := hJ.2
  have hφ : ∀ x, w.embedding ((σ : E →+* E) x) = star (w.embedding x) := fun x => hcc _ x
  have := corner_entry (σ : E →+* E) w.embedding hφ J hJ0 (A w) (hA w) γ p.1.1 p.1.2
    (fun i => f i p.1.1) (fun i => f i p.1.2) (s p.1.1) (s p.1.2) (hs _).ne' (hs _).ne'
    (had w p.1.1).2 (had w p.1.2).2
  simp only [gM]
  rw [this]

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.IntU

theorem hpk_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mulVec_esI (k r : ℕ) (a : Fin r) (z : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ z) (esI k r a) = z (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row]

theorem coord_eI {E : Type} [Field E] {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x y : Fin (2 * r + k + 1) → E) (a : Fin r) (s : ℝ) (hs : s ≠ 0)
    (hy : B *ᵥ (fun i => τ (y i)) = (s : ℂ)⁻¹ • bvec (esI k r a)) :
    (B *ᵥ fun i => τ (x i)) (eI k r a) = (s : ℂ) * τ (form σ J x y) := by
  have key : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) := by
    rw [← hB]
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have lhs : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (s : ℂ)⁻¹ * (B *ᵥ fun i => τ (x i)) (eI k r a) := by
    rw [hy, star_smul, bvec, ← hpk_mulVec_esI k r a (B *ᵥ fun i => τ (x i))]
    simp [Pi.star_def, dotProduct, Pi.single_apply, -Matrix.mulVec_mulVec]
  have rhs : star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) = τ (form σ J x y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, map_sum, map_mul, hτ, RingHom.map_mulVec]
    rfl
  rw [lhs, rhs] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end GlobalTheory.SnMass.VolN.IntU

namespace GlobalTheory.SnMass.VolN.IntU

theorem form_smul_smul {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (c c' : E) (x y : Fin n → E) : form σ J (c • x) (c' • y) = c * σ c' * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_of_pair {E : Type} [Field E] [NumberField E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0) (hst : FrameDual.Stab σ 𝔞⁻¹) (u : E)
    (hu : ∀ c ∈ 𝔟, ∀ c' ∈ 𝔞⁻¹, c * σ c' * u ∈ (algebraMap (𝓞 E) E).range) : u ∈ 𝔞 * 𝔟⁻¹ := by
  have hI : 𝔟 * 𝔞⁻¹ ≠ 0 := mul_ne_zero h𝔟 (inv_ne_zero h𝔞)
  have e : 𝔞 * 𝔟⁻¹ = (𝔟 * 𝔞⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [e, FractionalIdeal.mem_inv_iff hI]
  intro y hy
  refine FractionalIdeal.mul_induction_on hy (fun c hc d hd => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · have := hu c hc (σ d) (hst d hd)
    rw [hσ] at this
    obtain ⟨t, ht⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨t, by rw [ht]; ring⟩
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule h₁ h₂

end GlobalTheory.SnMass.VolN.IntU


open GlobalTheory.SnMass.VolN.IntU in
theorem GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ p
  obtain ⟨hCM, -, hND, hSD, -, -, hTup, hMod, hs, hAd⟩ := hV
  obtain ⟨⟨a, b⟩, hab⟩ := p
  dsimp only
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    show σ (σ x) = x
    exact (Classical.arbitrary (InfinitePlace E)).embedding.injective (by rw [hconj, hconj, star_star])
  set eb : Fin (2 * r + k + 1) → E := fun i => P i b.castSucc with heb
  set fa : Fin (2 * r + k + 1) → E := fun i => f i a with hfa
  refine ⟨form (σ : E →+* E) J (γ *ᵥ eb) fa, ?_, fun w => ?_⟩
  · refine mem_of_pair (σ : E →+* E) hσ _ _ (FrameDual.dInv_ne_zero _) (FrameDual.dInv_ne_zero _)
      ((FrameDual.stab_dInv hσ _).inv hσ (FrameDual.dInv_ne_zero _)) _ ?_
    intro c hc c' hc'
    have h1 : c • eb ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.castAdd r b.castSucc, c, by rw [FrameDual.frameDualTupleIdeals_castAdd]; exact hc, by
        funext i; simp [heb, sideM]⟩)
    have h2 : c' • fa ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.natAdd (r + 1) a, c', by rw [FrameDual.frameDualTupleIdeals_natAdd]; exact hc', by
        funext i; simp [hfa, sideM]⟩)
    have h3 : γ *ᵥ (c • eb) ∈ Λ := by
      rw [← hγ.2]; exact ⟨_, h1, rfl⟩
    have h4 := (hSD.2 _).1 h3 _ h2
    rwa [Matrix.mulVec_smul, form_smul_smul] at h4
  · set τ := w.embedding with hτ
    have hB := hMod w
    have hdet : IsUnit (A w).det := by
      refine Ne.isUnit fun h0 => hND.2 ?_
      have := congrArg Matrix.det hB
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact (map_eq_zero τ).1 this.symm
    have hsb : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have hbv : bvec (eI k r b) = (s b : ℂ)⁻¹ • (A w *ᵥ fun i => τ (eb i)) := by
      rw [(hAd w b).1, smul_smul, inv_mul_cancel₀ hsb, one_smul]
    have hmap : (γ.map τ *ᵥ fun i => τ (eb i)) = fun i => τ ((γ *ᵥ eb) i) := by
      funext i; exact (RingHom.map_mulVec τ γ eb i).symm
    have hent : gM A γ w (eI k r a) (eI k r b) =
        (s b : ℂ)⁻¹ * (A w *ᵥ fun i => τ ((γ *ᵥ eb) i)) (eI k r a) := by
      have e1 : gM A γ w (eI k r a) (eI k r b) = (gM A γ w *ᵥ bvec (eI k r b)) (eI k r a) := by
        simp [bvec]
      rw [e1, hbv, Matrix.mulVec_smul, gM, Matrix.mulVec_mulVec, Matrix.mul_assoc (A w * γ.map τ),
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap]
      rfl
    show gM A γ w (eI k r a) (eI k r b) = _
    rw [hent, coord_eI (σ : E →+* E) τ (hconj τ) J (A w) hB (γ *ᵥ eb) fa a (s a) (hs a).ne' (hAd w a).2]
    push_cast
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem local_nongeneric_bound_record_family :
    ∀ (C : ℝ), 39 ≤ C → (∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C) ∧
      (∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C ∧ Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBoundOfLargeRank D C ∧ Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C) ∧
      ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C ∧ Formalism.MainNotions.UniformConstantsAndStatements.admF5 Fm C := by
  intro C hC
  have h1 : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
    intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP
    exact _root_.GlobalTheory.HL.AbstractBound.ngAt C hC M hM H r k P hk hV hP
  have h2 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C := fun D hk => h1 _ _ hk
  have h3 : ∀ D : D7, Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C := fun D => h2 D
  exact ⟨h1, fun D => ⟨h2 D, h2 D, h3 D⟩, fun Fm => ⟨fun x i => h2 _, fun x i => h3 _⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.St

theorem siegelWeil_volumes : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J ∧ Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J := by
  intro hSW F E _ _ _ _ _ σ hσ n J hJ

  exact hSW F E σ hσ n J hJ

end GlobalTheory.St
end

