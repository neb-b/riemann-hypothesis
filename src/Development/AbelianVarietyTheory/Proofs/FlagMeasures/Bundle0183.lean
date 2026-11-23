module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecGapOfFormula

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.UnipUnimod

section General

open scoped Pointwise NNReal ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem unimod_of_contract (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G}
    (h : IsHaarSub (N : Set G) ν) (a : ℝ → G) (h1 : ∀ s, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) :
    (∀ m ∈ N, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first
  | exact @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | (apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted ..)

end General

theorem unimodular_NW : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  intro n ε W ν hW hν
  obtain ⟨a, Hm, -, ha, -, h1, h3, -⟩ := _root_.GlobalTheory.IsoTorus.split_torus n ε W hW
  have hinv : ∀ s, a (-s) = (a s)⁻¹ := fun s => by
    refine eq_inv_of_mul_eq_one_left (Subtype.ext (Units.ext ?_))
    change umat (a (-s)) * umat (a s) = 1
    rw [ha, ha, Complex.ofReal_neg, neg_smul,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl ((s : ℂ) • Hm)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  refine unimod_of_contract (nwSub ε W) (isClosed_NW ε W) hν a (fun s m hm => (h1 s m hm).1)
    (fun s m hm => ?_) h3
  have := (h1 (-s) m hm).1
  rwa [hinv, inv_inv] at this

end GlobalTheory.UnipUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEquivariant
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.Equivar

theorem rmulM_emb {k r : ℕ} {t : Mat k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (rmulM t : Mt k r → Mt k r) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := rmulM t
      invFun := rmulM t⁻¹
      left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right t (Matrix.of x) ht
      right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht
      continuous_toFun := continuous_rmulM t
      continuous_invFun := continuous_rmulM t⁻¹ }
  exact e.measurableEmbedding

theorem integral_comp_both {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A A' : E →L[ℂ] E) (B B' : F →L[ℂ] F) (h1 : A.comp A' = 1) (h2 : A'.comp A = 1)
    (h3 : B.comp B' = 1) (h4 : B'.comp B = 1) (φ : X → (F →L[ℂ] E)) :
    ∫ x, A.comp ((φ x).comp B) ∂μ = A.comp ((∫ x, φ x ∂μ).comp B) := by
  have a1 : ∀ v, A (A' v) = v := fun v => congrArg (fun f : E →L[ℂ] E => f v) h1
  have a2 : ∀ v, A' (A v) = v := fun v => congrArg (fun f : E →L[ℂ] E => f v) h2
  have a3 : ∀ v, B (B' v) = v := fun v => congrArg (fun f : F →L[ℂ] F => f v) h3
  have a4 : ∀ v, B' (B v) = v := fun v => congrArg (fun f : F →L[ℂ] F => f v) h4
  let L : (F →L[ℂ] E) ≃L[ℂ] (F →L[ℂ] E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.compL ℂ F E E A).comp ((ContinuousLinearMap.compL ℂ F F E).flip B))
    ((ContinuousLinearMap.compL ℂ F E E A').comp ((ContinuousLinearMap.compL ℂ F F E).flip B'))
    (fun f => by ext v; simp [a2, a3]) (fun f => by ext v; simp [a1, a4])
  exact L.integral_comp_comm φ

theorem Iint_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → ∀ γ ∈ GG k r, ∀ t ∈ Sset k r z, ∀ t' ∈ Sset k r z', Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (t * γ * t'⁻¹) = (PiS (psiGen k r z c) π t).comp ((Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (rmulM t '' Om)) (μS'.restrict (rmulM t' '' Om')) σ x y ξ ξ' γ).comp (PiS (psiGen k r z' c') π' t'⁻¹)) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' _ hs hs' x y ξ ξ' Om Om' _ _
    γ _ t ht t' ht'
  obtain ⟨hz, hT, hπ, hμ, -⟩ := hs
  obtain ⟨hz', hT', hπ', hμ', -⟩ := hs'
  have hS := isClosedSub_Sset hz hT
  have hS' := isClosedSub_Sset hz' hT'
  obtain ⟨-, ⟨⟨p1, pm⟩, -⟩, -⟩ := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ
  obtain ⟨-, ⟨⟨q1, qm⟩, -⟩, qa, -⟩ := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z' c' π' hz' hT' hπ'
  have u := ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1 hμ).1 t ht
  have u' := ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z' hz' hT' μS').1 hμ').1 t' ht'
  have dt := isUnit_det_of_mem_GG (hS.1 ht)
  have dt' := isUnit_det_of_mem_GG (hS'.1 ht')
  have hti := hS.2.2.2.2 t ht
  have hti' := hS'.2.2.2.2 t' ht'
  have := hμ.1
  have := hμ'.1
  have e := rmulM_emb dt
  have e' := rmulM_emb dt'
  have m : MeasurePreserving (rmulM t) μS μS := ⟨e.measurable, u⟩
  have m' : MeasurePreserving (rmulM t') μS' μS' := ⟨e'.measurable, u'⟩
  have mp := (m.restrict_image_emb e Om).prod (m'.restrict_image_emb e' Om')
  unfold Iint
  rw [← integral_comp_both _ _ (PiS (psiGen k r z c) π t⁻¹) _ (PiS (psiGen k r z' c') π' t')
    (by rw [← pm t ht _ hti, Matrix.mul_nonsing_inv _ dt, p1])
    (by rw [← pm _ hti t ht, Matrix.nonsing_inv_mul _ dt, p1])
    (by rw [← qm _ hti' _ ht', Matrix.nonsing_inv_mul _ dt', q1])
    (by rw [← qm _ ht' _ hti', Matrix.mul_nonsing_inv _ dt', q1]),
    ← mp.integral_comp (e.prodMap e')]
  have c1 : ∀ᵐ s ∂(μS.restrict Om), Matrix.of s ∈ Sset k r z := ae_restrict_of_ae hμ.2.2.1
  have c2 : ∀ᵐ s ∂(μS'.restrict Om'), Matrix.of s ∈ Sset k r z' := ae_restrict_of_ae hμ'.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae c1, Measure.quasiMeasurePreserving_snd.ae c2]
    with p h1 h2
  have k1 : PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ =
      (PiS (psiGen k r z c) π t).comp (PiS (psiGen k r z c) π (Matrix.of p.1 * t)⁻¹) := by
    rw [← pm t ht _ (hS.2.2.2.2 _ (hS.2.2.2.1 _ h1 _ ht)), Matrix.mul_inv_rev,
      Matrix.mul_nonsing_inv_cancel_left _ _ dt]
  have k2 : PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ =
      (PiS (psiGen k r z' c') π' t').comp (PiS (psiGen k r z' c') π' (Matrix.of p.2 * t')⁻¹) := by
    rw [← qm t' ht' _ (hS'.2.2.2.2 _ (hS'.2.2.2.1 _ h2 _ ht')), Matrix.mul_inv_rev,
      Matrix.mul_nonsing_inv_cancel_left _ _ dt']
  have k3 : act2 (t * γ * t'⁻¹) p = act2 γ (Prod.map (rmulM t) (rmulM t') p) := by
    show Matrix.of p.1 * (t * γ * t'⁻¹) * (Matrix.of p.2)⁻¹ =
      (Matrix.of p.1 * t) * γ * (Matrix.of p.2 * t')⁻¹
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  rw [k1, k2, k3]
  ext η
  rw [← (qa t' ht').2]
  simp only [Prod.map_fst, Prod.map_snd, of_rmulM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, rankOneInnerOperator_apply, map_smul, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.SgInf.Equivar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasis
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.AdSat

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem isSatFlag_of_isAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (_hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) :
    IsSatFlag I (lamX I (1, xf)) j S := by
  classical
  obtain ⟨-, -, hΛ, h1, h2, -, hL, hS⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  let p : ∀ i, (Fin I.n → I.E) →ₗ[I.E] (Fin (j i) → I.E) := fun i => ((T' i)ᴴ * I.J).mulVecLin
  have hsw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := fun i k => by
    simp [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc]
  have pT : ∀ i x, p i (T i *ᵥ x) = x := fun i x => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h2 i).1]; simp
  have pT' : ∀ i k x, k ≠ i → p i (T k *ᵥ x) = 0 := fun i k x hk => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h1 k i).2.2 hk]; simp
  have pS : ∀ i (u : ∀ i, Fin (j i) → I.E), p i (∑ k, T k *ᵥ u k) = u i := fun i u => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single i (fun k _ hk => pT' i k _ hk) (by simp), pT]
  have hsp : ∀ k z, z ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) →
      z = ∑ i, T i *ᵥ p i z ∧ ∀ i : Fin a, ¬ i.castSucc < k → p i z = 0 := fun k z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, -, hu, rfl⟩ := (hS k z).1 hz
      simp only [pS]
      exact ⟨trivial, hu⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, fun i hi => by rw [map_add (f := _), hx.2 i hi, hy.2 i hi, add_zero]⟩
      simp only [map_add (f := _), mulVec_add, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    | smul c x _ hx =>
      refine ⟨?_, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩
      simp only [map_smul, mulVec_smul, ← Finset.smul_sum]
      rw [← hx.1]
  have hmono : Monotone S := fun k l hkl z hz => by
    obtain ⟨u, hu, hu0, rfl⟩ := (hS k z).1 hz
    exact (hS l _).2 ⟨u, hu, fun i hi => hu0 i fun h => hi (h.trans_le hkl), rfl⟩
  refine ⟨?_, hmono, fun i => ?_, fun k y => ⟨fun hy => ⟨?_, Submodule.subset_span hy⟩, ?_⟩, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨u, -, hu0, rfl⟩ := (hS 0 z).1 hz
    have : ∀ i, u i = 0 := fun i => hu0 i (by simp)
    simp [this]
  · have hsup : Submodule.span I.E (S i.succ : Set (Fin I.n → I.E)) =
        Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊔ LinearMap.range (T i).mulVecLin := by
      apply le_antisymm
      · refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨u, hu, hu0, rfl⟩ := (hS _ z).1 hz
        have e1 : ∑ k, T k *ᵥ u k = ∑ k, T k *ᵥ Function.update u i 0 k + T i *ᵥ u i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ (fun k => T k *ᵥ Function.update u i 0 k) (Finset.mem_univ i)]
          rw [Finset.sum_congr rfl (s₁ := univ.erase i) (f := fun k => T k *ᵥ Function.update u i 0 k)
            (g := fun k => T k *ᵥ u k)
            (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])]
          simp [add_comm]
        rw [e1]
        refine Submodule.add_mem_sup (Submodule.subset_span ((hS _ _).2 ⟨_, fun k => ?_, fun k hk => ?_, rfl⟩))
          ⟨u i, rfl⟩
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]; exact hu k
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]
            refine hu0 k fun h => hk ?_
            rw [Fin.castSucc_lt_succ_iff] at h
            exact Fin.castSucc_lt_castSucc_iff.2 (lt_of_le_of_ne h hki)
      · refine sup_le (Submodule.span_mono (hmono (Fin.castSucc_lt_succ).le)) ?_
        letI : Submodule.IsFullLattice I.E (Λ i) := hΛ i
        rw [LinearMap.range_eq_map, ← Submodule.IsFullLattice.span_eq_top (A := I.E) (M := Λ i), Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine (hS _ _).2 ⟨Pi.single i x, fun k => ?_, fun k hk => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; simpa using hx
          · rw [Pi.single_eq_of_ne hki]; exact zero_mem _
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          exact hk Fin.castSucc_lt_succ
        · rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mulVec_zero]) (by simp)]
          simp
    have hinf : Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊓ LinearMap.range (T i).mulVecLin = ⊥ := by
      refine eq_bot_iff.2 ?_
      rintro _ ⟨hz, x, rfl⟩
      have : x = 0 := (pT i x).symm.trans ((hsp _ _ hz).2 i (lt_irrefl _))
      simp [this]
    have hinj : Function.Injective (T i).mulVecLin := fun x y hxy => by
      rw [← pT i x, ← pT i y]; exact congrArg (p i) hxy
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)))
      (LinearMap.range (T i).mulVecLin)
    rw [hinf, ← hsup, LinearMap.finrank_range_of_inj hinj] at this
    simpa [Formalism.HN.rkK] using this
  · obtain ⟨u, hu, -, rfl⟩ := (hS k y).1 hy
    refine (hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simp, zero_mem _, ?_⟩
    have : (fun l => e ((0 : Fin I₀.n → I₀.E) l)) = 0 := by ext; simp
    rw [this]
    simp
  · rintro ⟨hy, hy'⟩
    obtain ⟨u, u', y₀, hu, -, -, hz⟩ := (hL y).1 hy
    have hp : ∀ i, p i y = u i := fun i => by
      have a1 : ∀ k, p i (T' k *ᵥ u' k) = 0 := fun k => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h1 i k).2.1]; simp
      have a2 : ∀ x, p i (T₀ *ᵥ x) = 0 := fun x => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h2 i).2.2]; simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hz, map_add (f := _), map_add (f := _), pS, a2, map_sum]
      simp [a1]
    obtain ⟨b1, b2⟩ := hsp k y hy'
    exact (hS k y).2 ⟨fun i => p i y, fun i => by simpa only [hp] using hu i, b2, b1⟩
  · intro x hx y hy
    obtain ⟨u, -, -, rfl⟩ := (hS _ x).1 hx
    obtain ⟨v, -, -, rfl⟩ := (hS _ y).1 hy
    rw [hform_eq, star_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mulVec_sum, dotProduct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, (h1 i k).1]
    simp

end GlobalTheory.FlagBase.AdSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.RadCov

section Defs

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

def lowers (F : ℕ → Submodule R (Fin n → K)) (c : ℕ) : Submodule R (Matrix (Fin n) (Fin n) K) where
  carrier := {T | ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b}
  zero_mem' := fun b y _ => by simp
  add_mem' := fun {S T} hS hT b y hy => by
    rw [Matrix.add_mulVec]
    exact add_mem (hS b y hy) (hT b y hy)
  smul_mem' := fun r T hT b y hy => by
    rw [Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (hT b y hy)

theorem mem_lowers {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {T : Matrix (Fin n) (Fin n) K} :
    T ∈ lowers F c ↔ ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b := Iff.rfl

def IsDualFlag [StarRing K] (J : Matrix (Fin n) (Fin n) K) (F : ℕ → Submodule R (Fin n → K)) (m : ℕ) : Prop :=
  Monotone F ∧ F 0 = ⊥ ∧ (∀ b, m ≤ b → F b = F m) ∧
    ∀ b, b ≤ m → ∀ y, y ∈ F (m - b) ↔ y ∈ F m ∧ ∀ x ∈ F b, star x ⬝ᵥ (J *ᵥ y) = 0

def Biorth (r : ℕ → ℕ) (m : ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) K)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) K) : Prop :=
  (∀ b, T' b * T b = 1) ∧ (∀ b b', b ≠ b' → T' b * T b' = 0) ∧ ∑ b ∈ Finset.range m, T b * T' b = 1

theorem lowers_succ_le {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) (c : ℕ) :
    lowers F (c + 1) ≤ lowers F c := by
  intro T hT
  rw [mem_lowers] at hT ⊢
  intro b y hy
  exact hT b y (hF (by omega) hy)

theorem lowers_anti {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) : Antitone (lowers F) :=
  antitone_nat_of_succ_le (lowers_succ_le hF)

theorem lowers_mul {F : ℕ → Submodule R (Fin n → K)} {c c' : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F c') : X * Y ∈ lowers F (c + c' + 1) := by
  rw [mem_lowers] at hX hY ⊢
  intro b y hy
  rw [← Matrix.mulVec_mulVec]
  apply hX b
  apply hY (b + c + 1)
  have e : b + c + 1 + c' + 1 = b + (c + c' + 1) + 1 := by omega
  rw [e]
  exact hy

theorem lowers_mul_zero {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F 0) :
    X * Y ∈ lowers F (c + 1) ∧ Y * X ∈ lowers F (c + 1) := by
  have h1 := lowers_mul hX hY
  have h2 := lowers_mul hY hX
  rw [Nat.add_zero] at h1
  rw [Nat.zero_add] at h2
  exact ⟨h1, h2⟩

theorem lowers_eq_bot {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (h0 : F 0 = ⊥)
    (hm : ∀ b, m ≤ b → F b = F m) (hsp : Submodule.span K (F m : Set (Fin n → K)) = ⊤) :
    lowers F m = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [mem_lowers] at hT
  have hzero : ∀ y ∈ (F m : Set (Fin n → K)), T *ᵥ y = 0 := by
    intro y hy
    have hy' : y ∈ F (0 + m + 1) := by
      rw [hm (0 + m + 1) (by omega)]
      exact hy
    have h := hT 0 y hy'
    rw [h0] at h
    exact (Submodule.mem_bot R).1 h
  have hlin : Matrix.toLin' T = 0 := by
    apply LinearMap.ext_on hsp
    intro y hy
    simpa [Matrix.toLin'_apply] using hzero y hy
  have hT0 : T = 0 := by
    apply Matrix.toLin'.injective
    rw [hlin, map_zero]
  exact (Submodule.mem_bot R).2 hT0

theorem lowers_adj [StarRing K] {J : Matrix (Fin n) (Fin n) K} (hJ : Jᴴ = J)
    {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (hF : IsDualFlag J F m) {c : ℕ}
    {T T' : Matrix (Fin n) (Fin n) K} (hT : T ∈ lowers F c) (hadj : J * T' = Tᴴ * J)
    (htop : ∀ y ∈ F m, T' *ᵥ y ∈ F m) : T' ∈ lowers F c := by
  obtain ⟨hmono, h0, hstab, hdual⟩ := hF
  have hleM : ∀ k, F k ≤ F m := by
    intro k
    rcases le_total k m with h | h
    · exact hmono h
    · exact (hstab k h).le
  rw [mem_lowers] at hT ⊢
  intro b y hy
  have hyM : y ∈ F m := hleM _ hy
  rcases le_total m b with hb | hb
  · rw [hstab b hb]
    exact htop y hyM
  ·
    have key : ∀ x ∈ F (m - b), star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = 0 := by
      intro x hx
      have e : star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = star (T *ᵥ x) ⬝ᵥ (J *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.star_mulVec]
      rw [e]
      rcases le_or_gt (b + c + 1) m with hc | hc
      · have hTx : T *ᵥ x ∈ F (m - (b + c + 1)) := by
          apply hT
          have e' : m - (b + c + 1) + c + 1 = m - b := by omega
          rw [e']
          exact hx
        have hy' : y ∈ F (m - (m - (b + c + 1))) := by
          rw [show m - (m - (b + c + 1)) = b + c + 1 by omega]
          exact hy
        exact ((hdual _ (Nat.sub_le _ _) y).1 hy').2 _ hTx
      ·
        have hTx : T *ᵥ x ∈ F 0 := hT 0 x (hmono (by omega) hx)
        rw [h0] at hTx
        rw [(Submodule.mem_bot R).1 hTx, star_zero, zero_dotProduct]
    have hd := hdual (m - b) (Nat.sub_le _ _) (T' *ᵥ y)
    rw [show m - (m - b) = b by omega] at hd
    exact hd.2 ⟨htop y hyM, key⟩

end Defs

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def locFlag (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun y : Fin n → E => P⁻¹ *ᵥ fun l => φ (y l)) '' (F b : Set _))

def PlaceMatch {ι : Type} (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Function.Bijective (fun v => InfinitePlace.mk (φ v)) ∧
    ∀ v, ((InfinitePlace.mk (φ v)).embedding = φ v ∧ X (InfinitePlace.mk (φ v)) = P v) ∨
      ((InfinitePlace.mk (φ v)).embedding = (starRingEnd ℂ).comp (φ v) ∧
        X (InfinitePlace.mk (φ v)) = (P v).map (starRingEnd ℂ))

def pieceHt [StarRing E] (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) : ℝ :=
  Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F (b + 1)) / Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F b)

def covStd (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ℝ :=
  GlobalTheory.FlagBase.covAt E j (GlobalTheory.FlagBase.latAt E j Λ fun _ a b => if a = b then 1 else 0)

end Loc

end GlobalTheory.RadCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

theorem decGap_of_formulaGap : FormulaGap → DecGap := by
  intro hF n ε lam H _ _ σ hlam hDS h hgap hh g hg u hu v hv
  have hU := hDS.2.2.1
  have h1 : ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ := by
    obtain ⟨k, X, hk, hX, hgk⟩ := (polar_decomposition_holds n ε).1 g hg
    have hs' := GlobalTheory.LowKProj.mem_UJset_of_Kset (Kset_star ε hk)
    have hkk : star k * k = 1 := hk.1.1
    have e1 : σ (NormedSpace.exp X) u = σ (star k) (σ g u) := by
      have h := hU.1.2 (star k) hs' g hg
      rw [show star k * g = NormedSpace.exp X by rw [hgk, ← Matrix.mul_assoc, hkk, Matrix.one_mul]] at h
      exact congrArg (fun F : H →L[ℂ] H => F u) h
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (star k) : H →ₗ[ℂ] H), hU.2.1 _ hs'⟩
    have e2 : ⟪σ (star k) v, σ (star k) (σ g u)⟫_ℂ = ⟪v, σ g u⟫_ℂ := L.inner_map_map v (σ g u)
    have hb := dec_exp hF n ε lam H σ hlam hDS h hgap hh X hX u hu (σ (star k) v)
      (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ (Kset_star ε hk) v hv)
    rw [e1, e2, hU.2.1 _ hs' v, ← (GlobalTheory.Count.Cartan.cartan_distances n ε).1 k X hk hX, ← hgk] at hb
    exact hb
  refine ⟨h1, h1.trans ?_⟩
  have h0 : 0 ≤ h := le_trans (by positivity) hh
  obtain ⟨h2, h3⟩ := dOp_facts hg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (decHS_le_decE _ h0 h2 h3) (norm_nonneg u)) (norm_nonneg v)

end GlobalTheory.DecGapBound
end

