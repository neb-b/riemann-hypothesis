module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralContinuousMultilinearMapPiMeasure
section
open MeasureTheory

namespace GlobalTheory.MultilinFubini

theorem aestronglyMeasurable_pi_of_forall {α : Type*} {m0 : MeasurableSpace α} {ν : Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : ∀ i, α → E i} (hf : ∀ i, AEStronglyMeasurable (f i) ν) :
    AEStronglyMeasurable (fun x i => f i x) ν := by
  have key : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x (i : ι) => if i ∈ s then f i x else 0) ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, if_false]; exact aestronglyMeasurable_const
    | insert a s ha ih =>
      have hc : Continuous (fun p : E a × (∀ i, E i) => Function.update p.2 a p.1) :=
        continuous_snd.update a continuous_fst
      refine (hc.comp_aestronglyMeasurable ((hf a).prodMk ih)).congr (ae_of_all _ fun x => ?_)
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
  simpa using key Finset.univ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

def vecOn (g : ∀ i, X i → E i) (s : Finset ι) (m : ∀ i, E i) (x : ∀ i : s, X i) : ∀ i, E i :=
  fun i => if h : i ∈ s then g i (x ⟨i, h⟩) else m i

theorem integrable_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) (m : ∀ i, E i) :
    Integrable (fun x => Φ (vecOn g s m x)) (Measure.pi fun i : s => μ i) := by
  have hmeas : AEStronglyMeasurable (fun x => vecOn g s m x) (Measure.pi fun i : s => μ i) := by
    refine aestronglyMeasurable_pi_of_forall (f := fun i x => vecOn g s m x i) fun i => ?_
    by_cases hi : i ∈ s
    · simp only [vecOn, dif_pos hi]
      exact (hg i).1.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun j : s => μ j) ⟨i, hi⟩)
    · simp only [vecOn, dif_neg hi]; exact aestronglyMeasurable_const
  have hdom : Integrable (fun x : ∀ j : s, X j => ‖Φ‖ * ((∏ j : s, ‖g j (x j)‖) * ∏ i ∈ sᶜ, ‖m i‖))
      (Measure.pi fun i : s => μ i) :=
    ((Integrable.fintype_prod_dep (f := fun (j : s) (y : X j) => ‖g j y‖)
      fun j => (hg j).norm).mul_const _).const_mul _
  refine hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => ?_)
  refine (Φ.le_opNorm _).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.prod_mul_prod_compl s]
  congr 1
  · rw [← Finset.prod_coe_sort s]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [vecOn, j.2]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [vecOn, Finset.mem_compl.1 hi]

theorem integral_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, CompleteSpace (E i)] [CompleteSpace F]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) : ∀ m : ∀ i, E i,
    ∫ x, Φ (vecOn g s m x) ∂(Measure.pi fun i : s => μ i) =
      Φ (fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Measure.pi_of_empty (x := fun i => isEmptyElim i)]
    have hc : (fun x : ∀ i : (∅ : Finset ι), X i => Φ (vecOn g ∅ m x)) = fun _ => Φ m := by
      funext x; congr 1
    rw [hc]; simp
  | insert a s ha ih =>
    intro m
    rw [Finset.insert_eq]
    have hd : Disjoint ({a} : Finset ι) s := Finset.disjoint_singleton_left.2 ha
    have hmp := measurePreserving_piFinsetUnion hd μ
    letI : Unique ↥({a} : Finset ι) :=
      ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun j => Subtype.ext (Finset.mem_singleton.1 j.2)⟩
    have hpt : ∀ p : (∀ i : ({a} : Finset ι), X i) × (∀ i : s, X i),
        vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p) =
          vecOn g s (Function.update m a (g a (p.1 default))) p.2 := by
      rintro ⟨y, z⟩
      have he : (MeasurableEquiv.piFinsetUnion X hd (y, z) : ∀ i : ↥({a} ∪ s), X i) =
          Equiv.piFinsetUnion X hd (y, z) := rfl
      funext i
      by_cases hia : i = a
      · subst hia
        have h1 : i ∈ ({i} : Finset ι) ∪ s := by simp
        simp only [vecOn, dif_pos h1, dif_neg ha, Function.update_self, he]
        rw [Equiv.piFinsetUnion_left X hd (Finset.mem_singleton_self i)]
        rfl
      · by_cases his : i ∈ s
        · have h1 : i ∈ ({a} : Finset ι) ∪ s := by simp [his]
          simp only [vecOn, dif_pos h1, dif_pos his, he]
          rw [Equiv.piFinsetUnion_right X hd his]
        · have h1 : i ∉ ({a} : Finset ι) ∪ s := by simp [his, hia]
          simp only [vecOn, dif_neg h1, dif_neg his, Function.update_of_ne hia]
    have hint : Integrable (fun p => Φ (vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p)))
        ((Measure.pi fun i : ({a} : Finset ι) => μ i).prod (Measure.pi fun i : s => μ i)) :=
      (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
        (integrable_vecOn μ Φ g hg _ m)
    rw [← hmp.integral_comp', integral_prod _ hint]
    simp only [hpt, ih]
    set w : ∀ i, E i := fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i with hw
    have hupd : ∀ c : E a, (fun i => if i ∈ s then ∫ y, g i y ∂μ i else Function.update m a c i) =
        Function.update w a c := by
      intro c; funext i
      by_cases hia : i = a
      · subst hia; simp [hw, ha]
      · by_cases his : i ∈ s
        · simp [hw, his, Function.update_of_ne hia]
        · simp [hw, his, Function.update_of_ne hia]
    simp only [hupd]
    have hL : ∀ c : E a, Φ (Function.update w a c) = Φ.toContinuousLinearMap w a c := fun c => rfl
    simp only [hL]
    have h1 := (measurePreserving_piUnique (fun i : ({a} : Finset ι) => μ i)).integral_comp'
      (fun t => Φ.toContinuousLinearMap w a (g a t))
    rw [show (∫ x : ∀ i : ({a} : Finset ι), X i, Φ.toContinuousLinearMap w a (g a (x default))
        ∂Measure.pi fun i : ({a} : Finset ι) => μ i) = ∫ t, Φ.toContinuousLinearMap w a (g a t) ∂μ a from h1]
    rw [(Φ.toContinuousLinearMap w a).integral_comp_comm (hg a), ← hL]
    congr 1
    funext i
    by_cases hia : i = a
    · subst hia; simp [hw]
    · by_cases his : i ∈ s
      · simp [hw, his, Function.update_of_ne hia]
      · simp [hw, his, hia, Function.update_of_ne hia]

theorem integral_multilinear_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  intro ι _ _ X _ μ _ E _ _ _ F _ _ _ Φ g hg
  constructor
  · have hmeas : AEStronglyMeasurable (fun x : ∀ i, X i => fun i => g i (x i)) (Measure.pi μ) :=
      aestronglyMeasurable_pi_of_forall (f := fun i (x : ∀ i, X i) => g i (x i)) fun i =>
        (hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
    have hdom : Integrable (fun x : ∀ i, X i => ‖Φ‖ * ∏ i, ‖g i (x i)‖) (Measure.pi μ) :=
      (Integrable.fintype_prod_dep (f := fun i (y : X i) => ‖g i y‖) fun i => (hg i).norm).const_mul _
    exact hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => Φ.le_opNorm _)
  · let e : (↥(Finset.univ : Finset ι)) ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ
    have hmp := measurePreserving_piCongrLeft μ e
    rw [← hmp.integral_comp']
    have hpt : ∀ z : ∀ i : (Finset.univ : Finset ι), X i,
        (fun i => g i (MeasurableEquiv.piCongrLeft X e z i)) = vecOn g Finset.univ 0 z := by
      intro z; funext i
      have h := Equiv.piCongrLeft_apply_apply X e z ⟨i, Finset.mem_univ i⟩
      simp only [vecOn, dif_pos (Finset.mem_univ i)]
      rw [MeasurableEquiv.coe_piCongrLeft]
      exact congrArg (g i) h
    refine ((integral_congr_ae (ae_of_all _ fun z => congrArg Φ (hpt z))).trans
      (integral_vecOn μ Φ g hg Finset.univ 0)).trans ?_
    simp

end GlobalTheory.MultilinFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensity
section
open scoped InnerProductSpace

namespace GlobalTheory

namespace IrreducibleUnitaryDensity

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

noncomputable def diag (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] lemma diag_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    diag n T x j = T (x j) := rfl

noncomputable def incl (j : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)

lemma incl_apply (j : Fin n) (x : H) (i : Fin n) :
    (incl j x : PiLp 2 (fun _ : Fin n => H)) i = (Pi.single j x : Fin n → H) i := rfl

lemma diag_incl (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    diag n T (incl j x) = incl j (T x) := by
  ext i
  simp only [diag_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma sum_incl (x : PiLp 2 (fun _ : Fin n => H)) : ∑ j, incl j (x j) = x := by
  ext i
  simp [incl_apply, Finset.sum_apply]

lemma comm_diag (P : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (c : Fin n → Fin n → ℂ) (hc : ∀ i j x, P (incl j x) i = c i j • x) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) : P (diag n T x) = diag n T (P x) := by
  rw [← sum_incl x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, diag_incl]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  simp [hc]

end IrreducibleUnitaryDensity


open IrreducibleUnitaryDensity in
theorem irreducibleUnitary_density (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)) (hu : ∀ g x, ‖π g x‖ = ‖x‖)
    (hs : ∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H)
    (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)) (h : ∀ g, ∑ j, Λ j (π g (a j)) = 0)
    (φ u : H) : ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := open IrreducibleUnitaryDensity in by
  let a' : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 a
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) :=
    Submodule.span ℂ (Set.range fun g => diag n (π g) a')
  let W := S.topologicalClosure
  have hmul : ∀ g g' x, diag n (π g) (diag n (π g') x) = diag n (π (g * g')) x := by
    intro g g' x; ext i; simp
  have hone : ∀ x, diag n (π 1) x = x := by
    intro x; ext i; simp
  have hclos : ∀ (K : Submodule ℂ (PiLp 2 (fun _ : Fin n => H))), IsClosed (K : Set (PiLp 2 (fun _ : Fin n => H))) →
      (∀ g, diag n (π g) a' ∈ K) → W ≤ K := by
    intro K hK hg
    refine Submodule.topologicalClosure_minimal S ?_ hK
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hg g
  have hgen : ∀ g, diag n (π g) a' ∈ W := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hinv : ∀ g, ∀ x ∈ W, diag n (π g) x ∈ W := by
    intro g x hx
    have := hclos (W.comap (diag n (π g)).toLinearMap)
      (S.isClosed_topologicalClosure.preimage (diag n (π g)).continuous)
      (fun g' => by
        change diag n (π g) (diag n (π g') a') ∈ W
        rw [hmul]; exact hgen _) hx
    exact this
  have hinner : ∀ g (x y : H), ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (π g).toLinearMap (hu g)).inner_map_map x y
  have hinner' : ∀ g x y, ⟪diag n (π g) x, diag n (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro g x y
    simp [PiLp.inner_apply, hinner]
  have hinv' : ∀ g, ∀ x ∈ Wᗮ, diag n (π g) x ∈ Wᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    have h1 : w = diag n (π g) (diag n (π g⁻¹) w) := by rw [hmul, mul_inv_cancel, hone]
    rw [h1, hinner']
    exact hx _ (hinv _ _ hw)
  haveI : CompleteSpace W := S.isClosed_topologicalClosure.completeSpace_coe
  let P := W.starProjection
  have hP : ∀ g x, P (diag n (π g) x) = diag n (π g) (P x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (W.starProjection_apply_mem x)) ?_
    rw [← map_sub]
    exact hinv' g _ (W.sub_starProjection_mem_orthogonal x)
  have hblock : ∀ i j : Fin n, ∃ c : ℂ, ∀ x, P (incl j x) i = c • x := by
    intro i j
    obtain ⟨c, hc⟩ := hs ((PiLp.proj 2 (fun _ : Fin n => H) i).comp (P.comp (incl j))) (by
      intro g
      ext x
      change P (incl j (π g x)) i = π g (P (incl j x) i)
      rw [← diag_incl, hP, diag_apply])
    exact ⟨c, fun x => by simpa using congrArg (fun B : H →L[ℂ] H => B x) hc⟩
  choose c hc using hblock
  let R : H →L[ℂ] H := (innerSL ℂ φ).smulRight u
  have ha : a' ∈ W := hone a' ▸ hgen 1
  have hRa : diag n R a' ∈ W := by
    have h1 : P a' = a' := Submodule.starProjection_eq_self_iff.2 ha
    rw [← h1, ← comm_diag P c hc]
    exact W.starProjection_apply_mem _
  let L : PiLp 2 (fun _ : Fin n => H) →L[ℂ] ℂ :=
    ∑ j, (Λ j).comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  have hL : ∀ x, L x = ∑ j, Λ j (x j) := by
    intro x; simp [L]
  have hker : W ≤ LinearMap.ker L.toLinearMap := by
    refine hclos _ (ContinuousLinearMap.isClosed_ker L) fun g => ?_
    change L _ = 0
    rw [hL]
    exact h g
  have h0 : L (diag n R a') = 0 := hker hRa
  rw [hL] at h0
  simpa [R, a'] using h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
section
namespace GlobalTheory.PiIsotypic

open Representation

theorem nontrivial_of_isIrreducible {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  haveI := h
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule K V))).symm)

theorem exists_irreducible_subrep {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

def subrepOrderIso {K G V V' : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : Representation K G V) (τ : Representation K G V')
    (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v)) :
    Subrepresentation σ ≃o Subrepresentation τ where
  toFun T := ⟨T.toSubmodule.map (e : V →ₗ[K] V'), by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨σ g v, T.apply_mem_toSubmodule g hv, (he g v).symm⟩⟩
  invFun U := ⟨U.toSubmodule.comap (e : V →ₗ[K] V'), by
    intro g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact U.apply_mem_toSubmodule g hv⟩
  left_inv T := Subrepresentation.ext (Submodule.comap_map_eq_of_injective e.injective _)
  right_inv U := Subrepresentation.ext (Submodule.map_comap_eq_of_surjective e.surjective _)
  map_rel_iff' {a b} := by
    show a.toSubmodule.map (e : V →ₗ[K] V') ≤ b.toSubmodule.map (e : V →ₗ[K] V') ↔
      a.toSubmodule ≤ b.toSubmodule
    exact Submodule.map_le_map_iff_of_injective e.injective _ _

theorem isIrreducible_of_linearEquiv {K G V V' : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K V'] (σ : Representation K G V)
    (τ : Representation K G V') (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v))
    (h : σ.IsIrreducible) : τ.IsIrreducible := by
  haveI := h
  exact (subrepOrderIso σ τ e he).symm.isSimpleOrder

end GlobalTheory.PiIsotypic

namespace GlobalTheory.PiIsotypic

open Representation

theorem isotypic_factor_of_isIrreducible_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  intro ι _ _ G _ _ W _ _ _ ρ hρ i
  classical
  haveI : Nontrivial W := nontrivial_of_isIrreducible ρ hρ
  let ρi : Representation ℂ (G i) W := ρ.comp (MonoidHom.mulSingle G i)
  obtain ⟨S, hS⟩ := exists_irreducible_subrep ρi
  let n := Module.finrank ℂ S.toSubmodule
  let e : S.toSubmodule ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let τ : Representation ℂ (G i) (Fin n → ℂ) :=
    { toFun := fun g => e.toLinearMap ∘ₗ S.toRepresentation g ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hτe : ∀ g v, τ g (e v) = e (S.toRepresentation g v) := by
    intro g v; simp [τ]
  have hτ : τ.IsIrreducible := isIrreducible_of_linearEquiv S.toRepresentation τ e hτe hS
  let φ0 : (Fin n → ℂ) →ₗ[ℂ] W := S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have hφ0 : ∀ g z, φ0 (τ g z) = ρ (Pi.mulSingle i g) (φ0 z) := by
    intro g z
    simp [φ0, τ]
    rfl
  have hinj : Function.Injective φ0 :=
    Subtype.val_injective.comp e.symm.injective
  refine ⟨n, τ, hτ, ⟨φ0, hinj, hφ0⟩, ?_⟩
  set T : Set W := {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W,
    (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} with hTdef
  have hstab : ∀ g y, y ∈ T → ρ g y ∈ T := by
    rintro g y ⟨φ, hφ, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
    let g' : ∀ j, G j := g * Pi.mulSingle i (g i)⁻¹
    have hcomm : ∀ h : G i, g' * Pi.mulSingle i h = Pi.mulSingle i h * g' := by
      intro h
      funext j
      by_cases hj : j = i
      · subst hj
        simp [g']
      · simp [g', Pi.mulSingle_eq_of_ne hj]
    have hg : g = g' * Pi.mulSingle i (g i) := by
      simp only [g', mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, mul_one]
    refine ⟨ρ g' ∘ₗ φ, ?_, LinearMap.mem_range.2 ⟨τ (g i) z, ?_⟩⟩
    · intro h z'
      simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    · simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, ← hg]
  let U : Subrepresentation ρ := ⟨Submodule.span ℂ T, fun g v hv => by
    have hle : Submodule.span ℂ T ≤ (Submodule.span ℂ T).comap (ρ g) :=
      Submodule.span_le.2 (fun y hy => Submodule.subset_span (hstab g y hy))
    exact hle hv⟩
  haveI := hρ
  rcases eq_bot_or_eq_top U with h | h
  · exfalso
    have hspan : Submodule.span ℂ T = ⊥ := congrArg Subrepresentation.toSubmodule h
    haveI : Nontrivial (Fin n → ℂ) := nontrivial_of_isIrreducible τ hτ
    obtain ⟨z, hz⟩ := exists_ne (0 : Fin n → ℂ)
    have hmem : φ0 z ∈ Submodule.span ℂ T :=
      Submodule.subset_span ⟨φ0, hφ0, LinearMap.mem_range.2 ⟨z, rfl⟩⟩
    rw [hspan, Submodule.mem_bot] at hmem
    exact hz (hinj (by rw [hmem, map_zero]))
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.PiIsotypic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory

open scoped Pointwise

theorem lintegral_fundamentalDomain_le_of_meets_orbits
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) (_hS : MeasurableSet S)
    (hmeet : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (_hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕 := by
    intro g hg
    obtain ⟨γ, hγ, hγS⟩ := hmeet g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    refine Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩
    show (γ⁻¹ : G) * (γ * g) = g
    group
  calc ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in ⋃ γ : Γ, γ • S ∩ 𝓕, f g ∂ν := lintegral_mono_set hsub
    _ ≤ ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f g ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f (γ⁻¹ • g) ∂ν := by
        refine tsum_congr fun γ => ?_
        congr 1
        funext g
        show f g = f ((γ⁻¹ : Γ) * g)
        exact (hinv _ (γ⁻¹ : Γ).2 g).symm
    _ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm

end GlobalTheory
end

