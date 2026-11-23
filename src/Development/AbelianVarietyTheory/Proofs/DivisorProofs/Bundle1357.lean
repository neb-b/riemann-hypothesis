module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.SBTransl

theorem exists_nhds_zero_invariant {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {β : Type} [Zero β] (g : X → β) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ V ∈ 𝓝 (0 : X), ∀ x, ∀ u ∈ V, g (x + u) = g x := by
  have hW : ∀ x : X, {u : X | g (x + u) = g x} ∈ 𝓝 (0 : X) := fun x => by
    have h1 : IsOpen {y : X | g y = g x} := hg.isOpen_fiber _
    have h2 : Continuous fun u : X => x + u := continuous_const.add continuous_id
    exact (h2.isOpen_preimage _ h1).mem_nhds (by simp)
  choose W' hW' hW'h using fun x => exists_nhds_zero_half (hW x)
  have hU : ∀ x ∈ tsupport g, {y : X | y - x ∈ W' x} ∈ 𝓝 x := fun x _ => by
    have h2 : Continuous fun y : X => y - x := continuous_id.sub continuous_const
    exact h2.continuousAt.preimage_mem_nhds (by simpa using hW' x)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover _ hU
  set V0 : Set X := ⋂ x ∈ t, W' x
  have hV0 : V0 ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).2 fun x _ => hW' x
  have key : ∀ y ∈ tsupport g, ∀ u ∈ V0, g (y + u) = g y := fun y hy u hu => by
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hux : u ∈ W' x := Set.mem_iInter₂.1 hu x hx
    have e1 : g (x + ((y - x) + u)) = g x := hW'h x _ hyx _ hux
    have e2 : g (x + ((y - x) + 0)) = g x := hW'h x _ hyx _ (mem_of_mem_nhds (hW' x))
    rw [show x + ((y - x) + u) = y + u by abel] at e1
    rw [show x + ((y - x) + 0) = y by abel] at e2
    rw [e1, e2]
  refine ⟨V0 ∩ Neg.neg ⁻¹' V0, Filter.inter_mem hV0 (neg_mem_nhds_zero X hV0), fun x u hu => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact key x hx u hu.1
  by_cases hxu : x + u ∈ tsupport g
  · have := key (x + u) hxu (-u) hu.2
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem norm_absNorm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  simpa using this

theorem exists_nat_subset_nhds {F : Type} [Field F] [NumberField F] (V : Set (FiniteAdeleRing (𝓞 F) F))
    (hV : V ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ v, ‖Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v z‖ ≤ ‖(m : Fv F v)‖) → z ∈ V := by
  classical
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v => Valued.isOpen_integer _
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : IsOpenEmbedding f := RestrictedProduct.isOpenEmbedding_structureMap hopen
  have hV' : f ⁻¹' V ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := by
    rw [← Filter.mem_map, hf.map_nhds_eq]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at hV'
  obtain ⟨I, hI, t, ht, hsub⟩ := hV'
  have hk : ∀ v, ∃ k : ℕ, ∀ y : v.adicCompletionIntegers F,
      ‖(y : v.adicCompletion F)‖ ≤ ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ k → y ∈ t v := fun v => by
    have h1 := ht v
    rw [nhds_subtype, Filter.mem_comap] at h1
    obtain ⟨s, hs, hss⟩ := h1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_absNorm_lt_one v)
    refine ⟨k, fun y hy => hss (hball ?_)⟩
    rw [Metric.mem_ball, show ((0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) v : v.adicCompletion F) = 0 from rfl,
      dist_zero_right]
    exact lt_of_le_of_lt hy hk
  choose k hk using hk
  refine ⟨∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal ^ k v, Finset.prod_pos fun v _ =>
    pow_pos (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)) _, fun z hz => ?_⟩
  have hint : ∀ v, z v ∈ v.adicCompletionIntegers F := fun v =>
    Valued.toNormedField.norm_le_one_iff.1 ((hz v).trans (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _))
  have hz' : z = f (fun v => ⟨z v, hint v⟩) := by
    ext v; rfl
  rw [hz']
  refine hsub (fun v hv => hk v _ ?_)
  have hvI : v ∈ hI.toFinset := hI.mem_toFinset.2 hv
  refine (hz v).trans ?_
  rw [← Finset.mul_prod_erase _ _ hvI, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _)

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem exists_mulInt_invariant {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F,
      g (x + fun i => (a i).2) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  obtain ⟨V, hV, hinv⟩ := exists_nhds_zero_invariant g hlc hcs
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  obtain ⟨m, hm, hmV⟩ := exists_nat_subset_nhds (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨m, hm, fun a ha x => hinv x _ (hsub fun i _ => ?_)⟩
  exact Set.mem_iInter.1 (hmV _ fun v => ha.2 v i) i

theorem transInv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) → ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a →
      ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x :=
  fun g hg => exists_mulInt_invariant g hg

end GlobalTheory.SBTransl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLevelConductorCompatible
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.PureFix

theorem pureA_fixed : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (m₁ M m₃ : ℕ), 0 < m₁ → 0 < M → 0 < m₃ → (∀ a : κ → AF F, IsMulInt F m₁ a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x) → (∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 → ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1) → (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m₃ : Fv F v)‖) → ψ t = 1) → ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ, ∀ a b : κ → AF F, IsMulInt F (2 * m₁ * M * m₃) a → IsMulInt F (2 * m₁ * M * m₃) b → schr ψ (a, b) (pureA F f g) = pureA F f g := by
  intro F _ _ κ _ ψ g m₁ M m₃ hm₁ hM hm₃ hg hx hψ f a b ha hb
  funext x
  have ha' : IsMulInt F m₁ a := by
    have e : 2 * m₁ * M * m₃ = (2 * M * m₃) * m₁ := by ring
    rw [e] at ha; exact ha.mono
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + a) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i; congr 1; show (x i).1 + (a i).1 = (x i).1; rw [ha.1 i, add_zero]
  have e2 : (fun i => ((x + a) i).2) = (fun i => (x i).2) + fun i => (a i).2 := rfl
  simp only [schr, pureA]
  rw [e1, e2, hg a ha' (fun i => (x i).2)]
  by_cases h0 : g (fun i => (x i).2) = 0
  · simp [h0]
  · have hs : ∀ (c d : κ → AF F), (∀ i, (d i).1 = 0) → (c ⬝ᵥ d).1 = 0 := by
      intro c d hd
      change fstA F (∑ i, c i * d i) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul]; change (c i).1 * (d i).1 = 0; rw [hd i, mul_zero]
    have hnat : ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), ‖(n : Fv F v)‖ ≤ 1 :=
      fun v n => GlobalTheory.SmoothForms.denom_norm_natCast_le_one v n
    rw [hψ _ ?_ ?_, one_mul]
    · change (x ⬝ᵥ b).1 + (⅟2 : AF F).1 * (a ⬝ᵥ b).1 = 0
      rw [hs x b hb.1, hs a b hb.1, mul_zero, add_zero]
    · intro v
      have hb' : ∀ i, ‖evFin F v (b i)‖ ≤ ‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
        intro i; have := hb.2 v i; push_cast at this; simpa [norm_mul, mul_assoc] using this
      have h2 : ‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖ = 1 := by
        rw [← norm_mul, show (2 : Fv F v) = evFin F v (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul,
          invOf_mul_self, map_one, norm_one]
      have ha2 : ∀ i, ‖evFin F v (⅟2 * a i)‖ ≤ 1 := by
        intro i
        have := ha.2 v i
        push_cast at this
        rw [map_mul, norm_mul]
        calc ‖evFin F v (⅟2 : AF F)‖ * ‖evFin F v (a i)‖
            ≤ ‖evFin F v (⅟2 : AF F)‖ * ‖(2 * m₁ * M * m₃ : Fv F v)‖ := by gcongr
          _ = (‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖) * ‖((m₁ * M * m₃ : ℕ) : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 := by rw [h2, one_mul]; exact hnat v _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), dotProduct, dotProduct, Finset.mul_sum, map_sum, map_sum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [map_mul, norm_mul]
        calc ‖evFin F v (x i)‖ * ‖evFin F v (b i)‖
            ≤ ‖evFin F v (x i)‖ * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr; exact hb' i
          _ = ‖(M : Fv F v) * evFin F v (x i)‖ * ‖((2 * m₁ : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * 1 * ‖(m₃ : Fv F v)‖ := by
              gcongr
              · exact hx x h0 i v
              · exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := by ring
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [← mul_assoc, map_mul, norm_mul]
        calc ‖evFin F v (⅟2 * a i)‖ * ‖evFin F v (b i)‖
            ≤ 1 * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr
              · exact ha2 i
              · exact hb' i
          _ = ‖((2 * m₁ * M : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * ‖(m₃ : Fv F v)‖ := by gcongr; exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := one_mul _

end GlobalTheory.PureFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensor
section
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.SBBlocks

theorem isClosed_support_of_isLocallyConstant {Z : Type} [TopologicalSpace Z] {f : Z → ℂ}
    (hf : IsLocallyConstant f) : IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
  rw [this]; exact (hf.isOpen_fiber 0).isClosed_compl

theorem mem_SB_of_support_subset {Z : Type} [TopologicalSpace Z] {f : Z → ℂ} {C : Set Z}
    (hf : IsLocallyConstant f) (hC : IsCompact C) (hs : Function.support f ⊆ C) : f ∈ SB Z :=
  ⟨hf, HasCompactSupport.intro' (hC.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf) hs)
    (isClosed_support_of_isLocallyConstant hf) fun _ hx => Function.notMem_support.1 hx⟩

theorem prod_decomp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X × Y → ℂ)
    (hh : h ∈ SB (X × Y)) :
    ∃ (m : ℕ) (a : Fin m → X → ℂ) (b : Fin m → Y → ℂ), (∀ j, a j ∈ SB X) ∧ (∀ j, b j ∈ SB Y) ∧
      ∀ x y, h (x, y) = ∑ j, a j x * b j y := by
  classical
  obtain ⟨hlc, hcs⟩ := hh
  have hK : IsCompact (tsupport h) := hcs.isCompact
  have hK1 : IsCompact (Prod.fst '' tsupport h) := hK.image continuous_fst
  have hK2 : IsCompact (Prod.snd '' tsupport h) := hK.image continuous_snd
  have hzero : ∀ x y, h (x, y) ≠ 0 → x ∈ Prod.fst '' tsupport h ∧ y ∈ Prod.snd '' tsupport h :=
    fun x y hne => ⟨⟨(x, y), subset_tsupport h hne, rfl⟩, ⟨(x, y), subset_tsupport h hne, rfl⟩⟩
  let s : Y → X → ℂ := fun y x => h (x, y)
  have hs : IsLocallyConstant s := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    have key : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ Prod.fst '' tsupport h, h (x, y) = h (x, y₀) := by
      refine hK1.eventually_forall_of_forall_eventually (P := fun y x => h (x, y) = h (x, y₀)) ?_
      intro x _
      have h1 : IsLocallyConstant (fun z : Y × X => h (z.2, z.1)) := hlc.comp_continuous continuous_swap
      have h2 : IsLocallyConstant (fun z : Y × X => h (z.2, y₀)) :=
        hlc.comp_continuous (continuous_snd.prodMk continuous_const)
      filter_upwards [h1.eventually_eq (y₀, x), h2.eventually_eq (y₀, x)] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    funext x
    by_cases hx : x ∈ Prod.fst '' tsupport h
    · exact hy x hx
    · show h (x, y) = h (x, y₀)
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩),
        image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩)]
  have hsSB : ∀ y, s y ∈ SB X := fun y =>
    mem_SB_of_support_subset (hlc.comp_continuous (continuous_id.prodMk continuous_const)) hK1
      (fun x hx => (hzero x y hx).1)
  have hsne : ∀ y, s y ≠ 0 → y ∈ Prod.snd '' tsupport h := fun y hy => by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hy
    exact (hzero x y hx).2
  obtain ⟨t, ht⟩ := hK2.elim_finite_subcover (fun φ : X → ℂ => s ⁻¹' {φ}) (fun φ => hs.isOpen_fiber φ)
    (fun y _ => Set.mem_iUnion.2 ⟨s y, rfl⟩)
  let t' := t.filter (fun φ => φ ≠ 0 ∧ φ ∈ SB X)
  let bb : (X → ℂ) → Y → ℂ := fun φ y => if s y = φ then 1 else 0
  have hbSB : ∀ φ ∈ t', bb φ ∈ SB Y := by
    intro φ hφ
    have hφ0 : φ ≠ 0 := (Finset.mem_filter.1 hφ).2.1
    refine mem_SB_of_support_subset (hs.comp fun v => if v = φ then (1 : ℂ) else 0) hK2 ?_
    intro y hy
    have : s y = φ := by
      by_contra hne
      exact hy (if_neg hne)
    exact hsne y (this ▸ hφ0)
  have hsum : ∀ x y, h (x, y) = ∑ φ ∈ t', φ x * bb φ y := by
    intro x y
    have e1 : ∑ φ ∈ t', φ x * bb φ y = ∑ φ ∈ t', if s y = φ then φ x else 0 :=
      Finset.sum_congr rfl fun φ _ => by simp only [bb]; split_ifs <;> simp
    rw [e1, Finset.sum_ite_eq]
    split_ifs with hin
    · rfl
    · show s y x = 0
      by_contra hne
      have hy0 : s y ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
      apply hin
      obtain ⟨φ, hφ, hyφ⟩ := Set.mem_iUnion₂.1 (ht (hsne y hy0))
      have : s y = φ := hyφ
      exact Finset.mem_filter.2 ⟨this ▸ hφ, hy0, hsSB y⟩
  refine ⟨t'.card, fun j => (t'.equivFin.symm j : X → ℂ), fun j => bb (t'.equivFin.symm j),
    fun j => (Finset.mem_filter.1 (t'.equivFin.symm j).2).2.2, fun j => hbSB _ (t'.equivFin.symm j).2, ?_⟩
  intro x y
  rw [hsum x y, ← Finset.sum_coe_sort t']
  exact (Equiv.sum_comp t'.equivFin.symm (fun φ : t' => (φ : X → ℂ) x * bb φ y)).symm

theorem sum_prod_blocks {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (g : (κ ⊕ κ' → Af F) → ℂ) (hg : g ∈ SB (κ ⊕ κ' → Af F)) :
    ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧
      (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  let e : (κ ⊕ κ' → Af F) ≃ₜ (κ → Af F) × (κ' → Af F) := Homeomorph.sumArrowHomeomorphProdArrow
  have hh : g ∘ e.symm ∈ SB ((κ → Af F) × (κ' → Af F)) :=
    ⟨hg.1.comp_continuous e.symm.continuous, hg.2.comp_homeomorph e.symm⟩
  obtain ⟨m, a, b, ha, hb, hab⟩ := prod_decomp _ hh
  refine ⟨m, a, b, ha, hb, fun x x' => ?_⟩
  rw [← hab]
  show g _ = g (e.symm (x, x'))
  congr 1

end GlobalTheory.SBBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.SuppDen

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

def denSet (κ : Type) (m : ℕ) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), ‖(m : v.adicCompletion F) * y i v‖ ≤ 1}

theorem natCast_mul_apply (m : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((m : FiniteAdeleRing (𝓞 F) F) * a) v = (m : v.adicCompletion F) * a v := by
  have hm : (m : FiniteAdeleRing (𝓞 F) F) v = (m : v.adicCompletion F) := by
    induction m with
    | zero => rfl
    | succ n ih =>
      rw [Nat.cast_succ, Nat.cast_succ]
      change (n : FiniteAdeleRing (𝓞 F) F) v + 1 = _
      rw [ih]
  simp [hm]

theorem isOpen_denSet (κ : Type) [Finite κ] (m : ℕ) : IsOpen (denSet (F := F) κ m) := by
  have h : denSet (F := F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹'
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, natCast_mul_apply,
      norm_le_one_iff_mem]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))

theorem norm_mul_le_one_of_dvd {v : HeightOneSpectrum (𝓞 F)} {m m' : ℕ} (hd : m ∣ m')
    {z : v.adicCompletion F} (hz : ‖(m : v.adicCompletion F) * z‖ ≤ 1) :
    ‖(m' : v.adicCompletion F) * z‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]
  exact mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) hz

theorem denSet_mono (κ : Type) {m m' : ℕ} (hd : m ∣ m') :
    denSet (F := F) κ m ⊆ denSet κ m' :=
  fun _ hy i v => norm_mul_le_one_of_dvd hd (hy i v)

theorem exists_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ ∀ v : HeightOneSpectrum (𝓞 F), ‖(d : v.adicCompletion F) * a v‖ ≤ 1 := by
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite := by
    apply (Filter.eventually_cofinite.1 a.2).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro hmem
    apply hv
    have : ‖a v‖ ≤ 1 := (norm_le_one_iff_mem v _).2 hmem
    exact max_eq_left (by exact_mod_cast this)
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global (F := F)
    (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf
  exact ⟨d, hd, fun v => h v _ (le_max_right _ _)⟩

theorem exists_mem_denSet (κ : Type) [Fintype κ] (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, 0 < m ∧ y ∈ denSet κ m := by
  classical
  choose d hd h using fun i => exists_denom (y i)
  exact ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v =>
    norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩

theorem support_bounded_denominators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 →
      ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1 := by
  classical
  have hK : IsCompact (tsupport g) := hg.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1))
    (fun n => isOpen_denSet κ _) (fun y _ => by
      obtain ⟨m, hm, hy⟩ := exists_mem_denSet κ y
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
      exact Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩
  have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport _ hx
  obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v

end GlobalTheory.SuppDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
section
noncomputable section

namespace GlobalTheory.ChrWLocal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valuation_eq_one_iff {v : Pl F} (x : Fv F v) :
    valuation (Fv F v) x = 1 ↔ Valued.v x = 1 := by
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isUnram_chrW_iff (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t) := by
  constructor
  · intro h y hy
    obtain ⟨a, ha⟩ := (SplitTie.complMap_bijective t (splitPrime_under t)).2 (y : _)
    have hv : Valued.v a = 1 := by
      rw [← SplitTie.valued_complMap t (splitPrime_under t), ha]; exact hy
    have h0 : a ≠ 0 := by rintro rfl; simp at hv
    have h1 := h (Units.mk0 a h0) ((valuation_eq_one_iff _).2 hv)
    rw [← h1]
    exact congrArg (locChar χ _) (Units.ext ha.symm)
  · intro h x hx
    exact h _ (show Valued.v (complMap (splitPrime_under t) (x : Fv F v)) = 1 by
      rw [SplitTie.valued_complMap t (splitPrime_under t)]; exact (valuation_eq_one_iff _).1 hx)

theorem chrW_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E),
    IsHecke F E χ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  intro F E _ _ _ _ _ χ hχ v t
  have hc := GlobalTheory.ChrWSmooth.continuous_chrW hχ.1 t
  refine ⟨⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ hc, GlobalTheory.ChrWSmooth.isUnitaryChar_chrW χ t⟩, ?_,
    isUnram_chrW_iff χ t⟩
  exact GlobalTheory.GaussNonvanish.exists_condLE (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec _
    (Units.continuous_val.comp hc)

end GlobalTheory.ChrWLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMemberStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  first | exact @GlobalTheory.HoweD.stab_comap_of_thetaSubInf | exact GlobalTheory.HoweD.stab_comap_of_thetaSubInf | (intros; apply GlobalTheory.HoweD.stab_comap_of_thetaSubInf <;> assumption)
end

