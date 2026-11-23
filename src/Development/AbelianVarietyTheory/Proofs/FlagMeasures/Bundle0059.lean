module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContentThickenedTupleOrbitNormalSubgroup
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ThickSplit

theorem cont_iUnion_cosets {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {Γ : Type} [Group Γ]
    (N H : Subgroup Γ) [N.Normal] (hN : N.index ≠ 0) (S : Γ → Set W) (c : ℝ)
    (hco : ∀ a, IsCO W0 (S a)) (hc : ∀ a, cont W0 (S a) = c)
    (heq : ∀ a b, a⁻¹ * b ∈ N ⊔ H → S a = S b)
    (hdis : ∀ a b, ¬ Disjoint (S a) (S b) → a⁻¹ * b ∈ N ⊔ H) :
    cont W0 (⋃ a, S a) * (N.relIndex H : ℝ) = (N.index : ℝ) * c := by
  have hidx : N.relIndex H * (N ⊔ H).index = N.index := by
    rw [← Subgroup.relIndex_sup_left H N]
    exact Subgroup.relIndex_mul_index le_sup_left
  have hJ : (N ⊔ H).index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hidx
    exact hN hidx.symm
  haveI : (N ⊔ H).FiniteIndex := ⟨hJ⟩
  haveI : Fintype (Γ ⧸ (N ⊔ H)) := Fintype.ofFinite _
  have hU : (⋃ a, S a) = ⋃ q ∈ (Finset.univ : Finset (Γ ⧸ (N ⊔ H))), S q.out := by
    ext w
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(a : Γ ⧸ (N ⊔ H)), ?_⟩
      rw [heq _ a (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))]
      exact ha
    · rintro ⟨q, hq⟩
      exact ⟨_, hq⟩
  rw [hU, (_root_.GlobalTheory.HL.cont_biUnion W0 Finset.univ (fun q : Γ ⧸ (N ⊔ H) => S q.out) (fun q _ => hco _)).2]
  · simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hidx, Subgroup.index, Nat.card_eq_fintype_card]
    push_cast
    ring
  · intro q _ r _ hqr
    by_contra h
    apply hqr
    have := QuotientGroup.eq.2 (hdis _ _ h)
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem rmul_one {n m : ℕ} (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply]

theorem map_rmul {n m : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) : (fun a => g (rmul x A a)) = rmul (fun a => g (x a)) A := by
  funext j
  simp [rmul]

theorem hf_sum_sum (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (u v : Fin m → E) :
    hf L Hm (∑ i, u i • x i) (∑ j, v j • x j) = ∑ i, ∑ j, u i * L.cj (v j) * hf L Hm (x i) (x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc _ = ∑ p : Fin n × Fin n, ∑ q : Fin m × Fin m,
        u q.1 * L.cj (v q.2) * (x q.1 p.1 * Hm p.1 p.2 * L.cj (x q.2 p.2)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_comm, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type]

theorem gramT_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_sum, Matrix.mul_apply, cT, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mem_fixG (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ fixG L Hm (Submodule.span E (Set.range x)) ↔ g ∈ isomG L Hm ∧ ∀ a, g (x a) = x a := by
  constructor
  · rintro ⟨h1, _, h3⟩
    refine ⟨h1, fun a => ?_⟩
    have := h3 (x a) (Submodule.subset_span ⟨a, rfl⟩)
    exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
  · rintro ⟨h1, h2⟩
    have key : ∀ v ∈ Submodule.span E (Set.range x), g v = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨a, rfl⟩ := hv; exact h2 a
      | zero => simp
      | add u v _ _ hu hv => rw [map_add (f := _), hu, hv]
      | smul c v _ hv => rw [map_smul, hv]
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rw [key v hv]; exact hv⟩, fun v hv => ?_⟩
    · have := g.injective (key _ hv)
      rwa [this] at hv
    · rw [key v hv, sub_self]
      exact Submodule.zero_mem _
end

end GlobalTheory.HL.ThickSplit


open GlobalTheory.HL.ThickSplit in
theorem GlobalTheory.HL.cont_thick_torb_normal : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x _ K K' hK hK' hnorm hidx i hi hstab hco
  obtain ⟨-, hgrp, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  have hjac := (_root_.GlobalTheory.HL.TupleJac.tuple_jacobian L ϖ hϖ Hm hH Λs hΛ m).2
  have hconj : ∀ a ∈ K, ∀ k ∈ K', a * k * a⁻¹ ∈ K' := by
    intro a ha k hk
    rw [← hnorm a ha]
    exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj a) K' hk
  haveI : (K'.subgroupOf K).Normal :=
    ⟨fun k hk a => hconj a a.2 k hk⟩
  set Fx := fixG L Hm (Submodule.span E (Set.range x)) with hFx
  have hsub : ∀ a b : K, a⁻¹ * b ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K →
      (fun x c => (b : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i ⊆
      (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i := by
    intro a b hab
    obtain ⟨k, hk, h, hh, hkh⟩ := Subgroup.mem_sup_of_normal_left.1 hab
    have hb : b = a * (k * h) := by rw [hkh]; group
    have hhx := ((mem_fixG L Hm x h).1 hh).2
    rintro _ ⟨_, ⟨_, ⟨k1, hk1, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨k * (h * k1 * (h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹),
      K'.mul_mem hk (hconj h h.2 k1 hk1), rfl⟩, A, hA, rfl⟩, ?_⟩
    simp only [map_rmul]
    congr 1
    funext c
    have : ((h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹) (x c) = x c := by
      conv_lhs => rw [← hhx c]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hb]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, this]
  have main := cont_iUnion_cosets (tupLat L Λs m) (K'.subgroupOf K) (Fx.subgroupOf K) hidx
    (fun a : K => (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i)
    (cont (tupLat L Λs m) (thick L ϖ (torb K' x) i))
    (fun a => (hjac a (hK a.2) _ hco).1) (fun a => (hjac a (hK a.2) _ hco).2)
    (fun a b hab => Set.Subset.antisymm
      (hsub b a (by simpa using Subgroup.inv_mem _ hab)) (hsub a b hab)) ?_
  · have hU : thick L ϖ (torb K x) i = ⋃ a : K, (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) ''
        thick L ϖ (torb K' x) i := by
      ext w
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, A, hA, rfl⟩
        exact ⟨⟨a, ha⟩, _, ⟨x, ⟨1, K'.one_mem, rfl⟩, A, hA, rfl⟩, map_rmul a x A⟩
      · rintro ⟨a, _, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
        exact ⟨_, ⟨a * k, K.mul_mem a.2 (hK' hk), rfl⟩, A, hA, map_rmul _ _ A⟩
    have hI : (K'.subgroupOf K).relIndex (Fx.subgroupOf K) = (Fx ⊓ K').relIndex (Fx ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_right Fx K, Subgroup.relIndex_subgroupOf inf_le_right,
        ← Subgroup.inf_relIndex_right K' (Fx ⊓ K)]
      congr 1
      rw [inf_comm, inf_assoc, inf_eq_right.2 hK']
    rw [hU, ← hI]
    exact main
  · intro a b hab
    obtain ⟨w, ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨k', hk', rfl⟩, A', hA', rfl⟩, hw⟩⟩ :=
      Set.not_disjoint_iff.1 hab
    obtain ⟨-, hdet, -, hinv, -, -⟩ := hgrp A' hA'
    have hB : A * A'⁻¹ ∈ congK L ϖ m i := (hgrp A hA).2.2.2.2.1 _ hinv
    set g : (Fin n → E) ≃ₗ[E] (Fin n → E) := k⁻¹ * (a : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹ * b * k' with hg
    have hgK : g ∈ K := K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hK' hk)) (K.inv_mem a.2)) b.2) (hK' hk')
    have h1 : rmul (fun c => g (x c)) A' = rmul x A := by
      rw [← map_rmul]
      funext c
      have h2 := congrFun hw c
      have h3 := congrFun (map_rmul k' x A') c
      have h4 := congrFun (map_rmul k x A) c
      simp only at h2 h3 h4
      rw [← h3, ← h4] at h2
      rw [hg]
      simp only [LinearEquiv.mul_apply]
      rw [h2]
      simp [LinearEquiv.coe_inv]
    have h2 : (fun c => g (x c)) = rmul x (A * A'⁻¹) := by
      rw [← rmul_rmul, ← h1, rmul_rmul, Matrix.mul_nonsing_inv _ hdet, rmul_one]
    have h3 : cT L (A * A'⁻¹) * gramT L Hm x * (A * A'⁻¹) = gramT L Hm x := by
      rw [← gramT_rmul, ← h2]
      ext c d
      exact hK hgK _ _
    obtain ⟨k'', hk'', h4⟩ := hstab x ⟨1, K'.one_mem, rfl⟩ _ hB h3
    rw [← h2] at h4
    have hfix : k''⁻¹ * g ∈ Fx := by
      refine (mem_fixG L Hm x _).2 ⟨hK (K.mul_mem (K.inv_mem (hK' hk'')) hgK), fun c => ?_⟩
      rw [LinearEquiv.mul_apply, congrFun h4 c]
      exact LinearEquiv.symm_apply_apply _ _
    have hmem : ∀ u (hu : u ∈ K'), (⟨u, hK' hu⟩ : K) ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K :=
      fun u hu => Subgroup.mem_sup_left hu
    have hmem' : (⟨k''⁻¹ * g, K.mul_mem (K.inv_mem (hK' hk'')) hgK⟩ : K) ∈
        K'.subgroupOf K ⊔ Fx.subgroupOf K := Subgroup.mem_sup_right hfix
    have hfin := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem k hk) (hmem k'' hk''))
      hmem') (Subgroup.inv_mem _ (hmem k' hk'))
    convert hfin using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed
section
open Formalism.REAL
open scoped ContDiff Manifold Topology

namespace GlobalTheory


open scoped ContDiff Manifold Topology in
theorem _root_.GlobalTheory.exists_contDiff_extension_of_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsClosed S) (f : E → ℂ)
    (hf : ∀ x ∈ S, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ y ∈ U, y ∈ S → f y = F y) :
    ∃ F : E → ℂ, ContDiff ℝ ∞ F ∧ ∀ y ∈ S, F y = f y := by
  classical
  let t : E → Set ℂ := fun y => if y ∈ S then {f y} else Set.univ
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [t, if_pos hy]; exact convex_singleton _
    · simp only [t, if_neg hy]; exact convex_univ
  have hloc : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ g : E → ℂ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hf x hx
      refine ⟨U, hU.mem_nhds hxU, F, hF.contMDiffOn, fun y hy => ?_⟩
      by_cases hyS : y ∈ S
      · simp only [t, if_pos hyS, Set.mem_singleton_iff]; exact (hfF y hy hyS).symm
      · simp only [t, if_neg hyS, Set.mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, fun y hy => ?_⟩
      simp only [t, if_neg (show y ∉ S from hy), Set.mem_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, E) (n := ⊤) ht hloc
  refine ⟨g, g.contMDiff.contDiff, fun y hy => ?_⟩
  have hgy := hg y
  simpa only [t, if_pos hy, Set.mem_singleton_iff] using hgy


open scoped ContDiff Manifold Topology in
theorem _root_.GlobalTheory.smoothOnG_exists_contDiff_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), _root_.Formalism.REAL.SmoothOnG ε f →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
        ∀ g : Matrix (Fin n) (Fin n) ℂ, _root_.Formalism.REAL.inUJ ε g → F (fun i j => g i j) = f g := by
  intro n ε f hf
  let S : Set (Fin n → Fin n → ℂ) := {x | _root_.Formalism.REAL.inUJ ε (Matrix.of x)}
  have hS : IsClosed S := by
    have h0 : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
    have hc : Continuous
        (fun x : Fin n → Fin n → ℂ => Matrix.conjTranspose (Matrix.of x) * _root_.Formalism.REAL.Jm ε * Matrix.of x) :=
      (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  obtain ⟨F, hF, hFS⟩ := _root_.GlobalTheory.exists_contDiff_extension_of_isClosed hS
    (fun x => f (Matrix.of x)) (by
      intro x hx
      unfold _root_.Formalism.REAL.SmoothOnG at hf
      obtain ⟨U, G, hU, hxU, hG, hfG⟩ := hf (Matrix.of x) hx
      let U' : Set (Fin n → Fin n → ℂ) := U
      let G' : (Fin n → Fin n → ℂ) → ℂ := G
      have hU' : IsOpen U' := hU
      have hG' : ContDiffOn ℝ ∞ G' U' := hG
      exact ⟨U', G', hU', hxU, hG', fun y hy hyS => hfG (Matrix.of y) hy hyS⟩)
  exact ⟨F, hF, fun g hg => hFS (fun i j => g i j) hg⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDenominatorOfFg
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem exists_denominator_of_fg {V : Type} [AddCommGroup V] (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ)
    (M : Submodule ℤ V) (hM : M.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, (d : ℚ) * B x y = n := by
  obtain ⟨s, hs⟩ := Submodule.FG.map₂ B hM hM
  refine ⟨∏ a ∈ s, a.den, Finset.prod_pos fun a _ => a.den_pos, ?_⟩
  have key : ∀ r ∈ Submodule.span ℤ (s : Set ℚ), ∃ n : ℤ, ((∏ a ∈ s, a.den : ℕ) : ℚ) * r = n := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a : ℚ => a.den) (Finset.mem_coe.mp ha)
      refine ⟨c * a.num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.den_mul_eq_num]; ring
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [mul_add, hm, hn]; push_cast; ring⟩
    | smul c a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨c * m, by rw [zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring⟩
  intro x hx y hy
  exact key _ (hs ▸ Submodule.apply_mem_map₂ B hx hy)

theorem isom_sub_mem_of_congr : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U X : Submodule K V) (M : Submodule (𝓞 K) V) (γ : V ≃ₗ[K] V) (g : ℕ), h.IsSymm → X ≤ U → (∀ x ∈ X, ∀ y ∈ U, h x y = 0) → (∀ x ∈ U, x ∉ X → 0 < Algebra.trace ℚ K (h x x)) → M.FG → (∀ x ∈ M, x ∈ U) → γ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ x ∈ X, γ x ∈ X) → 3 ≤ g → (∀ x ∈ M, ∃ y ∈ M, γ x - x - (g : K) • y ∈ X) → ∀ x ∈ M, γ x - x ∈ X := by
  intro K V _ _ _ _ _ _ _ _ h U X M γ g hs hXU hrad hpos hM hMU hγ hγX hg hcong
  have hiso : ∀ x y, h (γ x) (γ y) = h x y := hγ
  have hrad' : ∀ y ∈ U, ∀ x ∈ X, h y x = 0 := fun y hy x hx => by
    rw [← hs.eq x y, hrad x hx y hy, map_zero]
  let B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ := LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ K (h x y))
    (fun a b c => by simp) (fun c a b => by rw [map_zsmul h, LinearMap.smul_apply, map_zsmul])
    (fun a b c => by simp)
    (fun c a b => by rw [map_zsmul (h a), map_zsmul])
  have hB : ∀ x y, B x y = Algebra.trace ℚ K (h x y) := fun _ _ => rfl
  obtain ⟨d, hd, hden⟩ := exists_denominator_of_fg B (M.restrictScalars ℤ) (hM.restrictScalars)
  have hnn : ∀ x ∈ U, 0 ≤ B x x := fun x hx => by
    by_cases hxX : x ∈ X
    · rw [hB, hrad x hxX x hx, map_zero]
    · exact (hpos x hx hxX).le
  have main : ∀ n : ℕ, ∀ x ∈ M, (d : ℚ) * B x x < n → γ x - x ∈ X := by
    intro n
    induction n with
    | zero =>
      intro x hx hlt
      have := hnn x (hMU x hx)
      have : (0 : ℚ) ≤ d * B x x := by positivity
      simp at hlt
      linarith
    | succ n ih =>
      intro x hx hlt
      by_cases hxX : x ∈ X
      · exact X.sub_mem (hγX x hxX) hxX
      obtain ⟨y, hy, hu⟩ := hcong x hx
      set u := γ x - x - (g : K) • y with hu_def
      set z := γ x - x with hz_def
      have hz : z = (g : K) • y + u := by rw [hu_def]; abel
      have hxU := hMU x hx
      have hyU := hMU y hy
      have hzU : z ∈ U := hz ▸ U.add_mem (U.smul_mem _ hyU) (hXU hu)
      have hγx : γ x = x + z := by rw [hz_def]; abel
      have hγxU : γ x ∈ U := hγx ▸ U.add_mem hxU hzU
      have h1 : B z z = (g : ℚ) ^ 2 * B y y := by
        have e1 : B u z = 0 := by rw [hB, hrad u hu z hzU, map_zero]
        have e2 : B y u = 0 := by rw [hB, hrad' y hyU u hu, map_zero]
        have hz' : z = (g : ℤ) • y + u := by rw [hz, natCast_zsmul, Nat.cast_smul_eq_nsmul]
        calc B z z = B ((g : ℤ) • y + u) z := by rw [← hz']
          _ = (g : ℤ) • B y z := by rw [map_add (f := _), LinearMap.add_apply, e1, map_smul]; simp
          _ = (g : ℤ) • B y ((g : ℤ) • y + u) := by rw [← hz']
          _ = _ := by rw [map_add (f := _), e2, map_smul]; simp; ring
      have h2 : B z z + B (γ x + x) (γ x + x) = 4 * B x x := by
        have e : B (γ x) (γ x) = B x x := by rw [hB, hB, hiso]
        rw [hz_def]
        simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, e]
        ring
      have h3 := hnn _ (U.add_mem hγxU hxU)
      have hxp : 0 < B x x := hpos x hxU hxX
      have hyn := hnn y hyU
      have hg' : (9 : ℚ) ≤ (g : ℚ) ^ 2 := by
        have : (3 : ℚ) ≤ g := by exact_mod_cast hg
        nlinarith
      have hlt' : B y y < B x x := by nlinarith
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      obtain ⟨a, ha⟩ := hden x hx x hx
      obtain ⟨b, hb⟩ := hden y hy y hy
      have hab : b < a := by
        have : (b : ℚ) < a := by rw [← ha, ← hb]; exact mul_lt_mul_of_pos_left hlt' hd'
        exact_mod_cast this
      have han : a < n + 1 := by
        rw [ha] at hlt
        exact_mod_cast hlt
      have hyX : γ y - y ∈ X := ih y hy (by
        rw [hb]
        have : b < n := by omega
        exact_mod_cast this)
      have hw : γ z - z ∈ X := by
        have : γ z - z = (g : K) • (γ y - y) + (γ u - u) := by
          rw [hz, map_add (f := _), map_smul, smul_sub]; abel
        rw [this]
        exact X.add_mem (X.smul_mem _ hyX) (X.sub_mem (hγX u hu) hu)
      have hzz : h z z = 0 := by
        have e := hiso x z
        have e2 : h (γ x) (γ z - z) = 0 := hrad' _ hγxU _ hw
        rw [map_sub, e, hγx, map_add (f := _), LinearMap.add_apply] at e2
        linear_combination -e2
      by_contra hzX
      have := hpos z hzU hzX
      rw [hzz, map_zero] at this
      exact lt_irrefl _ this
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℚ) * B x x)
  exact main n x hx hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

open NumberField Module Matrix in
open scoped ENNReal in
private lemma exists_integer_eq_star {K : Type} [Field K] [NumberField K] [StarRing K]
    (a : 𝓞 K) : ∃ b : 𝓞 K, (b : K) = star (a : K) := by
  have hint : IsIntegral ℤ (starRingEnd K (a : K)) :=
    map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)
  rw [starRingEnd_apply] at hint
  exact ⟨⟨star (a : K), (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩


open NumberField Module Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  intro K _ _ _ h
  unfold _root_.Formalism.HermitianLatticesTheory.IsCMUnram at h
  obtain ⟨-, -, hP⟩ := h
  let S : Set (𝓞 K) := {x | ∃ θ τ : 𝓞 K,
    algebraMap (𝓞 K) K τ = star (algebraMap (𝓞 K) K θ) ∧ x = θ - τ}
  let I : Ideal (𝓞 K) := Ideal.span S
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨θ, τ, hτ, hnot⟩ := hP P hPm
    exact hnot (hle (Ideal.subset_span ⟨θ, τ, hτ, rfl⟩))
  have key : ∀ x ∈ I, ∃ t : 𝓞 K, (x : K) * star (x : K) = (t : K) + star (t : K) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨θ, τ, hτ, rfl⟩ := hx
      change (τ : K) = star (θ : K) at hτ
      have h2 : star (τ : K) = θ := by rw [hτ, star_star]
      refine ⟨θ * (τ - θ), ?_⟩
      push_cast
      rw [star_sub, star_mul', star_sub, h2, ← hτ]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      obtain ⟨y', hy'⟩ := exists_integer_eq_star y
      refine ⟨s + u + x * y', ?_⟩
      push_cast
      simp only [star_add, star_mul', hy', star_star]
      linear_combination hs + hu
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨c', hc'⟩ := exists_integer_eq_star c
      refine ⟨c * c' * s, ?_⟩
      rw [smul_eq_mul]
      push_cast
      simp only [star_mul', hc', star_star]
      linear_combination ((c : K) * star (c : K)) * hs
  obtain ⟨t, ht⟩ := key 1 (hI ▸ Submodule.mem_top)
  exact ⟨t, by simpa using ht.symm⟩

end GlobalTheory
end

