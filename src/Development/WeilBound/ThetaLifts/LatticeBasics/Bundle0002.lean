module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExistsPowIdem

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistA
section
open MeasureTheory Filter Topology GlobalTheory.WeilM

namespace GlobalTheory.ThK.Dbl.LD

theorem sb_chart {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {U : Set X} {T : Set Y} (hU : IsOpen U)
    {e : X → Y} {r : Y → X} (ce : ContinuousOn e U) (cr : ContinuousOn r T) (hre : ∀ x ∈ U, r (e x) = x)
    (hr : ∀ y ∈ T, r y ∈ U) {F : Y → ℂ} (hF : F ∈ SB Y) (hT : ∀ y ∉ T, F y = 0) {G : X → ℂ}
    (h1 : ∀ x ∈ U, G x = F (e x)) (h0 : ∀ x ∉ U, G x = 0) : G ∈ SB X := by
  have hcl : IsClosed (Function.support F) := (hF.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support F) := hF.2.of_isClosed_subset hcl subset_closure
  have hsub : Function.support F ⊆ T := fun y hy => by_contra fun h => hy (hT y h)
  have hC : IsCompact (r '' Function.support F) := hc.image_of_continuousOn (cr.mono hsub)
  have hz : ∀ x ∉ r '' Function.support F, G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [h1 x hxU]; exact by_contra fun h => hx ⟨e x, h, hre x hxU⟩
    · exact h0 x hxU
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro hC hz⟩
  by_cases hxU : x ∈ U
  · filter_upwards [(ce.continuousAt (hU.mem_nhds hxU)).eventually (hF.1.eventually_eq (e x)), hU.mem_nhds hxU] with y a b
    rw [h1 y b, h1 x hxU, a]
  · have : x ∉ r '' Function.support F := by rintro ⟨y, hy, rfl⟩; exact hxU (hr y (hsub hy))
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds this] with y hy
    rw [hz y hy, h0 x hxU]

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] (e : X → Y) (r : Y → X)
    (ce : Continuous e) (cr : Continuous r) (hre : ∀ x, r (e x) = x) {F : Y → ℂ} (hF : F ∈ SB Y) :
    (fun x => F (e x)) ∈ SB X :=
  sb_chart (U := Set.univ) (T := Set.univ) isOpen_univ ce.continuousOn cr.continuousOn (fun x _ => hre x)
    (fun _ _ => trivial) hF (fun _ h => absurd trivial h) (fun _ _ => rfl) (fun _ h => absurd trivial h)

theorem sb_tens {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : (fun z : X × Y => f z.1 * g z.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (IsCompact.prod hf.2 hg.2) fun z hz => ?_⟩
  rcases not_and_or.1 hz with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem sb_cut {X : Type} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClopen A) {f : X → ℂ} (hf : f ∈ SB X) :
    A.indicator f ∈ SB X := by
  have : A.indicator f = fun x => A.indicator (fun _ => (1 : ℂ)) x * f x := by
    ext x; by_cases h : x ∈ A <;> simp [h]
  rw [this]
  exact ⟨(LocallyConstant.charFn ℂ hA).isLocallyConstant.mul hf.1, HasCompactSupport.mul_left hf.2⟩

theorem sb_unif {X P : Type} [TopologicalSpace X] [TopologicalSpace P] {φ : X → ℂ} (hφ : φ ∈ SB X) (a : P → X → X) (p : P)
    (ha : Continuous fun z : P × X => a z.1 z.2) (h0 : ∀ x, a p x = x) :
    ∀ᶠ k in 𝓝 p, ∀ x ∈ tsupport φ, φ (a k x) = φ x := by
  apply IsCompact.eventually_forall_of_forall_eventually hφ.2
  intro y _
  have e := hφ.1.eventually_eq y
  have t1 : Tendsto (fun z : P × X => a z.1 z.2) (𝓝 (p, y)) (𝓝 y) := by simpa [h0] using ha.tendsto (p, y)
  filter_upwards [t1.eventually e, (continuous_snd.tendsto (p, y)).eventually e] with z h1 h2
  rw [h1, h2]

theorem kill_tens {X V : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup V] [TopologicalSpace V]
    [NonarchimedeanAddGroup V] [LocallyCompactSpace V] [T2Space V] (S : Set X) (l : (X × V → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ f ∈ SB X, (∀ x ∉ S, f x = 0) → ∀ g ∈ SB V, l (fun z => f z.1 * g z.2) = 0)
    {F : X × V → ℂ} (hF : F ∈ SB (X × V)) (hS : ∀ z : X × V, z.1 ∉ S → F z = 0) : l F = 0 := by
  classical
  obtain ⟨K₁, hK₁⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (sb_unif hF (fun (k : V) z => (z.1, z.2 + k)) 0 (by fun_prop) (by simp))
  obtain ⟨K₀, hK₀⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  set K := K₀ ⊓ K₁
  have hK : IsCompact (K : Set V) := hK₀.of_isClosed_subset K.isClosed (fun x hx => hx.1)
  have hinv : ∀ k ∈ K, ∀ x v, F (x, v + k) = F (x, v) := fun k hk x v => by
    by_cases hx : (x, v) ∈ tsupport F
    · exact hK₁ hk.2 _ hx
    · by_cases hx' : (x, v + k) ∈ tsupport F
      · simpa using (hK₁ (neg_mem hk.2 : -k ∈ K₁) _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  haveI : DiscreteTopology (V ⧸ K.toAddSubgroup) := QuotientAddGroup.discreteTopology K.isOpen
  have hfin : ((fun z : X × V => (z.2 : V ⧸ K.toAddSubgroup)) '' tsupport F).Finite :=
    (IsCompact.image hF.2 (QuotientAddGroup.continuous_mk.comp continuous_snd)).finite_of_discrete
  have hmem : ∀ (x : V) (q : V ⧸ K.toAddSubgroup), x + -q.out ∈ (K : Set V) ↔ q = (x : V ⧸ K.toAddSubgroup) := by
    intro x q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq]
    rw [add_comm]; rfl
  have : F = ∑ q ∈ hfin.toFinset, fun z : X × V =>
      F (z.1, q.out) * Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (z.2 + -q.out) := by
    ext ⟨x, v⟩
    have hx : F (x, (v : V ⧸ K.toAddSubgroup).out) = F (x, v) := by
      rw [← hinv _ ((hmem v _).2 rfl) x]; congr 2; abel
    rw [Finset.sum_apply, Finset.sum_eq_single (v : V ⧸ K.toAddSubgroup)]
    · rw [Set.indicator_of_mem ((hmem v _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [Set.indicator_of_notMem (fun h => hq ((hmem v q).1 h)), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := F) (x := (x, v)), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  exact h (fun x => F (x, q.out)) (sb_comp (fun x => (x, q.out)) Prod.fst (by fun_prop) (by fun_prop) (fun _ => rfl) hF)
    (fun x hx => hS _ hx) (fun v => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (v + -q.out))
    (sb_comp (fun v => v + -q.out) (fun v => v + q.out) (by fun_prop) (by fun_prop) (by simp) (HaarUniq.indicator_mem K hK))

theorem kill_loc {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [T2Space V]
    (l : (V → ℂ) →ₗ[ℂ] ℂ) {φ : V → ℂ} (hφ : φ ∈ SB V)
    (h : ∀ x, φ x ≠ 0 → ∃ U ∈ 𝓝 x, ∀ ψ ∈ SB V, (∀ y ∉ U, ψ y = 0) → l ψ = 0) : l φ = 0 := by
  have hcl : IsClosed (Function.support φ) := (hφ.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support φ) := hφ.2.of_isClosed_subset hcl subset_closure
  have : ∃ A, IsClopen A ∧ Function.support φ ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0 := by
    refine hc.induction_on (p := fun s => ∃ A, IsClopen A ∧ s ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0)
      ⟨∅, isClopen_empty, subset_rfl, fun ψ _ h => ?_⟩ ?_ ?_ ?_
    · rw [show ψ = 0 from funext fun y => h y (by simp), map_zero]
    · rintro s t hst ⟨A, h1, h2, h3⟩; exact ⟨A, h1, hst.trans h2, h3⟩
    · rintro s t ⟨A, h1, h2, h3⟩ ⟨B, k1, k2, k3⟩
      refine ⟨A ∪ B, h1.union k1, Set.union_subset_union h2 k2, fun ψ hψ h => ?_⟩
      rw [← Set.indicator_self_add_compl A ψ, map_add (f := _), h3 _ (sb_cut h1 hψ) (fun y hy => Set.indicator_of_notMem hy _),
        k3 _ (sb_cut h1.compl hψ), add_zero]
      intro y hy
      by_cases hA : y ∈ A
      · exact Set.indicator_of_notMem (not_not.2 hA) _
      · rw [Set.indicator_of_mem hA]; exact h y (not_or.2 ⟨hA, hy⟩)
    · intro x hx
      obtain ⟨U, hU, hl⟩ := h x hx
      have : (fun k => k + x) ⁻¹' U ∈ 𝓝 (0 : V) := (continuous_add_const x).continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ this
      have hA : IsClopen ((fun y => y - x) ⁻¹' (K : Set V)) := K.isClopen.preimage (by fun_prop)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hA.isOpen.mem_nhds (by simp)), _, hA, subset_rfl,
        fun ψ hψ h0 => hl ψ hψ fun y hy => h0 y fun hy' => hy ?_⟩
      simpa using hK hy'
  obtain ⟨A, -, h2, h3⟩ := this
  exact h3 φ hφ fun y hy => by_contra fun h => hy (h2 h)

def Bump {V : Type} [Zero V] [TopologicalSpace V] (g : V → ℂ) : Prop := g ∈ SB V ∧ (∀ x, g x = 0 ∨ g x = 1) ∧ g 0 = 1

theorem exists_bump (V : Type) [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] : ∃ g : V → ℂ, Bump g := by
  obtain ⟨K, hK⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  refine ⟨_, HaarUniq.indicator_mem K hK, fun x => ?_, Set.indicator_of_mem K.zero_mem _⟩
  by_cases h : x ∈ (K : Set V) <;> simp [h]

theorem bump_ratio {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] {g₀ g₁ : V → ℂ} (h₀ : Bump g₀) (h₁ : Bump g₁) : ∃ s : ℝ, 0 < s ∧ ∀ m : (V → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ ∈ SB V, ∀ a : V, m (fun x => φ (x + a)) = m φ) → m g₀ = s * m g₁ ∧ (m g₀ = 0 → ∀ g ∈ SB V, m g = 0) := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have pos : ∀ g : V → ℂ, Bump g → ∃ s : ℝ, 0 < s ∧ ∫ x, g x ∂μ = s := fun g hg => by
    refine ⟨∫ x, (g x).re ∂μ, ?_, ?_⟩
    · refine (Complex.continuous_re.comp hg.1.1.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (hg.1.2.comp_left (g := Complex.re) rfl) (fun x => ?_) (x := 0) (by simp [hg.2.2])
      rcases hg.2.1 x with h | h <;> simp [h]
    · rw [← integral_complex_ofReal]
      congr 1; ext x; rcases hg.2.1 x with h | h <;> simp [h]
  obtain ⟨a, ha, ea⟩ := pos _ h₀
  obtain ⟨b, hb, eb⟩ := pos _ h₁
  refine ⟨a / b, div_pos ha hb, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := HaarUniq.exists_eq_mul_integral V μ m hm
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hc _ h₀.1, hc _ h₁.1, ea, eb]
  refine ⟨by push_cast; field_simp, fun h g hg => ?_⟩
  rw [hc g hg, (mul_eq_zero.1 h).resolve_right ha', zero_mul]

theorem nonarch_pi (ι V : Type) [Finite ι] [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] :
    NonarchimedeanAddGroup (ι → V) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hU⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i).toAddSubgroup, isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩,
      fun x hx => hU fun i _ => hK i (hx i trivial)⟩

end GlobalTheory.ThK.Dbl.LD
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Vf2

open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf

section Skew

variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem rank_lt {M : Matrix β β K} {y w φ : β → K} (hy : M *ᵥ y = 0) (hw : w ∉ LinearMap.range M.mulVecLin) (hφ : φ ⬝ᵥ y ≠ 0) :
    M.rank < (M + vecMulVec w φ).rank := by
  have e : ∀ x, (M + vecMulVec w φ) *ᵥ x = M *ᵥ x + (φ ⬝ᵥ x) • w := fun x => by
    rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  have h1 : w ∈ LinearMap.range (M + vecMulVec w φ).mulVecLin := ⟨(φ ⬝ᵥ y)⁻¹ • y, by
    rw [mulVecLin_apply, mulVec_smul, e, hy, zero_add, smul_smul, inv_mul_cancel₀ hφ, one_smul]⟩
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ fun h => hw (h ▸ h1))
  rintro _ ⟨x, rfl⟩
  rw [mulVecLin_apply, eq_sub_of_add_eq (e x).symm]
  exact sub_mem ⟨x, rfl⟩ (Submodule.smul_mem _ _ h1)

variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}

omit [DecidableEq β] in
theorem skew_two (hc : ∀ z, c (c z) = z) (hG : ∀ i j, c (G j i) = G i j) (u w : β → A) :
    (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u))ᵀ * G +
      G * (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u)).map c = 0 := by
  have k : ∀ u w : β → A, (vecMulVec u (G *ᵥ c ∘ w))ᵀ * G = G * (vecMulVec w (G *ᵥ c ∘ u)).map c := fun u w => by
    ext i j
    change (∑ k : β, (u k * (G *ᵥ c ∘ w) i) * G k j) =
      ∑ k : β, G i k * c (w k * (G *ᵥ c ∘ u) j)
    simp only [mulVec, dotProduct, Function.comp_apply, Finset.mul_sum, Finset.sum_mul,
      map_sum, map_mul, hc, hG]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [transpose_sub, Matrix.sub_mul, Matrix.map_sub _ (map_sub c), Matrix.mul_sub, k, k]
  abel

theorem step (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) (h0 : (M.map r).det = 0) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := by
  have mv : ∀ (N : Matrix β β A) x, N.map r *ᵥ r ∘ x = r ∘ (N *ᵥ x) := fun N x => funext fun i => (r.map_mulVec N x i).symm
  have mc : ∀ (N : Matrix β β A) x, N.map c *ᵥ c ∘ x = c ∘ (N *ᵥ x) := fun N x => funext fun i => (c.map_mulVec N x i).symm
  obtain ⟨y₀, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨y, rfl⟩ := hr.comp_left y₀
  obtain ⟨i, hi⟩ : ∃ i, r ((m *ᵥ y) i) ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun N : Matrix β β A => N.map r *ᵥ r ∘ y) inj
    simp only [Matrix.map_add _ (map_add r), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero,
      Matrix.map_one _ (map_zero r) (map_one r), one_mulVec] at this
    rw [mv m, show r ∘ (m *ᵥ y) = 0 from funext h, mulVec_zero, add_zero] at this
    exact hy0 this.symm
  let w : β → A := c ∘ (G' *ᵥ Pi.single i 1)
  have hw : G *ᵥ c ∘ w = Pi.single i 1 := by
    rw [show c ∘ w = G' *ᵥ Pi.single i 1 from funext fun _ => hc _, mulVec_mulVec, hG', one_mulVec]
  have fin : ∀ (u : β → A) (z : β → K), (∀ a b, r (u a * (Pi.single i 1 : β → A) b - w a * (G *ᵥ c ∘ u) b) =
      z a * (Pi.single i 1 : β → K) b) → z ∉ LinearMap.range (M.map r).mulVecLin → ∃ S : Matrix β β A,
      Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := fun u z h1 h2 => by
    refine ⟨_, skew_two hc hG u w, ?_⟩
    rw [Matrix.map_add _ (map_add r), Matrix.map_mul, hw, show (vecMulVec u (Pi.single i 1) - vecMulVec w (G *ᵥ c ∘ u)).map r =
      vecMulVec z (Pi.single i 1) from Matrix.ext h1, vecMulVec_mul]
    refine rank_lt hy h2 ?_
    rwa [← dotProduct_mulVec, mv, single_dotProduct, one_mul]
  have sg : ∀ b, r ((Pi.single i 1 : β → A) b) = (Pi.single i 1 : β → K) b := fun b => by
    simp [Pi.single_apply, apply_ite r]
  rcases hcase with ⟨h1, κ, hκ⟩ | ⟨η, h1, h2⟩
  · refine fin (κ • w) (r (κ - c κ) • r ∘ w) (fun a b => ?_) fun h => ?_
    · rw [show c ∘ (κ • w) = c κ • c ∘ w from funext fun _ => map_mul c _ _, mulVec_smul, hw]
      simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply]
      ring
    · obtain ⟨x₀, hx⟩ := (Submodule.smul_mem_iff _ hκ).1 h
      obtain ⟨x, rfl⟩ := hr.comp_left x₀
      rw [mulVecLin_apply, mv] at hx
      have l := congrArg (fun N => y ⬝ᵥ N *ᵥ c ∘ x) lag
      simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec, mc, zero_mulVec, dotProduct_zero] at l
      rw [dotProduct_mulVec y, dotProduct_mulVec y mᵀ, vecMul_transpose, vecMul_transpose] at l
      have e : (m *ᵥ y) i = (m *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (w - M *ᵥ x) - (M *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (m *ᵥ x) := by
        rw [show c ∘ (w - M *ᵥ x) = c ∘ w - c ∘ (M *ᵥ x) from funext fun _ => map_sub c _ _, mulVec_sub, dotProduct_sub, hw,
          dotProduct_single, mul_one]
        linear_combination l
      refine hi ?_
      rw [mv] at hy
      rw [e, map_sub, r.map_dotProduct, r.map_dotProduct, hy, zero_dotProduct, ← mv G, show r ∘ c ∘ (w - M *ᵥ x) = 0 from
        funext fun a => h1 _ (by rw [Pi.sub_apply, map_sub]; exact sub_eq_zero.2 (congrFun hx a).symm), mulVec_zero,
        dotProduct_zero, sub_zero]
  · obtain ⟨z₀, hz⟩ : ∃ z, z ∉ LinearMap.range (M.map r).mulVecLin := by
      by_contra h
      push Not at h
      exact ((isUnit_iff_isUnit_det _).1 (mulVec_surjective_iff_isUnit.1 h)).ne_zero h0
    obtain ⟨z, rfl⟩ := hr.comp_left z₀
    refine fin (η • z) _ (fun a b => ?_) hz
    rw [show c ∘ (η • z) = c η • c ∘ z from funext fun _ => map_mul c _ _, mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply, h1, h2]
    ring

theorem exists_skew (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (hu : ∀ z, r z ≠ 0 → r (c z) ≠ 0 → IsUnit z)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ IsUnit (M + S * m).det := by
  have l2 : ∀ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 →
      (M + S * m)ᵀ * G * m.map c + mᵀ * G * (M + S * m).map c = 0 := fun S hS => by
    rw [transpose_add, transpose_mul, Matrix.map_add _ (map_add c), Matrix.map_mul]
    linear_combination (norm := noncomm_ring) lag + mᵀ * hS * m.map c
  have i2 : ∀ S : Matrix β β A, P * (M + S * m) + (Q - P * S) * m = 1 := fun S => by
    linear_combination (norm := noncomm_ring) inj
  have ind : ∀ k : ℕ, ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧
      (((M + S * m).map r).det ≠ 0 ∨ k ≤ ((M + S * m).map r).rank) := fun k => by
    induction k with
    | zero => exact ⟨0, by simp, .inr (Nat.zero_le _)⟩
    | succ k ih =>
      obtain ⟨S, h1, h2⟩ := ih
      by_cases h0 : ((M + S * m).map r).det = 0
      · obtain ⟨S', h3, h4⟩ := step hc hr hG hG' hcase (l2 S h1) (i2 S) h0
        refine ⟨S + S', ?_, .inr ?_⟩
        · rw [transpose_add, Matrix.map_add _ (map_add c)]
          linear_combination (norm := noncomm_ring) h1 + h3
        · rw [Matrix.add_mul, ← add_assoc]
          exact (h2.resolve_left (not_not.2 h0)).trans_lt h4
      · exact ⟨S, h1, .inl h0⟩
  obtain ⟨S, h1, h2⟩ := ind (Fintype.card β + 1)
  have h3 := h2.resolve_right (not_le.2 (Nat.lt_succ_of_le (rank_le_card_width _)))
  refine ⟨S, h1, hu _ (by rwa [r.map_det]) fun h4 => ?_⟩
  rw [c.map_det, r.map_det] at h4
  obtain ⟨y, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h4
  have l := congrArg (fun N : Matrix β β A => N.map r *ᵥ y) (l2 S h1)
  have j := congrArg (fun N : Matrix β β A => (N.map c).map r *ᵥ y) (i2 S)
  generalize M + S * m = t at *
  change (t.map c).map r *ᵥ y = 0 at hy
  simp only [Matrix.map_add _ (map_add r), Matrix.map_add _ (map_add c), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy,
    mulVec_zero, add_zero, zero_add, Matrix.map_zero _ (map_zero r), zero_mulVec, Matrix.map_one _ (map_zero r) (map_one r),
    Matrix.map_one _ (map_zero c) (map_one c), one_mulVec] at l j
  have g0 : (G.map r).det ≠ 0 := fun h => by
    have := congrArg (fun N : Matrix β β A => (N.map r).det) hG'
    simp only [Matrix.map_mul, det_mul, h, zero_mul, Matrix.map_one _ (map_zero r) (map_one r), det_one] at this
    exact zero_ne_one this
  rw [eq_zero_of_mulVec_eq_zero g0 (eq_zero_of_mulVec_eq_zero (by rwa [transpose_map, det_transpose]) l), mulVec_zero] at j
  exact hy0 j.symm

end Skew

variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}

theorem lag_of {b b' x y : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) :
    (y + b * (y - x))ᵀ * J * (y - x).map c + (y - x)ᵀ * J * (y + b * (y - x)).map c = 0 := by
  have h1 : g.1.1ᵀ * dbl J * g.1.1.map c = dbl J := g.2
  have h2 : (fromRows x y)ᵀ * dbl J * (fromRows x y).map c = 0 := by
    rw [← hg, transpose_mul, mapc_mul]
    calc _ = (diagCols β : Matrix (β ⊕ β) β A)ᵀ * (g.1.1ᵀ * dbl J * g.1.1.map c) * (diagCols β : Matrix (β ⊕ β) β A).map c := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [h1]; simp [diagCols, dbl, fromRows_map, mapc_one, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  have e : b'.map c = -1 - b.map c := by
    rw [← mapc_one (c := c), ← mapc_neg, ← mapc_sub, ← hb]; congr 1; abel
  have b2 : bᵀ * J = -J - J * b.map c := by rw [b1, e]; noncomm_ring
  rw [transpose_fromRows, dbl, fromCols_mul_fromBlocks, fromRows_map, fromCols_mul_fromRows] at h2
  rw [transpose_add, transpose_mul, mapc_add, mapc_mul, mapc_sub, transpose_sub]
  linear_combination (norm := noncomm_ring) (yᵀ - xᵀ) * b2 * (y.map c - x.map c) - h2

theorem exists_decomp {b b' x y t' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) (ht : (y + b * (y - x)) * t' = 1) {ε : A} (he : ε * ε = ε)
    (hc : c ε = ε) (hm : ε • (y - x) = y - x) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ g = s * n * s * p ∧ s.1.1 = CC b * SS ε * Ci b ∧
      n.1.1 = CC b * fromBlocks 1 (-((y - x) * t')) 0 1 * Ci b ∧ (n⁻¹).1.1 = CC b * fromBlocks 1 ((y - x) * t') 0 1 * Ci b ∧
      n.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 : GL β A).1 ∧
      p.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t.1 ∧
      t.1 = y + b * (y - x) ∧ (t⁻¹).1 = t' := by
  have lag := lag_of b1 hb g hg
  set m : Matrix β β A := y - x with hmd
  set t₀ := y + b * m with ht₀
  set T := -(m * t') with hT
  have ht' : t' * t₀ = 1 := mul_eq_one_comm.1 ht
  have sk : Tᵀ * J + J * T.map c = 0 := by
    have a1 : t'ᵀ * t₀ᵀ = 1 := by rw [← transpose_mul, ht, transpose_one]
    have a2 : t₀.map c * t'.map c = 1 := by rw [← mapc_mul, ht, mapc_one]
    rw [hT, transpose_neg, transpose_mul, mapc_neg, mapc_mul]
    linear_combination (norm := noncomm_ring) -(t'ᵀ * lag * t'.map c) + a1 * J * m.map c * t'.map c + t'ᵀ * mᵀ * J * a2
  have e0 : ε * (1 - ε) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have e0' : (1 - ε) * ε = 0 := by rw [mul_comm, e0]
  have e1 : (1 - ε) * (1 - ε) = 1 - ε := by rw [sub_mul, one_mul, e0, sub_zero]
  have hS : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * SS ε = 1 := by
    rw [SS, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hSu : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 * (SS ε : Matrix (β ⊕ β) (β ⊕ β) A).map c =
      fromBlocks 0 J J 0 := by
    rw [SS, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mapc_smul, mapc_one, map_sub, map_one, hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hU : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 (m * t') 0 1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one, hT]; simp
  have hUu : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 *
      (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A).map c = fromBlocks 0 J J 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_one, mapc_zero]
    simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    rw [add_comm (J * _), sk]
  have hTt : T * t₀ = -m := by rw [hT, Matrix.neg_mul, Matrix.mul_assoc, ht', Matrix.mul_one]
  let s := mkU b1 hb _ _ hS hSu
  let n := mkU b1 hb _ _ hU hUu
  have hs : s.1.1 = CC b * SS ε * Ci b := rfl
  have hn : n.1.1 = CC b * fromBlocks 1 T 0 1 * Ci b := rfl
  have hεT : ε • T = T := by rw [hT, smul_neg, ← Matrix.smul_mul, hm]
  have hεT' : (1 - ε) • T = 0 := by rw [sub_smul, one_smul, hεT, sub_self]
  have hL : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 T 0 1 * SS ε = fromBlocks 1 0 T 1 := by
    rw [SS, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero, hεT, hεT',
      zero_add, Matrix.add_mul, smul_add, smul_smul, e0, e0', e1, he, zero_smul, ← add_smul]
    simp
  have hD : Ci b * (diagCols β : Matrix (β ⊕ β) β A) = (fromRows 1 0 : Matrix (β ⊕ β) β A) := by
    rw [Ci, diagCols, fromBlocks_mul_fromRows]; simp
  have hD' : CC b * (fromRows 1 0 : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) := by
    rw [CC, diagCols, fromBlocks_mul_fromRows]; simp
  refine ⟨s, n, (s * n * s)⁻¹ * g, ⟨t₀, t', ht, ht'⟩, Subtype.ext (Units.ext s.1.mul_inv), by group, hs, hn, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hn, Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows]
    simpa using hD'
  · have e : (s * n * s).1.1 = CC b * fromBlocks 1 0 T 1 * Ci b := by
      change s.1.1 * n.1.1 * s.1.1 = _
      rw [hs, hn, ← hL]
      calc CC b * SS ε * Ci b * (CC b * fromBlocks 1 T 0 1 * Ci b) * (CC b * SS ε * Ci b)
          = CC b * (SS ε * (Ci b * CC b) * fromBlocks 1 T 0 1 * (Ci b * CC b) * SS ε) * Ci b := by noncomm_ring
        _ = _ := by rw [Ci_CC, Matrix.mul_one, Matrix.mul_one]
    have e2 : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (s * n * s).1.1 * ((diagCols β : Matrix (β ⊕ β) β A) * t₀) := by
      rw [e, hg, ← Matrix.mul_assoc _ (diagCols β : Matrix (β ⊕ β) β A), Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b),
        fromBlocks_mul_fromRows, CC, fromBlocks_mul_fromRows, fromRows_mul]
      congr 1
      · linear_combination (norm := noncomm_ring) -((1 + b) * hTt) - ht₀ + hmd
      · linear_combination (norm := noncomm_ring) -(b * hTt) - ht₀
    change ((s * n * s)⁻¹).1.1 * g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t₀
    rw [Matrix.mul_assoc _ g.1.1, e2, ← Matrix.mul_assoc, show ((s * n * s)⁻¹).1.1 * (s * n * s).1.1 = 1 from (s * n * s).1.inv_mul,
      Matrix.one_mul]

end GlobalTheory.ThK.Dbl.Vf2

end
end

