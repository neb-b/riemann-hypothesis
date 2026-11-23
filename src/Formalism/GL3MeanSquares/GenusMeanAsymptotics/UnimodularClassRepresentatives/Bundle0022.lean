module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0020
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem det_update_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (a : ι → K) (i : ι) : b.det (Function.update x i (∑ k, a k • x k)) = a i * b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  have e : Matrix.transpose (b.toMatrix (Function.update x i (∑ k, a k • x k))) =
      (Matrix.transpose (b.toMatrix x)).updateRow i (∑ k, a k • Matrix.transpose (b.toMatrix x) k) := by
    ext r s
    rcases eq_or_ne r i with rfl | hr
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [Basis.toMatrix_apply, Matrix.updateRow_self, Finset.sum_apply, map_sum, map_smul]
    · simp [Basis.toMatrix_apply, Matrix.updateRow_ne hr, Function.update_apply, hr]
  rw [e, Matrix.det_updateRow_sum, smul_eq_mul]

theorem exists_adjust (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {c : 𝓞 K}
    (hc : c ∉ P) : ∃ π ∈ P, c + π ∉ P ∧ c + π ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hadd : ∀ π ∈ P, c + π ∉ P := fun π hπ h => hc (by simpa using P.sub_mem h hπ)
  have hle2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P.comap (conjO K) := by
    refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, hrs⟩
    show conjO K r ∈ P
    have e : conjO K r = s := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := by
        first | rfl | simp [conjO]
      rw [e1, hrs, star_star]
    rw [e]
    exact hs
  have hne_top : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ P.comap (conjO K) := hle2 (by rw [htop]; exact Submodule.mem_top)
    rw [Ideal.mem_comap, map_one] at h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  by_cases hc' : c ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P
  · have hnle : ¬ P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      intro hle
      have hPe := hP.eq_of_le hne_top hle
      exact hc (by rw [hPe]; exact hc')
    obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.1 hnle
    refine ⟨π, hπ, hadd π hπ, fun h => hπ' ?_⟩
    have h3 := (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).sub_mem h hc'
    simpa using h3
  · exact ⟨0, P.zero_mem, by simpa using hc, by simpa using hc'⟩

theorem step_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V} (S : IsStep P A B y)
    (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (b : Basis (Fin (finrank K V)) K V) :
    discrIdeal h A ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B := by
  refine discrIdeal_le b fun x hx z hz => ?_
  have hxB : ∀ i, x i ∈ B := fun i => S.le (hx i)
  by_cases hδ : b.det x = 0
  · have : z = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [hz, hδ, mul_zero, map_zero]
    rw [this]; exact Ideal.zero_mem _
  have hbas := (b.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hδ)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    (hbas.2 ▸ Submodule.mem_top : y ∈ Submodule.span K (Set.range x))
  let f : Option (Fin (finrank K V)) → K := fun o => o.elim 1 a
  obtain ⟨t, c, hc, j, hj⟩ := exists_prim f (j₀ := none) (by simp [f]) hP.ne_top
  have hf0 : f none = 1 := rfl
  have hfs : ∀ i, f (some i) = a i := fun i => rfl
  have hc0 : c none ∈ P := by
    apply S.mem_of_smul_mem hP
    have : c none • y = ∑ i, c (some i) • x i := by
      rw [← algebraMap_smul K, hc none, ← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul K (c (some i)), hc (some i), smul_smul, hf0, hfs, mul_one]
    rw [this]; exact A.sum_mem fun i _ => A.smul_mem _ (hx i)
  obtain ⟨i, rfl⟩ : ∃ i, j = some i := by
    cases j with
    | none => exact absurd hc0 hj
    | some i => exact ⟨i, rfl⟩
  have hδi : b.det (Function.update x i y) = a i * b.det x := by rw [← ha, det_update_sum]
  have hrel : algebraMap (𝓞 K) K (c (some i)) * b.det x =
      algebraMap (𝓞 K) K (c none) * b.det (Function.update x i y) := by
    rw [hc, hc, hδi, hf0, hfs]; ring
  obtain ⟨π, hπ, hcP, hcQ⟩ := exists_adjust hK hP hj
  set c₁ := c (some i) + π with hc₁
  set c₀ := c none with hc₀
  have hcδ : algebraMap (𝓞 K) K c₁ * b.det x =
      algebraMap (𝓞 K) K c₀ * b.det (Function.update x i y) + algebraMap (𝓞 K) K π * b.det x := by
    rw [hc₁, map_add (f := _), add_mul, hrel]
  have hxk : ∀ k, k ≠ i → x k ∈ B := fun k _ => hxB k
  have huy := update_mem hxk S.mem
  obtain ⟨zyy, hyy⟩ := exists_mixed hB b huy huy
  obtain ⟨zyx, hyx⟩ := exists_mixed hB b huy hxB
  obtain ⟨zxy, hxy⟩ := exists_mixed hB b hxB huy
  have myy := mem_discrIdeal b huy hyy
  have mxx := mem_discrIdeal b hxB hz
  have myx : zyx ∈ discrIdeal h B :=
    mixed_mem hK hB b hxk S.mem (hxB i) (by rw [Function.update_eq_self]; exact hyx)
  have mxy : zxy ∈ discrIdeal h B :=
    mixed_mem hK hB b hxk (hxB i) S.mem (by rw [Function.update_eq_self]; exact hxy)
  have heq : conjO K c₁ * c₁ * z = conjO K c₀ * c₀ * zyy + conjO K c₀ * π * zyx +
      conjO K π * c₀ * zxy + conjO K π * π * z := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_add (f := _), map_mul, algebraMap_conjO, hz, hyy, hyx, hxy]
    have h1 : star (algebraMap (𝓞 K) K c₁) * algebraMap (𝓞 K) K c₁ *
        (star (b.det x) * gdet h b * b.det x) =
        star (algebraMap (𝓞 K) K c₁ * b.det x) * gdet h b * (algebraMap (𝓞 K) K c₁ * b.det x) := by
      rw [star_mul']; ring
    rw [h1, hcδ, star_add, star_mul', star_mul']
    ring
  have hmem : conjO K c₁ * c₁ ∈ col (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B) z := by
    rw [mem_col, heq]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (term_mem hc0 hc0 myy)
      (term_mem hc0 hπ myx)) (term_mem hπ hc0 mxy)) (term_mem hπ hπ mxx)
  have hPP : P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤
      col (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B) z :=
    fun r hr => Ideal.mul_mem_mul hr mxx
  apply mem_of_col_eq_top
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcc : ∀ w : 𝓞 K, conjO K w ∈ P → w ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro w hw; rw [conjIdeal_eq_comap, Ideal.mem_comap]; exact hw
  have hcc' : ∀ w : 𝓞 K, conjO K w ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P → w ∈ P := by
    intro w hw; rw [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO] at hw; exact hw
  rcases hM.isPrime.mul_le.1 (hPP.trans hle) with h1 | h1
  · have hMP := hP.eq_of_le hM.ne_top h1
    rcases hM.isPrime.mem_or_mem (hle hmem) with h2 | h2
    · exact hcQ (hcc _ (hMP ▸ h2))
    · exact hcP (hMP ▸ h2)
  · have hMP := (conjIdeal_isMaximal hK hP).eq_of_le hM.ne_top h1
    rcases hM.isPrime.mem_or_mem (hle hmem) with h2 | h2
    · exact hcP (hcc' _ (hMP ▸ h2))
    · exact hcQ (hMP ▸ h2)

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem IsStep.relIndex {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V}
    (S : IsStep P A B y) : A.toAddSubgroup.relIndex B.toAddSubgroup = Ideal.absNorm P := by
  classical
  let f : 𝓞 K →+ B.toAddSubgroup :=
    { toFun := fun c => ⟨c • y, B.smul_mem c S.mem⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp [add_smul] }
  let g : 𝓞 K →+ B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    (QuotientAddGroup.mk' _).comp f
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨c, hc⟩ := S.gen x.1 x.2
    refine ⟨c, ?_⟩
    simp only [g, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [f, neg_add_eq_sub] using hc
  have hker : g.ker = P.toAddSubgroup := by
    ext c
    simp only [AddMonoidHom.mem_ker, g, f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact ⟨fun h => S.mem_of_smul_mem hP h, fun h => S.smul c h⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker,
    Ideal.absNorm_apply]
  rfl

theorem absNorm_discrIdeal_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {B : Submodule (𝓞 K) V} (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (b : Basis (Fin (finrank K V)) K V) :
    ∀ (n : ℕ) (A : Submodule (𝓞 K) V), A ≤ B → A.toAddSubgroup.relIndex B.toAddSubgroup = n →
      n ≠ 0 → Ideal.absNorm (discrIdeal h A) = n ^ 2 * Ideal.absNorm (discrIdeal h B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAB hn hn0
  by_cases hBA : B ≤ A
  · have : A = B := le_antisymm hAB hBA
    subst this
    rw [AddSubgroup.relIndex_self] at hn
    rw [← hn, one_pow, one_mul]
  obtain ⟨y₀, hy₀B, hy₀A⟩ := SetLike.not_le_iff_exists.1 hBA
  let J : Ideal (𝓞 K) := A.comap (LinearMap.toSpanSingleton (𝓞 K) V y₀)
  have hJ : ∀ c, c ∈ J ↔ c • y₀ ∈ A := fun c => Iff.rfl
  have hJtop : J ≠ ⊤ := by
    intro hJt
    have : (1 : 𝓞 K) ∈ J := hJt ▸ Submodule.mem_top
    rw [hJ, one_smul] at this
    exact hy₀A this
  have hJbot : J ≠ ⊥ := by
    intro hJb
    obtain ⟨k, hk0, -, hk⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero
      (H := A.toAddSubgroup) (K := B.toAddSubgroup) (hn ▸ hn0) (a := y₀) hy₀B
    have h1 : (k : 𝓞 K) ∈ J := by
      rw [hJ, Nat.cast_smul_eq_nsmul]
      exact hk.1
    rw [hJb, Ideal.mem_bot] at h1
    exact hk0.ne' (by exact_mod_cast h1)
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJtop
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 hJP
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ'
    exact hJbot hJ'
  have hnle : ¬ J' ≤ J := by
    intro hle
    have h1 : P * J' = 1 * J' := by
      rw [one_mul, ← hJ']
      exact le_antisymm (hJ' ▸ Ideal.mul_le_right) hle
    exact hP.ne_top (by rw [mul_right_cancel₀ hJ'0 h1, Ideal.one_eq_top])
  obtain ⟨c, hcJ', hcJ⟩ := SetLike.not_le_iff_exists.1 hnle
  have S : IsStep P A (A ⊔ Submodule.span (𝓞 K) {c • y₀}) (c • y₀) := by
    refine ⟨le_sup_left, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), hcJ,
      fun π hπ => ?_, fun x hx => ?_⟩
    · rw [smul_smul, ← hJ, hJ']
      exact Ideal.mul_mem_mul hπ hcJ'
    · obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hw
      exact ⟨e, by rwa [add_sub_cancel_right]⟩
  have hA'B : A ⊔ Submodule.span (𝓞 K) {c • y₀} ≤ B :=
    sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 (B.smul_mem c hy₀B))
  have hA' : Formalism.HermitianLatticesTheory.IsIntegralLat h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    fun x hx w hw => hB x (hA'B hx) w (hA'B hw)
  have hmul := AddSubgroup.relIndex_mul_relIndex A.toAddSubgroup
    (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup B.toAddSubgroup S.le hA'B
  rw [S.relIndex hP, hn] at hmul
  have hq1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have hq0 : Ideal.absNorm P ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hn0 hmul.symm
  have hn'0 : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hn0 hmul.symm
  have hlt : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup < n := by
    rw [← hmul]
    have h2 : 2 ≤ Ideal.absNorm P := by omega
    nlinarith [Nat.pos_of_ne_zero hn'0]
  have hI : discrIdeal h A = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P *
      discrIdeal h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    le_antisymm (step_le hK hP S hA' b) (step_ge hK hP S hA' b)
  rw [hI, map_mul, map_mul, absNorm_conjIdeal hK, ih _ hlt _ hA'B rfl hn'0, ← hmul]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  let ι := algebraMap (𝓞 F) (𝓞 K)
  have coe_ι (b : 𝓞 F) : ((ι b : 𝓞 K) : K) = algebraMap F K (b : F) :=
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K b).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K b)
  have ι_injective : Function.Injective ι := by
    intro b c h
    apply RingOfIntegers.ext
    have hcoe := congrArg (fun z : 𝓞 K => (z : K)) h
    exact (algebraMap F K).injective ((coe_ι b).symm.trans (hcoe.trans (coe_ι c)))
  have conj_ι (b : 𝓞 F) : conjO K (ι b) = ι b := by
    apply RingOfIntegers.ext
    change star ((ι b : 𝓞 K) : K) = ((ι b : 𝓞 K) : K)
    rw [coe_ι]
    exact (hF _).mpr ⟨b, rfl⟩
  have exists_trace (z : 𝓞 K) : ∃ b : 𝓞 F, ι b = z + conjO K z := by
    let w : 𝓞 K := z + conjO K z
    have hw : star (w : K) = (w : K) := by
      change star ((z : K) + star (z : K)) = (z : K) + star (z : K)
      rw [star_add, star_star, add_comm]
    obtain ⟨b, hb⟩ := (hF _).mp hw
    have hb_int : IsIntegral ℤ b := by
      apply (isIntegral_algHom_iff (algebraMap F K).toIntAlgHom (algebraMap F K).injective).mp
      change IsIntegral ℤ (algebraMap F K b)
      rw [hb]
      exact RingOfIntegers.isIntegral_coe w
    refine ⟨⟨b, hb_int⟩, RingOfIntegers.ext ?_⟩
    exact (coe_ι ⟨b, hb_int⟩).trans hb
  let trace (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_trace z)
  have trace_spec (z : 𝓞 K) : ι (trace z) = z + conjO K z :=
    Classical.choose_spec (exists_trace z)
  let tr : 𝓞 K →ₗ[𝓞 F] 𝓞 F :=
    { toFun := trace
      map_add' := by
        intro x y
        apply ι_injective
        rw [trace_spec, map_add, map_add, trace_spec, trace_spec]
        ring
      map_smul' := by
        intro b z
        apply ι_injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, trace_spec, trace_spec, Algebra.smul_def,
          map_mul, conj_ι]
        ring }
  have htop : LinearMap.range tr = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range tr) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← trace_spec]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have hdiff : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [pow_one] using hsq)
    have hone : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [mul_one] using hdiff)
    have hcomap : Ideal.comap ι (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    have hone_mem : (1 : 𝓞 F) ∈ 𝔭 := by
      rw [← hcomap, Ideal.mem_comap, map_one]
      simpa only [pow_one] using hone
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 hone_mem)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range tr := htop ▸ Submodule.mem_top
  exact ⟨z, (trace_spec z).symm.trans (congrArg ι hz)⟩

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem exists_smul_iff (N M : Submodule (𝓞 K) V) :
    (∃ g : Formalism.HermitianLatticesTheory.isom h, g • N = M) ↔ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨⟨g, hg⟩, e⟩

theorem finite_rep (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (n : K) : {x : V | x ∈ M ∧ h x x = n}.Finite := by
  have := hM
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos hd) M (Algebra.trace ℚ K n)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩

theorem finite_stab_lat (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsFullLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  have : Finite (Formalism.ThetaLiftIndependence.autL h M) := (Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos hd) M hM).to_subtype
  have : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M) := Finite.of_equiv _ (stabLatEquiv M).symm
  exact Set.toFinite _

theorem exists_classReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s :=
  (Formalism.ThetaLiftIndependence.classRepsDefinite K V h hs (trace_pos hd) L hL).1

theorem exists_pairReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (n : K) :
    ∃ sX : Finset (Submodule (𝓞 K) V × V), (∀ t ∈ sX, t ∈ pairs h L n) ∧
      ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p := by
  obtain ⟨s, hs1, hs2⟩ := exists_classReps hs hd hL
  refine OrbSum.exists_reps_of_cover (pairs h L n) (pairs_stable hs L n)
    (⋃ M ∈ s, (fun x => (M, x)) '' {x : V | x ∈ M ∧ h x x = n}) ?_ ?_ ?_
  · exact Set.Finite.biUnion s.finite_toSet fun M hM => (finite_rep hd (hs1 M hM).1.toIsLattice n).image _
  · intro c hc
    obtain ⟨M, hM, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨hs1 M hM, hx.1, hx.2⟩
  · intro p hp
    obtain ⟨M, ⟨hM, g, hg, hgM⟩, -⟩ := hs2 p.1 hp.1
    refine ⟨(M, g.symm p.2), Set.mem_iUnion₂.mpr ⟨M, hM, g.symm p.2, ⟨?_, ?_⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    · rw [← Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hgM]
      exact hp.2.1
    · rw [SplitBAux.symm_mem_isom hg]
      exact hp.2.2
    · exact Prod.ext hgM (LinearEquiv.apply_symm_apply g p.2)

theorem sum_pairs_eq_rep (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (n : K)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {sX : Finset (Submodule (𝓞 K) V × V)} (hsX : ∀ t ∈ sX, t ∈ pairs h L n)
    (hX : ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) t) : ℕ) : ℝ)⁻¹ =
      ∑ M ∈ s, (repCount h M n : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (Prod.fst : Submodule (𝓞 K) V × V → _)
    (fun _ _ => rfl) (pairs h L n) (Formalism.HermitianLatticesTheory.genus h L) (pairs_stable hs L n) (fun p hp => hp.1)
    sX s hsX hsr.1 hX (fun M hM => by simp_rw [exists_smul_iff]; exact hsr.2 M hM)
    (fun M hM => finite_stab_lat hs hd hM.1)
  rw [key]
  refine Finset.sum_congr rfl fun M hM => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V // p ∈ pairs h L n ∧ p.1 = M} = repCount h M n :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.2, (congrArg (fun N : Submodule (𝓞 K) V => p.1.2 ∈ N) p.2.2).mp p.2.1.2.1, p.2.1.2.2⟩
        invFun := fun x => ⟨(M, x.1), ⟨hsr.1 M hM, x.2.1, x.2.2⟩, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.symm rfl)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabLatEquiv M)]

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end

