module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter

namespace GlobalTheory.SBInduced

variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]


omit [IsTopologicalGroup G] in
theorem isClosedEmbedding_translate (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) (g : G) : IsClosedEmbedding fun y => r (j y) g := by
  have hc' : ∀ g, Continuous fun x => r x g := fun g => hc.comp (Continuous.prodMk_left g)
  let e : X ≃ₜ X :=
    { toFun := fun x => r x g
      invFun := fun x => r x g⁻¹
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := hc' g
      continuous_invFun := hc' g⁻¹ }
  exact e.isClosedEmbedding.comp hj

theorem isQuotientMap_sweep (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : X × K ≃ₜ X × K :=
    { toFun := fun p => (r p.1 p.2, p.2)
      invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2)
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
        continuous_snd
      continuous_invFun := (hc.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd }
  have hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2 :=
    (isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp
      (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)
  refine hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))) fun x => ?_
  obtain ⟨y, c, hc, rfl⟩ := hs x
  exact ⟨(y, ⟨c, hc⟩), rfl⟩

theorem descend [T2Space X] (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) (H : G → SB Y)
    (hU : ∀ᶠ u in 𝓝 (1 : G), ∀ g, H (g * u) = H g)
    (hfib : ∀ y g y' g', r (j y) g = r (j y') g' → (H g).1 y = (H g').1 y') :
    ∃ Φ : SB X, ∀ g y, Φ.1 (r (j y) g) = (H g).1 y := by
  have hq := isQuotientMap_sweep r h1 hm hc hj hK hs
  choose y c hcK hx using hs
  let φ : X → ℂ := fun x => (H (c x)).1 (y x)
  have hφ : ∀ g z, φ (r (j z) g) = (H g).1 z := fun g z => hfib _ _ _ _ (hx _).symm
  have hnear : ∀ g : G, ∀ᶠ z in 𝓝 g, H z = H g := fun g => by
    have hc : Tendsto (fun z : G => g⁻¹ * z) (𝓝 g) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually hU).mono fun z hz => by simpa using hz g
  have hlc : IsLocallyConstant fun p : Y × G => (H p.2).1 p.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    filter_upwards [(continuous_snd.tendsto p).eventually (hnear p.2),
      (continuous_fst.tendsto p).eventually ((H p.2).2.1.eventually_eq p.1)] with z h₁ h₂
    rw [h₁, h₂]
  refine ⟨⟨φ, fun s => ?_, ?_⟩, hφ⟩
  · rw [← hq.isOpen_preimage]
    have := (hlc.comp_continuous (f := fun p : Y × K => (p.1, (p.2 : G)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) s
    convert this using 1
    ext p
    simp only [Set.mem_preimage, hφ, Function.comp_apply]
  · obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | H z = H x}) fun x _ => hnear x
    have hC : IsCompact (⋃ g ∈ t, tsupport (H g).1) :=
      t.isCompact_biUnion fun g _ => (H g).2.2
    refine HasCompactSupport.intro (((hC.image hj.continuous).prod hK).image hc) fun x hxn => ?_
    by_contra h0
    apply hxn
    obtain ⟨g, hg, hcg⟩ := Set.mem_iUnion₂.1 (ht (hcK x))
    refine ⟨(j (y x), c x), ⟨⟨y x, Set.mem_iUnion₂.2 ⟨g, hg, subset_tsupport _ ?_⟩, rfl⟩, hcK x⟩,
      (hx x).symm⟩
    rw [← show H (c x) = H g from hcg]
    exact h0

theorem sb_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  intro G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev
  have hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1 := IsOpen.mem_nhds hχ (one_mem χ.ker)
  have hce := isClosedEmbedding_translate r h1 hm hc hj
  let A : SB X → G → SB Y := fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g),
    Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩
  have hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun _ _ _ => rfl
  have hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w' := fun w w' h =>
    ev.injective (Subtype.ext (funext h))
  let T : SB X →ₗ[ℂ] smoothPart (ind P σ) :=
    { toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by
          rw [hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul,
            mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'
          refine Subtype.ext (funext fun g => ?_)
          show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)
          congr 1
          refine Subtype.ext (funext fun y => ?_)
          rw [hA, hA, map_mul, hu, mul_one, hm, hu'])⟩
      map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (funext fun y => mul_add _ _ _)))
      map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)
        rw [← map_smul]
        congr 1
        exact Subtype.ext (funext fun y => mul_left_comm _ _ _))) }
  have hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun Φ g y => by
    show (ev (ev.symm (A Φ g))).1 y = _
    rw [ev.apply_symm_apply, hA]
  have hinj : Function.Injective T := fun Φ Ψ h => Subtype.ext (funext fun x => by
    obtain ⟨y, c, -, rfl⟩ := hs x
    have := hT Φ c y
    rw [h, hT] at this
    exact (mul_left_cancel₀ (χ c).ne_zero this).symm)
  have hsurj : Function.Surjective T := fun F => by
    have hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x =>
        congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x
    obtain ⟨Φ, hΦ⟩ := descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g))
      (by
        filter_upwards [hχ', hF] with u hu hu' g
        rw [hu', map_mul, hu, mul_one])
      (fun y g y' g' h => by
        have h2 : r (j y) (g * g'⁻¹) = j y' := by rw [hm, h, ← hm, mul_inv_cancel, h1]
        have hp := hP _ _ _ h2
        have h3 : s y ⟨_, hp⟩ = y' := hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)
        have h4 := F.1.2 ⟨_, hp⟩ g'
        rw [show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g'] at h4
        show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'
        rw [h4, hev, h3]
        simp [← mul_assoc])
    refine ⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩
    rw [hT, hΦ]
    exact mul_inv_cancel_left₀ (χ g).ne_zero _
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

end GlobalTheory.SBInduced
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGL
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology

noncomputable section

namespace GlobalTheory.GelfandKazhdan

section General

variable {G : Type} [Group G] [TopologicalSpace G]

def pull (t : G ≃ₜ G) : SB G →ₗ[ℂ] SB G where
  toFun φ := ⟨fun x => φ.1 (t x), φ.2.1.comp_continuous t.continuous, φ.2.2.comp_homeomorph t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] in
theorem anti_one {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) : t 1 = 1 := by
  have := hm 1 1
  rw [one_mul] at this
  exact left_eq_mul.1 this

omit [TopologicalSpace G] in
theorem anti_inv {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) (x : G) : t x⁻¹ = (t x)⁻¹ := by
  have := hm x x⁻¹
  rw [mul_inv_cancel, anti_one hm] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem exists_stable (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x) (ht : ∀ x, t (t x) = x)
    (K₀ : Subgroup G) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ (∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧ ∀ j ∈ J, t j ∈ J := by
  intro U hU
  obtain ⟨J, ho, hJU, hJK, hn⟩ := hb U hU
  refine ⟨{ carrier := {y | y ∈ J ∧ t y ∈ J}
            mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, by rw [hm]; exact mul_mem hb.2 ha.2⟩
            one_mem' := ⟨one_mem _, by rw [anti_one hm]; exact one_mem _⟩
            inv_mem' := fun ha => ⟨inv_mem ha.1, by rw [anti_inv hm]; exact inv_mem ha.2⟩ },
    ho.inter (ho.preimage t.continuous), fun y hy => hJU hy.1, fun y hy => hJK hy.1,
    fun x hx j hj => ⟨hn x hx j hj.1, ?_⟩, fun j hj => ⟨hj.2, by rw [ht]; exact hj.1⟩⟩
  have := hn _ (inv_mem (hK x hx)) _ hj.2
  rw [hm, hm, anti_inv hm, ← mul_assoc]
  rwa [inv_inv] at this

theorem invariant_of_anti [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x)
    (ht : ∀ x, t (t x) = x) (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G))
    (hKc : IsCompact (K₀ : Set G)) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hs : ∀ x, ∃ s, t s = s ∧ s * x = t x * s) (T : SB G →ₗ[ℂ] ℂ)
    (hT : ∀ (g : G) (φ ψ : SB G), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) (φ : SB G) :
    T (pull t φ) = T φ := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose J hJo hJU hJK hJn hJt using fun m =>
    exists_stable t hm ht K₀ hK hb (U m) (hU.1.mem_of_mem trivial)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable S := hSc.to_subtype
  let K : S → ℕ → Subgroup G := fun c m => J m ⊓ (J m).comap (MulAut.conj (c : G)).toMonoidHom
  have hKm : ∀ c m y, y ∈ K c m ↔ y ∈ J m ∧ (c : G) * y * (c : G)⁻¹ ∈ J m := fun c m y => Iff.rfl
  have hD : T - T.comp (pull t) = 0 := by
    refine _root_.GlobalTheory.BaireDistribution.eq_zero G S K (fun c m => ?_) (fun c V hV => ?_) _ fun x => ?_
    · have ho : IsOpen (K c m : Set G) :=
        (hJo m).inter ((hJo m).preimage (f := fun y => (c : G) * y * (c : G)⁻¹) (by fun_prop))
      exact ⟨ho, hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun y hy => hJK m hy.1⟩
    · obtain ⟨m, -, hm⟩ := hU.1.mem_iff.1 hV
      exact ⟨m, fun y hy => hm (hJU m hy.1)⟩
    · obtain ⟨s, hts, hsx⟩ := hs x
      obtain ⟨c, hc, hcS⟩ := hSd.inter_open_nonempty _
        (hKo.preimage (f := fun y => y * s⁻¹) (by fun_prop)) ⟨s, by simp⟩
      have hc' : c * s⁻¹ ∈ K₀ := hc
      refine ⟨⟨c, hcS⟩, fun m ψ hψ => ?_⟩
      have hK' : ∀ y, y ∈ K ⟨c, hcS⟩ m ↔ y ∈ J m ∧ s * y * s⁻¹ ∈ J m := fun y => by
        rw [hKm]
        refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
        · have := hJn m _ (inv_mem hc') _ h
          convert this using 1
          simp only []
          group
        · have := hJn m _ hc' _ h
          convert this using 1
          simp only []
          group
      have hτ : ∀ y, t (s * y * s⁻¹) = s⁻¹ * t y * s := fun y => by
        rw [hm, hm, anti_inv hm, hts, mul_assoc]
      have hτK : ∀ y ∈ K ⟨c, hcS⟩ m, s⁻¹ * t y * s ∈ K ⟨c, hcS⟩ m := fun y hy => by
        rw [hK'] at hy ⊢
        refine ⟨hτ y ▸ hJt m _ hy.2, ?_⟩
        convert hJt m _ hy.1 using 1
        group
      have h1 : ∀ y, y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} →
          s⁻¹ * t y * s ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨_, hτK b hb, _, hτK a ha, ?_⟩
        have : t x = s * x * s⁻¹ := by rw [hsx]; group
        rw [hm, hm, this]
        group
      have h2 : ∀ y, s⁻¹ * t (s⁻¹ * t y * s) * s = y := fun y => by
        rw [hm, hm, anti_inv hm, hts, ht]
        group
      have h3 : T ψ = T (pull t ψ) := hT s _ _ fun y => by
        show ψ.1 y = ψ.1 (t (s * y * s⁻¹))
        rw [hτ, hψ]
        by_cases hy : y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h1 y hy)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem fun h => hy (h2 y ▸ h1 _ h)]
      exact sub_eq_zero.2 h3
  exact (sub_eq_zero.1 (LinearMap.congr_fun hD φ)).symm

end General

section Transpose

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trGL (g : GL n R) : GL n R :=
  ⟨g.val.transpose, g.inv.transpose, by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]⟩

theorem trGL_trGL (g : GL n R) : trGL (trGL g) = g := rfl

theorem trGL_mul (g h : GL n R) : trGL (g * h) = trGL h * trGL g :=
  Units.ext (Matrix.transpose_mul _ _)

theorem continuous_trGL [TopologicalSpace R] : Continuous (trGL : GL n R → GL n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩

def trHomeo [TopologicalSpace R] : GL n R ≃ₜ GL n R where
  toFun := trGL
  invFun := trGL
  left_inv := trGL_trGL
  right_inv := trGL_trGL
  continuous_toFun := continuous_trGL
  continuous_invFun := continuous_trGL

end Transpose

theorem transpose_invariant (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ)
    (hT : ∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ)
    (φ ψ : SB (GL n k)) (h : ∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) :
    T ψ = T φ := by
  have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => h x (trGL x) rfl)
  rw [e]
  refine invariant_of_anti trHomeo trGL_mul trGL_trGL (KO k n) SplitFlip.isOpen_KO
    SplitFlip.isCompact_KO (fun x hx => ?_) (exists_open_normalised_subgroup_subset k n)
    (fun x => ?_) T hT φ
  · obtain ⟨h1, h2⟩ := (SplitFlip.mem_KO_iff _).1 hx
    exact (SplitFlip.mem_KO_iff _).2 ⟨fun i j => h1 j i, fun i j => h2 j i⟩
  · obtain ⟨P, ⟨s, rfl⟩, h1, h2⟩ := _root_.GlobalTheory.SymmetricSimilarTranspose.main k n x.val
    exact ⟨s, Units.ext h1, Units.ext h2⟩

end GlobalTheory.GelfandKazhdan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix

namespace GlobalTheory.LocalCartan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LocalCartan.diagT_mem_KO {t : n → kˣ} (ht : ∀ i, valuation k (t i : k) = 1) :
    _root_.GlobalTheory.SmGL.diagT k n t ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [_root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      exact (Valuation.mem_integer_iff _ _).mpr (ht i).le
    · exact zero_mem _
  · rw [← map_inv, _root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      refine (Valuation.mem_integer_iff _ _).mpr (le_of_eq ?_)
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, ht i, inv_one]
    · exact zero_mem _


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LocalCartan.exists_diagT (g : GL n k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ t : n → kˣ, g = x * _root_.GlobalTheory.SmGL.diagT k n t * y := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪[k])
    (Finset.univ : Finset (n × n)) (fun p => (g : Matrix n n k) p.1 p.2)
  choose G hG using fun i j => RingHom.mem_rangeS.mp (hb (i, j) (Finset.mem_univ _))
  set f := algebraMap 𝒪[k] k with hf
  set c : k := f b with hc_def
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hGg : f.mapMatrix (Matrix.of G) = c • (g : Matrix n n k) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [hG i j, Algebra.smul_def]
  have hdet : (Matrix.of G).det ≠ 0 := by
    intro h0
    have h1 := congrArg f h0
    rw [RingHom.map_det, hGg, map_zero, Matrix.det_smul] at h1
    exact mul_ne_zero (pow_ne_zero _ hc) ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h1
  obtain ⟨P, C, hP, hC, a, ha, hPC⟩ := _root_.Formalism.UG.P.cartan_smith (Matrix.of G) hdet
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hmap : ∀ A : GL n 𝒪[k],
      ((GeneralLinearGroup.map f A : GL n k) : Matrix n n k) = f.mapMatrix (A : Matrix n n 𝒪[k]) :=
    fun A => by ext i j; rw [GeneralLinearGroup.map_apply]; rfl
  have hmem : ∀ A : GL n 𝒪[k], GeneralLinearGroup.map f A ∈ _root_.GlobalTheory.SplitWeil.KO k n :=
    fun A => by unfold _root_.GlobalTheory.SplitWeil.KO; exact ⟨A, rfl⟩
  have hne : ∀ i, f (a i) / c ≠ 0 := fun i =>
    div_ne_zero ((map_ne_zero_iff f hinj).mpr (ha i)) hc
  refine ⟨_, hmem (GeneralLinearGroup.mk'' P hP), _, hmem (GeneralLinearGroup.mk'' C hC),
    fun i => Units.mk0 (f (a i) / c) (hne i), ?_⟩
  have key : f.mapMatrix P * diagonal (fun i => f (a i)) * f.mapMatrix C = c • (g : Matrix n n k) := by
    have hd : f.mapMatrix (diagonal a) = diagonal (fun i => f (a i)) := by
      rw [RingHom.mapMatrix_apply]
      exact Matrix.diagonal_map (map_zero f)
    rw [← hGg, hPC, map_mul, map_mul, hd]
  have hdiag : diagonal (fun i => ((Units.mk0 (f (a i) / c) (hne i) : kˣ) : k)) =
      c⁻¹ • diagonal (fun i => f (a i)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h, div_eq_inv_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hmap, hmap, _root_.GlobalTheory.SmGL.val_diagT]
  change (g : Matrix n n k) = f.mapMatrix P * _ * f.mapMatrix C
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_one_twisted_operators : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
  _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mpr (by simp)

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_inv_twisted_operators (y : kˣ) :
    _root_.GlobalTheory.SmGL.ord k y⁻¹ = -_root_.GlobalTheory.SmGL.ord k y := by
  have h := _root_.GlobalTheory.SmGL.ord_mul k y y⁻¹
  rw [mul_inv_cancel, ord_one_twisted_operators] at h
  omega

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_zpow_uniformizer' {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) :
    _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
  have h1 := _root_.GlobalTheory.SmGL.ord_eq_one hϖ
  induction m using Int.induction_on with
  | zero => simpa using ord_one_twisted_operators
  | succ i ih => rw [_root_.zpow_add_one, _root_.GlobalTheory.SmGL.ord_mul, ih, h1]
  | pred i ih =>
    rw [_root_.zpow_sub_one, _root_.GlobalTheory.SmGL.ord_mul, ih, ord_inv_twisted_operators, h1]
    ring

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma exists_unit_mul_zpow_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    ∃ u : kˣ, ∃ m : ℤ, valuation k (u : k) = 1 ∧ x = u * ϖ ^ m := by
  refine ⟨x * (ϖ ^ _root_.GlobalTheory.SmGL.ord k x)⁻¹, _root_.GlobalTheory.SmGL.ord k x, ?_, by simp⟩
  apply _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp
  rw [_root_.GlobalTheory.SmGL.ord_mul, ord_inv_twisted_operators,
    ord_zpow_uniformizer' hϖ]
  ring


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LocalCartan.cartan_decomposition (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    (ϖ : kˣ) (g : GL n k) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ m : n → ℤ, g = x * _root_.GlobalTheory.SmGL.diagT k n (fun i => ϖ ^ m i) * y := by
  obtain ⟨x, hx, y, hy, t, rfl⟩ := _root_.GlobalTheory.LocalCartan.exists_diagT g
  choose u m hu htu using fun i => exists_unit_mul_zpow_uniformizer hϖ (t i)
  refine ⟨x * _root_.GlobalTheory.SmGL.diagT k n u,
    mul_mem hx (_root_.GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, m, ?_⟩
  have ht : t = u * fun i => ϖ ^ m i := funext htu
  rw [ht, map_mul]
  simp only [mul_assoc]

end GlobalTheory.LocalCartan
end
end

