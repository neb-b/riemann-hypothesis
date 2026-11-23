module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts
section
noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

theorem tsfin_compact_lift {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X] (x : X)
    (hc : IsClosed (MulAction.orbit G x)) {K : Set X} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ y ∈ K, (∃ g : G, g • x = y) → ∃ g ∈ C, g • x = y := by
  haveI : LocallyCompactSpace (MulAction.orbit G x) := hc.locallyCompactSpace
  haveI : ContinuousSMul G (MulAction.orbit G x) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  let x₀ : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
  have ho : IsOpenMap fun g : G => g • x₀ := isOpenMap_smul_of_sigmaCompact x₀
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit G x)) :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let ex := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := hK'.elim_directed_cover (fun n : ℕ => (fun g : G => g • x₀) '' interior (ex n))
    (fun n => ho _ isOpen_interior)
    (by
      rintro ⟨y, g, rfl⟩ _
      obtain ⟨n, hn⟩ := ex.exists_mem g
      exact Set.mem_iUnion.2 ⟨n + 1, g, ex.subset_interior_succ n hn, rfl⟩)
    (Monotone.directed_le fun a b hab => Set.image_mono (interior_mono (ex.subset hab)))
  refine ⟨ex n, ex.isCompact n, fun y hy hg => ?_⟩
  obtain ⟨g, hg1, hg2⟩ := hn (a := ⟨y, hg⟩) hy
  exact ⟨g, interior_subset hg1, congrArg Subtype.val hg2⟩

theorem tsfin_hform_mulVec {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin n) (Fin n) A)
    (hg : Formalism.UG.cT σ g * J * g = J) (x : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec x) = Formalism.UG.hform σ J x x := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A),
      Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ J.mulVec y := by
    intro J x y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : σ ∘ g.mulVec x = (g.map σ).mulVec (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  rw [key, key, h2]
  conv_rhs => rw [← hg]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec (M := Formalism.UG.cT σ g), Matrix.dotProduct_mulVec (σ ∘ x),
    Formalism.UG.cT, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tsfin_q_smul (g : HA R σ J) (y : Fin 1 → Fin M → R ⊗[F] E) :
    qR R σ J ((g • y) 0) = qR R σ J (y 0) := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  unfold qR hR
  rw [← tsfin_hform_mulVec _ _ _ hg (y 0)]
  rfl

theorem tsfin_q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin 1 → Fin M → E) (a : F)
    (hx : hE σ J (x 0) (x 0) = algebraMap F E a) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R a := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have h : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      (1 : R) ⊗ₜ[F] algebraMap F E a := by
    rw [← hx]
    simp [hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, TensorProduct.tmul_sum]
  rw [qR, h, qloc_trace_tmul, Algebra.trace_algebraMap, h2, one_mul, ← map_mul]
  congr 1
  simp

theorem tsfin_q_cont [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun y : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (y 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  unfold qR hR Formalism.UG.hform
  fun_prop

end

theorem twoStep_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR M J x a B J' m m' N hS hO hm hm' _ hT
  classical
  obtain ⟨hJ, ha, hx, -, hJ', hJ'nd⟩ := hS
  have hq := tsfin_q_rat R σ J hcm.2.2.1 x a hx
  have hu : IsUnit (algebraMap F R a) := (IsUnit.mk0 a ha).map _
  have hc : IsClosed (MulAction.orbit (HA R σ J) (ratTup (F := F) R x)) := by
    have : MulAction.orbit (HA R σ J) (ratTup (F := F) R x) =
        {y | qR R σ J (y 0) = algebraMap F R a} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact (tsfin_q_smul R σ J g _).trans hq
      · intro hy
        exact GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hcm R hR (M + 1) J hJ _ _ y hu hq hy
    rw [this]
    exact isClosed_eq (tsfin_q_cont R σ J) continuous_const
  refine ⟨fun K hK => ?_⟩
  let K₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) := (fun X _ => X 0) '' K
  have hK₁ : IsCompact K₁ := hK.image (by fun_prop)
  obtain ⟨C, hC, hCK⟩ := tsfin_compact_lift _ hc hK₁
  let L : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)
  have hL : L * B = 1 := by
    rw [Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hJ'nd.2)
  have hL' : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let K' : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    (fun p : HA R σ J × (Fin 2 → Fin (M + 1) → R ⊗[F] E) => fun _ =>
      (L.map (inclR (F := F) R)).mulVec ((p.1⁻¹ • p.2) 1)) '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (continuous_pi fun _ =>
    continuous_const.matrix_mulVec ((continuous_apply 1).comp (continuous_fst.inv.smul continuous_snd)))
  let s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J := fun y =>
    if h : ∃ g ∈ C, g • ratTup (F := F) R x = y then h.choose
    else if h' : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h'.choose else 1
  have hs : IsSec R σ J x s := by
    intro y hy
    by_cases h : ∃ g ∈ C, g • ratTup (F := F) R x = y
    · simp only [s, dif_pos h]
      exact h.choose_spec.2
    · simp only [s, dif_neg h, dif_pos hy]
      exact hy.choose_spec
  have hsC : ∀ y ∈ K₁, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y ∈ C := by
    intro y hy hg
    have h := hCK y hy hg
    simp only [s, dif_pos h]
    exact h.choose_spec.1
  have h1 := hT (K.indicator 1) (measurable_one.indicator hK.measurableSet) s hs
  rw [lintegral_indicator_one hK.measurableSet] at h1
  rw [h1]
  have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := hO
  calc _ ≤ ∫⁻ y, K₁.indicator (fun _ => m' K') y ∂m := by
        refine lintegral_mono_ae (hae.mono fun y hy => ?_)
        by_cases hyK : y ∈ K₁
        · rw [Set.indicator_of_mem hyK, ← lintegral_indicator_one hK'.measurableSet]
          refine lintegral_mono fun y' => ?_
          by_cases hp : pairOf R σ J B y (s y) y' ∈ K
          · have : y' ∈ K' := by
              refine ⟨(s y, pairOf R σ J B y (s y) y'), ⟨hsC y hyK hy, hp⟩, ?_⟩
              funext i
              have e : ((s y)⁻¹ • pairOf R σ J B y (s y) y') 1 =
                  ((s y)⁻¹ • s y • fun _ : Fin 1 => (B.map (inclR (F := F) R)).mulVec (y' 0)) 0 := rfl
              simp only
              rw [e, inv_smul_smul, Matrix.mulVec_mulVec, hL', Matrix.one_mulVec,
                Subsingleton.elim i 0]
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem this]
          · simp [Set.indicator_of_notMem hp]
        · have : ∀ y', pairOf R σ J B y (s y) y' ∉ K := fun y' hp =>
            hyK ⟨_, hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩
          simp [Set.indicator_of_notMem (this _)]
    _ < ⊤ := by
        rw [lintegral_indicator_const hK₁.measurableSet]
        exact ENNReal.mul_lt_top hK'.measure_lt_top hK₁.measure_lt_top

end GlobalTheory.GaugeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamond
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpDia

section Local
variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem inc_dil {res : R →+* k} (hs : Function.Surjective res) {t : R} {p q : Pr R V k} (hp : p.Ok res)
    (h : Pr.Inc res t p q) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) := by
  obtain ⟨h1, h2, e, h3, h4⟩ := h
  obtain ⟨b, hb⟩ := hs a⁻¹
  have he : e ∈ q.L := by
    by_contra hn
    rw [h1.off _ hn] at h3
    exact zero_ne_one h3
  have hte : t • e ∈ p.L := by
    by_contra hn
    rw [hp.off _ hn] at h4
    exact zero_ne_one h4
  refine ⟨h1.dil ha, fun y => ?_, b • e, ?_, ?_⟩
  · show y ∈ p.L ↔ y ∈ q.L ∧ a * q.f y = 0
    rw [h2 y, mul_eq_zero, or_iff_right ha]
  · show a * q.f _ = 1
    rw [h1.smul _ _ he, h3, hb, mul_one, mul_inv_cancel₀ ha]
  · show a * p.f _ = 1
    rw [smul_comm, hp.smul _ _ hte, h4, hb, mul_one, mul_inv_cancel₀ ha]

def dilEquiv {a : k} (ha : a ≠ 0) : Pr R V k ≃ Pr R V k where
  toFun q := q.dil a
  invFun q := q.dil a⁻¹
  left_inv q := by
    show (q.dil a).dil a⁻¹ = q
    rw [Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one]
  right_inv q := by
    show (q.dil a⁻¹).dil a = q
    rw [Pr.dil_dil, mul_inv_cancel₀ ha, Pr.dil_one]

end Local

theorem atV_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J}
    (h : AtV v η) (δ : GA σ J) : AtV v (δ⁻¹ * η * δ) := by
  intro v' hv'
  have h1 := h v' hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1, mul_one, inv_mul_cancel]

theorem upAd_dia : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hP res t hs hok g hg v' hv' a δ hb' ha hδ x
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.LevelHecke.ValAt.valAt_spec F E σ n J T f bad ι S emb v hv k p hb hP g hg
  by_cases hvv : v' = v
  · subst hvv
    have ha' := ha rfl
    unfold upAd
    rw [hP.2.2 x δ a hδ, h2 x δ hδ.1]
    refine finsum_mem_eq_of_bijOn (fun q => q.dil (a : k)) ?_ (fun q _ => (h3 a δ x q ha' hδ).symm)
    refine (dilEquiv ha').bijOn' ?_ ?_
    · intro q hq
      exact inc_dil hs (hok x) hq ha'
    · intro q hq
      have := inc_dil hs ((hok x).dil ha') hq (inv_ne_zero ha')
      rw [Pr.dil_dil, inv_mul_cancel₀ ha', Pr.dil_one] at this
      exact this
  · have hp : ∀ y, p (y * δ) = p y := fun y => (hP.2.1 y δ).2 (by
      rw [hδ.1 v (Ne.symm hvv)]; exact one_mem _)
    have key : valAt v p (fun y => g (y * δ)) x = valAt v p g (x * δ) := by
      funext q
      by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
      · have hc := h.choose_spec
        have e : x * δ * (δ⁻¹ * h.choose * δ) = x * h.choose * δ := by group
        have := h1 (x * δ) _ (atV_conj hc.1 δ)
        rw [e, hp, hc.2] at this
        rw [this]
        unfold valAt
        rw [dite_eq_left h]
      · have h' : ¬ ∃ η, AtV v η ∧ p (x * δ * η) = q := by
          rintro ⟨η, hη, hq⟩
          refine h ⟨δ⁻¹⁻¹ * η * δ⁻¹, atV_conj hη _, ?_⟩
          rw [← hp, ← hq]
          congr 1
          group
        unfold valAt
        rw [dite_eq_right h, dite_eq_right h']
    unfold upAd
    rw [hp, key]

end GlobalTheory.LevelHecke.UpDia
end

