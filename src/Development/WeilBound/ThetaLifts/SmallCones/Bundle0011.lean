module

public import Development.WeilBound.ThetaLifts.SmallCones.IwaGlob
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLatWIff
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0010
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0009
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0008
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.IwaExOf
section
noncomputable section

namespace PositivityTheory.ThKCT

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem iwaEx_of (hS : StabEx) : IwaEx := by
  intro F E _ _ _ _ _ σ B n n₁ X r s H hB hX hx h0 K hK
  obtain ⟨K₀, -, -, k1, k2, -⟩ := hS F E σ B n X r s hB hX
  obtain rfl : K = K₀ := Subgroup.ext fun g => (hK g).trans (k1 g).symm
  exact ⟨k2, IwaG.iwa_glob hB hX hx h0 (fun v _ hg => PositivityTheory.ThKG.Loc.Iwa.iwaLoc hB (Or.inl hX) hx h0 v hg) hK⟩

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.KFinDataOf
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol
open scoped TensorProduct Classical Matrix

theorem sb_unif {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] {g : Y → ℂ} (hg : g ∈ SB Y) :
    ∀ᶠ u in 𝓝 (0 : Y), ∀ y, g (y + u) = g y := by
  have h1 : ∀ᶠ u in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + u) = g y := by
    refine hg.2.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
    have a : Tendsto (fun z : Y × Y => z.2 + z.1) (𝓝 (0, y)) (𝓝 y) := by
      exact (continuous_snd.add continuous_fst).tendsto' ((0 : Y), y) y (add_zero y)
    filter_upwards [a.eventually (hg.1.eventually_eq y), (continuous_snd.tendsto ((0 : Y), y)).eventually (hg.1.eventually_eq y)]
      with z h h'
    rw [h, h']
  have h2 : ∀ᶠ u in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + -u) = g y := by
    have : Tendsto (fun u : Y => -u) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0 : Y)
    exact this.eventually h1
  filter_upwards [h1, h2] with u a b y
  by_cases hy : y ∈ tsupport g
  · exact a y hy
  by_cases hy' : y + u ∈ tsupport g
  · rw [← b _ hy', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Lev (C U : Set (κ → Af F)) (Ψ : (κ → AF F) → ℂ) : Prop :=
  (∀ x, ∀ y ∉ C, Ψ (pt x y) = 0) ∧ ∀ x y, ∀ u ∈ U, Ψ (pt x (y + u)) = Ψ (pt x y)

theorem exists_lev {Ψ} (h : Ψ ∈ schA F κ) : ∃ C, IsCompact C ∧ ∃ U ∈ 𝓝 0, Lev C U Ψ := by
  induction h using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨_, hg.2.isCompact, _, sb_unif hg, fun x y hy => by rw [pureA_pt, image_eq_zero_of_notMem_tsupport hy, mul_zero],
      fun x y u hu => by rw [pureA_pt, pureA_pt, hu y]⟩
  | zero => exact ⟨∅, isCompact_empty, _, univ_mem, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨C, hC, U, hU, a, b⟩ := h1
    obtain ⟨C', hC', U', hU', a', b'⟩ := h2
    exact ⟨_, hC.union hC', _, inter_mem hU hU', fun x y hy => by
      rw [Pi.add_apply, a x y fun h => hy (Or.inl h), a' x y fun h => hy (Or.inr h), add_zero],
      fun x y u hu => by rw [Pi.add_apply, Pi.add_apply, b x y u hu.1, b' x y u hu.2]⟩
  | smul c Φ _ h =>
    obtain ⟨C, hC, U, hU, a, b⟩ := h
    exact ⟨C, hC, U, hU, fun x y hy => by rw [Pi.smul_apply, a x y hy, smul_zero],
      fun x y u hu => by rw [Pi.smul_apply, Pi.smul_apply, b x y u hu]⟩

def slc (P : Submodule ℂ (SInf F κ)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Ψ | ∀ y, ∃ f ∈ P, ∀ x, Ψ (pt x y) = f x}
  zero_mem' := fun _ => ⟨0, zero_mem _, fun _ => rfl⟩
  add_mem' := fun ha hb y => by
    obtain ⟨f, hf, e⟩ := ha y
    obtain ⟨f', hf', e'⟩ := hb y
    exact ⟨f + f', add_mem hf hf', fun x => by rw [Pi.add_apply, e, e', SchwartzMap.add_apply]⟩
  smul_mem' := fun c _ ha y => by
    obtain ⟨f, hf, e⟩ := ha y
    exact ⟨c • f, Submodule.smul_mem _ c hf, fun x => by rw [Pi.smul_apply, e, SchwartzMap.smul_apply]⟩

theorem slc_mono {P Q : Submodule ℂ (SInf F κ)} (h : P ≤ Q) : slc P ≤ slc Q := fun _ hΨ y =>
  (hΨ y).imp fun _ hf => ⟨h hf.1, hf.2⟩

def levS (C U : Set (κ → Af F)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Ψ | Lev C U Ψ}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨fun x y hy => by rw [Pi.add_apply, ha.1 x y hy, hb.1 x y hy, add_zero],
    fun x y u hu => by rw [Pi.add_apply, Pi.add_apply, ha.2 x y u hu, hb.2 x y u hu]⟩
  smul_mem' := fun c _ ha => ⟨fun x y hy => by rw [Pi.smul_apply, ha.1 x y hy, smul_zero],
    fun x y u hu => by rw [Pi.smul_apply, Pi.smul_apply, ha.2 x y u hu]⟩

theorem orbit_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ρ : G →* Module.End ℂ ((κ → AF F) → ℂ)) (Φ : (κ → AF F) → ℂ) (hc : ∀ z, Continuous fun k => ρ k Φ z)
    (hs : ∀ k, ρ k Φ ∈ schA F κ) (P : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ P] (hP : ∀ k, ρ k Φ ∈ slc P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k Φ)) := by
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  let C := CompactExhaustion.choice (κ → Af F)
  obtain ⟨U, hU⟩ := (𝓝 (0 : κ → Af F)).exists_antitone_basis
  obtain ⟨⟨a, b⟩, k₀, hk₀⟩ := nonempty_interior_of_iUnion_of_closed (f := fun p : ℕ × ℕ => {k | Lev (C p.1) (U p.2) (ρ k Φ)})
    (fun p => by
      simp only [Lev, Set.setOf_and, Set.setOf_forall]
      exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_eq (hc _) continuous_const).inter
        (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (hc _) (hc _)))
    (Set.eq_univ_of_forall fun k => by
      obtain ⟨D, hD, V, hV, h1, h2⟩ := exists_lev (hs k)
      obtain ⟨a, ha⟩ := C.exists_superset_of_isCompact hD
      obtain ⟨b, hb⟩ := hU.mem_iff.1 hV
      exact Set.mem_iUnion.2 ⟨(a, b), fun x y hy => h1 x y fun h => hy (ha h), fun x y u hu => h2 x y u (hb hu)⟩)
  let Ω := slc P ⊓ levS (C a) (U b)
  let c : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ Ω := level_fin pt (fun z => ⟨_, _, pt_eta z⟩) c P (C.isCompact a) (hU.mem b) Ω (fun Ψ h => h.1)
    (fun Ψ h => h.2.1) fun Ψ h => h.2.2
  obtain ⟨s, -, hcov⟩ := isCompact_univ.elim_nhds_subcover
    (fun k₁ : G => (fun k => k₀ * k₁⁻¹ * k) ⁻¹' {k | Lev (C a) (U b) (ρ k Φ)}) fun k₁ _ =>
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hk₀)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ k₁ : s, Ω.map (ρ (k₁.1 * k₀⁻¹))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨k₁, h₁, hk⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ k))
  refine Submodule.mem_iSup_of_mem ⟨k₁, h₁⟩ ⟨ρ (k₀ * k₁⁻¹ * k) Φ, ⟨hP _, hk⟩, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end PositivityTheory.ThKCT.So

namespace PositivityTheory.ThKCT

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol So
open scoped TensorProduct Classical Matrix

theorem kFinData_of (hS : StabEx) : KFinData := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP K hK Φ hΦ
  have hs := IsUWeilPair.isUSplitting hP.weil
  have h1 : Φ ∈ schA F (Fin n × Fin d) ∧ ∃ m, ∀ k ∈ K, om (k, 1) Φ ∈ slc (polM M B.emb m) := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, hf, φ, h1, h2, rfl⟩ := h
      obtain ⟨g, hg, e⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hP.good φ h1 h2
      obtain ⟨m, hm⟩ := exists_polM M hP.base.std hf
      rw [e f]
      refine ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, m, fun k hk y => ?_⟩
      obtain ⟨A, hA⟩ := exists_slice hs.toIsSplitting (k, 1) hg y
      exact ⟨A f, polM_stab hP.base.std hs.toIsSplitting hg ((hK _).1 (inv_mem hk)).1 hA m hm, hA f⟩
    | zero => exact ⟨zero_mem _, 0, fun k _ => by rw [map_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a1, m, hm⟩ := ha
      obtain ⟨b1, m', hm'⟩ := hb
      refine ⟨add_mem a1 b1, max m m', fun k hk => ?_⟩
      rw [map_add (f := _)]
      exact add_mem (slc_mono (fil_mono _ _ (le_max_left _ _)) (hm k hk)) (slc_mono (fil_mono _ _ (le_max_right _ _)) (hm' k hk))
    | smul c a _ ha =>
      obtain ⟨a1, m, hm⟩ := ha
      refine ⟨Submodule.smul_mem _ c a1, m, fun k hk => ?_⟩
      rw [map_smul]
      exact Submodule.smul_mem _ c (hm k hk)
  obtain ⟨h1, m, hm⟩ := h1
  refine ⟨h1, ?_⟩
  obtain ⟨K', -, -, hK', hc, -⟩ := hS F E σ B n X r s hP.base hP.herm
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI := polM_fin M hP.base.cm B.emb m
  refine orbit_fin (om.comp ((MonoidHom.inl _ _).comp K.subtype)) Φ (fun z => ?_) (fun k => hs.pres _ _ h1) _ fun k => hm k.1 k.2
  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj z
  have hl' : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
    ⟨g' (fun i => (z i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (z i)) ∘L
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _), fun f => by simp [l, pureA, evI, mul_comm]⟩
  exact (hs.cont l hl' Φ h1).comp (continuous_subtype_val.prodMk continuous_const)

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.Kernel
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
variable {H : Plane E n n₁} {H' : Plane E d d₁} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' i₀ i₁ j₀ j₁ : ℕ}
  {μ : Measure (unip σ W H')} {𝓕 : Set (unip σ W H')} {M₁ : Model σ X W₁} {e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁}

theorem countable_E : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable

theorem pair_low (hP : PairEx) (hL : Low) (hp : IsPair B M χX χW om r s r' s') (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hM₁ : M₁.IsGood B.ψ) : ∃ om₁, IsPair B M₁ χX χW om₁ r s (r' - 1) (s' - 1) :=
  (hP F E σ B hp.base n d₁ X W₁ r s _ _ hp.herm ((hL F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base hH').2 hp.skew).2.2).2 χX χW hp.hX hp.hW
    hp.resX (res_low hp.resW hH'.rank) M₁ hM₁

theorem mix0 (hW : MixW) (hp : IsPair B M χX χW om r s r' s') (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) {om₁ r₁ s₁}
    (hp₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀) (g) {u} (hu : u ∈ unip σ W H') {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e₀ (om (g, u) Φ) = om₁ (g, 1) (e₀ Φ) := by
  have := hW F E σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hp₁ e₀ he g 1 1 1 Fr.levi_one u hu Φ hΦ
  simpa using this

theorem meanOK (hU : UnipEx) (hG : GrpTop) (hO : EpsOf) (hp : IsPair B M χX χW om r s r' s') (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (a : μ.IsHaarMeasure) (b : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ) (c : μ 𝓕 = 1) : MeanOK σ W H' μ 𝓕 :=
  ⟨a, (hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH').2.2.2.1 μ a, b, c,
    (hG F E σ hp.base.cm d W.J (hO F E σ B hp.base d W r' s' (Or.inr hp.skew)).1).2.2.2.1⟩

theorem sum0 (hS : Slice) (hA : EvAdm) (hm : MeanOK σ W H' μ 𝓕) (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1))
    (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) {C : ℂ}
    (hC : ∀ Φ ∈ schA F _, HasSum (fun t => C * thetaSum F (e₀ (M.co.rho B.ψ (incM F (vL n H'.y t)) Φ))) (thetaSum F Φ)) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    HasSum (fun x => C * ∫ u in 𝓕, tm B M om H' e₀ (vecMulVec x H'.y) Φ u ∂μ) (∫ u in 𝓕, thetaSum F (om (1, u.1) Φ) ∂μ) := by
  have := countable_E (E := E)
  obtain ⟨m, b, z, hP⟩ := pol0 (F := F) (herm_det hp.herm) h'
  obtain ⟨β, h1, h2⟩ := slice_unif hS hp.base hp.good hM₁ he hP.toDual hΦ
  simp only [← integral_const_mul]
  refine hm.sum (f := fun x u => C * tm B M om H' e₀ (vecMulVec x H'.y) Φ u) (fun x => continuous_const.mul (tm_cont hA hp hM₁ he _ hΦ)) (b := fun x => ‖C‖ * β (b.equivFun x))
    ((b.equivFun.toEquiv.summable_iff.2 h1).mul_left _) (fun x u => ?_) fun u => hC _ (om_mem hp _ hΦ)
  obtain ⟨w, hw⟩ := constant_term_norm_eq_theta hp h' he hi x hΦ u
  rw [norm_mul, hw, ← vL_apply, ← lin_basis b]
  exact mul_le_mul_of_nonneg_left (h2 _ _) (norm_nonneg _)

theorem constant_term_integral_at_zero (hm : MeanOK σ W H' μ 𝓕) (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∫ u in 𝓕, tm B M om H' e₀ (vecMulVec 0 H'.y) Φ u ∂μ = thetaSum F (e₀ Φ) := by
  rw [← hm.const (thetaSum F (e₀ Φ))]
  congr 1
  funext u
  rw [tm, incM_vv, show incV F (0 : Fin n → E) = 0 from funext fun _ => map_zero _, Matrix.zero_vecMulVec, rho_zero, hi _ u.2 _ hΦ]

theorem constant_term_rational_translate (hW : MixW) (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) {om₁ r₁ s₁}
    (hp₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀) {γ : UA σ X.J} (hγ : γ ∈ ratU σ X.J)
    {x y : Fin n → E} (hx : mat γ *ᵥ incV F x = incV F y) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') :
    tm B M om H' e₀ (vecMulVec x H'.y) Φ u = tm B M om H' e₀ (vecMulVec y H'.y) (om (γ, 1) Φ) u := by
  have h1 := rho_mem M hp.base.std (incM F (vecMulVec x H'.y)) (om_mem hp (1, u.1) hΦ)
  have h2 := ((hT F E σ B n d₁ X W₁ M₁ χX χW om₁ r s r₁ s₁ hp₁).1 _ (he.maps _ h1)).2.1 γ hγ 1 (one_mem _) 1 1
  rw [theta, theta, mul_one, mul_one, ← mix0 hW hp hH' hp₁ he γ (one_mem _) h1, show ((1 : UA σ X.J), (1 : UA σ W₁.J)) = 1 from rfl,
    map_one, Module.End.one_apply, om_rho hp _ _ _ (om_mem hp _ hΦ), Fr.mat_one, Matrix.transpose_one, Matrix.mul_one, om_om, incM_vv,
    Matrix.mul_vecMulVec, hx] at h2
  rw [tm, tm, incM_vv, incM_vv, ← h2, om_om]
  simp

theorem constant_term_cone_integral_eq (hA : EvAdm) (hm : MeanOK σ W H' μ 𝓕) (hp : IsPair B M χX χW om r s r' s') (h : PG σ X X₁ H 1)
    (h' : PG σ W W₁ H' (-1)) {M₂ : Model σ X₁ W₁} (hM₂ : M₂.IsGood B.ψ) (he₀ : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₂ H.ι H'.ι (sumA H H') e)
    (hi₀ : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) {eX : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁} {C c : ℂ}
    (hc : c ≠ 0) (hC : ∀ Φ ∈ schA F _, HasSum (fun t => C * thetaSum F (eX (M₁.co.rho B.ψ (incM F (vR d₁ H.y t)) Φ))) (thetaSum F Φ))
    (hce : ∀ Φ ∈ schA F _, eX (e₀ Φ) = c • e Φ) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∫ u in 𝓕, tm B M om H' e₀ (vecMulVec H.x H'.y) Φ u ∂μ = C * c * thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) Φ)) := by
  have := countable_E (E := E)
  have hψ := hp.base.std
  have hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ := fun u hu Φ hΦ =>
    smul_right_injective _ hc (by simp only [← hce _ hΦ, ← hce _ (om_mem hp _ hΦ), hi₀ u hu Φ hΦ])
  have hs : ∀ u, HasSum (fun w => C * c * tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ u)
      (tm B M om H' e₀ (vecMulVec H.x H'.y) Φ u) := fun u => by
    have h1 := rho_mem M hψ (incM F (vecMulVec H.x H'.y)) (om_mem hp (1, u.1) hΦ)
    convert hC _ (he₀.maps _ h1) using 2 with w
    rw [← he₀.Heisenberg₂ _ _ h1, hce _ (rho_mem M hψ _ h1), theta_smul, vR_apply, incM_vv, ← mid_vv, incM_vv,
      rho_rho_of _ _ _ _ (sy_of_hT (by rw [hT_vv, h'.ad.iy, mul_zero])), tm, vA_apply, incM_add, incM_vv, incM_vv, inc_mulVec, add_comm,
      mul_assoc]
    rfl
  have := hm.sum (f := fun w u => C * c * tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ u) (fun w => continuous_const.mul (tm_cont hA hp hM₂ he _ hΦ)) (hs 1).summable.norm (fun w u => by
    rw [tA_eig hp h' he hi w hΦ u, norm_mul, norm_mul, norm_mul, std_norm hψ, one_mul, norm_mul (C * c), norm_mul C]) hs
  refine this.unique ?_
  convert hasSum_single (0 : Fin d₁ → E) fun w hw => ?_ using 1
  · rw [← hm.const (_ * _ * _)]
    congr 1
    funext u
    rw [tm_eq hp hi _ hΦ, vA_apply, Matrix.mulVec_zero, vv0, add_zero, incM_vv, vv_mul_r, shiftA, Units.val_one, one_smul]
    obtain ⟨a, z, e1⟩ := unip_y h' (inv_mem u.2)
    rw [e1, Matrix.vecMulVec_add, ev_I hψ he ⟨a • incV F H.x, z, by
      rw [Matrix.vecMulVec_add, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΦ,
      sy_of_hT (by rw [hT_vv, h.ad.xx, zero_mul]), mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  · rw [integral_const_mul, tA_zero hm hp h h' he hi hw hΦ, mul_zero]

theorem split_sum {ι : Type} [Zero ι] {g : ι → ℂ} {S : ℂ} (h : HasSum g S) (p : ι → Prop) (h0 : ∀ x, ¬ p x → g x = 0) :
    HasSum (fun x : {x // x ≠ 0 ∧ p x} => g x) (S - g 0) := by
  classical
  have h1 := h.update 0 0
  rw [← hasSum_subtype_iff_of_support_subset (s := {x | x ≠ 0 ∧ p x}) fun x hx => by
    have : x ≠ 0 := by rintro rfl; simp at hx
    exact ⟨this, by by_contra hp; exact hx (by rw [Function.update_of_ne this, h0 x hp])⟩] at h1
  rw [show S - g 0 = 0 - g 0 + S by ring, show (fun x : {x // x ≠ 0 ∧ p x} => g x) = Function.update g 0 0 ∘ Subtype.val from
    funext fun x => (Function.update_of_ne x.2.1 _ _).symm]
  exact h1

end PositivityTheory.ThKCT.Ker

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow Ker

theorem ctKernel_of (hE : ThetaExp) (hQ : EvUniq) (hS : Slice) (hA : EvAdm) (hW : MixW) (hX : MixX) (hT : ThetaBasic) (hP : PairEx)
    (hL : Low) (hU : UnipEx) (hG : GrpTop) (hO : EpsOf) : CTKernel := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀
  by_cases hex : ∃ χX χW om r s r' s', IsPair B M χX χW om r s r' s'
  swap
  · exact ⟨1, one_ne_zero, fun _ χX χW om r s r' s' hp => absurd ⟨χX, χW, om, r, s, r', s', hp⟩ hex,
      fun _ _ _ _ _ _ _ _ _ _ => ⟨1, one_ne_zero, fun _ _ χX χW om r s r' s' hp => absurd ⟨χX, χW, om, r, s, r', s', hp⟩ hex⟩⟩
  obtain ⟨χ₁, χ₂, om₀, r₀, s₀, r₀', s₀', hp₀⟩ := hex
  have hB := hp₀.base
  have h' := pg_skew hB hH' hp₀.skew
  obtain ⟨C₀, hC₀, hs₀⟩ := (pol0 (F := F) (herm_det hp₀.herm) h').exp hE hB hp₀.good hM₁ he₀
  have hi₀ : ∀ {χX χW om r s r' s'}, IsPair B M χX χW om r s r' s' →
      ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ := fun hp u hu Φ hΦ => by
    obtain ⟨om₁, hp₁⟩ := pair_low hP hL hp hH' hM₁
    rw [mix0 hW hp hH' hp₁ he₀ 1 hu hΦ, show ((1 : UA σ X.J), (1 : UA σ W₁.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have key : ∀ {χX χW om r s r' s'}, IsPair B M χX χW om r s r' s' → ∀ {μ 𝓕}, MeanOK σ W H' μ 𝓕 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g h,
      HasSum (fun x : IsoV σ X => C₀ * ∫ u in 𝓕, tm B M om H' e₀ (Matrix.vecMulVec x.1 H'.y) (om (g, h) Φ) u ∂μ)
        (∫ u in 𝓕, theta om Φ g (u.1 * h) ∂μ - C₀ * thetaSum F (e₀ (om (g, h) Φ))) := fun hp μ 𝓕 hm Φ hΦ g h => by
    have hΨ := om_mem hp (g, h) hΦ
    have := split_sum (sum0 hS hA hm hp h' hM₁ he₀ (hi₀ hp) hs₀ hΨ) (fun x => form σ X.J x x = 0) fun x hx => by
      rw [constant_term_anisotropic_integral_zero hm hp h' hM₁ he₀ (hi₀ hp) hx hΨ, mul_zero]
    simp only [constant_term_integral_at_zero hm (hi₀ hp) hΨ, om_om, Prod.mk_mul_mk, one_mul] at this
    exact this
  refine ⟨C₀, hC₀, fun han χX χW om r s r' s' hp Φ hΦ g μ 𝓕 a b c h => ?_, fun n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he => ?_⟩
  · haveI : IsEmpty (IsoV σ X) := ⟨fun x => x.2.1 (han _ x.2.2)⟩
    exact (sub_eq_zero.1 ((key hp (meanOK hU hG hO hp hH' a b c) Φ hΦ g h).unique hasSum_empty)).symm
  have h := pg_herm hB hH hp₀.herm
  obtain ⟨om₁, hp₁⟩ := pair_low hP hL hp₀ hH' hM₁
  obtain ⟨om₂, hp₂⟩ := (hP F E σ B hB n₁ d₁ X₁ W₁ _ _ _ _ ((hL F E σ B n n₁ X X₁ H j₀ j₁ r₀ s₀ hB hH).1 hp₀.herm).2.2 hp₁.skew).2 χ₁ χ₂
    hp₀.hX hp₀.hW (res_low hp₀.resX hH.rank) hp₁.resW M₂ hM₂
  obtain ⟨eX, heX⟩ := (hX F E σ B n d₁ X W₁ M₁ χ₁ χ₂ om₁ _ _ _ _ hp₁ n₁ X₁ H j₀ j₁ M₂ om₂ _ _ hH hp₂).1
  have hPX := polX (F := F) h (skew_det hp₁.skew)
  obtain ⟨C, hC, hsX⟩ := hPX.exp hE hB hM₁ hM₂ heX
  have he' := isEv_sumA hB.std h' he
  have hcomp := isEv_comp hB.std hp₀.good hM₁ hM₂ he₀ heX (comp_ne hPX hE hB hp₀.good hM₁ hM₂ he₀ heX) (K := isoA H H') (by
    rintro u (hu | ⟨z, rfl⟩)
    exacts [Or.inl hu, Or.inr ⟨_, ⟨z, rfl⟩, mid_vv _ _⟩])
  rw [Matrix.one_mul, Matrix.mul_one] at hcomp
  obtain ⟨c, hc, hce⟩ := (polA h h').uniq hQ hB hp₀.good hM₂ he' (isEv_sumA hB.std h' hcomp)
  refine ⟨C₀ * (C * c), mul_ne_zero hC₀ (mul_ne_zero hC hc), fun γ hγ χX χW om r s r' s' hp Φ hΦ g => ?_⟩
  have key2 : ∀ {μ 𝓕}, MeanOK σ W H' μ 𝓕 → ∀ k, HasSum
      (fun x => C₀ * (C * c) * thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, k) Φ))))
      (∫ u in 𝓕, theta om Φ g (u.1 * k) ∂μ - C₀ * thetaSum F (e₀ (om (g, k) Φ))) := fun hm k => by
    obtain ⟨om₁, hp₁⟩ := pair_low hP hL hp hH' hM₁
    convert key hp hm Φ hΦ g k using 2 with x
    simp only [constant_term_rational_translate hW hT hp hH' hp₁ he₀ (hγ x).1 (hγ x).2 (om_mem hp _ hΦ), om_om, Prod.mk_mul_mk, one_mul]
    rw [constant_term_cone_integral_eq hA hm hp h h' hM₂ he₀ he' (hi₀ hp) hc hsX hce (om_mem hp _ hΦ), mul_assoc]
  refine ⟨fun k => ?_, fun μ 𝓕 a b c' k => ?_⟩
  · obtain ⟨μ, 𝓕, a, b, c'⟩ := (hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hB (Or.inr hp.skew) hH').1
    exact (summable_mul_left_iff (mul_ne_zero hC₀ (mul_ne_zero hC hc))).1 (key2 (meanOK hU hG hO hp hH' a b c') k).summable
  · beta_reduce
    rw [← tsum_mul_left, (key2 (meanOK hU hG hO hp hH' a b c') k).tsum_eq, add_sub_cancel]

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SoStab
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_map (B : Base F E) (w : InfinitePlace F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : (J.map (B.emb w).1).det ≠ 0) : J.det ≠ 0 := fun h0 =>
  hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))

theorem det_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w))

theorem det_skew {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

theorem _root_.PositivityTheory.ThKCT.soStab_of : SoStab := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP x
  exact PositivityTheory.KCo.so_stable M hP.base.cm hP.base.std (det_herm hP.herm) (det_skew hP.skew) hP.good
    (IsUWeilPair.isUSplitting hP.weil).toIsSplitting B.τ₁ x

end PositivityTheory.ThKCT.So

end
end

