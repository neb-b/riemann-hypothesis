module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unfold

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfLoc
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def LinDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A →
      DensAll μ A id ν Set.univ

def ChangeVar : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)), μ.IsAddHaarMeasure →
    ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) →
      ∃ N, IsOpen N ∧ x0 ∈ N ∧ ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A ∧
        ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ N →
          ∃ G : (Fin n → ℝ) → ℝ, Continuous G ∧ HasCompactSupport G ∧
            ∀ S : Set (Fin m → ℝ), IsCompact S →
              ∫ v in f ⁻¹' S, φ v ∂μ = ∫ v in A ⁻¹' S, G v ∂μ

theorem submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by
  intro n m μ ν hμ hν f hf x0 hx0
  obtain ⟨N, hN, hxN, A, hA, hG⟩ := h2 n m μ hμ f hf x0 hx0
  refine ⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩
  obtain ⟨G, hGc, hGs, hGe⟩ := hG φ hc hs hφ
  obtain ⟨g, hgc, hg⟩ := h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)
  refine ⟨g, hgc, fun S hS => ?_⟩
  have := hg S hS
  simp only [Set.image_id] at this ⊢
  rw [hGe S hS, this]

theorem submDens_of_local (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx

theorem linDens_holds : LinDens := by
  intro n m μ ν hμ hν A hA φ hc hs _
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  let K := A.ker
  let lam : Measure K := Measure.addHaar
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let H : (Fin m → ℝ) × K → ℝ := fun w => φ (T.symm w)
  have hHc : Continuous H := hc.comp T.symm.continuous
  have hHs : HasCompactSupport H := hs.comp_homeomorph T.symm.toHomeomorph
  let s : Set K := Prod.snd '' tsupport H
  have hsc : IsCompact s := hHs.image continuous_snd
  let ψ : (Fin m → ℝ) → ℝ := fun y => ∫ k in s, H (y, k) ∂lam
  have hψc : Continuous ψ :=
    continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc
  have hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    apply image_eq_zero_of_notMem_tsupport
    intro h'
    exact hk ⟨(y, k), h', rfl⟩
  refine ⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  simp only [Set.image_id]
  let Q : (Fin m → ℝ) × K → ℝ := (Prod.fst ⁻¹' S).indicator H
  have hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v) := by
    intro v
    simp only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hQi : Integrable Q (ν.prod lam) :=
    (hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)
  rw [← integral_indicator (hSm.preimage A.continuous.measurable)]
  simp_rw [hQ]
  have e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T) := by
    rw [show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
    rfl
  rw [e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul,
    ← integral_indicator hSm, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · simp only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]
  · simp [Q, Set.indicator, hy]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolA
section
noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_one_of_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) (hA : ann χ (L : Set V) = L) :
    μ (L : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hLo.measurableSet]
    exact integrableOn_const hfin.ne
  have h0 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0) := by
    funext y
    rw [hT y]
    by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]
  rw [e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h0
  have h1 : c * c = 1 := by exact_mod_cast h0
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c = 1 := by nlinarith
  rw [hc, measureReal_def, ENNReal.toReal_eq_one_iff] at hc1
  exact hc1

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq {V : Type} (ψ0 : Fv F v → ℂ) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y)
    (hD : {y | ∀ x ∈ L, B x y ∈ v.adicCompletionIntegers F} = L) :
    ann (fun x y => ψ0 (B x y)) L = L := by
  ext y
  constructor
  · intro hy
    rw [← hD]
    intro x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy
    rw [← hD] at hy
    intro x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

theorem ev_int (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) f ∈ (v.adicCompletionIntegers F) := by
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) f
  refine hfin.eventually_cofinite_notMem.mono fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v ((f : v.adicCompletion F)) = v.valuation F f :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  exact (this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)

theorem ev_int_all {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) :=
  Filter.eventually_all.2 fun i => ev_int (f i)

end Ann

end VolAAW

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoClose
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem lcscPolish_holds : LCSCPolish := fun Y _ _ _ _ => TopoPolish.polish_of_lcsc Y

theorem secCtblW_holds : SecCtblW := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem scha_holds : SCHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem measGrp_holds : MeasGrp := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ⟨inferInstance, inferInstance⟩

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldMain
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gram_orbit_equiv {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩

end Main

section Of

theorem unfold_of (hW : Witt) (hFT : FinTheta) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) :
    Unfold := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C
    𝓕' h𝓕' φ hφ0 hadm hθ
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ'.IsHaarMeasure := hμ'H
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : μ'.IsInvInvariant :=
    (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : (GamA σ J) =>
        (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J)
      (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hint : Integrable (fun X => (φ X : ℂ)) νX := by
    obtain ⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩ := id hadm
    obtain ⟨⟨μinf, hμinf⟩, k1⟩ := hν.2
    obtain ⟨⟨νinf, hνinf⟩, k2⟩ := k1 μinf hμinf
    obtain ⟨⟨μv, hμv⟩, k3⟩ := k2 νinf hνinf
    obtain ⟨⟨νv, hνv⟩, k4⟩ := k3 μv hμv
    obtain ⟨⟨fI, hfI⟩, k5⟩ := k4 νv hνv
    obtain ⟨⟨fV, hfV⟩, k6⟩ := k5 fI hfI
    exact (k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1
  have hφae : AEMeasurable φ νX := by
    have h2 := Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX
      (fun X => ENNReal.ofReal (φ X)) hφae.ennreal_ofReal hmφ.ennreal_ofReal hμ'C.1 hμ'C.2 𝓕 h𝓕 𝓕' h𝓕'
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by
    intro h
    have hF := hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h
    rw [hθS h]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_hasFiniteSupport ?_)
    refine (hF.preimage Subtype.val_injective.injOn).subset ?_
    intro X hX
    simp only [Function.mem_support] at hX
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Ne, Complex.ofReal_eq_zero]
    intro hz
    apply hX
    change φ (h⁻¹ • ratTup (AF F) (X : Fin a → Fin M → E)) = 0 at hz
    simp [hz]
  have hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by
    refine Measurable.tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal
          : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]
  have hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφae.aestronglyMeasurable]
  rw [hI1] at hθ ⊢
  rw [hI2, key]
  rw [key] at hθ
  have hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0 := fun h0 => hθ (by rw [h0]; simp)
  have hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0 := fun h => hL0 (by simp [h])
  have hμ'top : μ' 𝓕' ≠ ⊤ := fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)
  refine ⟨hμ'top, ?_⟩
  rw [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]

end Of

end PI.VolStabS
end
end

