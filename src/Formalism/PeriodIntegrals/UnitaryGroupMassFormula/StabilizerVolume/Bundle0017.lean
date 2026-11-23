module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FinTheta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnimodStab

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCore
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

def GramFilt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (b : Module.Basis (Fin d) F E)
      (x : Fin a → Fin M → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) x →
      ∃ N ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E), ∀ y, y - x ∈ N →
        ∀ Λ0, scaledB (Fv F v) (latSub b v a M) Λ0 →
          (Λ0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ⊆ N →
        ∃ (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
          (H : ℕ → AddSubgroup (HermR (Fv F v) σ a))
          (D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a),
          Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
          (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
          (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
          (∀ n, (Λ n).map D = H n) ∧
          ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ hσ J hJ (y + Z + W) - gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈
              H (n + 1)

theorem densVLat_of (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensVLat := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, t3, _t4, t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  intro d b x hx
  obtain ⟨N, hN, hd⟩ := hF F E σ hσ M J hJ.1 hJ.2 a h1 (by omega) v d b x hx
  refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
  subst h0
  exact densCos_of_filt hP1 hP2 μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (Continuous.subtype_mk t5 _) (fun _ => rfl) y Λ H hΛo hΛc hΛa
    hHo hHc hHb D hD hyp

theorem densV_of_filt (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensV :=
  densV_of_lat hT (densVLat_of hP1 hP2 hT hF)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDxSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

def DxOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ)
      (b : Module.Basis (Fin d) F E) (x : Fin a → Fin M → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) x →
      IsOpen ((fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) '' (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E)))

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibUniq
section
noncomputable section

namespace PI.VolStabS.FibUniq

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}

theorem integral_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  have c1 := (h1.2.2 φ hφc hφs hφU).2
  have c2 := (h2.2.2 φ hφc hφs hφU).2
  have h0 : ∀ S, IsCompact S → S ⊆ univ →
      ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0 := by
    intro S hS _
    rw [integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS)
      ((c2.mono (subset_univ S)).integrableOn_compact hS),
      ← PI.VolStabS.DensGen.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S),
      ← PI.VolStabS.DensGen.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_self]
  exact sub_eq_zero.1 (PI.VolStabS.DensGen.eq_zero_of_setIntegral (ν := ν)
    (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)

theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, _⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := PI.VolStabS.DiscreteGroups.approx O hO
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have key : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib →
      fib b O = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
    intro fib hf
    calc fib b O = ∫⁻ v, O.indicator 1 v ∂(fib b) :=
          (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_congr fun v => (hlim v).symm
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_iSup hmeas hmon
      _ = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
          congr 1
          funext k
          exact (ofReal_integral_eq_lintegral_ofReal
            ((hf.2.2 _ (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU)).1 b (mem_univ b))
            (ae_of_all _ fun v => (h01 k v).1)).symm
  rw [key fib1 h1, key fib2 h2]
  congr 1
  funext k
  rw [integral_eq h1 h2 hf' hff' hι (φ k) (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU) b]

theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 := by
  funext b
  obtain ⟨W, hW, hWU⟩ := PI.VolStabS.DiscreteGroups.cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hnull : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → fib b Uᶜ = 0 :=
    fun fib hf => measure_mono_null (compl_subset_compl.2 inter_subset_right) (hf.1 b)
  have hfin : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → ∀ n, fib b (W n) ≠ ⊤ :=
    fun fib hf n => (lt_of_le_of_lt (measure_mono subset_closure)
      (fin_cpt hf hU b _ (hW n).2.1 (hW n).2.2)).ne
  let s : Option ℕ → Set V := fun o => o.elim Uᶜ W
  have hs : ⋃ o, s o = univ := by
    rw [iUnion_option]
    simp only [s, Option.elim_none, Option.elim_some]
    rw [hWU, compl_union_self]
  refine (Measure.ext_iff_of_iUnion_eq_univ hs).2 fun o => ?_
  cases o with
  | none =>
    simp only [s, Option.elim_none]
    rw [Measure.restrict_eq_zero.2 (hnull fib1 h1), Measure.restrict_eq_zero.2 (hnull fib2 h2)]
  | some n =>
    simp only [s, Option.elim_some]
    have : IsFiniteMeasure ((fib1 b).restrict (W n)) :=
      isFiniteMeasure_restrict.2 (hfin fib1 h1 n)
    refine ext_of_generate_finite {t : Set V | IsOpen t} (BorelSpace.measurable_eq.trans rfl)
      isPiSystem_isOpen (fun t ht => ?_) ?_
    · rw [Measure.restrict_apply ht.measurableSet, Measure.restrict_apply ht.measurableSet]
      exact open_eq h1 h2 hf' hff' hι _ (ht.inter (hW n).1) (inter_subset_right.trans (hWsub n)) b
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact open_eq h1 h2 hf' hff' hι _ (hW n).1 (hWsub n) b

end Gen

section Tens

open scoped TensorProduct
open PI.VolStabS PI.VolStabS.TensAllW

theorem fib_eq_tens {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib1 fib2 : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h1 : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib1)
    (h2 : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib2) : fib1 = fib2 :=
  fib_eq h1 h2 (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective
    (isOpen_linIndep (Module.finBasis F E) R hU hL)

end Tens

end PI.VolStabS.FibUniq
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHC
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ) :
    AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
    ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [AddSubgroup.coe_add, Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j k
    simp only [ZeroMemClass.coe_zero, Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [NegMemClass.coe_neg, Matrix.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

def VolAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
      (∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv → μv (latV b v) = 1) ∧
      (∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv → νv (hermO b v σ a) = 1)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def RPAbs : Prop :=
  ∀ (ι : Type) [Countable ι] (W : ι → Type) [∀ i, MeasurableSpace (W i)]
    (m : ∀ i, Measure (W i)) [∀ i, SigmaFinite (m i)] (L : ∀ i, Set (W i)),
    (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ⊤) →
    (∀ S : Finset ι, ∃ c : ENNReal, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c) →
    ∃ ρ : Measure (∀ i, W i), SFinite ρ ∧
      ρ {x | ¬ ∀ᶠ i in Filter.cofinite, x i ∈ L i} = 0 ∧
      (∀ i (C : Set (W i)), MeasurableSet C → m i Cᶜ = 0 → ρ {x | x i ∉ C} = 0) ∧
      ∀ f : ∀ i, W i → ℂ, (∀ i, Integrable (f i) (m i)) →
        (∀ᶠ i in Filter.cofinite, f i = (L i).indicator 1) →
        Integrable (fun x => ∏ᶠ i, f i (x i)) ρ ∧
        HasProd (fun i => ∫ w, f i w ∂(m i)) (∫ x, ∏ᶠ i, f i (x i) ∂ρ)

def RPFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
      (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E)),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Ainf F) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
      (fib : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Fv F v) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Fv F v) σ (gramE σ J X0) hT))

def RPGlue : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M a d : ℕ) (b : Module.Basis (Fin d) F E),
  ∃ Γ : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) →
      (Fin a → Fin M → AF F ⊗[F] E),
    Measurable Γ ∧ ∀ p, (∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v) →
      projInf (Γ p) = p.1 ∧ ∀ v, projV v (projFin (Γ p)) = p.2 v

def RPGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
  MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} ∧
  MeasurableSet {X : Fin a → Fin M → Ainf F ⊗[F] E |
    gramR (Ainf F) σ J X = T.map (inclR (Ainf F))} ∧
  (∀ v : HeightOneSpectrum (𝓞 F), MeasurableSet {X : Fin a → Fin M → Fv F v ⊗[F] E |
    gramR (Fv F v) σ J X = T.map (inclR (Fv F v))}) ∧
  ∀ X : Fin a → Fin M → AF F ⊗[F] E, gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) →
    (∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) →
    gramR (AF F) σ J X = T.map (inclR (AF F))

def RPTail : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a →
      Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (d : ℕ) (b : Module.Basis (Fin d) F E),
    (∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) →
    (∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ →
      ∫ X, Φ X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} =>
        fibV v.1 (hermOf (Fv F v.1) σ (gramE σ J X0) hT) (latV b v.1)) c

def LatCofin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a M d d' : ℕ)
    (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E),
    ∀ᶠ v in Filter.cofinite, latV (M := M) (n := a) b v = latV b' v

theorem restrProd_of (hA : RPAbs) (hF : RPFib) (hG : RPGlue) (hGr : RPGram) (hTl : RPTail)
    (hL : LatCofin) : RestrProd := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμi νinf hνi μv hμv νv hνv
    fibInf hfi fibV hfv hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have cF := hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨hsfI, hintI⟩ := cF.1 μinf νinf fibInf hfi
  have hFv := fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)
  have hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    fun v Φ h => (hFv v).2 Φ h.1.continuous h.2
  let b := Module.finBasis F E
  rcases hTl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV _ b hSB (hmult _ b) with
    ⟨v0, hv0⟩ | hconv
  · refine ⟨0, by simp, fun d' b' Φ Φinf Φf Φv _ _ hp _ => ⟨integrable_zero_measure, ?_⟩⟩
    have h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0 :=
      hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩
    rw [integral_zero_measure, h0.tprod_eq, mul_zero]
  · let W : HeightOneSpectrum (𝓞 F) → Type := fun v => Fin a → Fin M → Fv F v ⊗[F] E
    let m : ∀ v, Measure (W v) := fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)
    have : ∀ v, SigmaFinite (m v) := fun v => (hFv v).1
    have := hsfI
    have hLm : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
    have hLf : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
      have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
      rw [integrable_indicator_iff (hLm v)] at h
      exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
    obtain ⟨ρ, hρsf, hρgood, hρmarg, hρint⟩ :=
      hA (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv
    have := hρsf
    obtain ⟨Γ, hΓm, hΓ⟩ := hG F E M a _ b
    have cG := hGr F E σ M J a (gramE σ J X0)
    let P : Measure ((Fin a → Fin M → Ainf F ⊗[F] E) × ∀ v, W v) :=
      (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)).prod ρ
    have hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0 := by
      rw [Measure.prod_prod, hρgood, mul_zero]
    refine ⟨P.map Γ, ?_, ?_⟩
    · rw [Measure.map_apply hΓm cG.1]
      have h1 : (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
          {y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) (hfi.1 _)
      have h2 : ∀ v, m v {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        fun v => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hfv v).1 _)
      have hbad : Γ ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} ⊆
          ({y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) ∪
            ⋃ v, Set.univ ×ˢ {x : ∀ v, W v | x v ∉
              {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}}) := by
        intro p hp
        by_contra hn
        have hi : gramR (Ainf F) σ J p.1 = (gramE σ J X0).map (inclR (Ainf F)) := by
          by_contra h; exact hn (Or.inl ⟨h, Set.mem_univ _⟩)
        have hg : ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
          by_contra h; exact hn (Or.inr (Or.inl ⟨Set.mem_univ _, h⟩))
        have hv : ∀ v, gramR (Fv F v) σ J (p.2 v) = (gramE σ J X0).map (inclR (Fv F v)) := by
          intro v; by_contra h
          exact hn (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_univ _, h⟩)))
        obtain ⟨e1, e2⟩ := hΓ p hg
        apply hp
        apply cG.2.2.2 (Γ p)
        · rw [e1]; exact hi
        · intro v; rw [e2 v]; exact hv v
      refine measure_mono_null hbad (measure_union_null ?_ (measure_union_null hgood
        (measure_iUnion_null fun v => ?_)))
      · rw [Measure.prod_prod, h1, zero_mul]
      · rw [Measure.prod_prod, hρmarg v _ (cG.2.2.1 v) (h2 v), mul_zero]
    · intro d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have hΦm : Measurable Φ :=
        TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      have hf : ∀ v, Integrable (Φv v) (m v) := fun v => hSB v _ (hp.1 v)
      have hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 :=
        (hp.2.1.and (hL F E a M d' _ b' b)).mono fun v h => h.1.trans (by rw [h.2])
      obtain ⟨hIρ, hHP⟩ := hρint Φv hf hfc
      have hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
        rw [ae_iff]
        exact measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood
      have hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v) := by
        filter_upwards [hae'] with p hp'
        obtain ⟨e1, e2⟩ := hΓ p hp'
        rw [hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]
        congr 1
        exact finprod_congr fun v => by rw [e2 v]
      have hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P :=
        (hintI Φinf hc1 hc2).mul_prod hIρ
      refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2
        (hPI.congr hae.symm), ?_⟩
      rw [integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae,
        integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)),
        ← hHP.tprod_eq]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldFin
section
namespace PI.VolStabS

theorem unfold_holds : Unfold :=
  unfold_of witt_holds finTheta_holds invInv_holds measOrb_holds measGrp_holds

end PI.VolStabS
end

