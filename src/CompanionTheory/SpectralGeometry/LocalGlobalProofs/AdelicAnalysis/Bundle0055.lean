module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitsDecompositionFlowCompact
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Fujisaki

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

theorem isCompact_units_setOf {Ω W : Set K} (hΩ : IsCompact Ω) (hW : IsCompact W) :
    IsCompact {u : Kˣ | (u : K) ∈ Ω ∧ ((u⁻¹ : Kˣ) : K) ∈ W} := by
  have hc : IsCompact (Ω ×ˢ (MulOpposite.op '' W)) :=
    hΩ.prod (hW.image MulOpposite.continuous_op)
  have h := (Units.isClosedEmbedding_embedProduct (α := K)).isCompact_preimage hc
  convert h using 1
  ext u
  simp [Units.embedProduct]

def act (t : Kˣ) : (Fin 1 → Fin 1 → K) →+ (Fin 1 → Fin 1 → K) where
  toFun X := (t : K) • X
  map_zero' := smul_zero _
  map_add' := smul_add _

theorem continuous_act : Continuous fun p : Kˣ × (Fin 1 → Fin 1 → K) => act p.1 p.2 := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  have h1 : Continuous fun p : Kˣ × (Fin 1 → Fin 1 → K) => ((p.1 : Kˣ) : K) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun p : Kˣ × (Fin 1 → Fin 1 → K) => p.2 a i :=
    (continuous_apply i).comp ((continuous_apply a).comp continuous_snd)
  exact h1.mul h2

theorem chi_flow {V : Type} [TopologicalSpace V] [AddCommGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {c : ℝ≥0} {r : ℝ} (hr : 0 ≤ r)
    (h : c • μ = ENNReal.ofReal r • μ) : (c : ℝ) = r := by
  obtain ⟨Q, hQc, hQ⟩ := exists_compact_mem_nhds (0 : V)
  have h0 : μ Q ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hQ).ne'
  have h1 : μ Q ≠ ⊤ := hQc.measure_lt_top.ne
  have h2 : (c : ℝ≥0∞) * μ Q = ENNReal.ofReal r * μ Q := by
    have := congrArg (fun m : Measure V => m Q) h
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact this
  have h3 : (c : ℝ≥0∞) = ENNReal.ofReal r := (ENNReal.mul_left_inj h0 h1).1 h2
  have h4 := congrArg ENNReal.toReal h3
  rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal hr] at h4

theorem core {E : Type} [Field E] [Countable E] [LocallyCompactSpace K] [SecondCountableTopology K]
    (ι : E →+* K) [MeasurableSpace (Fin 1 → Fin 1 → K)] [BorelSpace (Fin 1 → Fin 1 → K)]
    (μ : Measure (Fin 1 → Fin 1 → K)) [μ.IsAddHaarMeasure] (hinf : μ Set.univ = ⊤)
    (hcov : ∃ C : Set (Fin 1 → Fin 1 → K), IsCompact C ∧
      ∀ y, ∃ X : Fin 1 → Fin 1 → E, y - (fun a i => ι (X a i)) ∈ C)
    (hfin : ∀ C : Set (Fin 1 → Fin 1 → K), IsCompact C →
      {X : Fin 1 → Fin 1 → E | (fun a i => ι (X a i)) ∈ C}.Finite)
    (τ : Multiplicative ℝ →* Kˣ) (hτ : Continuous τ) (D : ℝ) (hD : 0 < D)
    (hflow : ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd x) : Kˣ) : K) • X) =
      ENNReal.ofReal (Real.exp (-(D * x))) • μ) :
    ∃ ω : Set Kˣ, IsCompact ω ∧ ∀ a : Kˣ, ∃ (l : Eˣ) (a' c : Kˣ) (j : ℤ),
      (a' : K) = ι (l : E) ∧ c ∈ ω ∧ a = a' * τ (Multiplicative.ofAdd (j : ℝ)) * c := by
  obtain ⟨C, hCc, hC⟩ := hcov
  haveI : LocallyCompactSpace Kˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology Kᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := K)).symm.secondCountableTopology
  haveI : SecondCountableTopology Kˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  obtain ⟨χ, -, hχ⟩ := _root_.GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus (Fin 1 → Fin 1 → K) μ Kˣ act continuous_act continuous_inv
    (fun y => by simp [act]) (fun s t y => by simp [act, mul_smul])
  let jj : (Fin 1 → Fin 1 → E) →+ (Fin 1 → Fin 1 → K) :=
    { toFun := fun X a i => ι (X a i)
      map_zero' := by ext a i; simp
      map_add' := fun X Y => by ext a i; simp }
  obtain ⟨ΩV, hΩc, hΩ⟩ := _root_.GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving (Fin 1 → Fin 1 → K) μ hinf (Fin 1 → Fin 1 → E) jj C hCc hC

  set Ω : Set K := (fun Y : Fin 1 → Fin 1 → K => Y 0 0) '' ΩV with hΩdef
  have hΩK : IsCompact Ω :=
    hΩc.image ((continuous_apply 0).comp (continuous_apply 0))
  have hΩ2 : IsCompact (Ω * Ω) := hΩK.mul hΩK
  have hconst : Continuous fun k : K => (fun _ _ => k : Fin 1 → Fin 1 → K) :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_id
  have hS := hfin _ (hΩ2.image hconst)
  set Z : Set E := (fun X : Fin 1 → Fin 1 → E => X 0 0) '' {X : Fin 1 → Fin 1 → E |
    (fun a i => ι (X a i)) ∈ (fun k : K => (fun _ _ => k : Fin 1 → Fin 1 → K)) '' (Ω * Ω)} with hZdef
  have hZ : Z.Finite := hS.image _
  set Zi : Set K := (fun z : E => ι z⁻¹) '' Z with hZidef
  have hZi : IsCompact Zi := (hZ.image _).isCompact
  have hW : IsCompact (Zi * Ω) := hZi.mul hΩK
  have hω₀ := isCompact_units_setOf hΩK hW
  set T₀ : Set Kˣ := (fun r : ℝ => τ (Multiplicative.ofAdd r)) '' Set.Icc 0 1 with hT₀
  have hT₀c : IsCompact T₀ := isCompact_Icc.image
    (hτ.comp continuous_ofAdd)
  refine ⟨T₀ * {u : Kˣ | (u : K) ∈ Ω ∧ ((u⁻¹ : Kˣ) : K) ∈ Zi * Ω}, hT₀c.mul hω₀, fun a => ?_⟩

  have hτχ : ∀ x : ℝ, ((χ (τ (Multiplicative.ofAdd x)) : ℝ≥0) : ℝ) = Real.exp (-(D * x)) := by
    intro x
    refine chi_flow μ (Real.exp_pos _).le ?_
    rw [← hχ, ← hflow x]
    rfl
  have hχa : χ a ≠ 0 := by
    intro h
    have := map_mul χ a a⁻¹
    simp [h] at this
  set x : ℝ := -Real.log (χ a : ℝ) / D with hx
  set a₁ : Kˣ := a * τ (Multiplicative.ofAdd (-x)) with ha₁
  have hχ₁ : χ a₁ = 1 := by
    apply NNReal.coe_injective
    have hpos : 0 < (χ a : ℝ) := by exact_mod_cast pos_iff_ne_zero.2 hχa
    rw [ha₁, map_mul, NNReal.coe_mul, hτχ]
    have : -(D * -x) = -Real.log (χ a : ℝ) := by rw [hx]; field_simp
    rw [this, Real.exp_neg, Real.exp_log hpos]
    simp [hpos.ne']
  have hχ₂ : χ a₁⁻¹ = 1 := by rw [map_inv, hχ₁, inv_one]
  have hm₁ : μ.map (act a₁) = μ := by rw [hχ, hχ₁, one_smul]
  have hm₂ : μ.map (act a₁⁻¹) = μ := by rw [hχ, hχ₂, one_smul]
  have hcont : ∀ t : Kˣ, Continuous (act t) := fun t =>
    continuous_act.comp (continuous_const.prodMk continuous_id)
  obtain ⟨X, hX0, hX⟩ := hΩ (act a₁) (hcont _) hm₁
  obtain ⟨X', hX'0, hX'⟩ := hΩ (act a₁⁻¹) (hcont _) hm₂
  have hne : ∀ Y : Fin 1 → Fin 1 → E, Y ≠ 0 → Y 0 0 ≠ 0 := by
    intro Y hY h
    apply hY
    ext a i
    rw [Subsingleton.elim a 0, Subsingleton.elim i 0]
    simpa using h
  set l : E := X 0 0 with hl
  set l' : E := X' 0 0 with hl'
  have hl0 : l ≠ 0 := hne _ hX0
  have hl'0 : l' ≠ 0 := hne _ hX'0
  have h1 : (a₁ : K) * ι l ∈ Ω := ⟨_, hX, rfl⟩
  have h2 : ((a₁⁻¹ : Kˣ) : K) * ι l' ∈ Ω := ⟨_, hX', rfl⟩
  have hll : ι (l * l') ∈ Ω * Ω := by
    refine ⟨_, h1, _, h2, ?_⟩
    show (a₁ : K) * ι l * (((a₁⁻¹ : Kˣ) : K) * ι l') = ι (l * l')
    have hu : (a₁ : K) * ((a₁⁻¹ : Kˣ) : K) = 1 := Units.mul_inv_of_eq rfl
    calc (a₁ : K) * ι l * (((a₁⁻¹ : Kˣ) : K) * ι l')
        = ((a₁ : K) * ((a₁⁻¹ : Kˣ) : K)) * (ι l * ι l') := by ring
      _ = ι (l * l') := by rw [hu, one_mul, map_mul]
  have hz : l * l' ∈ Z := by
    refine ⟨fun _ _ => l * l', ⟨_, hll, rfl⟩, rfl⟩
  let lU : Eˣ := Units.mk0 l hl0
  let m : Kˣ := Units.map ι.toMonoidHom lU
  have hm : (m : K) = ι l := rfl
  have hmi : ((m⁻¹ : Kˣ) : K) = ι l⁻¹ := by
    show ι.toMonoidHom ((lU⁻¹ : Eˣ) : E) = _
    simp [lU]
  have hu1 : ((a₁ * m : Kˣ) : K) ∈ Ω := by simpa [hm] using h1
  have hu2 : (((a₁ * m)⁻¹ : Kˣ) : K) ∈ Zi * Ω := by
    refine ⟨ι (l * l')⁻¹, ⟨_, hz, rfl⟩, _, h2, ?_⟩
    show ι (l * l')⁻¹ * (((a₁⁻¹ : Kˣ) : K) * ι l') = _
    have e : ((a₁ * m)⁻¹ : Kˣ) = a₁⁻¹ * m⁻¹ := mul_inv _ _
    have ez : (l * l')⁻¹ = l'⁻¹ * l⁻¹ := mul_inv_rev _ _
    have : ι l'⁻¹ * ι l' = 1 := by rw [← map_mul, inv_mul_cancel₀ hl'0, map_one]
    rw [e, Units.val_mul, hmi, ez, map_mul]
    calc ι l'⁻¹ * ι l⁻¹ * (((a₁⁻¹ : Kˣ) : K) * ι l')
        = (ι l'⁻¹ * ι l') * (((a₁⁻¹ : Kˣ) : K) * ι l⁻¹) := by ring
      _ = _ := by rw [this, one_mul, mul_comm]
  have hfr : x - (⌊x⌋ : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.2 (Int.floor_le x), (sub_le_iff_le_add').2 (Int.lt_floor_add_one x).le |>.trans' le_rfl⟩
  refine ⟨lU⁻¹, m⁻¹, τ (Multiplicative.ofAdd (x - (⌊x⌋ : ℝ))) * (a₁ * m), ⌊x⌋, ?_, ?_, ?_⟩
  · exact hmi.trans (by simp [lU])
  · exact ⟨_, ⟨_, hfr, rfl⟩, _, ⟨hu1, hu2⟩, rfl⟩
  · have hone : τ (Multiplicative.ofAdd ((⌊x⌋ : ℤ) : ℝ)) * τ (Multiplicative.ofAdd (x - (⌊x⌋ : ℝ))) *
        τ (Multiplicative.ofAdd (-x)) = 1 := by
      rw [← map_mul, ← map_mul, ← ofAdd_add, ← ofAdd_add]
      simp
    calc a = (m⁻¹ * m) * (a * (τ (Multiplicative.ofAdd ((⌊x⌋ : ℤ) : ℝ)) *
          τ (Multiplicative.ofAdd (x - (⌊x⌋ : ℝ))) * τ (Multiplicative.ofAdd (-x)))) := by
            rw [hone]; simp
      _ = _ := by rw [ha₁]; ac_rfl

end GlobalTheory.CompanionTheory.SW.Fujisaki

namespace GlobalTheory.CompanionTheory.SW.Fujisaki

theorem units_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ ω : Set (AF F ⊗[F] E)ˣ, IsCompact ω ∧ ∀ a : (AF F ⊗[F] E)ˣ, ∃ (l : Eˣ) (a' : (AF F ⊗[F] E)ˣ) (c : (AF F ⊗[F] E)ˣ) (j : ℤ), (a' : AF F ⊗[F] E) = inclR (AF F) (l : E) ∧ c ∈ ω ∧ a = a' * τ (Multiplicative.ofAdd (j : ℝ)) * c := by
  intro F E _ _ _ _ _ σ hσ τ hτ
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTR, hLCK, hSCK, hT2K, -, -, -, hBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hTR
  haveI := hLCK
  haveI := hSCK
  haveI := hT2K
  haveI : BorelSpace (Fin 1 → Fin 1 → AF F ⊗[F] E) := hBor 1 1
  haveI : Countable E :=
    ((Module.finBasis ℚ E).equivFun.toEquiv.injective).countable
  obtain ⟨hcov, hfin, hnc⟩ := _root_.GlobalTheory.CompanionTheory.SW.CocW.main F E σ hσ 1 1
  haveI := hnc one_pos one_pos
  have hinf : (Measure.addHaar : Measure (Fin 1 → Fin 1 → AF F ⊗[F] E)) Set.univ = ⊤ :=
    measure_univ_of_isAddLeftInvariant _
  have hD : (0 : ℝ) < 2 * Module.finrank ℚ F := by
    have : 0 < Module.finrank ℚ F := Module.finrank_pos
    positivity
  refine core (inclR (AF F)) Measure.addHaar hinf hcov hfin τ hτ.1 _ hD fun x => ?_
  have h := _root_.GlobalTheory.CompanionTheory.SW.Flow.modulus_flow F E σ hσ τ hτ 1 1 Measure.addHaar inferInstance x
  simpa using h

end GlobalTheory.CompanionTheory.SW.Fujisaki

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBounded
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatCount

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def ratHom (M : ℕ) : (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun := ratTup (AF F)
  map_zero' := by
    funext a i
    simp [ratTup]
  map_add' X Y := by
    funext a i
    simp [ratTup]

lemma box_mono {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

lemma sizeInf_nonneg {d : ℕ} (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma repr_projInf_ratTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf (ratTup (AF F) X) a i) k =
      algebraMap F (Ainf F) (b.repr (X a i) k) := by
  have : projInf (ratTup (AF F) X) a i = (1 : Ainf F) ⊗ₜ[F] X a i := by
    simp [projInf, ratTup, inclR]
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

lemma sizeTup_ratTup_pos {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (hX : X ≠ 0) : 0 < sizeTup b (projInf (ratTup (AF F) X)) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨k, hk⟩ : ∃ k, b.repr (X a i) k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi (b.repr.map_eq_zero_iff.mp (Finsupp.ext h))
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  set Y := projInf (ratTup (AF F) X : Fin n → Fin M → AF F ⊗[F] E) with hY
  have h1 : 0 < ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ := by
    rw [hY, repr_projInf_ratTup, norm_pos_iff]
    change algebraMap F v.Completion (b.repr (X a i) k) ≠ 0
    exact (map_ne_zero _).mpr hk
  have h2 : ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ ≤ sizeInf b (Y a i) :=
    (Finset.single_le_sum
      (f := fun v => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum
      (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have h3 : sizeInf b (Y a i) ≤ sizeTup b Y :=
    (Finset.single_le_sum (f := fun i => sizeInf b (Y a i))
      (fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (Y a i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ a))
  linarith

end SlopeTestRemainingChoices

lemma exists_pos_lt {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ S, r < f x :=
  _root_.Bl.FirstLemmaK.goal1 hS f hf

theorem count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M Ω hΩ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨hcpt, hexh, hflow⟩ := _root_.GlobalTheory.CompanionTheory.SW.BoxF.box_facts F E σ hCM _ b 1 M
  obtain ⟨-, hfin, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.CocW.main F E σ hCM 1 M
  obtain ⟨N, r, hN, hr, hsub⟩ := hexh Ω hΩ

  obtain ⟨r₀, h0, h1, hsmall⟩ := exists_pos_lt
    (((hfin _ (hcpt N 1 hN)).subset (Set.inter_subset_left
      (t := {X : Fin 1 → Fin M → E | X ≠ 0}))))
    (fun X => sizeTup b (projInf (ratTup (AF F) X)))
    (fun X hX => sizeTup_ratTup_pos b X hX.2)
  have hnone : ∀ X : Fin 1 → Fin M → E, X ≠ 0 → ratTup (AF F) X ∉ box b N r₀ := by
    intro X hX hmem
    have := hsmall X ⟨box_mono b N h1 hmem, hX⟩
    exact absurd hmem.2 (not_le.mpr this)
  have hscale : ∀ (x : ℝ) (Y : Fin 1 → Fin M → AF F ⊗[F] E),
      ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ Ω →
        Y ∈ box b N (Real.exp x * r) := by
    intro x Y hY
    refine (hflow τ hτ N (Real.exp x * r) (-x) Y).mp ?_
    have : Real.exp (-x) * (Real.exp x * r) = r := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact hsub hY
  refine ⟨Real.log (r₀ / r), (5 * r / r₀) ^ (2 * Module.finrank ℚ F * M), fun x => ?_⟩
  split_ifs with hx
  ·
    have hlt : Real.exp x * r < r₀ := by
      have := (Real.lt_log_iff_exp_lt (div_pos h0 hr)).mp hx
      exact (lt_div_iff₀ hr).mp this
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun X => Set.indicator_of_notMem ?_ _)
    intro hmem
    exact hnone X.1 X.2 (box_mono b N hlt.le (hscale x _ hmem))
  · have hge : r₀ ≤ Real.exp x * r := by
      have := (Real.log_le_iff_le_exp (div_pos h0 hr)).mp (not_lt.mp hx)
      exact (div_le_iff₀ hr).mp this
    set e := ratHom (F := F) (E := E) M with he
    have hone : ∑' l : Fin 1 → Fin M → E,
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ 1 := by
      rw [tsum_eq_single 0]
      · exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => by simp)
      · intro X hX
        exact Set.indicator_of_notMem (hnone X hX) _
    have hpack := _root_.GlobalTheory.CompanionTheory.SW.Pack.box_packing F E σ hCM _ b M (Fin 1 → Fin M → E) e N r₀ (Real.exp x * r) h0 hge
    calc ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞)))
            (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1)
        ≤ ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0},
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e X.1) := by
          refine ENNReal.tsum_le_tsum fun X => ?_
          by_cases hm : ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
              ratTup (AF F) X.1 ∈ Ω
          · have hm' : e X.1 ∈ box b N (Real.exp x * r) := hscale x _ hm
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
          · rw [Set.indicator_of_notMem hm]
            exact bot_le
      _ ≤ ∑' l : Fin 1 → Fin M → E,
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun l => (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l))
      _ ≤ ENNReal.ofReal ((5 * (Real.exp x * r) / r₀) ^ (2 * Module.finrank ℚ F * M)) * 1 :=
          hpack.trans (mul_le_mul_right hone _)
      _ = ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M) *
            Real.exp (2 * Module.finrank ℚ F * M * x)) := by
          rw [mul_one]
          congr 1
          have : (2 * (Module.finrank ℚ F : ℝ) * M * x) =
              ((2 * Module.finrank ℚ F * M : ℕ) : ℝ) * x := by push_cast; ring
          rw [this, Real.exp_nat_mul, ← mul_pow]
          congr 1
          ring

end GlobalTheory.CompanionTheory.SW.LatCount
end
end

