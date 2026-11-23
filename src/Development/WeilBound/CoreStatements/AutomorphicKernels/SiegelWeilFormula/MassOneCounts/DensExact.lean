module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityBoundNonzero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PrimitiveVectorQuadraticLevelMeasure
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝒪" => v.adicCompletionIntegers F
local notation "𝓴" => IsLocalRing.ResidueField 𝒪
local notation "phi" => ValuationSubring.subtype 𝒪
local notation "res" => IsLocalRing.residue 𝒪

theorem dens_exact (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (BO : Matrix ι ι 𝒪) (hBs : (BO.map phi).IsSymm)
    (hBdet : Valued.v (BO.map phi).det = 1) (s : 𝒪) (hsu : Valued.v (s : Fv F v) = 1)
    (A : Set (Fv F v)) (hA : MeasurableSet A) (hAs : A ⊆ {z | Valued.v (z - s) < Valued.v (s : Fv F v)}) :
    (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
        (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
      ((Nat.card {y : ι → 𝓴 // (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y)) = res s} : ℝ≥0∞) *
        (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1)) * lam A := by
  classical
  have hLoc := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : SecondCountableTopology (Fv F v) := hLoc.2.2.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, hcard⟩ := _root_.GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion F v lam hlam
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  haveI : Finite 𝓴 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq0)
  letI : Fintype 𝓴 := Fintype.ofFinite _
  have hBint : ∀ i j, (BO.map phi) i j ∈ v.adicCompletionIntegers F := fun i j => (BO i j).2
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  let c : 𝒪 := ⟨2⁻¹, by show Valued.v ((2 : Fv F v)⁻¹) ≤ 1; rw [map_inv₀, h2, inv_one]⟩
  have hc : (c : Fv F v) = 2⁻¹ := rfl
  have hc2 : c * 2 = 1 := by
    apply Subtype.ext
    have e : (phi : 𝒪 →+* Fv F v) (c * 2) = phi c * phi 2 := map_mul _ _ _
    have e2 : (phi : 𝒪 →+* Fv F v) 2 = 2 := map_ofNat _ 2
    have e3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [e2, e3, inv_mul_cancel₀ h20] at e
    exact e
  have hr1 : res c * 2 = 1 := by
    have := congrArg res hc2
    rwa [map_mul, map_one, map_ofNat] at this
  have hr : res c = 2⁻¹ := eq_inv_of_mul_eq_one_left hr1
  have hres_zero (a : 𝒪) : res a = 0 ↔ Valued.v (a : Fv F v) < 1 :=
    (IsLocalRing.residue_eq_zero_iff a).trans (Valued.v.mem_maximalIdeal_iff)
  have hres_eq (a b : 𝒪) : res a = res b ↔ Valued.v ((a : Fv F v) - b) < 1 := by
    rw [← sub_eq_zero, ← map_sub, hres_zero]
    rfl
  set sb : 𝓴 := res s with hsb
  have hsb0 : sb ≠ 0 := by
    intro h0
    have h' := (hres_zero s).1 h0
    rw [hsu] at h'
    exact lt_irrefl _ h'
  let qk : (ι → 𝓴) → 𝓴 := fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))
  let Fl : Finset (ι → 𝓴) := Finset.univ.filter fun y => qk y = sb
  have hN : Nat.card {y : ι → 𝓴 // (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y)) = sb} = Fl.card :=
    Nat.subtype_card Fl (fun x => by simp [Fl, qk])

  obtain ⟨π, hπ⟩ := GlobalTheory.CompanionTheory.SW.GBall.exists_unif v
  have hprimeq : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
      (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
      {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧
        (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} := by
    ext x
    constructor
    · rintro ⟨hx, hQ⟩
      refine ⟨hx, ?_, hQ⟩
      by_contra hnp
      have h5 := GlobalTheory.CompanionTheory.SW.GBall.q_nonprim h2 hBint hπ hx hnp
      have hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) - s) < Valued.v (s : Fv F v) := hAs hQ
      have hv := Valuation.map_eq_of_sub_lt Valued.v hlt
      rw [hv, hsu] at h5
      have hlt1 : WithZero.exp (-2 : ℤ) < 1 := by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.2 (by norm_num)
      exact absurd h5 (not_le.2 hlt1)
    · rintro ⟨hx, -, hQ⟩
      exact ⟨hx, hQ⟩
  have hAs1 : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => by
    have := hAs hz
    rw [hsu] at this
    exact this
  rw [hprimeq, hN]
  set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf
  have hQc : Continuous Qf := by
    refine continuous_const.mul ?_
    exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  let lift : 𝓴 → 𝒪 := Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪))
  have hres_lift (y : 𝓴) : res (lift y) = y := Function.surjInv_eq _ y
  let lf (y : ι → 𝓴) (i : ι) : Fv F v := lift (y i)
  have hcover (x : ι → Fv F v) :
      ((∀ i, x i ∈ 𝒪) ∧ ∃ i, Valued.v (x i) = 1) ↔
        ∃ y : ι → 𝓴, y ≠ 0 ∧ ∀ i, Valued.v (x i - lf y i) < 1 := by
    constructor
    · rintro ⟨hx, i, hi⟩
      let y : ι → 𝓴 := fun j => res ⟨x j, hx j⟩
      refine ⟨y, ?_, fun j => (hres_eq ⟨x j, hx j⟩ (lift (y j))).1 (hres_lift _).symm⟩
      intro h
      have hlt := (hres_zero ⟨x i, hx i⟩).1 (congrFun h i)
      exact (ne_of_lt hlt) hi
    · rintro ⟨y, hy, h⟩
      have hx (i : ι) : x i ∈ 𝒪 := by
        change Valued.v (x i) ≤ 1
        calc
          Valued.v (x i) = Valued.v (x i - lf y i + lf y i) := by rw [sub_add_cancel]
          _ ≤ 1 := Valuation.map_add_le _ (h i).le (lift (y i)).2
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
      refine ⟨hx, i, le_antisymm (hx i) (not_lt.1 fun hlt => hi ?_)⟩
      calc
        y i = res (lift (y i)) := (hres_lift _).symm
        _ = res ⟨x i, hx i⟩ := ((hres_eq _ _).2 (h i)).symm
        _ = 0 := (hres_zero _).2 hlt
  let P : (ι → 𝓴) → Set (ι → Fv F v) := fun y =>
    {x | (∀ i, Valued.v (x i - lf y i) < 1) ∧ Qf x ∈ A}
  let T0 : Finset (ι → 𝓴) := Finset.univ.filter fun y => y ≠ 0
  have hS : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
      (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
      ⋃ y ∈ T0, P y := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨h1, h3, h4⟩
      obtain ⟨y, hy, h⟩ := (hcover x).1 ⟨h1, h3⟩
      exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, h, h4⟩
    · rintro ⟨y, hy, h, h4⟩
      obtain ⟨h1, h3⟩ := (hcover x).2 ⟨y, (Finset.mem_filter.1 hy).2, h⟩
      exact ⟨h1, h3, h4⟩
  have hball : MeasurableSet {a : Fv F v | Valued.v a < 1} := by
    have h := (Valued.isOpen_ball (Fv F v) 1).measurableSet
    simpa [Valuation.restrict_lt_iff_lt_embedding] using h
  have hmeas : ∀ y ∈ T0, MeasurableSet (P y) := by
    intro y _
    have e : P y = (⋂ i, (fun x : ι → Fv F v => x i - lf y i) ⁻¹' {a | Valued.v a < 1}) ∩ Qf ⁻¹' A := by
      ext x
      simp [P]
    rw [e]
    refine (MeasurableSet.iInter fun i => ?_).inter (hQc.measurable hA)
    exact ((continuous_apply i).sub continuous_const).measurable hball
  have hdisj : Set.PairwiseDisjoint (↑T0) P := by
    intro y _ y' _ hne
    refine Set.disjoint_left.2 fun x hx hx' => hne (funext fun i => ?_)
    have h := Valuation.map_sub_lt _ (hx'.1 i) (hx.1 i)
    have e : (x i - lf y' i) - (x i - lf y i) = lf y i - lf y' i := by ring
    rw [e] at h
    have he := (hres_eq (lift (y i)) (lift (y' i))).2 h
    rwa [hres_lift, hres_lift] at he
  have hclass : ∀ y ∈ T0, (Measure.pi fun _ : ι => lam) (P y) =
      if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1)) * lam A else 0 := by
    intro y hy
    have hy0 : y ≠ 0 := (Finset.mem_filter.1 hy).2
    obtain ⟨hint, hprim⟩ := (hcover (lf y)).2 ⟨y, hy0, fun i => by simp⟩
    let z : ι → 𝒪 := lift ∘ y
    let a : 𝒪 := c * (z ⬝ᵥ (BO *ᵥ z))
    have hmap_quad {R : Type} [CommRing R] (f : 𝒪 →+* R) :
        f (z ⬝ᵥ (BO *ᵥ z)) = (f ∘ z) ⬝ᵥ ((BO.map f) *ᵥ (f ∘ z)) := by
      rw [RingHom.map_dotProduct]
      congr 1
      funext i
      exact RingHom.map_mulVec f BO z i
    have haQ : (a : Fv F v) = Qf (lf y) := by
      change phi (c * (z ⬝ᵥ (BO *ᵥ z))) = _
      rw [map_mul, hmap_quad, show phi c = _ from hc]
      rfl
    have har : res a = qk y := by
      change res (c * (z ⬝ᵥ (BO *ᵥ z))) = _
      have hz : (⇑res ∘ z) = y := funext fun i => hres_lift (y i)
      rw [map_mul, hr, hmap_quad, hz]
    have key := _root_.GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA
    have hkey : (Measure.pi fun _ : ι => lam) (P y) = _ := key
    rw [hkey]
    have hcl : Valued.v ((s : Fv F v) - Qf (lf y)) < 1 ↔ qk y = sb := by
      have := hres_eq s a
      rw [har] at this
      rw [show Qf (lf y) = (a : Fv F v) from haQ.symm]
      exact ⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩
    split_ifs with he
    · have hlt := hcl.2 he
      have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A := by
        refine Set.inter_eq_left.2 fun z hz => ?_
        have h5 : Valued.v (z - s) < 1 := hAs1 hz
        have h6 := Valuation.map_add_lt _ h5 hlt
        have e : z - s + (s - Qf (lf y)) = z - Qf (lf y) := by ring
        rw [e] at h6
        exact h6
      rw [this]
    · have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)
        have h5 : Valued.v (z - s) < 1 := hAs1 hz.1
        have h6 : Valued.v (z - Qf (lf y)) < 1 := hz.2
        have h7 := Valuation.map_sub_lt _ h6 h5
        have e : z - Qf (lf y) - (z - s) = s - Qf (lf y) := by ring
        rw [e] at h7
        exact h7
      rw [this, measure_empty, mul_zero]
  rw [hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  have hT : T0.filter (fun y => qk y = sb) = Fl := by
    ext y
    simp only [T0, Fl, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      apply hsb0
      rw [← h]
      simp [qk]
  rw [hT, mul_assoc]

end PositivityTheory.SiegelWeilFormula.MOne

end
