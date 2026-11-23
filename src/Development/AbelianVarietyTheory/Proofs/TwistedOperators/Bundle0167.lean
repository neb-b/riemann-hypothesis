module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalOfAFormBForm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma pos_of_isLval {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {c : Eig D} {z : ℝ} (h : IsLval R i t c z) : 0 < z := by
  obtain ⟨_, _, hL⟩ := h
  exact hL.2.1

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {p q r : Prop} (f : p → q) (k₁ : ¬p → r) (k₂ : q → r) : r := by
  by_cases hp : p
  · exact k₂ (f hp)
  · exact k₁ hp

theorem scal_of_aForm_bForm {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (SF)
    (hA : AForm R SF) (hB : BForm R SF) (hM : MatchUp R SF) : Scal R SF := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨κ₀, hκ₀, hB⟩ := hB
  have hPa : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i

  have hA' : ∀ i t c, ∃ l : ℝ, 0 < l ∧
      (∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((l : ℝ) : ℂ) • x) ∧
      ((∃ z, IsLval R i t c z ∧ l = a i * z) ∨ ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0) := by
    intro i t c
    refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hA i t c) (fun h => ?_) (fun hq => ?_)
    · have h0 : ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0 := by
        intro x hx
        by_contra hne
        exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
      refine ⟨1, one_pos, fun x hx => ?_, Or.inr h0⟩
      rw [h0 x hx]
      simp only [map_zero, smul_zero]
    · obtain ⟨z, hz, hx⟩ := hq
      exact ⟨a i * z, mul_pos (ha i) (pos_of_isLval hz), hx, Or.inl ⟨z, hz, rfl⟩⟩
  choose lam hlpos hlW hlz using hA'
  refine ⟨lam, κ₀ / (∏ i, a i), div_pos hκ₀ hPa, hlpos, hlW, ?_⟩
  intro t c x hx
  refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hM c) (fun h => ?_) (fun hW => ?_)
  ·
    have hx0 : x = 0 := by
      by_contra hne
      exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
    rw [hx0]
    simp only [map_zero, smul_zero]
  ·
    have hz' : ∀ i, ∃ z, IsLval R i t c z ∧ lam i t c = a i * z := fun i =>
      (hlz i t c).resolve_right fun h0 => hW i ((Submodule.eq_bot_iff _).mpr h0)
    choose z hz hlz' using hz'
    have key : κ₀ / (∏ i, a i) * ∏ i, lam i t c = κ₀ * ∏ i, z i := by
      rw [Finset.prod_congr rfl fun i _ => hlz' i, Finset.prod_mul_distrib, ← mul_assoc,
        div_mul_cancel₀ κ₀ hPa.ne']
    rw [key]
    exact hB t c z hz x hx

end GlobalTheory.LiftRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasFiniteOnCompactsAndOpenPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem exists_mul_of_mem_sup_range {G H : Type} [Group G] [Group H] (N : Subgroup G) (s : H →* G)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) {g : G} (hg : g ∈ N ⊔ s.range) :
    ∃ n ∈ N, ∃ h, g = n * s h := by
  let K : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ h, x = n * s h}
      one_mem' := ⟨1, N.one_mem, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
        refine ⟨n₁ * (s h₁ * n₂ * (s h₁)⁻¹), N.mul_mem hn₁ (hnorm n₂ hn₂ h₁), h₁ * h₂, ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨n, hn, h, rfl⟩
        refine ⟨s h⁻¹ * n⁻¹ * (s h⁻¹)⁻¹, hnorm n⁻¹ (N.inv_mem hn) h⁻¹, h⁻¹, ?_⟩
        rw [map_inv]
        group }
  have hle : N ⊔ s.range ≤ K := by
    refine sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) ?_
    rintro _ ⟨h, rfl⟩
    exact ⟨1, N.one_mem, h, by simp⟩
  exact hle hg

theorem semiMeas_finite_on_compacts_and_open_pos : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G), IsClosed (N : Set G) → Continuous s → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N), p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h) → ∀ (μ : Measure H) (ν : Measure N), μ.IsHaarMeasure → ν.IsHaarMeasure → (∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) → IsFiniteMeasureOnCompacts (semiMeas N s μ ν) ∧ (semiMeas N s μ ν).IsOpenPosMeasure := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N s hN hs hnorm hp μ ν hμ hν _
  obtain ⟨p, hpc, hps⟩ := hp
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := inferInstanceAs (SecondCountableTopology (N : Set G))
  haveI : IsFiniteMeasureOnCompacts ν := inferInstance
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : ν.IsOpenPosMeasure := inferInstance
  haveI : (μ.prod ν).IsOpenPosMeasure := inferInstance

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun q =>
    ⟨q.2.1 * s q.1, mul_mem (Subgroup.mem_sup_left q.2.2) (Subgroup.mem_sup_right ⟨q.1, rfl⟩)⟩
  have hφc : Continuous φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)).subtype_mk _
  have hmemN : ∀ k : (N ⊔ s.range : Subgroup G), (k : G) * (s (p k))⁻¹ ∈ N := by
    intro k
    obtain ⟨n, hn, h, hk⟩ := exists_mul_of_mem_sup_range N s hnorm k.2
    have hpk : p k = h := by
      have hk' : k = ⟨n * s h, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ :=
        Subtype.ext hk
      rw [hk']
      exact hps h ⟨n, hn⟩
    rw [hpk, hk, mul_inv_cancel_right]
    exact hn
  let ψ : (N ⊔ s.range : Subgroup G) → H × N := fun k => (p k, ⟨(k : G) * (s (p k))⁻¹, hmemN k⟩)
  have hψc : Continuous ψ :=
    hpc.prodMk ((continuous_subtype_val.mul (hs.comp hpc).inv).subtype_mk _)
  have hψφ : ∀ q, ψ (φ q) = q := by
    rintro ⟨h, n⟩
    have h1 : p (φ (h, n)) = h := hps h n
    refine Prod.ext h1 (Subtype.ext ?_)
    show (n : G) * s h * (s (p (φ (h, n))))⁻¹ = n
    rw [h1, mul_inv_cancel_right]
  have hφψ : ∀ k, φ (ψ k) = k := by
    intro k
    apply Subtype.ext
    show (k : G) * (s (p k))⁻¹ * s (p k) = k
    rw [inv_mul_cancel_right]
  have hsurj : Function.Surjective φ := fun k => ⟨ψ k, hφψ k⟩
  show IsFiniteMeasureOnCompacts ((μ.prod ν).map φ) ∧ ((μ.prod ν).map φ).IsOpenPosMeasure
  refine ⟨⟨fun C hC => ?_⟩, hφc.isOpenPosMeasure_map hsurj⟩
  rw [Measure.map_apply hφc.measurable hC.measurableSet]
  refine lt_of_le_of_lt (measure_mono ?_) (hC.image hψc).measure_lt_top
  intro q hq
  exact ⟨φ q, hq, hψφ q⟩

end GlobalTheory.MixPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasIsMulLeftInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MixPer.semiMeas_isMulLeftInvariant {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (_hp : ∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N),
      p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h)
    (μ : Measure H) (ν : Measure N) (hμ : μ.IsHaarMeasure) (hν : ν.IsHaarMeasure)
    (hc : ∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) :
    (semiMeas N s μ ν).IsMulLeftInvariant := by
  have := hμ
  have := hν
  have : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite ν := inferInstance
  have : SigmaFinite μ := inferInstance
  have hemb : MeasurableEmbedding (Subtype.val : N → G) :=
    MeasurableEmbedding.subtype_coe hN.measurableSet

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun p =>
    ⟨p.2.1 * s p.1, mul_mem (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right ⟨p.1, rfl⟩)⟩
  have hφ : Measurable φ :=
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul
      (hs.comp continuous_fst)) _).measurable
  have hm : semiMeas N s μ ν = (μ.prod ν).map φ := rfl

  let T : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ N ⊔ s.range,
        (semiMeas N s μ ν).map (fun x => (⟨g, hg⟩ : (N ⊔ s.range : Subgroup G)) * x) =
          semiMeas N s μ ν}
      one_mem' := by
        refine ⟨one_mem _, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨1, one_mem _⟩ : (N ⊔ s.range : Subgroup G)) * x) = id := funext fun x => one_mul x
        rw [e, Measure.map_id]
      mul_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a * b, mul_mem ha hb⟩ : (N ⊔ s.range : Subgroup G)) * x) =
            (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨b, hb⟩ : (N ⊔ s.range : Subgroup G)) * x) :=
          funext fun x => mul_assoc (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) ⟨b, hb⟩ x
        rw [e, ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), eb, ea]
      inv_mem' := by
        rintro a ⟨ha, ea⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← ea]
        rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have e : ((fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a⁻¹, inv_mem ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x)) = id :=
          funext fun x => inv_mul_cancel_left (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) x
        rw [e, Measure.map_id] }

  have hNT : N ≤ T := by
    intro n hn
    refine ⟨Subgroup.mem_sup_left hn, ?_⟩
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨n, Subgroup.mem_sup_left hn⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map id (fun m : N => (⟨n, hn⟩ : N) * m) := by
      funext p
      apply Subtype.ext
      simp [φ, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ (measurable_id.prodMap (measurable_const_mul _)),
      ← Measure.map_prod_map μ ν measurable_id (measurable_const_mul _), Measure.map_id,
      map_mul_left_eq_self]

  have hST : s.range ≤ T := by
    rintro _ ⟨h₀, rfl⟩
    refine ⟨Subgroup.mem_sup_right ⟨h₀, rfl⟩, ?_⟩
    let c : N → N := fun m => ⟨s h₀ * m.1 * (s h₀)⁻¹, hnorm m.1 m.2 h₀⟩
    have hcm : Measurable c :=
      (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const)
        _).measurable
    have hcν : ν.map c = ν := by
      rw [← hemb.comap_map (ν.map c), Measure.map_map hemb.measurable hcm]
      have e : (Subtype.val ∘ c) = (fun m : N => s h₀ * m.1 * (s h₀)⁻¹) := rfl
      rw [e, hc h₀, hemb.comap_map]
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨s h₀, Subgroup.mem_sup_right ⟨h₀, rfl⟩⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map (fun h => h₀ * h) c := by
      funext p
      apply Subtype.ext
      simp [φ, c, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ ((measurable_const_mul _).prodMap hcm),
      ← Measure.map_prod_map μ ν (measurable_const_mul _) hcm, hcν, map_mul_left_eq_self]
  have hT : N ⊔ s.range ≤ T := sup_le hNT hST
  exact ⟨fun k => by
    obtain ⟨hk, ek⟩ := hT k.2
    exact ek⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantMulMaximalCompact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembers

theorem kset_apply_eq_zero {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    {i j : Fin n} (hij : ε i ≠ ε j) : g i j = 0 := by
  have h := congrFun (congrFun hg.2 i) j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ne_eq, not_true_eq_false] at hij h ⊢ <;>
    simp at h <;> first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h

theorem signBlockDeterminant_mul_maximalCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {g h : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hh : h ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e (g * h) = signBlockDeterminant ε e g * signBlockDeterminant ε e h := by
  classical
  unfold signBlockDeterminant
  rw [← Matrix.det_mul]
  congr 1
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ l, ε l ≠ e → g x l * h l y = 0 := fun l hl => by
    rw [kset_apply_eq_zero hg (by rw [x.2]; exact fun h' => hl h'.symm), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun l => ε l = e))
    (fun l _ hl => key l (by simpa using hl))]
  exact Finset.sum_subtype _ (by simp) (fun l => g x l * h l y)

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem subst_one_X (k : Matrix (Fin b) (Fin b) ℂ) (i : Fin b) (j : Fin a) :
    subst τ ε ε' 1 k (MvPolynomial.X (τ, i, j)) =
      ∑ l, (if ε' i = ε j then k l i else star (k l i)) • MvPolynomial.X (τ, l, j) := by
  classical
  simp only [subst, MvPolynomial.aeval_X, if_true]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro m _ hm
    split_ifs <;> simp [Matrix.one_apply_ne hm]
  · simp

theorem subst_one_mul {k₁ k₂ : Matrix (Fin b) (Fin b) ℂ} (h₁ : k₁ ∈ Formalism.REAL.Kset ε') (h₂ : k₂ ∈ Formalism.REAL.Kset ε')
    (P : PolF D b a) : subst τ ε ε' 1 (k₁ * k₂) P = subst τ ε ε' 1 k₁ (subst τ ε ε' 1 k₂ P) := by
  classical
  suffices h : subst τ ε ε' 1 (k₁ * k₂) = (subst τ ε ε' 1 k₁).comp (subst τ ε ε' 1 k₂) by
    rw [h]; rfl
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨ρ, i, j⟩ := v
  by_cases hρ : ρ = τ
  · subst hρ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, subst_one_X, subst_one_X, map_sum]
    simp only [map_smul, subst_one_X, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Matrix.mul_apply]
    split_ifs with hij
    · refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : ε' l = ε' i
      · rw [if_pos (hl.trans hij)]; ring
      · rw [kset_apply_eq_zero h₂ hl]; simp
    · rw [star_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : ε' l = ε' i
      · rw [if_neg (fun h => hij (hl.symm.trans h)), star_mul']; ring
      · rw [kset_apply_eq_zero h₂ hl]; simp
  · simp [subst, hρ]

theorem signCard_signed (l₁ l₂ : List ℚ) (c : ℚ) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (signed l₁ l₂ c) true = l₁.length ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (signed l₁ l₂ c) false = l₂.length := by
  classical
  have n₁ : (l₁.map fun x => (x + c, true)).Nodup := h₁.map fun x y h => by simpa using h
  have n₂ : (l₂.map fun x => (x + c, false)).Nodup := h₂.map fun x y h => by simpa using h
  have m₁ : ∀ x ∈ (l₁.map fun x => (x + c, true)).toFinset, x.2 = true := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rfl
  have m₂ : ∀ x ∈ (l₂.map fun x => (x + c, false)).toFinset, x.2 = false := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard signed
  rw [Finset.filter_union, Finset.filter_union]
  constructor
  · rw [Finset.filter_true_of_mem m₁, Finset.filter_false_of_mem (fun x hx => by simp [m₂ x hx]),
      Finset.union_empty, List.card_toFinset, List.dedup_eq_self.2 n₁, List.length_map]
  · rw [Finset.filter_false_of_mem (fun x hx => by simp [m₁ x hx]), Finset.filter_true_of_mem m₂,
      Finset.empty_union, List.card_toFinset, List.dedup_eq_self.2 n₂, List.length_map]

theorem opPow_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (h : ∀ i, A i 0 = 0) (k : ι →₀ ℕ) :
    opPow A k 0 = 0 := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, h]

theorem ptF_zero {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hA : ∀ l, aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l 0 = 0 := by
    intro l
    funext x
    simp [aPlusAll, aPlus, crea, Formalism.IndefR.Datum.dRho, heisO]
  have e : pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 = 0 := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [pureTensorL, Module.Basis.constr_basis, opPow_zero _ hA]
    rfl
  change pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 P = 0
  rw [e]
  rfl

end GlobalTheory.LowerMembers

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquetStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_borelJacquet_of_cuspidal_segment_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (l d : ℕ), 0 < l → 1 < d → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W) (π : Representation ℂ (GL (Fin (l * d)) k) V), IsCuspidal σ → (∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d), Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) → Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  first | exact @GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | exact GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | (intros; apply GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TraceFrames

theorem hO_eq_trace_mul {D : D7} (S T : HSp D) (k y : WO S T) :
    hO S T y k = Matrix.trace (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D))
      * (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]; enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem toEAf_hO_eq_trace_frames {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D))
    (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  set X₀ : Matrix (Fin S.rank) (Fin T.rank) (AE D) := HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D)) with hX
  set Y₀ : Matrix (Fin T.rank) (Fin S.rank) (AE D) := y with hY
  set A : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := (βS⁻¹).val with hA
  set A' : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := βS.val with hA'
  set B : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := βT.val with hB
  set B' : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := (βT⁻¹).val with hB'
  set Xf : Matrix (Fin S.rank) (Fin T.rank) (Datum.EAf D) := X₀.map (toEAf D) with hXf
  set Yf : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := Y₀.map (toEAf D) with hYf
  have hBB : HMul.hMul B B' = (1 : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D)) := Units.mul_inv βT
  have hAA : HMul.hMul A' A = (1 : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) := Units.mul_inv βS
  have h1 : frMapAdj S T βS βT k = HMul.hMul (HMul.hMul A Xf) B := rfl
  have h2 : frMapO S T βS βT y = HMul.hMul (HMul.hMul B' Yf) A' := rfl
  have h4 : HMul.hMul Xf Yf = (HMul.hMul X₀ Y₀ : Matrix (Fin S.rank) (Fin S.rank) (AE D)).map (toEAf D) :=
    (Matrix.map_mul).symm
  have h3 : (HMul.hMul (HMul.hMul (HMul.hMul A Xf) B) (HMul.hMul (HMul.hMul B' Yf) A') :
      Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) = HMul.hMul A (HMul.hMul (HMul.hMul Xf Yf) A') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
  rw [h1, h2, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, hAA, Matrix.mul_one, h4, hO_eq_trace_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rfl

end GlobalTheory.TraceFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem witt_anisotropic_group_normalizes_flag_unipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∀ n ∈ flagN d, ∀ h : GA D S₀,
    d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d := by
  intro D S S₀ ρ d n hn h
  have he : Formalism.L2.Theta.mt S (d.emb0 h) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX h
  have he' := GlobalTheory.BesselChar.inv_fix_cols (GlobalTheory.BesselChar.mt_inv_mul S (d.emb0 h)) he
  unfold flagN at hn ⊢
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e (isIsoSub_e d).1] at hn ⊢
  rw [GlobalTheory.BesselChar.mt_mul, GlobalTheory.BesselChar.mt_mul]
  exact hn.conj he he' (GlobalTheory.BesselChar.mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end GlobalTheory.MixPer
end

