module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepTensor
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.HilbTensorUnitary

open GlobalTheory.HilbTensorRep

theorem isURep_tensor {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {tens : (∀ i, H i) → Hs} {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    {π : ∀ i, G i →* (H i →L[ℂ] H i)} {σs : (∀ i, G i) → (Hs →L[ℂ] Hs)}
    (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (hc : ∀ i a, Continuous fun g => π i g a) :
    IsURep σs := by
  classical
  have h1 : σs 1 = 1 := by
    apply ext_op hd
    intro x
    rw [hs]
    simp
  have hmul : ∀ a b, σs (a * b) = (σs a).comp (σs b) := by
    intro a b
    apply ext_op hd
    intro x
    rw [ContinuousLinearMap.comp_apply, hs, hs, hs]
    simp [Pi.mul_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hnorm : ∀ g u, ‖σs g u‖ = ‖u‖ := by
    intro g u
    have key : ⟪σs g u, σs g u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [← inner_inv hi hd hs hn g (σs g u) u, ← ContinuousLinearMap.comp_apply, ← hmul,
        inv_mul_cancel, h1, ContinuousLinearMap.one_apply]
    have h2 : ‖σs g u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), key]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  let S : Submodule ℂ Hs :=
    { carrier := {u | Continuous fun g => σs g u}
      add_mem' := fun {a b} ha hb => by
        show Continuous fun g => σs g (a + b)
        simp only [map_add (f := _)]
        exact ha.add hb
      zero_mem' := by
        show Continuous fun g => σs g 0
        simp only [map_zero]
        exact continuous_const
      smul_mem' := fun c a ha => by
        show Continuous fun g => σs g (c • a)
        simp only [map_smul]
        exact ha.const_smul c }
  have hmemS : ∀ u, u ∈ S ↔ Continuous fun g => σs g u := fun u => Iff.rfl
  have htens : ∀ x, tens x ∈ S := by
    intro x
    rw [hmemS]
    have e : (fun g => σs g (tens x)) = fun g => tens fun i => π i (g i) (x i) := by
      funext g
      exact hs g x
    rw [e]
    exact (continuous_tens hi).comp (continuous_pi fun i => (hc i (x i)).comp (continuous_apply i))
  have hclosed : IsClosed (S : Set Hs) := by
    apply isClosed_of_closure_subset
    intro u hu
    show Continuous fun g => σs g u
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hub⟩ := Metric.mem_closure_iff.1 hu (ε / 3) (by positivity)
    have hbc : Continuous fun g => σs g b := hb
    filter_upwards [Metric.tendsto_nhds.1 hbc.continuousAt (ε / 3) (by positivity)] with g hg
    have d1 : dist (σs g u) (σs g b) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm]
    have d2 : dist (σs g0 b) (σs g0 u) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm, dist_comm]
    calc dist (σs g u) (σs g0 u)
        ≤ dist (σs g u) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 u) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [d1, d2]; linarith
      _ = ε := by ring
  have hall : ∀ u, u ∈ S := by
    intro u
    have hle : (Submodule.span ℂ (Set.range tens) : Set Hs) ⊆ S :=
      Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact htens x)
    have hcl := closure_minimal hle hclosed
    rw [hd.closure_eq] at hcl
    exact hcl (Set.mem_univ u)
  exact ⟨h1, hmul, hnorm, fun u => hall u⟩

theorem isURep_rows :
    ∀ B : RowsAut, (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) → IsURep B.σs := by
  intro B hB
  have hmem : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), uMat g ∈ UJset (B.I.ε v) := fun v g => g.2
  have hcu : ∀ v, Continuous fun g : Formalism.REAL.UJ (B.I.ε v) => uMat g :=
    fun v => Units.continuous_val.comp continuous_subtype_val
  exact isURep_tensor (H := B.H) (tens := B.tens)
    (π := fun v =>
      { toFun := fun g => B.σ v (uMat g)
        map_one' := (hB v).1.1
        map_mul' := fun a b => (hB v).1.2 _ (hmem v a) _ (hmem v b) })
    B.tens_spec.1 B.tens_spec.2.2 (fun g x => B.tens_spec.2.1 g x)
    (fun v g a => (hB v).2.1 _ (hmem v g) a)
    (fun v a => ((hB v).2.2 a).comp_continuous (hcu v) (hmem v))

end GlobalTheory.HilbTensorUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem inv_keeps {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hA : ∀ y ∈ V, A *ᵥ y ∈ V) : ∀ y ∈ V, B *ᵥ y ∈ V := by
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by simpa using hA y hy
  have hinj : Function.Injective ((Matrix.toLin' A).restrict hA') := by
    intro x y hxy
    have h1 : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (y : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxy
    have h2 := congrArg (fun z => B *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have h1 : A *ᵥ (x : Fin n → ℂ) = y := by
    simpa using congrArg Subtype.val hx
  rw [← h1, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  exact x.2


variable (ε) in
def leviSub {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := flagM ε W
  one_mem' := by
    intro i y hy
    simpa [uMat_one] using hy
  mul_mem' := by
    intro g h hg hh i y hy
    rw [uMat_mul, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg i _ (hh i y hy).1).1, (hh i _ (hg i y hy).2).2⟩
  inv_mem' := by
    intro g hg i y hy
    refine ⟨inv_keeps (uMat_inv_mul g) (W i) (fun z hz => (hg i z hz).1) y hy,
      inv_keeps (A := (uMat g)ᴴ) ?_ (W i) (fun z hz => (hg i z hz).2) y hy⟩
    rw [← Matrix.conjTranspose_mul, uMat_mul_inv, Matrix.conjTranspose_one]


variable (ε) in
def compactSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := maxK ε
  one_mem' := by
    show (uMat (1 : Formalism.REAL.UJ ε))ᴴ * uMat (1 : Formalism.REAL.UJ ε) = 1
    simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have hh' : (uMat h)ᴴ * uMat h = 1 := hh
    show (uMat (g * h))ᴴ * uMat (g * h) = 1
    rw [uMat_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
      Matrix.one_mul, hh']
  inv_mem' := by
    intro g hg
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have h1 : uMat g⁻¹ = (uMat g)ᴴ := by
      calc uMat g⁻¹ = ((uMat g)ᴴ * uMat g) * uMat g⁻¹ := by rw [hg', Matrix.one_mul]
        _ = (uMat g)ᴴ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
    show (uMat g⁻¹)ᴴ * uMat g⁻¹ = 1
    conv_lhs => enter [1]; rw [h1, Matrix.conjTranspose_conjTranspose]
    exact uMat_mul_inv g

theorem isClosed_flagM {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : IsClosed (flagM ε W) := by
  have h : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp only [flagM, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_mulVec continuous_const)).inter
    ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_conjTranspose.matrix_mulVec continuous_const))

theorem isClosed_maxK : IsClosed (maxK ε) :=
  isClosed_eq (continuous_uMat.matrix_conjTranspose.matrix_mul continuous_uMat) continuous_const

theorem conj_sub (m u : Formalism.REAL.UJ ε) (y : Fin n → ℂ) :
    uMat (m * u * m⁻¹) *ᵥ y - y = uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec y (uMat m) (uMat m⁻¹), uMat_mul_inv, Matrix.one_mulVec,
    uMat_mul, uMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem form_inv (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = star (uMat m *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem conj_mem_flagN {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {m u : Formalism.REAL.UJ ε}
    (hm : m ∈ flagM ε W) (hu : u ∈ flagN ε W) : m * u * m⁻¹ ∈ flagN ε W := by
  have hm' : m⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hm
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [conj_sub]
    exact (hm _ _ (hu.1 i _ (hm' _ y hy).1)).1
  · rw [conj_sub]
    refine (hm _ _ (hu.2 _ fun x hx => ?_)).1
    rw [form_inv]
    exact hy _ (hm _ x hx).1

theorem levi_compact_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)),
    (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧
    (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧
    ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W :=
  fun _ ε _ W => ⟨⟨leviSub ε W, rfl⟩, isClosed_flagM W, ⟨compactSub ε, rfl⟩, isClosed_maxK,
    fun _ hm _ hu => conj_mem_flagN W hm hu⟩

end GlobalTheory.FlagLeviGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.UnipRad

variable {n : ℕ} {ε : Fin n → Bool}

private lemma uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

private lemma uMat_one' : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

private lemma inv_mulVec_mulVec (g : Formalism.REAL.UJ ε) (y : Fin n → ℂ) : uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← uMat_mul', inv_mul_cancel, uMat_one', Matrix.one_mulVec]

lemma inv_keeps (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, uMat g *ᵥ y ∈ V) :
    ∀ y ∈ V, uMat g⁻¹ *ᵥ y ∈ V := by
  intro y hy
  have h' : ∀ y ∈ V, Matrix.toLin' (uMat g) y ∈ V := fun y hy => by simpa using h y hy
  have hinj : Function.Injective ((Matrix.toLin' (uMat g)).restrict h') := by
    intro x z hxz
    have h1 : uMat g *ᵥ (x : Fin n → ℂ) = uMat g *ᵥ (z : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxz
    apply Subtype.ext
    rw [← inv_mulVec_mulVec g x, h1, inv_mulVec_mulVec]
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨y, hy⟩
  have h1 : uMat g *ᵥ (x : Fin n → ℂ) = y := by simpa using congrArg Subtype.val hx
  rw [← h1, inv_mulVec_mulVec]
  exact x.2

lemma keeps {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) (i : Fin (a + 1)) : ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  intro y hy
  induction i using Fin.cases with
  | zero =>
    rw [hW.1] at hy ⊢
    rw [(Submodule.mem_bot ℂ).mp hy]
    simp
  | succ i =>
    have h1 := hW.2.1 (Fin.castSucc_le_succ i) (hu.1 i y hy)
    simpa using (W i.succ).add_mem h1 hy

private lemma step_mul (g h : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) (h2 : uMat h *ᵥ y - y ∈ V) :
    uMat (g * h) *ᵥ y - y ∈ V := by
  have := V.add_mem (hk _ h2) h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← uMat_mul'] at this
  simpa using this

private lemma step_inv (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) :
    uMat g⁻¹ *ᵥ y - y ∈ V := by
  have := V.neg_mem (inv_keeps g V hk _ h1)
  rw [Matrix.mulVec_sub, inv_mulVec_mulVec] at this
  simpa using this

private lemma closed_step (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    IsClosed {g : Formalism.REAL.UJ ε | uMat g *ᵥ y - y ∈ V} := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact V.closed_of_finiteDimensional.preimage
    ((hc.matrix_mulVec continuous_const).sub continuous_const)

theorem flagN_subgroup_closed_keeps (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (hW : IsIsoFlag ε j W) :
    (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧
      ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  refine ⟨⟨{ carrier := flagN ε W, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩, ?_,
    fun u hu i => keeps hW u hu i⟩
  · intro g h hg hh
    exact ⟨fun i y hy => step_mul g h _ y (keeps hW g hg _) (hg.1 i y hy) (hh.1 i y hy),
      fun y hy => step_mul g h _ y (keeps hW g hg _) (hg.2 y hy) (hh.2 y hy)⟩
  · refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
    · rw [uMat_one', Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
  · intro g hg
    exact ⟨fun i y hy => step_inv g _ y (keeps hW g hg _) (hg.1 i y hy),
      fun y hy => step_inv g _ y (keeps hW g hg _) (hg.2 y hy)⟩
  · unfold flagN
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y)

end GlobalTheory.FlagMeas.UnipRad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatUnipMapMulVec
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.PointLattice

section General

variable {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem latUnip_map_mulVec (ι : E →+* A) (M : Matrix n n E) (y : n → E) :
    (fun i => ι ((M *ᵥ y) i)) = M.map ι *ᵥ fun i => ι (y i) := by
  funext i
  exact RingHom.map_mulVec ι M y i

theorem latUnip_conj_pow (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) :
    (Y * G * X - 1) ^ m * Y = Y * (G - 1) ^ m := by
  have h1 : (Y * G * X - 1) * Y = Y * (G - 1) := by
    rw [sub_mul, one_mul, mul_assoc (Y * G), h, mul_one, mul_sub, mul_one]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, mul_assoc, ← pow_succ]

end General

theorem lamX_unipMod : ∀ (I : AutInst) (x a : I.GA) (γ : GL (Fin I.n) I.E) (l : ℕ), 1 ≤ l → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (x⁻¹ * a * x).2 ∈ I.Kset → I.UnipMod l (x⁻¹ * a * x).2 → (∀ y ∈ lamX I x, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) ∧ ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y = (l : I.E) • z := by
  intro I x a γ l hl hfa hk hu
  have hK : ∀ w, w ∈ I.Lf ↔ I.fmat (x⁻¹ * a * x).2 *ᵥ w ∈ I.Lf := hk
  have hmem : ∀ y, y ∈ lamX I x ↔
      I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := (lamX_selfDual I x).1
  have hconj : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hXY : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := by
    show I.fmat (x.2 * x.2⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have key : ∀ y, I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat (x⁻¹ * a * x).2 *ᵥ (I.fmat x.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    intro y
    rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (γ : Matrix (Fin I.n) (Fin I.n) I.E) y, ← hfa, hconj, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, mul_assoc (I.fmat x.2⁻¹ * I.fmat a.2), hXY, mul_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hmem, key]
    exact (hK _).1 ((hmem y).1 hy)
  · obtain ⟨w, hw, hwe⟩ := hu _ ((hmem y).1 hy)
    have hl0 : (l : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨(l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y), ?_, ?_⟩
    · rw [hmem]
      have hpow : (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = (I.fmat a.2 - 1) ^ I.n := by
        rw [hfa, ← RingHom.mapMatrix_apply, map_pow, map_sub, map_one, RingHom.mapMatrix_apply]
      have hcp := latUnip_conj_pow (I.fmat x.2) (I.fmat x.2⁻¹) (I.fmat a.2) hXY I.n
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y)) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) ((l : I.E)⁻¹) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      have e2 : I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i)) =
          (l : TensorProduct I.F I.E (Af I.F)) • w := by
        rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) y, hpow, Matrix.mulVec_mulVec, ← hcp,
          ← Matrix.mulVec_mulVec, ← hconj, hwe]
      rw [e1, Matrix.mulVec_smul, e2, smul_smul, ← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) l, ← map_mul,
        inv_mul_cancel₀ hl0, map_one, one_smul]
      exact hw
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]

end GlobalTheory.PointLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqMeasureInterFundamentalDom
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory


open scoped Pointwise in
theorem covol_eq_measure_inter_fund : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) (μ : Measure G) (fund A : Set G), (Γ : Set G).Countable → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → MeasurableSet A → (∀ γ ∈ Γ, ∀ x ∈ A, γ * x ∈ A) → covol (Γ : Set G) μ A = μ (A ∩ fund) := by
  intro G _ _ _ Γ μ fund A hc hμ hf hcov hdis hA hinv
  have : Countable Γ := hc.to_subtype
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s hs => by
    have h := hμ γ γ.2
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_const_mul (γ : G)) hs]
    rfl⟩
  have hF : IsFundamentalDomain Γ fund μ := by
    refine IsFundamentalDomain.mk'' hf.nullMeasurableSet ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact ⟨⟨γ, hγ⟩, h⟩
    · intro γ hγ
      exact hdis γ γ.2 (fun h => hγ (Subtype.ext h))
    · intro γ
      exact (measurePreserving_smul γ μ).quasiMeasurePreserving
  apply le_antisymm
  · unfold covol
    refine iInf_le_of_le (A ∩ fund) (iInf_le_of_le (hA.inter hf) (iInf_le_of_le ?_ le_rfl))
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    exact ⟨γ, hγ, hinv γ hγ x hx, h⟩
  · unfold covol
    refine le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_
    rw [hF.measure_eq_tsum D]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro x ⟨hx, hxf⟩
    obtain ⟨γ, hγ, h⟩ := hD x hx
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hxf⟩
    rw [Set.mem_inv_smul_set_iff]
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingEqLeadingMinor
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PrincipalMinorExterior

theorem pairing_eq_leading_minor : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp l (Formalism.QuantumDeterminants.Hpk k r))
      (cmp l g *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z' (Fin.castLE hl a))))
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) =
      ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  intro k r l hl z z' g
  rw [Formalism.QuantumDeterminants.herm, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge,
    GlobalTheory.TopMinorWedge.star_wedge_dot]
  rfl

end GlobalTheory.PrincipalMinorExterior
end

