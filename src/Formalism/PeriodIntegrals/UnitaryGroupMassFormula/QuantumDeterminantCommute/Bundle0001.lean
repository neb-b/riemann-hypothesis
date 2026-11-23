module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Development
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.CapelliOperatorCongruence
section
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace QmCapCommW

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
      (NormedSpace.exp ((s : ℂ) • X) * X * E) s := by
    intro s
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) X (s : ℂ)
    have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
    have h3 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X))
        (NormedSpace.exp ((s : ℂ) • X) * X) s := by
      have hcomm : X * NormedSpace.exp ((s : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * X :=
        (((Commute.refl X).smul_right (s : ℂ)).exp_right).eq
      exact h2.congr_deriv (by simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; exact hcomm)
    exact h3.mul_const E
  have hc := is_const_of_deriv_eq_zero (f := fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
    (fun s => (hd s).differentiableAt) (fun s => by rw [(hd s).deriv, Matrix.mul_assoc, hXE, Matrix.mul_zero])
  have := hc t 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
  exact this

lemma exp_curve_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  let E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j _ => v j
  have hXE : X * E = 0 := by
    ext j l
    have := congrFun hXv j
    simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h := exp_mul_fix X E hXE t
  funext j
  have := congrFun (congrFun h j) j
  simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  have hU : IsUnit H := IsUnit.of_mul_eq_one _ hH
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hH
  have h1 : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [hinv]
    calc Yᴴ = Yᴴ * H * H := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = H * (-Y) * H := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hU, hinv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

lemma glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg1, hh1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a ha).1, (hg2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a ha).2, (hg2 a ha).2]

lemma exp_mem_glev {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩

lemma skew_minus {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
  have e1 : (Z - H * Zᴴ * H)ᴴ = Zᴴ - H * Z * H := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hh, Matrix.mul_assoc H Z H]
  rw [e1, Matrix.sub_mul, Matrix.mul_sub]
  have e2 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc (H * Z) H H, hHH, Matrix.mul_one]
  have e3 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [← Matrix.mul_assoc H (H * Zᴴ) H, ← Matrix.mul_assoc H H Zᴴ, hHH, Matrix.one_mul]
  rw [e2, e3]
  abel

lemma skew_plus {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    H * (Z + H * Zᴴ * H) - (Z + H * Zᴴ * H)ᴴ * H = 0 := by
  have e1 : (Z + H * Zᴴ * H)ᴴ = Zᴴ + H * Z * H := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hh, Matrix.mul_assoc H Z H]
  rw [e1, Matrix.add_mul, Matrix.mul_add]
  have e2 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc (H * Z) H H, hHH, Matrix.mul_one]
  have e3 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [← Matrix.mul_assoc H (H * Zᴴ) H, ← Matrix.mul_assoc H H Zᴴ, hHH, Matrix.one_mul]
  rw [e2, e3]
  abel

lemma hpart1_skew {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  unfold hpart1
  rw [hinv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    have h1 := Complex.conj_ofReal (1 / 2 : ℝ)
    push_cast at h1
    exact h1
  rw [hs, ← smul_add, skew_minus H Z hh hHH, smul_zero]

lemma hpart2_skew {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  unfold hpart2
  rw [hinv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    ring
  rw [hs, neg_smul, neg_add_eq_sub, ← smul_sub, skew_plus H Z hh hHH, smul_zero]

lemma hpk_zero {k r : ℕ} (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor <;> simp only [Hpk, posL, eI, esI, Fin.ext_iff, Fin.val_mk] <;> split_ifs <;>
    first | rfl | (exfalso; omega)

lemma col_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (h : ∀ j, Y j c = 0) : Y *ᵥ bvec c = 0 := by
  funext j
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h]

lemma single_ct {n : ℕ} (a b : Fin n) : (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all

lemma hpart_col {k r : ℕ} {i : Fin (r + 1)} (a b : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcb : c ≠ posL k r i b) (hac : Hpk k r (posL k r i a) c = 0) (s : ℂ) (j : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) + s • ((Hpk k r)⁻¹ *
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) j c = 0 := by
  rw [single_ct]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, hac, Ne.symm hcb]

lemma hpart1_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  refine ⟨hpart1_skew _ _ (hpkFacts k r).1 (hpkFacts k r).2.1, fun a' ha' => ⟨?_, ?_⟩⟩
  all_goals
    refine col_zero _ _ fun j => ?_
    unfold hpart1
    rw [Matrix.smul_apply, sub_eq_add_neg, ← neg_one_smul ℂ ((Hpk k r)⁻¹ * _ * _)]
  · rw [hpart_col a b _ (by simp only [posL, eI, ne_eq, Fin.ext_iff]; omega) (hpk_zero i a a' ha').1, smul_zero]
  · rw [hpart_col a b _ (by simp only [posL, esI, ne_eq, Fin.ext_iff]; have := b.isLt; unfold mdim at this; omega)
      (hpk_zero i a a' ha').2, smul_zero]

lemma hpart2_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  refine ⟨hpart2_skew _ _ (hpkFacts k r).1 (hpkFacts k r).2.1, fun a' ha' => ⟨?_, ?_⟩⟩
  all_goals
    refine col_zero _ _ fun j => ?_
    unfold hpart2
    rw [Matrix.smul_apply, ← one_smul ℂ ((Hpk k r)⁻¹ * _ * _)]
  · rw [hpart_col a b _ (by simp only [posL, eI, ne_eq, Fin.ext_iff]; omega) (hpk_zero i a a' ha').1, smul_zero]
  · rw [hpart_col a b _ (by simp only [posL, esI, ne_eq, Fin.ext_iff]; have := b.isLt; unfold mdim at this; omega)
      (hpk_zero i a a' ha').2, smul_zero]

lemma rdV_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)}
    {D : Set (Mx k r)} (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    {X : Mx k r} (hX : inLieLev k r i X) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RdV X f g = RdV X f' g := by
  unfold RdV
  apply Filter.EventuallyEq.deriv_eq
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (exp_curve_cont X)
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ D := by
    apply hcont.continuousAt.preimage_mem_nhds
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact hD.mem_nhds hg.2
  filter_upwards [hmem] with t ht
  exact h _ ⟨glev_mul hg.1 (exp_mem_glev hX t), ht⟩

theorem capelli_operator_congruence : CapCongr := by
  intro E _ _ k r i D a b f f' hD h g hg
  show EabH (Hpk k r) _ _ f g = EabH (Hpk k r) _ _ f' g
  unfold EabH
  rw [rdV_congr hD h (hpart1_lie i a b) hg, rdV_congr hD h (hpart2_lie i a b) hg]

end QmCapCommW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.QuantumDeterminantCommutes
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace QmCapCommW

theorem quantum_determinant_commutes : QdetCommute := by
  intro A _ _ n E hE u v
  have hc : ∀ c d, Commute (qdet E u) (E c d) := fun c d => qDetCentral A n E hE u c d
  have hT : ∀ w a b, Commute (qdet E u) (Tm E w a b) := by
    intro w a b
    unfold Tm
    refine Commute.add_right ?_ (hc a b)
    split_ifs
    · exact Algebra.commute_algebraMap_right w _
    · exact Commute.zero_right _
  have key : Commute (qdet E u) (qdet E v) := by
    show Commute (qdet E u) (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin n => Tm E (v - (k : ℂ)) (id (σ k)) (id k)).prod)
    refine Commute.sum_right _ _ _ fun σ _ => ?_
    refine Commute.mul_right Commute.intCast_right ?_
    refine Commute.list_prod_right _ _ fun y hy => ?_
    simp only [List.mem_ofFn] at hy
    obtain ⟨k, rfl⟩ := hy
    exact hT _ _ _
  exact key.eq

end QmCapCommW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Transfer
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace QmCapCommW

abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}


open Classical in
def ext0 {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [Zero E] (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0

section Core

variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma extension_by_zero_apply {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext0 φ g = φ ⟨g, hg⟩ := by
  simp only [ext0, dif_pos hg]

lemma matrixExtendByZero_add (φ ψ : Pt k r i D → E) : ext0 (φ + ψ) = fun h => ext0 φ h + (1 : ℂ) • ext0 ψ h := by
  funext h
  simp only [ext0]
  split_ifs <;> simp

lemma extendByZeroOffSubset_smul_apply (c : ℂ) (φ : Pt k r i D → E) : ext0 (c • φ) = fun h => (fun _ => (0 : E)) h + c • ext0 φ h := by
  funext h
  simp only [ext0]
  split_ifs <;> simp

lemma matrixExtendByZero_zero : ext0 (0 : Pt k r i D → E) = fun _ => 0 := by
  funext h
  simp only [ext0]
  split_ifs <;> simp

lemma smooth_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgl => ?_⟩
  rw [← h g ⟨hgl, hg.2⟩]
  exact hfF g hg.1 hgl

lemma smooth_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma smooth_lin {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') (c : ℂ) :
    SmoothLev k r i D (fun g => f g + c • f' g) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, hg1, hF1, hf1⟩ := hf g₀ hg₀
  obtain ⟨U2, F2, hU2, hg2, hF2, hf2⟩ := hf' g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + c • F2 g, hU1.inter hU2, ⟨hg1, hg2⟩,
    (hF1.mono Set.inter_subset_left).add ((hF2.mono Set.inter_subset_right).const_smul c),
    fun g hg hgl => ?_⟩
  show f g + c • f' g = F1 g + c • F2 g
  rw [hf1 g hg.1 hgl, hf2 g hg.2 hgl]


variable (k r i D E) in
def SS : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext0 φ)}
  add_mem' {φ ψ} hφ hψ := by
    show SmoothLev k r i D (ext0 (φ + ψ))
    rw [matrixExtendByZero_add]; exact smooth_lin hφ hψ 1
  zero_mem' := by
    show SmoothLev k r i D (ext0 (0 : Pt k r i D → E))
    rw [matrixExtendByZero_zero]; exact smooth_zero
  smul_mem' c φ hφ := by
    show SmoothLev k r i D (ext0 (c • φ))
    rw [extendByZeroOffSubset_smul_apply]; exact smooth_lin smooth_zero hφ c

lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) : EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EH, EabH, RdV]

def TT (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1

lemma TT_mem (hP : EabPres) (hD : IsOpen D) {φ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E) (a b : Fin (mdim k r i)) :
    TT a b φ ∈ SS k r i D E := by
  have h1 := (hP E k r 0 i D a b (ext0 φ) (ext0 φ) 0 hD hφ hφ).1
  refine smooth_congr hD (fun g hg => ?_) h1
  exact (extension_by_zero_apply (φ := TT a b φ) hg).symm

lemma TT_add (hP : EabPres) (hD : IsOpen D) {φ ψ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E)
    (hψ : ψ ∈ SS k r i D E) (a b : Fin (mdim k r i)) : TT a b (φ + ψ) = TT a b φ + TT a b ψ := by
  funext p
  have h3 := (hP E k r 0 i D a b (ext0 φ) (ext0 ψ) 1 hD hφ hψ).2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext0 (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext0 ψ) p.1
  rw [matrixExtendByZero_add, h3, one_smul]

lemma TT_smul (hP : EabPres) (hD : IsOpen D) {φ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E) (c : ℂ)
    (a b : Fin (mdim k r i)) : TT a b (c • φ) = c • TT a b φ := by
  funext p
  have h3 := (hP E k r 0 i D a b (fun _ => (0 : E)) (ext0 φ) c hD smooth_zero hφ).2.2 p.1 p.2
  try dsimp only at h3
  show EH k r (posL k r i a) (posL k r i b) (ext0 (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1
  rw [extendByZeroOffSubset_smul_apply]
  try dsimp only
  rw [h3, eh_zero, zero_add]

def EE (hP : EabPres) (hD : IsOpen D) (a b : Fin (mdim k r i)) : Module.End ℂ (SS k r i D E) where
  toFun x := ⟨TT a b x.1, TT_mem hP hD x.2 a b⟩
  map_add' x y := Subtype.ext (TT_add hP hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (TT_smul hP hD x.2 c a b)

def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop := ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩

lemma EE_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (EE hP hD a b x).1 := by
  unfold Rep at h ⊢
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext0 x.1) g
  exact hC E k r i D a b F (ext0 x.1) hD (fun g' hg' => by rw [extension_by_zero_apply hg']; exact h g' hg') g hg

lemma rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E} {x : ι → SS k r i D E}
    (h : ∀ j, Rep (F j) (x j).1) : Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by
  unfold Rep at h ⊢
  intro g hg
  show ∑ j, c j • F j g = _
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, h j g hg]

lemma posL_inj {a b : Fin (mdim k r i)} (e : posL k r i a = posL k r i b) : a = b := by
  have h1 := congrArg Fin.val e
  simp only [posL, Fin.val_mk] at h1
  exact Fin.ext (by omega)

lemma Tm_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (EE hP hD) u a b x).1 := by
  have h1 := EE_rep hC hP hD h a b
  unfold Rep at h h1 ⊢
  intro g hg
  by_cases hab : a = b
  · subst hab
    first
      | simp [Formalism.QuantumDeterminants.Top, Formalism.REAL.Tm, Module.algebraMap_end_apply, h g hg, h1 g hg]
      | simp [Formalism.QuantumDeterminants.Top, Tm, Module.algebraMap_end_apply, h g hg, h1 g hg]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    first
      | simp [Formalism.QuantumDeterminants.Top, Formalism.REAL.Tm, hab, hne, h1 g hg]
      | simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h1 g hg]

lemma foldr_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    {F : Mx k r → E} {x : SS k r i D E} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons q l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    first
      | rw [Module.End.mul_apply]
      | rw [LinearMap.mul_apply]
    exact Tm_rep hC hP hD ih q.1 q.2.1 q.2.2

lemma qminor_apply (hP : EabPres) (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ)
    (x : SS k r i D E) :
    qminor (EE hP hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Module.End.mul_apply, List.map_ofFn]
  simp [Function.comp_def, Int.cast_smul_eq_zsmul]

lemma qdet_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (u : ℂ) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) : Rep (capL k r i u F) (qdet (EE hP hD) u x).1 := by
  unfold qdet capL
  rw [qminor_apply]
  unfold qminorOp
  have H := rep_sum (fun σ : Equiv.Perm (Fin (mdim k r i)) => (((Equiv.Perm.sign σ : ℤ) : ℂ)))
    (fun σ => foldr_rep hC hP hD (List.ofFn fun q : Fin (mdim k r i) => (u - ((q : ℕ) : ℂ), σ q, q)) h)
  simp only [List.map_ofFn, Function.comp_def, id] at H ⊢
  intro g hg
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  exact H g hg

lemma EE_gl (hC : CapCongr) (hP : EabPres) (hG : EabGlLev) (hD : IsOpen D) :
    GlRel (EE (E := E) (i := i) hP hD) := by
  unfold GlRel
  unfold EabGlLev at hG
  have loc : ∀ (a b c d : Fin (mdim k r i)) (x : SS k r i D E) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D),
      (EE hP hD a b (EE hP hD c d x)).1 ⟨g, hg⟩ =
        EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) (ext0 x.1)) g := by
    intro a b c d x g hg
    show EH k r (posL k r i a) (posL k r i b) (ext0 (TT c d x.1)) g = _
    exact (hC E k r i D a b (EH k r (posL k r i c) (posL k r i d) (ext0 x.1)) (ext0 (TT c d x.1)) hD
      (fun g' hg' => by rw [extension_by_zero_apply hg']; rfl) g hg).symm
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext q
  obtain ⟨g, hg⟩ := q
  have key := hG E k r i D a b c d (ext0 x.1) hD x.2 g hg
  change (EE hP hD a b (EE hP hD c d x)).1 ⟨g, hg⟩ - (EE hP hD c d (EE hP hD a b x)).1 ⟨g, hg⟩ = _
  rw [loc a b c d x g hg, loc c d a b x g hg, key]
  split_ifs <;> rfl

end Core

theorem capelli_operator_transfer : CapTransfer := by
  unfold CapTransfer
  intro hC hQ hP hG
  unfold CapCommute
  unfold QdetCommute at hQ
  intro E _ _ k r i D f hD hf g hg u v
  have hmem : (fun q : Pt k r i D => f q.1) ∈ SS k r i D E :=
    smooth_congr hD (fun g' hg' => (extension_by_zero_apply (φ := fun q : Pt k r i D => f q.1) hg').symm) hf
  let x : SS k r i D E := ⟨fun q => f q.1, hmem⟩
  have hx : Rep f x.1 := fun _ _ => rfl
  have h1 := qdet_rep hC hP hD u (qdet_rep hC hP hD v hx)
  have h2 := qdet_rep hC hP hD v (qdet_rep hC hP hD u hx)
  have hcomm := hQ (Module.End ℂ (SS k r i D E)) (mdim k r i) (EE hP hD) (EE_gl hC hP hG hD) u v
  rw [h1 g hg, h2 g hg]
  have := congrArg (fun T => (T x).1 ⟨g, hg⟩) hcomm
  simpa only [Module.End.mul_apply] using this

end QmCapCommW
end
end

