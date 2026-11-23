module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix NumberField

noncomputable section

namespace DualLatticeBasisExistsAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem eq_zero_of_dotProduct_gens (F : HermLattice K i) (s : Finset (Fin i → K))
    (hs : Submodule.span (𝓞 K) (s : Set (Fin i → K)) = F.lattice) (φ : Fin i → K)
    (h : ∀ g ∈ s, φ ⬝ᵥ g = 0) : φ = 0 := by
  let L : (Fin i → K) →ₗ[K] K :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := dotProduct_add φ
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have h1 : F.lattice ≤ (LinearMap.ker L).restrictScalars (𝓞 K) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    exact h g hg
  have h2 : Submodule.span K (F.lattice : Set (Fin i → K)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    intro x hx
    exact h1 hx
  rw [F.span_eq, top_le_iff] at h2
  funext j
  have hj : Pi.single j (1 : K) ∈ LinearMap.ker L := by rw [h2]; trivial
  have : φ ⬝ᵥ Pi.single j (1 : K) = 0 := hj
  simpa [dotProduct_single] using this

theorem dualLattice_fg (F : HermLattice K i) : (dualLattice F).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let G : (Fin i → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ g => φ ⬝ᵥ (g : Fin i → K)
      map_add' := fun φ ψ => by funext g; simp [add_dotProduct]
      map_smul' := fun c φ => by
        funext g
        show (c • φ) ⬝ᵥ (g : Fin i → K) = c • (φ ⬝ᵥ (g : Fin i → K))
        exact smul_dotProduct c φ _ }
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    refine eq_zero_of_dotProduct_gens F s hs φ (fun g hg => ?_)
    exact congrFun hφ ⟨g, hg⟩

  let ι : (s → 𝓞 K) →ₗ[ℤ] (s → K) :=
    LinearMap.pi (fun g => ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).comp (LinearMap.proj g))
  have hle : (dualLattice F).map G ≤ LinearMap.range ι := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ g : s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = φ ⬝ᵥ (g : Fin i → K) := fun g =>
      hφ g (hs ▸ Submodule.subset_span g.2)
    choose a ha using hv
    exact ⟨a, funext fun g => ha g⟩
  have hfg : ((dualLattice F).map G).FG := by
    have e : (dualLattice F).map G = (((dualLattice F).map G).comap ι).map ι := by
      rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
    rw [e]
    exact (IsNoetherian.noetherian _).map ι
  exact Submodule.fg_of_fg_map_injective G hG hfg

end DualLatticeBasisExistsAlt


open DualLatticeBasisExistsAlt in
theorem DualLatticeBasisExists.proof : DualLatticeBasisExists.Statement := by
  intro K _ _ i F
  classical
  have : Module.Finite ℤ (dualLattice F) := Module.Finite.iff_fg.mpr (dualLattice_fg F)
  exact ⟨Module.Free.ChooseBasisIndex ℤ (dualLattice F), inferInstance, inferInstance,
    ⟨Module.Free.chooseBasis ℤ (dualLattice F)⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineConj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding

noncomputable section

namespace DualLineConjugation

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)


omit [Fintype T] [DecidableEq T] in
theorem conj_mulVec (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]

theorem recover_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]

theorem re_conj_form {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, mulVec, map_sum, map_mul]

theorem normSq_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)

end DualLineConjugation

theorem DualLineConj.proof : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLineOfLargeDegreeDual
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem LineOfLargeDegreeFromZ.proofDual (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by
  intro hZ1 hZ2 hEx K _ _ i hi F ε hε
  obtain ⟨II, hII⟩ := hEx
  obtain ⟨T, _, _, ⟨b⟩⟩ := hBasis K i F
  have hb := hBij K i F T b
  set A := dualLine F b hb with hA
  set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he
  by_contra hne
  push Not at hne
  have hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W →
      e * degC W ≤ II Unit (dualBlocks T) W 1 ![A] := by
    intro W hW1 hPW
    obtain ⟨hdeg, K', iF, iN, iA, v, hv, hline⟩ := hPt K i F T b hb II hII W hW1 hPW
    have hlt := hne K' iF iN iA v hv
    rw [hline] at hlt
    have hd : (0 : ℝ) < degC W := by exact_mod_cast hdeg
    have h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W := by
      rw [neg_div] at hlt
      linarith
    exact ((lt_div_iff₀ hd).mp h1).le
  have hV : IsArithVar (dualIdeal b) (i - 1 + 1) := by
    rw [Nat.sub_add_cancel hi]; exact hArith K i F T b hi
  have hZ := hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV
    bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW
  rw [Nat.sub_add_cancel hi] at hZ
  have hT := hTop hZ2 K i F T b hb II hi hII
  have hG := hPos K i F T b hb hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1) := hZ.trans hT
  have : (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0 := by
    rw [he] at key
    nlinarith
  have : 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) :=
    mul_pos (mul_pos hi' hε) hG
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ReMulOfPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem gramAt_single {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def HermLattice.withStdMetric {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def DualTopMetricChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopLatticeChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice (HermLattice.standard K i)))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) =
      II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine (HermLattice.standard K i) b' hb') -
        F.withStdMetric.degree *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) *
        II (Fin 1) (plBlocks 1 1 (i - 1)) (grassIdeal 1 1 (i - 1)) (1 * 1 * (i - 1) + 1)
          (fun _ => fsMulti (plBlocks 1 1 (i - 1)))

def DualGeomDegStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
      (Module.finrank ℚ K : ℝ) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def HermLattice.scaledExample : HermLattice ℚ 1 where
  lattice := (HermLattice.standard ℚ 1).lattice
  fg := (HermLattice.standard ℚ 1).fg
  span_eq := (HermLattice.standard ℚ 1).span_eq
  metric := fun _ => Matrix.diagonal fun _ => (4 : ℂ)
  posDef := fun _ => Matrix.PosDef.diagonal fun _ => by norm_num
  conj := fun _ => by
    ext a c
    by_cases h : a = c <;> simp [h, map_ofNat]

end

end GroundTheory.Heights₂.Heights
end

