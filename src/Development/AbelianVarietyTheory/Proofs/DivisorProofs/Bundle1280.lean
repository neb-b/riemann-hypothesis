module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform.RealSchwartz

private theorem norm_add_smul_single_sub_le_of_hasDerivAt_bound {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) (i : Fin k) (t : Fin k → ℝ) (a : ℝ) :
    ‖φ (t + a • (Pi.single i (1 : ℝ) : Fin k → ℝ)) - φ t‖ ≤ B i * |a| := by
  set e : Fin k → ℝ := Pi.single i (1 : ℝ) with he
  have hder : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ (t + u • e)) (φ' i (t + s • e)) s := by
    intro s
    have h0 : HasDerivAt (fun u : ℝ => φ (t + s • e + u • e)) (φ' i (t + s • e)) (s - s) := by
      rw [sub_self]; exact hd i (t + s • e)
    have h1 := HasDerivAt.scomp (h := fun u : ℝ => u - s) s h0 ((hasDerivAt_id' s).sub_const s)
    rw [one_smul] at h1
    have hf : (fun u : ℝ => φ (t + u • e)) = ((fun u : ℝ => φ (t + s • e + u • e)) ∘ fun u : ℝ => u - s) := by
      funext u
      simp only [Function.comp_apply]
      congr 1
      rw [sub_smul]; abel
    rw [hf]
    exact h1
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (f := fun u : ℝ => φ (t + u • e)) (f' := fun s => φ' i (t + s • e))
    (fun s _ => (hder s).hasDerivWithinAt) (fun s _ => hB i _) convex_univ (Set.mem_univ 0) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem continuous_of_bdd_partials {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) : Continuous φ := by

  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  set M : ℝ := ∑ i, B i with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hB0 i
  have hBM : ∀ i, B i ≤ M := fun i => Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)

  have key : ∀ x y : Fin k → ℝ, ‖φ y - φ x‖ ≤ (k * M) * ‖y - x‖ := by
    intro x y
    let p : ℕ → Fin k → ℝ := fun j l => if (l : ℕ) < j then y l else x l
    have hp0 : p 0 = x := by funext l; simp [p]
    have hpk : p k = y := by funext l; simp [p, l.isLt]
    have hstep : ∀ j (hj : j < k), p (j + 1) =
        p j + (y ⟨j, hj⟩ - x ⟨j, hj⟩) • (Pi.single (⟨j, hj⟩ : Fin k) (1 : ℝ) : Fin k → ℝ) := by
      intro j hj
      funext l
      simp only [p, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases h : l = ⟨j, hj⟩
      · subst h; simp
      · have hne : (l : ℕ) ≠ j := fun h' => h (Fin.ext h')
        simp only [h, ↓reduceIte, mul_zero, add_zero]
        by_cases hl : (l : ℕ) < j
        · simp [hl, show (l : ℕ) < j + 1 by omega]
        · simp [hl, show ¬ (l : ℕ) < j + 1 by omega]
    have hind : ∀ j, j ≤ k → ‖φ (p j) - φ x‖ ≤ j * (M * ‖y - x‖) := by
      intro j
      induction j with
      | zero => intro _; simp [hp0]
      | succ j ih =>
        intro hj
        have hjk : j < k := hj
        have h1 := norm_add_smul_single_sub_le_of_hasDerivAt_bound φ φ' hd B hB ⟨j, hjk⟩ (p j) (y ⟨j, hjk⟩ - x ⟨j, hjk⟩)
        rw [← hstep j hjk] at h1
        have hc : |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ ‖y - x‖ := by
          have := norm_le_pi_norm (y - x) ⟨j, hjk⟩
          simpa [Real.norm_eq_abs] using this
        have h2 : B ⟨j, hjk⟩ * |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ M * ‖y - x‖ :=
          mul_le_mul (hBM _) hc (abs_nonneg _) hM0
        calc ‖φ (p (j + 1)) - φ x‖ ≤ ‖φ (p (j + 1)) - φ (p j)‖ + ‖φ (p j) - φ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ M * ‖y - x‖ + j * (M * ‖y - x‖) := add_le_add (h1.trans h2) (ih (by omega))
          _ = ((j + 1 : ℕ) : ℝ) * (M * ‖y - x‖) := by push_cast; ring
    have := hind k le_rfl
    rw [hpk] at this
    calc ‖φ y - φ x‖ ≤ k * (M * ‖y - x‖) := this
      _ = (k * M) * ‖y - x‖ := by ring
  refine (LipschitzWith.of_dist_le' (K := (k : ℝ) * M) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact key y x

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform.RealSchwartz

variable {F : Type} [Field F] [NumberField F]

theorem continuous_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : v.IsReal
  · have hE := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.1 ⟨v, hv⟩ := by
      funext y
      have h0 := congrArg (fun z => z.1 ⟨v, hv⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_fst
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have hE := (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbedding v ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.2 ⟨v, hc⟩ := by
      funext y
      have h0 := congrArg (fun z => z.2 ⟨v, hc⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_snd

theorem embR_add {N : ℕ} (a b : Fin N → mixedEmbedding.mixedSpace F) :
    (embR (a + b) : Fin N → AF F) = embR a + embR b := by
  funext i
  simp only [embR, Pi.add_apply, map_add (f := _)]
  exact (congrArg (pairA F _) (add_zero (0 : Af F))).symm.trans rfl

theorem embR_zero {N : ℕ} : (embR (0 : Fin N → mixedEmbedding.mixedSpace F) : Fin N → AF F) = 0 := by
  funext i
  simp only [embR, pairA, Pi.zero_apply, map_zero]
  rfl

theorem continuous_embR {N : ℕ} : Continuous (embR : (Fin N → mixedEmbedding.mixedSpace F) → Fin N → AF F) := by
  apply continuous_pi
  intro i
  show Continuous fun t : Fin N → mixedEmbedding.mixedSpace F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  exact (continuous_mixedSpace_symm.comp (continuous_apply i)).prodMk continuous_const

theorem fin_embR {N : ℕ} (t : Fin N → mixedEmbedding.mixedSpace F) : fin (embR t : Fin N → AF F) = 0 := by
  funext l
  first
  | rfl
  | simp [fin, embR, pairA, sndA]

def lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : ℝ →+ VA F N where
  toFun s := (embR (s • v), 0)
  map_zero' := by rw [zero_smul, embR_zero]; rfl
  map_add' a b := by rw [add_smul, embR_add, Prod.mk_add_mk, add_zero]

theorem isRealLine_lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : IsRealLine (lineR v) := by
  refine ⟨?_, fun t => ⟨fin_embR (t • v), ?_⟩⟩
  · show Continuous fun s : ℝ => ((embR (s • v), 0) : VA F N)
    exact (continuous_embR.comp (continuous_id.smul continuous_const)).prodMk continuous_const
  · funext l
    first
    | rfl
    | simp [fin, sndA]

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform


open RealSchwartz in
theorem schwartz_invV_realTranslate : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  intro F _ _ N _ ψ lam ν _ 𝓓 _ _ 𝒱 _ hder hdec f hf x

  let E := Fin N → mixedEmbedding.mixedSpace F
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv

  let V : Set ((Fin (Module.finrank ℝ E) → ℝ) → ℂ) :=
    {φ | ∃ g ∈ 𝒱, φ = fun s => invV ψ ν 𝓓 g (x + embR (L s))}

  have hpart : ∀ g ∈ 𝒱, ∀ i : Fin (Module.finrank ℝ E), ∃ g' ∈ 𝒱, ∀ s,
      HasDerivAt (fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))))
        (invV ψ ν 𝓓 g' (x + embR (L s))) 0 := by
    intro g hg i
    obtain ⟨g', hg', hd⟩ := hder g hg (lineR (L (Pi.single i (1 : ℝ)))) (isRealLine_lineR _)
    refine ⟨g', hg', fun s => ?_⟩
    have h := hd (x + embR (L s))
    have heq : (fun u : ℝ => invV ψ ν 𝓓 (heisV ψ (lineR (L (Pi.single i (1 : ℝ))) u) g) (x + embR (L s))) =
        fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))) := by
      funext u
      rw [show lineR (L (Pi.single i (1 : ℝ))) u = (embR (u • L (Pi.single i (1 : ℝ))), 0) from rfl,
        invV_heisV_fst, map_add, map_smul, embR_add, add_assoc]
    rwa [heq] at h

  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨g, hg, rfl⟩
    choose g' hg' hd' using hpart g hg
    have hb : ∀ i, ∃ C : ℝ, ∀ s, ‖invV ψ ν 𝓓 (g' i) (x + embR (L s))‖ ≤ C := by
      intro i
      obtain ⟨C, hC⟩ := hdec (g' i) (hg' i) x 0
      exact ⟨C, fun s => by simpa using hC (L s)⟩
    choose B hB using hb
    exact continuous_of_bdd_partials _ (fun i s => invV ψ ν 𝓓 (g' i) (x + embR (L s)))
      (fun i t => hd' i t) B hB
  have hclosed : ∀ φ ∈ V, ∀ i : Fin (Module.finrank ℝ E), ∃ φ' ∈ V, ∀ s : Fin (Module.finrank ℝ E) → ℝ,
      HasDerivAt (fun u : ℝ => φ (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ))) (φ' s) 0 := by
    rintro φ ⟨g, hg, rfl⟩ i
    obtain ⟨g', hg', hd'⟩ := hpart g hg i
    exact ⟨_, ⟨g', hg', rfl⟩, hd'⟩

  have hdecV : ∀ φ ∈ V, ∀ n : ℕ, ∃ C : ℝ, ∀ s, ‖s‖ ^ n * ‖φ s‖ ≤ C := by
    rintro φ ⟨g, hg, rfl⟩ n
    obtain ⟨C, hC⟩ := hdec g hg x n
    refine ⟨‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C, fun s => ?_⟩
    have hs : ‖s‖ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖ := by
      have h := (L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).le_opNorm (L s)
      simpa using h
    calc ‖s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖
        ≤ (‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖) ^ n *
            ‖invV ψ ν 𝓓 g (x + embR (L s))‖ := by gcongr
      _ = ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n *
            (‖L s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖) := by ring
      _ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C := by
            gcongr
            exact hC (L s)
  obtain ⟨_, hS⟩ := GlobalTheory.Unf.PartialClass.smooth_schwartz _ V hcont hclosed
  obtain ⟨g0, hg0⟩ := hS hdecV _ ⟨f, hf, rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g0, fun t => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  show invV ψ ν 𝓓 f (x + embR (L (L.symm t))) = _
  rw [L.apply_symm_apply]

end GlobalTheory.ThetaTransform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.RelDimOfDim

theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq :
    ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ),
      Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  intro F _ X _ q n hq hn
  have x₀ : X := Classical.arbitrary X
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected q x₀
  have h := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q d hd
  rw [hn] at h
  have hdn : d = n := by exact_mod_cast h.symm
  exact hdn ▸ hd

end GlobalTheory.RelDimOfDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponent
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

theorem smoothing_growth_exponent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α →
    ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) →
    ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  intro E _ _ _ a ν _ α hα f C N hC
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  have hK : IsCompact (tsupport α) := hα.2.1
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ tsupport α, ‖x‖ ≤ M ∧ ‖toL (Matrix.of x)⁻¹‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn (continuousOn_toL_inv.mono hα.2.2)
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  set c : ℝ := 1 + a * M with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) * M := by positivity
    linarith
  refine ⟨(∫ x, ‖α x‖ ∂ν) * C * c ^ N, fun y => ?_⟩
  have hb : ∀ x, ‖α x * chart f (infGL E a y) x‖ ≤ ‖α x‖ * (C * c ^ N * height y ^ N) := by
    intro x
    by_cases hx : x ∈ tsupport α
    · obtain ⟨u, hu⟩ : IsUnit (Matrix.of x) := hα.2.2 hx
      have hxu : x = toL u.val := by rw [hu]; rfl
      subst hxu
      obtain ⟨m1, m2⟩ := hM _ hx
      have m2' : ‖toL (u⁻¹).val‖ ≤ M := by rw [Matrix.coe_units_inv]; exact m2
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [chart_val, ← map_mul]
      refine (hC (y * u)).trans ?_
      have hh : height (y * u) ≤ c * height y := by
        have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
          rw [_root_.mul_inv_rev]; rfl
        have p1 := norm_toL_mul_le y.val u.val
        have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
        have n1 := norm_nonneg (toL y.val)
        have n2 := norm_nonneg (toL (y⁻¹).val)
        have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
          calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
            _ = a * M * ‖toL y.val‖ := by ring
        have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
        have aM : 0 ≤ (a : ℝ) * M := by positivity
        unfold height
        rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2, hc]
        nlinarith
      calc C * height (y * u) ^ N ≤ C * (c * height y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * u)]) hh N) C0
        _ = C * c ^ N * height y ^ N := by rw [mul_pow, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  change ‖∫ x, α x * chart f (infGL E a y) x ∂ν‖ ≤ _
  have hi : Integrable (fun x => ‖α x‖) ν :=
    hα.1.continuous.norm.integrable_of_hasCompactSupport hα.2.1.norm
  refine (norm_integral_le_of_norm_le (hi.mul_const _) (.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const]
  ring

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompact
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjKinf (k : Kinf E a) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse
    ((lmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))).comp (rmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))))
    ((lmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))).comp (rmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))))
    (fun x => by
      change toL (star (k : Matrix (Fin a) (Fin a) (Cinf E)) * ((k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) * (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]; rfl)
    (fun x => by
      change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * (k : Matrix (Fin a) (Fin a) (Cinf E))) * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.one_mul]; rfl)

theorem conjKinf_apply (k : Kinf E a) (x : Lie E a) :
    conjKinf k x = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) := by
  change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = _
  rw [Matrix.mul_assoc]

def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w‖ ^ 2

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem trace_mul_conjTranspose_cinf (M : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    (M * M.conjTranspose).trace w = ((∑ i, ∑ j, ‖M i j w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_apply,
    Pi.mul_apply, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem frobSq_eq (x : Lie E a) :
    frobSq x = ∑ w, ((Matrix.of x * (Matrix.of x).conjTranspose).trace w).re := by
  simp only [frobSq, trace_mul_conjTranspose_cinf, Complex.ofReal_re]; rfl

theorem frobSq_conjKinf (k : Kinf E a) (x : Lie E a) : frobSq (conjKinf k x) = frobSq x := by
  rw [frobSq_eq, frobSq_eq, conjKinf_apply]
  have h : ∀ M : Matrix (Fin a) (Fin a) (Cinf E),
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
        ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))).conjTranspose =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (M * M.conjTranspose) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro M
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (k : Matrix (Fin a) (Fin a) (Cinf E))) (k : Matrix (Fin a) (Fin a) (Cinf E)),
      Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]
  rw [show Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
    (k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) from rfl, h,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

theorem norm_le_one_of_frobSq (x : Lie E a) (h : frobSq x < 1) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | (apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one ..)

theorem continuous_frobSq : Continuous (frobSq : Lie E a → ℝ) := by
  unfold frobSq
  fun_prop

theorem measurePreserving_conjKinf (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (k : Kinf E a) :
    MeasurePreserving (conjKinf k) ν ν := by
  refine ⟨(conjKinf k).continuous.measurable, ?_⟩
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hdet : LinearMap.det ((conjKinf k : Lie E a ≃L[ℝ] Lie E a).toLinearEquiv.toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have e := Measure.map_linearMap_addHaar_eq_smul_addHaar ν hdet
  change Measure.map (conjKinf k) ν = _ at e
  set B : Set (Lie E a) := frobSq ⁻¹' Set.Iio 1
  have hBo : IsOpen B := isOpen_Iio.preimage continuous_frobSq
  have hB0 : (0 : Lie E a) ∈ B := by simp [B, frobSq]
  have hpos : ν B ≠ 0 := (hBo.measure_pos ν ⟨0, hB0⟩).ne'
  have hfin : ν B ≠ ⊤ := (measure_mono fun x hx => (mem_closedBall_zero_iff.2 (norm_le_one_of_frobSq x hx))).trans_lt
    (measure_closedBall_lt_top (μ := ν) (x := (0 : Lie E a)) (r := 1)) |>.ne
  have hpre : conjKinf k ⁻¹' B = B := by
    ext x; simp [B, frobSq_conjKinf]
  have h1 := congrArg (fun m : Measure (Lie E a) => m B) e
  simp only [Measure.map_apply (conjKinf k).continuous.measurable hBo.measurableSet, hpre, Measure.smul_apply,
    smul_eq_mul] at h1
  have hc := (ENNReal.mul_eq_right hpos hfin).1 h1.symm
  rw [e, hc, one_smul]

theorem smoothing_rt_Kinf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a))
    [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : KInv α) (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a) :
    smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  unfold smoothing
  rw [chart_rt_inf, chart_mul, ← (measurePreserving_conjKinf ν k).integral_comp (conjKinf k).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  congr 1
  · rw [conjKinf_apply]; exact hα k x
  · congr 1
    rw [conjKinf_apply]
    change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
      (k : Matrix (Fin a) (Fin a) (Cinf E))) = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x)
    rw [Matrix.mul_assoc _ (star _), Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLocFrame

theorem uAt_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  intro F E _ _ _ _ _ σ v n X L _ ι hι g A hg u hu
  have hent : ∀ i j, (mat g - 1) i j = ι ((A - 1) i j) := by
    intro i j
    rw [hg]
    by_cases h : i = j
    · subst h
      simp [Matrix.one_apply, map_sub]
      abel
    · simp [Matrix.one_apply, h, map_sub]
  ext i j
  have h1 : At (evFin F v) ((mat g - 1) i j) := (hι _).2 ⟨_, (hent i j).symm⟩
  simpa using h1 u hu

end GlobalTheory.InertLocFrame
end

