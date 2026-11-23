module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem sFinite_vol : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  intro D ρ m vb vU
  constructor
  · obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D ρ m
    haveI : IsTopologicalAddGroup (Mx D ρ m) := i1
    haveI : LocallyCompactSpace (Mx D ρ m) := i2
    haveI : SecondCountableTopology (Mx D ρ m) := i3
    haveI : vb.μ.IsAddHaarMeasure := vb.covol.1
    haveI : SigmaFinite vb.μ := Measure.IsAddHaarMeasure.sigmaFinite _
    infer_instance
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.UnitU.topology D ρ
    haveI : LocallyCompactSpace (UX D ρ) := i1
    haveI : SecondCountableTopology (UX D ρ) := i2
    haveI : vU.ν.IsHaarMeasure := vU.unit.1
    haveI : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite _
    infer_instance

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
section
noncomputable section

namespace GlobalTheory.ChainOnto.SatHeckeChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem heckeVec_eq_smul_of_isSatVecGL :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ),
      ∀ φ ∈ Hecke ℂ (KGL w (n := n)), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V),
          IsSatVecGL w ρ x B → heckeVec ρ (KGL w (n := n)) φ x = z • x := by
  intro E _ _ w n B φ hφ
  by_cases hB : B.card = n
  · obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
      obtain ⟨l, rfl⟩ := Quot.exists_rep B
      obtain rfl : l.length = n := hB
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
    obtain ⟨x₀, hx₀⟩ := (hasSatGL_psFunGL (w := w) α).exists_vec
    obtain ⟨z, hz, -⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx₀ φ hφ
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    obtain ⟨c, e1, e2⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx φ hφ
    have e : z = c := smul_left_injective ℂ hx₀.1 (hz.symm.trans e1)
    rw [e2, e]
  · exact ⟨0, fun V _ _ ρ x hx => absurd hx.2.2.1 hB⟩

end GlobalTheory.ChainOnto.SatHeckeChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBoun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SBUnif

theorem uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) → ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧ ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := by
  intro k _ _ _ _ n n' _ _ _ _ Ψ hΨ
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset (GlobalTheory.LocMod.Inhab.eventually_invariant hΨ)
  have hinv : ∀ X u, u ∈ GlobalTheory.LocMod.Inhab.box n n' a → Ψ (X + u) = Ψ X := fun X u hu =>
    GlobalTheory.LocMod.Inhab.invariant_of_tsupport (K := GlobalTheory.LocMod.Inhab.box n n' a) (fun u hu => ha u hu) u hu X
  obtain ⟨R, hR⟩ := GlobalTheory.LocMod.Inhab.exists_cosets hΨ a
  let F : Finset k := insert (a : k) ((R ×ˢ (Finset.univ ×ˢ Finset.univ)).image fun x => x.1 x.2.1 x.2.2)
  obtain ⟨b, -, hb⟩ := F.exists_max_image (fun x => valuation k x) ⟨_, Finset.mem_insert_self _ _⟩
  have hab : valuation k (a : k) ≤ valuation k b := hb _ (Finset.mem_insert_self _ _)
  have ha0 : valuation k (a : k) ≠ 0 := by simp
  have hb0 : valuation k b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) zero_le')
  have hsupp : ∀ X, Ψ X ≠ 0 → ∀ i j, valuation k (X i j) ≤ valuation k b := by
    intro X hX i j
    obtain ⟨r, hr, hXr⟩ := hR X hX
    have h1 : valuation k ((X - r) i j) ≤ valuation k (a : k) := hXr i j
    have h2 : valuation k (r i j) ≤ valuation k b :=
      hb _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(r, i, j), by simp [hr], rfl⟩))
    have e : X i j = r i j + (X - r) i j := by simp
    rw [e]
    exact Valuation.map_add_le _ h2 (h1.trans hab)
  have hq := GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one (k := k)
  obtain ⟨e₁, he₁⟩ := exists_pow_lt₀ hq (Units.mk0 _ ha0)
  obtain ⟨e₂, he₂⟩ := exists_pow_lt₀ hq (Units.mk0 _ (inv_ne_zero hb0))
  have hpos : 0 < resCard k := Nat.card_pos
  refine ⟨resCard k ^ (e₁ + e₂), pow_pos hpos _, ?_, ?_⟩
  · intro X Y hY
    refine hinv X _ fun r q => ?_
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, Nat.cast_pow, map_pow]
    have hY' : valuation k (Y r q) ≤ 1 := hY r q
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (Y r q)
        ≤ valuation k (resCard k : k) ^ e₁ * 1 :=
          mul_le_mul' (pow_le_pow_right_of_le_one' hq.le (Nat.le_add_right _ _)) hY'
      _ ≤ valuation k (a : k) := by rw [mul_one]; exact he₁.le
  · intro X hX i j
    show valuation k _ ≤ 1
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (X i j)
        ≤ (valuation k b)⁻¹ * valuation k b :=
          mul_le_mul' ((pow_le_pow_right_of_le_one' hq.le (Nat.le_add_left _ _)).trans he₂.le) (hsupp X hX i j)
      _ = 1 := inv_mul_cancel₀ hb0

end GlobalTheory.SBUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstances
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo

section

variable (I : AutInst)

theorem hform_eq_dot {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : Formalism.UG.hform (starRingEnd K) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_NInf_of_NA {W : Submodule I.E (Fin I.n → I.E)} {m : I.Ginf} (hm : ((m, 1) : I.GA) ∈ I.NA W) :
    m ∈ CompanionTheory.D.gk.RF.NInf I W := by
  intro v
  obtain ⟨h1, h2, h3⟩ := hm.1 v
  show CompanionTheory.D.gk.RF.Lowers (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) (uMat (m v) - 1)
  have hdet := CompanionTheory.D.gk.RF.P_det I v
  have hPi : I.P v * (I.P v)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hiP : (I.P v)⁻¹ * I.P v = 1 := nonsing_inv_mul _ hdet
  have hB : ∀ z, (I.P v * uMat (m v) * (I.P v)⁻¹ - 1) *ᵥ (I.P v *ᵥ z) =
      I.P v *ᵥ ((uMat (m v) - 1) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (I.P v)⁻¹ (I.P v), hiP,
      Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  have hWC : ∀ w ∈ CompanionTheory.D.gk.RF.Wv I W v, I.P v *ᵥ w ∈
      Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [CompanionTheory.D.gk.RF.P_atV]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hWv : ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      (I.P v)⁻¹ *ᵥ x ∈ CompanionTheory.D.gk.RF.Wv I W v := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hfP : ∀ w z, CompanionTheory.D.gk.RF.hf (Formalism.REAL.Jm (I.ε v)) w z =
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) (I.P v *ᵥ w) (I.P v *ᵥ z) := fun w z => by
    rw [hform_eq_dot, CompanionTheory.D.gk.RF.hf, ← I.P_spec v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      mulVec_mulVec, Matrix.mul_assoc]
  have hc1 : ∀ z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v),
      ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0 := fun z hz x hx => by
    have e : x = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ x) := by rw [mulVec_mulVec, hPi, one_mulVec]
    rw [e, ← hfP]
    exact hz _ (hWv x hx)
  have hc2 : ∀ z, (∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0) →
      z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) := fun z h w hw => by
    rw [hfP]
    exact h _ (hWC w hw)
  have inj : ∀ a : Fin I.n → ℂ, a = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ a) := fun a => by
    rw [mulVec_mulVec, hiP, one_mulVec]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · have := h1 _ (hWC w hw)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ w), this, mulVec_zero]
  · have := h2 _ (hc1 z hz)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ z)]
    exact hWv _ this
  · refine hc2 _ fun x hx => ?_
    have := h3 (I.P v *ᵥ z)
    rw [hB] at this
    exact this x hx

theorem shortCusp_holds : ShortCusp I := by
  intro U hU
  obtain ⟨M, hM, hMU⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I U hU
  obtain ⟨s₁, hs₁, hSI⟩ := CompanionTheory.D.gk.RF.short_isotropic_vector_of CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₁, hC₁, hCS⟩ := CompanionTheory.D.gk.RF.covolume_span I
  obtain ⟨C₂, hC₂, hCP⟩ := CompanionTheory.D.gk.RF.covolume_orthogonal_complement CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₃, hC₃, hNC⟩ := CompanionTheory.D.gk.RF.nilpotent_cover_of CompanionTheory.D.gk.RF.transport_to_standard_form CompanionTheory.D.gk.RF.gamSub
    CompanionTheory.D.gk.RF.nilpotent_lie_algebra CompanionTheory.D.gk.RF.nilpotent_subgroup_representation I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  have hD : 0 < 2 * (C₁ + C₂ + 1) := by positivity
  refine ⟨s₀, 1 / (2 * (C₁ + C₂ + 1)), C₃ * (C₁ + C₂), hs₀, by positivity, fun y η hη hηη₀ hc => ?_⟩
  have hηD : η * (2 * (C₁ + C₂ + 1)) ≤ 1 := (le_div_iff₀ hD).1 hηη₀
  have hη1 : η < 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηb : (C₁ + C₂) * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηa : 2 * C₁ * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  obtain ⟨u, hu, hu0, hus⟩ := hc
  have hc' : ∃ u ∈ CompanionTheory.D.gk.RF.IntV I, u ≠ 0 ∧ ‖CompanionTheory.D.gk.RF.vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    ⟨u, hu, hu0, hus⟩
  obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := CompanionTheory.D.gk.RF.successive_minima_gap I.E I.n (CompanionTheory.D.gk.RF.IntV I)
    (fun u => ‖CompanionTheory.D.gk.RF.vecAt I y u‖) s₀ η hs₀ hη hη1 hc'
  have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
  have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
  have hI : CompanionTheory.D.gk.RF.Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact CompanionTheory.D.gk.RF.mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
  have c1 := hCS y d w (η * t) hd (by positivity) hw
  have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
    by_contra h
    exact hn (hall u hu (not_le.1 h).le)
  have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
    have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
    have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
    have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
    rw [e]; linarith
  refine ⟨Submodule.span I.E (Set.range w), ⟨hne, fun x hx z hz => ?_⟩, fun m hm => ?_⟩
  · have := hI hz x hx
    rw [hform_eq_dot]
    exact this
  obtain ⟨γ, h1, -, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
    (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
    (c2.mono (le_add_of_nonneg_left (by positivity))) m (mem_NInf_of_NA I hm)
  obtain ⟨x, hxU, hx⟩ := hMU γ h1
  refine ⟨(γ, x), hx, hxU, fun v i j => (h3 v i j).trans ?_⟩
  rw [mul_assoc C₃]
  exact mul_le_mul_of_nonneg_left hρ hC₃.le

end

theorem shortCusp_all : ∀ I : AutInst, ShortCusp I := shortCusp_holds

end GlobalTheory.CuspGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SnocColumnsMovedByUpperUnitriangularIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.BlockUni

theorem unitri_isUnit {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (h0 : ∀ i j, j < i → A i j = 0) (h1 : ∀ i, A i i = 1) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hb : A.BlockTriangular id := fun i j h => h0 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [h1]

theorem snoc_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := by
  intro R _ n σ M w Y
  set x : Matrix (Fin n) (Fin (σ+1)) R := Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) with hx
  have hxc : ∀ k i, x k (Fin.castSucc i) = M k i := by intro k i; simp [hx]
  have hxl : ∀ k, x k (Fin.last σ) = w k := by intro k; simp [hx]
  have col : ∀ (U : Matrix (Fin (σ+1)) (Fin (σ+1)) R) k j,
      (x * U) k j = ∑ i, M k i * U (Fin.castSucc i) j + w k * U (Fin.last σ) j := by
    intro U k j; rw [Matrix.mul_apply, Fin.sum_univ_castSucc]; simp only [hxc, hxl]
  have Ycol : ∀ k j, (Y * x) k (Fin.castSucc j) = (Y * M) k j := by
    intro k j; simp only [Matrix.mul_apply, hxc]
  have Ylast : ∀ k, (Y * x) k (Fin.last σ) = (Y *ᵥ w) k := by
    intro k; simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hxl]
  constructor
  · rintro ⟨U, hU, hE⟩
    have hU' := (GlobalTheory.UniIndexPrime.mem_uniSub U).1 hU
    let u : Matrix (Fin σ) (Fin σ) R := Matrix.of fun i j => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.castSucc j)
    have hu0 : ∀ i j, j < i → u i j = 0 := fun i j h =>
      hU'.1 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.2 h)
    have hu1 : ∀ i, u i i = 1 := fun i => hU'.2 _
    refine ⟨(unitri_isUnit u hu0 hu1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hu0, hu1⟩,
      fun i => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.last σ), ?_, ?_⟩
    · ext k j
      have h := congrFun (congrFun hE k) (Fin.castSucc j)
      rw [Ycol, col] at h
      rw [h, IsUnit.unit_spec, Matrix.mul_apply]
      have h0 : (U : Matrix _ _ R) (Fin.last σ) (Fin.castSucc j) = 0 := hU'.1 _ _ (Fin.castSucc_lt_last j)
      simp [h0, u]
    · ext k
      have h := congrFun (congrFun hE k) (Fin.last σ)
      rw [Ylast, col, hU'.2 (Fin.last σ)] at h
      rw [h]; simp only [Pi.add_apply, Matrix.mulVec, dotProduct]; ring
  · rintro ⟨u, hu, v, h1, h2⟩
    have hu' := (GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu
    let U : Matrix (Fin (σ+1)) (Fin (σ+1)) R := Matrix.of fun a b =>
      Fin.lastCases (Fin.lastCases (1 : R) (fun _ => 0) b)
        (fun i => Fin.lastCases (v i) (fun j => (u : Matrix _ _ R) i j) b) a
    have Ucc : ∀ i j, U (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
      intro i j; simp [U]
    have Ucl : ∀ i, U (Fin.castSucc i) (Fin.last σ) = v i := by intro i; simp [U]
    have Ulc : ∀ j, U (Fin.last σ) (Fin.castSucc j) = 0 := by intro j; simp [U]
    have Ull : U (Fin.last σ) (Fin.last σ) = 1 := by simp [U]
    have hU0 : ∀ a b, b < a → U a b = 0 := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (lt_irrefl _)
        | cast j => exact Ulc j
      | cast i =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => rw [Ucc]; exact hu'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hab)
    have hU1 : ∀ a, U a a = 1 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact Ull
      | cast i => rw [Ucc]; exact hu'.2 i
    refine ⟨(unitri_isUnit U hU0 hU1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hU0, hU1⟩, ?_⟩
    rw [IsUnit.unit_spec]
    ext k b
    induction b using Fin.lastCases with
    | last =>
      rw [Ylast, col, h2, Ull]
      simp only [Ucl, Pi.add_apply, Matrix.mulVec, dotProduct]; ring
    | cast j =>
      rw [Ycol, col, h1, Matrix.mul_apply]
      simp only [Ucc, Ulc]; ring

end GlobalTheory.BlockUni
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitChar

theorem cont_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) →
    Continuous χ ∧ χ ≠ 1 := by
  intro D k _ _ _ _ p ψ χ hχ hψ
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  refine ⟨?_, ?_⟩
  · have h' : Continuous fun a : k => ((χ a : Circle) : ℂ) := by
      have he : (fun a : k => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hχ
      rw [he]; exact hc
    first
      | exact Circle.isEmbedding_coe.continuous_iff.2 h'
      | exact continuous_induced_rng.2 h'
  · intro h1
    obtain ⟨a, ha⟩ := GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
    apply ha
    rw [← hχ a, h1]
    simp

end GlobalTheory.FinPl.SplitChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticPairingLatticeAwaySupportedAtPlaceEqZe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffSympl

theorem placeIdem_smul_latO {D : D7} {S T : HSp D} {MS : Set (Fin S.rank → D.host.E)}
    {MT : Set (Fin T.rank → D.host.E)} {P : Pl D → Prop} {v : Pl D} (hv : ¬ P v) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) : ∀ u ∈ latO S T MS MT P, algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = 0 := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w 0
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [hP w hv, mul_zero]
      · rw [h0 w hw, zero_mul]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    rw [this, TensorProduct.zero_tmul]
  | zero => exact smul_zero _
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem symplO_off_eq_zero (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E))
    (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) : ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T,
    (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := by
  intro hv u hu x hx
  obtain ⟨ε, hε, he⟩ := p.above
  have hx' : (p.e + cA D p.e) • x = x := Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hx]
  have hc : cA D (p.e + cA D p.e) = p.e + cA D p.e := by rw [map_add (f := _), cA_cA, add_comm]
  rw [← hx', ← hc, ← GlobalTheory.PlaceModel.symplO_smul, he, placeIdem_smul_latO hv hε u hu,
    GlobalTheory.PlaceModel.symplO_zero_left]

end GlobalTheory.FinPl.OffSympl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_rational_translate_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h w, om (γ * g, γ' * h) f w = om (g, h) f (mt T γ'⁻¹ ⬝ w ⬝ mt S γ) := by
  first | exact @GlobalTheory.Unf.om_rat_mul | exact GlobalTheory.Unf.om_rat_mul | (intros; apply GlobalTheory.Unf.om_rat_mul <;> assumption)
end

