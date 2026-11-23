module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0012
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0011

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGNonunit
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix Pointwise

variable {D : D7} (X : HidaSetting D)

def eC : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F := 1 - X.ew - sigA X.B.I X.ew

theorem imA_eC_idem : eC X * eC X = eC X := by
  have h1 := X.ew_idem
  have h2 := X.ew_orth
  have h3 : sigA X.B.I X.ew * sigA X.B.I X.ew = sigA X.B.I X.ew := by rw [← map_mul, h1]
  simp only [eC]
  linear_combination h1 + h3 + 2 * h2

theorem imA_mL_mem (m : ℕ) {b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hb' : b ∈ mL X.B.I m) : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
  induction hb' using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
  | smul c y _ hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
    show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
    rw [smul_smul, smul_smul, mul_comm]

theorem imA_lat_fg (p : TypX X) : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).FG := by
  classical
  obtain ⟨m, b, hb', -, he⟩ := MassDataIdxK.latImage p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg
  refine ⟨(Finset.univ.image b), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hb' i
  · intro x hx
    have hx' : x ∈ (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
        Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) := hx
    rw [he] at hx'
    obtain ⟨c, hc, rfl⟩ := hx'
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i • b i = (⟨c i, hc i (Set.mem_univ _)⟩ : p.1.adicCompletionIntegers X.B.I.F) • b i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem imA_g_nonunit (p : TypX X) : ¬ IsUnit ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  intro hu
  have hr : ResArith X p := by
    have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
    have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
      have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
        (D.host.g_prime 1).ne_zero p.1).1 p.2
      unfold gOf
      split_ifs with h
      · exact h
      · exact hty.resolve_left h
    have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
        ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
      unfold gOf
      split_ifs
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
    obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
    exact ⟨hc, hmem, hn⟩
  obtain ⟨π, -, -⟩ : StResZ X p := stResZ_of X p hr
  have hd : gOf p ∣ X.B.g := by
    rw [X.g_eq]; unfold gOf; split_ifs
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hu' : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hu
  have h0 : π ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) = 0 := by
    rw [map_natCast, ZMod.natCast_self]
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have h1 := hu'.map π
  rw [h0] at h1
  exact not_isUnit_zero h1

theorem imA_n_pos : 0 < X.B.I.n := by
  rw [X.n_eq]
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem imA_ew_split (p : TypX X) :
    PI.FinKW.psiV X.B.I p.1 X.ew + PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) = 1 := by
  set ε := PI.FinKW.psiV X.B.I p.1 (eC X) with hε
  have hεi : ε * ε = ε := by rw [hε, ← map_mul, imA_eC_idem]
  let φ : (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) →ₗ[p.1.adicCompletionIntegers X.B.I.F]
      (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
    { toFun := fun u => ε • u
      map_add' := fun u w => smul_add _ _ _
      map_smul' := fun c u => smul_comm _ _ _ }
  have hφ : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ ≤
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    show ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l ∈
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := imA_mL_mem X X.B.g (X.ew_full _ hin)
    have hv : PI.FinKW.vecV X.B.I p.1 (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l := by
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    have h2 := congrArg (PI.FinKW.vecV X.B.I p.1) he
    rw [imA_vecV_smul', imA_vecV_smul', hv, map_natCast] at h2
    have h3 : ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l =
        ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) • PI.FinKW.vecV X.B.I p.1 y := by
      rw [Nat.cast_smul_eq_nsmul] at h2
      rw [hε, Nat.cast_smul_eq_nsmul]
      exact h2
    rw [h3]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy p.1)
  have hφφ : φ.comp φ = φ := LinearMap.ext fun u => by
    show ε • ε • u = ε • u
    rw [smul_smul, hεi]
  have hN : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ ≤
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ := by
    calc _ = ((latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ).map φ := by
            rw [← Submodule.map_comp, hφφ]
      _ ≤ _ := Submodule.map_mono hφ
      _ = _ := Submodule.map_smul'' _ _ _
  have hjac : Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (imA_g_nonunit X p)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ ((imA_lat_fg X p).map φ) hN hjac
  have hz : ∀ l ∈ X.B.I.L, ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l = 0 := by
    intro l hl
    have : φ (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l) ∈
        (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, hl, rfl⟩)
    rw [hbot] at this
    exact this
  have hex : ∃ l ∈ X.B.I.L, l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hs := X.B.I.L_span
    rw [Submodule.span_eq_bot.mpr h] at hs
    have i0 : Fin X.B.I.n := ⟨0, imA_n_pos X⟩
    have hm : (Pi.single i0 (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ (⊥ : Submodule X.B.I.E _) := by
      rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at hm
    have := congrFun hm i0
    simp at this
  obtain ⟨l, hl, hl0⟩ := hex
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hl0
  have h0 := congrFun (hz l hl) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  have hu : IsUnit (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l i) :=
    (isUnit_iff_ne_zero.mpr hi).map (inclR (F := X.B.I.F) (Fv X.B.I.F p.1))
  have hε0 : ε = 0 := (hu.mul_left_eq_zero).mp h0
  rw [hε, eC, map_sub, map_sub, map_one] at hε0
  linear_combination -hε0

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatFreeHolds
section
noncomputable section

namespace MassDataIdxLatFree

open NumberField

variable {E K : Type} [Field E] [NumberField E] [Field K] (O : ValuationSubring K) (ι : E →+* K)
  {n : Type} [Fintype n] [DecidableEq n]

theorem int_mem (a : 𝓞 E) : ι (a : E) ∈ O := by
  have h1 : IsIntegral ℤ (ι (a : E)) := (RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  have h2 : IsIntegral O (ι (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

def Mι (L : Submodule (𝓞 E) (n → E)) : Submodule O (n → K) :=
  Submodule.span O ((fun l : n → E => fun j => ι (l j)) '' (L : Set (n → E)))

theorem fg (L : Submodule (𝓞 E) (n → E)) (hL : L.FG) : (Mι O ι L).FG := by
  classical
  obtain ⟨S, hS⟩ := hL
  refine ⟨S.image (fun l : n → E => fun j => ι (l j)), ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.2
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
    exact Submodule.subset_span ⟨l, hS ▸ Submodule.subset_span hl, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    rw [← hS] at hl
    induction hl using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
    | zero =>
        have : (fun j => ι ((0 : n → E) j)) = 0 := by funext j; simp
        beta_reduce; rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
        have : (fun j => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
          funext j; simp
        beta_reduce; rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        have : (fun j => ι ((a • x) j)) = (⟨ι (a : E), int_mem O ι a⟩ : O) • (fun j => ι (x j)) := by
          funext j
          simp [Algebra.smul_def]
        beta_reduce; rw [this]; exact Submodule.smul_mem _ _ hx

theorem span_top (L : Submodule (𝓞 E) (n → E)) (hL : Submodule.span E (L : Set (n → E)) = ⊤) :
    Submodule.span K (Mι O ι L : Set (n → K)) = ⊤ :=
  by apply _root_.UpperTheory.Reformulated.B.SpanTopFamily.span_top <;> assumption

end MassDataIdxLatFree

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting

theorem latFree_holds {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    LatFreeP X p θ :=
  MassDataIdxLatFree.exists_gl (OpX X p) (Mlat1 X p θ)
    (MassDataIdxLatFree.fg (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_fg)
    (MassDataIdxLatFree.span_top (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_span)

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def StAdaptB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (e : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))
      (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ ((Matrix.reindex e e (jm1 X.B.I.J θ))ᵀ *ᵥ
        (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm)) = l b • Pi.single (pf b) 1) ∧
      ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
        ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
          (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
            - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
          ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
            ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) * Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) * (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

theorem isUnit_det_split_form (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    IsUnit (jm1 X.B.I.J θ).det := by
  have h := (unit_JR X p).map (th1 X p θ)
  rw [RingHom.map_det] at h
  exact h

theorem stFrameB_of (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : StFrameB X u p := by
  obtain ⟨θ, hθ, e, Q, l, hl, hy1, hy2, K, hK, ψ, hψ, hker, hred⟩ := h
  refine ⟨K, hK, ψ, hψ, hker, 1, fun x => ?_⟩
  let g1 : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p) :=
    Q * glRed (algebraMap (Op X p) (FpX X p)) (ψ x) * Q⁻¹
  have hg1 : (g1 : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) := by
    simp only [g1, Units.val_mul, hred x, ← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have hinj : Function.Injective (algebraMap (Op X p) (FpX X p)) := Subtype.val_injective
  rw [MassDataIdxStIm.mem_Ssub_iff_sG X.B.I.cm.sig X.B.I.J θ hθ e (isUnit_det_split_form X p θ) (frameOf X u) Q l hl
    hy1 hy2 (x : HAp X p) g1 hg1, inv_one, one_mul, mul_one,
    MassDataIdxStIm.mem_sG_iff_map _ hinj (ψ x)]
  simp only [g1, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem parabolic_image_of_adapted (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : ParabolicReductionImage X u p := parabolic_image_of_frame X u p (stFrameB_of X u p h)

end Loc

end MassDataIdxSteps
end
end

