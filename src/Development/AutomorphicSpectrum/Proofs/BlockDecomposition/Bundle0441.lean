module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEvaluationOfMemAdjoin

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ConvHecke

theorem conv_isHecke : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
    IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧
      ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  intro H _ _ _ _ K L f₁ f₂ hLK hfin h₁ h₂
  have hu : ∀ y, L ≤ rStab (fun z => f₁ z * f₂ (z⁻¹ * y)) := by
    intro y l hl x
    show f₁ (x * l) * f₂ ((x * l)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)
    have e : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y) := by group
    rw [e, (h₁.2 l hl x).2, (h₂.2 l⁻¹ (L.inv_mem hl) _).1]
  have hlev := fun y =>
    GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L (fun z => f₁ z * f₂ (z⁻¹ * y)) hLK (hu y) hfin
  have hnz : ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 →
      ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    apply hy
    rw [hlev y]
    have hz : ∀ p : H ⧸ L, f₁ p.out * f₂ ((p.out)⁻¹ * y) = 0 := by
      intro p
      by_cases h : f₁ p.out = 0
      · simp [h]
      · simp [hcon _ h]
    simp [hz]
  refine ⟨⟨?_, ?_⟩, hnz⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (h₁.1.isCompact.mul h₂.1.isCompact) ?_
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := hnz y hy
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ hz1, z⁻¹ * y, subset_tsupport _ hz2, by group⟩
  · intro l hl x
    constructor
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (l * x))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      rw [hlev (l * x), hlev x]
      congr 1
      refine (finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (H ⧸ L))).symm.trans
        (finsum_congr fun p => ?_)
      set w : H := ((MulAction.toPerm l : Equiv.Perm (H ⧸ L)) p).out with hw
      have hcl : ((l * p.out : H) : H ⧸ L) = (w : H ⧸ L) := by
        rw [hw, QuotientGroup.out_eq']
        show ((l * p.out : H) : H ⧸ L) = l • p
        conv_rhs => rw [← QuotientGroup.out_eq' p]
        rfl
      have hm : (l * p.out)⁻¹ * w ∈ L := QuotientGroup.eq.1 hcl
      have hinv := hu (l * x) hm (l * p.out)
      have hmul : l * p.out * ((l * p.out)⁻¹ * w) = w := by group
      simp only [hmul] at hinv
      refine hinv.trans ?_
      have e : (l * p.out)⁻¹ * (l * x) = (p.out)⁻¹ * x := by group
      rw [e, (h₁.2 l hl _).1]
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      have e : (fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = fun z => f₁ z * f₂ (z⁻¹ * x) := by
        funext z
        rw [← mul_assoc, (h₂.2 l hl _).2]
      rw [e]

end GlobalTheory.CompanionTheory.ConvHecke

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenfunctionsClosed
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.HeckeEigenspaces

theorem exists_closed_common_ker {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (𝒯 : Set (X →L[ℂ] X)) :
    ∃ Y : Submodule ℂ X, IsClosed (Y : Set X) ∧ ∀ φ, φ ∈ Y ↔ ∀ T ∈ 𝒯, T φ = 0 := by
  refine ⟨{ carrier := {φ | ∀ T ∈ 𝒯, T φ = 0}
            add_mem' := fun {x y} hx hy T hT => by rw [map_add (f := _), hx T hT, hy T hT, add_zero]
            zero_mem' := fun T _ => map_zero T
            smul_mem' := fun c x hx T hT => by rw [map_smul, hx T hT, smul_zero] }, ?_, fun _ => Iff.rfl⟩
  have e : ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X) = ⋂ T ∈ 𝒯, T ⁻¹' {0} := by
    ext φ; simp
  change IsClosed ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X)
  rw [e]
  exact isClosed_biInter fun T _ => isClosed_singleton.preimage T.continuous

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_heckeOp (w : Pl E) {h : GL (Fin a) (w.adicCompletion E) → ℂ} (hh : h ∈ Hecke ℂ (KGL w (n := a))) :
    ∃ T : XB E a →L[ℂ] XB E a, (∀ x, heckeVec (repW a w) (KGL w (n := a)) h x = T x) ∧
      ∀ A : XB E a →L[ℂ] XB E a, (∀ u, Commute A (Rt E a (fl a w u))) → Commute A T := by
  classical
  have hs := Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) hh.2
  refine ⟨∑ c ∈ hs.toFinset, h c.out • Rt E a (fl a w c.out), fun x => ?_, fun A hA => ?_⟩
  · rw [heckeVec, finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · simp
    · intro c hc
      refine Finset.mem_coe.2 (hs.mem_toFinset.2 fun h0 => hc (by simp [h0]))
  · exact Commute.sum_right _ _ _ fun c _ => (hA c.out).smul_right _

theorem hecke_eigenfunctions_closed : G0 → G2c := by
  intro h0 E _ _ _ a w B hB
  have hcomm : ∀ g : GA E a, cLoc w g = 1 → ∀ u, Commute (Rt E a g) (Rt E a (fl a w u)) := fun g hg u => by
    have e := (h0 E a).2.2.2.2.2.2.2.1 w g hg u
    change Rt E a g * Rt E a (fl a w u) = Rt E a (fl a w u) * Rt E a g
    rw [← map_mul, ← map_mul, e]
  choose T hT hC using fun (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ) =>
    exists_heckeOp (a := a) w (Tj_mem_hecke (n := a) p.2 j)
  obtain ⟨Y, hcl, hY⟩ := exists_closed_common_ker
    ({R | (∃ k ∈ KGL w (n := a), R = Rt E a (fl a w k) - 1) ∨
      ∃ (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ), j ≤ a ∧ R = T p j - satEig (qV E w) a B j • 1} :
      Set (XB E a →L[ℂ] XB E a))
  refine ⟨Y, hcl, fun g hg φ hφ => ?_, fun φ => ?_⟩
  · rw [hY] at hφ ⊢
    intro R hR
    have hRc : Commute (Rt E a g) R := by
      rcases hR with ⟨k, -, rfl⟩ | ⟨p, j, -, rfl⟩
      · exact (hcomm g hg k).sub_right (Commute.one_right _)
      · exact (hC p j _ (hcomm g hg)).sub_right ((Commute.one_right _).smul_right _)
    have e : R (Rt E a g φ) = Rt E a g (R φ) := (DFunLike.congr_fun hRc.eq φ).symm
    rw [e, hφ R hR, map_zero]
  · rw [hY]
    constructor
    · intro h
      by_cases hφ : φ = 0
      · exact Or.inl hφ
      · refine Or.inr ⟨hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hB, fun ϖ hϖ j hj => ?_⟩
        · have := h _ (Or.inl ⟨k, hk, rfl⟩)
          simpa [sub_eq_zero] using this
        · have := h _ (Or.inr ⟨⟨ϖ, hϖ⟩, j, hj, rfl⟩)
          rw [hT ⟨ϖ, hϖ⟩ j]
          simpa [sub_eq_zero] using this
    · rintro (rfl | ⟨-, hfix, -, heig⟩) R hR
      · exact map_zero R
      · rcases hR with ⟨k, hk, rfl⟩ | ⟨p, j, hj, rfl⟩
        · have := GlobalTheory.LGrp.mem_fixed.1 hfix k hk
          simpa [sub_eq_zero] using this
        · have := heig p.1 p.2 j hj
          rw [hT p j] at this
          simpa [sub_eq_zero] using this

end GlobalTheory.CompanionTheory.HeckeEigenspaces
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

section Alg

open Pointwise

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem smul_top_eq_ker (π : M →ₗ[R] N) (a : R) (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) :
    a • (⊤ : Submodule R M) = LinearMap.ker π := by
  ext t
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, hk]
  simp

theorem isWeaklyRegular_of_quotSMulTop (π : M →ₗ[R] N) (hπ : Function.Surjective π) (a : R)
    (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop a M) l) :
    RingTheory.Sequence.IsWeaklyRegular N l :=
  (((Submodule.quotEquivOfEq _ _ (smul_top_eq_ker π a hk)).trans
    (π.quotKerEquivOfSurjective hπ)).isWeaklyRegular_congr l).1 h

theorem length_quot_eq_of_cut (π : M →ₗ[R] N) (hπ : Function.Surjective π) (a : R)
    (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) (J : Ideal R) :
    Module.length R (N ⧸ (J • ⊤ : Submodule R N)) =
      Module.length R (M ⧸ ((Ideal.span {a} ⊔ J) • ⊤ : Submodule R M)) := by
  have hf : Function.Surjective ((J • ⊤ : Submodule R N).mkQ ∘ₗ π) :=
    (Submodule.mkQ_surjective _).comp hπ
  have hker : (Ideal.span {a} ⊔ J) • (⊤ : Submodule R M) =
      LinearMap.ker ((J • ⊤ : Submodule R N).mkQ ∘ₗ π) := by
    have hmap : (J • ⊤ : Submodule R N) = (J • ⊤ : Submodule R M).map π := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hmap, Submodule.comap_map_eq, Submodule.sup_smul,
      Submodule.ideal_span_singleton_smul, smul_top_eq_ker π a hk, sup_comm]
  exact (((Submodule.quotEquivOfEq _ _ hker).trans
    (((J • ⊤ : Submodule R N).mkQ ∘ₗ π).quotKerEquivOfSurjective hf)).length_eq).symm

end Alg

section Cut

variable {X : Scheme.{0}} {L : LB X}

theorem germSec_cons {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    (fun j => germSec ((Fin.cons s t : Fin (d + 1) → L.Sec) j) hx) =
      (Fin.cons (germSec s hx) (fun j => germSec (t j) hx) :
        Fin (d + 1) → X.presheaf.stalk x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem mono_cutHom_of_isSMulRegular [IsLocallyNoetherian X] (hL : L.IsLB) (F : X.Modules)
    [F.IsQuasicoherent] (s : L.Sec)
    (h : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i), IsSMulRegular (F.presheaf.stalk x :) (germSec s hx)) :
    Mono (cutHom F hL s) := by
  refine (mono_cutHom_iff F hL s).2 fun x hx => ?_
  obtain ⟨i, hi⟩ := GlobalTheory.ThickeningDetermines.exists_mem_chart hL x
  obtain ⟨u, hu⟩ := mem_assPoints_iff_exists.1 hx
  refine (Cartier.mem_nonzeroLocus_iff s i hi).2 ((X.mem_basicOpen _ x hi).2 ?_)
  by_contra hn
  have hm : germSec s hi ∈ maximalIdeal (X.presheaf.stalk x) := hn
  have h0 : u = 0 := (h x i hi).right_eq_zero_of_smul ((hu _).2 hm)
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 ((hu 1).1 (by simp [h0])))

end Cut

theorem mono_cutHom_and_goodStalks_cut {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB)
    (F : X.Modules) [IsFiniteQC F] {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec)
    (h : GoodStalks F (Fin.cons s t : Fin (d + 1) → L.Sec)) :
    Mono (cutHom F hL s) ∧ GoodStalks (cut F hL s) t := by
  have key : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
      IsSMulRegular (F.presheaf.stalk x :) (germSec s hx) ∧
        RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop (germSec s hx) (F.presheaf.stalk x :))
          (List.ofFn fun j => germSec (t j) hx) := fun x i hx => by
    have h₁ := (h x i hx).1
    rw [germSec_cons, List.ofFn_succ, RingTheory.Sequence.isWeaklyRegular_cons_iff] at h₁
    exact h₁
  refine ⟨mono_cutHom_of_isSMulRegular hL F s fun x i hx => (key x i hx).1, fun x i hx => ?_⟩
  have hπ := stalkLinear_surjective (cutπ F hL s) x
  have hk := (isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx
  refine ⟨isWeaklyRegular_of_quotSMulTop (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk _
    (key x i hx).2, ?_⟩
  have h₂ := (h x i hx).2
  rw [germSec_cons, Fin.range_cons, Ideal.span_insert] at h₂
  rw [length_quot_eq_of_cut (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk]
  exact h₂

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n :=
  unit_mem (1 : Matrix.unitaryGroup (Fin n) ℂ)

theorem ini_injective {n : ℕ} (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

theorem lm_one {n : ℕ} (j : Fin n) : lm j (1 : Mat n) = 1 := by
  delta lm
  rw [Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]

theorem gm_one {n : ℕ} (j : Fin n) : gm j (1 : Mat n) = 1 := by
  delta gm
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
    Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]

theorem fRaw_one (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) : fRaw lam lev 1 = 1 := by
  delta fRaw
  rw [Set.indicator_of_mem (one_mem_GLs n)]
  simp [lm_one, gm_one]

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariant
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.FMul

open GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem ini_injective (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

theorem rows_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    (p * g).submatrix (ini j) id = p.submatrix (ini j) (ini j) * g.submatrix (ini j) id := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)
  intro k hk
  have hjk : j < k := by
    by_contra h
    have h' : (k : ℕ) ≤ j := by
      have := not_lt.1 h
      exact Fin.le_def.1 this
    exact hk ⟨⟨k, by omega⟩, by ext; rfl⟩
  have haj : ini j a ≤ j := by
    have := a.isLt
    rw [Fin.le_def]
    show (a : ℕ) ≤ j
    omega
  rw [hz _ _ haj hjk, zero_mul]

theorem lm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    lm j (p * g) = lm j p * lm j g := by
  have h : (p * g).submatrix (ini j) (ini j) =
      p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j) := by
    ext a c
    exact congrFun (congrFun (rows_mul j p g hz) a) (ini j c)
  delta lm
  rw [h, Matrix.det_mul]

theorem gm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j (p * g) = lm j p * star (lm j p) * gm j g := by
  delta gm lm
  rw [rows_mul j p g hz, Matrix.conjTranspose_mul]
  have h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id *
      ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) =
      p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) *
        (p.submatrix (ini j) (ini j))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  ring

theorem gm_one (j : Fin n) : gm j (1 : Mat n) = 1 := by
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one _ (ini_injective j)]
  delta gm
  rw [h, Matrix.det_one]

theorem gm_left (j : Fin n) (p : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j p = lm j p * star (lm j p) := by
  have := gm_mul j p 1 hz
  rwa [Matrix.mul_one, gm_one, mul_one] at this

theorem dif_eq_zero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  obtain ⟨-, hl⟩ := hl
  have hlam := hl _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    delta muZ
    simp only [hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    delta yZ
    simp only [hlam, hmu]
  delta dif
  constructor
  · simp only [dite_eq_left h, hmu, sub_self]
  · simp only [dite_eq_left h, hy, sub_self]

theorem fRaw_mul : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  intro n lam _ lev hl p hp g hg
  obtain ⟨hp1, hp2⟩ := hp
  have hpg : p * g ∈ GLs n := by
    show (p * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hp1 hg
  delta fRaw
  simp only [Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b
  · have hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0 := fun a b h1 h2 => hp2 a b (hgood a b h1 h2)
    rw [lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · push Not at hgood
    obtain ⟨a, b, haj, hjb, hba⟩ := hgood
    have hmono := hl.1
    have hb : (j : ℕ) < b := Fin.lt_def.1 hjb
    have h : (j : ℕ) + 1 < n := by have := b.isLt; omega
    have h1 : lev j ≤ lev ⟨j + 1, h⟩ := hmono (Fin.le_def.2 (by simp))
    have h2 : lev ⟨j + 1, h⟩ ≤ lev b := hmono (Fin.le_def.2 (by simpa using hb))
    have h3 : lev a ≤ lev j := hmono haj
    have he : lev j = lev ⟨j + 1, h⟩ := by omega
    obtain ⟨d1, d2⟩ := dif_eq_zero lam lev hl j h he
    simp only [d1, d2, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.ModelS.FMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPickReal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.InvPickKP

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.RealMult (Pair2 Inv2 ev2)

variable {n : ℕ}

def toKP : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p =>
    if p.1 then (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, p.2) + FreeAlgebra.ι ℂ (true, p.2))
    else (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, p.2) - FreeAlgebra.ι ℂ (true, p.2))

theorem evalCartan_toCartan {V : Type} [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : evKP E1 E2 (toKP a) = ev2 E1 E2 a := by
  have eK : ∀ a b, evKP E1 E2 (FreeAlgebra.ι ℂ (false, a, b)) = E1 a b + E2 a b := fun a b => by
    simp [evKP, kA]
  have eP : ∀ a b, evKP E1 E2 (FreeAlgebra.ι ℂ (true, a, b)) = E1 a b - E2 a b := fun a b => by
    simp [evKP, pA]
  have h : (evKP E1 E2).comp toKP = ev2 E1 E2 := by
    apply FreeAlgebra.hom_ext
    funext ⟨s, a, b⟩
    show evKP E1 E2 (toKP (FreeAlgebra.ι ℂ (s, a, b))) = ev2 E1 E2 (FreeAlgebra.ι ℂ (s, a, b))
    cases s
    · have t : toKP (FreeAlgebra.ι ℂ (false, a, b)) =
          (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, a, b) - FreeAlgebra.ι ℂ (true, a, b)) := by simp [toKP]
      have e : ev2 E1 E2 (FreeAlgebra.ι ℂ (false, a, b)) = E2 a b := by simp [ev2]
      rw [t, e, map_smul, map_sub, eK, eP]
      module
    · have t : toKP (FreeAlgebra.ι ℂ (true, a, b)) =
          (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, a, b) + FreeAlgebra.ι ℂ (true, a, b)) := by simp [toKP]
      have e : ev2 E1 E2 (FreeAlgebra.ι ℂ (true, a, b)) = E1 a b := by simp [ev2]
      rw [t, e, map_smul, map_add (f := _), eK, eP]
      module
  exact DFunLike.congr_fun h a

theorem invKP_toKP {a : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Inv2 a) : InvKP n (toKP a) := by
  intro V _ _ E1 E2 hE c d
  rw [evalCartan_toCartan]
  exact h V E1 E2 ⟨hE.1, hE.2.1, hE.2.2⟩ c d

theorem invPick : InvPick := by
  intro n lam lev V _ _ E1 E2 hA μ v w hv hw hv0 hx
  obtain ⟨a, ha, hav⟩ := GlobalTheory.CompanionTheory.RealMult.Lift.liftInv n V E1 E2 ⟨hA.gl1, hA.gl2, hA.comm⟩ hA.unitK hA.locFin
    μ v w hv0 hv hw hx
  exact ⟨toKP a, invKP_toKP ha, by rw [evalCartan_toCartan, hav]⟩

end GlobalTheory.CompanionTheory.InvPickKP
end
end

