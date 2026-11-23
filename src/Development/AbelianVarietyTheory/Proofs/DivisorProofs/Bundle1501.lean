module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open GlobalTheory.CxForm

variable {n : ℕ}

theorem delAt_pull_comp {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) {β : V n → Alt n}
    (hβ : ∀ S, DifferentiableAt ℝ (fun u => (bas n).repr (β u) S) (φ v)) :
    delAt (fun w => pull (fderiv ℂ φ w) (β (φ w))) v = pull (fderiv ℂ φ v) (delAt β (φ v)) := by
  have hφ1 : DifferentiableAt ℂ φ v := hφ.differentiableAt two_ne_zero
  have e : (fun w => pull (fderiv ℂ φ w) (β (φ w))) =
      fun w => ∑ T, (bas n).repr (β (φ w)) T • pull (fderiv ℂ φ w) (bas n T) := funext fun w => by
    conv_lhs => rw [← (bas n).sum_repr (β (φ w))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e, _root_.GlobalTheory.CxForm.DelForm.delAt_sum_smul (fun T w => (bas n).repr (β (φ w)) T) (fun T w => pull (fderiv ℂ φ w) (bas n T))
    (fun T => (hβ T).comp v (hφ1.restrictScalars ℝ)) (fun T S => _root_.GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv hφ (bas n T) S)]
  simp only [_root_.GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv hφ, smul_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [delAt_eq_sum_dOne β (φ v), map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_mul, GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic (c := fun u => (bas n).repr (β u) T) (hβ T) hφ1]

variable {M : Type} [TopologicalSpace M] {A : HolAtlas M n}

theorem del_compat {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.del α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.del α x') := by
  set φ : V n → V n := x'.ch ∘ x.ch.symm with hφdef
  have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hv : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  have hφ : ContDiffAt ℂ 2 φ x.crd := by
    have hd : DifferentiableOn ℂ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := A.holo x.1.1 x'.1.1
    have hs : ContDiffOn ℂ ∞ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := (contDiffOn_piLp 2).2 fun c =>
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hW
        ((EuclideanSpace.proj c : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hd)
    exact (hs.contDiffAt (hW.mem_nhds hv)).of_le (WithTop.coe_le_coe.2 le_top)
  have hφv : φ x.crd = x'.crd := by
    change x'.ch (x.ch.symm (x.ch x.pt)) = x'.ch x'.pt
    rw [x.ch.left_inv x.2]
    exact congrArg x'.ch h
  have hloc : A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun w => pull (fderiv ℂ φ w) (A.loc α x'.1.1 (φ w)) := by
    filter_upwards [hW.mem_nhds hv] with w hw
    let p : A.Pt := ⟨(x.1.1, x.ch.symm w), x.ch.map_target hw.1⟩
    let p' : A.Pt := ⟨(x'.1.1, x.ch.symm w), hw.2⟩
    have hc := hα.compat p p' rfl
    have hp : p.crd = w := x.ch.right_inv hw.1
    rw [HolAtlas.loc, dite_eq_left hw.1]
    refine hc.trans ?_
    rw [hp, ← A.loc_crd α p']
    rfl
  show delAt (A.loc α x.1.1) x.crd = pull (fderiv ℂ φ x.crd) (delAt (A.loc α x'.1.1) x'.crd)
  rw [delAt_congr hloc, delAt_pull_comp hφ (fun S => hφv ▸ FormMul.differentiableAt_coef hα x' S), hφv]

theorem isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld),
    A.IsForm α → A.IsForm (A.del α) :=
  fun A α hα => ⟨_root_.GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn A α hα, fun x x' h => del_compat hα x x' h⟩

end GlobalTheory.CxForm.DelForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorMoveArgsOriginEqBoxIndicator
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.OriginBoxVac

section Alg
variable {k : Type} [Field k] [ValuativeRel k]

theorem unit_mul_mem_integer_iff (u : kˣ) (x : k) :
    (u : k) * x ∈ 𝒪[k] ↔ valuation k x ≤ valuation k ((u⁻¹ : kˣ) : k) := by
  have hu : valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    ← one_mul (valuation k (u : k))⁻¹, le_mul_inv_iff₀ (zero_lt_iff.2 hu), mul_comm]

theorem scale_eq (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) =
      ((ϖ ^ (A - B - a) : kˣ) : k) * x := by
  have h : ϖ ^ (A - B - a) = (ϖ ^ a)⁻¹ * ϖ ^ A * (ϖ ^ B)⁻¹ := by
    rw [_root_.zpow_sub, _root_.zpow_sub]; group
  rw [h, Units.val_mul, Units.val_mul]; ring

theorem scaled_mem_iff (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k ((ϖ ^ (a - A + B) : kˣ) : k) := by
  rw [scale_eq, unit_mul_mem_integer_iff, ← _root_.zpow_neg, show -(A - B - a) = a - A + B by ring]

end Alg

theorem basePt_zero_of_var {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) :
    basePt c (0 : Matrix n n' k) r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp [basePt, Free, Kept] at h ⊢ <;> omega

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBoxVac

theorem moveArgs_one_entry {k : Type} [Field k] (G : Grid k) (g : G.VertexGroup) (z : G.Args) (b : Edge)
    (dt : Fin (G.rank b.tgt) → kˣ) (ds : Fin (G.rank b.src) → kˣ) (ht : g b.tgt = diagGL dt)
    (hsrc : g b.src = diagGL ds) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one g z b r s = (dt r : k) * z b r s * ((ds s)⁻¹ : kˣ) := by
  have h1 : ((g b.src)⁻¹).val = diagonal fun i => (((ds i)⁻¹ : kˣ) : k) := by rw [hsrc]; rfl
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val]
  rw [h1, ht, diagGL_val, diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBox
open GlobalTheory.OriginBoxVac

theorem indicator_moveArgs_origin {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup)
    (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (e : Vars G) :
    Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}
      (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  classical
  set M := G.moveArgs .one g (fill hs 0 0 e) with hMdef
  have hM : ∀ (j : ℕ) (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))), M (.theta G.m j) r s =
      ((ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) r : kˣ) : k) * downMap hs 0 e j s r *
        (((ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) s)⁻¹ : kˣ) : k) := by
    intro j r s
    rw [hMdef, moveArgs_one_entry G g _ (.theta G.m j)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) x) (hg j) (hg (j + 1)),
      fill_theta, transpose_apply]
  have hE : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)),
      M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') =
      ((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) r' : kˣ) : k) * stepPt ((0 : ColArgs G) j) (e ⟨j, hj⟩) s' r' *
        (((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) s')⁻¹ : kˣ) : k) := by
    intro j hj r' s'
    rw [hM, show G.m - 1 - j = G.m - 2 - j + 1 by omega, vtxExp_frame,
      show G.m - 1 - (j + 1) = G.m - 2 - j by omega, vtxExp_frame]
    congr 2
    simp only [downMap, dif_pos hj, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]

  have hbox : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')),
      (((ϖ ^ a)⁻¹ : kˣ) : k) * M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') ∈ 𝒪[k] ↔
      valuation k (e ⟨j, hj⟩ ⟨(s', r'), hv⟩) ≤ valuation k ((ϖ ^ boxExp G a a' ⟨j, hj⟩ ⟨(s', r'), hv⟩ : kˣ) : k) := by
    intro j hj r' s' hv
    rw [hE, scaled_mem_iff]
    simp only [stepPt, Matrix.add_apply, of_apply, dif_pos hv, Pi.zero_apply, basePt_zero_of_var s' r' hv, zero_add]
    rfl
  have key : (∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * M b i j ∈ 𝒪[k]) ↔ e ∈ box G ϖ a a' := by
    constructor
    · intro H j _ v _
      have hb : Edge.theta G.m j ∈ oppositePath G.m := by have := j.2; simp [oppositePath]; omega
      exact (hbox j j.2 v.1.2 v.1.1 v.2).1 (H _ hb _ _)
    · intro he b hb r s
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, -, rfl⟩ | ⟨j, hj, rfl⟩
      · have h0 : M (.ex i G.m) = 0 := by
          simp only [hMdef, Grid.moveArgs, fill_ex, Pi.zero_apply, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
        simp [h0]
      · rcases Nat.lt_or_ge j (G.m - 1) with hj' | hj'
        · obtain ⟨r', rfl⟩ := (frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega)).surjective r
          obtain ⟨s', rfl⟩ := (frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega)).surjective s
          by_cases hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')
          · exact (hbox j hj' r' s' hv).2 (he ⟨j, hj'⟩ trivial ⟨(s', r'), hv⟩ trivial)
          · rw [hE j hj', scale_eq]
            simp only [stepPt, Matrix.add_apply, of_apply, dif_neg hv, add_zero, Pi.zero_apply]
            rcases s' with s' | l <;> rcases r' with r' | i
            · simp [basePt]
            · simp [basePt]
            · simp [basePt]
            · simp only [basePt, fromBlocks_apply₂₂, of_apply]
              split_ifs with hli
              · have h0 : auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) (Sum.inr i : Fin (topRank G j) ⊕ _) -
                    auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) (Sum.inr l : Fin (topRank G (j + 1)) ⊕ _) - a = 0 := by
                  simp only [auxiliaryVectorUniformizerExponent, hli]; push_cast; ring
                rw [h0]; simp
              · simp
        · have hjm : j + 1 = G.m := by omega
          have h0 : M (.theta G.m j) r s = 0 := by
            rw [hM]; simp [downMap, show ¬ j < G.m - 1 by omega, hjm]
          simp [h0]
  by_cases he : e ∈ box G ϖ a a'
  · rw [Set.indicator_of_mem he]
    exact Set.indicator_of_mem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (key.2 he) _
  · rw [Set.indicator_of_notMem he]
    exact Set.indicator_of_notMem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (fun h => he (key.1 h)) _

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaFixedSH

theorem vs_inv_mem_of_not_mem_nonunits {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ∈ A)
    (hn : x ∉ A.nonunits) : x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
  have h1 : A.valuation x = 1 := le_antisymm ((A.valuation_le_one_iff x).2 hx) hn
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem inertiaFixed_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have hc : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this
  have hinv : ∀ π : R, Irreducible π → (algebraMap K Ω (algebraMap R K π))⁻¹ ∉ V := by
    intro π hπ h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω _ ∈ V
      rwa [map_inv₀]
    rw [hV] at h'
    obtain ⟨s, hs⟩ := h'
    have hπ0 : algebraMap R K π ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨s, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hs, map_one, mul_inv_cancel₀ hπ0]
  have hc0 : ∀ π : R, Irreducible π → algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    intro π hπ h
    apply hinv π hπ
    rw [h, inv_zero]; exact V.zero_mem
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  have memV' : ∀ y : K', y ∈ V' ↔ (y : Ω) ∈ V := fun y => ValuationSubring.mem_comap
  let f : R →+* V' := ((algebraMap K K').comp (algebraMap R K)).codRestrict V' (fun r => by
      rw [memV']; simpa using hc r)
  have hf : ∀ r : R, ((f r : K') : Ω) = algebraMap K Ω (algebraMap R K r) := fun r => by simp [f]
  have unitV' : ∀ a : V', ((a : K') : Ω) ∉ V.nonunits → IsUnit a := by
    intro a ha
    obtain ⟨h0, hi⟩ := vs_inv_mem_of_not_mem_nonunits V ((memV' a).1 a.2) ha
    have hmem : (a : K')⁻¹ ∈ V' := by rw [memV']; simpa using hi
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv, OneMemClass.coe_one,
      IntermediateField.coe_one]
    exact mul_inv_cancel₀ h0
  have hfπ : ∀ π : R, Irreducible π → Irreducible (f π) := by
    intro π hπ
    refine irreducible_iff.2 ⟨fun hu => hinv π hπ ?_, fun a b hab => ?_⟩
    · obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hb' : ((f π : K') : Ω) * ((b : K') : Ω) = 1 := by
        have := congrArg (fun z : V' => ((z : K') : Ω)) hb
        simpa using this
      rw [hf] at hb'
      rw [inv_eq_of_mul_eq_one_right hb']
      exact (memV' b).1 b.2
    · by_contra hne
      push_neg at hne
      have ha : ((a : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.1 (unitV' a h)
      have hb : ((b : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.2 (unitV' b h)
      have h1 := _root_.GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ _ (a : K').2 ha
      have h2 := _root_.GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ _ (b : K').2 hb
      have hab' : algebraMap K Ω (algebraMap R K π) = ((a : K') : Ω) * ((b : K') : Ω) := by
        rw [← hf, hab]; simp
      apply hinv π hπ
      have h0 := hc0 π hπ
      convert mul_mem h1 h2 using 1
      rw [div_mul_div_comm, ← hab']
      field_simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdvr : IsDiscreteValuationRing V' := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f π, hfπ π hπ, fun {x} hx => ?_⟩
    have hx0 : ((x : K') : Ω) ≠ 0 := by
      intro h; apply hx; apply Subtype.ext; apply Subtype.ext; simpa using h
    classical
    have hex := _root_.GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ _ hx0
    have hn := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h; rw [h] at hn; apply hn; simpa using (memV' x).1 x.2
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m ∈ V := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      simpa using this
    set y : K' := (x : K') / (algebraMap K K' (algebraMap R K π)) ^ m with hy
    have hyΩ : (y : Ω) = ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m := by simp [y]
    have hyV' : y ∈ V' := by rw [memV', hyΩ]; exact hmin
    have hyU : (y : Ω) ∉ V.nonunits := by
      intro hyn
      have := _root_.GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ _ y.2 hyn
      apply hn
      rw [hm, hyΩ] at *
      convert this using 1
      rw [pow_succ, div_div]
    refine ⟨m, (unitV' ⟨y, hyV'⟩ hyU).unit, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp only [IsUnit.unit_spec, MulMemClass.coe_mul, IntermediateField.coe_mul, SubmonoidClass.coe_pow,
      IntermediateField.coe_pow]
    rw [hf, hyΩ]
    field_simp [pow_ne_zero m (hc0 π hπ)]
  exact ⟨⟨hdvr, _root_.GlobalTheory.henselianLocalRing_fixedField_inertia R K Ω V hV, _root_.GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed R K Ω V hV, inferInstance⟩, f, hf, hfπ⟩

end GlobalTheory.InertiaFixedSH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertia
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedDVR

theorem isDiscreteValuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  classical
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c : Ω := algebraMap K Ω (algebraMap R K π) with hc
  have hπK : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have hc0 : c ≠ 0 := (map_ne_zero _).2 hπK
  have hcV : c ∈ V := by
    have h : algebraMap R K π ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨π, rfl⟩
    exact h
  have hcinv : c⁻¹ ∉ V := by
    intro h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
      rw [map_inv₀]; exact h
    rw [hV] at h'
    obtain ⟨r, hr⟩ := h'
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, map_one, mul_inv_cancel₀ hπK]
  have hcK' : c ∈ K' := K'.algebraMap_mem _

  let j : W → Ω := fun w => ((w : K') : Ω)
  have hjinj : Function.Injective j := fun a b h => Subtype.ext (Subtype.ext h)
  have hjV : ∀ w : W, j w ∈ V := fun w => w.2
  have hjK : ∀ w : W, j w ∈ K' := fun w => (w : K').2
  have hj_mul : ∀ a b : W, j (a * b) = j a * j b := fun _ _ => rfl
  have hj_zero : j 0 = 0 := rfl
  have hj_one : j 1 = 1 := rfl
  have hj_pow : ∀ (a : W) (n : ℕ), j (a ^ n) = j a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hj_one
    | succ n ih => rw [pow_succ, hj_mul, ih, pow_succ]
  let mk : (y : Ω) → y ∈ K' → y ∈ V → W := fun y h1 h2 => ⟨⟨y, h1⟩, h2⟩
  have hunit : ∀ w : W, j w ≠ 0 → (j w)⁻¹ ∈ V → IsUnit w := by
    intro w h0 hinv
    refine isUnit_iff_exists_inv.2 ⟨mk (j w)⁻¹ (K'.inv_mem (hjK w)) hinv, hjinj ?_⟩
    rw [hj_mul, hj_one]
    exact mul_inv_cancel₀ h0
  have hdvd : ∀ w : W, ¬ IsUnit w → ∃ u : W, w = mk c hcK' hcV * u := by
    intro w hw
    have hnu : j w ∈ V.nonunits := by
      rw [GlobalTheory.FixInertUnram.mem_nonunits_iff']
      by_cases h0 : j w = 0
      · exact Or.inl h0
      · exact Or.inr fun h => hw (hunit w h0 h)
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j w) (hjK w) hnu
    refine ⟨mk (j w / c) (K'.div_mem (hjK w) hcK') hq, hjinj ?_⟩
    rw [hj_mul]
    change j w = c * (j w / c)
    field_simp
  set ϖ : W := mk c hcK' hcV with hϖ
  have hϖnu : ¬ IsUnit ϖ := by
    intro h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 h
    apply hcinv
    have e : c * j v = 1 := by
      have := congrArg j hv
      rw [hj_mul, hj_one] at this
      exact this
    rw [inv_eq_of_mul_eq_one_right e]
    exact hjV v
  have hϖ0 : ϖ ≠ 0 := fun h => hc0 (by have := congrArg j h; rw [hj_zero] at this; exact this)
  have hirr : Irreducible ϖ := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨a', rfl⟩ := hdvd a hne.1
    obtain ⟨b', rfl⟩ := hdvd b hne.2
    apply hϖnu
    have e : ϖ * 1 = ϖ * (ϖ * (a' * b')) := by
      rw [_root_.mul_one]
      calc ϖ = ϖ * a' * (ϖ * b') := hab
        _ = ϖ * (ϖ * (a' * b')) := by ring
    have h1 := mul_left_cancel₀ hϖ0 e
    exact isUnit_iff_exists_inv.2 ⟨a' * b', h1.symm⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, fun {x} hx => ?_⟩
  have hx0 : j x ≠ 0 := fun h => hx (hjinj (h.trans hj_zero.symm))
  have hex : ∃ n : ℕ, j x / c ^ n ∉ V := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ (j x) hx0
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, j x / c ^ n ∉ V ∧ ∀ k < n, j x / c ^ k ∈ V :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hn
    rw [pow_zero, div_one]
    exact hjV x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmV : j x / c ^ m ∈ V := hmin m (by omega)
  have hyK : j x / c ^ m ∈ K' := K'.div_mem (hjK x) (pow_mem hcK' m)
  have hy0 : j x / c ^ m ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hc0)
  have hyinv : (j x / c ^ m)⁻¹ ∈ V := by
    by_contra hyi
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j x / c ^ m) hyK
      ((GlobalTheory.FixInertUnram.mem_nonunits_iff' V _).2 (Or.inr hyi))
    apply hn
    rw [pow_succ, ← div_div]
    exact hq
  have hu : IsUnit (mk (j x / c ^ m) hyK hmV) := hunit _ hy0 hyinv
  refine ⟨m, hu.unit, hjinj ?_⟩
  rw [IsUnit.unit_spec, hj_mul, hj_pow]
  change c ^ m * (j x / c ^ m) = j x
  field_simp

end GlobalTheory.InertiaFixedDVR
end

