module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamily
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_ne_zero {x : X} {h : X.functionField} (hh : UnitAt x h) : h ≠ 0 := by
  obtain ⟨b, hb, rfl⟩ := hh
  intro e
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * ↑hb.unit⁻¹) = 1 := by
    rw [IsUnit.mul_val_inv, map_one]
  rw [map_mul, e, zero_mul] at h1
  exact zero_ne_one h1

theorem regAt_div_unitAt {x : X} {g h : X.functionField} (hg : RegAt x g) (hh : UnitAt x h) :
    RegAt x (g / h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb, hbh⟩ := hh
  refine ⟨a * ↑hb.unit⁻¹, ?_⟩
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField b *
      algebraMap (X.presheaf.stalk x) X.functionField ↑hb.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, ha, div_eq_mul_inv, ← hbh, eq_inv_of_mul_eq_one_right h1]

theorem le_shift_of_isFS_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ)
      (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' →
      (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  intro k _ X _ p M M' J J' _ _ f w w' ι Δ hι hM hM' hw
  rw [_root_.GlobalTheory.HSNef.le_iff_local]
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨ρ', hρ', hreg', hφ'⟩ := hM'
  simp only [Function.comp_apply] at hreg' hφ'

  have hq : ∀ (x : X) c d (j' : J'), UnitAt x (f (ι j') * (ρ' d : X.functionField)) →
      (ρ c : X.functionField) / (ρ' d : X.functionField) =
        f (ι j') * (ρ c : X.functionField) / (f (ι j') * (ρ' d : X.functionField)) := by
    intro x c d j' hu
    have hf : f (ι j') ≠ 0 := left_ne_zero_of_mul (unitAt_ne_zero hu)
    rw [mul_div_mul_left _ _ hf]
  have hτ : ∀ (x : X) c d, x ∈ M.B.U c → x ∈ M'.B.U d →
      RegAt x ((ρ c : X.functionField) / (ρ' d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨-, j', hj'⟩ := hreg' x d hd
    rw [hq x c d j' hj']
    exact regAt_div_unitAt ((hreg x c hc).1 (ι j')) hj'
  refine ⟨ρ, ρ', hρ, hρ', hτ, ?_⟩
  intro σ y c d hc hd
  have hc' := mem_ptsIn.1 hc
  have hd' := mem_ptsIn.1 hd
  set τ : X.functionField := (ρ c : X.functionField) / (ρ' d : X.functionField) with hτdef
  have hτr : RegAt (under y) τ := hτ _ c d hc' hd'

  have hval : ∀ j' : J', ratVal (f (ι j') * (ρ c : X.functionField)) y =
      ratVal τ y * ratVal (f (ι j') * (ρ' d : X.functionField)) y := by
    intro j'
    have e : f (ι j') * (ρ c : X.functionField) = τ * (f (ι j') * (ρ' d : X.functionField)) := by
      rw [hτdef]; field_simp
    rw [e, ratVal_mul hτr ((hreg' _ d hd').1 j')]
  set S : ℝ := ∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) with hS
  set S' : ℝ := ∑ j', ‖ratVal (f (ι j') * (ρ' d : X.functionField)) y‖ ^ 2 * Real.exp (2 * w' j') with hS'
  have e1 : (M.φ σ).φ c y = Real.log S := hφ σ y c hc
  have e2 : ((M'.shift (fun _ => Δ) fun _ => rfl).φ σ).φ d y = Real.log S' + 2 * Δ := by
    change (M'.φ σ).φ d y + 2 * Δ = _
    rw [hφ' σ y d hd]
  have hS'pos : 0 < S' := by
    obtain ⟨-, j₀, hj₀⟩ := hreg' _ d hd'
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ _, ?_⟩
    have : ratVal (f (ι j₀) * (ρ' d : X.functionField)) y ≠ 0 := ratVal_ne_zero hj₀
    have : 0 < ‖ratVal (f (ι j₀) * (ρ' d : X.functionField)) y‖ := norm_pos_iff.2 this
    positivity
  set t : ℝ := ‖ratVal τ y‖ with ht
  have hineq : t ^ 2 * Real.exp (2 * Δ) * S' ≤ S := by
    classical
    calc t ^ 2 * Real.exp (2 * Δ) * S'
        = ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * (w' j' + Δ)) := by
          rw [hS', Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hval, norm_mul, ← ht, mul_add, Real.exp_add]; ring
      _ ≤ ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w (ι j')) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          gcongr
          exact hw j'
      _ = ∑ j ∈ Finset.univ.image ι, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) :=
          by rw [Finset.sum_image (fun a _ b _ h => hι h)]
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
  rw [e1, e2]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact zero_le_one
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hineq
  have hE : Real.exp (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) ^ 2 = S' * Real.exp (2 * Δ) / S := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) = (Real.log S' + 2 * Δ) - Real.log S := by
      push_cast; ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_log hS'pos, Real.exp_log hSpos]
  rw [← sq_le_one_iff₀ (by positivity), mul_pow, hE]
  rw [← mul_div_assoc, div_le_one hSpos]
  linarith [hineq]

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTopVertex_frame_point_transport_lattice : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (S : Finset ℕ)
    (fr₀ : GL (Fin (G.V (.grid D.R.m D.R.m)).rank) D.host.E) (u₀ : FinPt G (.grid D.R.m D.R.m)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr₀.1 * (G.V (.grid D.R.m D.R.m)).gram * fr₀.1 = 1 →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w) →
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
        (Formalism.IndefR.Lev.finE (G.V (.grid D.R.m D.R.m)) u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid D.R.m D.R.m))) →
    ∃ (fr : GL (Fin (G.V (.top D.R.m)).rank) D.host.E) (u : FinPt G (.top D.R.m)),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V (.top D.R.m)).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V (.top D.R.m)) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) ∧
      (∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), fr.1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
        (frameMat _ _ G.sp.topDec.ι * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0) ∧
      HMul.hMul (mt (G.V (.top D.R.m)) u.1) (topEmb G) = HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) u₀.1) ∧
      mt (G.V (.top D.R.m)) u.1 *ᵥ topVec G = topVec G := by
  first | exact @GlobalTheory.FunObj.top_transport | exact GlobalTheory.FunObj.top_transport | (intros; apply GlobalTheory.FunObj.top_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def growth : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (g * infGL E a y)‖ ≤ C * height y ^ N}
  zero_mem' g := ⟨0, 0, fun y => by simp⟩
  add_mem' {f f'} h h' g := by
    obtain ⟨C, N, hC⟩ := h g
    obtain ⟨C', N', hC'⟩ := h' g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have h1 := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have q1 : 0 ≤ height y ^ N := le_trans zero_le_one (one_le_pow₀ h1)
    have q2 : 0 ≤ height y ^ N' := le_trans zero_le_one (one_le_pow₀ h1)
    calc ‖(f + f') (g * infGL E a y)‖ ≤ ‖f (g * infGL E a y)‖ + ‖f' (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (hC y) (hC' y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) q1).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') q2).trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring
  smul_mem' c f h g := by
    obtain ⟨C, N, hC⟩ := h g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)


variable (E a) in
def tame : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ l : List (Lie E a), ((l.map (lie E a)).prod ψ).1 ∈ growth E a}
  zero_mem' l := by simp
  add_mem' {ψ ψ'} h h' l := by
    rw [map_add (f := _), Submodule.coe_add]
    exact add_mem (h l) (h' l)
  smul_mem' c ψ h l := by
    rw [map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ c (h l)

theorem growth_of_tame {ψ : Sm E a} (h : ψ ∈ tame E a) : ψ.1 ∈ growth E a := by
  simpa using h []

theorem lie_mem_tame (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ tame E a) : lie E a X ψ ∈ tame E a := by
  intro l
  have e : (l.map (lie E a)).prod (lie E a X ψ) = ((l ++ [X]).map (lie E a)).prod ψ := by
    simp [List.map_append, List.prod_append, Module.End.mul_apply]
  rw [e]
  exact h _

def dens (X : Lie E a) (α : Lie E a → ℂ) (x : Lie E a) : ℂ :=
  -(fderiv ℝ α x (lmul X x) + (LinearMap.trace ℝ (Lie E a) (lmul X).toLinearMap : ℂ) * α x)

def KInv (α : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a),
    α (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = α x

def maps (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a))
    (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) : Submodule ℂ (W →ₗ[ℂ] Sm E a) where
  carrier := {T | (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
    ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w}
  zero_mem' := ⟨fun k w => by simp, fun w => ⟨by simp, fun _ _ => rfl, fun k _ => by simp⟩⟩
  add_mem' {T T'} h h' := ⟨fun k w => by simp [h.1 k w, h'.1 k w], fun w =>
    ⟨by simpa using add_mem (h.2 w).1 (h'.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g, (h'.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk, (h'.2 w).2.2 k hk]⟩⟩
  smul_mem' c T h := ⟨fun k w => by simp [h.1 k w], fun w =>
    ⟨by simpa using Submodule.smul_mem _ c (h.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk]⟩⟩

theorem isTest_dens (X : Lie E a) {α : Lie E a → ℂ} (h : GlobalTheory.CuspQuot.IsTest (invSet E a) α) :
    GlobalTheory.CuspQuot.IsTest (invSet E a) (dens X α) := by
  have hs : Function.support (dens X α) ⊆ tsupport α := by
    intro x hx
    by_contra hn
    apply hx
    have h1 : α x = 0 := image_eq_zero_of_notMem_tsupport hn
    have h2 : fderiv ℝ α x = 0 := fderiv_of_notMem_tsupport ℝ hn
    simp [dens, h1, h2]
  have ht : tsupport (dens X α) ⊆ tsupport α := closure_minimal hs (isClosed_tsupport α)
  refine ⟨?_, h.2.1.mono' hs, ht.trans h.2.2⟩
  refine (((h.1.fderiv_right (m := ∞) (by simp)).clm_apply (lmul X).contDiff).add
    (contDiff_const.mul h.1)).neg

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNef
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.noSection_H1_bound_riemann_roch : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL F _ hF h0 hI hi
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hX (d+1) F hF L hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.euler_char_h0_h1_bound_higher k X hX (d+1) L hL F hF (fun m => (d+1)*(m+1)^d) hi
  refine ⟨C1 + C2 + hdim k (twist F (lbPow L 0)) 1, fun m => ?_⟩
  have he1 : 1 ≤ (d+1)*(m+1)^d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · calc hdim k (twist F (lbPow L 0)) 1 ≤ hdim k (twist F (lbPow L 0)) 1 * ((d+1)*(0+1)^d) :=
          Nat.le_mul_of_pos_right _ he1
      _ ≤ (C1 + C2 + hdim k (twist F (lbPow L 0)) 1) * ((d+1)*(0+1)^d) :=
          Nat.mul_le_mul_right _ (by omega)
  · have a1 := hC1 m
    have a2 := hC2 m
    rw [h0 m hm] at a1
    simp only [Nat.add_sub_cancel] at a2
    have hfac : (1 : ℤ) ≤ ((d+1).factorial : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hImp : 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) := mul_nonneg hI (by positivity)
    have hE : (((d+1)*(m+1)^d : ℕ) : ℤ) = ((d+1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ d := by push_cast; ring
    rw [← hE] at a2
    have hEpos : (1 : ℤ) ≤ (((d+1)*(m+1)^d : ℕ) : ℤ) := by exact_mod_cast he1
    suffices h : (hdim k (twist F (lbPow L m)) 1 : ℤ) ≤
        ((C1 + C2 + hdim k (twist F (lbPow L 0)) 1 : ℕ) : ℤ) * (((d+1)*(m+1)^d : ℕ) : ℤ) by
      exact_mod_cast h
    generalize (((d+1)*(m+1)^d : ℕ) : ℤ) = E at a1 a2 hEpos ⊢
    generalize chi k (twist F (lbPow L m)) = c at a1 a2
    generalize interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) = I at a2 hImp
    generalize (((d+1).factorial : ℕ) : ℤ) = f at a2 hfac
    generalize (hdim k (twist F (lbPow L m)) 1 : ℤ) = H at a1 ⊢
    push_cast
    have hh0 : (0 : ℤ) ≤ (hdim k (twist F (lbPow L 0)) 1 : ℤ) := by positivity
    generalize (hdim k (twist F (lbPow L 0)) 1 : ℤ) = h00 at hh0 ⊢
    have hC1' : (0:ℤ) ≤ C1 := by positivity
    have hC2' : (0:ℤ) ≤ C2 := by positivity
    rw [abs_le] at a1 a2
    simp only [CharP.cast_eq_zero, sub_zero] at a1
    have hc : -c ≤ (C2 : ℤ) * E := by
      rcases le_or_gt 0 c with hc | hc
      · nlinarith
      · nlinarith
    nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

noncomputable section

namespace GlobalTheory.HCF.FormsSub

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isAutForm_zero : IsAutForm (0 : Sm E a) := by
  constructor
  · intro γ g
    rfl
  · have : {k | finRep E a k (0 : Sm E a) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
    rw [this]; exact isOpen_univ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp
  · intro g
    exact ⟨0, 0, fun y => by simp⟩

theorem isAutForm_add {φ ψ : Sm E a} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + ψ) := by
  constructor
  · intro γ g
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [hφ.left, hψ.left]
  · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
      ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
        have h1 : finRep E a k φ = φ := hk.1
        have h2 : finRep E a k ψ = ψ := hk.2
        change finRep E a k (φ + ψ) = φ + ψ
        rw [map_add (f := _), h1, h2]
  · have := hφ.kfin
    have := hψ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  · have := hφ.zfin
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
      Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C1, N1, h1⟩ := hφ.growth g
    obtain ⟨C2, N2, h2⟩ := hψ.growth g
    refine ⟨|C1| + |C2|, N1 + N2, fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N1 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N2 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have p1 : 0 ≤ height y ^ N1 := by positivity
    have p2 : 0 ≤ height y ^ N2 := by positivity
    change ‖φ.1 _ + ψ.1 _‖ ≤ _
    calc ‖φ.1 (g * infGL E a y) + ψ.1 (g * infGL E a y)‖
        ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C1 * height y ^ N1 + C2 * height y ^ N2 := add_le_add (h1 y) (h2 y)
      _ ≤ |C1| * height y ^ (N1 + N2) + |C2| * height y ^ (N1 + N2) := by
          exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C1) p1).trans
              (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)))
            ((mul_le_mul_of_nonneg_right (le_abs_self C2) p2).trans
              (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)))
      _ = _ := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (hφ : IsAutForm φ) : IsAutForm (c • φ) := by
  constructor
  · intro γ g
    change c • φ.1 _ = c • φ.1 _
    rw [hφ.left]
  · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
      (hφ.level.mem_nhds (by simp)) fun k hk => by
        have h1 : finRep E a k φ = φ := hk
        change finRep E a k (c • φ) = c • φ
        rw [map_smul, h1]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have := hφ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := hφ.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c • φ.1 _‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem foldr_lin (χ : Module.End ℂ (Sm E a) → ℂ) (c : ℂ) (φ ψ : Sm E a) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (c • φ + ψ) =
      c • zs.foldr (fun z f => z f - χ z • f) φ + zs.foldr (fun z f => z f - χ z • f) ψ := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.foldr_cons]
    rw [ih, map_add (f := _), map_smul]
    module

theorem foldr_zero (χ : Module.End ℂ (Sm E a) → ℂ) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (0 : Sm E a) = 0 := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.foldr_cons, ih, map_zero, smul_zero, sub_zero]

end GlobalTheory.HCF.FormsSub


open GlobalTheory.HCF.FormsSub in
theorem GlobalTheory.HCF.formsGL_single_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ),
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  intro E _ _ _ a L W χ N
  let S : Submodule ℂ (Sm E a) :=
    { carrier := formsGL E a L W {χ} N
      zero_mem' := by
        refine ⟨isAutForm_zero, fun k _ => map_zero _, fun g => ?_, χ, rfl, fun zs _ _ => foldr_zero χ zs⟩
        have : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
          funext k; simp
        rw [this]; exact W.zero_mem
      add_mem' := by
        rintro φ ψ ⟨a1, b1, c1, χ1, e1, d1⟩ ⟨a2, b2, c2, χ2, e2, d2⟩
        rw [Set.mem_singleton_iff] at e1 e2
        rw [e1] at d1
        rw [e2] at d2
        refine ⟨isAutForm_add a1 a2, fun k hk => by rw [map_add (f := _), b1 k hk, b2 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
              (fun k : Kinf E a => (cptRep E a k φ).1 g) + (fun k : Kinf E a => (cptRep E a k ψ).1 g) := by
            funext k; simp
          rw [this]; exact W.add_mem (c1 g) (c2 g)
        · have := foldr_lin χ 1 φ ψ zs
          rw [one_smul, one_smul] at this
          rw [this, d1 zs hl hz, d2 zs hl hz, add_zero]
      smul_mem' := by
        rintro c φ ⟨a1, b1, c1, χ1, e1, d1⟩
        rw [Set.mem_singleton_iff] at e1
        rw [e1] at d1
        refine ⟨isAutForm_smul c a1, fun k hk => by rw [map_smul, b1 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) = c • (fun k : Kinf E a => (cptRep E a k φ).1 g) := by
            funext k; simp
          rw [this]; exact W.smul_mem c (c1 g)
        · have := foldr_lin χ c φ 0 zs
          rw [add_zero, foldr_zero, add_zero] at this
          rw [this, d1 zs hl hz, smul_zero] }
  intro φ hφ
  exact (Submodule.span_le (p := S)).2 le_rfl hφ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermPointSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_term_point_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  first | (exact @GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (exact GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (intros; apply GlobalTheory.LKMid.Pair.term_one_eq_pointSum <;> assumption)
end

