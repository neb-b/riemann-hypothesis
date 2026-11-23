module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUnipBOfMemUnipotent
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic Matrix
open scoped ValuativeRel
open PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSBound

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem psiOK_of_hasConductor {ψ₁ : AddChar F Circle} (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) :
    PsiOK (Circle.coeHom.compAddChar ψ₁) := by
  have h1 : ∀ y : F, ValuativeRel.valuation F y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  refine ⟨fun x hx => ?_, ?_, fun x => Circle.norm_coe (ψ₁ x)⟩
  · simp [h1 x ((Valuation.mem_integer_iff _ _).mp hx)]
  · have hlt := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one F
    have hne := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero F
    set ϖ : F := (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) with hϖdef
    have hϖ : ϖ ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
    have hinv : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hϖ, map_one]
    have hnot : ¬ ValuativeRel.valuation F ϖ⁻¹ ≤ ValuativeRel.valuation F ((1 : Fˣ) : F) := by
      rw [Units.val_one, map_one]
      intro hle
      have h3 : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ ≤
          ValuativeRel.valuation F ϖ * 1 := by gcongr
      rw [hinv, mul_one] at h3
      exact absurd hlt (not_lt.mpr h3)
    have hex : ¬ ∀ y : F, ValuativeRel.valuation F y ≤ ValuativeRel.valuation F ϖ⁻¹ → ψ₁ y = 1 :=
      fun hall => hnot ((h _).mp hall)
    push Not at hex
    obtain ⟨y, hy, hy1⟩ := hex
    refine ⟨y, ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, map_mul]
      calc ValuativeRel.valuation F ϖ * ValuativeRel.valuation F y
          ≤ ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ := by gcongr
        _ = 1 := hinv
    · intro hc
      apply hy1
      apply Circle.ext
      rw [Circle.coe_one]
      exact hc

theorem mem_unipB_of_mem_unipotent {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ Iwasawa.unipotent F n) :
    g ∈ GlobalTheory.SmGL.unipB F (Fin n) := by
  obtain ⟨hut, hdiag⟩ := hg
  have hp : g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.points (Fin n)) := by
    intro i j hij
    exact hut (by simpa [GlobalTheory.SmGL.blk, GlobalTheory.SmGL.points] using hij)
  refine ⟨⟨g, hp⟩, ?_, rfl⟩
  show GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.points (Fin n)) ⟨g, hp⟩ = 1
  refine funext fun a => ?_
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a).toHomUnits ⟨g, hp⟩ = 1
  apply Units.ext
  ext i j
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a ⟨g, hp⟩) i j = (1 : Matrix Unit Unit F) i j
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [Matrix.one_apply_eq]
  exact hdiag a

theorem superDiag_eq_superdiagSum {n : ℕ} (g : GL (Fin n) F) :
    GlobalTheory.Whittaker.superDiag g = Whittaker.superdiagSum (g : Matrix (Fin n) (Fin n) F) := by
  simp only [GlobalTheory.Whittaker.superDiag, GroundTheory.Automorphic.Whittaker.superdiagSum, Finset.sum_filter]

theorem whit_of_isFunctional {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {ψ₁ : AddChar F Circle} {l : Module.Dual ℂ V}
    (h : GlobalTheory.Whittaker.IsFunctional ψ₁ ρ l) : Whit ρ (Circle.coeHom.compAddChar ψ₁) l := by
  intro g hg u
  rw [h g (mem_unipB_of_mem_unipotent hg) u, GroundTheory.Automorphic.Whittaker.psiN,
    ← superDiag_eq_superdiagSum]
  all_goals rfl

end Local

private theorem continuous_of_hasConductor_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ₁ : AddChar k Circle}
    (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) : Continuous ψ₁ := by
  have h1 : ∀ y : k, ValuativeRel.valuation k y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  have hopen : IsOpen ((ValuativeRel.valuation k).integer : Set k) := Valuation.isOpen_integer
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((ValuativeRel.valuation k).integer : Set k),
    hopen.preimage (continuous_sub_right x), ?_, ?_⟩
  · show x - x ∈ (ValuativeRel.valuation k).integer
    rw [sub_self]
    exact zero_mem _
  · intro y hy
    have hy' : ψ₁ (y - x) = 1 := h1 _ ((Valuation.mem_integer_iff _ _).mp hy)
    calc ψ₁ y = ψ₁ ((y - x) + x) := by rw [sub_add_cancel]
      _ = ψ₁ (y - x) * ψ₁ x := AddChar.map_add_eq_mul _ _ _
      _ = ψ₁ x := by rw [hy', one_mul]

theorem global_character_holds : G4 := by
  intro E _ _ _ a ha π w
  obtain ⟨ψ₁, hψ⟩ := GlobalTheory.SplitWeil.Model.exists_hasConductor (k := w.adicCompletion E)
  have hne : ψ₁ ≠ 1 := by
    rintro rfl
    exact GlobalTheory.SplitWeil.Model.not_hasConductor_one 1 hψ
  obtain ⟨l, hl0, hl⟩ := GlobalTheory.Published.cuspidalGeneric_holds E a ha π w ψ₁
    (continuous_of_hasConductor_one hψ) hne
  exact ⟨_, psiOK_of_hasConductor hψ, l, hl0, whit_of_isFunctional hl⟩

end GlobalTheory.CompanionTheory.JSBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair

section Alg

variable {k : Type} [Field k]

theorem uM_mul_uM (n : ℕ) (x y : Fin n → k) : uM n x * uM n y = uM n (x + y) := by
  unfold uM
  rw [← map_mul]
  rfl

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hrow : ∀ j : Fin n, GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j
    simp [GlobalTheory.BZMir.glEmbMat]
  have hcorner : GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.BZMir.glEmbMat]
  have hminor : (GlobalTheory.BZMir.glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [GlobalTheory.BZMir.glEmbMat, Fin.succAbove_last]
  have hsign : ((-1 : k) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_row (GlobalTheory.BZMir.glEmbMat k n A) (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, hcorner, hminor, hsign, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, one_mul]

theorem det_one_add_colMat (n : ℕ) (v : Fin n → k) : (1 + colMat k n v).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = Fin.last n
    · subst hi
      simp [GlobalTheory.BZMir.colMat]
    · simp [GlobalTheory.BZMir.colMat, hi]
  · intro i j hji
    change j < i at hji
    have hj : j ≠ Fin.last n := by
      intro h
      subst h
      exact absurd hji (not_lt.mpr (Fin.le_last i))
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp [GlobalTheory.BZMir.colMat, hj]

theorem det_uM (n : ℕ) (y : Fin n → k) :
    GeneralLinearGroup.det ((uM n y : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.MirPair.det_one_add_colMat n y

theorem det_levi (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact GlobalTheory.CompanionTheory.MirPair.det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)

theorem uM_mul_levi (n : ℕ) (g : GL (Fin n) k) (x : Fin n → k) :
    uM n x * levi k n g =
      levi k n g * uM n (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) := by
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n g
    (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))
  have hx : (g : Matrix (Fin n) (Fin n) k) *ᵥ (Multiplicative.toAdd
      (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))) = x := by
    rw [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hx] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.symm

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem coef_rules (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) (hB : TwInv T T' B s) :
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧
    (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'),
      coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) *
          coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  unfold GlobalTheory.CompanionTheory.MirPair.TwInv at hB
  have hT : ∀ (a b : GlobalTheory.BZMir.Mir k (n + 1)) (w : V), T a (T b w) = T (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM]
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    have hxy : y + (x - y) = x := by abel
    have h := hB (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) y) (T (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) (x - y)) v) v'
    rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_uM, map_one, Units.val_one, one_mul,
      hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM, hxy] at h
    exact h
  · intro g x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_levi, ← hT, hB, GlobalTheory.SmGL.detChar_apply,
      GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_levi]

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCompactModParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coc

theorem continuous_levi_mir (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (levi k n) := by
  have hval : Continuous fun g : GL (Fin n) k => GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_val
  have hinv : Continuous fun g : GL (Fin n) k =>
      GlobalTheory.BZMir.glEmbMat k n ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_coe_inv
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hval
  · exact hinv

theorem hgp_cocompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
      ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := by
  intro k _ _ _ _ i t
  refine ⟨GlobalTheory.BZMir.levi k ((i + 1) + t) ''
      (GlobalTheory.SplitWeil.KO k (Fin ((i + 1) + t)) : Set (GL (Fin ((i + 1) + t)) k)),
    GlobalTheory.SplitFlip.isCompact_KO.image (GlobalTheory.CompanionTheory.BZPhiPG.Coc.continuous_levi_mir k _), ?_⟩
  intro g
  obtain ⟨p, w, hw, hx⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t)))
    (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) g)
  refine ⟨g * (GlobalTheory.BZMir.levi k _ w)⁻¹, ?_, GlobalTheory.BZMir.levi k _ w, ⟨w, hw, rfl⟩,
    (inv_mul_cancel_right g _).symm⟩
  have hmem : ∀ (g : Mir k ((i + 1) + t)),
      g ∈ MirabolicParabolic k (i + 1) t ↔
        mirabolicProjection k ((i + 1) + t) g ∈ parab k (two (stdSum (rfl : (i + 1) + t = (i + 1) + t))) := by
    intro g
    have hlast : ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (Fin.last ((i + 1) + t)) = GlobalTheory.BZMir.eLast k ((i + 1) + t) :=
      (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin ((i + 1) + t + 1)) k)).1 g.2
    have hproj : ∀ a b : Fin ((i + 1) + t),
        ((mirabolicProjection k ((i + 1) + t) g : GL (Fin ((i + 1) + t)) k) : Matrix _ _ k) a b =
          ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
    simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
      Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
    constructor
    · intro h b a
      convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    · intro h b a
      induction b using Fin.lastCases with
      | last =>
        have h0 : ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix _ _ k)
            (Fin.last ((i + 1) + t))
            (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t) (Sum.inl a))) = 0 := by
          rw [hlast]
          simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
          rw [if_neg (Fin.castSucc_lt_last _).ne]
        convert h0 using 2 <;> apply Fin.ext <;>
          simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
      | cast b =>
        convert h b a using 2 <;> apply Fin.ext <;>
          simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  rw [hmem]
  have hlevi : mirabolicProjection k ((i + 1) + t) (levi k _ w) = w := by
    apply Units.ext
    ext a b
    show GlobalTheory.BZMir.glEmbMat k _ (w : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
    simp [GlobalTheory.BZMir.glEmbMat]
  have hproj : GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) (g * (GlobalTheory.BZMir.levi k _ w)⁻¹) = p := by
    rw [map_mul, map_inv, hlevi, hx, mul_inv_cancel_right]
  rw [hproj]
  exact p.2

end GlobalTheory.CompanionTheory.BZPhiPG.Coc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinear
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair.EvLin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM (k := k) n 0 = 1 := by
  simp only [uM, ofAdd_zero, map_one]

theorem continuous_coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T)
    (v : V) (v' : V') : Continuous (coef T B v v') := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => uM n (y - x)) ⁻¹' {g | T g v = v}, (hT v).preimage
    ((continuous_uM n).comp (continuous_id.sub continuous_const)), ?_, fun y hy => ?_⟩
  · simp [uM_zero]
  · have hy' : T (uM n (y - x)) v = v := hy
    have h : uM n y = uM n x * uM n (y - x) := by
      rw [← uM_add, add_sub_cancel]
    simp only [coef, h, map_mul, Module.End.mul_apply, hy']

theorem continuous_wt (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) : Continuous (wt ψ n) :=
  continuous_subtype_val.comp (hψ.comp (continuous_apply _).neg)

variable [MeasurableSpace k] [BorelSpace k]

theorem integrableOn_box (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) (v : V) (v' : V') (t : kˣ) :
    IntegrableOn (fun x => wt ψ n x * coef T B v v' x) (box (n + 1) t : Set (Fin (n + 1) → k))
      (piHaar ν (n + 1)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : IsFiniteMeasureOnCompacts (piHaar ν (n + 1)) := by
    unfold piHaar
    infer_instance
  exact ((continuous_wt ψ hψ n).mul (continuous_coef T B hT v v')).continuousOn.integrableOn_compact
    (isCompact_box _ t)

theorem coef_add_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v₁ v₂ : V) (v' : V')
    (x : Fin n → k) : coef T B (v₁ + v₂) v' x = coef T B v₁ v' x + coef T B v₂ v' x := by
  simp [coef]

theorem coef_smul_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B (z • v) v' x = z * coef T B v v' x := by
  simp [coef]

theorem coef_add_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v₁ v₂ : V')
    (x : Fin n → k) : coef T B v (v₁ + v₂) x = coef T B v v₁ x + coef T B v v₂ x := by
  simp [coef]

theorem coef_smul_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B v (z • v') x = z * coef T B v v' x := by
  simp [coef]

theorem exists_common_threshold {P Q : kˣ → Prop}
    (hP : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t)
    (hQ : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → Q t) :
    ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t ∧ Q t := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
  · exact ⟨b, fun t ht => ⟨ha t (h.trans ht), hb t ht⟩⟩
  · exact ⟨a, fun t ht => ⟨ha t ht, hb t (h.trans ht)⟩⟩

theorem evVal_bilinear (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) :
    (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ →
      EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧
    (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ →
      EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  refine ⟨fun v₁ v₂ v' A₁ A₂ h₁ h₂ => ?_, fun z v v' A h => ?_, fun v v₁ v₂ A₁ A₂ h₁ h₂ => ?_,
    fun z v v' A h => ?_⟩
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_left, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v₁ v' t) (integrableOn_box ν ψ T B hψ hT v₂ v' t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_left, mul_left_comm _ z]
    exact integral_const_mul z _
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_right, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v v₁ t) (integrableOn_box ν ψ T B hψ hT v v₂ t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_right, mul_left_comm _ z]
    exact integral_const_mul z _

theorem evVal_additive_homogeneous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ → EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧ (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ → EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT
  exact evVal_bilinear ν ψ T B hψ hT

end GlobalTheory.CompanionTheory.MirPair.EvLin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolicStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (m j : ℕ),
      MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro k _ _ _ _ m j g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  have hne : eGP m j ⟨true, b⟩ ≠ eGP m j ⟨false, a⟩ := by
    intro h
    have hval := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val,
      GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val] at hval
    have ha := a.isLt
    omega
  rw [hmat]
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat,
    ite_eq_right (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a), ite_eq_right hne,
    add_zero]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMemStatement
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_conjugate_inverse_mem : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ {φ : GA E a → ℂ}, φ ∈ Sm E a → (fun g => star (φ (invA E a g))) ∈ Sm E a := by
  first | exact @GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | exact GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm <;> assumption)
end

