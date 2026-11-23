module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjections
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem mul_eq_mul_diagonal_of_comm {R : Type} [CommRing R] {n r : ℕ} {G : Matrix (Fin n) (Fin n) R}
    {C : Matrix (Fin n) (Fin r) R} {L : Matrix (Fin r) (Fin n) R} (hL : L * C = 1)
    (hc : ∀ i, G * Matrix.vecMulVec (fun k => C k i) (L i) = Matrix.vecMulVec (fun k => C k i) (L i) * G) :
    G * C = C * Matrix.diagonal (fun i => (L * (G * C)) i i) := by
  ext k i
  have h := congrArg (fun M => (M * C) k i) (hc i)
  simp only [Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_apply] at h
  have h1 : (L i ᵥ* C) i = 1 := by
    have := congrFun (congrFun hL i) i
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
  rw [h1, mul_one] at h
  rw [Matrix.mul_diagonal, ← Matrix.mul_assoc]
  simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct] using h

theorem mem_leviMin_of_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW γ hγ hcomm
  have hF := pfrA h hJ hW
  have hinj : Function.Injective (inclR (F := F) (AF F) : E → AF F ⊗[F] E) := fun a b hab =>
    congrFun (GlobalTheory.CompanionTheory.RedCov.ratV_injective (F := F) (E := E) (n := 1)
      (show ratV F (fun _ : Fin 1 => a) = ratV F (fun _ : Fin 1 => b) from funext fun _ => hab)) 0
  have key : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin n) (Fin n) E,
      (matHom _ σ J p).1 = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    have hp2 : (p.1 : GL (Fin n) (AF F ⊗[F] E)) ∈
        Subgroup.map (Formalism.UG.bc (inclR (F := F) (AF F))) (Formalism.UG.UJ (σ : E →+* E) J) := hp
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 hp2
    refine ⟨g.1, ?_⟩
    rw [show (matHom _ σ J p).1 = ((p.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) _) from rfl, ← hg]
    rfl
  have bmRat : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin r) (Fin r) E,
      Bm σ J X Y p = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    obtain ⟨M, hM⟩ := key p hp
    refine ⟨cT (σ : E →+* E) Y * J * (M * X), ?_⟩
    rw [Bm, coefM, hM, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hrow : ∀ C : Matrix (Fin n) (Fin r) E,
      cT (sigR (AF F) σ) (adMat F C) * JR (AF F) J = (cT (σ : E →+* E) C * J).map (inclR (F := F) (AF F)) := by
    intro C
    rw [Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hP : ∀ (C D : Matrix (Fin n) (Fin r) E) (i : Fin r),
      (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
        Matrix.vecMulVec (fun k => adMat F C k i)
          ((cT (sigR (AF F) σ) (adMat F D) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) i) := by
    intro C D i
    rw [hrow]
    ext a b
    simp only [lineProj, rowOf, Matrix.vecMulVec_apply, Matrix.map_apply, adMat, map_mul]
  have hX := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.yx (fun i => by
    have := hcomm (Sum.inl i)
    rwa [projFam, Sum.elim_inl, hP] at this)
  have hY := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.xy (fun i => by
    have := hcomm (Sum.inr i)
    rwa [projFam, Sum.elim_inr, hP] at this)
  refine ⟨⟨_, _, hX, hY⟩, ⟨Matrix.diagonal _, Matrix.blockTriangular_diagonal _, hX, fun i => ?_⟩⟩
  have hp : γ ∈ minPar σ J X := ⟨_, Matrix.blockTriangular_diagonal _, hX⟩
  have hp' := inv_mem_minPar h hJ hW hp
  refine ⟨uU σ J X Y h hJ hW hp hp' i, ?_, ?_⟩
  · rw [val_uU h hJ hW hp hp' i, Bm_eq hF hX]
  · obtain ⟨M, hM⟩ := bmRat γ hγ
    obtain ⟨M', hM'⟩ := bmRat γ⁻¹ (inv_mem hγ)
    have hu1 : ((uU σ J X Y h hJ hW hp hp' i : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M i i) := by
      rw [val_uU h hJ hW hp hp' i, hM]
      rfl
    have hu2 : (((uU σ J X Y h hJ hW hp hp' i)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M' i i) := by
      show Bm σ J X Y γ⁻¹ i i = _
      rw [hM']
      rfl
    have he : M i i * M' i i = 1 := hinj (by rw [map_mul, ← hu1, ← hu2, Units.mul_inv, map_one])
    have he' : M' i i * M i i = 1 := by rw [mul_comm]; exact he
    have hu : uU σ J X Y h hJ hW hp hp' i =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* AF F ⊗[F] E) ⟨M i i, M' i i, he, he'⟩ :=
      Units.ext (by rw [hu1]; rfl)
    rw [hu]
    exact GlobalTheory.Doubling.absE_inclR _

end GlobalTheory.CompanionTheory.ParCocompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShift
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.ConjEv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_box_iff_forall_valuation_le {m : ℕ} {s : kˣ} {x : Fin m → k} :
    x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s ↔ ∀ j, valuation k (x j) ≤ valuation k (s : k) :=
  Iff.rfl

theorem exists_mulVec_box (m : ℕ) (g : Matrix (Fin m) (Fin m) k) (t : kˣ) :
    ∃ t' : kˣ, ∀ x ∈ box m t, g *ᵥ x ∈ box m t' := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact ⟨t, fun x _ => mem_box_iff_forall_valuation_le.2 fun j => isEmptyElim j⟩
  obtain ⟨ij, hij⟩ := Finite.exists_max (fun ij : Fin m × Fin m => valuation k (g ij.1 ij.2))
  by_cases h0 : g ij.1 ij.2 = 0
  · refine ⟨t, fun x _ => ?_⟩
    have hg : g = 0 := by
      ext i j
      simpa [h0] using hij (i, j)
    rw [hg, Matrix.zero_mulVec]
    exact zero_mem _
  · refine ⟨Units.mk0 _ h0 * t, fun x hx => ?_⟩
    rw [mem_box_iff_forall_valuation_le] at hx ⊢
    intro i
    show valuation k (∑ j, g i j * x j) ≤ _
    refine Finset.sum_induction _ (fun y => valuation k y ≤ valuation k ((Units.mk0 _ h0 * t : kˣ) : k))
      (fun a b ha hb => (valuation k).map_add_le ha hb) (by simp) (fun j _ => ?_)
    rw [map_mul, Units.val_mul, map_mul, Units.val_mk0]
    exact mul_le_mul' (hij (i, j)) (hx j)

theorem box_mono {m : ℕ} {t t' : kˣ} (h : valuation k (t : k) ≤ valuation k (t' : k)) :
    ∀ x ∈ box m t, x ∈ box m t' := by
  intro x hx
  rw [mem_box_iff_forall_valuation_le] at hx ⊢
  exact fun j => le_trans (hx j) h


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_mul_inv_le {c r t : kˣ} (h : valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t : k)) :
    valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  have e1 : c * t⁻¹ = (c * r⁻¹) * (r * t⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left]
  have e2 : t * (r * t⁻¹) = r := by
    rw [mul_comm r, ← mul_assoc, mul_inv_cancel, one_mul]
  calc valuation k ((c * t⁻¹ : kˣ) : k)
      = valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((r * t⁻¹ : kˣ) : k) := by
        rw [e1, Units.val_mul, map_mul]
    _ ≤ valuation k (t : k) * valuation k ((r * t⁻¹ : kˣ) : k) := mul_le_mul' h le_rfl
    _ = valuation k (r : k) := by
        rw [← map_mul, ← Units.val_mul, e2]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem wt_mir (ψ : AddChar k Circle) {n : ℕ} (p : Mir k n) (y : Fin (n + 1) → k) :
    wt ψ n (((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) = wt ψ n y := by
  unfold GlobalTheory.CompanionTheory.MirPair.wt
  rw [GlobalTheory.BZMir.mulVec_last_of_mem k _ p.2]

theorem absPow_succ_val (s : ℕ) (u : kˣ) :
    ((absPow k ((s + 1 : ℕ) : ℂ) u : ℂˣ) : ℂ) = ((absPow k (s : ℂ) u : ℂˣ) : ℂ) * ((nabs k u : ℝ) : ℂ) := by
  rw [show ((s + 1 : ℕ) : ℂ) = (s : ℂ) + 1 by push_cast; ring, GlobalTheory.SmGL.absPow_add,
    MonoidHom.mul_apply, Units.val_mul, GlobalTheory.SmGL.val_absPow k 1, Complex.cpow_one]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
  (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ)

theorem JJ_conj (hB : TwInv T T' B s) (p : Mir k n) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') :
    JJ ν ψ T B M (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
        (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') =
      ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
        JJ ν ψ T B {y | ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} v v' := by
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hw : ∀ x : Fin (n + 1) → k, GlobalTheory.CompanionTheory.MirPair.wt ψ n x =
      GlobalTheory.CompanionTheory.MirPair.wt ψ n
        ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := GlobalTheory.CompanionTheory.MirPair.ConjEv.wt_mir ψ p⁻¹ x
    rw [Subgroup.coe_inv] at h
    exact h.symm
  have hF := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (p : GL (Fin (n + 1)) k) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n y * GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  have key : ∀ x : Fin (n + 1) → k,
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x *
                   GlobalTheory.CompanionTheory.MirPair.coef T B (T (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
                     (T' (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') x =
        ((GlobalTheory.SmGL.detChar (Fin (n + 1)) (GlobalTheory.SmGL.absPow k (s : ℂ))
            (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
          (GlobalTheory.CompanionTheory.MirPair.wt ψ n
                       ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) *
            GlobalTheory.CompanionTheory.MirPair.coef T B v v'
              ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
    intro x
    rw [hlevi, ← hw]
    ring
  unfold GlobalTheory.CompanionTheory.MirPair.JJ
  simp only [key]
  rw [integral_const_mul, hF, ← mul_assoc]
  congr 1
  rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.ConjEv.absPow_succ_val]

end GlobalTheory.CompanionTheory.MirPair.ConjEv

namespace GlobalTheory.CompanionTheory.MirPair

theorem evVal_conj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB p v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box ν ψ c T T' B s hψ hc hT hT' hB
    (p : GL (Fin (n + 1)) k) v v'
  obtain ⟨t₁, ht₁₀, ht₁r⟩ : ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t₁ : k) := by
    rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
    · exact ⟨c * r⁻¹, h, le_rfl⟩
    · exact ⟨t₀, le_rfl, h⟩
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.CompanionTheory.MirPair.ConjEv.exists_mulVec_box (n + 1)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) t₁
  refine ⟨t₂, fun t ht => ?_⟩
  rw [GlobalTheory.CompanionTheory.MirPair.ConjEv.JJ_conj ν ψ T T' B s hB p]
  congr 1
  rw [← ht₀ t₁ ht₁₀]
  exact hr t₁ (GlobalTheory.CompanionTheory.MirPair.ConjEv.val_mul_inv_le ht₁r) t
    (fun x hx => GlobalTheory.CompanionTheory.MirPair.ConjEv.box_mono ht _ (ht₂ x hx))

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishing
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem exists_evVal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB v v'
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box ν ψ c T T' B s hψ hc hT hT' hB 1 v v'
  refine ⟨JJ ν ψ T B (box (n + 1) (c * r⁻¹) : Set (Fin (n + 1) → k)) v v', c * r⁻¹, fun t ht => ?_⟩
  have hc' : valuation k ((c * (c * r⁻¹)⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
    have : c * (c * r⁻¹)⁻¹ = r := by
      rw [_root_.mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
  have hsub : ∀ x ∈ box (n + 1) (c * r⁻¹), ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t := by
    intro x hx
    rw [Units.val_one, one_mulVec]
    rw [mem_box] at hx ⊢
    exact fun i => show valuation k (x i) ≤ valuation k (t : k) from
      le_trans (show valuation k (x i) ≤ valuation k ((c * r⁻¹ : kˣ) : k) from hx i) ht
  have h := hr (c * r⁻¹) hc' t hsub
  rw [← h]
  simp only [Units.val_one, one_mulVec]
  rfl

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.CuspForms

theorem memL2_and_bounded_of_normalised : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  intro hB E _ _ _ a μ _ _ π hπ φ hφ
  have hc := π.cusp φ hφ
  obtain ⟨C, hC⟩ := hB.of_invariant hc (hπ φ hφ)
  exact ⟨memL2_of_isAutForm hc.1 (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC), C, hC⟩

end GlobalTheory.CompanionTheory.CuspForms
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorCommutesInfiniteGlStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_commutes_infinite_gl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    ∀ y : GL (Fin a) (Cinf E),
      GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | exact GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | (intros; apply GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSumStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_eq_casimir_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | exact GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | (intros; apply GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenSupp

theorem isLocallyConstant_ind {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ) :
    IsLocallyConstant (fun g => f.1.1 g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hT := f.2
  refine Filter.mem_of_superset
    ((IsOpen.preimage (f := fun y => g⁻¹ * y) (continuous_const.mul continuous_id) hT).mem_nhds ?_) ?_
  · show _ = _
    simp
  · intro y hy
    have h1 := congrFun (congrArg Subtype.val hy) g
    have h2 : f.1.1 (g * (g⁻¹ * y)) = f.1.1 g := h1
    simpa using h2

theorem support_stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (p : GL (Fin N) k) (hp : p ∈ parab k (stdBlocks d hd)) (g : GL (Fin N) k) (hg : f.1.1 g ≠ 0) :
    f.1.1 (p * g) ≠ 0 := by
  intro h0
  apply hg
  have := parInd_law (stdBlocks d hd) ρ f (⟨p, hp⟩⁻¹) (p * g)
  rw [h0, map_zero, smul_zero] at this
  simpa using this

theorem cell_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : GL (Fin N) k)
    (hg : g ∈ cell k d hd (wOpen d hd)) :
    ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ unipU k d hd, g = p * pm k (wOpen d hd) * u := by
  obtain ⟨p, hp, n, hn, rfl⟩ := hg
  let w := pm k (wOpen d hd)
  let e := stdBlocks d hd
  have hnLower : w * n * w⁻¹ ∈ parab k (opp e) := OpenFactor.conj_mem_parabLower k d hd hn
  let nLower : parab k (opp e) := ⟨w * n * w⁻¹, hnLower⟩
  obtain ⟨v, hv, hnv⟩ := GlobalTheory.SmGL.exists_levi_mul_unip k (opp e) nLower
  let m := leviProj k (opp e) nLower
  have hfactor : w * n * w⁻¹ = leviEmb k e m * v := hnv
  refine ⟨p * leviEmb k e m, mul_mem hp (leviEmb_mem_parab k e m), w⁻¹ * v * w,
    LowerOpen.inv_conj_mem_unipU k d hd hv, ?_⟩
  change p * w * n = p * leviEmb k e m * w * (w⁻¹ * v * w)
  calc
    p * w * n = p * (w * n * w⁻¹) * w := by group
    _ = p * leviEmb k e m * w * (w⁻¹ * v * w) := by rw [hfactor]; group

theorem exists_open_of_le {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U L L₀ : Subgroup G)
    (hL : L ≤ U) (h0 : L₀ ≤ L) (O₀ : Set G) (hO : IsOpen O₀) (hOU : O₀ ∩ (U : Set G) = L₀) :
    ∃ O : Set G, IsOpen O ∧ O ∩ (U : Set G) = L := by
  refine ⟨⋃ l ∈ (L : Set G), (fun x => l⁻¹ * x) ⁻¹' O₀, isOpen_biUnion fun l _ =>
    hO.preimage (continuous_const.mul continuous_id), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨⟨l, hl, hx⟩, hxU⟩
    have : l⁻¹ * x ∈ (L₀ : Set G) := by
      rw [← hOU]
      exact ⟨hx, mul_mem (inv_mem (hL hl)) hxU⟩
    have h2 := mul_mem hl (h0 this)
    simpa using h2
  · intro hx
    have h1 : (1 : G) ∈ (L₀ : Set G) := one_mem L₀
    rw [← hOU] at h1
    exact ⟨⟨x, hx, by simpa using h1.1⟩, hL hx⟩

end GlobalTheory.CompanionTheory.Rodier.OpenSupp


open GlobalTheory.CompanionTheory.Rodier.OpenSupp in
theorem GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  intro k _ _ _ _ h N d hd W _ _ ρ hρ f hf
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  set w := pm k (wOpen d hd) with hw
  set U := unipU k d hd with hU
  set P := parab k (stdBlocks d hd) with hP
  have hUB : U ≤ unipB k (Fin N) := inf_le_left
  have hUc : IsClosed (U : Set (GL (Fin N) k)) := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.2
  obtain ⟨Lj, hmono, hcpt, hle, hexh⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N U hUB hUc
  have hlc := isLocallyConstant_ind d hd ρ f
  let S : Set (GL (Fin N) k) := {g | f.1.1 g ≠ 0}
  have hSo : IsOpen S := hlc ({0}ᶜ)
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff]
    have : Sᶜ = (fun g => f.1.1 g) ⁻¹' {0} := by
      ext g; simp [S]
    rw [this]; exact hlc {0}
  have hcov : ∀ g ∈ S, ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n := by
    intro g hg
    obtain ⟨p, hp, u, hu, rfl⟩ := cell_eq d hd g (hf g hg)
    obtain ⟨j, hj⟩ := hexh u hu
    exact ⟨p, hp, j, u, hj, rfl⟩
  have hSeq : S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n} = S :=
    Set.inter_eq_left.2 hcov
  obtain ⟨j, hj⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset P (GlobalTheory.WhitHered.CellLoc.isClosed_parab _) (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k))
    GlobalTheory.SplitFlip.isCompact_KO (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩) Lj hmono hcpt w S hSo
    (fun p hp g hg => support_stable d hd ρ f p hp g hg) (by rw [hSeq]; exact hSc)
  obtain ⟨L₀, hL₀U, hL₀c, ⟨O₀, hO₀, hO₀U⟩, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump k (1 : AddChar k Circle) (by simpa using (continuous_one : Continuous (1 : k → Circle))) h N d hd ρ hρ 0
  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact
    ((L₀ : Set (GL (Fin N) k)) ∪ (Lj j : Set (GL (Fin N) k))) (hL₀c.union (hcpt j)) (by
      rintro x (hx | hx)
      · exact hUB (hL₀U hx)
      · exact hUB (hle j hx))
  refine ⟨U₀ ⊓ U, inf_le_right, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hU₀c.inter_right hUc
  · exact exists_open_of_le U (U₀ ⊓ U) L₀ inf_le_right
      (fun x hx => ⟨hU₀ (Or.inl hx), hL₀U hx⟩) O₀ hO₀ hO₀U
  · intro g hg
    obtain ⟨p, hp, n, hn, e⟩ := hj g hg (hcov g hg)
    exact ⟨p, hp, n, ⟨hU₀ (Or.inr hn), hle j hn⟩, e⟩
end

