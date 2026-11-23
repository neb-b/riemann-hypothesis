module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Development.WeilBound.ThetaLifts.LatticeBasics.Unfold0
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitaryCharEqOneOfTrivialRationalSplitPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitaryCharacterTrivialGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0005
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBasePolFin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem polFin_k {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  obtain ⟨U, h0, h1⟩ : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      have hgauss : M.IsGauss B.ψ B.emb (A f₀) := by
        obtain ⟨ε, hε⟩ := h₀
        refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
        set N := (mat k⁻¹).transpose with hN
        have hNk : N * (mat k).transpose = 1 := by
          rw [hN, ← Matrix.transpose_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.transpose_one]
        have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have hf1 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hf
        have hf2 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu' hf'
        have i1 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀
        have i2 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀
        rw [e1, ← hf1] at i1
        rw [e2, ← hf2] at i2
        have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (B.emb w))) (W.θ w) := fun w => by
          have hc : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
          have h1 : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
          have h2 : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
          show _ * _ = _ * _
          calc (mat k⁻¹).map (piInf (B.emb w)) * W.θ w
              = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w * ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by
                rw [h2, Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) * (mat k⁻¹).map (piInf (B.emb w)) := by
                simp only [Matrix.mul_assoc]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * ((mat k).map (piInf (B.emb w)) * W.θ w) * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [hc.eq]
            _ = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hrel' : ∀ w, (u' * N).map (piInf (B.emb w)) =
            (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (B.emb w)) * (W.θ w).transpose) := fun w => by
          have hN' : N.map (piInf (B.emb w)) = ((mat k⁻¹).map (piInf (B.emb w))).transpose := by
            rw [hN, Matrix.transpose_map]
          have hc : (W.θ w).transpose * N.map (piInf (B.emb w)) = N.map (piInf (B.emb w)) * (W.θ w).transpose := by
            rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
          rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
          simp only [Matrix.mul_assoc, hc]
        have hg := hε (u * N) (u' * N) (PositivityTheory.ThKOwn.KPol.at_mul hu N) (PositivityTheory.ThKOwn.KPol.at_mul hu' N) hrel' _ _
          (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀) (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀)
        rw [← i1, ← i2, hg, map_smul]
      obtain ⟨ε, hε⟩ := hgauss
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtN
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def PolSch_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ PolData B M, Φ ∈ schA F _
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def DblX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ h g g' x, IsEmb g g' x →
        detInv χW g' * thetaSum F (om₂ x (S h (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g' h) ∧
        detInv χW g' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (g, 1) Φ₁) (star (om (g', 1) Φ₂))) ∧
      IsDblCoordX M dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν
def BoxSecX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M, IsSec K χ (((d : ℂ) - n) / 2) (fun x => l (om x (boxFun Φ₁ (star Φ₂))))
def SWFullX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧ (((d : ℂ) - n) / 2) ∈ U ∧
        ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstStmt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
variable {n d : ℕ}
variable {X : Spc F E n} {W : Spc F E d}
end Pair
def EpsOf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (X : Spc F E n) (r s : ℕ), (X.IsHerm σ B r s ∨ X.IsSkew σ B r s) → EpsHerm σ X.J ∧ r + s = n ∧ ∀ fr : Frame σ X.J, fr.IsGood → fr.r ≤ min r s
def CoefEq_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ (g : UA σ X.J) (h : UA σ W.J) (z : Ten F E n d), coef F B.ψ μ (om (g, h) Φ₁) (om (g, h) Φ₂) (M.co.e z) = coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * z * (mat h⁻¹)ᵀ))
def CoefBd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ φ₁ ∈ SB (Fin n × Fin d → Af F), ∀ φ₂ ∈ SB (Fin n × Fin d → Af F), ∀ N : ℕ, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧ IsCompact C ∧ ∀ (f₁ f₂ : SInf F (Fin n × Fin d)) (z : Ten F E n d), ‖coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (M.co.e z)‖ ≤ p f₁ * p f₂ * maj B.emb C N z
end PositivityTheory.ThKEst
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacStmt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKF
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
def ArchOp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T, IsArchOp om (g, h) T ∧
      (g ∈ KInf σ X B.emb → h ∈ KInf σ W B.emb → ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb)
end PositivityTheory.ThKF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStab
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem stabEx_k : _root_.GlobalTheory.ThK.StabEx_k := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hc := _root_.PositivityTheory.ThKG.Tow.Stab.isCompact_stabK_k hB hX
  obtain ⟨μK, hμK⟩ := Stab.exists_haar_of_isCompact _ hc
  obtain ⟨μ, hμ⟩ := Stab.exists_haar_idele (F := F) (E := E)
  exact ⟨Stab.stabK B X, μK, μ, Stab.isStab_stabK B X, hc, hμK, hμ⟩
end PositivityTheory.ThKG.Tow
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStmt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
def ModelEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∃ M : Model σ X W, M.IsGood B.ψ
def WeilEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om
def PairEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → (∃ M : Model σ X W, M.IsGood B.ψ) ∧
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
      ∀ M : Model σ X W, M.IsGood B.ψ → ∃ om, _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s'
theorem pairEx_of_k (h₁ : _root_.PositivityTheory.ThKG.Tow.ModelEx_k) (h₂ : _root_.PositivityTheory.ThKG.Tow.WeilEx_k) : _root_.PositivityTheory.ThKG.Tow.PairEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  refine ⟨h₁ F E σ B hB n d X W r s r' s' hX hW, fun χX χW a b c e M hM => ?_⟩
  obtain ⟨om, hom⟩ := h₂ F E σ B hB n d X W r s r' s' hX hW M hM χX χW a b c e
  exact ⟨om, hB, hX, hW, hM, a, b, c, e, hom⟩
end PositivityTheory.ThKG.Tow
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Unfold0K
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}
theorem unfold0_k : _root_.GlobalTheory.ThK.Dbl.Unfold0_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * (detInv χ g * φ (h * g))
  have ik : Integrable k μ := hi.mul_bdd (c := C)
    ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
    (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have := An.unfold hD (ik.comp_mul_left h⁻¹)
  rw [integral_mul_left_eq_self k] at this
  simp only [mul_assoc]
  refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this
  refine (((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)
  simp only [k]
  rw [← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]
  have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
  simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
  linear_combination (-(f (e (h, δ * g)) * detInv χ g * φ g)) * this
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitCoefK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
theorem unit_coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (w₀ : WOF F E nS (nT + nT)) (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitaryCharacterTrivialOfLocal
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.unitary_character_trivial_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : Formalism.IndefR.DatumF.GAF σ J →* Circle, Continuous ν → (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ν γ = 1) →
        (∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e → ∀ g, Formalism.IndefR.DatumF.SuppAtF σ e J g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @_root_.PositivityTheory.ThKW.unitary_character_trivial_global | exact _root_.PositivityTheory.ThKW.unitary_character_trivial_global | (intros; apply _root_.PositivityTheory.ThKW.unitary_character_trivial_global <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilDatumSplittingCharacters
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_splitting_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  first | exact @_root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | exact _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | (intros; apply _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRationalSupportBound
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0
open Grow
theorem weil_rational_support_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, -, hC⟩ := htBd F E σ n d X W M
  obtain ⟨m₀, hm₀, h₀⟩ := finInv F _ B.ψ hP.base.std Φ hΦ
  obtain ⟨D, hD, hDD⟩ := exists_dual_den F
  refine ⟨D * m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨m, hm, hmC, hb⟩ := hC g h
  refine ⟨D * (m₀ * m), Nat.mul_pos hD (Nat.mul_pos hm₀ hm), ?_, fun ξ hξ i => ?_⟩
  · push_cast
    rw [pow_one, mul_assoc, mul_assoc]
    gcongr
  · rw [Nat.cast_mul D, mul_assoc]
    refine hDD _ fun y => trace_int hP.base.std _ ?_
    let u : AF F := (0, (algebraMap F (AF F) (y : F)).2)
    have hu : IntF u := ⟨rfl, fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v y⟩
    have h0 : IntF (0 : AF F) := ⟨rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
    have key := congrFun (h₀ _ _ _ _ (impl_sOf hP.weil g h) hb (0, Pi.single i u) ⟨fun _ => h0, fun j => by
      by_cases e : j = i
      · subst e; simpa using hu
      · simpa [e] using h0⟩) fun i => algebraMap F (AF F) (ξ i)
    simp only [schr, Prod.smul_mk, smul_zero, add_zero, Pi.zero_apply, zero_mul, mul_zero, dotProduct_smul,
      dotProduct_single] at key
    rw [← mul_right_cancel₀ hξ (key.trans (one_mul _).symm)]
    refine congrArg B.ψ (Prod.ext ?_ ?_)
    · change (0 : Ainf F) = ((m₀ * m : ℕ) : AF F).1 * ((algebraMap F (AF F) (ξ i)).1 * 0)
      rw [mul_zero, mul_zero]
    · rw [map_mul, map_mul, map_natCast, mul_assoc]
      rfl
end PositivityTheory.ThKF0
end
end

