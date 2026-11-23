module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZariskiDenseRationalPointsDefiniteUnitaryCharZer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvecto
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHwT

section Fam

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]


open Classical in
def fam (τ : L →+* K) (B : GL (Fin n) K) : (L →+* K) → GL (Fin n) K := fun σ =>
  if σ = τ then B else if σ = τ.comp (IsCMField.complexConj L : L →+* L) then inside₂ K n B else 1

theorem fam_conj (τ : L →+* K) (B : GL (Fin n) K) (h : τ.comp (IsCMField.complexConj L : L →+* L) ≠ τ)
    (σ : L →+* K) : ((fam τ B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose (((fam τ B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hcc : ∀ σ' : L →+* K, (σ'.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ' := by
    intro σ'
    ext x
    simp [IsCMField.complexConj_apply_apply]
  have hinj : ∀ σ₁ σ₂ : L →+* K, σ₁.comp (IsCMField.complexConj L : L →+* L) = σ₂.comp (IsCMField.complexConj L : L →+* L) → σ₁ = σ₂ := by
    intro σ₁ σ₂ e
    rw [← hcc σ₁, e, hcc]
  by_cases h1 : σ = τ
  · subst h1
    simp only [fam, h, if_false, if_true]
    rfl
  · by_cases h2 : σ = τ.comp (IsCMField.complexConj L : L →+* L)
    · subst h2
      simp only [fam, hcc, if_true, h]
      simp [inside₂]
    · have h3 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ := by
        intro e; apply h2; rw [← e, hcc]
      have h4 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ.comp (IsCMField.complexConj L : L →+* L) :=
        fun e => h1 (hinj _ _ e)
      simp [fam, h1, h2, h3, h4]

theorem fam_eval (τ : L →+* K) (B : GL (Fin n) K) :
    (fun p : (L →+* K) × Fin n × Fin n => ((fam τ B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) =
      Formalism.L2.NX.evPtF (IsCMField.complexConj L : L →+* L) τ B := by
  funext p
  simp only [fam, Formalism.L2.NX.evPtF]
  split_ifs <;> simp_all [inside₂, Matrix.one_apply]

end Fam

section Eig

open Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

theorem bVVfun_mem (lam : ι → DomWeight n) (j : VVIdx lam) : bVVfun K lam j ∈ VV K lam := by
  rw [← (bVVfun_spec K lam).2]
  exact Submodule.subset_span ⟨j, rfl⟩

def wOf (lam : ι → DomWeight n) (u : VVIdx lam → K) : Pol K ι n := ∑ j, u j • bVVfun K lam j

theorem wOf_mem (lam : ι → DomWeight n) (u : VVIdx lam → K) : wOf lam u ∈ VV K lam :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bVVfun_mem lam j)

theorem wOf_ne (lam : ι → DomWeight n) (u : VVIdx lam → K) (hu : u ≠ 0) : wOf lam u ≠ 0 := by
  intro h0
  apply hu
  funext j
  exact Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 u h0 j

theorem wOf_eig (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K)
    (hMV : ∀ F ∈ VV K lam, Formalism.GradedWeylDivisibility.blockAct K M F ∈ VV K lam) (c χ : K) (hc : c ≠ 0) (u : VVIdx lam → K)
    (h : ∀ i, ∑ j, c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M (bVVfun K lam j)) * u j = χ * u i) :
    Formalism.GradedWeylDivisibility.blockAct K M (wOf lam u) = (c⁻¹ * χ) • wOf lam u := by
  classical
  set w := wOf lam u with hw
  set F : VV K lam := ⟨_, hMV w (wOf_mem lam u)⟩ with hF
  have hco : ∀ i, (bVV K lam).repr F i = c⁻¹ * χ * u i := by
    intro i
    have e1 : c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = χ * u i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h i, hw, wOf, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    have e2 : DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = (bVV K lam).repr F i := DDHw.coord_spec lam i F
    rw [← e2, mul_assoc, ← e1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hsum := congrArg Subtype.val ((bVV K lam).sum_repr F)
  rw [Submodule.coe_sum] at hsum
  simp only [Submodule.coe_smul, bVV_coe, hco] at hsum
  show (F : Pol K ι n) = _
  rw [← hsum, hw, wOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

theorem blockAct_mem [DecidableEq ι] (lam : ι → DomWeight n) (τ₀ : ι) (B : GL (Fin n) K) (F : Pol K ι n)
    (hF : F ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F ∈ VV K lam := by
  set g : ι → GL (Fin n) K := fun τ => if τ = τ₀ then B else 1 with hg
  have hgM : (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    by_cases h : τ = τ₀ <;> simp [hg, h]
  have hdet : detTwK lam g ≠ 0 := by
    unfold detTwK
    exact Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have e : actP lam g F = detTwK lam g •
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F := by
    rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct, hgM]
  have h1 := polyAction_mem_VV lam g hF
  rw [e] at h1
  exact (Submodule.smul_mem_iff _ hdet).1 h1

end Eig

section Main

open Formalism.L2.DIV
open scoped Matrix

theorem hw_eigvec_transport : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] [CharZero K] (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb →
    ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu →
      ∃ w : Formalism.L2.DIV.Pol K ι n, w ∈ Formalism.L2.DIV.VV K lam ∧ w ≠ 0 ∧
        ∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
          Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) w =
            ((detPow K n B (lam τ₀).detShift)⁻¹ * ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • w := by
  intro L _ _ _ n ι _ _ K _ _ emb lam hd τ₀ mu hH
  classical
  obtain ⟨ι', _, _, b', P', hP', v, hv, hB⟩ := hH
  have hinj := hd.1
  have hcm := hd.2
  set bD := DDHw.bDD (K := K) lam with hbD
  set Q : Matrix ι' (VVIdx lam) K := b'.toMatrix bD with hQ
  set Q' : Matrix (VVIdx lam) ι' K := bD.toMatrix b' with hQ'
  have hQQ : Q * Q' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hQQ' : Q' * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hrat : ∀ a a', ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
        (P' a a' - ∑ i, ∑ j, MvPolynomial.C (Q a i * Q' j a') * DDHw.tenPF emb lam i j) = 0 := by
    intro a a' γ₀ hγ
    obtain ⟨γ, rfl⟩ := ratHom_surjective L n γ₀ hγ
    have hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((ratHom (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      rw [show ratHom (L := L) (n := n) γ = ratFun γ from rfl, ← incGL_ratFun γ]
      rfl
    have h1 := congrFun (congrFun (hP' γ _ hm) a) a'
    have h2 : LinearMap.toMatrix b' b' ((wtRepF emb lam).dual γ) =
        Q * LinearMap.toMatrix bD bD ((wtRepF emb lam).dual γ) * Q' :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' bD b' bD _).symm
    rw [hbD, DDHw.dd_toMatrix, DDHw.tenRepF_toMatrix emb lam γ _ hm] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, ← h1, h2, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, Matrix.mul_apply, Finset.sum_mul]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set u : VVIdx lam → K := Q' *ᵥ v with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv
    have e : Q *ᵥ u = v := by rw [hu, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
    rw [← e, h0, Matrix.mulVec_zero]
  refine ⟨wOf lam u, wOf_mem lam u, wOf_ne lam u hu0, fun B hBt => ?_⟩
  have hne : (emb τ₀).comp (IsCMField.complexConj L : L →+* L) ≠ emb τ₀ := fun h' => hcm τ₀ τ₀ h'.symm
  set T : Matrix (VVIdx lam) (VVIdx lam) K := Matrix.of fun i j =>
    MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (DDHw.tenPF emb lam i j) with hT
  have hev : ∀ a a', MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a') =
      ∑ i, ∑ j, Q a i * Q' j a' * T i j := by
    intro a a'
    have h0 := _root_.GlobalTheory.UnitaryDense.unitary_points_dense L n K _ (hrat a a') (fam (emb τ₀) B) (fam_conj _ B hne)
    rw [fam_eval, map_sub, sub_eq_zero] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hT, Matrix.of_apply]
  have hmat : (Matrix.of fun a a' => MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a')) =
      Q * T * Q' := by
    ext a a'
    rw [Matrix.of_apply, hev, Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set χ : K := ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a with hχ
  have hTu : T *ᵥ u = χ • u := by
    have h1 := hB B hBt
    rw [hmat] at h1
    have e : Q' *ᵥ ((Q * T * Q') *ᵥ v) = T *ᵥ u := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [← e, h1, Matrix.mulVec_smul]
  set c : K := detPow K n B (lam τ₀).detShift with hc
  have hc0 : c ≠ 0 := by
    rw [hc, detPow]
    exact Units.ne_zero _
  have hM : (fun τ => (Matrix.of fun a b => NX.evPtF (DDHw.cL L) (emb τ₀) B (emb τ, a, b)).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    split_ifs with hτ
    · rw [hτ, DDHw.evPtF_self]
    · rw [DDHw.evPtF_other _ _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]
  have hTe : ∀ i j, T i j = c * DDHw.coord lam i
      (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) (bVVfun K lam j)) := by
    intro i j
    rw [hT, Matrix.of_apply, DDHw.tenPF_eval]
    erw [DDHw.detTwistPolynomial_eval_embeddingPoint emb hd lam τ₀ B]
    rw [← hM]
  refine wOf_eig lam _ (blockAct_mem lam τ₀ B) c χ hc0 u fun i => ?_
  have := congrFun hTu i
  simp only [Matrix.mulVec, dotProduct, hTe, Pi.smul_apply, smul_eq_mul] at this
  exact this

end Main

end GlobalTheory.AlgWtF.DDHwT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

private theorem levEx_of_levelPrimes_eq (D : D7) (S : Finset ℕ) (g : Fin 2 → ℕ) (a b c : ℕ) (hS : S = {g 0, g 1, a, b, c})
    (hlev : ∀ p, p ∈ D.host.levelPrimes ↔ p ∈ S ∨ ∃ u, p = (D.mem u).A.T)
    (hg : ∀ i, D.host.g i = g i) (ha : D.host.pde = a) (hb : D.host.pde' = b) (hc : q0Av D = c) : LevEx D := by
  intro p
  rw [hlev, hS]
  simp only [Finset.mem_insert, Finset.mem_singleton, hg, ha, hb, hc, Fin.exists_fin_two]
  tauto

theorem levEx_of_over : ∀ (D : D7) (P : PreCh) (Lv : LevCh P), Over D P Lv →
    P.H.levelPrimes = {P.H.g 0, P.H.g 1, P.H.pde, P.H.pde', DC.q0H P.H} → LevEx D ∧ ∀ N h, LevEx (setDiv D N h) := by
  intro D P Lv hO hlev
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hX, rfl⟩ := hO
  refine (fun hD => ⟨hD, fun _ _ => hD⟩) ?_
  obtain ⟨B, C, W, V, S, Ns, G⟩ := X
  cases B
  dsimp only at hX
  subst hX
  refine levEx_of_levelPrimes_eq _ P.H.levelPrimes P.H.g P.H.pde P.H.pde' (DC.q0H P.H) hlev ?_ (fun _ => rfl) rfl rfl ?_
  · intro p
    have hT' := C.A_T
    show p ∈ P.H.levelPrimes ∪ Finset.univ.image Lv.T ↔ _
    rw [Finset.mem_union, Finset.mem_image]
    exact or_congr Iff.rfl
      ⟨fun ⟨u, _, hu⟩ => ⟨u, hu.symm.trans (hT' u).symm⟩, fun ⟨u, hu⟩ => ⟨u, Finset.mem_univ _, (hT' u).symm.trans hu.symm⟩⟩
  · unfold q0Av DC.q0H rPrAv DC.rPrH LevelStarExponents.condE
    rfl

end GlobalTheory.Mem.HD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
section
open Formalism.BasicNotions GlobalTheory.Mem.HD

theorem GlobalTheory.Mem.HD.levelTied_of_levEx : ∀ D : D7, LevEx D → Formalism.L2.Host.LevelTied D :=
  fun D h => ⟨fun p => by
    have hq : Formalism.MainNotions.q0Av D = Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D := rfl
    simpa [hq] using h p⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df.RowsEx

theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)

end GlobalTheory.Mem.Df.RowsEx

open GlobalTheory.Mem.Df.RowsEx in
theorem GlobalTheory.Mem.Df.rowsDef_nonempty : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), Nonempty (RowsDef I l hX) := by
  intro B X I hI hP l hX
  classical
  have hb := fun a => _root_.GlobalTheory.Mem.Df.mtHL_good_basis I hX a
  choose j hj using fun a => (hb a).2.1
  have hA := fun a => _root_.GlobalTheory.exists_equiv_normAt_eq_norm B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1
    (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)
  choose n gA hgA using hA
  have hme := _root_.GlobalTheory.Mem.Df.mtCx_equiv_per I hI hP l hX
  choose mq hmq using hme
  let jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a)) := fun a => (gA a).toLinearMap.comp (j a)
  letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV
  haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV
  have hL := fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V
    (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1
    (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by
      have h2 := (hb a).2.2.2
      simp only [← hj] at h2
      have : (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i)) := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))
  choose L hLc hLg hLy hLs using hL
  let mt : B.places.Pl → (I.cols l).Tup := fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  have hmt : ∀ w, mt (B.places.conj w) = mt w := fun w => by
    simp only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]
  obtain ⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩ :=
    _root_.GlobalTheory.Mem.DfGen.exists_rowsRest_std B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0))
      (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (_root_.GlobalTheory.Mem.Df.cols_pos I hI hP l hX)
  letI := W.instAmb
  letI := W.instAmbi
  refine ⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩
  refine
    { muAt := hmuAt
      muTw := hmuTw
      eMt0 := ?_
      eMtTw := ?_
      norm := ?_
      lat := ?_
      gen := ?_
      eOp := heOp
      ze := hze }
  · intro u F
    have h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F) :=
      (he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))
    have h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F := by
      rw [← h]; exact (W.eMt0 u).symm_apply_apply _
    have hs := hmq u I.mu0 F
    rw [← h'] at hs
    exact hs
  · intro u a F
    have h : W.eMtTw u a (mq u a F) = g a (gA a F) :=
      (heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))
    have h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F := by
      rw [← h]; exact (W.eMtTw u a).symm_apply_apply _
    have hs := hmq u a F
    rw [← h'] at hs
    exact hs
  · intro a x
    have h := (g a).norm_map (gA a (toCx I hX a x))
    exact (hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)
  · intro a y
    constructor
    · intro hy
      have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')
      refine ⟨x, hx, ?_⟩
      have h1 : gA a (toCx I hX a x) = (g a).symm y := (congrArg (gA a) (hj a x)).symm.trans hxy
      have h2 : g a (gA a (toCx I hX a x)) = y := by rw [h1]; simp
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have h1 : jj a x = gA a (toCx I hX a x) := congrArg (gA a) (hj a x)
      have h2 : g a (jj a x) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)
      rw [h1] at h2
      exact h2
  · intro a y hy
    have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen := by simpa using hy
    have h1 := hLg a _ ((hgen a _).1 hy')
    have h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)
    simpa using h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfOrderDvd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.ValFin

theorem locInf_eq_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (w : InfinitePlace E) (x : (w.Completion)ˣ) : χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w x) = 1 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) hn
  have hz' : (e.symm z) ^ n = x := by rw [← map_pow, hz, e.symm_apply_apply]
  have h0 : e.symm z ≠ 0 := fun h0 => x.ne_zero (by rw [← hz', h0, zero_pow hn.ne'])
  have hx : x = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
  rw [hx, map_pow, map_pow]
  exact congrArg (fun χ : HChar E => χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (Units.mk0 _ h0))) h

theorem inf_eq_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Eˣ) : χ.inf k = 1 := by
  show χ.1 (infDiag k) = 1
  simp [infDiag, map_prod, locInf_eq_one χ hn h]

theorem mem_of_orderDvd : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (M : IntermediateField ℚ ℂ), (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) → valueField χ 0 ≤ M → ∀ x, ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ _ χ M hn hM x
  obtain ⟨n, hn0, hord⟩ := hn
  have hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M := fun k => by
    rw [inf_eq_one χ hn0 hord k, Units.val_one]
    exact one_mem M
  rw [← GlobalTheory.Mem.ReadEx.map_finPartI hn0 hord x]
  exact _root_.GlobalTheory.HeckeValField.mem_of_inf_eq_one E χ M hM hinf (GlobalTheory.Mem.Chr.finPartI E x) fun w => by
    rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl

end GlobalTheory.Mem.ValFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFieldHostConductor_isRayClassField : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  first | exact @GlobalTheory.ParRayMax.rayField_isRay | exact GlobalTheory.ParRayMax.rayField_isRay | (intros; apply GlobalTheory.ParRayMax.rayField_isRay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOntoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L), γ₀ ∈ GQ0 L n →
    ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom (L := L) (n := n) γ = γ₀ :=
  GlobalTheory.AlgWtF.ratHom_surjective
end

