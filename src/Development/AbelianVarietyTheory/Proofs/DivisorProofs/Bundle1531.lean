module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ}
  {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem Fr.invol (hF : Fr σ J C D Z J₀) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hF.cm.2.2.2, hF.cm.2.2.2, star_star])

theorem Fr.isIsoCols (hF : Fr σ J C D Z J₀) : IsIsoCols σ J C := by
  refine ⟨Matrix.mulVec_injective_iff.1 ?_, hF.cc⟩
  intro v w h
  have := congrArg ((cT (σ : E →+* E) D * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hF.dc, Matrix.one_mulVec] using this

theorem isClosed_fixG' {k : ℕ} (X : Matrix (Fin n) (Fin k) E) : IsClosed (fixG σ J X : Set (GAd σ J)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_mul continuous_const) continuous_const

theorem unipRad_le_fixG' (X : Matrix (Fin n) (Fin j) E) : unipRad σ J X ≤ fixG σ J X := by
  rw [unipRad, Subgroup.closure_le]
  intro g hg
  obtain ⟨h, -, -⟩ := hg
  show _ * _ = _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem unipRad_onZ (hF : Fr σ J C D Z J₀) {g : GAd σ J} (hg : g ∈ unipRad σ J C) :
    ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Z = adMat F Z + adMat F C * b := by
  unfold unipRad at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨-, -, h3⟩ := hx
    choose a ha using fun k : Fin m => h3 (fun i => Z i k) (funext fun i => congrFun (congrFun hF.cz i) k)
    have e : ((matHom _ σ J x).1 - 1) * adMat F Z = adMat F C * Matrix.of fun i k => a k i :=
      Matrix.ext fun i k => congrFun (ha k) i
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at e
    exact ⟨_, e⟩
  | one => exact ⟨0, by simp⟩
  | mul x y hxm _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := unipRad_le_fixG' (σ := σ) (J := J) C hxm
    refine ⟨b + b', ?_⟩
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb', Matrix.mul_add, hb, ← Matrix.mul_assoc, hxC, Matrix.mul_add,
      add_assoc]
  | inv x hxm hx =>
    obtain ⟨b, hb⟩ := hx
    have hi : (matHom _ σ J x⁻¹).1 * (matHom _ σ J x).1 = 1 := Units.inv_mul x.1
    have hxC : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C :=
      unipRad_le_fixG' (σ := σ) (J := J) C (inv_mem (show x ∈ unipRad σ J C from hxm))
    have e : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) = (matHom _ σ J x⁻¹).1 * (adMat F Z + adMat F C * b) :=
      congrArg _ hb
    rw [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_add, ← Matrix.mul_assoc, hxC] at e
    refine ⟨-b, ?_⟩
    rw [Matrix.mul_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq e.symm

theorem unipRad_inf_fixG (hF : Fr σ J C D Z J₀) (g : GAd σ J) (hu : g ∈ unipRad σ J C)
    (hg : g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) : g = 1 := by
  obtain ⟨b, hb⟩ := unipRad_onZ hF hu
  have hC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg.1
  have hD : (matHom _ σ J g).1 * adMat F D = adMat F D := hg.2
  have hD1 : (matHom _ σ J g).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by rw [Matrix.mul_one]; exact hD
  have e := form_mul_of_mul_cols hD1
  rw [Formalism.UG.cT_one, Matrix.one_mul] at e
  have hi : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  have e2 : adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) D * J) := by
    conv_lhs => rw [← e, Matrix.mul_assoc, hi, Matrix.mul_one]
  have hb0 : b = 0 := by
    have h : adMat F (cT (σ : E →+* E) D * J) * ((matHom _ σ J g).1 * adMat F Z) =
        adMat F (cT (σ : E →+* E) D * J) * (adMat F Z + adMat F C * b) := congrArg _ hb
    have hdc : adMat F (cT (σ : E →+* E) D * J) * adMat F C = 1 := by
      rw [adMat, adMat, ← Matrix.map_mul, hF.dc, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.mul_assoc, e2, Matrix.mul_add, ← Matrix.mul_assoc, hdc, Matrix.one_mul] at h
    calc b = (adMat F (cT (σ : E →+* E) D * J) * adMat F Z + b) -
          adMat F (cT (σ : E →+* E) D * J) * adMat F Z := by abel
      _ = 0 := by rw [← h, sub_self]
  rw [hb0, Matrix.mul_zero, add_zero] at hb
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add,
      Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  have k1 := key 1
  simp only [map_one, Units.val_one, Matrix.one_mul] at k1
  rw [key g, hC, hb, hD, map_one, Units.val_one]
  exact k1.symm

theorem frame_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → IsIsoCols σ J C ∧ IsClosed (fixG σ J C : Set (GAd σ J)) ∧ IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) ∧ IsClosed (unipRad σ J C : Set (GAd σ J)) ∧ unipRad σ J C ≤ fixG σ J C ∧ fixG σ J C ≤ parFlag σ J C (fun _ => 0) ∧ (∀ g ∈ unipRad σ J C, g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) → g = 1) ∧ (∀ p ∈ parFlag σ J C (fun _ => 0), ∀ u, u ∈ unipRad σ J C ↔ p * u * p⁻¹ ∈ unipRad σ J C) ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → p ∈ parFlag σ J C (fun _ => 0) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hJ := hF.herm
  have hσ := hF.invol
  have hIC := hF.isIsoCols
  refine ⟨hIC, isClosed_fixG' C, ?_, ?_, unipRad_le_fixG' C, ?_, unipRad_inf_fixG hF, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact (isClosed_fixG' C).inter (isClosed_fixG' D)
  · rw [← unipFlag_const C 0]; exact isClosed_unipFlag hJ hσ hIC _
  · intro g hg
    have hg' : g⁻¹ ∈ fixG σ J C := inv_mem hg
    refine ⟨⟨1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩, 1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    · rw [Matrix.mul_one]; exact hg
    · rw [Matrix.mul_one]; exact hg'
  · intro p hp u
    rw [← unipFlag_const C 0]
    exact ⟨fun hu => conj_mem_unipFlag hJ hσ hIC _ hp hu, fun hu => by
      have := conj_mem_unipFlag hJ hσ hIC _ (inv_mem hp) hu
      simpa [mul_assoc] using this⟩
  · intro p β h
    have hi : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := Units.inv_mul p.1
    have hb : β.1 * (β⁻¹).1 = 1 := Units.mul_inv β
    refine ⟨⟨β.1, fun _ _ h => absurd h (lt_irrefl 0), h⟩, (β⁻¹).1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    calc (matHom _ σ J p⁻¹).1 * adMat F C = (matHom _ σ J p⁻¹).1 * (adMat F C * (β.1 * (β⁻¹).1)) := by
          rw [hb, Matrix.mul_one]
      _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F C * (β⁻¹).1 := by
          rw [← Matrix.mul_assoc (adMat F C), ← h]; simp only [Matrix.mul_assoc]
      _ = adMat F C * (β⁻¹).1 := by rw [hi, Matrix.one_mul]

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatVac

variable {F : Type} [Field F] [NumberField F]

def liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Fv F v →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v)

def psiAt (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (liftV v).toAddMonoidHom

theorem psiAt_apply (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : Fv F v) :
    psiAt ψ v x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x := rfl

def locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : W →+ (κ → Fv F v) × (κ → Fv F v) where
  toFun w := (fun k => GlobalTheory.AdelicU.evFin F v ((co.e w).1 k), fun k => GlobalTheory.AdelicU.evFin F v ((co.e w).2 k))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem evFin_liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) : GlobalTheory.AdelicU.evFin F v (liftV v a) = a :=
  GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem at_liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (liftV v a) := by
  intro u hu
  refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
  change u.2 * GlobalTheory.AdelicU.singleFin v a = 0
  apply GlobalTheory.AdelicU.af_ext
  intro w
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · subst hw
    have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, mul_zero]

end GlobalTheory.LatVac

namespace GlobalTheory.LatVac

theorem symp_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a a' : AF F)
    (x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB (a • x) (a' • y) =
      a * a' * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  have h : ξ * ∑ i, ∑ j, ∑ k, ∑ l, (a • x) i j * JA i k * JB j l * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((a' • y) k l)
      = (a * a') • (ξ * ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (y k l)) := by
    simp only [Matrix.smul_apply, map_smul, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h, map_smul, smul_eq_mul]

end GlobalTheory.LatVac

namespace GlobalTheory.LatVac

theorem latAtV_at_stable : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) ∧
    ∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      GlobalTheory.LatVac.liftV v a • γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := by
  intro F E _ _ _ _ _ n d X Y v
  constructor
  · intro γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
      intro u hu
      rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
    | zero => intro u _; exact smul_zero u
    | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
    | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]
  · intro a ha γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      rw [smul_smul]
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a • a', ?_, ?_, x, hx, y, hy, rfl⟩
      · intro u hu
        rw [smul_eq_mul, smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [smul_eq_mul, map_mul, evFin_liftV]
        exact mul_mem ha hv
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LatVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpace
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewTheta

theorem semiChar_of_nice {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    (h : GlobalTheory.InertSign.Nice D T A) : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.SemiChar T A := by
  intro x hx y hy
  have hW := GlobalTheory.InertSign.Wd_Wd D T x y (fun _ => (1 : ℂ))
  rw [h.2.1 x hx y hy, one_smul, h.1 _ (A.add_mem hx hy), h.1 y hy] at hW
  have hz := congrFun hW 0
  rw [h.1 x hx] at hz
  simp only at hz
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_smul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_U] at hz
  have hU : U D T (x + y) (fun _ => (1 : ℂ)) 0 ≠ 0 := by
    simp only [U, one_mul]
    exact Complex.exp_ne_zero _
  refine mul_right_cancel₀ hU ?_
  rw [← hz]; ring

theorem iop_mem_thSp : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (𝔪 : Ideal (𝓞 D.host.E)), SD D (skewLat D 𝔪 d) → Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ ThSp D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) := by
  intro D δ hc a d e0 he0 𝔪 hsd
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩
  have hN := (GlobalTheory.ThetaTriple.klat_triples D ⊤ δ hc a d).1 _ hK
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Iop_mem_ThSp (tor0 D ⊤ δ) (semiChar_of_nice hN) he0

end GlobalTheory.SkewTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerReductionEqLocalReduction
section
namespace ReductionComponent
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.RedComp

variable {D : D7}

theorem val_lt_one_iff (PP : Pl D.host.E) (x : Kw PP) :
    valuation (Kw PP) x < 1 ↔ Valued.v x < 1 := by
  haveI : (Valued.v : Valuation (Kw PP) _).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw PP)) Valued.v).lt_one_iff_lt_one

theorem cpt_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    cpt PP ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      algebraMap D.host.E (Kw PP) (a : D.host.E) := by
  have h : toAd D ((algebraMap (𝓞 D.host.E) D.host.E a) ⊗ₜ[D.host.F] (1 : Af D.host.F)) = _ :=
    GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) _
  show (Formalism.UG.evalV D.host.E PP) (toAd D ((algebraMap (𝓞 D.host.E) D.host.E a) ⊗ₜ[D.host.F] (1 : Af D.host.F))) = _
  rw [h]
  rfl

theorem v_algebraMap_lt_one_iff (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 ↔ a ∈ PP.asIdeal := by
  have h : Valued.v (algebraMap D.host.E (Kw PP) (a : D.host.E)) = PP.valuation D.host.E (a : D.host.E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' PP _
  rw [h]
  exact PP.valuation_lt_one_iff_mem a

def ballIdeal (PP : Pl D.host.E) : Ideal (Formalism.L2.Herm.intAf D.host.F D.host.E) where
  carrier := {s | Valued.v (cpt PP ((s : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1}
  add_mem' := by
    intro s t hs ht
    show Valued.v (cpt PP (((s + t : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hs ht
  zero_mem' := by
    show Valued.v (cpt PP (((0 : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    simp
  smul_mem' := by
    intro c s hs
    show Valued.v (cpt PP (((c * s : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    have hc : Valued.v (cpt PP ((c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) ≤ 1 := (mem_OA_iff _).1 c.2 PP
    rw [Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hs

theorem idS_le_ballIdeal (PP : Pl D.host.E) : idS D.host.F PP.asIdeal ≤ ballIdeal PP := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show Valued.v (cpt PP ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1
  rw [cpt_oToS]
  exact (v_algebraMap_lt_one_iff PP a).2 ha

theorem mem_idS_of_resS_eq_zero (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : resS D.host.F PP s = 0) : s ∈ idS D.host.F PP.asIdeal := by
  unfold resS at h
  rw [RingHom.comp_apply] at h
  have h2 : (RingEquiv.ofBijective (cmpS D.host.F PP.asIdeal) (cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm
      (Ideal.Quotient.mk (idS D.host.F PP.asIdeal) s) = 0 := h
  have h3 := (RingEquiv.symm_apply_eq _).1 h2
  rw [map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

theorem resS_eq_mk_iff (PP : Pl D.host.E) (z : Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E) :
    resS D.host.F PP z = Ideal.Quotient.mk PP.asIdeal a ↔
      Valued.v (cpt PP ((z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS D.host.F PP z)
  have h0 : resS D.host.F PP (z - oToS D.host.F D.host.E b) = 0 := by
    rw [map_sub, resS_oToS, hb, sub_self]
  have hv : Valued.v (cpt PP ((z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - algebraMap D.host.E (Kw PP) (b : D.host.E)) < 1 := by
    have h1 := idS_le_ballIdeal PP (mem_idS_of_resS_eq_zero PP _ h0)
    have h2 : Valued.v (cpt PP (((z - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1 := h1
    rwa [AddSubgroupClass.coe_sub, map_sub, cpt_oToS] at h2
  have hba : Valued.v (algebraMap D.host.E (Kw PP) ((b - a : 𝓞 D.host.E) : D.host.E)) < 1 ↔
      resS D.host.F PP z = Ideal.Quotient.mk PP.asIdeal a := by
    rw [v_algebraMap_lt_one_iff, ← hb, Ideal.Quotient.eq]
  have hsub : algebraMap D.host.E (Kw PP) ((b - a : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.E (Kw PP) (b : D.host.E) - algebraMap D.host.E (Kw PP) (a : D.host.E) := by
    rw [← map_sub]; rfl
  rw [← hba, hsub]
  constructor
  · intro h
    have := Valuation.map_add_lt _ hv h
    rwa [sub_add_sub_cancel] at this
  · intro h
    have h3 := Valuation.map_sub_lt (v := Valued.v) h hv
    rwa [sub_sub_sub_cancel_left] at h3

theorem redFn_entry_eq_mk_iff : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  intro D n β x PP hx i j a
  obtain ⟨y, rfl⟩ := hx
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  rw [redFn_frGL, inBasis_apply, e1, val_lt_one_iff]
  exact resS_eq_mk_iff PP (y.1 i j) a

end GlobalTheory.CompanionTheory.RedComp

end
end

end ReductionComponent
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  first | exact @ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff | exact ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff | (intros; apply ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff <;> assumption)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionWittFrameStabilizer
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviDecompositionFrame

theorem levi_dec_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW p β hp
  have yx' : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx h hJ hW
  have hinv : ScalesBy σ J X p⁻¹ β⁻¹ := by
    unfold ScalesBy at *
    have := congrArg (fun Z => (matHom _ σ J p⁻¹).1 * Z * (β⁻¹).1) hp
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  have hpF : p ∈ GlobalTheory.UAut.parFlag σ J X fun _ => 0 :=
    ⟨⟨_, fun _ _ hlt => absurd hlt (lt_irrefl _), hp⟩, _, fun _ _ hlt => absurd hlt (lt_irrefl _), hinv⟩
  obtain ⟨u, hu, m, hmF, hpm, hr⟩ := (GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ (r + 1) X Y (fun _ => 0)
    hW.xx hW.yy hW.xy).1 p hpF
  rw [GlobalTheory.UAut.unipFlag_const] at hu
  have hm : m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := by
    simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Finset.mem_singleton]
    rintro k rfl
    exact Subgroup.mem_inf.2 ⟨GlobalTheory.ResLineLevi.mem_frameStab_of_parFlag yx' hmF.1,
      GlobalTheory.ResLineLevi.mem_frameStab_of_parFlag hW.xy hmF.2⟩
  have hmb : ScalesBy σ J X m β := by
    have e : m = u⁻¹ * p := by rw [hpm, inv_mul_cancel_left]
    unfold ScalesBy at *
    rw [e, map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc,
      GlobalTheory.ResLineLevi.unipRad_fix (inv_mem hu)]
  refine ⟨u, hu, m, hm, hpm, hmb, hr, fun hl => Subgroup.mem_inf.2 ⟨hm, ?_⟩⟩
  simp only [Subgroup.mem_iInf, Finset.mem_singleton]
  rintro k rfl
  exact ⟨β, by simpa [MonoidHom.mem_ker] using hl, hmb⟩

end GlobalTheory.LeviDecompositionFrame
end
end

