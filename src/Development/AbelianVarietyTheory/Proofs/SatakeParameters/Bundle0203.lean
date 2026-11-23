module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertLocalEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section
open TensorProduct

namespace GlobalTheory.InertLocSurj

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem compAt_conjAL (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [conjAL, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul,
      GlobalTheory.InertUmax.compAt_tmul, Formalism.UG.sigR, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]

theorem exists_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (t : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ T : AL L, compAt L v T = t ∧ ∀ u, u ≠ v → compAt L u T = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, rfl⟩ := GlobalTheory.InertUmax.tensor_decomp b t
  refine ⟨b 0 ⊗ₜ GlobalTheory.InertUmax.sgl L v a + b 1 ⊗ₜ GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same]
  · intro u hu
    rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem exists_trivOutside_loc_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n →
    ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  have hy' : Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let Z : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((Dv.P * y * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)
  have hPP : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZ : Formalism.UG.cT Dv.σw Z * Z = 1 := by
    simp only [Z, Units.val_mul, Formalism.UG.cT_mul]
    have h1 := Dv.Panti
    calc Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) * Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) * (y : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _))
        = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) *
            (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
            (y : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          rw [h1, hy']
      _ = Formalism.UG.cT Dv.σw ((Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  have hZ' : Z * Formalism.UG.cT Dv.σw Z = 1 := mul_eq_one_comm.mp hZ
  set sg := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) with hsg
  let Xv : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
    Z.map Dv.e.symm
  have hXZ : Xv.map Dv.e = Z := by ext i j; simp [Xv]
  have hX : Xv * conjT sg Xv = 1 := by
    have hcomm : ∀ z, Dv.e.symm (Dv.σw z) = sg (Dv.e.symm z) := by
      intro z
      apply Dv.e.injective
      rw [RingEquiv.apply_symm_apply, Dv.comm, RingEquiv.apply_symm_apply]
    have h2 := congrArg (fun M => M.map Dv.e.symm) hZ'
    simp only [Matrix.map_mul] at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h2
    convert h2 using 2
    ext i j
    simp [conjT, Formalism.UG.cT, Xv, hcomm]
  choose T hTv hTu using GlobalTheory.InertLocSurj.exists_supported (L := L) v
  obtain ⟨E, hEv, hEu⟩ := GlobalTheory.InertLocSurj.exists_supported (L := L) v 1
  let A : Matrix (Fin n) (Fin n) (AL L) := fun i j => T (Xv i j) + if i = j then 1 - E else 0
  have hAv : A.map (compAt L v) = Xv := by
    ext i j
    show compAt L v (T (Xv i j) + if i = j then 1 - E else 0) = Xv i j
    by_cases h : i = j
    · rw [if_pos h, map_add (f := _), hTv, map_sub, map_one, hEv, sub_self, add_zero]
    · rw [if_neg h, map_add (f := _), hTv, map_zero, add_zero]
  have hAu : ∀ u, u ≠ v → A.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    show compAt L u (T (Xv i j) + if i = j then 1 - E else 0) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, map_add (f := _), hTu _ u hu, map_sub, map_one, hEu u hu, zero_add, sub_zero]
    · rw [if_neg h, if_neg h, map_add (f := _), hTu _ u hu, map_zero, add_zero]
  have hmap : ∀ u, (A * conjT (conjAL L) A).map (compAt L u) =
      A.map (compAt L u) * conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
        (u.adicCompletion (maximalRealSubfield L))) (A.map (compAt L u)) := by
    intro u
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [conjT, GlobalTheory.InertLocSurj.compAt_conjAL]
  have hA : A * conjT (conjAL L) A = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have h3 : (A * conjT (conjAL L) A).map (compAt L u) = (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L u) := by
      rw [hmap, Matrix.map_one _ (map_zero _) (map_one _)]
      rcases eq_or_ne u v with rfl | hu
      · rw [hAv]; exact hX
      · rw [hAu u hu, conjT_one, Matrix.one_mul]
    have h4 := congrFun (congrFun h3 i) j
    simp only [Matrix.map_apply] at h4
    rw [map_sub, h4, sub_self]
  let g : GL (Fin n) (AL L) := ⟨A, conjT (conjAL L) A, hA, mul_eq_one_comm.mp hA⟩
  have hg : g ∈ GA L n := hA
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hAu u (by simpa using hu)
  · have hbc : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) = Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      show (A.map (compAt L v)).map Dv.e = Z
      rw [hAv, hXZ]
    unfold InertDatum.loc
    show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) * Dv.P = y
    rw [hbc]
    group

end GlobalTheory.InertLocSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineWeilDeligneSpaceRestrictionEquiv
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Pst.ResLetter

open TensorProduct Module

theorem zpow_intertwine {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : M →+ N) (a : (Module.End R M)ˣ) (b : (Module.End R N)ˣ) (hab : ∀ x, T ((a : Module.End R M) x) = (b : Module.End R N) (T x)) (n : ℤ) (x : M) :
    T (((a ^ n : (Module.End R M)ˣ) : Module.End R M) x) = ((b ^ n : (Module.End R N)ˣ) : Module.End R N) (T x) := by
  have hinv : ∀ y, T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y) =
      ((b⁻¹ : (Module.End R N)ˣ) : Module.End R N) (T y) := by
    intro y
    have h1 : (b : Module.End R N) (T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y)) = T y := by
      rw [← hab, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]
    rw [← h1, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hab]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hinv]

section Gen

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : FinExt l} {V : Type} [AddCommGroup V]
  [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] {K K' : FinExt l}
  (ρ : Representation ↥LL.1 ↥(GK K) V) (hle : K.1 ≤ K'.1)

def toRes : ↥(Dpst P ρ) →+ ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) where
  toFun x := ⟨x.1, by rw [GlobalTheory.Pst.Dpst_resTo]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def ofRes : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) →+ ↥(Dpst P ρ) where
  toFun x := ⟨x.1, by rw [← GlobalTheory.Pst.Dpst_resTo P ρ hle]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toRes_ofRes (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) : toRes P ρ hle (ofRes P ρ hle x) = x := rfl
theorem ofRes_toRes (x : ↥(Dpst P ρ)) : ofRes P ρ hle (toRes P ρ hle x) = x := rfl

theorem toRes_smul (a : ↥LL.1) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle ((Dpst P ρ).module.toSMul.smul a x) =
      (Dpst P (GlobalTheory.Pst.resTo ρ hle)).module.toSMul.smul (RingHom.id _ a) (toRes P ρ hle x) := rfl
theorem ofRes_smul (a : ↥LL.1) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle ((Dpst P (GlobalTheory.Pst.resTo ρ hle)).module.toSMul.smul a x) =
      (Dpst P ρ).module.toSMul.smul (RingHom.id _ a) (ofRes P ρ hle x) := rfl

theorem toRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (mulD P ρ c x) = mulD P (GlobalTheory.Pst.resTo ρ hle) c (toRes P ρ hle x) := rfl
theorem ofRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle (mulD P (GlobalTheory.Pst.resTo ρ hle) c x) = mulD P ρ c (ofRes P ρ hle x) := rfl
theorem toRes_phiD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (phiD P ρ x) = phiD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl
theorem toRes_monD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (monD P ρ x) = monD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl

theorem toRes_actD (g : ↥(GK K)) (g' : ↥(GK K')) (hg : (g' : GQ l) = (g : GQ l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (actD P ρ g x) = actD P (GlobalTheory.Pst.resTo ρ hle) g' (toRes P ρ hle x) := by
  have e : Subgroup.inclusion (GK_le hle) g' = g := Subtype.ext hg
  subst e
  rfl

theorem toRes_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))] (n : ℤ) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (((phiU P ρ ^ n : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x) =
      ((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ n : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
        End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x) :=
  zpow_intertwine (toRes P ρ hle) (phiU P ρ) (phiU P (GlobalTheory.Pst.resTo ρ hle)) (fun y => toRes_phiD P ρ hle y) n x

end Gen

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L Ω : Type} [Field Ω] [Field K] [NumberField K]
  [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O']
  [TopologicalSpace O'] {Bw : LocBridge l K Ω (Dec (F := K) A) O} {Bw' : LocBridge l L Ω (Dec (F := L) A) O'}
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]

theorem alpha_eq (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) : alpha l σ' = alpha l σ := by
  have e := GlobalTheory.LocLanglands.normV_zpow_deg_eq σ' σ hσ
  rw [GlobalTheory.Pst.normV_eq_pow (hj'.mem_placesOver h'), GlobalTheory.Pst.normV_eq_pow (hj.mem_placesOver h)] at e
  push_cast at e
  simp only [← zpow_natCast, ← zpow_mul] at e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact zpow_right_injective₀ (zero_lt_one.trans hl) hl.ne' e

variable (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))]

theorem toRes_weilD (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (weilD Bw h P ρ σ x) = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by
  calc toRes P ρ hle (weilD Bw h P ρ σ x)
      = toRes P ρ hle (actD P ρ (weilToGK Bw h σ)
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) := rfl
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ') (toRes P ρ hle
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) :=
        toRes_actD P ρ hle _ _ hg _
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ')
          (((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
            End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x)) :=
        congrArg _ (toRes_phiU_zpow P ρ hle _ x)
    _ = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by rw [← ha]; rfl

variable (ι : Om l ≃+* ℂ)

theorem wdHom_ext {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : WDSpace P ι ρ →ₗ[ℂ] M}
    (hfg : ∀ x, f (wdMk P ι ρ x) = g (wdMk P ι ρ x)) : f = g :=
  LinearMap.ext_on_range (span_wdMk P ι ρ) hfg

def resEquiv : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle) :=
  letI := algC ι LL
  LinearEquiv.ofLinear
    (EnlargeCoeff.chg (mulD P ρ) (mulD P (GlobalTheory.Pst.resTo ρ hle)) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (toRes P ρ hle) (toRes_smul P ρ hle) (toRes_mulD P ρ hle))
    (EnlargeCoeff.chg (mulD P (GlobalTheory.Pst.resTo ρ hle)) (mulD P ρ) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (ofRes P ρ hle) (ofRes_smul P ρ hle) (ofRes_mulD P ρ hle))
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, toRes_ofRes, LinearMap.id_apply])
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, ofRes_toRes, LinearMap.id_apply])

theorem resEquiv_mk (x : ↥(Dpst P ρ)) :
    resEquiv P ρ hle ι (wdMk P ι ρ x) = wdMk P ι (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) :=
  letI := algC ι LL
  EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ (toRes_mulD P ρ hle) x

theorem resEquiv_wdN (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdN P ι ρ y) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdN P ι ρ =
      wdN P ι (GlobalTheory.Pst.resTo ρ hle) ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdN_mk, resEquiv_mk, toRes_monD]
  exact LinearMap.congr_fun this y

theorem resEquiv_wdRho (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdRho P ι Bw h hj ρ σ y) =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdRho P ι Bw h hj ρ σ =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdRho_mk, resEquiv_mk, toRes_weilD P ρ hle σ σ' hg ha]
  exact LinearMap.congr_fun this y

end Weil

theorem wdSpace_resTo_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  intro l _ P ι K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' O O' _ _ _ _ _ _ Bw Bw' hj hj' hle hW LL V _ _ _ _ _ ρ _ _ _
  exact ⟨resEquiv P ρ hle ι, fun σ σ' hσ x =>
    resEquiv_wdRho P ρ hle ι hj hj' σ σ' (hW σ σ' hσ) (alpha_eq hj hj' σ σ' hσ) x,
    fun x => resEquiv_wdN P ρ hle ι x⟩

end GlobalTheory.Pst.ResLetter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsTwistByDeRhamCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.TwistJumpsW
open Formalism.BasicNotions.Loc

theorem jumpsW_twist : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  intro D T W i ι a ρ χ hρ hχ τ c hdR hc
  let w := PI.CompDegEF.plOf τ
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := PI.CompDegEF.natCast_mem_plIdeal τ
  have hIW : InducesW D.nd i τ w := fun x => Iff.rfl
  obtain ⟨hdρ, hdχ⟩ := hdR w hIW
  have hj : GlobalTheory.Pst.Induces (D.nbr i w hw) := D.nbr_ind i w hw
  obtain ⟨L₁, hL₁, hm₁⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) a ρ hρ
    (D.nbr i w hw).LL
  obtain ⟨L, hL, hm⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) 1 χ hχ L₁
  have hBL : (D.nbr i w hw).LL.1 ≤ L.1 := hL₁.trans hL
  obtain ⟨τ', hτ'⟩ := GlobalTheory.EmbExt.main D (D.nd.l i) w _ (D.nbr i w hw) hj τ hIW L hBL
  obtain ⟨ρ₁, cρ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem ρ hρ L (fun g i j => hL (hm₁ g i j))
  obtain ⟨χ₁, cχ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem χ hχ L hm
  obtain ⟨-, H⟩ := W.loc (D.nd.l i) ι w hw _ (D.nbr i w hw) hj
    ((algebraMap ↥(D.nbr i w hw).LL.1 (Om (D.nd.l i))).comp (D.nbr i w hw).toLL) (fun _ => rfl)
  let tw₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L.1 := GlobalTheory.TwistAbove.twGL (Matrix.GeneralLinearGroup.det.comp χ₁) ρ₁
  have htw : Formalism.MainNotions.SumRepresentations.At.twGL (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁)
      (Matrix.GeneralLinearGroup.det.comp (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) χ₁)) =
      mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) tw₁ := by
    refine MonoidHom.ext fun g => Units.ext ?_
    ext p q
    simp [tw₁, mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  have ctw : Continuous (fun g => ((tw₁ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1)) := by
    have h1 : Continuous (fun g => ((χ₁ g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1).det) := cχ.matrix_det
    refine continuous_matrix fun p q => ?_
    refine (h1.mul (cρ.matrix_elem p q)).congr fun g => ?_
    simp [tw₁, GlobalTheory.TwistAbove.twGL_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [htw]
  have Hρ := H L hBL a ρ₁ cρ
  have Hχ := H L hBL 1 χ₁ cχ
  have Htw := H L hBL a tw₁ ctw
  have dρ := Hρ.2.1.1 hdρ
  have dχ := Hχ.2.1.1 hdχ
  have hcom := GlobalTheory.TwistAbove.twist_common (D.nbr i w hw) (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)
    (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) (D.locT (D.nd.l i))
  have dtw : (D.nbr i w hw).IsdRE (D.loc (D.nd.l i)) L (tw₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    hcom.1 dρ dχ
  have mχ : ∀ n, (D.nbr i w hw).multE (D.loc (D.nd.l i)) L (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' n =
      if n = c then 1 else 0 := by
    intro n
    rw [← (Hχ.2.2.2 τ τ' hτ').2 dχ n, hc, Multiset.count_singleton]
    split_ifs <;> simp
  ext n
  have e1 := (Htw.2.2.2 τ τ' hτ').2 dtw n
  have e2 := hcom.2.2.2 τ' c dχ mχ (n - c)
  have e3 := (Hρ.2.2.2 τ τ' hτ').2 dρ (n - c)
  have e4 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) (W.jumpsW (D.nd.l i) ι (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁) τ)
    (add_left_injective c) (n - c)
  simp only [sub_add_cancel] at e2 e4
  rw [e4]
  exact_mod_cast e1.trans (e2.trans e3.symm)

end GlobalTheory.TwistJumpsW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorBilinear
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertHeckeLin

open Classical in
theorem heckeFunI_bilinear : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ (c : ℂ) (f f' : GAf L n → W), heckeFunI L n U Dv (h + h') f = heckeFunI L n U Dv h f + heckeFunI L n U Dv h' f ∧ heckeFunI L n U Dv (c • h) f = c • heckeFunI L n U Dv h f ∧ heckeFunI L n U Dv h (f + f') = heckeFunI L n U Dv h f + heckeFunI L n U Dv h f' ∧ heckeFunI L n U Dv h (c • f) = c • heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU W _ _ h hh h' hh' c f f'
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    _root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (_root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram) (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h hh f' g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [smul_add]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs
    · exact smul_comm _ _ _
    · rw [smul_zero]

end GlobalTheory.InertHeckeLin
end

