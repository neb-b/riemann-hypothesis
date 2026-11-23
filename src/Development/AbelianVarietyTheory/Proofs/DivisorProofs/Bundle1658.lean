module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSplitPlaceComponentsDual
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewSplitDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x x' : Fin n → E) :
    form σ J y (x + x') = form σ J y x + form σ J y x' := by
  have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (y x : Fin n → E) :
    form σ J y (c • x) = σ c * form σ J y x := by
  have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem isIntegral_iff_mem_range (e : E) : IsIntegral ℤ e ↔ e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩

theorem coe_algebraMap_int (d : 𝓞 F) : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap F E (d : F) := rfl

theorem eq_dualGlob {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hu : Algebra.Unramified (𝓞 F) (𝓞 E))
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) :
    L = SelfDual.dualGlob σ Jᵀ ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  ext y
  rw [SelfDual.mem_dualGlob]
  simp only [hE_transpose]
  constructor
  · intro hy x hx
    refine Submodule.smul_induction_on hx (fun i hi x hx => ?_) (fun a b ha hb => ?_)
    · have key := (_root_.GlobalTheory.UnrTraceDual.traceDual_ringOfIntegers_iff_of_unramified F E hu (form σ J y x)).1 ((hdual y).1 hy x hx)
      have e1 : i • x = (i : E) • x := by ext j; rfl
      rw [e1, form_smul_right]
      have hi' : i ∈ Ideal.span (algebraMap (𝓞 F) (𝓞 E) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) := hi
      refine Submodule.span_induction
        (p := fun (i : 𝓞 E) _ => σ (i : E) * form σ J y x ∈ (algebraMap (𝓞 E) E).range) ?_ ?_ ?_ ?_ hi'
      · rintro _ ⟨d, hd, rfl⟩
        rw [coe_algebraMap_int, AlgHom.commutes, ← isIntegral_iff_mem_range]
        exact key d hd
      · simp
      · intro a b _ _ ha hb
        simp only [Subalgebra.coe_add, map_add (f := _), add_mul]
        exact add_mem ha hb
      · intro c a _ ha
        have e2 : σ ((c • a : 𝓞 E) : E) * form σ J y x = σ (c : E) * (σ (a : E) * form σ J y x) := by
          rw [← mul_assoc, ← map_mul]; rfl
        rw [e2]
        exact mul_mem ((isIntegral_iff_mem_range _).1
          ((isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) σ.injective).2 c.isIntegral_coe)) ha
    · rw [form_add_right]; exact add_mem ha hb
  · intro hy
    rw [hdual y]
    intro x hx o
    refine (_root_.GlobalTheory.UnrTraceDual.traceDual_ringOfIntegers_iff_of_unramified F E hu (form σ J y x)).2 (fun d hd => ?_) o
    have hmem : (algebraMap (𝓞 F) (𝓞 E) d) • x ∈ (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • L :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hd) hx
    have h2 := hy _ hmem
    have e1 : (algebraMap (𝓞 F) (𝓞 E) d) • x = ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) • x := by ext j; rfl
    rw [e1, form_smul_right, coe_algebraMap_int, AlgHom.commutes] at h2
    exact (isIntegral_iff_mem_range _).2 h2

theorem mem_splitLat_comp_iff_skew {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hskew : ∀ i j, σ (J j i) = -J i j) {L L₁ : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)}
    (t : E →ₐ[F] Fv F v) (z : Fv F v)
    (hloc : latLoc F L v = dualLoc σ Jᵀ L₁ v)
    (h1 : ∀ y, y ∈ latLoc F L₁ v ↔ ∃ x ∈ latLoc F L v, y = z • x) (u' : Fin n → Fv F v) :
    u' ∈ splitLat (t.comp σ) L ↔ ∀ u ∈ splitLat t L, z * (u ⬝ᵥ J.map t *ᵥ u') ∈ v.adicCompletionIntegers F := by
  have hJ : Jᵀ.map (t.comp σ) = -J.map t := by
    ext i j; simp [Matrix.transpose_apply, hskew]
  rw [← splitIncl_mem_latLoc_iff hcm, hloc]
  change (∀ x ∈ latLoc F L₁ v, hLin σ Jᵀ (Fv F v) (splitIncl hcm (t.comp σ) u') x ∈ intLoc F E v) ↔ _
  have hc : ∀ x, hLin σ Jᵀ (Fv F v) (splitIncl hcm (t.comp σ) u') x ∈ intLoc F E v ↔
      splitVec t x ⬝ᵥ J.map t *ᵥ u' ∈ v.adicCompletionIntegers F := by
    intro x
    rw [mem_intLoc_iff_split hcm t, splitProj_hLin, splitProj_hLin, comp_conj_conj hcm, splitVec_splitIncl_comp,
      splitVec_splitIncl, hJ, Matrix.mulVec_zero, dotProduct_zero, Matrix.neg_mulVec, dotProduct_neg, neg_mem_iff]
    exact and_iff_right (zero_mem _)
  simp only [hc]
  have hsv : ∀ x : Fin n → Fv F v ⊗[F] E, splitVec t (z • x) = z • splitVec t x := fun x =>
    funext fun i => map_smul (splitProj t) z (x i)
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := H (z • x) ((h1 _).2 ⟨x, hx, rfl⟩)
    rwa [hsv, smul_dotProduct, smul_eq_mul] at this
  · intro H y hy
    obtain ⟨x, hx, rfl⟩ := (h1 y).1 hy
    rw [hsv, smul_dotProduct, smul_eq_mul]
    exact H _ ⟨x, hx, rfl⟩

theorem skewSplitDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)), IsSplitBasis t W.L c →
    ∃ (z : (Fv F v)ˣ) (c₂ : GL (Fin d) (Fv F v)), (PsiUnr B.ψ v → z = 1) ∧
      (c₂⁻¹).1 = (z : Fv F v) • (c.1ᵀ * W.J.map t) ∧ IsSplitBasis (t.comp σ) W.L c₂ := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v t c hc
  haveI := hB.unram
  have hcm : IsCMExt F E σ := hB.cm
  have h𝔡0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hdet : W.J.det ≠ 0 := GlobalTheory.InertSelfDual.det_ne_zero_of_skew σ B hW
  have hdetT : W.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hdet
  have hfull : Submodule.IsFullLattice E
      ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • W.L) := by
    haveI := hW.lat
    haveI := _root_.GlobalTheory.ideal_map_smul_isLattice F E d W.L _ h𝔡0 hW.lat.toIsLattice
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔡0
    have haE : ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) ≠ 0 := by
      intro h
      apply ha0
      have h1 : algebraMap (𝓞 F) (𝓞 E) a = 0 := by exact_mod_cast h
      exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h1)
    let u : Eˣ := Units.mk0 _ haE
    apply Submodule.IsFullLattice.of_le E (M := u • W.L)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have heq : (u • y : Fin d → E) = (algebraMap (𝓞 F) (𝓞 E) a) • y := by
      rw [Units.smul_def, Units.val_mk0, ← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) a) y]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) hy
  have hglob := eq_dualGlob (σ := σ) (J := W.J) (L := W.L) hB.unram hW.dual
  have hloc : latLoc F W.L v =
      dualLoc σ W.Jᵀ ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • W.L) v :=
    (congrArg (fun L => latLoc F L v) hglob).trans
      (SelfDual.latLoc_dualGlob hdetT hfull v)
  obtain ⟨z, hz0, hz1, hzle, hzeq⟩ := _root_.GlobalTheory.ideal_localGenerator F (differentIdeal ℤ (𝓞 F)) v h𝔡0
  have key := mem_splitLat_comp_iff_skew hcm hW.skew t z hloc (GlobalTheory.T.mem_localLattice_idealMap_smul_iff_generator F E d W.L _ v z hzle hzeq)
  set M : Matrix (Fin d) (Fin d) (Fv F v) := z • (c.1ᵀ * W.J.map t) with hM
  have hMdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ hz0) (mul_ne_zero (c.isUnit.map Matrix.detMonoidHom).ne_zero ?_)
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero t).2 hdet
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin d) (Fv F v), g.1 = M :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet, rfl⟩
  refine ⟨Units.mk0 z hz0, g⁻¹, fun hp => Units.ext ?_, ?_, ?_⟩
  · simpa using hz1 (GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std v hp)
  · rw [inv_inv, hg]; rfl
  · have hMc : M * (g⁻¹).1 = 1 := by rw [← hg]; exact g.mul_inv
    have hid : ∀ (w a : Fin d → Fv F v), z * ((c.1 *ᵥ a) ⬝ᵥ W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w)) = a ⬝ᵥ w := by
      intro w a
      have e1 : z * ((c.1 *ᵥ a) ⬝ᵥ W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w)) = a ⬝ᵥ ((M * (g⁻¹).1) *ᵥ w) := by
        rw [hM, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_smul,
          smul_eq_mul]
        congr 1
        generalize W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w) = X
        simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, hMc, Matrix.one_mulVec]
    intro w
    rw [key]
    constructor
    · intro hw u hu
      have hu' := hc.mem_iff.1 hu
      have e : u = c.1 *ᵥ ((c⁻¹).1 *ᵥ u) := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, hid]
      simp only [dotProduct]
      exact sum_mem fun i _ => mul_mem (hu' i) (hw i)
    · intro H i
      have hs : ∀ j, (Pi.single i (1 : Fv F v) : Fin d → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
        by_cases e : j = i
        · subst e; simp
        · simp [e]
      have := H _ ((hc _).1 hs)
      rwa [hid, single_dotProduct, one_mul] at this

end GlobalTheory.SkewSplitDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumEigenvectorBlockLevel
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

theorem sum_mul_right_eq {G M : Type} [Group G] [AddCommMonoid M] (H K : Subgroup G)
    (hn : ∀ g ∈ H, ∀ κ ∈ K, g⁻¹ * κ * g ∈ K) (R : Finset G) (hR : ∀ r ∈ R, r ∈ H)
    (hR2 : ∀ x ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * x ∈ K) (f : G → M) (hf : ∀ x, ∀ κ ∈ K, f (x * κ) = f x)
    (g : G) (hg : g ∈ H) : ∑ r ∈ R, f (r * g) = ∑ r ∈ R, f r := by
  classical
  choose! σ hσ hσu using hR2
  have hmem : ∀ r ∈ R, r * g ∈ H := fun r hr => mul_mem (hR r hr) hg
  refine Finset.sum_nbij (fun r => σ (r * g)) (fun r hr => (hσ _ (hmem r hr)).1) ?_ ?_ ?_
  · intro r1 h1 r2 h2 e
    simp only at e
    have a1 := (hσ _ (hmem r1 h1)).2
    have a2 := (hσ _ (hmem r2 h2)).2
    rw [e] at a1
    have h3 : g⁻¹ * (r1⁻¹ * r2) * g ∈ K := by
      have := mul_mem (inv_mem a1) a2
      simpa [mul_assoc] using this
    have h4 : r1⁻¹ * r2 ∈ K := by
      have := hn g⁻¹ (inv_mem hg) _ h3
      simpa [mul_assoc] using this
    have u1 := hσu r1 (hR r1 h1) r1 ⟨h1, by simpa using K.one_mem⟩
    have u2 := hσu r1 (hR r1 h1) r2 ⟨h2, by simpa using inv_mem h4⟩
    exact u1.trans u2.symm
  · intro r' hr'
    have hx : r' * g⁻¹ ∈ H := mul_mem (hR r' hr') (inv_mem hg)
    obtain ⟨hr, hk⟩ := hσ _ hx
    refine ⟨σ (r' * g⁻¹), hr, ?_⟩
    have h5 : g⁻¹ * (g * r'⁻¹ * σ (r' * g⁻¹)) * g ∈ K := by
      refine hn g hg _ ?_
      have := inv_mem hk
      simpa [mul_assoc] using this
    exact (hσu _ (hmem _ hr) r' ⟨hr', by simpa [mul_assoc] using h5⟩).symm
  · intro r hr
    have := (hσ _ (hmem r hr)).2
    rw [← hf (σ (r * g)) _ this]
    simp

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

theorem congOne_conj {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {g κ : GA D N} (hg : g ∈ intG D N) (hκ : CongOne D 𝔪 κ) :
    CongOne D 𝔪 (g⁻¹ * κ * g) := by
  intro i j
  have e : (((g⁻¹ * κ * g : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((κ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) *
          ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
    have h1 : (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hgi := (mem_intG g).1 hg
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine mul_mem_hatId (hgi l j).1 ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem_hatId (hgi i m).2 (hκ m l)

theorem om_finsum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem stdSum_eig : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → ∀ h ∈ blockLev D 𝔪 d a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 h (stdSum W 𝔪 0 R) = c • stdSum W 𝔪 0 R := by
  intro D δ t0 hc a d e0 vac had W 𝔪 hm hcop hnu R hR1 hR2 _hfix h hh
  obtain ⟨hhi, hb⟩ := (_root_.GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff D 𝔪 d a h).1 hh
  obtain ⟨c, hc1, k, hk, hk'⟩ := _root_.GlobalTheory.FunObj.CosetMove.om_cosetV_block D δ t0 hc e0 vac had W 𝔪 hm hcop hnu h hhi hb
  refine ⟨c, hc1, ?_⟩
  have hcv := _root_.GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc 𝔪 hm 0 a d e0 vac.1
  have hcong : ∀ x, x ∈ congLev D 𝔪 a ↔ x ∈ intG D a ∧ CongOne D 𝔪 x := _root_.GlobalTheory.FunObj.StdDatum.mem_congLev_iff D 𝔪 a
  unfold stdSum
  rw [om_finsum W 1 h R _ (fun r _ => W.maps _ _ _ hcv), Finset.smul_sum]
  have e1 : ∀ r, W.Om 1 h (W.Om r 1 (cosetV D δ 𝔪 0 a d e0)) = c • W.Om (r * k) 1 (cosetV D δ 𝔪 0 a d e0) := by
    intro r
    have m1 := W.mul 1 r h 1 _ hcv
    have m2 := W.mul r 1 1 h _ hcv
    have m3 := W.mul r k 1 1 _ hcv
    simp only [one_mul, mul_one] at m1 m2 m3
    rw [← m1, m2, hk', W.smul _ _ _ _ (W.maps _ _ _ hcv), ← m3]
  simp_rw [e1]
  refine sum_mul_right_eq (intG D a) (congLev D 𝔪 a) (fun g hg κ hκ => ?_) R hR1 (fun x hx => ?_)
    (fun x => c • W.Om x 1 (cosetV D δ 𝔪 0 a d e0)) (fun x κ hκ => ?_) k hk
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    exact (hcong _).2 ⟨mul_mem (mul_mem (inv_mem hg) h1) hg, congOne_conj hg h2⟩
  · obtain ⟨r, ⟨hr, hrx⟩, hu⟩ := hR2 x hx
    exact ⟨r, ⟨hr, (hcong _).2 ⟨mul_mem (inv_mem (hR1 r hr)) hx, hrx⟩⟩,
      fun r' ⟨hr', h'⟩ => hu r' ⟨hr', ((hcong _).1 h').2⟩⟩
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    have m4 := W.mul x κ 1 1 _ hcv
    rw [mul_one] at m4
    rw [m4, _root_.GlobalTheory.FunObj.FixKey.om_cosetV_of_congOne D δ t0 hc e0 vac W 𝔪 hm hcop hnu 0 (by omega) κ h1 h2]

end GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGoodEmbeddingIndependentReadings
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifGood

theorem span_top_of_range {H X S C : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup S]
    [Module ℂ S] (ev : H →ₗ[ℂ] X) (hev : Function.Injective ev) (ad : S →ₗ[ℂ] X) (rd : C → S) (j : C → H) (c : ℂ) (hc : c ≠ 0)
    (hj : ∀ f, ev (j f) = c • ad (rd f))
    (hr : Set.range ev = ad '' (Submodule.span ℂ (Set.range rd) : Set S)) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun h _ => ?_
  obtain ⟨F, hF, hFh⟩ : ev h ∈ ad '' (Submodule.span ℂ (Set.range rd) : Set S) := hr ▸ ⟨h, rfl⟩
  have key : Submodule.span ℂ (Set.range rd) ≤ ((Submodule.span ℂ (Set.range j)).map ev).comap ad := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨c⁻¹ • j f, Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩), ?_⟩
    rw [map_smul, hj, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨y, hy, hy'⟩ := key hF
  rwa [← hev (hy'.trans hFh)]

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

noncomputable def evLin {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by
    unfold evAt
    rw [map_add (f := _)]
    rfl
  map_smul' a x := by
    unfold evAt
    rw [map_smul]
    rfl

theorem unif_good : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ i σ, GoodEmb T.Q.c (res T σ) → (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧ Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hlast hn i σ hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hT.laws.spaceW _ (inR i) _ hσ
  have hj := _root_.GlobalTheory.CuspFormValues.jEvExists h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
  have hev : ∀ f, evLin R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
    jTop_good T R κ v₀ hσ hV hj
  refine ⟨fun m b hb => ?_, ?_⟩
  · refine LinearIndependent.of_comp (evLin R i σ (v₀ i σ)) ?_
    have h := _root_.GlobalTheory.PhiIndep.phiC_indep D T κ hT.laws i _ hσ hV m b hb
    exact (funext fun k => hev (b k) : (evLin R i σ (v₀ i σ) ∘ fun k => jTop T R κ v₀ i σ (b k)) = _) ▸ h
  · have hr := _root_.GlobalTheory.HolDict.range_evAt_eq_adel_image h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
    rw [_root_.GlobalTheory.Onto.holSub0_eq_span_readings D T κ hT.laws hT.kap hlast hn i _ hσ] at hr
    exact span_top_of_range (evLin R i σ (v₀ i σ)) (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW hT.hv₀ i σ hσ) _ _ _ _
      (Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne') (fun f => (hev f).trans (phiC_eq T hV _ _)) hr

end GlobalTheory.UnifGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPNeZeroCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecNeCore

theorem thetaVector_ne_zero_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i, VStd D i → R.vP i A.μ0 ≠ 0 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i _
  exact GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hC.thP.vP i A.μ0)

end GlobalTheory.AdTh.VecNeCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueThetaIndependentStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_eigenvalue_theta_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ' : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) := by
  first | exact @GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | exact GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | (intros; apply GlobalTheory.VacThetaIndep.vacuum_character_theta_indep <;> assumption)
end

