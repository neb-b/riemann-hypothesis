module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalLatticeIdealMapSmulIffGenerator
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LatLocIdealSmul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem smul_tmul_fun {v : HeightOneSpectrum (𝓞 F)} (z b : Fv F v) (x : Fin n → E) :
    (z • fun i => b ⊗ₜ[F] x i) = fun i => (z * b) ⊗ₜ[F] x i := by
  funext i
  simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]

omit [NumberField E] in
theorem tmul_algebraMap_mul {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) (c : F) (e : E) :
    a ⊗ₜ[F] (algebraMap F E c * e) = (algebraMap F (Fv F v) c * a) ⊗ₜ[F] e := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

noncomputable def smulSet (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v) :
    AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.map (DistribSMul.toAddMonoidHom _ z)

omit [NumberField E] in
theorem mem_smulSet {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {z : Fv F v}
    {y : Fin n → Fv F v ⊗[F] E} : y ∈ smulSet L v z ↔ ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  simp only [smulSet, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, DistribSMul.toAddMonoidHom_apply]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩

theorem mem_latLoc_idealMap_smul_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (hle : ∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z)
    (hex : ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z) :
    ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E,
      y ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v ↔
        ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  intro y
  rw [← mem_smulSet]
  constructor
  · intro hy

    have key : ∀ a ∈ v.adicCompletionIntegers F, ∀ d ∈ I, ∀ x₀ ∈ L,
        (fun i => a ⊗ₜ[F] (algebraMap F E (d : F) * x₀ i)) ∈ smulSet L v z := by
      intro a ha d hd x₀ hx₀
      simp_rw [tmul_algebraMap_mul]
      by_cases hz : z = 0
      · have h0 : algebraMap F (Fv F v) (d : F) = 0 := by
          have := hle d hd
          rw [hz, map_zero] at this
          exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
        rw [h0, zero_mul]
        simp only [TensorProduct.zero_tmul]
        exact zero_mem _
      · refine mem_smulSet.2 ⟨fun i => (algebraMap F (Fv F v) (d : F) * a / z) ⊗ₜ[F] x₀ i,
          GlobalTheory.AdelicU.tmul_mem_latLoc ?_ hx₀, ?_⟩
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
          have hzv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
          rw [map_div₀, map_mul, div_le_one₀ (zero_lt_iff.2 hzv)]
          calc Valued.v (algebraMap F (Fv F v) (d : F)) * Valued.v a
              ≤ Valued.v z * 1 := mul_le_mul' (hle d hd) ha
            _ = Valued.v z := mul_one _
        · rw [smul_tmul_fun, mul_div_cancel₀ _ hz]
    refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ smulSet L v z) ?_ (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    intro a ha x' hx'
    refine Submodule.smul_induction_on hx' ?_ ?_
    · intro r hr x₀ hx₀
      induction hr using Submodule.span_induction generalizing x₀ with
      | mem r hr =>
        obtain ⟨d, hd, rfl⟩ := hr
        exact key a ha d hd x₀ hx₀
      | zero =>
        simp only [zero_smul, Pi.zero_apply, TensorProduct.tmul_zero]
        exact zero_mem _
      | add r s _ _ hr hs =>
        have e : (fun i => a ⊗ₜ[F] ((r + s) • x₀) i) =
            (fun i => a ⊗ₜ[F] (r • x₀) i) + fun i => a ⊗ₜ[F] (s • x₀) i := by
          funext i; simp [add_smul, TensorProduct.tmul_add]
        rw [e]; exact add_mem (hr x₀ hx₀) (hs x₀ hx₀)
      | smul o r _ hr =>
        have e : (o • r) • x₀ = r • (o • x₀) := by rw [smul_eq_mul, mul_smul, smul_comm]
        rw [e]; exact hr _ (L.smul_mem o hx₀)
    · intro x y hx hy
      have e : (fun i => a ⊗ₜ[F] (x + y) i) = (fun i => a ⊗ₜ[F] x i) + fun i => a ⊗ₜ[F] y i := by
        funext i; simp [TensorProduct.tmul_add]
      rw [e]; exact add_mem hx hy
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_smulSet.1 hy
    obtain ⟨d₀, hd₀, hv⟩ := hex
    refine GlobalTheory.AdelicU.latLoc_induction
      (p := fun x => z • x ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v) ?_
      (by rw [smul_zero]; exact zero_mem _) (fun _ _ h h' => by rw [smul_add]; exact add_mem h h')
      (fun _ h => by rw [smul_neg]; exact neg_mem h) hx
    intro a ha x₀ hx₀
    by_cases hz : z = 0
    · rw [hz, zero_smul]; exact zero_mem _
    have hzv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
    have hd0 : algebraMap F (Fv F v) (d₀ : F) ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact hzv hv.symm
    have hmem : (algebraMap (𝓞 F) (𝓞 E) d₀ • x₀) ∈ I.map (algebraMap (𝓞 F) (𝓞 E)) • L :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hd₀) hx₀
    have hc : z * a / algebraMap F (Fv F v) (d₀ : F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
      rw [map_div₀, map_mul, hv, mul_div_cancel_left₀ _ hzv]
      exact ha
    have := GlobalTheory.AdelicU.tmul_mem_latLoc (L := I.map (algebraMap (𝓞 F) (𝓞 E)) • L) hc hmem
    convert this using 1
    rw [smul_tmul_fun]
    funext i
    change _ = (z * a / algebraMap F (Fv F v) (d₀ : F)) ⊗ₜ[F] (algebraMap F E (d₀ : F) * x₀ i)
    rw [tmul_algebraMap_mul, mul_div_cancel₀ _ hd0]

end GlobalTheory.LatLocIdealSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicSchwartzFunctionLeftGLEquivariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory

theorem fFun_mul_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k),
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν Ψ g h
  let f : Matrix (Fin a) (Fin a) k →* Matrix C C k :=
    { toFun := fun M => (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
      map_one' := by rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
      map_mul' := fun M N => by
        rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp }
  let E : GL C k := Units.map f g
  have hE : ∀ M : Matrix (Fin a) (Fin a) k, f M = (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm := fun _ => rfl
  have hX : g.val * X0 k σ = X0 k σ * E.val := by
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [X0, E, hE, Matrix.mul_apply]
  have hY : Y0 k σ * (invT E).val = Y0 k σ := by
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply, invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [Y0, E, hE, ← map_inv, Matrix.one_apply, eq_comm]
  have hdet : gdet E = gdet g := by
    ext
    simp [E, hE, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : g.val * (X0 k σ * (invT h).val) = X0 k σ * (invT (invT E * h)).val := by
    rw [map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have h2 : Y0 k σ * (invT E * h).val = Y0 k σ * h.val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hY]
  have h3 : gdet (invT E * h) = (gdet g)⁻¹ * gdet h := by rw [gdet_mul, gdet_invT, hdet]
  rw [h1, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, h2, h3, map_mul, map_inv, apow_mul, apow_inv, apow_neg,
    Units.val_mul, Units.val_inv_eq_inv_val]
  have hν : ((ν (gdet g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have ha : apow (gdet g) ((Fintype.card C : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
section
namespace GlobalTheory.OffIdem


open NumberField in
theorem exists_common {O R ι : Type} [CommRing O] [IsDomain O] [CommRing R] (f : O →+* R) (I : ι → Ideal O) (ε : R)
    (hε : ε * ε = ε) (P : Finset ι) (h : ∀ i ∈ P, ∃ x ∈ I i, x ≠ 0 ∧ ∃ s, ε = s * f x) :
    ∃ x, x ≠ 0 ∧ (∀ i ∈ P, x ∈ I i) ∧ ∃ s, ε = s * f x := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp, ε, by simp⟩
  | insert a P _ ih =>
    obtain ⟨x, hx0, hx, s, hs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨y, hy, hy0, t, ht⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨x * y, mul_ne_zero hx0 hy0, fun i hi => ?_, s * t, ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Ideal.mul_mem_left _ _ hy
      · exact Ideal.mul_mem_right _ _ (hx i hi)
    · rw [map_mul, mul_mul_mul_comm, ← hs, ← ht, hε]

end GlobalTheory.OffIdem

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffIdem

theorem idemSum_mul_idemAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) : ∃ a : AE D, Formalism.L2.NTheta.IsIdemAt a PP ∧ a * e = a := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 hc
  refine ⟨es PP, hes PP hPP, ?_⟩
  rw [Finset.mul_sum, Finset.sum_eq_single PP (fun j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes PP hPP) (hes j hj) (hcross PP hPP j hj) (hcross j hj PP hPP) hji)
    (fun h => absurd hPP h), h1 PP hPP]

theorem exists_eq_mul_of_mul_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (Formalism.L2.DIV.Pl E)) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε)
    (h : ∀ PP ∈ P, ∃ a : Formalism.L2.Herm.intAf F E, Formalism.L2.DIV.resS F PP a = 1 ∧ a * ε = 0) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ (∀ PP ∈ P, x ∈ PP.asIdeal) ∧ ∃ s, ε = s * Formalism.L2.DIV.oToS F E x :=
  exists_common (Formalism.L2.DIV.oToS F E) (fun PP : Formalism.L2.DIV.Pl E => PP.asIdeal) _ hε P fun PP hPP => by
    refine GlobalTheory.IdemRes.exists_eq_mul_of_resS_ne_one PP _ hε fun hne => ?_
    have := PP.isPrime
    obtain ⟨a, ha1, h0⟩ := h PP hPP
    have h3 := congrArg (Formalism.L2.DIV.resS F PP) h0
    rw [RingHom.map_mul, ha1, hne, RingHom.map_zero, one_mul] at h3
    exact one_ne_zero h3

theorem one_sub_mul_self {R : Type} [CommRing R] {e : R} (h : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination h

theorem mul_one_sub {R : Type} [CommRing R] {a e : R} (h : a * e = a) : a * (1 - e) = 0 := by
  linear_combination -h

theorem mul_ringHom_mul_ringHom_inv_cancel {K R : Type} [Field K] [CommRing R] (f : K →+* R) (s : R) {y : K} (hy : y ≠ 0) :
    s * f y * f y⁻¹ = s := by
  rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, mul_one]

theorem exists_den {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) ≠ 0 ∧ (∀ PP ∈ P, y ∈ PP.asIdeal) ∧
      finPart D ((1 - e) * incA D ((y : D.host.E)⁻¹)) ∈ intAE D := by
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : (1 - e) * (1 - e) = 1 - e := one_sub_mul_self (R := AE D) h1
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h2]))
  obtain ⟨y, hy0, hy, s, hs⟩ := exists_eq_mul_of_mul_eq_zero P ⟨toEAf D (1 - e), hint⟩
    (Subtype.ext (by change toEAf D (1 - e) * toEAf D (1 - e) = toEAf D (1 - e); rw [← RingHom.map_mul, h2]))
    fun PP hPP => by
      obtain ⟨a, ha, hae⟩ := idemSum_mul_idemAt he hPP
      obtain ⟨hai, ha1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D a PP ha
      refine ⟨_, ha1, Subtype.ext ?_⟩
      change toEAf D a * toEAf D (1 - e) = 0
      rw [← RingHom.map_mul, mul_one_sub (R := AE D) hae, RingHom.map_zero]
  have hs' : toEAf D (1 - e) = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (y : D.host.E) := congrArg Subtype.val hs
  have hy0' : (y : D.host.E) ≠ 0 := fun h => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h4 : toEAf D (incA D ((y : D.host.E)⁻¹)) = eToEAf D ((y : D.host.E)⁻¹) := rfl
  refine ⟨y, hy0', hy, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_⟩
  rw [RingHom.map_mul, h4, hs', mul_ringHom_mul_ringHom_inv_cancel (eToEAf D) _ hy0']
  exact s.2

theorem one_sub_smul_mem_latO : ∀ (D : D7) (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ x : WO V W, (∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) → incA D (s : D.host.E) • x ∈ (latO V W LV LW fun _ => True)) → (1 - e) • x ∈ (latO V W LV LW fun _ => True) := by
  intro D V W LV LW e P he x hx
  obtain ⟨y, hy0, hy, hw⟩ := exists_den he
  have h5 := GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hw _ (hx y hy)
  rwa [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hy0, RingHom.map_one, mul_one] at h5

end GlobalTheory.OffIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

end Claims

theorem BigC.and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF ((le_max_left _ _).trans hCF)
  obtain ⟨C0', h'⟩ := h' CF ((le_max_right _ _).trans hCF)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  obtain ⟨x0', h'⟩ := h' ε C ((le_max_right _ _).trans hC)
  refine ⟨max x0 x0', fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ⟨?_, ?_⟩⟩
  · exact h D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3
  · exact h' D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3

end GlobalTheory.SumSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.SizesOfRows

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  intro D large₂ h
  obtain ⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have hbig2 : bigN D ≤ 2 * D.R.N D.R.m := by
    simp only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1 := by omega
    have h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ h1
    have e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6) := by ring
    omega
  have hmR : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
  have hdR : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast hd
  have hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ) := by exact_mod_cast hbig2
  have hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      have : D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)
    linarith
  have hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
  have hrd1 : 1 ≤ D.host.rdE := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by
    show Real.log (Real.exp large₂.sc.L) = large₂.sc.L
    exact Real.log_exp _
  refine ⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩
  · rw [hlogb]; linarith
  · have : (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
    linarith

end GlobalTheory.SizesOfRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem nuH_not_unrAt_above {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) ∈ G.pl.S0) : ¬ (nuH G t i j).UnrAt P := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [← div_eq_mul_inv, nuH, div_div_cancel]
  intro hn
  rcases G.pl.mem_S0_of_sum_eq.1 hP with hv | hv
  · have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      rw [hv] at h
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt P := by
      by_contra hc
      rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h hv
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
    apply (G.ch.lev0 _ hm.1 hm.2 _ hv).2
    rw [e]
    exact (hmu.mul hxi).mul hn.inv
  · apply (G.ch.lev1 _ hm.1 hm.2 P hv).2
    rw [e]
    exact (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame P) (hL.xi_tame t P)).mul (hn.levelLe 1).inv

theorem heckeL_eq_of_ram {K : Type} [Field K] [NumberField K] {χ : HChar K} {S : Set (HeightOneSpectrum (𝓞 K))}
    (hr : ∀ w ∈ S, ¬ χ.UnrAt w) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    GlobalTheory.LFun.heckeL S χ s = Λ s := by
  have e : ({w | w ∉ S} : Set (HeightOneSpectrum (𝓞 K))).mulIndicator (GlobalTheory.CMVal.eulerFactor χ s) =
      GlobalTheory.CMVal.eulerFactor χ s :=
    Set.mulIndicator_eq_self.2 fun w hw => by
      by_contra h
      exact hw (if_neg (hr w (not_not.1 h)))
  have h := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ S}) (f := GlobalTheory.CMVal.eulerFactor χ s)).2
    (by rw [e]; exact hΛ.2 s hs)
  unfold GlobalTheory.LFun.heckeL GlobalTheory.LFun.eulerProd
  simp only [GlobalTheory.LFun.locL_heckeFam]
  exact h.tprod_eq

theorem chs_nu (G : GridData L sc) (i j : Fin D.R.m) (t : T) : (chs G i j t).ν = G.nu t i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem charL_chs_eq : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G i j t s Λ hs hΛ => ?_⟩⟩
  rw [chs_nu, GlobalTheory.LFun.charL_eq_of_chrEq (chrEq_nu G t i j hL)]
  refine heckeL_eq_of_ram (fun w hw => nuH_not_unrAt_above hL G t i j w hw) hΛ ?_
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < s)

end GlobalTheory.SqStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOneStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_unitary_lift_tendsto_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  first | exact @GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | exact GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | (intros; apply GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one <;> assumption)
end

