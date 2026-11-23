module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.ConjHConjHInv
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem conjH_conjH_inv' (a : GL (Fin n) (AE D)) (b : hermA D n) : conjH a (conjH a⁻¹ b) = b := by
  apply Subtype.ext
  change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1 = b.1
  have h1 : a.1 * (a⁻¹).1 = 1 := Units.mul_inv a
  have h2 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul, h1]
    unfold adj
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
      = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

theorem inv_cpow_neg' (x : ℝ≥0) {w : ℂ} (hw : w ≠ 0) : (((x : ℝ)⁻¹ : ℝ) : ℂ) ^ (-w) = npow x w := by
  unfold npow
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Complex.zero_cpow hw, Complex.zero_cpow (neg_ne_zero.2 hw)]
  · have hpos : (0 : ℝ) ≤ (x : ℝ) := x.2
    have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos]
      exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

set_option maxHeartbeats 1000000 in
theorem nu_conj {θ : InfFam D} (hRc : RealConj) (hθ : IsInfFam θ) (a : GL (Fin n) (AE D))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1)) (c : hermA D n) :
    PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lam L₁ L₂ (conjH a c).1 = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L c.1 := by
  exact congrArg₂ (· * ·) (hRc D θ hθ n a c) (finprod_congr fun v => hnu2 v c)

end PositivityTheory.PfSWUS.SwMatch

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.IntegrableWhitOfUnfold
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

private theorem conjH_cancel (a a' : GL (Fin n) (AE D)) (h : a * a' = 1) (b : hermA D n) :
    conjH a (conjH a' b) = b := by
  have h1 : a.1 * a'.1 = 1 := by rw [← Units.val_mul, h, Units.val_one]
  have h2 : adj a'.1 * adj a.1 = 1 := by rw [← adj_mul, h1, adj_one]
  refine Subtype.ext ?_
  change a.1 * (a'.1 * b.1 * adj a'.1) * adj a.1 = b.1
  calc a.1 * (a'.1 * b.1 * adj a'.1) * adj a.1 = (a.1 * a'.1) * b.1 * (adj a'.1 * adj a.1) := by
        simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

private theorem conjH_add' (a : GL (Fin n) (AE D)) (b c : hermA D n) :
    conjH a (b + c) = conjH a b + conjH a c := by
  refine Subtype.ext ?_
  change a.1 * (b.1 + c.1) * adj a.1 = a.1 * b.1 * adj a.1 + a.1 * c.1 * adj a.1
  rw [mul_add, add_mul]

private theorem continuous_conjH' (a : GL (Fin n) (AE D)) : Continuous (conjH (D := D) a) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_comp_conjH (lam : Measure (hermA D n)) (hlam : lam.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    {f : hermA D n → ℂ} (hf : Integrable f lam) : Integrable (fun b => f (conjH a b)) lam := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : LocallyCompactSpace (Mx D n n) := i2
  have : SecondCountableTopology (Mx D n n) := i3
  have : T2Space (Mx D n n) := i4
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have : LocallyCompactSpace (hermA D n) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := n)).locallyCompactSpace
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  let e : hermA D n ≃+ hermA D n :=
    { toFun := conjH a, invFun := conjH a⁻¹
      left_inv := conjH_cancel a⁻¹ a (inv_mul_cancel a)
      right_inv := conjH_cancel a a⁻¹ (mul_inv_cancel a)
      map_add' := conjH_add' a }
  have hc : Continuous e := continuous_conjH' a
  have hc' : Continuous e.symm := continuous_conjH' a⁻¹
  have : (lam.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map lam hc hc'
  have h1 := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  have h2 : Integrable f (lam.map e) := by
    rw [h1]
    exact hf.smul_measure_nnreal
  exact h2.comp_aemeasurable hc.measurable.aemeasurable

private theorem sect_wn {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (H : G D n → ℝ≥0) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) (z : ℂ) (b : hermA D n) :
    sect ω H Φ z (w * nb b) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
  unfold sect
  congr 1
  rw [map_mul, mul_apply_eq_comp, hω.weyl w hw]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]
  beta_reduce
  rw [hω.unip (nb b) b.1 (hnb b), h0, Matrix.trace_zero, trA, map_zero, AddChar.map_zero_eq_one, mul_one, mul_comm]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_whit_of_unfold (hU : Unfold) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
    ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
    ∀ φ : Mx D V.rank n → ℂ, φ ∈ schwartzA θ V.rank n → φ ∈ fockA θ V n l s →
    ∀ (T : Mx D n n) (z : ℂ), (n : ℝ) / 2 < z.re →
      Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b *
        ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n)))) lam := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ φ hsch hfock T z hz
  have hS' : Std D n V ψ χ θ μ ω H l s ν ⟨φ, hsch⟩ :=
    ⟨hS.hψ, hS.hχ, hS.hη, hS.hθ, hS.hμ, hS.hω, hS.hH, hS.hl, hS.hs, hS.hν, hfock⟩
  have h1 := (hU D n V ψ χ θ μ ω H l s ν ⟨φ, hsch⟩ hS' hR nb lam 𝓖 hC w hw β hβ z hz 1).1
  have h2 : Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b) lam := by
    refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [mul_one]
    exact sect_wn hS.hω H hC.1 hw ⟨φ, hsch⟩ z b
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : SecondCountableTopology (Mx D n n) := i3
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) := by
    unfold halfTr
    exact hS.hψ.1.comp (continuous_const.mul (ht.comp
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg
  exact h2.mul_bdd (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun b => (hS.hψ.2.1 _).le)

end PositivityTheory.PfSWUS.SwMatch

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.TrPairEqHalfTr
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem trPair_eq_halfTr (S T : Mx D n n) :
    PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) S T = halfTr (Matrix.trace (HMul.hMul S T : Mx D n n)) := rfl

theorem gramR_tupInv (V : HSp D) (y : Mx D V.rank n) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
  ext a c
  exact hR_tup V y y a c

theorem inner_mul_right (V : HSp D) (y : Mx D V.rank n) (a : Mx D n n) :
    GlobalTheory.StdUnn.inner V (HMul.hMul y a : Mx D V.rank n) (HMul.hMul y a : Mx D V.rank n) =
      adj a * GlobalTheory.StdUnn.inner V y y * a := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jt_conj (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n))
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (a : GL (Fin n) (AE D)) (φ : Mx D V.rank n → ℂ) (c : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ c := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  have : IsTopologicalAddGroup (Mx D V.rank n) := k1
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  unfold Jt
  rw [← GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a]
  refine (integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf μ
    (fun Y => φ (HMul.hMul (tupOf Y) a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) Y)))).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change φ (HMul.hMul y a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y))) =
    φ (HMul.hMul y a.1) * ψ (halfTr (Matrix.trace (HMul.hMul c.1
      (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)) : Mx D n n)))
  rw [gramR_tupInv, trPair_eq_halfTr, inner_mul_right]
  have e : Matrix.trace (a.1 * c.1 * adj a.1 * GlobalTheory.StdUnn.inner V y y) =
      Matrix.trace (c.1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) := by
    rw [← Matrix.mul_assoc c.1, Matrix.trace_mul_comm _ a.1]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => φ (HMul.hMul y a.1) * ψ (halfTr z)) e

theorem char_conj (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (a : GL (Fin n) (AE D)) (c : hermA D n) :
    ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) c.1 : Mx D n n))) := by
  have e : Matrix.trace (β.1.map (incA D) * (a.1 * c.1 * adj a.1)) =
      Matrix.trace (adj a.1 * β.1.map (incA D) * a.1 * c.1) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (adj a.1)]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => ψ (-z))
    ((trPair_eq_halfTr (D := D) (β.1.map (incA D)) (a.1 * c.1 * adj a.1)).trans (congrArg halfTr e))

end PositivityTheory.PfSWUS.SwMatch

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Transport
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

section Transport

variable {D : D7} {n : ℕ}

def hermToME : hermA D n ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n where
  toFun := hermTo
  invFun := hermFrom
  left_inv := hermFrom_hermTo
  right_inv := hermTo_hermFrom
  measurable_toFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermTo.measurable
  measurable_invFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermFrom.measurable

theorem integral_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) :
    ∫ b, W b ∂(lam.map hermTo) = ∫ b, W (hermTo b) ∂lam :=
  (hermToME (D := D) (n := n)).measurableEmbedding.integral_map W

theorem integrable_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) (h : Integrable (fun b => W (hermTo b)) lam) :
    Integrable W (lam.map hermTo) :=
  ((hermToME (D := D) (n := n)).measurableEmbedding.integrable_map_iff).2 h

end Transport

end PositivityTheory.PfSWUS.SwMatch

end
end

