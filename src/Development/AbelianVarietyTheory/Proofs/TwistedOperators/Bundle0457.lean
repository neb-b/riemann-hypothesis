module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompMulFin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.KerTrans

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_fin (p : Pair T) (k : FinPt G p.small) :
    (G.toPair p k.1 1).1 ∈ GfC (G.pS p) ∧ (G.toPair p k.1 1).2 ∈ GfC (G.pT p) := by
  cases p <;> simp [GridData.toPair]

theorem ker_mul_fin (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h : GA D (G.V p.big)) : W.ker p F (g * k) h = W.ker p (W.om p (G.toPair p k 1) F) g h := by
  have e : G.toPair p (g * k) h = G.toPair p g h * G.toPair p k 1 := by
    rw [← GlobalTheory.RowClaim.toPair_mul, mul_one]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G)
    {p : Pair T}, p.InRange D.R.m → ∀ (f : WO (G.pS p) (G.pT p) → ℂ), IsThetaFunO W.ψ (G.pS p) (G.pT p) f →
    ∀ (g k : FinPt G p.small) (h : FinPt G p.big),
      fockComp W B p f (g * k) h = fockComp W B p (W.om p (G.toPair p k.1 1) f) g h := by
  intro D T L sc G W B p hp f hf g k h
  have hk := toPair_fin p k
  unfold fockComp
  congr 1
  funext m
  unfold jetTab kerFin
  rw [Subgroup.coe_mul, ker_mul_fin]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) (W.om_is p hp) W.θ W.θ_is _ hk.1 _ hk.2 _ _ _ _ f _ hf

end GlobalTheory.KerTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockTranslate

theorem compAt_fin {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} (g : GA D V) (hg : g ∈ Formalism.L2.Theta.GfC V) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h6 : (Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D) = 1 :=
    congrArg Units.val (show Formalism.L2.Theta.infHom V g = 1 from hg)
  unfold Formalism.IndefR.Datum.compAt
  rw [show (Formalism.L2.Theta.mt V g).map (fun a => θ τ (Formalism.L2.Theta.infPart D a)) =
    ((Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D)).map (θ τ) from (Matrix.map_map).symm, h6]
  exact Matrix.map_one _ (θ τ).map_zero (θ τ).map_one

theorem fockComp_translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G) (t : T) (j : ℕ),
    j + 1 ≤ D.R.m → ∀ (f : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
    IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) f →
    ∀ (a k₁ : FinPt G (.top j)) (b k₂ : FinPt G (.top (j + 1))),
      fockComp W B (.top t j) f (a * k₁) (b * k₂) =
        fockComp W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) a b := by
  intro D T L sc G W B t j hj f hf a k₁ b k₂
  have hom := W.om_is (.top t j) hj
  have hcomm : ∀ P, W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1)))))
      (fockIn W B (.top t j) f P) = fockIn W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) P := by
    intro P
    unfold fockIn
    refine Formalism.IndefR.Eqv.KerDiag.comm_pureTensorO W.ψ_std W.θ W.θ_is _ _ _ _ _ (fun τ z g hg => ?_) hf P
    rw [GlobalTheory.OrientedHeis.om_dRho hom W.θ_is _ _ τ z hg, compAt_fin W.θ τ _ k₂.2, compAt_fin W.θ τ _ (inv_mem k₁.2),
      Matrix.one_mul, Matrix.mul_one]
  unfold fockComp
  congr 1
  funext M
  unfold jetTab kerFin GridData.Weil.ker
  simp only [GridData.toPair, thetaKO, Subgroup.coe_mul]
  rw [show ((a : GA D (G.V (.top j))) * k₁, (b : GA D (G.V (.top (j + 1)))) * k₂) =
    ((a : GA D (G.V (.top j))), (b : GA D (G.V (.top (j + 1))))) * ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) from rfl,
    map_mul, Module.End.mul_apply, hcomm]

end GlobalTheory.FockTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReduction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIdem

section General

variable {R : Type} [CommRing R] {n : ℕ}

theorem cut_mem (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f * A i j ∈ O) (h' : ∀ i j, f' * A i j ∈ O) (i j : Fin n) :
    ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j ∈ O := by
  have e : ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j =
      f * A i j + f' * A i j + (1 - (f + f')) * (1 : Matrix (Fin n) (Fin n) R) i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]
  rw [e]
  refine O.add_mem (O.add_mem (h i j) (h' i j)) (O.mul_mem (O.sub_mem O.one_mem (O.add_mem hf hf')) ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem exists_cut (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (hff : f * f = f) (hff' : f' * f' = f')
    (h0 : f * f' = 0) (A B : Matrix (Fin n) (Fin n) R) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, f * A i j ∈ O) (hA' : ∀ i j, f' * A i j ∈ O)
    (hB : ∀ i j, f * B i j ∈ O) (hB' : ∀ i j, f' * B i j ∈ O) :
    ∃ Y : GL (Fin n) O, Y.1.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ {k : Type} [CommRing k] (ρ : O →+* k), ρ ⟨f, hf⟩ = 1 →
        ∀ i j, ρ (Y.1 i j) = ρ ⟨f * A i j, hA i j⟩ := by
  have hφ : (f + f') * (f + f') = f + f' := by
    have h0' : f' * f = 0 := by rw [mul_comm, h0]
    simp only [add_mul, mul_add, hff, hff', h0, h0', add_zero, zero_add]
  let Ym : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' A hA hA' i j⟩
  let Ym' : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' B hB hB' i j⟩
  have hm : Ym.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have hm' : Ym'.map O.subtype = (f + f') • B + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h i) j
  have e1 : Ym * Ym' = 1 := inj (by
    show (Ym * Ym').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ A B hAB, Matrix.map_one _ (map_zero _) (map_one _)])
  have e2 : Ym' * Ym = 1 := inj (by
    show (Ym' * Ym).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ B A hBA, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨Ym, Ym', e1, e2⟩, hm, ?_⟩
  intro k _ ρ hρ i j
  have hz : ρ ⟨f', hf'⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f', hf'⟩ = 0 := Subtype.ext h0
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hz' : ρ ⟨f' * A i j, hA' i j⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f' * A i j, hA' i j⟩ = 0 :=
      Subtype.ext (show f * (f' * A i j) = 0 by rw [← mul_assoc, h0, zero_mul])
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hd : ρ ((1 : Matrix (Fin n) (Fin n) O) i j) * 0 = 0 := mul_zero _
  have split : Ym i j = ⟨f * A i j, hA i j⟩ + ⟨f' * A i j, hA' i j⟩ +
      (1 - (⟨f, hf⟩ + ⟨f', hf'⟩)) * (1 : Matrix (Fin n) (Fin n) O) i j := by
    apply Subtype.ext
    show ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j = _
    have : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : R) = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Subring.coe_add, Subring.coe_mul,
      this]
    rfl
  show ρ (Ym i j) = _
  rw [split, map_add (f := _), map_add (f := _), map_mul, map_sub, map_add (f := _), hρ, hz, hz', map_one]
  simp

end General

theorem frGL_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (frGL β Y).1 = β.1 * Y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl


set_option maxHeartbeats 400000 in
theorem cut_mem_St_red : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  intro D n β γ y Z e he h1 h2 h3 h4 hy
  obtain ⟨hf, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hfc : toEAf D e * toEAf D (cA D e) = 0 := by rw [← map_mul, he.2, map_zero]
  have hf' : toEAf D (cA D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hcc]))
  obtain ⟨Y, hY, hred⟩ := exists_cut (Formalism.L2.Herm.intAf D.host.F D.host.E) hf hf'
    (by rw [← map_mul, hee]) (by rw [← map_mul, hcc]) hfc γ.1 (γ⁻¹ : GL (Fin n) (EAf D)).1
    γ.mul_inv γ.inv_mul h1 h3 h2 h4
  have hyY : y = frGL β Y := by
    have hs : toEAf D (e + cA D e) = toEAf D e + toEAf D (cA D e) := (toEAf D).map_add _ _
    refine Units.ext (hy.trans ?_)
    rw [frGL_val, hY, hs]
  subst hyY
  refine ⟨⟨Y, rfl⟩, fun PP hP => ?_⟩
  rw [redFn_frGL]
  ext i j
  have := hred (resS D.host.F PP) (hres PP hP) i j
  refine this.trans ?_
  unfold redM
  rw [dite_eq_left (h1 i j)]
  rfl

end GlobalTheory.FrameIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKForms

open Matrix Filter Topology GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.CuspGK
open Formalism.IndefR.Mult

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem exists_sigOK (V : HSp D) : ∃ s, (GlobalTheory.SmoothAutCheck.reSig V s).SigOK := by
  have h : ∀ ρ : D.host.E →+* ℂ, ∃ pq : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map ρ) pq.1 pq.2 := fun ρ => by
    have hd : IsUnit (V.gram.map ρ).det := by
      have : (V.gram.map ρ).det = ρ V.gram.det := (RingHom.map_det _ _).symm
      rw [this, isUnit_iff_ne_zero]
      exact (map_ne_zero _).2 (GlobalTheory.SmoothAutCheck.gram_det_ne V)
    have hh : Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map ρ) := by
      ext i j
      have hcm := D.host.isCMField_hostE
      have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
      simp only [Formalism.UG.cT, transpose_apply, map_apply, HSpace.gram]
      rw [← h1]
      exact (NumberField.IsCMField.complexEmbedding_complexConj _ ρ _).symm
    obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ _ hh hd
    exact ⟨(p, q), h⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem goodPar_of_isTypeAt (hV : V.SigOK) {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ S φ) :
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S := by
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, -⟩ := h
  obtain ⟨e1, e2⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr hP hJ (hV (tauE D τ))
  exact ⟨lam, ε, hE, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD, e1, e2⟩

theorem isTypeAt_rTr_same (hθ : IsInfFam θ) {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ S φ)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsTypeAt θ V τ S (rTr V (atTau θ V τ k) φ) := by
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, h⟩ := h
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  have hσ := hD.2.2.1
  have hG : IsUnit (gramAt D V τ) := (isUnit_iff_isUnit_det _).2 (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  have hk' : kᴴ * gramAt D V τ * k = gramAt D V τ := hk
  have hku : IsUnit k := by
    have := congrArg Matrix.det hk'
    rw [det_mul] at this
    rw [isUnit_iff_isUnit_det]
    exact isUnit_of_mul_isUnit_right (this ▸ GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  have a1 : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hku)
  have a2 : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hku)
  have b2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP)
  have hki : k⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = gramAt D V τ
    calc (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * gramAt D V τ * k) * k⁻¹ := by rw [hk']
      _ = (k * k⁻¹)ᴴ * gramAt D V τ * (k * k⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a1]; simp
  have hm := GlobalTheory.TypeAtCompare.conj_mem hP hJ hk
  have t0 : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => σ (P * g * P⁻¹))
      fun g => φ (x * atTau θ V τ k * atTau θ V τ g) := hasTypeAll_iff.2 (h (x * atTau θ V τ k))
  have t1 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) (fun g => σ (P * g * P⁻¹)) _ _ k hG hku hk'
    (opEquiv hσ hm) (fun g hg v => by
      have m1 := GlobalTheory.TypeAtCompare.conj_mem hP hJ hg
      have m2 := GlobalTheory.TypeAtCompare.conj_mem hP hJ (mul_mem_UH (mul_mem_UH hk hg) hki)
      show σ (P * k * P⁻¹) (σ (P * g * P⁻¹) v) = σ (P * (k * g * k⁻¹) * P⁻¹) (σ (P * k * P⁻¹) v)
      rw [← sigma_mul hσ hm m1, ← sigma_mul hσ m2 hm]
      congr 2
      calc P * k * P⁻¹ * (P * g * P⁻¹) = P * k * (P⁻¹ * P) * g * (k⁻¹ * k) * P⁻¹ := by
            rw [a2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = P * k * g * k⁻¹ * (P⁻¹ * P) * k * P⁻¹ := by rw [b2]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]) _ t0
  obtain ⟨v, h1, ℓ, h2, h3, h4⟩ := hasTypeAll_iff.1 t1
  refine ⟨v, h1, ℓ, h2, h3, fun g hg => ?_⟩
  have e : x * atTau θ V τ k * atTau θ V τ (k⁻¹ * g * k) = x * atTau θ V τ g * atTau θ V τ k := by
    rw [mul_assoc x, mul_assoc x, ← atTau_mul hθ V τ hk (mul_mem_UH (mul_mem_UH hki hg) hk), ← atTau_mul hθ V τ hg hk,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul]
  have := h4 g hg
  simp only [e] at this
  exact this

theorem isTypeAt_rTr (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ' S φ)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsTypeAt θ V τ' S (rTr V (atTau θ V τ k) φ) := by
  by_cases c : τ = τ'
  · subst c
    exact isTypeAt_rTr_same hθ h hk
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, h⟩ := h
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨v, h1, ℓ, h2, h3, h4⟩ := h (x * atTau θ V τ k)
  refine ⟨v, h1, ℓ, h2, h3, fun g hg => ?_⟩
  have := h4 g hg
  rw [mul_assoc x, GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' c k hk g hg, ← mul_assoc x] at this
  exact this

theorem exists_quotient_near (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) {C : Set (GA D V)} (hC : IsCompact C) {δ : ℝ}
    (hδ : 0 < δ) : ∃ t : ℝ, ∀ x ∈ C,
      ‖Rder θ V τ X φ x - (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x‖ < δ := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc := (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ).cont
  have hu := GlobalTheory.Mem.Lift.continuous_oneP hθ hX
  have h0 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
  have hd := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ.smooth hX)
  set ψ := Rder θ V τ X φ
  have ev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ C, ‖ψ (x * oneP θ V τ X t) - ψ x‖ < δ / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have cF : Continuous fun z : ℝ × GA D V => ‖ψ (z.2 * oneP θ V τ X z.1) - ψ z.2‖ :=
      ((hc.comp (continuous_snd.mul (hu.comp continuous_fst))).sub (hc.comp continuous_snd)).norm
    refine cF.continuousAt.eventually_lt continuousAt_const ?_
    simp only [h0, mul_one, sub_self, norm_zero]
    linarith
  obtain ⟨η, hη, hb⟩ := Metric.eventually_nhds_iff.1 ev
  refine ⟨η / 2, fun x hx => ?_⟩
  have hp : 0 < η / 2 := by linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => φ (x * oneP θ V τ X s) - (s : ℂ) * ψ x)
    (f' := fun s => ψ (x * oneP θ V τ X s) - ψ x) (a := 0) (b := η / 2) (C := δ / 2)
    (fun s _ => by
      have := (hd x s).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (ψ x))
      simpa using this.hasDerivWithinAt)
    (fun s hs => (hb (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; linarith [hs.2]) x hx).le)
    (η / 2) ⟨hp.le, le_rfl⟩
  set t := η / 2
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : ψ x - (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x =
      -(t : ℂ)⁻¹ * ((φ (x * oneP θ V τ X t) - (t : ℂ) * ψ x) - (φ (x * oneP θ V τ X 0) - ((0 : ℝ) : ℂ) * ψ x)) := by
    simp only [h0, mul_one, Pi.smul_apply, Pi.add_apply, rTr, smul_eq_mul, Complex.ofReal_zero]
    field_simp
    ring
  rw [e, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hp.le, inv_mul_lt_iff₀ hp]
  refine key.trans_lt ?_
  nlinarith

section Sig

variable (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ ψ : GA D V → ℂ}
include hPr hθ

end Sig

variable {S : D.what₂.Tau → SPar}

end GlobalTheory.CuspGKForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.FormTopAut

variable {D : D7}

theorem aut_cast {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : IsAutFun D.sp.X' φ) :
    IsAutFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact hφ

theorem formTop_cont_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t y, Continuous (formTop ch t y) ∧
    ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g := by
  refine ⟨0, ?_⟩
  intro ε CF _
  refine ⟨0, ?_⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ t y
  have hm := hS.core.models
  obtain ⟨h1, -, -⟩ := GlobalTheory.EndCusp.formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have k := aut_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (ch.cv.formX t y) h1.toIsAutFun
  exact ⟨k.cont, k.left⟩

end GlobalTheory.FormTopAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.ConjSplitIdem

theorem isIdemAt_cA_of_ne : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → w.under (𝓞 D.host.F) = v → w'.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → Formalism.L2.NTheta.IsIdemAt (cA D ε) w' := by
  intro D v w w' hne hw hw' ε hε
  rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := w') (by rw [hw, hw']) with h | h
  · exact absurd h.symm hne
  · subst h
    exact GlobalTheory.MovedIdem.isIdemAt_conj hε (fun x => Iff.rfl)

end GlobalTheory.ConjSplitIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDual
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitLatSelfDual

theorem latAtV_selfDual_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _ _ z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.SplitLatSelfDual
end

