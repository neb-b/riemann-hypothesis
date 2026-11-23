module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7}

theorem natCast_smul_mem_of_halfAO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) : (c : E) • x ∈ M := by
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by simp)
  · exact key 2 (by rw [neg_neg, zpow_one]; field_simp)
  · exact key 1 (by simp)

theorem conjP_conjP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
  apply HeightOneSpectrum.ext
  ext r
  rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]

theorem conjP_not_mem {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e SS)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hPP : PP ∈ SS) : Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun h' =>
  GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hPP _ h' fun r hr =>
    ⟨Formalism.L2.Col.cO D.host.E r, by rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]; exact hr, rfl⟩

end GlobalTheory.AdForm.CocycleSS

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem smul_tmul_fin {a : AE D} (ha : infPart D a = 0) (r : D.host.E) :
    a * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] r) = a * incA D r :=
  GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul]; rfl)

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, GlobalTheory.SplitScalar.symplO_smul]

theorem lhs_eq {e : AE D} (hinf : infPart D (cA D e) = 0) (hec : e * cA D e = 0)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (X.map fun r => e * incA D r) (GlobalTheory.VacUnique.finRat S T X - X.map fun r => e * incA D r) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hXt : (X.map fun r => e * incA D r : WO S T) = e • (X.map (incA D) : WO S T) := by ext i j; rfl
  have hF : cA D e • GlobalTheory.VacUnique.finRat S T X = cA D e • (X.map (incA D) : WO S T) := by
    ext i j; exact smul_tmul_fin hinf _
  rw [hXt, symplOH_smul, smul_sub, hF, smul_smul, mul_comm, hec, zero_smul, sub_zero]

theorem smul_finRat_natCast {e : AE D} (hinf : infPart D e = 0) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X) = (e * incA D (c : D.host.E)) • (X.map (incA D) : WO S T) := by
  ext i j
  show e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((c : D.host.E) * X i j)) = (e * incA D (c : D.host.E)) * incA D (X i j)
  rw [smul_tmul_fin hinf, map_mul, mul_assoc]

theorem smul_map_inv {e : AE D} (hcc : cA D e * cA D e = cA D e) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T) =
      (cA D e * incA D ((c : D.host.E)⁻¹)) • (X.map (incA D) : WO S T) := by
  ext i j
  show cA D e * (cA D e * incA D ((c : D.host.E)⁻¹ * X i j)) = (cA D e * incA D ((c : D.host.E)⁻¹)) * incA D (X i j)
  rw [map_mul, ← mul_assoc, hcc, mul_assoc]

theorem cA_incA_natCast (c : ℕ) : cA D (incA D (c : D.host.E)) = incA D (c : D.host.E) := by
  show incA D (star (c : D.host.E)) = _
  rw [star_natCast]

theorem rhs_eq {e : AE D} (hinf : infPart D e = 0) (hcc : cA D e * cA D e = cA D e) {c : ℕ} (hc : 0 < c)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X))
        (cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T)) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hs : cA D e * incA D (c : D.host.E) * (cA D e * incA D ((c : D.host.E)⁻¹)) = cA D e := by
    rw [mul_mul_mul_comm, hcc, ← map_mul, mul_inv_cancel₀ hcE, map_one, mul_one]
  rw [smul_finRat_natCast hinf, smul_map_inv hcc, symplOH_smul, smul_smul, RingHom.map_mul, cA_incA_natCast, hs]

theorem finRat_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {c : ℕ} (hc : 0 < c)
    {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have e1 : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) =
      finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) := by ext i j; rfl
  rw [e1]
  exact finTens_mem_latO (one_mem_intAf _)
    (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc hN (natCast_smul_mem_of_halfAO hc hx))

theorem conjHalf_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS)
    {c : ℕ} {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hno : ∀ PP ∈ SS, Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun PP hPP => conjP_not_mem hE hPP
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (es PP) * incA D r : WO S T) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
    rfl
  rw [e1]
  refine sum_mem fun PP hPP => GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN (hes PP hPP) ?_ ?_
  · refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  · have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ PP)))⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ PP).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx _
    have hexp : expS SS (Formalism.L2.Col.conjPrime₂ PP) = -1 := by
      unfold expS
      rw [if_neg (hno PP hPP), conjP_conjP, if_pos hPP]
    rw [hexp, neg_neg, zpow_one] at h
    exact h

theorem cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _hodd x' hx
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hinfc : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have H := GlobalTheory.HalfCocycle.char_symplOH_idem_conj D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' _ (finRat_mem hP.cc hN hc hx) _
    (conjHalf_mem hP.cc hN hE hx)
  have e1 : ∀ r : D.host.E, (LinearMap.toMatrix' (r • x') : Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
      r • LinearMap.toMatrix' x' := fun r => LinearEquiv.map_smul LinearMap.toMatrix' r x'
  rw [e1, e1, rhs_eq hinf hcc hc] at H
  rw [lhs_eq hinfc hE.2]
  exact H

end GlobalTheory.AdForm.CocycleSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.FlatFix

variable {D : D7}

theorem two_ne_zero_at (w : Pl D) : (2 : Fv D.host.F w) ≠ 0 := by
  rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]
  exact (map_ne_zero_iff _ (algebraMap D.host.F (Fv D.host.F w)).injective).2 two_ne_zero

theorem two_inv_int (w : Pl D) (hw : (2 : 𝓞 D.host.F) ∉ w.asIdeal) :
    (2⁻¹ : Fv D.host.F w) ∈ w.adicCompletionIntegers D.host.F := by
  have h3 : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (2 : 𝓞 D.host.F)
    rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hw] at this
    rw [← this]
    congr 1
  have h2 : ((2 : D.host.F) : Fv D.host.F w) = 2 := by
    rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]; rfl
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← h2,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h3, inv_one]

theorem finite_two (P : Pl D → Prop) : {v : Pl D | P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv.2


open Classical in
def halfOff (P : Pl D → Prop) : Af D.host.F :=
  RestrictedProduct.mk (fun w => if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0)
    (Filter.Eventually.of_forall fun w => by
      split_ifs with h
      · exact two_inv_int w h.2
      · exact zero_mem _)

open Classical in
theorem evalV_halfOff (P : Pl D → Prop) (w : Pl D) :
    evalV D.host.F w (halfOff P) = if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0 := rfl

theorem halfOff_int (P : Pl D → Prop) : halfOff P ∈ intAf D.host.F := by
  classical
  intro w
  rw [evalV_halfOff]
  split_ifs with h
  · exact two_inv_int w h.2
  · exact zero_mem _

theorem pair_add (a b : Af D.host.F) : pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
  Prod.ext (add_zero (0 : Ainf D.host.F)).symm rfl

theorem sum_pair {ι : Type} (s : Finset ι) (α : ι → Af D.host.F) :
    ∑ i ∈ s, pairA D.host.F 0 (α i) = pairA D.host.F 0 (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Prod.ext rfl rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, pair_add]

theorem indicatorIdempotent_eq_add_sum (P : Pl D → Prop) (Qs : Finset (Pl D)) (hQ : ∀ v, v ∈ Qs ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Pl D → AF D.host.F) (hε : ∀ v ∈ Qs, IsPlaceIdem D v (ε v)) :
    GlobalTheory.SelfDualAt.cP P = pairA D.host.F 0 (halfOff P + halfOff P) + ∑ v ∈ Qs, ε v := by
  classical
  choose! α hα h1 h0 using hε
  rw [Finset.sum_congr rfl hα, sum_pair, ← pair_add]
  unfold GlobalTheory.SelfDualAt.cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  change evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) = evalV D.host.F w (halfOff P + halfOff P + ∑ i ∈ Qs, α i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_add (f := _), map_sum, GlobalTheory.SelfDualAt.evalV_indP, evalV_halfOff]
  by_cases hw : w ∈ Qs
  · obtain ⟨hP, h2⟩ := (hQ w).1 hw
    rw [Finset.sum_eq_single_of_mem w hw (fun v hv hvw => h0 v hv w (Ne.symm hvw)), h1 w hw, if_pos hP,
      if_neg (fun h => h.2 h2), zero_add, zero_add]
  · rw [Finset.sum_eq_zero (fun v hv => h0 v hv w (fun h => hw (h ▸ hv))), add_zero]
    by_cases hP : P w
    · have h2 : (2 : 𝓞 D.host.F) ∉ w.asIdeal := fun h2 => hw ((hQ w).2 ⟨hP, h2⟩)
      rw [if_pos hP, if_pos ⟨hP, h2⟩, ← two_mul, mul_inv_cancel₀ (two_ne_zero_at w)]
    · rw [if_neg hP, if_neg (fun h => hP h.1), add_zero]

theorem int_alg_pair {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) ∈ intAE D := by
  have e : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) = pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) =
      β ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
    show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]; rfl
  rw [e, e2]
  exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩

theorem fix_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} {z : WO S T}
    (hiso : ∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) {a b : AE D}
    (ha : heisO ψ S T (a • z) f = f) (hb : heisO ψ S T (b • z) f = f) : heisO ψ S T ((a + b) • z) f = f := by
  have key := GlobalTheory.LatVac.heisO_heisO ψ (a • z) (b • z) f
  rw [hb, ha, hiso a b, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
  exact key.symm

end GlobalTheory.FinPl.FlatFix


open GlobalTheory.FinPl.FlatFix in
theorem GlobalTheory.FinPl.FlatFix.fix_of_isotropic : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), IsSelfDualC S LS → IsSelfDualC T LT → (∀ v, P v → Tame D v) → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f → ∀ z ∈ latO S T (LS : Set _) (LT : Set _) P, (∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) → heisO ψ S T z f = f := by
  intro D ψ S T LS LT P _ _ hT f hf z hz hiso
  classical
  have hfix_split : ∀ e, IsSplitIdem D e → heisO ψ S T (e • z) f = f := fun e he =>
    hf.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P e (GlobalTheory.SplitHomLattice.idem_int he) z hz)
      (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
  have hQ := finite_two (D := D) P
  have hmemQ : ∀ v, v ∈ hQ.toFinset ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal := fun v => hQ.mem_toFinset
  have hch : ∀ v, v ∈ hQ.toFinset → ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
    intro v hv
    obtain ⟨hPv, h2⟩ := (hmemQ v).1 hv
    rcases (hT v hPv).2 with h | h
    · exact absurd h2 h
    · exact h
  choose! e ε he hε hsum using hch
  have hdec := indicatorIdempotent_eq_add_sum P hQ.toFinset hmemQ ε hε
  have hzc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP P) • z = z := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul P _ (LatMem.latO_mxAt hz i j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hzc, hdec, map_add (f := _), map_sum]
  refine fix_add hiso ?_ ?_
  · have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P _ (int_alg_pair (halfOff_int P)) z hz
    have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P + halfOff P)) • z =
        2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P)) • z) := by
      rw [pair_add, map_add (f := _), add_smul, two_nsmul]
    rw [e2]
    exact hf.1 _ hm
  · refine Finset.sum_induction _ (fun c => heisO ψ S T (c • z) f = f) (fun a b ha hb => fix_add hiso ha hb) ?_ ?_
    · rw [zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
    · intro v hv
      rw [← hsum v hv]
      exact fix_add hiso (hfix_split _ (he v hv)) (hfix_split _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (he v hv)))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemEMulIdemE
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacUnion

variable {D : D7}


open Classical in
def idemF (v : Pl D) : Af D.host.F :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    show (if w = v then (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.F w) else 0) ∈ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem evalV_idemF (v w : Pl D) : evalV D.host.F w (idemF v) = if w = v then 1 else 0 := rfl

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [mul_zero]

def idemE (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (pairA _ 0 (idemF v))

theorem idemE_mul_gen (v : Pl D) (α : Af D.host.F) (x : D.host.E) :
    idemE v * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x := by
  rw [idemE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, pairA_mul]

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idemE_smul_gen (v : Pl D) (α : Af D.host.F) (x : Fin T.rank → Fin S.rank → D.host.E) :
    idemE v • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
      Matrix.of fun i j => pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x i j := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.of_apply, idemE_mul_gen]

theorem idemE_smul_mem (v : Pl D) {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    idemE v • u ∈ latO S T LS LT (· = v) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    have hα' : ∀ w, evalV D.host.F w α ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F w := hα
    have hmem : idemF v * α ∈ intAf D.host.F := by
      simp only [intAf, Set.mem_setOf_eq]
      intro w
      rw [map_mul]
      refine mul_mem ?_ (hα' w)
      rw [evalV_idemF]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine ⟨idemF v * α, hmem, fun w hw => ?_, a, ha, s, hs, t, ht, idemE_smul_gen v α _⟩
    rw [map_mul, evalV_idemF, if_neg hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.VacUnion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSeeSaw

variable {D : D7}

theorem isThetaFunO_const_mul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => c * f w) := {
  quasi γ w := by
    show c * f (ratW T S γ + w) = _ * (c * f w)
    rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk u hu h0) w
    simp only [heisO] at e ⊢
    rw [← e]; ring
  cont := continuous_const.mul hf.cont
  smooth n L hL h0 w := contDiff_const.mul (hf.smooth n L hL h0 w) }

theorem isThetaFunO_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO L S → ℂ} (hf : IsThetaFunO ψ L S f) : IsThetaFunO ψ S L'' (fun w => f (kap τ S w)) := by
  obtain ⟨hadd, hcont, hrat, -, hsym, hpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) (by simpa using hτ)
    (kap τ S) (fun _ => rfl)
  have hsH : ∀ x y, symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := fun x y => by
    simp only [symplOH, hsym]; push_cast; ring
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun n M hM h0 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) (by rw [ratW_eq]; exact rat_mem _)
    show f (kap τ S (ratW L'' S γ + w)) = _
    have e : ratW S L γ' = kap τ S (ratW L'' S γ) := hγ'
    rw [hadd, ← e, hf.quasi, e, hsH]
  · obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap K, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk (kap τ S u) hu ((hpart u).1 h0)) (kap τ S w)
    simp only [heisO] at e ⊢
    rw [hadd, ← hsH]
    exact e
  · have := hf.smooth n (K.comp M) (hcont.comp hM) (fun t => (hpart (M t)).2 (h0 t)) (kap τ S w)
    simp only [hadd]
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, K] using this

end GlobalTheory.LastSeeSaw
end

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LastSeeSaw

end GlobalTheory.LastSeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorValuesThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocModTheta

theorem flat_model_theta : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ Ψ, IsThetaFunO ψ B.V₀ J.W₀ (L₀ Ψ) := by
  intro D _hFL hFlat _hOm k _ _ _ _ _ _ p ν hν ψ ψk hchar ρ B J st s _hs n n' _ _ _ _ c FA F₀ FV G₀ FW _hCore hBes _hJac Tm hTm L₀ hL Ψ
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  have hcont : Continuous ψk := ((_root_.GlobalTheory.LocChar.weil_char_split D k p ψ hstd).2.1 ψk hchar).1
  have hc : c = 2 * ρ := by have := hBes.1; omega
  obtain ⟨Φ₀, hΦ₀, hfl⟩ := ((_root_.GlobalTheory.LocFlat.flat_SB_onto k ψk ν hcont hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  rw [← hL ⟨Φ₀, hΦ₀⟩ Ψ hfl.symm]
  exact ((hFlat ψ (fun _ => True)).1 ρ B J st).Heisenberg₂.theta (Tm ⟨Φ₀, hΦ₀⟩) (hTm.theta _)

end GlobalTheory.LocModTheta
end

