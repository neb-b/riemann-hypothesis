module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem hasConductor_one_continuous_ne_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle),
    HasConductor ψ 1 → Continuous ψ ∧ ψ ≠ 1 := by
  intro k _ _ _ _ ψ h
  exact ⟨h.continuous, h.ne_one⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinRestComm

variable {D : D7}

theorem finPart_finRat_sub {S T : HSp D} (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : finPart D (GlobalTheory.VacUnique.finRat S T M i j - incA D (M i j)) = 0 := by
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 ((GlobalTheory.LatVac.finPart_pair 1 (M i j)).trans (GlobalTheory.LatVac.finPart_incA (M i j)).symm)

theorem infPart_of_idemSum {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS) :
    infPart D e = 0 := by
  obtain ⟨⟨es, hes, he⟩, -⟩ := hI
  subst he
  induction SS using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

theorem smul_rest_eq_zero {S T : HSp D} {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • (GlobalTheory.VacUnique.finRat S T M - M.map (fun r => e * incA D r)) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.zero_apply, smul_eq_mul, mul_sub,
    ← mul_assoc, hee, ← mul_sub]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]
  · rw [RingHom.map_mul, finPart_finRat_sub, mul_zero, RingHom.map_zero]

theorem char_sympl_rest_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y'))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx' y' hy'
  have hZ := _root_.GlobalTheory.HalfAComp.zmem D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx'
  have hY := _root_.GlobalTheory.HalfBComp.ybmem D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP y' hy'
  have heZ := smul_rest_eq_zero (S := S) (T := T) (GlobalTheory.PlaceDatum.idemSum_mul_self hI) (infPart_of_idemSum hI)
    (LinearMap.toMatrix' x')
  have hsplit : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') =
      (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') -
        (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r)) +
      cA D e • (LinearMap.toMatrix' y').map (incA D) := by
    have : (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r) =
        cA D e • (LinearMap.toMatrix' y').map (incA D) := Matrix.ext fun i j => rfl
    rw [this, sub_add_cancel]
  rw [hsplit, ← GlobalTheory.LatVac.symplHom_apply, map_add (f := _), AddChar.map_add_eq_mul, GlobalTheory.LatVac.symplHom_apply,
    GlobalTheory.LatVac.symplHom_apply, ← GlobalTheory.SplitScalar.symplO_smul, heZ, GlobalTheory.SplitScalar.symplO_zero_left,
    AddChar.map_zero_eq_one, mul_one]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN' hZ hY

end GlobalTheory.FinRestComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ChiStd

variable {D : D7}

theorem prV_toEAf_idem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (hv : v' ≠ v) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v' (Formalism.IndefR.Datum.toEAf D (algebraMap (AF D.host.F) (AE D) ε * a)) = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  have h0' : (Formalism.UG.evalV D.host.F v') ((sndA D.host.F) (pairA D.host.F 0 α)) = 0 := h0 v' hv
  induction a using TensorProduct.induction_on with
  | zero => rw [mul_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
    rw [h0', zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => rw [mul_add, RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

end GlobalTheory.AdForm.ChiStd

namespace GlobalTheory.AdForm.ChiStd

variable {D : D7}

theorem finM_gl_map_prV {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {m : Type} [Fintype m] [DecidableEq m] (β : Frame p S m)
    (g : GL m k) {v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v' ≠ p.v) :
    (finM S hn (β.gl g)).map (Formalism.UG.prV (E := D.host.E) v') = 1 := by
  obtain ⟨ε, hε, he⟩ := p.above
  have hs := β.gl_supp g
  subst hn
  ext r s
  have key : Formalism.UG.prV (E := D.host.E) v' (Formalism.IndefR.Datum.toEAf D ((mt S (β.gl g) - 1) r s)) = 0 := by
    rw [← hs r s, he]; exact prV_toEAf_idem_mul hε hv _
  have e1 : mt S (β.gl g) r s = (mt S (β.gl g) - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s := by
    rw [Matrix.sub_apply, sub_add_cancel]
  simp only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [e1, RingHom.map_add (f := _), RingHom.map_add (f := _), key, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.AdForm.ChiStd

theorem GlobalTheory.AdForm.ChiStd.not_both_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a c : ℕ}
    (ha : a.Prime) (hc : c.Prime) (hne : a ≠ c) (h1 : ((a : ℕ) : 𝓞 F) ∈ v.asIdeal) (h2 : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime a c := (Nat.coprime_primes ha hc).2 hne
  have hg : ((Nat.gcd a c : ℕ) : ℤ) = a * Nat.gcdA a c + c * Nat.gcdB a c := Nat.gcd_eq_gcd_ab a c
  rw [hcop, Nat.cast_one] at hg
  have h3 : ((1 : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hg]; push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h1) (v.asIdeal.mul_mem_right _ h2)
  rw [Int.cast_one] at h3
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.AdForm.chi_std_trivial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → ∀ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1 := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg h
  obtain ⟨κ, hκ⟩ := ((hA.U j hj b _).1 h).2
  rw [hA.chi j hj b ⟨_, h⟩ κ hκ]
  apply hA.lev_chi_eq_one j hj b κ
  intro v' hv'
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ (p i).v.asIdeal := by
    obtain ⟨⟨e, he⟩, -⟩ := hS
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    have hmem : X.piT u ∈ (e i).1.asIdeal := (Formalism.L2.Col.mem_divs hne _).1 (e i).2
    obtain ⟨ε, hε, hε'⟩ := (p i).above
    have hund := GlobalTheory.IdemUnder.under_eq_of_isIdemAt (I.rec7 l Z) (p i).e (e i).1 (p i).v ε (he i) hε hε'
    have hTE : ((B.T u : ℕ) : 𝓞 B.host.E) ∈ (e i).1.asIdeal := by
      have := hPr.piT_norm u
      rw [← this]
      exact Ideal.mul_mem_right _ _ hmem
    rw [← hund]
    show _ ∈ Ideal.comap _ _
    refine Ideal.mem_comap.2 ?_
    have h2 : (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E)) ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) =
        ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.E) := map_natCast _ _
    first | (erw [h2]; exact hTE) | exact h2 ▸ hTE | simpa using hTE
  have hne : v' ≠ (p i).v := by
    rintro rfl
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    rcases hv' with hbad | hq
    · rcases hbad with h0 | h1
      · exact GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 0) (hPr.T_ne_g u 0) hT h0
      · exact GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 1) (hPr.T_ne_g u 1) hT h1
    · exact (GlobalTheory.Mem.Col2.TC.underQ_notMem I hOk l u a _ hq).1 hT
  apply Units.ext
  show (κ.1.1).map (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v') = 1
  rw [hκ]
  exact GlobalTheory.AdForm.ChiStd.finM_gl_map_prV (p i) _ _ (β j i) g hne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelColumnSubOneMemBaseLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.AdForm.level_col_sub_one_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  set_option maxHeartbeats 10000000 in
    next =>
      intro B X I hI hP l Z u a Ch A hA j hj b κ hκ v hv s
      obtain ⟨-, κ', hκ'⟩ := (hA.U j hj b κ).1 hκ
      have hgram : gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
      haveI : NeZero ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) := ⟨by
        have := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_add_three_le_k
        simp only [Ranks.N]; omega⟩
      obtain ⟨At, -, hpi, -⟩ := GlobalTheory.Mem.AtLevel.exists_atTTied I hI hP l Z u
      let sg : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E := RingOfIntegers.mapRingHom (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)
      have hsc : ∀ x, (sg x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.conj (x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
      have hpq : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) * (sg At.piU : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hsc]; exact At.piU_norm
      have hTp := ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T_prime
      have hp0 : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
      have hL : (A.K j hj b).lev.Lb = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) (((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)⁻¹) := by
        refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ At.piU hp0 _ ?_
        rw [hpi]; exact (hA.reads j hj).lb b
      have hx := (((A.K j hj b).lev.U_eq κ'.1).1 κ'.2).2 v
      have hT := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.fixed x).1 hx)
          (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.cmUnram.2.2 hgram (A.K j hj b).lev At.piU (sg At.piU) rfl hpq hTp hL v hv (_root_.GlobalTheory.LevelUnif.dvd_of_val_lt_one (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u At v hv) _).1 hx
      have hsp : Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb) = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) ((sg At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hL, hgram]; exact GlobalTheory.uLocDual_eq (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (fun x => star_star x) _ At.piU (sg At.piU) hp0 rfl
      have hy : (fun r => Formalism.UG.inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((Pi.single s 1 : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) r)) ∈ Formalism.UG.latS (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (intV (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E v) (Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb)) := by
        simp only [hsp]
        refine Submodule.subset_span ⟨Pi.single s 1, ?_, rfl⟩
        rw [SetLike.mem_coe, Formalism.L2.Col.rll_mem_dLat]
        refine ⟨fun i _ => ?_, ?_⟩
        · by_cases h : i = s
          · subst h; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _
        · by_cases h : Formalism.L2.Col.lastIdx ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) = s
          · rw [h, Pi.single_eq_same, mul_one]; exact ⟨sg At.piU, rfl⟩
          · rw [Pi.single_eq_of_ne h, mul_zero]; exact zero_mem _
      have key := hT.2 _ hy
      convert key using 1
      funext r
      have hm : ((Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) κ'.1 : GL _ _) : Matrix _ _ _) = (κ'.1.1).map (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) := rfl
      rw [Pi.sub_apply, hm, hκ']
      congr 1
      · simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply]
      · simp [Pi.single_apply, Matrix.one_apply]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIdempotentCutIsClosedScaledKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem continuous_mt_cutTop (V : HSp D) : Continuous (fun g : GA D V => Formalism.L2.Theta.mt V g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) :
    Continuous (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  refine continuous_matrix fun i j => ?_
  have h : (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g) i j) = fun g : GA D V =>
      ε • Formalism.L2.Theta.mt V g i j +
        ((1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) i j := by
    funext g
    rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def ε]
  rw [h]
  exact (((continuous_mt_cutTop V).matrix_elem i j).const_smul ε).add continuous_const

theorem continuous_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : Continuous (cutG V ε hε) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨continuous_mt_cutG V ε hε, ?_⟩)
  have h := (continuous_mt_cutG V ε hε).comp (continuous_inv (G := GA D V))
  refine h.congr fun g => ?_
  rw [Function.comp_apply, map_inv]
  rfl

theorem isClosed_smul_sub_one_eq_zero (V : HSp D) (c : AF D.host.F) :
    IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e.isEmbedding.t2Space
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  have h : {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} =
      ⋂ i, ⋂ j, {g : GA D V | c • Formalism.L2.Theta.mt V g i j =
        c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero, Algebra.smul_def, Algebra.smul_def]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (((continuous_mt_cutTop V).matrix_elem i j).const_smul c) continuous_const

theorem continuous_cutG_and_isClosed : ∀ (D : D7) (V : HSp D), (∀ (ε : AF D.host.F) (hε : ε * ε = ε), Continuous (GlobalTheory.FinPl.SetCut.cutG V ε hε)) ∧ ∀ c : AF D.host.F, IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} :=
  fun _ V => ⟨continuous_cutG V, isClosed_smul_sub_one_eq_zero V⟩

end GlobalTheory.FinPl.SetCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem mt_mul (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

def locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) : GA D S →* GL Y k where
  toFun g := ⟨F.γ * (mt S g).map q.pr * F.β, F.γ * (mt S g⁻¹).map q.pr * F.β, by
      rw [show F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S g⁻¹).map q.pr * F.β) =
        F.γ * ((mt S g).map q.pr * (F.β * F.γ) * (mt S g⁻¹).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ], by
      rw [show F.γ * (mt S g⁻¹).map q.pr * F.β * (F.γ * (mt S g).map q.pr * F.β) =
        F.γ * ((mt S g⁻¹).map q.pr * (F.β * F.γ) * (mt S g).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ]⟩
  map_one' := by
    ext1; simp only [mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, F.γβ]; rfl
  map_mul' g h := by
    ext1
    change F.γ * (mt S (g * h)).map q.pr * F.β = F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S h).map q.pr * F.β)
    rw [mt_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem locHom_val (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) :
    (locHom q S F g).val = F.γ * (mt S g).map q.pr * F.β := rfl

theorem eq_locHom_iff (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) (x : GL Y k) :
    (mt S g).map q.pr = F.β * x.val * F.γ ↔ x = locHom q S F g := by
  constructor
  · intro h
    ext1
    rw [locHom_val, h]
    simp only [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
  · rintro rfl
    rw [locHom_val]
    simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

theorem continuous_locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    Continuous (locHom q S F) := by
  rw [Units.continuous_iff]
  have hm : Continuous fun g : GA D S => (mt S g).map q.pr :=
    (GlobalTheory.MixModel.continuous_mt S).matrix_map q.cont_pr
  refine ⟨(continuous_const.matrix_mul hm).matrix_mul continuous_const, ?_⟩
  have hi : Continuous fun g : GA D S => (mt S g⁻¹).map q.pr :=
    ((GlobalTheory.MixModel.continuous_mt S).comp continuous_inv).matrix_map q.cont_pr
  exact (continuous_const.matrix_mul hi).matrix_mul continuous_const

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) : μ.real H' * (H'.relIndex H : ℝ) = μ.real H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

end GlobalTheory.LevIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfStdFin

theorem exists_reps_half_stdHom : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  classical
  intro D S T Q E₂ _ k hk
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T (Formalism.L2.Col.stdLat D.host.E S.rank)
    (Formalism.L2.Col.stdLat D.host.E T.rank) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg (fun _ => True) k hk
  rw [coe_colStdLat, coe_colStdLat] at h
  let G : WO S T → Prop := fun r => ∃ u ∈ stdHom S T, IsHalf E₂ u ∧ ∃ w ∈ stdHom S T, u = r + k • w
  let pick : WO S T → WO S T := fun r => if hG : G r then hG.choose else 0
  refine ⟨hR.toFinset.image pick, fun u hu hh => ?_⟩
  obtain ⟨r, hr, w, hw, huw⟩ := h u hu
  have hG : G r := ⟨u, hu, hh, w, hw, huw⟩
  obtain ⟨_, hh₀, w₀, hw₀, hu₀w⟩ := hG.choose_spec
  have hp : pick r = hG.choose := dif_pos hG
  have hdiff : u = hG.choose + k • (w - w₀) := by
    rw [hu₀w, smul_sub, huw]; abel
  exact ⟨pick r, Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hr), w - w₀, sub_mem hw hw₀,
    GlobalTheory.HalfLatFin.isHalf_of_nsmul E₂ hk hh hh₀ hdiff, by rw [hp]; exact hdiff⟩

end GlobalTheory.HalfStdFin

end
end

