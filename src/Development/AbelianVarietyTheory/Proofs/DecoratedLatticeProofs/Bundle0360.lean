module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG

namespace GlobalTheory.Mem.Col2.AdT.SplitChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_conjP_eq_one (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) (r s : Fin n) :
    adAt F (conjPrime₂ P) (u.1 r s) = (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
  subst J
  have hunit : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) * u.1 = 1 := by
    have h := hu
    change cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) u.1 * (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * u.1 = _ at h
    simpa only [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] using h
  have h1 : (u : Matrix (Fin n) (Fin n) (AfE F E)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    have hcT : 1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) = cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) u.1 := by
      ext i j
      by_cases h : i = j <;> simp [cT, Matrix.one_apply, map_sub, h, eq_comm]
    rw [hcT]
    exact (mul_eq_one_comm).1 hunit
  have hC : (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P)) = 0 := by
    refine Matrix.ext fun i j => ?_
    show adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)) = 0
    have e2 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) j i := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hX : adAt F P (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i) = 0 := by
      rw [Matrix.sub_apply, map_sub, hP, e2, sub_self]
    have e := GlobalTheory.Mem.Col2.valued_sigR hc (conjPrime₂ P) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)
    rw [GlobalTheory.CharValCompare.conjP_conjP, hX, Valuation.map_zero] at e
    exact (Valuation.zero_iff _).1 e
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add (f := _), map_one] at h2
  change _ * (1 + (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P))) = 1 at h2
  rw [hC, add_zero, mul_one] at h2
  exact congrFun (congrFun h2 r) s

theorem bc_prV_eq_one_of_split (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hover : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) :
    bc (prV (E := E) v) u = 1 := by
  refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt F E n v u fun w hw r s => ?_
  rcases hover w hw with rfl | rfl
  · rw [hP, Matrix.one_apply]
  · rw [adAt_conjP_eq_one hc hJ hu P hP r s, Matrix.one_apply]

end Gen

section Root

theorem exists_root_GL {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n : ℕ) (hn : 0 < n)
    (c : P.adicCompletion E) (hc : Valued.v c < 1) (A : GL (Fin m) (P.adicCompletion E))
    (hA : ∀ r s, Valued.v (A.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤
      Valued.v ((n : P.adicCompletion E) ^ 2 * c)) :
    ∃ M : GL (Fin m) (P.adicCompletion E), M ^ n = A ∧
      ∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ Valued.v ((n : P.adicCompletion E) * c) := by
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n c A.1 hn hc
    (fun r s => by rw [Matrix.sub_apply]; exact hA r s)
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ A.isUnit)
  obtain ⟨M, rfl⟩ := hu
  exact ⟨M, Units.ext (by rw [Units.val_pow_eq_pow_val, hM2]), fun r s => by rw [← Matrix.sub_apply]; exact hM1 r s⟩

end Root

section Fin

theorem chi_eq_one_of_pow {G : Type} [Group G] {U : Subgroup G} (χ : U →* ℂˣ) (x z : U) (n : ℕ) (hz : χ z ^ n = 1)
    (hy : χ ((z ^ n)⁻¹ * x) = 1) : χ x = 1 := by
  rw [map_mul, map_inv, map_pow, hz, inv_one, one_mul] at hy
  exact hy

theorem map_inv_pow_mul_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {x z : G} (n : ℕ) (hz : f z = 1) (hx : f x = 1) :
    f ((z ^ n)⁻¹ * x) = 1 := by
  rw [map_mul, map_inv, map_pow, hz, hx, one_pow, inv_one, one_mul]

end Fin


set_option maxHeartbeats 8000000 in
theorem chi_eq_one_of_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  intro B X I hI hPin l Z a T i hi bad S n hn hchi P v hv
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  have hu : P.1.under (𝓞 B.host.F) = v := by
    rw [hs] at hv
    exact HeightOneSpectrum.ext (Eq.symm hv)
  haveI : CharZero (P.1.adicCompletion B.fields.E) := algebraRat.charZero _
  set c : P.1.adicCompletion B.fields.E := ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) ^ (N₀ + 1) with hcdef
  have hc : Valued.v c = WithZero.exp (-((N₀ : ℤ) + 1)) := by
    rw [hcdef, map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc1 : Valued.v c < 1 := by
    rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hn1 : Valued.v (n : P.1.adicCompletion B.fields.E) ≤ 1 := GlobalTheory.MatNthRoot.v_natCast_le_one n
  have hε : Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  set e := WithZero.log (Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c)) with he
  refine ⟨(-e).toNat, fun x hxv w hw hxw => ?_⟩

  have hxP : ∀ r s, adAt B.host.F P.1 (x.1.1 r s) = adAt B.host.F P.1 (w.1 r s) := fun r s => by
    have h := congrArg (fun g : GL (Fin ((I.rec7 l Z).R.N i)) _ => g.1 r s) hxw
    refine GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 ?_
    rw [hu]
    exact h
  have hwP := ((hd _ w).2.2).1 hw
  have hwP := ((hd (-e).toNat w).2.2).1 hw
  have hA : ∀ r s, Valued.v (adAt B.host.F P.1 (x.1.1 r s) - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s) ≤
      Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) := fun r s => by
    rw [hxP]
    refine (hwP r s).trans ?_
    rw [← WithZero.exp_log hε, ← he]
    exact WithZero.exp_le_exp.2 (by omega)
  let x' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := x.1
  obtain ⟨Mu, hMun, hMu1⟩ := exists_root_GL P.1 (B.R.N i) n hn c hc1
    (Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) x') hA
  obtain ⟨z, hzU, hzv, hzP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv Mu
  have hz : z ∈ S.U := hN₀ z hzU hzv (((hd N₀ z).2.2).2 fun r s => by
    rw [hzP]
    refine (hMu1 r s).trans ?_
    rw [map_mul, hc]
    exact (mul_le_of_le_one_left' hn1).trans (WithZero.exp_le_exp.2 (by omega)))
  have hgU : (z ^ n)⁻¹ * x.1 ∈ S.U := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hz n)) x.2
  have hyU := ((S.U_eq _).1 hgU).1
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPin l Z).2.2.2 i hi).1
  let z' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := z
  have hzmap : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) z' = Mu := Units.ext (Matrix.ext hzP)
  have key : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) ((z' ^ n)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, map_pow, hzmap, hMun, inv_mul_cancel]
  have hyP : ∀ r s, adAt B.host.F P.1 (((z ^ n)⁻¹ * x.1).1 r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s :=
    fun r s => congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) key
  have hover : ∀ w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), w.under (𝓞 (I.rec7 l Z).host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 :=
    fun w hw => (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 w).1 (hw.trans hu.symm)
  have hyv : ∀ v', bc (prV (E := (I.rec7 l Z).host.E) v') ((z ^ n)⁻¹ * x.1) = 1 := by
    intro v'
    by_cases hv' : v' = v
    · rw [hv']
      exact bc_prV_eq_one_of_split (I.rec7 l Z).sp.cm hgram hyU P.1 v hover hyP
    · exact map_inv_pow_mul_eq_one _ n (hzv v' hv') (hxv v' hv')
  exact chi_eq_one_of_pow S.chi x ⟨z, hz⟩ n (hchi _) (S.chi_triv _ fun v' _ => hyv v')

end GlobalTheory.Mem.Col2.AdT.SplitChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterOnParahoricChartImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartChi


set_option maxHeartbeats 2000000 in
theorem levChi_chart : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd
  have hlev := (GlobalTheory.chart_level_iff D c w hw j hj s hs PP hPP v φ hφ ι hι y).2 hy
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hfl.selfDual hfl.frame hι
  have hv : v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  rw [Lev.levG, Lev.mem_levA, hL] at hlev
  have hmem := hlev.2
  rw [mem_lev, mem_parLev] at hmem
  obtain ⟨⟨-, hS, -, hQ⟩, -⟩ := hmem
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [Lev.levChi, hL]
  set L := Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B with hLd
  have hLxq : L.xq = fun PP => (w.ξ PP)⁻¹ := by rw [hLd]; simp [Lev.datY]
  have hLPg : L.Pg = w.Pg := rfl
  have hLQ : L.Q = w.Q := rfl
  have hLr : L.r = D.R.r := rfl
  set x := Lev.finE s.V (ι y) with hx
  have h1 : ext1 L.P.H (⇑L.P.chi) (rTup s.β L x) = 1 := Lev.subgroupCharExtension_one_apply (LevelP.triv w.Pg D.R.r ℂ).H _
  have h2 : ∏ PP ∈ L.Pg, ∏ c ∈ Finset.range L.s, (L.cg (c + 1) PP) (dBlk (blkOf L.r L.t) (c + 1) (redFn s.β PP x)) = 1 := by
    refine Finset.prod_eq_one fun PP' hP' => Finset.prod_eq_one fun c' _ => ?_
    have hne : PP' ≠ PP := by
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    rw [hone PP' (hsub _ (Or.inl hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  have h3 : ∏ PP ∈ L.Q, (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) = (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) := by
    refine Finset.prod_eq_single PP (fun PP' hP' hne => ?_) (fun h => absurd hPP h)
    rw [hone PP' (hsub _ (Or.inr hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  unfold levFn
  rw [h1, h2, h3, one_mul, one_mul, hLxq]
  obtain ⟨⟨rr, -, -, hrel, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hQP : redFn s.β PP x ∈ blockTri (blk2 D.R.r) := hQ PP hPP
  obtain ⟨Y, hY⟩ := hS
  set G := (grpCo φ s.V (frCo φ s.β) (ι y)).val with hG
  have hi : intGL D.host.F D.host.E _ Y = s.β⁻¹ * x * s.β := by
    rw [← hY]
    simp [frGL, MulAut.conj_apply]
    group
  have hxm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) x =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom s.V (ι y)) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (x.val i j) = rdA φ ((Formalism.L2.Theta.matHom s.V (ι y)).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (s.β⁻¹ * x * s.β) = grpCo φ s.V (frCo φ s.β) (ι y) := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hxm]
    rfl
  have key : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = G a b := by
    intro a b
    rw [hG, ← hm, ← hi]
    rfl
  have hint : ∀ a b, G a b ∈ v.adicCompletionIntegers D.host.F := fun a b => key a b ▸ (hN _ (Y.val a b).2).1
  have hred : ∀ a b, rr ⟨G a b, hint a b⟩ = (redFn s.β PP x).val a b := by
    intro a b
    obtain ⟨h, hh⟩ := hN _ (Y.val a b).2
    rw [← hY, redFn_frGL]
    have e : (⟨G a b, hint a b⟩ : v.adicCompletionIntegers D.host.F) = ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (Y.val a b : Lev.EAf D), h⟩ :=
      Subtype.ext (key a b).symm
    rw [e, hh]
    rfl
  have hT : ∀ i : Blocks j D.R.t, blk2 D.R.r (ε (.inr i)) = 1 := by
    intro i
    have := GlobalTheory.ChartLevel.eps_inr_ge ε hε i
    simp [blk2, not_lt.2 this]
  let f : Blocks j D.R.t → {a : Fin s.V.rank // blk2 D.R.r a = 1} := fun i => ⟨ε (.inr i), hT i⟩
  have hfb : Function.Bijective f := by
    constructor
    · intro i i' h
      have := congrArg Subtype.val h
      exact Sum.inr_injective (ε.injective this)
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := ε.surjective a
      rcases p with p | p
      · exfalso
        have hp : ((ε (.inl p) : Fin s.V.rank) : ℕ) < D.R.r := by rw [hε]; exact p.2
        simp [blk2, hp] at ha
      · exact ⟨p, rfl⟩
  let ef := Equiv.ofBijective f hfb
  let Gi : Matrix (Fin s.V.rank) (Fin s.V.rank) (v.adicCompletionIntegers D.host.F) := fun a b => ⟨G a b, hint a b⟩
  let A : Matrix {a : Fin s.V.rank // blk2 D.R.r a = 1} {a : Fin s.V.rank // blk2 D.R.r a = 1} (v.adicCompletionIntegers D.host.F) :=
    Gi.submatrix Subtype.val Subtype.val
  have hdA : (d : Fv D.host.F v) = ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) := by
    rw [hd]
    have e1 : ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
        (G.submatrix (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank) (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank)).det := by
      rw [show ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = (v.adicCompletionIntegers D.host.F).subtype A.det from rfl,
        RingHom.map_det]
      congr 1
    rw [e1, ← Matrix.det_submatrix_equiv_self ef]
    congr 1
    refine Matrix.ext fun i i' => ?_
    have := congrFun (congrFun (hch y).2 (.inr i)) (.inr i')
    exact this.symm
  have hk : ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) = rr A.det := by
    rw [diag_block_det_val 1 hQP, RingHom.map_det]
    congr 1
    ext a b
    exact (hred a b).symm
  have hrel' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (d : Fv D.host.F v) ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) := by
    rw [hrel]
    refine ⟨hdA ▸ A.det.2, ?_⟩
    rw [hk]
    congr 1
    exact Subtype.ext hdA
  have hξd := hξ d _ hrel'
  show ((((w.ξ PP)⁻¹) (dBlk (blk2 D.R.r) 1 (redFn s.β PP x)) : ℂˣ) : ℂ) = _
  rw [MonoidHom.inv_apply, hξd]

end GlobalTheory.ChartChi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocModMove

theorem placeIdem_mul_eq_zero {D : D7} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε) (a : AE D)
    (ha : a ∈ GlobalTheory.FinPl.idOff D (· = v)) : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := GlobalTheory.FinPl.placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hav : GlobalTheory.FinPl.compAt D v a = 0 := by
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha
    exact ha v rfl
  apply GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · subst h; rw [hav, mul_zero]
    · rw [hc w, hw w h, TensorProduct.zero_tmul, zero_mul]

theorem ent_of_mem_grpOff {D : D7} {V : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V P) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D P := by
  have hker := MonoidHom.mem_ker.1 hg
  intro i j
  rw [← Ideal.Quotient.eq]
  have h2 := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P) => u.1 i j) hker
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
  have h3 : Ideal.Quotient.mk (GlobalTheory.FinPl.idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P)) i j := by
    by_cases hij : i = j
    · subst hij; simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h3, ← h2]
  rfl

theorem mul_mul_eq_self {D : D7} {m n : ℕ} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (A : Matrix (Fin m) (Fin m) (AE D)) (B : Matrix (Fin n) (Fin n) (AE D)) (y : Matrix (Fin m) (Fin n) (AE D))
    (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hB : ∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hy : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * y i j = y i j) : HMul.hMul (HMul.hMul A y) B = y := by
  have kill : ∀ a ∈ GlobalTheory.FinPl.idOff D (· = v), ∀ b : AE D, b = algebraMap (AF D.host.F) (AE D) ε * b → a * b = 0 := by
    intro a ha b hb
    rw [hb, ← mul_assoc, mul_comm a, placeIdem_mul_eq_zero v ε hε a ha, zero_mul]
  have h1 : HMul.hMul (A - 1) y = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply]
    exact kill _ (hA i l) _ (hy l j).symm
  have h2 : HMul.hMul y (B - 1) = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply, mul_comm]
    exact kill _ (hB l j) _ (hy i l).symm
  have e1 : HMul.hMul A y = y := by
    rw [← sub_eq_zero, ← h1, Matrix.sub_mul, Matrix.one_mul]
  have e2 : HMul.hMul y B = y := by
    rw [← sub_eq_zero, ← h2, Matrix.mul_sub, Matrix.mul_one]
  rw [e1, e2]

theorem actO_eq_self {D : D7} {V W : HSp D} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = v)) {h : GA D W} (hh : h ∈ GlobalTheory.FinPl.grpOff W (· = v))
    (y : WO V W) (hy : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y) : actO V W g h y = y := by
  unfold actO
  exact mul_mul_eq_self v ε hε _ _ _ (ent_of_mem_grpOff hh)
    (ent_of_mem_grpOff ((GlobalTheory.FinPl.grpOff V (· = v)).inv_mem hg)) hy

theorem isModel_weil_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (ω : Om V W), IsWeilDatumO ψ V W χV χW ω →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FV : Frame k V.rank Y') (FW : Frame k W.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO V W → ℂ)), (ofSplit q).IsModel ψ FV FW Tm →
  ∀ g ∈ GlobalTheory.FinPl.grpOff V (· = q.v), ∀ h ∈ GlobalTheory.FinPl.grpOff W (· = q.v), (ofSplit q).IsModel ψ FV FW ((ω (g, h)) ∘ₗ Tm) := by
  intro D k _ _ _ _ q ψ hψ V W χV χW ω hω Y Y' _ _ _ _ FV FW Tm hM g hg h hh
  obtain ⟨ε, hεv, hsum⟩ := q.above
  refine (GlobalTheory.LocModU.localModel_uniq_transport_exist D k (ofSplit q) Y Y' V W FV FW ψ hψ).2.1 Tm hM (ω (g, h))
    (fun f hf => hω.om_pres _ f hf) (fun f hf y hy => ?_)
  have hy' : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y := by
    rw [← hsum]; exact hy
  rw [hω.om_heis g h y f hf, actO_eq_self q.v ε hεv hg hh y hy']

end GlobalTheory.LocModMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparation
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem normalCountSteps : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep :=
  ⟨Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds, Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds,
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds⟩

end GlobalTheory.Core.One
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvdStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd : ∀ (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ), (π' : D.host.E) = star (π : D.host.E) → π * π' = (T : 𝓞 D.host.E) → π ≠ 0 → ∀ x : HeightOneSpectrum (𝓞 D.host.F), (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  first | exact @GlobalTheory.NormPlaces.places_dvd_iff | exact GlobalTheory.NormPlaces.places_dvd_iff | (intros; apply GlobalTheory.NormPlaces.places_dvd_iff <;> assumption)
end

