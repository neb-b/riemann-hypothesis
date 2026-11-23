module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Formalism.LocalToGlobal.Divisibility.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinksInputs

theorem inputs_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, Inputs D := by
  intro hW _ hH hC D
  obtain ⟨hcart, hsd, hsp, hdim, hpet, hsm⟩ := GlobalTheory.Mem.EasyInputs.easy_inputs D
  exact
    { weil := Formalism.IndefR.WeilFull.weilExistsFull_of (hW D) (_root_.GlobalTheory.InertAll.inertAllO D) (_root_.GlobalTheory.WeilReal.realAllO D)
      vac := GlobalTheory.Member.vacuum_oriented_exists D
      stepVec := GlobalTheory.PlaceDatum.stepVecExists D
      thPVec := GlobalTheory.PlaceVec.thPVecExists D
      ptStable := _root_.GlobalTheory.FockTheta.ptStable D
      cartan := hcart
      selfDual := hsd
      vecTheta := _root_.GlobalTheory.VecTheta.vecThetaSD D
      measFD := Formalism.IndefR.Eqv.measFDExists_holds D
      measDef := Formalism.IndefR.Eqv.measLevDefExists_holds D
      fund := Formalism.IndefR.Eqv.fundDomExists_holds D
      sp := hsp
      lev := GlobalTheory.Mem.LevelOK.levOK_all D
      hc := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
      schur := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
      pet := hpet
      sm := hsm
      dim := hdim
      act := GlobalTheory.MultAction.actRep D }

end GlobalTheory.LinksInputs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisChangeIntegralUnitDet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.LocBasisChange

theorem norm_le_one_of_isIntegral_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_det_le_one {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (h : ∀ a b, ‖M a b‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, M (σ i) i‖ ≤ 1 := by
    rw [norm_prod]; exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

theorem norm_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {s : ℕ} (hs : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs

theorem basis_change : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm Bs hR hL
  have hm : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  set ρ : D.host.E →+* ℂ_[p] := lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar hm) with hρ
  have hρe : ∀ x, TaylorLogMetric.tauEmb D lam τ x = ρ x := fun x => dif_pos (hm x)
  have hint : ∀ y : 𝓞 D.host.E, ‖ρ (y : D.host.E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (map_isIntegral_int ρ y.isIntegral_coe)
  have hunit : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact norm_natCast_of_not_dvd hs
  set Mm : Matrix (Fin N) (Fin N) D.host.E := (Bm : Matrix (Fin N) (Fin N) D.host.E) with hMm
  set Mi : Matrix (Fin N) (Fin N) D.host.E := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) with hMi
  have hMMi : Mm * Mi = 1 := Bm.mul_inv
  have hMiM : Mi * Mm = 1 := Bm.inv_mul
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := Mm.map ρ with hA
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := Mi.map ρ with hAi
  have hAAi : A * Ai = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMMi, map_one]
  have hAiA : Ai * A = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMiM, map_one]
  set g : Matrix (Fin N) (Fin N) ℂ_[p] := Ai * Bs with hg
  have hBs : Bs = A * g := by rw [hg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hgi : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hB⟩ := hR.2.2 b
    have e : g a b = ∑ k, r k * ρ ((Mi *ᵥ x k) a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hg, Matrix.mul_apply, hB, hρe, hAi, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    obtain ⟨s, hs, hmem⟩ := (hL (x k)).1 ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using hx k⟩
    obtain ⟨z, hz⟩ := hmem a
    have h1 : ‖ρ ((s : D.host.E) * (Mi *ᵥ x k) a)‖ ≤ 1 := by rw [← hz]; exact hint z
    rw [map_mul, norm_mul, hunit s hs, one_mul] at h1
    rw [norm_mul]
    calc ‖r k‖ * ‖ρ ((Mi *ᵥ x k) a)‖ ≤ 1 * 1 := by gcongr; exact hr k
      _ = 1 := one_mul 1
  have hBsu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hR.1
  set h : Matrix (Fin N) (Fin N) ℂ_[p] := Bs⁻¹ * A with hh
  have hgh : g * h = 1 := by
    rw [hg, hh, Matrix.mul_assoc, ← Matrix.mul_assoc Bs, Matrix.mul_nonsing_inv _ hBsu, Matrix.one_mul, hAiA]
  have hhi : ∀ a b, ‖h a b‖ ≤ 1 := by
    intro a b
    set xb : Fin N → D.host.E := fun j => Mm j b with hxb
    have hcol : ∀ a, (Mi *ᵥ xb) a = (1 : Matrix (Fin N) (Fin N) D.host.E) a b := by
      intro a; rw [← hMiM]; rfl
    obtain ⟨s, hs, hmem⟩ := (hL xb).2 ⟨1, (Fact.out : p.Prime).not_dvd_one, fun a => by
      rw [hcol, Nat.cast_one, one_mul, Matrix.one_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩⟩
    have hb := hR.2.1 _ hmem a
    have key : (Bs⁻¹ *ᵥ fun i => TaylorLogMetric.tauEmb D lam τ (((s : D.host.E) • xb) i)) a = ρ s * h a b := by
      simp only [hρe, Pi.smul_apply, smul_eq_mul, map_mul, hh, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hA, Matrix.map_apply, hxb, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key, norm_mul, map_natCast, norm_natCast_of_not_dvd hs, one_mul] at hb
    exact hb
  have hd1 := norm_det_le_one g hgi
  have hd2 := norm_det_le_one h hhi
  have hprod : ‖g.det‖ * ‖h.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, hgh, Matrix.det_one, norm_one]
  refine ⟨g, hgi, le_antisymm hd1 ?_, ?_⟩
  swap
  · rw [hBs]; congr 1; ext i j; simp only [hA, Matrix.map_apply, hρe]
  calc (1 : ℝ) = ‖g.det‖ * ‖h.det‖ := hprod.symm
    _ ≤ ‖g.det‖ * 1 := by gcongr
    _ = ‖g.det‖ := mul_one _

end GlobalTheory.LocBasisChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetric
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc

theorem membership_iff_unipSym : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  intro D X h hE hg k hk Ns hNs
  have hK2 : k ∈ X.K2 ↔ K2cong X.B.I X.B.g X.e0 X.z0 X.bw k := ⟨fun hm => hm.2, fun hm => ⟨hk, hm⟩⟩
  have hLf : ∀ y ∈ X.B.I.Lf, (X.B.I.fmat k - 1) *ᵥ y ∈ X.B.I.Lf := by
    intro y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hk y).1 hy) hy
  have hS1 : ∀ a : Fin D.R.rS, X.e0 '' {b | b.1 < a.1} ⊆ X.B.I.Lf := by
    rintro a _ ⟨b, -, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS2 : Set.range X.e0 ⊆ X.B.I.Lf := by
    rintro _ ⟨b, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS3 : ∀ i : Fin D.R.k, Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} ⊆ X.B.I.Lf := by
    rintro i _ (⟨b, rfl⟩ | ⟨j, -, rfl⟩)
    · exact (X.vectorsInLattice.1 b).1
    · exact (X.vectorsInLattice.2.2 j).1
  have hK : K2cong X.B.I X.B.g X.e0 X.z0 X.bw k ↔
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k := by
    have e1 := fun a => _root_.GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW D X h hE _ (hS1 a) _ (hLf _ (X.vectorsInLattice.1 a).1)
    have e2 := _root_.GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW D X h hE _ hS2 _ (hLf _ X.vectorsInLattice.2.1)
    have e3 := fun i => _root_.GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW D X h hE _ (hS3 i) _ (hLf _ (X.vectorsInLattice.2.2 i).1)
    constructor
    · rintro ⟨h1, h2, h3⟩ w hw
      exact ⟨fun a => (e1 a).1 (h1 a) w hw, e2.1 h2 w hw, fun i => (e3 i).1 (h3 i) w hw⟩
    · intro H
      exact ⟨fun a => (e1 a).2 fun w hw => (H w hw).1 a, e2.2 fun w hw => (H w hw).2.1,
        fun i => (e3 i).2 fun w hw => (H w hw).2.2 i⟩
  have hgE : ((X.B.g : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [X.g_eq, Nat.cast_mul]
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    rintro ⟨kk, v⟩
    rw [hgE]
    fin_cases kk
    · exact Ideal.mul_mem_right _ _ (hg ⟨0, v⟩)
    · exact Ideal.mul_mem_left _ _ (hg ⟨1, v⟩)
  have hP : (∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k) ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), CondAt X (D.naut.plGw kv.1 kv.2) k ∧
        CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k := by
    constructor
    · intro H kv
      refine ⟨H _ (hgw kv), H _ ?_⟩
      rw [GlobalTheory.DimPartsCompare.mem_cPl, map_natCast]
      exact hgw kv
    · intro H w hw
      rw [hgE] at hw
      rcases w.isPrime.mem_or_mem hw with h0 | h1
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 0 w h0
        · exact (H ⟨0, v⟩).1
        · exact (H ⟨0, v⟩).2
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 1 w h1
        · exact (H ⟨1, v⟩).1
        · exact (H ⟨1, v⟩).2
  rw [hK2, hK, hP]
  exact forall_congr' fun kv => (_root_.GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt D X h hE hg k hk kv).symm.trans (_root_.GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond D X h hE hg k hk kv (Ns kv) (hNs kv)).symm

end GlobalTheory.Mem.GroupLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormOneIntegralIffConjugateValuationsEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.FullDt
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E)

theorem mem_u1int_iff_entry (u : GL (Fin 1) (AfE F E)) :
    u ∈ Formalism.L2.Herm.IntegralUnitGroup hc ↔ u ∈ Formalism.L2.Herm.unitaryOneFiniteAdeles hc ∧ ∀ y : Fin 1 → AfE F E,
      (y 0 ∈ RInt F E ↔ (u : Matrix (Fin 1) (Fin 1) (AfE F E)) 0 0 * y 0 ∈ RInt F E) := by
  have hl : ∀ y : Fin 1 → AfE F E, y ∈ (Formalism.UG.stdLat (n := Fin 1) ↥(RInt F E) : Submodule ↥(RInt F E) (Fin 1 → AfE F E)) ↔
      y 0 ∈ RInt F E := by
    intro y
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_one]
    exact ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  show u ∈ Formalism.UG.UJ _ _ ⊓ Formalism.UG.stabGL _ ↔ _
  rw [Subgroup.mem_inf]
  refine and_congr Iff.rfl ?_
  show (∀ y, _ ↔ _) ↔ _
  refine forall_congr' fun y => ?_
  rw [hl, hl]
  simp [Matrix.mulVec, dotProduct]


omit [StarRing E] in
theorem rInt_mul_iff {c d : AfE F E} (hcd : c * d = 1) :
    (∀ y : AfE F E, y ∈ RInt F E ↔ c * y ∈ RInt F E) ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P c) = 1 := by
  constructor
  · intro h P
    have hc1 : c ∈ RInt F E := by simpa using (h 1).1 (one_mem _)
    have hd1 : d ∈ RInt F E := (h d).2 (by rw [hcd]; exact one_mem _)
    have a1 := (mem_rInt_iff F E c).1 hc1 P
    have a2 := (mem_rInt_iff F E d).1 hd1 P
    rw [← adAt_apply] at a1 a2
    have e : Valued.v (adAt F P c) * Valued.v (adAt F P d) = 1 := by rw [← map_mul, ← map_mul, hcd, map_one, map_one]
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  · intro h y
    rw [mem_rInt_iff, mem_rInt_iff]
    refine forall_congr' fun P => ?_
    rw [← adAt_apply, ← adAt_apply, map_mul, map_mul, h P, one_mul]
end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_u1int_iff_val : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E),
    IsDetLift (host_cmData R H) x.1 a → ((x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)) ↔
      ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (compAt w a) = Valued.v (compAt (conjPrime₂ w) a)) := by
  intro R H x a ha
  have hcd : ((x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0) * ((x.1⁻¹ : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 = 1 := by
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) (AfE H.F H.E) => M 0 0) (Units.mul_inv x.1)
    simpa [Matrix.mul_apply] using this
  rw [mem_u1int_iff_entry, and_iff_right x.2]
  have e1 : (∀ y : Fin 1 → AfE H.F H.E, (y 0 ∈ RInt H.F H.E ↔ (x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 * y 0 ∈ RInt H.F H.E)) ↔
      ∀ y : AfE H.F H.E, (y ∈ RInt H.F H.E ↔ (x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 * y ∈ RInt H.F H.E) :=
    ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩
  rw [e1, rInt_mul_iff hcd]
  refine forall_congr' fun w => ?_
  have k := congrArg Valued.v (DetSpec.compAt_eq ha w)
  rw [map_mul, valued_sigR, adAt_finAf, Matrix.det_fin_one] at k
  rw [k]
  have h0 := DetSpec.val_compAt_ne (conjPrime₂ w) a
  constructor
  · intro h; rw [h, one_mul]
  · intro h
    exact (mul_eq_right₀ h0).1 h
end GlobalTheory.Mem.Col2.FullDt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem adAt_eq_one_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z : AfE F E}
    (hz : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = 1) : adAt F P z = 1 := by
  set v := P.under (𝓞 F)
  have h1 : Formalism.UG.P.afsplitEps E v * z = Formalism.UG.P.afsplitEps E v := by
    rw [← Formalism.UG.P.afsplit_decomp, hz]
    rfl
  have h2 : Formalism.UG.P.afsplitEps E v = (1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (1 : v.adicCompletion F) := by
    rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 := by
    rw [h2, adAt_apply, GlobalTheory.Mem.ReadTwist.afIso_one_tmul (k := 1)]
    · simp
    · rw [Formalism.UG.P.afsplitI_self]; simp
  have h4 := congrArg (adAt F P) h1
  rwa [map_mul, h3, one_mul] at h4

theorem detPt_eq_u1Dt_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  intro R H n ST SG Q SQ p y k x hl hp hk hc hbc hx
  obtain ⟨a, ha⟩ := exists_lift H x
  obtain ⟨b, hb⟩ := DetLift.exists_isDetLift R H n k hk
  have hab : IsDetLift (host_cmData R H) (y * k) (a * b) := by
    unfold IsDetLift at ha hb ⊢
    rw [map_mul, map_mul, ha, hb, hx, map_mul]
  have hK : b ∈ KDq H SQ := by
    refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
    · rw [DetSpec.val_compAt_eq hb ⟨stdLat_lattice, stdLat_unimodular⟩ hc (fr := fun _ => LinearEquiv.refl _ _)
        (fun _ _ => Iff.rfl) w]
      simp
    · have hdet : adAt H.F P (k : Matrix (Fin n) (Fin n) (AfE H.F H.E)).det = 1 := by
        refine adAt_eq_one_of_prV P ?_
        have h := congrArg (fun g => Matrix.det (Units.val g)) (hbc P hP)
        simp only [Formalism.UG.bc, Units.coe_map, Units.val_one, Matrix.det_one] at h
        rw [RingHom.map_det]
        exact h
      have hs0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 :=
        (((Units.isUnit (finAf H.F H.E b)).map (Formalism.UG.sigR (host_cmData R H).sig _)).map (adAt H.F P)).ne_zero
      rw [DetSpec.compAt_eq hb P, hdet, one_mul, div_self hs0, sub_self, map_zero]
      exact zero_lt_one
  rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, ← DetSpec.mk_eq_detPt R H n ST SG Q SQ p (y * k) (a * b) hl hp hab,
    QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hK, mul_one]

end GlobalTheory.Mem.Col2.FullDt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClass
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem e1Q_eq_u1Dt_of_det_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  intro R H SQ z x hx
  obtain ⟨k, hk⟩ := exists_eq_div_conj H z
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk]
  symm
  apply normOneFiniteAdeleDetClass_of_isDetLift
  unfold IsDetLift
  rw [hx]
  have hf : finAf H.F H.E (Neutral.B1.diagUnits H.E k) = Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    apply (afIso H.F H.E).injective
    rw [afIso_finAf]
    show _ = afIso H.F H.E ((k : H.E) ⊗ₜ[H.F] 1)
    rw [afIso_tmul_one]
    rfl
  rw [hf]
  have key : Formalism.L2.Herm.unitaryOneRationalAdele H.F z * conjId (host_cmData R H).sig
      (Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k) =
      Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    show Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (z : H.E) *
      Formalism.UG.sigR (host_cmData R H).sig _ (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)) =
      Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)
    rw [sigR_inclE, ← map_mul, bridge_star_holds R H, hk]
  rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]
  exact key.symm

end GlobalTheory.Mem.Col2.FullDt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 4000000 in
theorem rowConditions_at_companion_from_readings : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) , (Lam3 x.Z → RowsHoldLam3 (divisionPairOfAdelicFormsFaceColumnsData x)) ∧ RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) ∧ DcPtG (divisionPairOfAdelicFormsFaceColumnsData x) ∧ (DivRows3 D x.A3 x.F.P0 x.F.ψ0 x.F.P1 x.F.ψ1 (zsOf x.R x.F) (s0Of x.R x.F) (s1Of x.R x.F) ex.p0 (colOf x.R x.F x.sEE) x.C.NuC (idsOf x.cG x.Z x.C) → DivRows3G (divisionPairOfAdelicFormsFaceColumnsData x)) := by
  intro D L hT Gi Gl K Yd cX ex x
  have hD : RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) := fun u t y F => x.C.pt u t y F
  exact ⟨fun h => h, hD, dcPtG_of hD, fun h => DivRows3.toG (P := divisionPairOfAdelicFormsFaceColumnsData x) h⟩

end GlobalTheory.Mem.R3
end

