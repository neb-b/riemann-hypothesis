module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixDiagonalModLevelOfDiagonalAction
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDiag

theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

theorem coord_zmod (I : AutInst) (g : ℕ) {β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : IsFrame β I.L) {v : VA I}
    (hv : v ∈ mL I g) (i : Fin I.n) :
    ZMod' I g ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v) i) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hv
  have hz' : z ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by rw [hatL_eq]; exact hz
  refine ⟨_, (hβ z).1 hz' i, ?_⟩
  rw [Matrix.mulVec_smul]
  rfl

theorem diag_mod_in_frame : ∀ (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (Y : I.Gf) (d : Fin I.n → Formalism.L2.Herm.intAf I.F I.E), IsLiftFrame I g b β → (∀ y ∈ I.Lf, I.fmat Y *ᵥ y ∈ I.Lf) → (∀ y ∈ I.Lf, I.fmat Y⁻¹ *ᵥ y ∈ I.Lf) → (∀ j : Fin I.n, I.fmat Y *ᵥ b j.val - (d j).1 • b j.val ∈ mL I g) → ∃ x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), frGL β x = (Y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∧ ∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - Matrix.diagonal d) i j).1 := by
  intro I g b β Y d hβ hY hYi hd
  have hK : Y ∈ I.Kset := by
    intro y
    refine ⟨fun hy => hY y hy, fun hy => ?_⟩
    have h := hYi _ hy
    have e : I.fmat Y⁻¹ * I.fmat Y = 1 := by
      show (((Y⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * _ = 1
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  obtain ⟨x, hx⟩ := (kset_iff I hβ.1 Y).1 hK
  refine ⟨x, hx, fun i j => ?_⟩
  have hconj : β⁻¹ * frGL β x * β = intGL I.F I.E I.n x := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx] at hconj
  set col : VA I := fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j with hcol
  have hw : I.fmat Y *ᵥ col - (d j).1 • col ∈ mL I g := by
    have h1 := hβ.2 j
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.RowIndex.mem_mL.1 h1
    have h2 : I.fmat Y *ᵥ (col - b j.val) ∈ mL I g := by
      rw [show col - b j.val = _ from hz']
      exact Formalism.L2.SG.Pf.unitaryCongruence.mL_mv I hY g le_rfl z hz
    have h3 : (d j).1 • (col - b j.val) ∈ mL I g := (mL I g).smul_mem (d j) h1
    have e : I.fmat Y *ᵥ col - (d j).1 • col =
        (I.fmat Y *ᵥ b j.val - (d j).1 • b j.val) + I.fmat Y *ᵥ (col - b j.val) - (d j).1 • (col - b j.val) := by
      rw [Matrix.mulVec_sub, smul_sub]
      abel
    rw [e]
    exact sub_mem (add_mem (hd j) h2) h3
  have key := coord_zmod I g hβ.1 hw i
  convert key using 1
  have eA : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ (I.fmat Y *ᵥ col)) i =
      ((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).1 := by
    rw [Matrix.mulVec_mulVec]
    show ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * I.fmat Y) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, ← Units.val_mul, hconj]
    rfl
  have eB : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ col) i =
      if i = j then 1 else 0 := by
    show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, eA, eB, Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp
  · simp

end GlobalTheory.FrameDiag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_max_iff_val_lt_one (x : 𝒪[k]) : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem pr_incA_int_mem (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] :=
  (q.pr_mem_iff _).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1
    (Formalism.L2.DIV.oToS D.host.F D.host.E x).2)

theorem exists_int_approx (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {u : k} (hu : u ∈ 𝒪[k]) : ∃ z : 𝓞 D.host.E, valuation k (u - q.pr (incA D (z : D.host.E))) < 1 := by
  have h1 : toEAf D (q.e * q.sec u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [map_mul]
    exact (q.pr_mem_iff (q.sec u)).1 (by rw [q.pr_sec]; exact hu)
  have h2 : q.pr (q.e * q.sec u) = u := by rw [← q.sec_pr, q.pr_sec, q.pr_sec]
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot
    (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
  have ha : (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈
    Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h3 := q.val_lt_of_mem_idS he ha
  have e2 : (((⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (q.e * q.sec u) - toEAf D (incA D (a : D.host.E)) := rfl
  rw [e2, RingHom.map_sub, prF_toEAf, prF_toEAf, h2] at h3
  exact ⟨a, h3⟩

theorem hasVal_of_int_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  intro D k _ _ _ _ p PP he m b b' hb _ P hlat c₀ hval u hu r0 hr0
  classical
  choose z hz using fun r => p.exists_int_approx he (hu r)
  obtain ⟨s, hs, hv⟩ := hval (fun r => (z r : D.host.E)) (fun r => (z r).isIntegral_coe) r0 hr0
  have hw : ∀ r, p.pr (incA D (z r : D.host.E)) ∈ 𝒪[k] := fun r => p.pr_incA_int_mem he (z r)
  let d : Fin m → 𝒪[k] := fun r => ⟨u r - p.pr (incA D (z r : D.host.E)), sub_mem (hu r) (hw r)⟩
  have hd : ∀ r, d r ∈ maximalIdeal 𝒪[k] := fun r => (mem_max_iff_val_lt_one (d r)).2 (hz r)
  have hcol : ∀ r, b' *ᵥ (Pi.single r 1 : Fin m → k) ∈ P.lat := fun r => (hlat _).2 fun r' => by
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hker : ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) ∈ P.ker :=
    Submodule.sum_mem _ fun r _ => Pair.smul_mem_ker (hd r) (hcol r)
  have hsum : b' *ᵥ u = (b' *ᵥ fun r' => p.pr (incA D (z r' : D.host.E))) +
      ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) := by
    have : ∀ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = b' *ᵥ (Pi.single r (d r : k) : Fin m → k) := fun r => by
      change (d r : k) • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = _
      rw [← Matrix.mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun r _ => this r, ← Matrix.mulVec_sum, ← Matrix.mulVec_add, Finset.univ_sum_single]
    congr 1
    funext r
    simp [d]
  let c : 𝒪[k] := ⟨_, p.pr_incA_int_mem he c₀⟩
  refine ⟨s + c * d r0, ?_, ?_⟩
  · change (s : k) + p.pr (incA D (c₀ : D.host.E)) * (u r0 - p.pr (incA D (z r0 : D.host.E))) = _
    rw [hs, map_mul, map_mul]
    ring
  · rw [hsum, map_add (f := _), (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_left _ c (hd r0))]
    exact hv.add (Pair.mem_ker.1 hker)

end GlobalTheory.FinPl.SplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlMemGfC
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGfCImg

theorem gl_mem_GfC : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfCImg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAComponentsMemCompletedLatticeOffPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAComp
open GlobalTheory.AdForm.HalfPairing

theorem conjP_not_mem {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS) : Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro hc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  rw [GlobalTheory.OffIdemDen.conjP_eq_cP] at hc
  have hd : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ P (es P) := fun P hP =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ (GlobalTheory.IdemSupport.cP P) (cA D (es P)) := fun P hP =>
    GlobalTheory.IdemSupport.delta_conj hΦ (hd P hP)
  have h1 : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hE : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (es P') (GlobalTheory.IdemSupport.cP P) :=
      map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hE, Finset.sum_eq_single (GlobalTheory.IdemSupport.cP P) (fun P' hP' hne => (hd P' hP').2.2 _ (fun h => hne h.symm))
      (fun h => absurd hc h), (hd _ hc).2.1]
  have h2 : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hC : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (cA D (es P')) (GlobalTheory.IdemSupport.cP P) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hC, Finset.sum_eq_single P (fun P' hP' hne => (hdc P' hP').2.2 _ (fun h => hne (by
        have := congrArg GlobalTheory.IdemSupport.cP h
        rwa [GlobalTheory.OffIdemDen.cP_cP, GlobalTheory.OffIdemDen.cP_cP, eq_comm] at this)))
      (fun h => absurd hP h), (hdc P hP).2.1]
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ P ∈ SS, es P) (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P)
  rw [horth, h1, h2, one_mul, GlobalTheory.IdemSupport.ev_zero] at h3
  exact one_ne_zero h3.symm

theorem halfA_smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E)) :
    (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by rw [_root_.zpow_neg, zpow_one, inv_inv, pow_zero, one_mul])
  · exact key 2 (by rw [neg_neg, zpow_one, pow_two, mul_assoc, mul_inv_cancel₀ hc', mul_one])
  · exact key 1 (by rw [neg_zero, zpow_zero, inv_one, pow_one, mul_one])

theorem halfA_mem_locP_conj {D : D7} {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.HomE D.host.E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE D.host.E a b} (hx : x ∈ halfAO SS M c) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS)
    (hP' : Formalism.L2.Col.conjPrime₂ P ∉ SS) : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := by
  have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ P)))⁻¹ • x ∈
      Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := (Submodule.mem_iInf _).1 hx _
  have hcc : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := by
    rw [GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.cP_cP]
  have he : expS SS (Formalism.L2.Col.conjPrime₂ P) = -1 := by
    unfold expS; rw [if_neg hP', if_pos (by rw [hcc]; exact hP)]
  have hc' : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [he, neg_neg, zpow_one] at h
  have := nsmul_mem h c
  rwa [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hc', one_smul] at this

theorem halfA_mem_locP_off {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ}
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)) : x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have he : expS SS Q = 0 := by
    unfold expS; rw [if_neg (fun h => hQ (Or.inl h)), if_neg (fun h => hQ (Or.inr h))]
  rwa [he, neg_zero, zpow_zero, inv_one, one_smul] at h


set_option maxHeartbeats 1000000 in
theorem zmem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _ x' hx
  have hA : ((LinearMap.toMatrix' x').map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    have hE' := hE
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE'
    have e1 : ((LinearMap.toMatrix' x').map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x').map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
      rfl
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc hN (hes PP hPP) ?_
      (halfA_mem_locP_conj hc hx hPP (conjP_not_mem hE hPP))
    exact GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by
      rw [Finset.mem_singleton.1 hQ]; exact hes PP hPP, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
  have hcx : ((c : D.host.E) • x') ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    GlobalTheory.ThetaMove.mem_of_locP fun Q => halfA_smul_mem_locP hc hx Q
  obtain ⟨d, hd0, hdx, hdG⟩ := _root_.GlobalTheory.OffDen.exists_den_avoid D.host.E _ _ _ (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc x' hcx
    (fun Q hQ => halfA_mem_locP_off hx Q hQ)
  obtain ⟨a₁, a₂, ha₁, ha₂, ho⟩ := _root_.GlobalTheory.OffIdemTwo.off_two D e SS hE c hc d hd0 hdG
  have hB : a₁ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₁ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hcx))
  have hC : a₂ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((d : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₂ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hdx))
  convert add_mem hA (add_mem hB hC) using 1
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc := GlobalTheory.PlaceVec.infPart_cA hinf
  have i1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := fun M i j => by
    have := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
    simpa using this
  have f1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := fun M i j => by
    rw [GlobalTheory.LatVacSign.finRat_eq]; rfl
  rw [← GlobalTheory.LatVacSign.finRat_eq, ← GlobalTheory.LatVacSign.finRat_eq]
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, i1, hinf, hinfc,
      mul_zero, zero_mul, sub_zero, add_zero]
  · have hs : ∀ r : D.host.E, LinearMap.toMatrix' (r • x') i j = r * LinearMap.toMatrix' x' i j := fun r => by
      rw [map_smul]; rfl
    have ho' := congrArg (finPart D) ho
    simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_one] at ho'
    simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, f1, hs]
    linear_combination (finPart D (incA D (LinearMap.toMatrix' x' i j))) * ho'

end GlobalTheory.HalfAComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfASignTraceIsInteger
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TraceInt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SemiTrace

theorem alV_embH_eq_exp_trace (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ)
    (hP : StdPair θ S T δ sc ψ) (y : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    alV D.host.d sc (embH (tauE D) δ y) = Complex.exp (-(Real.pi : ℂ) * Complex.I *
      ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) : ℚ) : ℂ)) := by
  have hd : 0 < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))
  set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) with htdef
  set M := LinearMap.toMatrix' y with hMdef
  have hMij : ∀ i j, M i j = y (Pi.single j 1) i := by
    intro i j; simp [M, LinearMap.toMatrix'_apply]
  set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs
  have hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ) := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]
    simp only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]
    push_cast
    rw [Finset.sum_comm]
    calc _ = ∑ j, ∑ i, ((Complex.normSq (tauE D τ (M i j)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
      _ = _ := Finset.sum_comm
  have hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2 := by
    intro τ
    rw [map_mul, map_mul, map_pow, map_div₀, map_add (f := _), map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD,
      Complex.re_mul_ofReal, re_xi_mul_sq _ hd]
    ring
  have hk' : (t : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ) := by
    have e1 := sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)
    rw [← htdef] at e1
    rw [← e1]
    simp only [hτ]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹ := by
    rw [← Complex.sq_norm]; exact hP.scale
  have hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ := by
    simp only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]
    rw [show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) =
        ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    simp_rw [Complex.normSq_mul, ← Finset.mul_sum]
    simp only [hs, hMij]
    rw [← mul_assoc sc, hsc]
    field_simp
  have hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(t : ℂ) := by rw [hk']; push_cast; ring
  rw [alV, Formalism.L2.Th1.H.alphaQ, hq, hsum]
  congr 1
  ring

theorem trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) := by
  intro D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'
  have h2 := _root_.GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'
  rw [alV_embH_eq_exp_trace D ψ θ S T δ sc hP, ← Complex.exp_add] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨-n, ?_⟩
  set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) with htdef
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
  have : ((t : ℚ) : ℂ) = (((-n : ℤ) : ℚ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination (-1/2 : ℂ) * hn
  exact_mod_cast this.symm
end GlobalTheory.TraceInt
end
end

