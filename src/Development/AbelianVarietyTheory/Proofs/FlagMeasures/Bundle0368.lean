module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaCocycleProductOfRationalUnipotents
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealIntegralUnipotentBesselModelsCountableSubgro
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovGrp
open Formalism.QuantumDeterminants Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen
variable {n k r : ℕ}

theorem coord_span_zero (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (hQ1 : Qi * Q = 1) (lam : ℂ) (e : Fin r → Fin n → ℂ)
    (he : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (c : ℕ) (y : Fin n → ℂ) (hy : y ∈ Formalism.L2.SG.HidaSetting.spanLt e c) (i : Fin (2 * r + k + 1)) (hi : c ≤ i.val) :
    (Qi *ᵥ y) i = 0 := by
  let f : (Fin n → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp (Matrix.mulVecLin Qi)
  have hle : Formalism.L2.SG.HidaSetting.spanLt e c ≤ LinearMap.ker f := by
    unfold Formalism.L2.SG.HidaSetting.spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_setOf_eq] at hb
    have hne : lam ^ (r - (b : ℕ)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => Qi *ᵥ w) (he b)
      simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (eI k r b)
      simp at h2
    have h1 := congrArg (fun w => Qi *ᵥ w) (he b)
    simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    have h3 : Qi *ᵥ e b = (lam ^ (r - (b : ℕ)))⁻¹ • Pi.single (eI k r b) 1 := by
      rw [h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    show f (e b) = 0
    simp only [f, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj,
      Function.eval, h3, Pi.smul_apply, smul_eq_mul]
    have : i ≠ eI k r b := by
      intro h; rw [h] at hi; simp [eI] at hi; omega
    simp [Pi.single_apply, this]
  exact hle hy

theorem mem_nset (J : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (hQ1 : Qi * Q = 1) (hQ2 : Q * Qi = 1)
    (hH : Qᴴ * J * Q = Hpk k r) (lam : ℂ) (e : Fin r → Fin n → ℂ)
    (he : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * J * M = J)
    (hS : ∀ a : Fin r, (M - 1) *ᵥ e a ∈ Formalism.L2.SG.HidaSetting.spanLt e a.1)
    (hX : ∀ y, (∀ a, star (e a) ⬝ᵥ (J *ᵥ y) = 0) → (M - 1) *ᵥ y ∈ Formalism.L2.SG.HidaSetting.spanLt e r) :
    Qi * M * Q ∈ Nset k r := by
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qi * M * Q) i j = (Qi *ᵥ (M *ᵥ (Q *ᵥ Pi.single j 1))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hsplit : ∀ w : Fin n → ℂ, Qi *ᵥ (M *ᵥ w) = Qi *ᵥ w + Qi *ᵥ ((M - 1) *ᵥ w) := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    abel
  refine ⟨?_, ?_, ?_⟩
  · show (Qi * M * Q)ᴴ * Hpk k r * (Qi * M * Q) = Hpk k r
    have hQ2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ2, Matrix.conjTranspose_one]
    rw [← hH]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    calc Qᴴ * (Mᴴ * (Qiᴴ * (Qᴴ * (J * (Q * (Qi * (M * Q)))))))
        = Qᴴ * (Mᴴ * ((Qiᴴ * Qᴴ) * (J * ((Q * Qi) * (M * Q))))) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((Mᴴ * J * M) * Q) := by rw [hQ2', hQ2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hM]
  · intro a i hai
    have hne : lam ^ (r - (a : ℕ)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
      simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (eI k r a)
      simp at h2
    have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
    simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    have hv : Qi *ᵥ (M *ᵥ (Q *ᵥ Pi.single (eI k r a) 1)) =
        Pi.single (eI k r a) 1 + lam ^ (r - (a : ℕ)) • (Qi *ᵥ ((M - 1) *ᵥ e a)) := by
      rw [he a, Matrix.mulVec_smul, Matrix.mulVec_smul, hsplit, smul_add, ← h1]
    rw [hcol, hv, Pi.add_apply, Pi.smul_apply,
      coord_span_zero Q Qi hQ1 lam e he a.1 _ (hS a) i (by simpa [eI] using hai), smul_zero, add_zero,
      Pi.single_apply]
  · intro i j hj1 hj2 hi
    have horth : ∀ a, star (e a) ⬝ᵥ (J *ᵥ (Q *ᵥ Pi.single j 1)) = 0 := by
      intro a
      have hne : lam ^ (r - (a : ℕ)) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
        simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
        have h2 := congrFun h1 (eI k r a)
        simp at h2
      have key : star (Q *ᵥ Pi.single (eI k r a) 1) ⬝ᵥ (J *ᵥ (Q *ᵥ Pi.single j 1)) = 0 := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
        have hz : Hpk k r (eI k r a) j = 0 := by
          have ha := a.isLt
          unfold Hpk
          simp only [eI, Fin.ext_iff]
          split_ifs <;> first | rfl | (exfalso; omega)
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, hz]
      rw [he a, star_smul, smul_dotProduct] at key
      exact (smul_eq_zero.1 key).resolve_left (by simpa using hne)
    rw [hcol, hsplit, Pi.add_apply, coord_span_zero Q Qi hQ1 lam e he r _ (hX _ horth) i hi, add_zero,
      Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
    simp [Pi.single_apply]

end Gen

section Main
open GlobalTheory.TypeAsm

theorem trI_one {D : D7} {X : HidaSetting D} (C : Choice X 1) : trI C 1 = fun _ => Matrix.of.symm 1 := by
  funext τ
  show Matrix.of.symm (C.Qi τ * Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) (vOf X τ)) * C.Q τ) = Matrix.of.symm 1
  have hu : Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) (vOf X τ)) = 1 := rfl
  rw [hu, Matrix.mul_one, (C.isT τ).1]

theorem trI_mul {D : D7} {X : HidaSetting D} (C : Choice X 1) (s t : X.B.I.Ginf) :
    trI C (s * t) = GlobalTheory.DegVol.mulP (trI C s) (trI C t) := by
  funext τ
  have h2 := (C.isT τ).2.1
  have e : C.Qi τ * Formalism.MainNotions.S.uMat ((s * t) (vOf X τ)) * C.Q τ =
      (C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ) * (C.Qi τ * Formalism.MainNotions.S.uMat (t (vOf X τ)) * C.Q τ) := by
    have : Formalism.MainNotions.S.uMat ((s * t) (vOf X τ)) = Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (t (vOf X τ)) := by
      simp [Formalism.MainNotions.S.uMat]
    rw [this]
    calc C.Qi τ * (Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (t (vOf X τ))) * C.Q τ
        = C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * (C.Q τ * C.Qi τ) * Formalism.MainNotions.S.uMat (t (vOf X τ)) * C.Q τ := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  simp only [trI, GlobalTheory.DegVol.mulP, Formalism.QuantumDeterminants.lmulM, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply]
  rw [e]
  rfl

theorem trI_inv {D : D7} {X : HidaSetting D} (C : Choice X 1) (s : X.B.I.Ginf) :
    (fun τ => Matrix.of.symm (Matrix.of (trI C s τ))⁻¹) = trI C s⁻¹ := by
  funext τ
  have h1 := (C.isT τ).1
  have h2 := (C.isT τ).2.1
  simp only [trI, Equiv.apply_symm_apply, Formalism.L2.SG.RealObj.trG]
  congr 1
  apply Matrix.inv_eq_right_inv
  have hu : Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  calc C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ * (C.Qi τ * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) * C.Q τ)
      = C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * (C.Q τ * C.Qi τ) * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = C.Qi τ * C.Q τ := by
        rw [h2, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hu, Matrix.mul_one]
    _ = 1 := h1

theorem cov_grp : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u).Countable ∧
    (fun _ => Matrix.of.symm 1) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      GlobalTheory.DegVol.mulP m m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      (fun τ => Matrix.of.symm (Matrix.of (m τ))⁻¹) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ τ, Matrix.of (m τ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  intro D X Y u C
  have hS := Formalism.L2.SG.Pf.NOsub_coe X u Y.hK
  have mem : ∀ s, s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ s ∈ Formalism.L2.SG.Pf.NOsub X u Y.hK := by
    intro s; rw [← hS]; rfl
  refine ⟨(Formalism.L2.SG.Pf.noCount_holds X u).image _, ⟨1, (mem 1).2 (Subgroup.one_mem _), trI_one C⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨s * t, (mem _).2 (Subgroup.mul_mem _ ((mem _).1 hs) ((mem _).1 ht)), trI_mul C s t⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, (mem _).2 (Subgroup.inv_mem _ ((mem _).1 hs)), (trI_inv C s).symm⟩
  · rintro _ ⟨s, hs, rfl⟩ τ
    obtain ⟨γ, -, hγ1, hγN, -⟩ := hs
    have hN : s ∈ X.NinfU u := hγ1 ▸ hγN
    have hNv := hN (vOf X τ)
    obtain ⟨hQ1, hQ2, hH, he⟩ := C.isT τ
    simp only [trI, Equiv.apply_symm_apply, Formalism.L2.SG.RealObj.trG]
    exact mem_nset (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ) hQ1 hQ2 hH (frS D) _
      (fun a => (he a a rfl).1) _ (s (vOf X τ)).2 hNv.1.1 hNv.2

end Main

end GlobalTheory.CovGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowSameCosetScalarCorankOne
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFamCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

theorem scalar_of_same_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 ∧ (Y.tO u u').scal t t' := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsLattice D.host.E t.lam := hrow.2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh : Th t.lam (lf D (X.Fu u)) t.frame t'.frame (n * (t.lin * n' * t.lin⁻¹)) = Hp t.lam (lf D (X.Fu u)) t.frame := by
    first
    | exact _root_.GlobalTheory.DcosetCompl.th_eq_hp D t.lam (lf D (X.Fu u)) t.frame t'.frame hrow.1.1 rfl hLt.2 hLt'.2 n hn1 _ hm hfr
    | exact _root_.GlobalTheory.DcosetCompl.th_eq_hp D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  have hsc := GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh hsc
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hrow.1.1 _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  refine ⟨?_, ?_⟩
  · show s0T t t' = 1
    unfold s0T
    rw [if_pos ⟨hlam, hlam'⟩]
    exact hs0
  · show scalT t t'
    exact ⟨⟨hlam, hlam'⟩, hs0, hsc⟩

end GlobalTheory.SnFamCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledLocalDualCoeffEqGlobalCoeff
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem scaled_local_coef_eq :
    ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (a : Fin D.R.rS) (x : (VS D).V), x ∈ G.fl.X → frFac Z.δ p a.castSucc * (locH Z p).h (baseChange₂ D p x) ((A p).es a) = (D.s.atP p).ιE (G.fl.coefX x a) := by
  intro D T G Z A hA p a x hx

  have hes : ∀ b : Fin D.R.rS, frFac Z.δ p b.castSucc * (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) =
      if b = a then 1 else 0 := by
    intro b
    have h1 := (A p).h_es b a
    rw [hA p] at h1
    rw [← (locH Z p).h_smul_left]
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  have hunit : ∀ b : Fin D.R.rS, IsUnit (frFac Z.δ p b.castSucc) := by
    intro b
    have h1 := (A p).h_es b b
    rw [hA p] at h1
    rw [if_pos rfl, (locH Z p).h_smul_left] at h1
    exact isUnit_iff_exists_inv.mpr ⟨_, by simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1⟩
  have hzero : ∀ b : Fin D.R.rS, b ≠ a → (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) = 0 := by
    intro b hb
    have h1 := hes b
    rw [if_neg hb] at h1
    exact (hunit b).mul_right_eq_zero.mp h1

  have hxs : x ∈ Submodule.span D.host.E (Set.range G.fl.e) := hx
  have hexp : x = ∑ b, G.fl.coefX x b • G.fl.e b := by
    have h2 := G.fl.e_indep.linearCombination_repr ⟨x, hxs⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h2
    simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hxs]
    exact h2.symm

  have hsum : ∀ (s : Finset (Fin D.R.rS)) (v : Fin D.R.rS → Vp D p) (y : Vp D p),
      (locH Z p).h (∑ b ∈ s, v b) y = ∑ b ∈ s, (locH Z p).h (v b) y := by
    intro s v y
    induction s using Finset.induction_on with
    | empty => simpa using (locH Z p).h_zero_left y
    | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, (locH Z p).h_add_left, ih]
  have hbc : baseChange₂ D p x = ∑ b, (D.s.atP p).ιE (G.fl.coefX x b) • baseChange₂ D p (G.fl.e b) := by
    conv_lhs => rw [hexp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => baseChange_smul₂ p _ _
  rw [hbc, hsum, Finset.mul_sum, Finset.sum_eq_single a]
  · rw [(locH Z p).h_smul_left, mul_left_comm, hes a, if_pos rfl, mul_one]
  · intro b _ hb
    rw [(locH Z p).h_smul_left, hzero b hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.RowLatXS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledUnitriangularChangeEqLocalImage
section
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrCoord

theorem frFac_mul_c {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (b : Fin (D.R.rS + 1)) :
    (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) * algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) = 1 := by
  have hu : IsUnit (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
    ((G.c p).isUnit.pow _).map _
  have he : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) =
      Ring.inverse (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) := by
    rw [map_pow]
    exact congrArg (fun x => Ring.inverse (x ^ (D.R.rS - (b : ℕ)))) (c.c_eq p).symm
  rw [he]
  exact Ring.inverse_mul_cancel _ hu

theorem step {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV)
    (hm : (placesOf Z).Ext p N m) (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (v : Fin (D.R.rS + 1) → (VS D).V) (g : Fin (D.R.rS + 1) → G.V) (gl : Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ a, g a = c.e (v a))
    (hgl : ∀ a : Fin (D.R.rS + 1), algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (a : ℕ))) • gl a =
      (placesOf Z).bc p (g a))
    (hN : ∀ b, N (g b) = ∑ a, B a b • g a) (b : Fin (D.R.rS + 1)) :
    (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) = m (gl b) := by
  have h1 : c.e (∑ a, B a b • v a) = N (g b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hN b, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hg a]
  have h2 : (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) =
      frFac Z.δ p b • (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) := (c.c p).e.map_smul _ _
  have h3 : m ((placesOf Z).bc p (g b)) = (placesOf Z).bc p (N (g b)) := hm (g b)
  have h4 : m (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • gl b) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) := m.map_smul _ _
  have h5 : (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) :=
    (c.compat p _).trans ((congrArg ((placesOf Z).bc p) h1).trans
      (h3.symm.trans ((congrArg m (hgl b).symm).trans h4)))
  have h6 : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) •
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) =
      m (gl b) := by
    rw [smul_smul, frFac_mul_c c p b, one_smul]
  rw [h2, h5]
  exact h6

theorem scaled_coord : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV), (placesOf Z).Ext p N m → ∀ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0 a) b) = m ((G.S p).f b)) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0' a) b) = m ((G.S p).f' b)) := by
  intro D Z T T' F0 F0' FP G c p N m hm B
  exact ⟨fun hN b => step c p N m hm B (frame F0) G.f (G.S p).f c.f_eq (G.f_eq p) hN b,
    fun hN b => step c p N m hm B (frame F0') G.f' (G.S p).f' c.f'_eq (G.f'_eq p) hN b⟩

end GlobalTheory.FrCoord
end
end

