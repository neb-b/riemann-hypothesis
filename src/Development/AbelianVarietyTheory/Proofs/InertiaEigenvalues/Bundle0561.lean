module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNatural
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Natural

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem homW_inclL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (c : ι → OA l O) :
    homW t ϖ F (inclL t ϖ P c) = inclL t ϖ Q (((homMat t ϖ F).map (frobOA l O)) *ᵥ c) := by
  rw [homW_apply, inclL_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, inclL_apply]
  have hM : ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) =
      ((homMat t ϖ F).map (frobOA l O)).map (inclO l O) := by
    ext i j; simp [frobOW_inclO]
  rw [hM]
  congr 1
  funext i
  exact (RingHom.map_mulVec (inclO l O).toRingHom _ _ i).symm


omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem map_id_smul {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}
    (g : ↥T.L.T →ₗ[O] ↥T'.L.T) (r : OB l O) (x : TW (OB l O) T) :
    TensorProduct.map LinearMap.id g (r • x) = r • TensorProduct.map LinearMap.id g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem toBcris_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (m : P.MMl)
    (m' : Q.MMl) (hm : m'.1 = F.app m.1) :
    toBcris t ϖ Q m' = (((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ toBcris t ϖ P m := by
  have hmat : ∀ τ, Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := fun τ => by
    calc Q.mxInv τ * F.mat τ = Q.mxInv τ * F.mat τ * (P.mx τ * P.mxInv τ) := by
          rw [P.mx_mul_mxInv, Matrix.mul_one]
      _ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by simp only [Matrix.mul_assoc]
      _ = Q.mxInv τ * Q.mx τ * (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
          rw [F.comm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Q.mxInv_mul_mx, Matrix.one_mul]
  have hA : ∀ (g : ZMod a → A O K) (h : ∀ τ, (g τ : K⟦X⟧) ∈ invL l (S O K e)),
      ϖ.iB t K (fun τ => ⟨(g τ : K⟦X⟧), h τ⟩) = toB l O (ϖ.iTot t K g) := fun g h =>
    (ϖ.iB_of_mem t K (fun τ => ⟨g τ, A_le_S l e (g τ).2⟩)).trans
      (congrArg (toOB l O) (ϖ.iC_of_mem t K g))
  funext i
  rw [toBcris_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.map_apply, toBcris_apply, homMat, Matrix.of_apply, ← PiSys.iTot_frob]
  trans ∑ j, ϖ.iB t K (fun τ => ⟨(frobAc l (fun τ => ⟨F.mat τ i j, F.mem τ i j⟩) τ : K⟦X⟧),
      le_away _ _ (A_le_S l e (Subtype.prop _))⟩) * ϖ.iB t K (GlobalTheory.BKReal.coordL P (invL l (S O K e)) m j)
  swap
  · exact Finset.sum_congr rfl fun j _ => by rw [hA]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  have h1 := congrFun (congrArg (· *ᵥ (m.1 τ)) (hmat τ)) i
  simp only [← Matrix.mulVec_mulVec] at h1
  simp only [Finset.sum_apply, Pi.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
  change (Q.mxInv τ *ᵥ m'.1 τ) i = ∑ j, frob K l (F.mat (τ - 1) i j) * (P.mxInv τ *ᵥ m.1 τ) j
  rw [hm, BK.Hom.app_apply, h1]
  rfl

variable [TameDescentExponentData K l e a]

theorem jB_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) (v : ι → OB l O) :
    jB' ((((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ v) =
      TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB v) := by
  set Φ := TensorProduct.map (LinearMap.id : OB l O →ₗ[O] OB l O) ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  set H := (homMat t ϖ F).map (frobOA l O) with hH
  let Pr : (ι → OB l O) → Prop := fun v => jB' (H.map (toB l O) *ᵥ v) = Φ (jB v)
  have hsm : ∀ (r : OB l O) v, Pr (r • v) ↔ r • jB' (H.map (toB l O) *ᵥ v) = r • Φ (jB v) := by
    intro r v
    change jB' (H.map (toB l O) *ᵥ (r • v)) = Φ (jB (r • v)) ↔ _
    rw [Matrix.mulVec_smul, map_smul, map_smul, hΦ, map_id_smul]
  have hcancel : ∀ (r : OB l O) v, IsUnit r → Pr (r • v) → Pr v := fun r v hr h =>
    (hr.smul_left_cancel).1 ((hsm r v).1 h)
  have hofT : ∀ x : ↥T.L.T, Pr (jB.symm ((1 : OB l O) ⊗ₜ[O] x)) := by
    intro x
    obtain ⟨m, c, hu, hc, hb⟩ := ((_root_.GlobalTheory.CrisComparison.main l a e O K t ϖ ι P T I).2 jB hB).2.2.2.1 x
    obtain ⟨m', c', hu', hc', hb'⟩ :=
      ((_root_.GlobalTheory.CrisComparison.main l a e O K t ϖ κ Q T' I').2 jB' hB').2.2.2.1 ⟨f.f x, f.T_le _ x.2⟩
    refine hcancel (toB l O m) _ hu ?_
    have e1 : toB l O m • jB.symm ((1 : OB l O) ⊗ₜ[O] x) = fun i => toB l O (c i) := by
      rw [← map_smul, hb, LinearEquiv.symm_apply_apply]
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [e1]
    have e2 : (H.map (toB l O) *ᵥ fun i => toB l O (c i)) = fun i => toB l O ((H *ᵥ c) i) :=
      funext fun i => (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm
    have hc2 : inclO l O m • I'.ofT ⟨f.f x, f.T_le _ x.2⟩ = inclL t ϖ Q (H *ᵥ c) := by
      rw [← hF.homW_ofT x, ← (homW t ϖ F).map_smul, hc, homW_inclL]
    have heq : m' • (H *ᵥ c) = m • c' := by
      apply inclL_injective t ϖ Q
      rw [inclL_smul, inclL_smul, ← hc2, ← hc', smul_comm]
    have heqB : toB l O m' • (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • fun i => toB l O (c' i) := by
      funext i
      have := congrArg (toB l O) (congrFun heq i)
      simpa [map_mul] using this
    have e3 : jB' (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • ((1 : OB l O) ⊗ₜ[O] (⟨f.f x, f.T_le _ x.2⟩ : ↥T'.L.T)) := by
      refine (hu'.smul_left_cancel).1 ?_
      rw [← map_smul, heqB, map_smul, ← hb', smul_comm]
    rw [e2, e3, ← hb, hΦ, map_id_smul]
    rfl
  obtain ⟨y, rfl⟩ := jB.symm.surjective v
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    have : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact (hsm b _).2 (by rw [hofT x])
  | add x y hx hy =>
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [map_add (f := _), Matrix.mulVec_add, map_add (f := _), map_add (f := _), map_add (f := _)]
    exact congrArg₂ (· + ·) hx hy

theorem isCrisVal_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) :
    IsCrisVal t ϖ Q jB' (homW t ϖ F w)
      (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  refine ⟨m, ((homMat t ϖ F).map (frobOA l O)) *ᵥ c, hu, ?_, ?_⟩
  · rw [← (homW t ϖ F).map_smul, hc, homW_inclL]
  · rw [← map_id_smul ((f.f.restrictScalars O).restrict f.T_le), hb, ← jB_hom t ϖ hB hB' hF]
    congr 1
    funext i
    exact (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm

end GlobalTheory.BKGal.Natural

theorem GlobalTheory.BKGal.cris_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hB κ _ _ Q T' I' jB' f F hB' hF
  refine ⟨fun m m' hm => ?_, fun w b hw => GlobalTheory.BKGal.Natural.isCrisVal_hom t ϖ hB hB' hF hw⟩
  rw [GlobalTheory.BKGal.Natural.toBcris_hom t ϖ F m m' hm]
  exact GlobalTheory.BKGal.Natural.jB_hom t ϖ hB hB' hF _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPoles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {m n : Type*} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pre_of_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (T A0 A0' : Matrix (Fin d) (Fin d) (WCb l)) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T.map (frobW l) = T * A0 → A0 * A0' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T) → Y.map (inclW l) = inclW l τ ^ N • T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → ∃ F : Pre bk N d ρ, F.T = T := by
  intro l _ K bk τ hτ N d ρ T A0 A0' Y Y' hT hA0 hA0' hφ hA hfix hY hYY'
  classical
  have htu : IsUnit (inclW l τ) := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  obtain ⟨-, hinj, -⟩ := GlobalTheory.BSP.BK.evW_isUnit_injective_dvd l K bk
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
  have hiT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  have hYm : Y.map (inclW l) = t ^ N • T := hY
  have hYY'm : Y.map (inclW l) * Y'.map (inclW l) = t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, hYY', map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  have hTY' : T * Y'.map (inclW l) = t ^ N • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [hYm, Matrix.smul_mul, show 2 * N = N + N by ring, pow_add, ← smul_smul] at hYY'm
    exact ((htu.pow N).smul_left_cancel).1 hYY'm
  have hY'm : Y'.map (inclW l) = t ^ N • T⁻¹ := by
    calc Y'.map (inclW l) = T⁻¹ * (T * Y'.map (inclW l)) := by rw [← Matrix.mul_assoc, hTi, Matrix.one_mul]
      _ = t ^ N • T⁻¹ := by rw [hTY', Matrix.mul_smul, Matrix.mul_one]
  have hfr : ∀ M : Matrix (Fin d) (Fin d) (Ainf l),
      (M.map WittVector.frobenius).map (inclW l) = (M.map (inclW l)).map (frobW l) := by
    intro M; ext i j; simp [GlobalTheory.Prism.frobW_inclW]
  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hfmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
    fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
  have hfsmul : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)), (c • M).map (frobW l) = frobW l c • M.map (frobW l) :=
    fun c M => map_smul_ringHom (frobW l).toRingHom c M

  have hOE : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨A, hAm⟩ := GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0) (Y' * Y.map WittVector.frobenius)
    (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0 i j)) (by
      rw [Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, hφ, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hTi,
        Matrix.one_mul, smul_smul, smul_smul]
      rw [← ht]; exact congrArg (· • A0) (by ring))
  have hTf : (T⁻¹).map (frobW l) * T = A0' := by
    have h1 : (T⁻¹).map (frobW l) * T.map (frobW l) = 1 := by
      rw [← hfmul, hTi, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hφ, ← Matrix.mul_assoc] at h1
    calc (T⁻¹).map (frobW l) * T = (T⁻¹).map (frobW l) * T * (A0 * A0') := by rw [hA, Matrix.mul_one]
      _ = A0' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨A', hA'm⟩ := GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0') (Y'.map WittVector.frobenius * Y)
    (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0' i j)) (by
      rw [Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, Matrix.smul_mul, Matrix.mul_smul, hTf, smul_smul, smul_smul]
      rw [← ht]; exact congrArg (· • A0') (by ring))
  refine ⟨{ T := T, unit := hT, A := A, A' := A', A_mul := ?_, φ := ?_, fix := hfix }, rfl⟩
  · refine Matrix.map_injective hinj (?_ : (A * A').map bk.evW = (bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.evW)
    rw [Matrix.map_mul, hAm, hA'm, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
      Matrix.mul_smul, hA, smul_smul, map_pow, ← pow_add]
    rw [← he, two_mul]
  · rw [hAm, hφ, Matrix.mul_smul]

end GlobalTheory.BKLim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentUnitLatticeDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.UnitDatum


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (Pk : Pack a ϖ η H (unitLat (Gl l) : QLat LL)), ∃ (u : ME Pk.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) ∧ u.1 ∈ Pk.D.Minv ∧ Pk.D.phi u.1 = u.1 ∧ toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x := by
  intro BS l _ a e _ _ ϖ LL _ _ η H Pk
  have hx : ((1 : ↥LL.1) : (unitLat (Gl l) : QLat LL).V) ∈ (unitLat (Gl l) : QLat LL).L.T := ⟨1, by simp⟩
  let x : ↥(unitLat (Gl l) : QLat LL).L.T := ⟨(1 : ↥LL.1), hx⟩
  let x' : ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T := ⟨(1 : ↥LL.1), hx⟩
  have hTriv : IsTriv (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) := fun _ _ => rfl
  let b : Module.Basis Unit ↥(OL LL) ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T :=
    ⟨(LinearEquiv.ofInjective (Algebra.linearMap ↥(OL LL) ↥LL.1) IsUnitBall.inj).symm.trans
      (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm⟩
  have hb : b () = x' := by
    apply Subtype.ext
    change Algebra.linearMap ↥(OL LL) ↥LL.1 ((Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1)) = 1
    rw [show (Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1) = 1 from Finsupp.single_eq_same]
    simp
  have hBK := isBK_unitIdent (thetaW a LL) ϖ hTriv b
  have hBK' := Pk.isBK
  have h1 := GlobalTheory.BKReal.Full.main BS l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ Unit (Fin Pk.n)
    (unitMod l a e ↥(OL LL) ↥LL.1 Unit) Pk.D.toPhiMod
  have h2 := h1 (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) (resF (unitLat (Gl l) : QLat LL) (ϖ.field a))
    (unitIdent (thetaW a LL) ϖ _ b)
  have h3 := h2 (Pk.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
  have h4 := h3 hBK
  have h5 := h4 hBK' (latId _)
  obtain ⟨F, hF⟩ := h5
  have hev : (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ (unitMod l a e ↥(OL LL) ↥LL.1 Unit).M :=
    mem_tot.2 fun _ _ => one_mem _
  have huM : F.app (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ Pk.D.M := F.app_mem_M hev
  let u : ME Pk.D.toPhiMod := ⟨_, mem_ME_of_mem_M huM⟩
  have h0 : toW (thetaW a LL) ϖ (unitMod l a e ↥(OL LL) ↥LL.1 Unit) ⟨_, mem_ME_of_mem_M hev⟩ =
      (unitIdent (thetaW a LL) ϖ _ b).ofT x' := by
    apply (unitIdent (thetaW a LL) ϖ _ b).j.injective
    refine Eq.trans ?_ ((unitIdent (thetaW a LL) ϖ _ b).j_ofT x').symm
    rw [unitIdent_j, Fintype.sum_unique, hb]
    congr 1
    rw [toW_apply, ← map_one (ϖ.iW (thetaW a LL) ↥LL.1)]
    exact congrArg _ (funext fun _ => Subtype.ext rfl)
  have h6 := homW_toW (thetaW a LL) ϖ F ⟨_, mem_ME_of_mem_M hev⟩
  have key : toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x :=
    h6.symm.trans ((congrArg (homW (thetaW a LL) ϖ F) h0).trans (IsMapOf.homW_ofT hF x'))
  refine ⟨u, x, rfl, (Descent.mem_invOf _).2 ⟨huM, fun γ => ?_⟩, ?_, key⟩
  · obtain ⟨k, -, hk⟩ := (_root_.GlobalTheory.TameCover.main l a e ϖ LL).2.2.1 γ
    have hkG : k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
      intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
      exact k.commutes c
    have hv' : Pk.D.desc.act γ u.1 ∈ ME Pk.D.toPhiMod := mem_ME_of_mem_M (Pk.D.desc.act_mem_M γ _ huM)
    have h := Pk.R.desc ⟨k, hkG⟩ γ hk u ⟨_, hv'⟩ rfl
    have hx' : (unitLat (Gl l) : QLat LL).actT ⟨k, hkG⟩ x = x := Subtype.ext rfl
    have h10 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨_, hv'⟩ = toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h.symm.trans ((congrArg (Pk.R.I.act (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩) key).trans
        ((Pk.R.I.act_ofT (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩ x).trans ((congrArg Pk.R.I.ofT hx').trans key.symm)))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h10)
  · have h7 := toW_phi (thetaW a LL) ϖ Pk.D.toPhiMod huM
    have h8 : phiW (thetaW a LL) ϖ Pk.D.toPhiMod (Pk.R.I.ofT x) = Pk.R.I.ofT x := by
      rw [← mem_Treal, ← Pk.R.I.range_ofT]
      exact LinearMap.mem_range_self Pk.R.I.ofT x
    have h9 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨Pk.D.phi u.1, mem_ME_of_mem_L (Pk.D.phi_mem_L huM)⟩ =
        toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h7.trans ((congrArg (phiW (thetaW a LL) ϖ Pk.D.toPhiMod) key).trans (h8.trans key.symm))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h9)

end GlobalTheory.BKGal.UnitDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemLatticeOnKummerTowerGalois
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleKinf

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G] {T : LocLat G ℚ_[l] K O}

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  simp [map_mul]

theorem isCrisVal_add (P : PhiMod O K l e a ι) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T)
    {w w' : ι → OW l O} {b b' : TW (OB l O) T} (h : IsCrisVal t ϖ P jB w b)
    (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, hw, hb⟩ := h
  obtain ⟨m', c', hm', hw', hb'⟩ := h'
  refine ⟨m * m', m' • c + m • c', ?_, ?_, ?_⟩
  · rw [map_mul]; exact hm.mul hm'
  · rw [map_add (f := _), inclL_smul, inclL_smul, ← hw, ← hw', smul_smul, smul_smul, smul_add, map_mul,
      mul_comm (inclO l O m) (inclO l O m')]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      ext1 i
      simp [map_add (f := _), map_mul]
    rw [e1, map_add (f := _), map_smul, map_smul, ← hb, ← hb', map_mul, smul_add, smul_smul, smul_smul,
      mul_comm (toB l O m') (toB l O m)]

theorem cocycle_mem_lattice_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hpot g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, hσ, -, hval, rfl⟩ := hpot
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.KinfCover.exists_covers_of_mem_GKinf l a e O K t ϖ (sQ l g) hg

  have hσfix : actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) :=
    _root_.GlobalTheory.TameAct.main l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc g γ hγ σ σ (hσ γ).symm

  have hyfix : R.I.act (sQ l g) g (toW t ϖ D.toPhiMod ⟨y, hy⟩) = toW t ϖ D.toPhiMod ⟨y, hy⟩ :=
    R.desc g γ hγ ⟨y, hy⟩ ⟨y, hy⟩ (((Descent.mem_invOf _).1 hyY).2 γ).symm

  set w := R.I.act (sQ l g) g m₀ - m₀ with hw
  have hφw : phiW t ϖ D.toPhiMod w = w := by
    have h1 : phiW t ϖ D.toPhiMod w - w =
        R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀ - m₀) - (phiW t ϖ D.toPhiMod m₀ - m₀) := by
      rw [hw, map_sub, map_sub, R.I.act_phiW]; abel
    rw [hm₀, hyfix, sub_self] at h1
    exact sub_eq_zero.1 h1
  obtain ⟨x, hx⟩ : w ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hφw
  obtain ⟨-, huniq, -, hofT, hgal⟩ :=
    (_root_.GlobalTheory.CrisComparison.main l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp
  have h2 : IsCrisVal t ϖ D.toPhiMod R.jB (R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀))
      (actB (sQ l) T g b₀) := hgal g (R.stable g) _ _ hval
  have h3 : R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀) = phiW t ϖ D.toPhiMod m₀ + R.I.ofT x := by
    rw [R.I.act_phiW, hx, ← hφw, hw, map_sub]; abel
  rw [h3] at h2
  have h4 := huniq _ _ _ h2 (GlobalTheory.CocycleKinf.isCrisVal_add D.toPhiMod R.jB hval (hofT x))
  refine ⟨-x, ?_⟩
  rw [map_sub, hσfix, h4, tmul_neg]
  abel

end GlobalTheory.CocycleKinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumnsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_rational_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | exact @GlobalTheory.BSP.FrobRational.main | exact GlobalTheory.BSP.FrobRational.main | (intros; apply GlobalTheory.BSP.FrobRational.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeRationalInColumnsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BSP.rational_in_columns | exact GlobalTheory.BSP.rational_in_columns | (intros; apply GlobalTheory.BSP.rational_in_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  first | exact @GlobalTheory.ExtLatCrys.isCrys_resF_extLat | exact GlobalTheory.ExtLatCrys.isCrys_resF_extLat | (intros; apply GlobalTheory.ExtLatCrys.isCrys_resF_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDual
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RegularRing

theorem quot_tensor_dual_crys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    GlobalTheory.Per.IsStd P AI → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys l P ∧ GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys l P ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys l P := by
  intro l _ P AI hs
  have h := fontaineFormalism_of_regular l P AI
    (fun C => ⟨_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C, _root_.GlobalTheory.MemLoc.regular_of_tensorInj l C (_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C)⟩) hs
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

end GlobalTheory.RegularRing
end

