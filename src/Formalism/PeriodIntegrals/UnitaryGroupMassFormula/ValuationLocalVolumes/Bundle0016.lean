module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AugTCastSucc
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def augT {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) : TupV (E := E) v n (a + 1) :=
  Fin.snoc (α := fun _ => Fin n → Fv F v ⊗[F] E) X w

theorem augT_castSucc {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) (i : Fin a) :
    augT v X w i.castSucc = X i := by
  simp [augT]

def IsoExt (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w : Fin n → Fv F v ⊗[F] E, IsPrim v Λ (augT v X w) ∧ gramR (Fv F v) σ J (augT v X w) = T

theorem extP_of (a : ℕ) (Y : TupV (E := E) v n a) (hn : a + 1 ≤ n) (hI : IsoExt σ J ψ v Λ a Y) :
    ExtP σ J ψ v Λ a Y := by
  intro h hG
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hU : UnitV σ J ψ v Λ :=
    unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  obtain ⟨T, hTu, hext⟩ := hI hG
  obtain ⟨hS, hL, hSD, hUn, -, hP⟩ := hG
  obtain ⟨wY, hPY, hgY⟩ := hext Y hP rfl
  have hGY : GoodY σ J ψ v Λ (a + 1) (augT v Y wY) := ⟨hS, hL, hSD, hUn, hn, hPY, by rw [hgY]; exact hTu⟩
  have hE := extOrth_of σ J ψ v Λ (a + 1) (augT v Y wY) (oSub (E := E) v) (oSmul v Λ)
    (orthoB_of σ J ψ v Λ (a + 1) (augT v Y wY) hU)
  have hT : IsUnit (gramR (Fv F v) σ J (augT v Y wY)).det := by
    obtain ⟨u, -, -, hu⟩ := hTu
    rw [hgY]
    exact ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  refine ⟨gT v hn (gramR (Fv F v) σ J (augT v Y wY)), fun X hX hXY => ?_⟩
  obtain ⟨wX, hPX, hgX⟩ := hext X hX hXY
  obtain ⟨Z, hZb, hZe, hZg⟩ := hE hn hGY (augT v X wX) hPX.1 (by rw [hgX, hgY])
  refine ⟨Z, hZb, fun i => ?_, hZg, isUnit_det_colM σ J v hn _ hT Z hZg⟩
  have e1 : eSp h (Sum.inl i) = eSp hn (Sum.inl i.castSucc) := by
    apply Fin.ext
    simp [eSp]
  rw [e1, hZe i.castSucc, augT_castSucc]

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IotaAlgInj
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

def OmVDdTr : Prop :=
  ∀ d : 𝓞 D.host.F, d ∈ differentIdeal ℤ (𝓞 D.host.F) ↔
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)

theorem iota_alg_inj : Function.Injective (fun x : X.B.I.F => X.ιE (algebraMap X.B.I.F X.B.I.E x)) :=
  X.ιE.injective.comp (algebraMap X.B.I.F X.B.I.E).injective

theorem pre_int (d : 𝓞 D.host.F) : ∃ x : 𝓞 X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  obtain ⟨a, ha⟩ := (X.ιE_F ((d : D.host.F) : D.host.E)).1 (d : D.host.F).2
  set f : X.B.I.F →+* D.host.E := (X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E) with hf
  have hd : IsIntegral ℤ (((d : D.host.F) : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe d).map ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom
  have ha' : f a = ((d : D.host.F) : D.host.E) := ha
  rw [← ha'] at hd
  have hai : IsIntegral ℤ a := (isIntegral_algHom_iff f.toIntAlgHom (iota_alg_inj X)).1 hd
  exact ⟨⟨a, (mem_integralClosure_iff ℤ _).2 hai⟩, ha⟩

theorem pow_tr (hT : OmVDdTr X) (k : ℕ) (d : 𝓞 D.host.F) (hd : d ∈ differentIdeal ℤ (𝓞 D.host.F) ^ k) :
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ k ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  induction k generalizing d with
  | zero =>
    obtain ⟨x, hx⟩ := pre_int X d
    exact ⟨x, by simp, hx⟩
  | succ k ih =>
    rw [pow_succ'] at hd
    refine Submodule.mul_induction_on
      (C := fun d : 𝓞 D.host.F => ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ (k + 1) ∧
        X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)) hd ?_ ?_
    · intro a ha b hb
      obtain ⟨x1, hx1, e1⟩ := (hT a).1 ha
      obtain ⟨x2, hx2, e2⟩ := ih b hb
      refine ⟨x1 * x2, by rw [pow_succ']; exact Submodule.mul_mem_mul hx1 hx2, ?_⟩
      have : ((x1 * x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) * (x2 : X.B.I.F) := rfl
      rw [this, map_mul, map_mul, e1, e2]; rfl
    · rintro a b ⟨x1, hx1, e1⟩ ⟨x2, hx2, e2⟩
      refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, ?_⟩
      have : ((x1 + x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) + (x2 : X.B.I.F) := rfl
      rw [this, map_add (f := _), map_add (f := _), e1, e2]; rfl

def Qi (v : PlX X) (c : Fv X.B.I.F v) : Ideal (𝓞 D.host.E) where
  carrier := {i | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (i : D.host.E)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((0 : 𝓞 D.host.E) : D.host.E)) ∈
      OEv (E := X.B.I.E) v
    simp only [map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro i j hi hj
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((i : D.host.E) + (j : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_add (f := _), map_add (f := _), mul_add]; exact Submodule.add_mem _ hi hj
  smul_mem' := by
    intro o i hi
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((o : D.host.E) * (i : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hi

theorem alg_int_mem (v : PlX X) (c : Fv X.B.I.F v) (hc : Valued.v c ≤ 1) :
    algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c ∈ OEv (E := X.B.I.E) v := by
  have e : algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c =
      (⟨c, hc⟩ : v.adicCompletionIntegers X.B.I.F) • (1 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e]; exact Submodule.smul_mem _ _ (one_mem_oev v)

theorem ddS_pow (k : ℕ) : ddS D ^ k = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
    (differentIdeal ℤ (𝓞 D.host.F) ^ k) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [Ideal.map_pow, FractionalIdeal.coeIdeal_pow]; rfl

theorem dd1 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ ddS D ^ k) :
    sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  rw [ddS_pow, FractionalIdeal.mem_coeIdeal] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F) ^ k) ≤
      Qi X v ((dV v)⁻¹ ^ k) := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    obtain ⟨x, hx, ex⟩ := pow_tr X hT k d hd
    show sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (X.ιE.symm ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E)) ∈ OEv (E := X.B.I.E) v
    have e1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E) = ((d : D.host.F) : D.host.E) := rfl
    rw [e1, ← ex, RingEquiv.symm_apply_apply, ← alg_alg]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) _ * _ ∈ _
    rw [← map_mul]
    refine alg_int_mem X v _ ?_
    rw [map_mul]
    show Valued.v ((dV v)⁻¹ ^ k) * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F)) ≤ 1
    rw [map_pow, map_inv₀]
    have h1 := val_pow_le v k x hx
    have h0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
    calc (Valued.v (dV v))⁻¹ ^ k * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F))
        ≤ (Valued.v (dV v))⁻¹ ^ k * Valued.v (dV v) ^ k := mul_le_mul' le_rfl h1
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  exact hle hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfDdX
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVSD_holds : OmVSD X := omVSD_of X (omVSDBwd_holds X)

theorem omVPrim_of_dd (hD : OmVDdLoc X) : OmVPrim X u' :=
  omVPrim_of X u' (omVMem_of X u' (omVMemEF_of X u' hD)) (omVZPrim_holds X u')

theorem omVSD_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVSD X := omVSD_holds X

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ThetaExists
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

section Box

variable (r : ℕ)

def pSet (g : ℕ) (p : Fin (r + 1) × Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then {y | y * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
  else if p.1 = p.2 then
    {y | y ∈ OEv (E := E) v ∧ (y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
  else OEv (E := E) v

theorem famL_image
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (p : Fin (r + 1) × Fin (r + 1)) (y : Fv F v ⊗[F] E) :
    y ∈ famL v r (g : Fv F v) θ p '' OEv (E := E) v ↔ y ∈ pSet σ v r g p := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  unfold famL pSet
  split_ifs with h1 h2
  · simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← VolTU.sc_mul_eq_smul, mul_comm, ← mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ hgv, VolTU.sc_one,
        one_mul]
      exact hz
    · intro h
      refine ⟨y * sc (E := E) v (g : Fv F v)⁻¹, h, ?_⟩
      rw [← VolTU.sc_mul_eq_smul, mul_comm, mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ hgv, VolTU.sc_one,
        mul_one]
  · exact mem_aL_image v σ htr hg0 hθO hθ y
  · simp

theorem box_meas (hfin : Module.finrank F E = 2)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) {θ Δ : Fv F v ⊗[F] E}
    (hθO : θ ∈ OEv (E := E) v) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0) (hΔ0 : Δ ≠ 0)
    (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1) :
    μ {Y | ∀ p, Y p ∈ pSet σ v r g p} = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹ := by
  obtain ⟨hD, hA⟩ := absV_det_bigL v r hfin hg0 hg θ Δ hθ hΔ hΔ0
  have himg : bigL v r (g : Fv F v) θ '' VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) =
      {Y | ∀ p, Y p ∈ pSet σ v r g p} := by
    ext Y
    simp only [Set.mem_image, Set.mem_setOf_eq, VolTO]
    constructor
    · rintro ⟨Z, hZ, rfl⟩ p
      exact (famL_image σ v r htr hg0 hθO hθ p _).1 ⟨Z p, hZ p, rfl⟩
    · intro h
      have : ∀ p, ∃ z, z ∈ OEv (E := E) v ∧ famL v r (g : Fv F v) θ p z = Y p := fun p =>
        (famL_image σ v r htr hg0 hθO hθ p _).2 (h p)
      choose Z hZ using this
      exact ⟨Z, fun p => (hZ p).1, funext fun p => (hZ p).2⟩
  have hgpos : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero hg0
  rw [← himg, meas_image v _ μ _ hD _ (VolUL.volTO_meas v _), hK, mul_one, hA,
    ENNReal.ofReal_pow (inv_nonneg.2 hgpos.le), ENNReal.ofReal_inv_of_pos hgpos, ENNReal.ofReal_natCast,
    ENNReal.inv_pow]

theorem diag_key
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w)
    {θ : Fv F v ⊗[F] E} (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (c y : Fv F v ⊗[F] E)
    (hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c = c) :
    (y - c * θ) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (y - c * θ) = y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ y - c := by
  have h1 : θ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ = 1 := by rw [← htr, hθ, map_one]
  rw [map_sub, map_mul, hc]
  linear_combination (-c) * h1

def ctr (θ : Fv F v ⊗[F] E) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (p : Fin (r + 1) × Fin (r + 1)) : Fv F v ⊗[F] E :=
  if p.1 < p.2 then c p.1 p.2 else if p.1 = p.2 then c p.1 p.2 * θ else 0

theorem hermBox_eq
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    VolUHm.hermBox σ v g r c =
      {Y | (fun p => Y p - ctr v r θ c p) ∈ {Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E |
        ∀ p, Y p ∈ pSet σ v r g p}} := by
  have hgO : sc (E := E) v (g : Fv F v) ∈ OEv (E := E) v := VolUTr.TrW.alg_mem v (VolTU.natCast_memO v g)
  ext Y
  simp only [VolUHm.hermBox, Set.mem_setOf_eq]
  constructor
  · intro h p
    obtain ⟨i, j⟩ := p
    obtain ⟨hO, hup, hdg⟩ := h i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [ctr, pSet, if_pos hij, Set.mem_setOf_eq]
      exact hup hij
    · subst hij
      simp only [ctr, pSet, lt_irrefl, if_false, if_true, Set.mem_setOf_eq]
      refine ⟨Submodule.sub_mem _ hO (VolUTr.TrW.mul_mem v (hc.2 i i) hθO), ?_⟩
      rw [diag_key σ v htr hθ _ _ (hc.1 i i).symm]
      exact hdg rfl
    · have h1 : ¬ i < j := not_lt.2 hij.le
      have h2 : i ≠ j := hij.ne'
      simp only [ctr, pSet, if_neg h1, if_neg h2, sub_zero]
      exact hO
  · intro h i j
    have hp := h (i, j)
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [ctr, pSet, if_pos hij, Set.mem_setOf_eq] at hp
      have hO : Y (i, j) ∈ OEv (E := E) v := by
        have e : Y (i, j) = sc (E := E) v (g : Fv F v) * ((Y (i, j) - c i j) * sc (E := E) v (g : Fv F v)⁻¹) +
            c i j := by
          rw [mul_comm, mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ (VolTU.natCast_ne_zero v hg0), VolTU.sc_one,
            mul_one, sub_add_cancel]
        rw [e]
        exact Submodule.add_mem _ (VolUTr.TrW.mul_mem v hgO hp) (hc.2 i j)
      exact ⟨hO, fun _ => hp, fun h => absurd h hij.ne⟩
    · subst hij
      simp only [ctr, pSet, lt_irrefl, if_false, if_true, Set.mem_setOf_eq] at hp
      have hO : Y (i, i) ∈ OEv (E := E) v := by
        rw [← sub_add_cancel (Y (i, i)) (c i i * θ)]
        exact Submodule.add_mem _ hp.1 (VolUTr.TrW.mul_mem v (hc.2 i i) hθO)
      refine ⟨hO, fun h => absurd h (lt_irrefl _), fun _ => ?_⟩
      rw [← diag_key σ v htr hθ _ _ (hc.1 i i).symm]
      exact hp.2
    · have h1 : ¬ i < j := not_lt.2 hij.le
      have h2 : i ≠ j := hij.ne'
      simp only [ctr, pSet, if_neg h1, if_neg h2, sub_zero] at hp
      exact ⟨hp, fun h => absurd h h1, fun h => absurd h h2⟩

theorem hermBox_meas (hfin : Module.finrank F E = 2)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) {θ Δ : Fv F v ⊗[F] E}
    (hθO : θ ∈ OEv (E := E) v) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0) (hΔ0 : Δ ≠ 0)
    (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    μ (VolUHm.hermBox σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹ := by
  rw [hermBox_eq σ v r htr hg0 hθO hθ c hc, VolUH.sub_pre v _ μ,
    box_meas σ v r hfin htr hg0 hg hθO hθ hΔ hΔ0 μ hK]

end Box

theorem theta_exists (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x) (hfin : Module.finrank F E = 2)
    (a t : 𝓞 E) (ht : σ (a : E) = (t : E)) (e : 𝓞 F)
    (he : ((a : E) - t) ^ 2 = algebraMap F E (e : F)) (hev : e ∉ v.asIdeal) :
    ∃ θ Δ : Fv F v ⊗[F] E, θ ∈ OEv (E := E) v ∧ Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1 ∧
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0 ∧ Δ ≠ 0 := by
  have hst : σ (t : E) = a := by rw [← ht, hinv]
  have hTa : Algebra.trace F E ((a : E) - t) = 0 := by
    apply (algebraMap F E).injective
    rw [VolUTr.TrW.trace_eq_add σ hinv hnt hfin, map_sub, ht, hst, map_zero]
    ring
  have hTb : Algebra.trace F E ((a : E) * ((a : E) - t)) = e := by
    apply (algebraMap F E).injective
    rw [VolUTr.TrW.trace_eq_add σ hinv hnt hfin, map_mul, map_sub, ht, hst, ← he]
    ring
  set ev := algebraMap F (Fv F v) (e : F) with hevdef
  have hval : Valued.v ev = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F e)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hev] at h
    exact h
  have he0 : ev ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  have hinvm : ev⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hθ1 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
      (sc (E := E) v ev⁻¹ * inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t))) = 1 := by
    rw [VolUTr.TrW.sc_eq, ← Algebra.smul_def, map_smul, PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR, hTb, smul_eq_mul,
      inv_mul_cancel₀ he0]
  refine ⟨sc (E := E) v ev⁻¹ * inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t)),
    inclR (F := F) (Fv F v) ((a : E) - t), ?_, hθ1, ?_, ?_⟩
  · refine VolUTr.TrW.mul_mem v (VolUTr.TrW.alg_mem v hinvm) ?_
    have e1 : (((a * (a - t) : 𝓞 E)) : E) = (a : E) * ((a : E) - t) := by push_cast; ring
    rw [← e1]
    exact VolUTr.TrW.inclR_mem' (E := E) v (a * (a - t))
  · rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR, hTa, map_zero]
  · intro h0
    rw [show inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t)) =
        inclR (F := F) (Fv F v) (a : E) * inclR (F := F) (Fv F v) ((a : E) - t) from map_mul _ _ _, h0,
      mul_zero, mul_zero, map_zero] at hθ1
    exact zero_ne_one hθ1

end Formalism.L2.SG.Pf.NcVal.VolV
end
end

