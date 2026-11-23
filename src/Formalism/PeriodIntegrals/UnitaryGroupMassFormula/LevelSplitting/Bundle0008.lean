module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousLevLMat
section
noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}


set_option maxHeartbeats 800000 in
theorem continuous_uT (P : Frame E M r) (a b : Fin r) :
    Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := by
  have h1 : Continuous fun g : HA (Af F) σ J => lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b)) :=
    PI.LevelKSplit.W.ExC.continuous_lin _
  have h0 : Continuous fun g : HA (Af F) σ J =>
      ((ratV (F := F) (Af F) (P.f a), lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b))) :
        (Fin M → Af F ⊗[F] E) × (Fin M → Af F ⊗[F] E)) :=
    continuous_const.prodMk h1
  have h3 := PI.VolStabSW.continuous_hR (R := Af F) σ J
  have h2 := h3.comp h0
  unfold uT
  simp only [Matrix.of_apply]
  split_ifs
  · exact h2
  · exact continuous_const
  · exact continuous_const

theorem continuous_levL_mat (T : F) (P : Frame E M r) {X : Type} [TopologicalSpace X]
    {U W : X → Matrix (Fin r) (Fin r) (Af F ⊗[F] E)}
    (hU : ∀ a b, Continuous fun x => U x a b) (hW : ∀ a b, Continuous fun x => W x a b) :
    Continuous fun x => LinearMap.toMatrix' (levL (datR (Af F) σ J P T) (U x) (W x)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [levL, map_add (f := _), map_sum, map_smul]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (hU a b).smul continuous_const)).add
    (continuous_finsetSum _ fun d _ => continuous_finsetSum _ fun b _ => (hW d b).smul continuous_const)

theorem continuous_levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : Continuous (levG (R := Af F) hσσ hJ hP) := by
  have hU : ∀ a b, Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := continuous_uT P
  have hUm : Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g :=
    continuous_pi fun a => continuous_pi fun b => hU a b
  have hIm : Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g := by
    unfold uI
    exact hUm.matrix_adjugate
  have hI : ∀ a b, Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp hIm)
  have hcI : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uI (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hI b a)
  have hcT : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uT (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hU b a)
  have hM : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)) := by
    simp only [lin_levG]
    exact continuous_levL_mat T P hU hcI
  have hMi : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)⁻¹) := by
    have e : ∀ g : HA (Af F) σ J, lin (Af F) σ J (levG hσσ hJ hP g)⁻¹ =
        levL (datR (Af F) σ J P T) (uI (Af F) σ J P g) (cj (Af F) σ (uT (Af F) σ J P g)) :=
      fun g => LinearMap.ext fun x => by rw [lin_levG_inv]
    simp only [e]
    exact continuous_levL_mat T P hI hcT
  unfold levG
  apply Continuous.subtype_mk
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hM.congr fun g => LinearMap.toMatrix'_toLin' _
  · exact hMi.congr fun g => LinearMap.toMatrix'_toLin' _

end Af

end PI.LevelKSplit.W.NCL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfSemiNHSHeisLev
section
noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]

theorem isClosed_FixXp {r : ℕ} (P : Frame E M r) :
    IsClosed (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have h : (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) =
      ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), {g | lin (Af F) σ J g v = v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (ExC.continuous_lin _) continuous_const

theorem ncoord_of_parts (hH : HeisP F E σ M J) (hL : LevP F E σ M J) : NCoord F E σ M J := by
  intro hJ hinv r P T hP
  obtain ⟨sH, csH, cyH, hs1, hdec, hyH, hZN1, hcent, hmul, hZnorm, hconj, hZconj⟩ :=
    hH hJ hinv r P T hP
  obtain ⟨A, Lev, hAN, hAcl, cLev, hLev, hAN1, hN1norm, hAcomm⟩ := hL hJ hinv r P T hP
  have hmemW : ∀ m : LevelUnipotentSubgroup (Af F) σ J P, ∀ a, yH (Af F) σ J P m a ∈ PI.LevelKSplit.W.NC.Wp (Af F) σ J P := by
    intro m a
    obtain ⟨y, hy, -⟩ := hdec m m.2
    rw [← hy a]; exact (y a).2
  let yQ : LevelUnipotentSubgroup (Af F) σ J P → (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := fun m a =>
    ⟨yH (Af F) σ J P m a, hmemW m a⟩
  have H : CoordHyp (Nsub (Af F) σ J P) A (LevelUnipotentSubgroup (Af F) σ J P) (Zsub (Af F) σ J P) Lev sH yQ :=
    { hAN := hAN
      coordinate_level_le := inf_le_left
      hZN1 := hZN1
      cLev := cLev
      csH := csH
      cyQ := continuous_pi fun a => Continuous.subtype_mk
        ((continuous_apply a).comp (cyH.comp continuous_subtype_val)) _
      lev_mem := fun n hn => (hLev n hn).1
      lev_rest := fun n hn => (hLev n hn).2
      triv := hAN1
      norm1 := hN1norm
      sH_mem := hs1
      dec := fun m => by
        obtain ⟨y, hy, hz⟩ := hdec m m.2
        have : yQ m = y := funext fun a => Subtype.ext (hy a).symm
        rw [this]; exact hz
      yQ_sH := fun y z hz => funext fun a => Subtype.ext (hyH y z hz a)
      cent := hcent
      mul := hmul }
  refine ⟨A, Zsub (Af F) σ J P, cHomeo H, hAcl, ?_, fun n0 => coord_skew H n0, ?_⟩
  · show IsClosed ((Nsub (Af F) σ J P ⊓ FixXp (Af F) σ J P : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J))
    rw [Subgroup.coe_inf]
    exact (ExC.isClosed_Nsub hJ hinv P T hP).inter (isClosed_FixXp P)
  · intro h hh u y z
    obtain ⟨y', hy', hc⟩ := hconj h hh y
    refine ⟨y', hy', ?_⟩
    rw [cHomeo_apply, cHomeo_apply]
    have hu : h * (u : HA (Af F) σ J) * h⁻¹ = u := by rw [hAcomm h hh u u.2]; group
    have hz : h * (z : HA (Af F) σ J) * h⁻¹ = z := hZconj h hh z z.2
    calc h * ((u : HA (Af F) σ J) * sH y * (z : HA (Af F) σ J)) * h⁻¹
        = (h * u * h⁻¹) * (h * sH y * h⁻¹) * (h * z * h⁻¹) := by group
      _ = u * sH y' * z := by rw [hu, hc, hz]

end Ext

theorem ncoordAll_of (hH : HeisPAll) (hL : LevPAll) : NCoordAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact ncoord_of_parts (hH F E σ hσ M J hJ) (hL F E σ hσ M J hJ)

theorem levelSAll_of_semiNHS_heis_lev (hS : PI.LevelKSplit.W.ExS.SemiNHSAll) (hH : HeisPAll) (hL : LevPAll)
    (hV : PI.LevelKSplit.W.CD.ModVAll) (hA : NCAsmAll) : PI.LevelKSplit.LevelSAll :=
  levelSAll_of_parts hS (ncoordAll_of hH hL) hV hA

end PI.LevelKSplit.W.NC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ModulusAllExtensions
section
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem modVAll_of_vmod (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro _ _ g μ hμ
  exact pres_snd (InfiniteAdeleRing F) (Af F) σ J
    (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ

theorem modulus_all_extensions : PI.LevelKSplit.W.CD.ModVAll :=
  modVAll_of_vmod PI.VolSemiDirect.W.Cj.unipotent_modulus_holds

end PI.LevelKSplit.W.MVA
end
end

