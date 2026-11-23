module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorSecond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.YvMemUUE

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfE
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohIntPf

variable {D : Formalism.BasicNotions.D7}

theorem exists_den {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x

variable (Zd : LocDat D)

theorem bcP_mem_cof {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    {p : PlF D | baseChange₂ D p x ∉ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨d, hd, hdx⟩ := exists_den hΛ x
  have hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnd
  apply hp
  have := p.isPrime
  letI := hΛ
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance)]
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩

theorem scal_mem {p : PlF D} (hs : (Zd.M p).split = none)
    (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (b : Fin (D.R.rS + 1)) : TermLoc.sgnP' D p b * frFac Zd.δ p b ∈ (D.s.atP p).O := by
  have hs' : (D.s.atP p).split = none := by
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hs] at hA
    cases h2 : (D.s.atP p).split with
    | none => rfl
    | some sg =>
      rw [h2] at hA
      exact (hA : False).elim
  refine Subring.mul_mem _ ?_ ?_
  · unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · rw [Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b]
    set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ *
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw
    have hwO : w ∈ (D.s.atP p).O :=
      Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2
    have hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1
      rw [hw]
      have hδ0 : Zd.δ p ≠ 0 := (Zd.agree p).2.1
      have hu0 := Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p
      calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹))
          = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p * (Zd.δ p)⁻¹) *
            (D.s.atP p).ιE ((uP p : D.host.E) * (uP p : D.host.E)⁻¹) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [mul_inv_cancel₀ hδ0, mul_inv_cancel₀ hu0, map_one, map_one, mul_one]
    rw [Units.val_pow_eq_pow_val, hinv]
    exact Subring.pow_mem _ hwO _

end CohIntPf

open CohIntPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem cohInt_holds : CohInt Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' _
  have hΛ : Submodule.IsFullLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅
  rw [Filter.eventually_cofinite] at hgood
  refine (hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn
  obtain ⟨hg, hb⟩ := hn
  apply hp
  intro b
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.InvAlgCf
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem frFac_cf (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) := by
  rw [frFac_eq]; rfl

theorem inv_alg_cf (a : Fin (D.R.rS + 1)) :
    Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) := by
  have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) = 1 := by
    rw [← map_mul, cf_cfi, map_one]
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
  calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
      = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
        rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem lOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.lOf Zd.δ Zd.M p A B = Formalism.L2.SG.Pf.TupGlob.locL Zd p A B := by
  unfold Formalism.L2.SG.Pf.StabShape.lOf Formalism.L2.SG.Pf.TupGlob.locL
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.lL, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [frFac_cf, frFac_cf, RingHom.coe_coe, AlgEquiv.commutes, AlgEquiv.commutes, inv_alg_cf]
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.lG, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes, Prod.algebraMap_apply, map_mul, map_pow,
      map_neg, map_one, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h1 : ∀ a, cf Zd p a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (cf_cfi Zd p a)
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    ext
    all_goals (simp only [h2, div_eq_mul_inv]; try ring)

end Formalism.L2.SG.Pf.FibD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsomHTSymm
section
noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem isom_hT {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) : S.hT (γ x) (γ y) = S.hT x y := h x y

theorem mapLF_fl {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T') :
    (mapLF γ L).fl = mapFlag γ h L.fl := by
  unfold mapLF; rw [dif_pos h]

theorem mapLF_fl_z {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T') :
    (mapLF γ L).fl.z = γ L.fl.z := by
  rw [mapLF_fl h]; rfl

private theorem mapFlag_fvec' {T0 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (i : Fin (r + 1)) : (mapFlag γ h F).fvec i = γ (F.fvec i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

private theorem Zhat_mapFlag' {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    Zhat (mapFlag γ h F) (mapFlag γ h F') = Zhat F F' := by
  ext a b
  simp [Zhat, brS, mapFlag_fvec', isom_hT h]

private theorem Gflag_mapFlag {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    Gflag (mapFlag γ h F) (mapFlag γ h F') = Gflag F F' := by
  simp only [Gflag, Dl, Zhat_mapFlag']

private theorem yv_mapFlag {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    yv (mapFlag γ h F) (mapFlag γ h F') = γ (yv F F') := by
  simp only [yv, omp, Dl, Zhat_mapFlag', mapFlag_fvec']
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, mapFlag]

private theorem mapFlag_X' {T0 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) : (mapFlag γ h F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  simp only [FlagG.X, mapFlag]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

private theorem mem_Hp_iff_orthogonal {T0 T1 : E} (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T0) (F' : LFlag S r T1)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') (h : S.V) :
    h ∈ Hp Λ F F' ↔ ((∀ x ∈ F.fl.X, S.hT x h = 0) ∧ S.hT F.fl.z h = 0 ∧
      (∀ x ∈ F'.fl.X, S.hT x h = 0) ∧ S.hT F'.fl.z h = 0) := by
  constructor
  · intro hh
    exact ⟨fun x hx => hT_UUE_Hp Λ F F' hh (X_le_UUE Λ hΛ F F' hF hF' hx),
      hT_UUE_Hp Λ F F' hh (z_mem_UUE Λ hΛ.toIsLattice F F' hF hF'),
      fun x hx => hT_UUE_Hp Λ F F' hh (X'_le_UUE Λ hΛ F F' hF hF' hx),
      hT_UUE_Hp Λ F F' hh (z'_mem_UUE Λ hΛ.toIsLattice F F' hF hF')⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hU : UU Λ F F' ≤ (LinearMap.ker (S.hT.flip h)).restrictScalars
        (NumberField.RingOfIntegers E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro x hx
        simpa using h1 x hx.2
      · rw [Submodule.span_singleton_le_iff_mem, hF.2]
        simpa using h2
      · intro x hx
        simpa using h3 x hx.2
      · rw [Submodule.span_singleton_le_iff_mem, hF'.2]
        simpa using h4
    have key : UUE Λ F F' ≤ LinearMap.ker (S.hT.flip h) := by
      unfold UUE spanE
      rw [Submodule.span_le]
      intro u hu
      exact hU hu
    simp only [Hp, orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro u hu
    simpa using key hu

private theorem isLattice_sup_span_singleton (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (v : S.V) :
    Submodule.IsFullLattice E (Λ ⊔ Submodule.span (NumberField.RingOfIntegers E) {v}) := by
  let : Submodule.IsFullLattice E Λ := hΛ
  exact Submodule.IsFullLattice.of_le_of_fg E le_sup_left
    (hΛ.fg.sup (Submodule.fg_span_singleton v))

private theorem flagG_ext_of_e_eq_of_z_eq {T0 : E} (F G : FlagG S r T0) (he : F.e = G.e) (hz : F.z = G.z) :
    F = G := by
  cases F
  cases G
  simp only at he hz
  subst he
  subst hz
  rfl

theorem line_pair' (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (Fl : LFlag S r T) (L0 : LFlag S r T') (γ1 γ2 : S.V ≃ₗ[E] S.V)
    (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ2 : γ2 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ (mapLF γ1 L0)) (hL2 : IsLift Λ (mapLF γ2 L0))
    (hG1 : Gval Fl (mapLF γ1 L0) ≠ 0) (hG12 : Gval Fl (mapLF γ2 L0) = Gval Fl (mapLF γ1 L0))
    (hT' : T' ≠ 0) (hTs' : star T' = T')
    (hTh : Th Λ Fl (mapLF γ1 L0) (mapLF γ2 L0) (γ2 * γ1⁻¹) = Hp Λ Fl (mapLF γ1 L0)) :
    γ2.symm (yv (mapLF γ2 L0).fl Fl.fl) -
        (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) •
        γ1.symm (yv (mapLF γ1 L0).fl Fl.fl) ∈ L0.fl.X ∧
      (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) *
        star (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) = 1 := by
  have hδ : γ1 * γ2⁻¹ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem hγ1 (inv_mem hγ2)
  set δ := γ1 * γ2⁻¹ with hδd
  set Λ' := Λ ⊔ Submodule.span (NumberField.RingOfIntegers E) {δ Fl.fl.z} with hΛ'd
  have hΛ' : Submodule.IsFullLattice E Λ' := isLattice_sup_span_singleton Λ hΛ _
  have hle : Λ ≤ Λ' := le_sup_left
  have hL1' : IsLift Λ' (mapLF γ1 L0) := ⟨hle hL1.1, hL1.2⟩
  have hL' : IsLift Λ' Fl := ⟨hle hL.1, hL.2⟩
  have hB : IsLift Λ' (mapLF δ Fl) := by
    refine ⟨?_, ?_⟩
    · rw [mapLF_fl_z hδ]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · simp only [mapLF, dif_pos hδ]
      rw [hL.2]
      rfl
  have eF1 : (mapLF γ1 L0).fl = mapFlag γ1 hγ1 L0.fl := mapLF_fl hγ1 L0
  have eF2 : (mapLF γ2 L0).fl = mapFlag γ2 hγ2 L0.fl := mapLF_fl hγ2 L0
  have eB : (mapLF δ Fl).fl = mapFlag δ hδ Fl.fl := mapLF_fl hδ Fl
  have eflag : mapFlag γ1 hγ1 L0.fl = mapFlag δ hδ (mapFlag γ2 hγ2 L0.fl) := by
    apply flagG_ext_of_e_eq_of_z_eq
    · funext a
      simp [mapFlag, hδd]
    · simp [mapFlag, hδd]
  have hb : yv (mapLF γ1 L0).fl (mapLF δ Fl).fl = δ (yv (mapLF γ2 L0).fl Fl.fl) := by
    rw [eF1, eB, eF2, eflag, yv_mapFlag]
  have hGA : Gval (mapLF γ1 L0) Fl ≠ 0 := by
    simp only [Gval]
    rw [Gflag_swap]
    exact hG1
  have hGB : Gval (mapLF γ1 L0) (mapLF δ Fl) = Gval (mapLF γ1 L0) Fl := by
    have e1 : Gflag (mapLF γ1 L0).fl (mapLF δ Fl).fl = Gflag (mapLF γ2 L0).fl Fl.fl := by
      rw [eF1, eB, eF2, eflag, Gflag_mapFlag]
    have e2 : Gflag (mapLF γ1 L0).fl Fl.fl = Gflag Fl.fl (mapLF γ1 L0).fl := Gflag_swap _ _
    have e3 : Gflag (mapLF γ2 L0).fl Fl.fl = Gflag Fl.fl (mapLF γ2 L0).fl := Gflag_swap _ _
    show Gflag (mapLF γ1 L0).fl (mapLF δ Fl).fl = Gflag (mapLF γ1 L0).fl Fl.fl
    rw [e1, e2, e3]
    exact hG12
  have hTh' : Th Λ' (mapLF γ1 L0) Fl (mapLF δ Fl) δ = Hp Λ' (mapLF γ1 L0) Fl := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
      exact hp.1.1.1
    · intro h hh
      have hh1 := (mem_Hp_iff_orthogonal Λ' hΛ' (mapLF γ1 L0) Fl hL1' hL' h).1 hh
      have hh0' : h ∈ Hp Λ (mapLF γ1 L0) Fl := (mem_Hp_iff_orthogonal Λ hΛ (mapLF γ1 L0) Fl hL1 hL h).2 hh1
      have hh0 : h ∈ Hp Λ Fl (mapLF γ1 L0) := by
        rw [Hp_symm]
        exact hh0'
      rw [← hTh] at hh0
      obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hh0
      obtain ⟨⟨⟨hpa, hpb⟩, hpc⟩, hpd⟩ := hp
      have hp1' : p.1 = h := hp1
      have hpc' : p.1 - p.2 ∈ Fl.fl.X := hpc
      have hpd' : (γ2 * γ1⁻¹) p.1 - p.2 ∈ (mapLF γ2 L0).fl.X := hpd
      have c2 := (mem_Hp_iff_orthogonal Λ hΛ Fl (mapLF γ2 L0) hL hL2 p.2).1 hpb
      have hXF1 : (mapLF γ1 L0).fl.X = ((mapLF γ2 L0).fl.X).map (δ : S.V →ₗ[E] S.V) := by
        rw [eF1, eF2, eflag, mapFlag_X']
      have hXB : (mapLF δ Fl).fl.X = (Fl.fl.X).map (δ : S.V →ₗ[E] S.V) := by
        rw [eB, mapFlag_X']
      have hzF1 : (mapLF γ1 L0).fl.z = δ (mapLF γ2 L0).fl.z := by
        rw [mapLF_fl_z hγ1, mapLF_fl_z hγ2]
        simp [hδd]
      have hzB : (mapLF δ Fl).fl.z = δ Fl.fl.z := mapLF_fl_z hδ Fl
      refine Submodule.mem_map.2 ⟨(h, δ p.2), ⟨⟨⟨hh, ?_⟩, ?_⟩, ?_⟩, rfl⟩
      · refine (mem_Hp_iff_orthogonal Λ' hΛ' (mapLF γ1 L0) (mapLF δ Fl) hL1' hB (δ p.2)).2 ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [hXF1] at hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
          rw [show (δ : S.V →ₗ[E] S.V) y = δ y from rfl, isom_hT hδ]
          exact c2.2.2.1 y hy
        · rw [hzF1, isom_hT hδ]
          exact c2.2.2.2
        · intro x hx
          rw [hXB] at hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
          rw [show (δ : S.V →ₗ[E] S.V) y = δ y from rfl, isom_hT hδ]
          exact c2.1 y hy
        · rw [hzB, isom_hT hδ]
          exact c2.2.1
      · show h - δ p.2 ∈ Xsp (mapLF γ1 L0)
        show h - δ p.2 ∈ (mapLF γ1 L0).fl.X
        rw [hXF1]
        refine Submodule.mem_map.2 ⟨_, hpd', ?_⟩
        rw [← hp1']
        simp [hδd, map_sub]
      · show δ h - δ p.2 ∈ (mapLF δ Fl).fl.X
        rw [hXB]
        refine Submodule.mem_map.2 ⟨_, hpc', ?_⟩
        rw [← hp1']
        simp [map_sub]
  have LP := line_pair k hdim Λ' hΛ' (mapLF γ1 L0) Fl (mapLF δ Fl) δ hL1' hL' hB hGA hGB hT' hTs' hTh'
  rw [hb] at LP
  set w1 := yv (mapLF γ1 L0).fl Fl.fl with hw1
  set w2 := yv (mapLF γ2 L0).fl Fl.fl with hw2
  have hc1 : brS S (δ w2) w1 = brS S (γ2.symm w2) (γ1.symm w1) := by
    simp only [brS]
    rw [← isom_hT hγ1 (γ1.symm w1) (γ2.symm w2)]
    simp [hδd]
  have hc2 : brS S w1 w1 = brS S (γ1.symm w1) (γ1.symm w1) := by
    simp only [brS]
    rw [← isom_hT hγ1 (γ1.symm w1) (γ1.symm w1)]
    simp
  rw [hc1, hc2] at LP
  refine ⟨?_, LP.2⟩
  have hX : (mapLF γ1 L0).fl.X = L0.fl.X.map (γ1 : S.V →ₗ[E] S.V) := by
    rw [eF1, mapFlag_X']
  have h1 := LP.1
  rw [hX] at h1
  obtain ⟨a, ha, hae⟩ := Submodule.mem_map.1 h1
  convert ha using 1
  apply γ1.injective
  rw [show (γ1 : S.V →ₗ[E] S.V) a = γ1 a from rfl] at hae
  rw [hae]
  simp [hδd, map_sub, map_smul]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

