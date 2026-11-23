module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0085
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOnto

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewTies
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def ProdConvNew : Prop :=
  (∀ v, (TypAt X v → 0 < MX X u u' ψ v) ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v) ∧
  True ∧ True ∧
  Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) ∧ 0 < ∏' v : OrdX X, localVolumeUnit X ψ v.1 ∧
  Multipliable (ZZX X u u' ψ) ∧ 0 < ∏' v : PlX X, ZZX X u u' ψ v ∧
  (∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v) ∧
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1 ∧
  Multipliable (jacX X) ∧ 0 < ∏' v : PlX X, jacX X v

private theorem multipliable_and_tprod_pos_of_finite_mulSupport {ι : Type*} (f : ι → ℝ) (hpos : ∀ i, 0 < f i) (hfin : (Function.mulSupport f).Finite) :
    Multipliable f ∧ 0 < ∏' i, f i := by
  refine ⟨multipliable_of_hasFiniteMulSupport hfin, ?_⟩
  rw [tprod_eq_prod' (s := hfin.toFinset) (by simp)]
  exact Finset.prod_pos fun i _ => hpos i

theorem prodConvNew_of (h1 : VolOneAEC X u u' ψ)
    (hpos : ∀ v, 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧ 0 < jacX X v)
    (hM : ∀ v, TypAt X v → 0 < MX X u u' ψ v) (hal : ∀ v, 0 < alX X u u' v) (h3 : AlConvC X u u') :
    ProdConvNew X u u' ψ := by
  have hS : ∀ g : PlX X → ℝ, (∀ v, g v ≠ 1 → ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧
      (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)) → (Function.mulSupport g).Finite :=
    fun g hg => h1.subset fun v hv => hg v hv
  have hU : (Function.mulSupport fun v : OrdX X => localVolumeUnit X ψ v.1).Finite := by
    refine (h1.preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    intro h
    exact hv h.1
  have hZ := hS (ZZX X u u' ψ) fun v hv h => hv h.2.1
  have hP : ∀ l, (Function.mulSupport (PPX X u u' ψ l)).Finite := fun l => hS _ fun v hv h => hv (h.2.2.1 l)
  have hJ := hS (jacX X) fun v hv h => hv h.2.2.2
  have rU := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v : OrdX X => (hpos v.1).1) hU
  have rZ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.1) hZ
  have rJ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.2) hJ
  exact ⟨fun v => ⟨hM v, (hpos v).1, (hpos v).2.1, (hpos v).2.2.1, hal v⟩, trivial, trivial, rU.1, rU.2, rZ.1, rZ.2,
    fun l => multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.1 l) (hP l), h3.1, h3.2, rJ.1, rJ.2⟩

theorem prodConvNew_gen (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ)
    (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (hpos : ∀ v, (¬ TypAt X v → 0 < localVolumeUnit X ψ v) ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
      0 < jacX X v) :
    ProdConvNew X u u' ψ := by
  have hk : 1 ≤ D.R.k := Formalism.MainNotions.S.k_pos (D := D)
  refine prodConvNew_of X u u' ψ (VolOneAEC_holds (X := X) (u := u) (u' := u') (ψ := ψ) hψ hs) (fun v => ⟨?_, (hpos v).2.1,
    (hpos v).2.2.1, (hpos v).2.2.2⟩) (fun v h => (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).1)
    (fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds (X := X) (u := u) (u' := u') hk v).1)
    (AlConvC_holds (X := X) (u := u) (u' := u'))
  by_cases h : TypAt X v
  · exact (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).2
  · exact (hpos v).1 h

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanOmHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open SpanOmPf in
theorem spanOm_holds (D : Formalism.BasicNotions.D7) : SpanOm D := by
  intro T T' F F' hdet hG m hm
  set ω := Gom F.fvec F'.fvec with hω
  set Dd := GDl F.fvec F'.fvec (D.R.rS + 1) with hDd
  set Dr := GDl F.fvec F'.fvec D.R.rS with hDr
  have hD : Dd ≠ 0 := by rw [hDd, GDl_top', SpanOmPf.GZ_eq]; exact hdet
  have hG' : Dd * star Dd - T * T' * (Dr * star Dr) ≠ 0 := by
    rw [hDd, hDr, SpanOmPf.GDl_eq, SpanOmPf.GDl_eq]; exact hG
  set W0 := orth (VS D) (F.Xplus ⊔ F'.Xplus) with hW0
  set U := F'.X ⊔ W0 ⊔ Submodule.span D.host.E {F'.z, ω} with hU
  have key : ∀ u ∈ orth (VS D) U, u ∈ F'.X := by
    intro u hu
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hu
    have h1 : ∀ y ∈ F'.X, (VS D).hT y u = 0 := fun y hy =>
      hu y (Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    have h2 : ∀ w ∈ W0, (VS D).hT w u = 0 := fun w hw =>
      hu w (Submodule.mem_sup_left (Submodule.mem_sup_right hw))
    have h3 : (VS D).hT F'.z u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _)))
    have h4 : (VS D).hT ω u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hP : u ∈ F.Xplus ⊔ F'.Xplus :=
      BwdNA.mem_of_orth_orth (VS D) _ (fun w hw => by rw [SpanOmPf.hsw', h2 w hw, star_zero])
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hP
    obtain ⟨y', hy', s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hs
    have hxX : ∀ y0 ∈ F'.X, (VS D).hT y0 x = 0 := by
      intro y0 hy0
      have := h1 y0 hy0
      rw [map_add (f := _), map_add (f := _), SpanOmPf.iso_X F' hy0 hy', map_smul, SpanOmPf.isotropicSpan_orthogonal_anisotropicVector F' hy0, smul_zero, add_zero, add_zero] at this
      exact this
    obtain ⟨c, rfl⟩ := SpanOmPf.om_uniq F F' hD (by rw [← SpanOmPf.Xplus_eq]; exact hx) hxX
    have hzo : (VS D).hT F'.z ω = star Dd := by rw [SpanOmPf.hsw', SpanOmPf.omega_hermitian_z]
    have e3 : c * star Dd + β * -T' = 0 := by
      have := h3
      rw [map_add (f := _), map_add (f := _), map_smul, map_smul, hzo, SpanOmPf.z_orth_X F' hy', F'.z_norm, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have e4 : c * (-T * (Dr * star Dr)) + β * Dd = 0 := by
      have := h4
      rw [map_add (f := _), map_add (f := _), map_smul, map_smul, SpanOmPf.om_om, SpanOmPf.om_X' F F' hy', SpanOmPf.omega_hermitian_z, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have hc : c = 0 := by
      have hcG : c * (Dd * star Dd - T * T' * (Dr * star Dr)) = 0 := by
        linear_combination Dd * e3 + T' * e4
      exact (mul_eq_zero.1 hcG).resolve_right hG'
    have hβ : β = 0 := by
      rw [hc] at e4
      have : β * Dd = 0 := by linear_combination e4
      exact (mul_eq_zero.1 this).resolve_right hD
    rw [hc, hβ, zero_smul, zero_smul, add_zero, zero_add]
    exact hy'
  have hmU : m ∈ U := BwdNA.mem_of_orth_orth (VS D) U (fun u hu => by
    rw [SpanOmPf.hsw', (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm u (key u hu), star_zero])
  obtain ⟨y, hy, s, hs, rfl⟩ := Submodule.mem_sup.1 hmU
  obtain ⟨x', hx', w, hw, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hs
  exact ⟨x', hx', w, hw, a, b, by abel⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLat
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def coordX (X : MatR D) : FreeE w → D.host.E := fun q => X q.1.1 q.1.2

theorem Xmat_coordX {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : Xmat w (coordX w X) = X := by
  funext a c
  by_cases h : a = c
  · subst h; simp [Xmat, (hU a a).2 rfl]
  · simp only [Xmat, h, if_false]
    by_cases h2 : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val
    · rw [dite_eq_left h2]; rfl
    · rw [dite_eq_right h2]
      by_cases h3 : a < c
      · exact (hB a c (fun e => h2 ⟨h3, e⟩)).symm
      · exact ((hU a c).1 (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h))).symm

theorem coordX_Xmat (y : FreeE w → D.host.E) : coordX w (Xmat w y) = y := by
  funext q; exact Xmat_q w y q

theorem mem_stabInt_iff_twist (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (hodd : Odd (gS D))
    (u u' : D.what₂.Word) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔
      ∀ q, coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) q -
        τA w q (coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w)) ∈ Λq w q := by
  obtain ⟨-, hU, hB⟩ := X_of_st w hβ hb hW
  rw [mem_stabInt_iff_X δ M hA u u' w β hβ hb hW, ← Xmat_coordX w hU hB, coordX_Xmat]
  exact twistC δ M hA hodd w _

theorem exists_of_coord (y : FreeE w → D.host.E) :
    ∃ β : GLR D, IsLoUni (β : MatR D) ∧ IsUpUni (Xmat w y)⁻¹ ∧
      (β : MatR D) * ptMat w * (Xmat w y)⁻¹ = ptMat w ∧ (ptMat w)⁻¹ * (β : MatR D) * ptMat w = Xmat w y := by
  obtain ⟨hlo, hXi, hW, hdet⟩ := st_of_X w (Xmat_upU w y) (Xmat_blk w y)
  set B := ptMat w * Xmat w y * (ptMat w)⁻¹
  have hd : IsUnit B.det := by rw [hdet]; exact isUnit_one
  refine ⟨⟨B, B⁻¹, Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩, hlo, hXi, hW, ?_⟩
  have hu := ptMat_isUnit w
  show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w = Xmat w y
  rw [show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w =
      ((ptMat w)⁻¹ * ptMat w) * Xmat w y * ((ptMat w)⁻¹ * ptMat w) by simp only [Matrix.mul_assoc],
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]

theorem hpr_lt {p q : FreeE w} (h : hgt w q < hgt w p) : hpr w q < hpr w p := by
  unfold hpr; split_ifs <;> omega

theorem trunc_eq {y y' : FreeE w → D.host.E} (q : FreeE w) (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    trunc w y (hgt w q) = trunc w y' (hgt w q) := by
  funext p
  unfold trunc
  split_ifs with hp
  · exact h p (hpr_lt w hp)
  · rfl

theorem τA_lowdep (q : FreeE w) {y y' : FreeE w → D.host.E} (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    τA w q y = τA w q y' := by
  unfold τA
  by_cases h1 : selfP w q
  · simp only [h1, if_true, cf, trunc_eq w q h]
  · by_cases h2 : upperM w q
    · obtain ⟨hp1, hp2⟩ := upper_qbar w h2
      have hlt : hpr w (qbar w q) < hpr w q := by
        unfold hpr; rw [hgt_qbar]; simp only [h2, hp2, if_true, if_false]; omega
      have hc : cf w y (qbar w q) = cf w y' (qbar w q) := by
        unfold cf
        rw [trunc_eq w (qbar w q) (fun p hp => h p (lt_trans hp hlt))]
      simp only [h1, h2, if_false, if_true, h _ hlt, hc]
    · simp only [h1, h2, if_false]

end Formalism.L2.SG.Pf.StabIntLat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupAct
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupAct

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Pf.TupOrb
  Formalism.L2.SG.Pf.TupLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lift_move {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) (hu : Tu D u ≠ 0) (hu' : Tu D u' ≠ 0)
    {t : TermsOf D u' F0 Λ} {Z₁ : PairVal.MatR D} {F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (h₁ : F₁ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (r₁ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁)
    {U U' : PairVal.MatR D} (hU : IsUpUni U) (hU' : IsUpUni U') (hiU : TupGlob.IntFr U) (hiU' : TupGlob.IntFr U')
    (htie : TupGlob.TieG U U') :
    ∃ ν ∈ NLam Λ (lf D F0), ∃ m ∈ NLam Λ F₁,
      (∀ b, ν (frame (lf D F0) b) = ∑ c, U c b • frame (lf D F0) c) ∧
      (∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c) ∧
      ∃ F2 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ (U.conjTranspose * Z₁ * U'),
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F2 ∧ ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := by
  obtain ⟨p₁, e₁⟩ := r₁
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 Λ hΛ
  obtain ⟨ν, hν, hνF⟩ := TupOnto.nLamOnto_holds D u F0 Λ hΛ hu U hU hiU
  obtain ⟨m, hm, hmF⟩ := TupOnto.nLamOnto_holds D u' F₁.fl Λ (isRowLat_of_pd hΛ p₁) hu' U' hU' hiU'
  have hm' : m ∈ NLam Λ F₁ := hm
  have hmF' : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c := hmF
  have hAut : IsAutLam (VS D) Λ (ν⁻¹ * m) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_inv hν.1) hm.1
  let F2 := Formalism.L2.SG.Saturated.mapL (ν⁻¹ * m) hAut.1 F₁
  have hf2 : ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := fun b => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel Λ (lf D F0) F₁ F2 := ⟨ν⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hν, m, hm', hf2, rfl⟩
  have pd2 : PD D Λ (lf D F0) u' F2 := Formalism.L2.SG.Closed.TermStable_holds D u u' F0 Λ hΛ ⟨F₁, p₁⟩ F2 hdc
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hu'
  have hFΛ : ∀ c, frame (lf D F0) c ∈ Λ := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · rw [Formalism.L2.SG.Pf.frame_last_td]; exact hΛ.2.1.2.2.1.1
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td]; exact PI.NRL.e_mem_lam D F0 Λ hΛ a
  have hiso : ∀ x y, (VS D).hT (ν x) (ν y) = (VS D).hT x y := ((Formalism.L2.SG.Pf.isAutLam_iff Λ ν).1 hν.1).1
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F2 b) =
      (U.conjTranspose * ZhatL (lf D F0) F₁ * U') a b := fun a b => by
    rw [hf2 b]; exact zhat_lift (lf D F0) F₁ hiso hνF hmF' a b
  refine ⟨ν, hν, m, hm', hνF, hmF', F2, ⟨⟨pd2.1, pd2.2.1, ?_⟩, ?_, ?_, pd2.2.2, ?_⟩,
    ⟨pd2, (Quot.sound (show TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F₁, p₁⟩ ⟨F2, pd2⟩ from hdc)).symm.trans e₁⟩, hf2⟩
  · change Gval (lf D F0) F2 ≠ 0
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact h₁.1.2.2
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one']
    change ModG (VS D) Λ (Lat.gS D) (frame F2 b - frame (lf D F0) b)
    rw [hf2 b]
    exact modG_lift hT' p₁.1 p₁.2.2.1 hFΛ hν.1 hm' hνF hmF' htie
      (fun c => by have := h₁.2.1.2.2 c; rwa [frameAct_one'] at this) b
  · exact (hFun.2.2.2.1 ⟨F₁, p₁⟩ ⟨F2, pd2⟩ hdc).1 h₁.2.2.1
  · have hZZ : ZhatL (lf D F0) F2 = U.conjTranspose * ZhatL (lf D F0) F₁ * U' := by
      funext a b
      exact hent a b
    change ZhatL (lf D F0) F2 = U.conjTranspose * Z₁ * U'
    have hz1 : ZhatL (lf D F0) F₁ = Z₁ := h₁.2.2.2.2
    rw [hZZ, hz1]

theorem integral_pair_of_shape (Zd : Formalism.L2.SG.TermLoc.LocDat D) {A B : PairVal.MatR D} (hA : Formalism.L2.SG.Pf.AtPt.IsLo A)
    (hB : Formalism.L2.SG.Pf.AtPt.IsUp B) (hES : Formalism.L2.SG.Pf.StabIntSh.EntryShape D A B) :
    TupGlob.IntFr A.conjTranspose ∧
      TupGlob.IntFr (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) ∧
      TupGlob.TieG A.conjTranspose
        (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) := by
  open Formalism.L2.SG.Pf.FibD in
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

theorem ez_of_normRep {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {γ : TermDef.Term D u u' F0 what₂}
    (hΛ : IsRowLat D F0 γ.lam) {w w₁ : Point D.host.E (D.R.rS + 1)} (hel : Formalism.L2.SG.DataCut.EligAt γ w)
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)} {L U : PairVal.MatR D}
    (hn : PairVal.NormRep γ w₁ F' L U) :
    F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') := by
  obtain ⟨⟨p₁, e₁⟩, hadm₁, -⟩ := hn
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ
  obtain ⟨Fa, ⟨pa, ea⟩, hGa, -⟩ := hel.2
  have hdca := (hEq ⟨Fa, pa⟩ ⟨F', p₁⟩).1 (ea.trans e₁.symm)
  obtain ⟨Fg, ⟨pg, eg⟩, hgen⟩ := hel.1.1
  refine ⟨⟨p₁.1, p₁.2.1, ?_⟩, hadm₁, ?_, p₁.2.2, rfl⟩
  · change Gval (lf D F0) F' ≠ 0
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca]; exact hGa
  · exact (hFun.2.2.2.1 ⟨Fg, pg⟩ ⟨F', p₁⟩ ((hEq ⟨Fg, pg⟩ ⟨F', p₁⟩).1 (eg.trans e₁.symm))).1 hgen

theorem moveCZ {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) (hu : Tu D u ≠ 0) (hu' : Tu D u' ≠ 0)
    (Zd : Formalism.L2.SG.TermLoc.LocDat D) {t : TermsOf D u' F0 Λ} {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (h' : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z)
    (r' : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F')
    {a' b : PairVal.MatR D} (ha : IsLoUni a') (hb : IsUpUni b) (hst : a' * ZhatOM Z * b = ZhatOM Z)
    (hES : Formalism.L2.SG.Pf.StabIntSh.EntryShape D a' b) :
    ∃ ν ∈ NLam Λ (lf D F0), ∃ m ∈ NLam Λ F',
      (∀ c, ν (frame (lf D F0) c) = ∑ d, a'.conjTranspose d c • frame (lf D F0) d) ∧
      (∀ c, m (frame F' c) = ∑ d, (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) d c •
        frame F' d) ∧
      ∃ F2 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F2 ∧ ∀ c, frame F2 c = ν⁻¹ (m (frame F' c)) := by
  set Sg := Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS with hSg
  have hlo : Formalism.L2.SG.Pf.AtPt.IsLo a' := ⟨fun i => (ha i i).2 rfl, fun i j h => (ha i j).1 h⟩
  have hup : Formalism.L2.SG.Pf.AtPt.IsUp b := ⟨fun i => (hb i i).2 rfl, fun i j h => (hb j i).1 h⟩
  obtain ⟨hi1, hi2, htie⟩ := integral_pair_of_shape Zd hlo hup hES
  have hU : IsUpUni a'.conjTranspose := fun i j => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Matrix.conjTranspose_apply, (ha j i).1 h, star_zero]
    · subst h; rw [Matrix.conjTranspose_apply, (ha i i).2 rfl, star_one]
  have hU' : IsUpUni (Sg * b * Sg) := fun i j => by
    rw [Formalism.L2.SG.Pf.FibD.sg_entry]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp [Formalism.L2.SG.Pf.StabIntSh.bt, (hb i j).1 h]
    · subst h
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, (hb i i).2 rfl, ← pow_add, ← two_mul, pow_mul]
  obtain ⟨ν, hν, m, hm, hνF, hmF, F2, hF2, hr2, hf2⟩ := lift_move hΛ hu hu' h' r' hU hU' hi1 hi2 htie
  refine ⟨ν, hν, m, hm, hνF, hmF, F2, ?_, hr2, hf2⟩
  have hZ : a'.conjTranspose.conjTranspose * Z * (Sg * b * Sg) = Z := by
    rw [Matrix.conjTranspose_conjTranspose]
    have hS : ZhatOM Z = Z * Sg := Formalism.L2.SG.Pf.AtPt.zhatOM_eq Z
    rw [hS] at hst
    calc a' * Z * (Sg * b * Sg) = (a' * (Z * Sg) * b) * Sg := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [hst, Matrix.mul_assoc, Formalism.L2.SG.Pf.AtPt.sg_sq, Matrix.mul_one]
  rwa [hZ] at hF2

end Formalism.L2.SG.Pf.TupAct
end
end

