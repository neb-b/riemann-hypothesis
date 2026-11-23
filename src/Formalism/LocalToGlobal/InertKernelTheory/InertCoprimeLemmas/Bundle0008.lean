module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0015
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0003
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.SharpRestriction.GrowthBounds.Bundle0006

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem bodyC_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) {I : Type} [Fintype I] (wt : I → Y.Kc) (La : I → X.Lt j)
    (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add (f := _), Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm]

theorem second_kernel_coupled (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (lp : (D.chTw u μ).cls j → X.Lt j)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hT : TiesC Y t u μ cmp ι Rd Sr j lp) (hH : HeckeC Y u μ j lp) : ExpansionDecomposition D X Y j := by
  obtain ⟨hSh, hRd, hLat, hDG, hSer, cK, h1, h2, _, hDel⟩ := hT
  have body := bodyC_of_span Y j cK (fun x : (D.chTw u μ).cls j => (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹) lp
    (Set.range (cmp j)) (by
      rintro _ ⟨x, rfl⟩ c' L' hL
      obtain ⟨y, hy⟩ := hrat x
      have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
          ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
        have hQ := sharpQ_qOf (hSh x)
        funext c1 y1
        rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smulₛₗ, map_inv₀, map_natCast, hDel c x c' L' hL,
        kernel_of_smul p X Y j (lp c) (c', L') _ (hSer c c' L' hL), mul_smul])
  refine ⟨cK, h1, h2, (D.chTw u μ).cls j, Unit, inferInstance, inferInstance,
    fun x => Nat.card ((D.chTw u μ).stab j x), fun x _ => lp x, fun x _ => hLat x,
    fun x => ⟨Nat.card_pos, hDG x⟩, ?_, ?_⟩
  · intro F hF c' L' hL
    simpa only [Finset.univ_unique, Finset.sum_singleton] using body F (hspan hF) c' L' hL
  · intro v i F hF La' hLa'
    simpa only [Finset.univ_unique, Finset.sum_singleton] using hH v i F hF La' hLa'

end Gen

theorem second_kernel_coupled_instance : SecondKernelCoupledLastLift := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hTs hH
  have hj : D.R.m - 1 < D.R.m := by omega
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp (D.R.m - 1) (KA.cmp_int (D.R.m - 1) hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat (D.R.m - 1)).V) (y : ((ex.tw.fm u μ).lat (D.R.m - 1 + 1)).V),
      (ex.tw.fm u μ).emb (D.R.m - 1 + 1) y = (D.chTw u μ).K (D.R.m - 1) ((ex.tw.fm u μ).emb (D.R.m - 1) x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz (D.R.m - 1) (KA.cmp (D.R.m - 1) x) = KA.cmp (D.R.m - 1 + 1) y :=
    fun x y hy => (KA.cmp_K (D.R.m - 1) hj x y hy).symm
  exact second_kernel_coupled (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cmp ι Rd Sr
    (D.R.m - 1) hj lp hsp (KA.rat (D.R.m - 1) hj) hch hTs hH

theorem admissible_fourth_instance : Adm4NewInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hE hL
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hl : j + 1 < D.R.m := by omega
    obtain ⟨cK, h1, h2, _, hb⟩ :=
      second_kernel_entry_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hE j hl
    exact ⟨cK, h1, h2, hb⟩
  · have hm : 0 < D.R.m := by omega
    obtain rfl : j = D.R.m - 1 := by omega
    obtain ⟨hT1, hH1⟩ := hL hm
    exact second_kernel_coupled_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp
      hm hT1 hH1

theorem hecke_coupled_entry : HeckeCEntry := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y lp hm h5b hsec hst
    v i F hF La' hLa'
  have hj : D.R.m - 1 < (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm :=
    lt_of_lt_of_eq (by omega : D.R.m - 1 < D.R.m) KA.fl_m.symm
  let X := sysAt Ch std vp unif eO eO_spec dG dG_spec om
  letI := X.G.ringO
  letI := X.G.domO
  letI := X.G.dvrO
  letI := X.G.fieldK
  letI := X.G.algOK
  letI := Y.algKf
  have h6 := Formalism.L2.G.Pend.up_down_adjoint D _ Y
  have hk0 (j : ℕ) (hj : j < X.mm) (v : X.Pl) (k : ℕ)
      (F : X.Fm j) (hF : F ∈ X.FQ j) (La' : X.Lt (j + 1)) (hLa' : (X.Pj (j + 1)).IsLatTup La'.2) :
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ •
        ∑ A1 ∈ Pf.UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2) =
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ • Y.ker j La La' (X.Tm v k j F La.1 La.2) := by
    open Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.G.LatticeSystems in
    classical
    apply MvPolynomial.ext
    intro n
    let φ : X.Lv.comp j → (X.Pj j).Tup → (X.Pj j).Tup → Y.Kc := fun c L L1 =>
      if (X.Pj j).IsLatTup L1 then AddMonoidAlgebra.coeff (Y.ker j (c, L1) La' (F c L)) n else 0
    have hφ : ∀ c (γ : (X.Lv.lev j c).Γ) L L1,
        φ c ((X.Lv.lev j c).smul γ L) ((X.Lv.lev j c).smul γ L1) = φ c L L1 := by
      intro c γ L L1
      simp only [φ]
      by_cases h : (X.Pj j).IsLatTup L1
      · rw [if_pos h, if_pos ((latTup_smul _ _ γ L1).2 h), (Eqv_of_FQ X hF).2 c γ L,
          h5b j hj c L1 La' γ (F c L) (vt_FQ X hF c L) h hLa']
      · rw [if_neg h, if_neg (fun h' => h ((latTup_smul _ _ γ L1).1 h'))]
    have key := h6 j hj.le (X.vJ j v) k φ hφ
    have hs : ∀ (La : X.Lt j) (z : Y.Kc), ((X.stab j La : X.G.Kf))⁻¹ • z = ((X.stab j La : Y.Kc))⁻¹ * z := by
      intro La z
      rw [Algebra.smul_def, map_inv₀, map_natCast]
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun La hLa => ?_
      have hlat := Y.Rep_lat j La hLa
      rw [MvPolynomial.coeff_smul, hs, MvPolynomial.coeff_sum]
      congr 1
      refine Eq.trans ?_ (finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))).symm
      refine Finset.sum_congr rfl fun A1 hA1 => ?_
      have hE := (mem_UP _).1 hA1
      simp only [φ]
      rw [if_pos (hk_latTup_update _ hlat _ A1 hE.2.1)]
    · refine Finset.sum_congr rfl fun La hLa => ?_
      have hlat := Y.Rep_lat j La hLa
      rw [MvPolynomial.coeff_smul, hs]
      congr 1
      refine Eq.trans (finsum_mem_eq_finite_toFinset_sum _ (edges_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))) ?_
      have e : X.Tm v k j F La.1 La.2 = ∑ L0 ∈ EE (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          F La.1 (Function.update La.2 (X.vJ j v) L0) := Tminus_eq (X.Pj j) (X.vJ j v) k (F La.1) La.2
      rw [e, ker_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun L0 _ => ?_
      simp only [φ]
      rw [if_pos hlat]
  have hk := hk0 (D.R.m - 1) hj v i F hF La' hLa'
  have hs : ∀ (n : ℕ) (z : XspC (X.Pj (D.R.m - 1 + 1)) Y.Kc), ((n : X.G.Kf))⁻¹ • z = ((n : Y.Kc))⁻¹ • z := by
    intro n z
    rw [← algebraMap_smul Y.Kc ((n : X.G.Kf))⁻¹ z, map_inv₀, map_natCast]
  simp only [hs] at hk
  have hk := ((Finset.sum_coe_sort (Y.Rep (D.R.m - 1)) _).trans hk).trans (Finset.sum_coe_sort (Y.Rep (D.R.m - 1)) _).symm
  simp only [Pf.up_finsum]
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  have hbij : Function.Bijective fun x : (D.chTw u μ).cls (D.R.m - 1) =>
      (⟨lp x, (hsec x).1⟩ : {La // La ∈ Y.Rep (D.R.m - 1)}) := by
    constructor
    · intro x1 x2 he
      have h1 := (hsec x1).2
      have h2 := (hsec x2).2
      have : lp x1 = lp x2 := congrArg Subtype.val he
      rw [← h1, ← h2, this]
    · intro La
      refine ⟨KA.cls (D.R.m - 1) La.1.1 La.1.2, ?_⟩
      apply hb.1
      show KA.cls (D.R.m - 1) (lp _).1 (lp _).2 = KA.cls (D.R.m - 1) La.1.1 La.1.2
      exact (hsec _).2
  have hw : ∀ x : (D.chTw u μ).cls (D.R.m - 1),
      Nat.card ((D.chTw u μ).stab (D.R.m - 1) x) = (sysAt Ch std vp unif eO eO_spec dG dG_spec om).stab (D.R.m - 1) (lp x) := by
    intro x
    have e := hst (lp x) (hsec x).1
    rw [(hsec x).2] at e
    exact e
  refine (Fintype.sum_bijective _ hbij _ _ fun x => ?_).trans (hk.trans (Fintype.sum_bijective _ hbij _ _ fun x => ?_).symm)
  · simp only [hw x]
    rfl
  · simp only [hw x]
    rfl

theorem coupled_compatibility_at_place : TiesCOfAt := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hsec hTs
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hTs
  refine ⟨hSh, hRd, fun x => Y.Rep_lat _ _ (hsec x).1, fun x => ?_, fun x c' L' hL => hSer (lp x) (hsec x).1 c' L' hL,
    cK, h1, h2, h3, fun x y c' L' hL => ?_⟩
  · have e := hSt (lp x) (hsec x).1
    rw [(hsec x).2] at e
    rw [e]
    exact dG_spec (D.R.m - 1) (by have := KA.fl_m; omega) (lp x).1 (lp x).2 (Y.Rep_lat _ _ (hsec x).1)
  · have e := hDel (lp x) (hsec x).1 y c' L' hL
    rw [(hsec x).2] at e
    exact e

theorem coupled_section_exists : SecCEx := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y hm
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  refine ⟨fun x => (Function.surjInv hb.2 x).1, fun x => ⟨(Function.surjInv hb.2 x).2, ?_⟩⟩
  exact Function.surjInv_eq hb.2 x

end Formalism.L2.KerInert.SecondKernelCoupled
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelSeries
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

theorem eFac_ne_zero {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_) <;>
  · refine Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ ?_
    have hs := X.G.P.setting v
    haveI := hs.frac_alt
    have h1 : ((p : ℕ) : X.G.P.W v) ≠ 0 := hs.p_unif.ne_zero
    have h2 : ((p : ℕ) : X.G.P.Qq v) ≠ 0 := by
      rw [← map_natCast (algebraMap (X.G.P.W v) (X.G.P.Qq v))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr h1
    rw [← map_natCast (X.G.P.ι v)]
    exact (map_ne_zero _).mpr h2

theorem series_compatibility_of : TieSerOf := by
  intro p _ X Y j La _ c' L' _
  unfold srOf
  rw [smul_smul, inv_mul_cancel₀ (eFac_ne_zero Y j La (c', L')), one_smul]

end Formalism.L2.KerInert.SecondKernelSeries
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelSharpWeights
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSharpWeights

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

theorem sharp_weight_formula : SharpWtIs := by
  intro D Tw u μ j hj τ r
  have h1 := (nu_t_identity D u j hj τ r).1
  have h2 := (D.chTw u μ).sSharp_eq j hj τ
  have h3 := (Tw.fm u μ).lam_eq j hj.le τ r
  have h2' : (((D.chTw u μ).sSharp j τ : ℤ) : ℝ) =
      (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) + ((j : ℝ) + 1) * ((D.R.t : ℝ) + 1)) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [sExp', Ranks.N] at this
    push_cast at this
    exact this
  have he : ∀ (k : ℕ) (hk : k < D.R.m), k = j → (D.hc τ).e ⟨k, hk⟩ = (D.hcW u τ).e ⟨j, hj⟩ := by
    rintro k hk rfl; rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  have hw : ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℝ) = (((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  push_cast
  rw [h1, h2', hw, h3]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dite_eq_left (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m by omega), he _ _ (by omega)]
  simp only [Ranks.N]
  by_cases hr : r.1 < D.R.k
  · rw [dite_eq_left hr, dite_eq_left hr]
    simp only [hcToWeightQ, rhoVec]
    push_cast
    ring
  · have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
      have := D.R.blk_lt hj.le r hr
      omega
    rw [dite_eq_right hr, dite_eq_right hr, dite_eq_left hb]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hrk : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
      exact_mod_cast this
    simp only [wG]
    push_cast
    rw [hrk]
    ring

end Formalism.L2.KerInert.SecondKernelSharpWeights
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelStabilizers
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.KernelStabilizer

namespace Formalism.L2.KerInert.SecondKernelStabilizers

def StabEqAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _),
    StabEqRest (CmpJ.kerAtMu_any K H hS Gt Ch hCh)

def TieStabAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    DV.Used D μ → OrbitPlaces.Stab0 D → ∀ j, j ≤ D.R.m → TieStabAt (Y := Y) u μ (CmpJ.kerAtMu_any K H hS Gt Ch hCh).cls j

theorem stabilizer_any_level : TieStabAny := by
  intro D c Tw u μ w h _ Fl Lv K I H hS Gt Ch hCh std vp unif eO eO_spec dG dG_spec om Y hU hS0 j hj
  exact stabilizer_all_instances D Tw c u μ w h Fl Lv Ch (CmpJ.kerAtMu_any K H hS Gt Ch hCh) std vp unif eO eO_spec dG dG_spec om Y
    hU hS0 K.stab_eq j hj

end Formalism.L2.KerInert.SecondKernelStabilizers
end
end

