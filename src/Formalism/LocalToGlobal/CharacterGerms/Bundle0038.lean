module

public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfCore
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0036
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0037
public import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0035
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyGlue
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDelta
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0002
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyRes2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfOfProjection
section
set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

theorem noLinSelf_of (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) : NoLinSelfSt :=
  fun _ _ _ _ _ _ _ _ Y _ _ _ _ p g a0 u0 hu0 heig hV1 hc0 => noLin_self hAdj hPL Y p g a0 u0 hu0 heig hV1 hc0

theorem rank_maximal_self_of_projection (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) :
    RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_core hV1 hFE hC0 (noLinSelf_of hAdj hPL)

theorem rank_maximal_self_of_eigen (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hAdj : ALinAdjSt)
    (hE : RowTiePKey.KeyEigSt) : RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_of_projection hV1 hFE hC0 hAdj (projLieSelf_of hE)

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCharS
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I0 : Type} [Fintype I0]

def SelfData.yOf {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) (χ : Fin 2 → PS C 1 dd) (x : I0) : C :=
  ∑ col, ∑ i, dlogC (χ col) i * (Y.rawSelf p).u g x (col, i)

def CharGermSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (χ : Fin 2 → PS C 1 dd), (∀ col, Y.IsChar (χ col)) →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ _ : Fin 2, I0 → MvPowerSeries I0 C),
      (∀ g, (S g).IsT (t g)) →
      upG (I := fun _ => I0) g (mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C))) ∈ IntGerm V t

namespace ChG

open VP

theorem subst_linU_linF {ι : Type} [Fintype ι] (U : ι → Fin dd → C) (y : Fin dd → C) :
    MvPowerSeries.subst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) (linF y) =
      ∑ x : ι, (∑ i, y i * U x i) • (MvPowerSeries.X x : MvPowerSeries ι C) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) :=
    VP.hs (fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [linF, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem cc_linU {ι κ : Type} [Fintype ι] (U : ι → κ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

end ChG

theorem SelfData.yOf_int {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) {χ : Fin 2 → PS C 1 dd}
    (h : ∀ col, Y.IsChar (χ col)) (x : I0) : V.Ge 0 (p.yOf g χ x) := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.Ge 0 (f i)) → V.Ge 0 (∑ i ∈ s, f i) :=
    fun s f hf => Finset.sum_induction f (fun z => V.Ge 0 z) (fun _ _ ha hb => VF.Ge.add ha hb)
      (VF.Ge.zero 0) hf
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨M, hM⟩ := p.gm_lim 0
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := VF.Ge.add h1 (p.em_int a (M r s))
    simpa using h2
  unfold SelfData.yOf
  refine hsum _ _ fun col _ => hsum _ _ fun i _ => ?_
  refine VF.Ge.mul_int ((h col).1 _) ?_
  exact VF.Ge.mul_int (hgm _ _ _) (p.e_int _ _)

open ChG VP in
theorem charGermSelf_holds : CharGermSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := GeneralGermZero.sysK_P (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y)
    (SelfConjugateGermZero.lgS_add Y p) (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  set U : I0 → Fin 2 × Fin dd → C := fun c' i => (Y.rawSelf p).u g c' i with hU
  set γ0 : MvPowerSeries I0 C := ∏ col : Fin 2, MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col)) with hγ0
  have hI : IntS V γ0 := IntS_prod _ fun col _ =>
    IntS.subst (fun i => hP0 (col, i)) (fun i => hPI (col, i)) (integralSeries_uncurry_one (hχ col).1)
  have hcol : ∀ col : Fin 2, MvPowerSeries.subst (t g) (MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col))) =
      mvExp (∑ x : I0, (∑ i, dlogC (χ col) i * U x (col, i)) • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    intro col
    rw [subst_subst (fun i => hP0 (col, i)) (ht0 g)]
    have h1 : (fun i => MvPowerSeries.subst (t g) (P (col, i))) = fun i =>
        MvPowerSeries.subst (fun k : Fin dd => ∑ c', U c' (col, k) • (MvPowerSeries.X c' : MvPowerSeries I0 C)) (e Y i) := by
      funext i
      rw [hPt (t g) (ht g) (col, i)]
      show MvPowerSeries.subst (fun k : Fin 2 × Fin dd => ∑ c', U c' k • (MvPowerSeries.X c' : MvPowerSeries I0 C))
        (MvPowerSeries.subst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.ex i))) = _
      rw [subst_subst (fun _ => cc_X _) (cc_linU U)]
      congr 1
      funext k
      rw [subst_X (cc_linU U)]
    rw [h1, ← subst_subst (cc_e Y) (fun k => cc_linU U (col, k))]
    show MvPowerSeries.subst _ (Psi Y (χ col)) = _
    rw [chi_exp Y (hχ col), subst_exp (fun k => cc_linU U (col, k)) (constantCoeff_linF _),
      subst_linU_linF (fun c' k => U c' (col, k))]
  have key : MvPowerSeries.subst (t g) γ0 =
      mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    rw [hγ0, subst_prod (ht0 g), Finset.prod_congr rfl fun col _ => hcol col,
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum Finset.univ _ (fun col _ => cc_linU (fun x (_ : Unit) => ∑ i, dlogC (χ col) i * U x (col, i)) ()),
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul]
    rfl
  refine ⟨upG (I := fun _ => I0) g γ0, ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst (I := fun _ => I0) t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEig
section
namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBr
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

section Series

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ}
variable {R : Type} [CommRing R] [Algebra R C]

abbrev toC {n : ℕ} (f : PS R n dd) : PS C n dd := MvPowerSeries.map (algebraMap R C) f

theorem mpt_pt {n : ℕ} (j : Fin n) : MapFB.mpt (algebraMap R C) (pt R dd j) = pt C dd j := by
  funext i
  simp [MapFB.mpt, pt]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt R dd j i) = 0 := by
  simp [pt]

theorem isChar_of_isCh (Y : FBChart C V OE dd) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) {u : PS R 1 dd} (hu : IsCh FR u) :
    Y.IsChar (toC u) := by
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact hR _
  · rw [MvPowerSeries.constantCoeff_map, hu.1, map_one]
  · have h := congrArg (MvPowerSeries.map (algebraMap R C)) hu.2
    have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1) i) = 0 := by
      intro i
      refine MapFB.cc_ev _ ?_ _ (hF0 i)
      intro j i'
      fin_cases j <;> simp [pt]
    rw [map_mul, MapFB.map_ev1 _ _ hadd, MapFB.map_ev1 _ _ (cc_pt 0), MapFB.map_ev1 _ _ (cc_pt 1), mpt_pt, mpt_pt] at h
    have e : MapFB.mpt (algebraMap R C) (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1)) =
        addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) := by
      funext i
      show MvPowerSeries.map (algebraMap R C) (ev ![pt R (n := 2) dd 0, pt R (n := 2) dd 1] (FR i)) = _
      rw [MapFB.map_ev2 _ _ _ (cc_pt 0) (cc_pt 1), mpt_pt, mpt_pt]
      show _ = ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F i)
      rw [hF i]
    rw [e] at h
    exact h

end Series

section Len

theorem lenCoker_mono {R : Type} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h h' : ℕ}
    (B : Matrix (Fin m) (Fin h') R) (f : Fin h → Fin h') :
    S4.lenCoker v B ≤ S4.lenCoker v (B.submatrix id f) := by
  unfold S4.lenCoker
  refine Finset.le_inf fun g _ => ?_
  exact Finset.inf_le (f := fun g : Fin m → Fin h' => v (B.submatrix id g).det) (Finset.mem_univ (f ∘ g))

variable {C : Type} [Field C] {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] {dd : ℕ}

theorem lenCoker_le_of_hasLen (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {s N : ℕ} (W : Fin s → Fin dd → R) (u : Fin N → PS R 1 dd) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm R
      ((Fin s → R) ⧸ Submodule.span R (Set.range fun k => res W (dl (u k)))) x)
    {S : ℝ} (hS : vm (V.l : C) ^ S ≤ x) :
    S4.lenCoker V.v (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) ≤
      ((S : ℝ) : WithTop ℝ) := by
  set α : Matrix (Fin s) (Fin N) R := Matrix.of fun c k => res W (dl (u k)) c with hα
  have hr : LinearMap.range α.mulVecLin = Submodule.span R (Set.range fun k => res W (dl (u k))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [← hr] at hx
  have hSr : (vm (V.l : C) : ℝ) ^ S ≤ (x : ℝ) := by exact_mod_cast hS
  have hpos : 0 < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 S) hSr
  have e := lenCoker_eq_logb hT hv h0 h1 α hx hpos
  have e2 : (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) =
      Matrix.of fun c k => algebraMap R C (α c k) := by
    ext c k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, hα, res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e2, e]
  refine WithTop.coe_le_coe.mpr ?_
  have h2 : Real.logb (vm (V.l : C) : ℝ) x ≤ Real.logb (vm (V.l : C) : ℝ) ((vm (V.l : C) : ℝ) ^ S) :=
    (Real.logb_le_logb_of_base_lt_one h0 h1 hpos (Real.rpow_pos_of_pos h0 S)).mpr hSr
  rwa [Real.logb_rpow h0 (ne_of_lt h1)] at h2

end Len

section Sum

theorem frobSum_conj_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (q : ZMod d → ℕ)
    (hqb : ∀ b, big b → q b = j') (hqs : ∀ b, ¬ big b → q b = n + j) (a : ZMod d) (ha : big a) :
    S4.frobSum l q a = upB l (n + j) j' (gam l) := by
  rw [S4.frobSum_alt hl j' 0 (n + j) big halt q (fun b hb => by rw [hqb b hb]; rfl) hqs a ha]
  have h1 := S4.one_div_eq_gam_add_rho hl
  have hg : gam l = S4.gam l := rfl
  have hdiv : (j' : ℝ) / ((l : ℝ) - 1) = j' * (S4.gam l + S4.rho l) := by rw [← h1]; ring
  unfold upB
  rw [hg, hdiv]
  push_cast
  ring

theorem frobSum_conj_all {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (q : ZMod d → ℕ) (hq : ∀ b, q b = j')
    (a : ZMod d) : S4.frobSum l q a = upB l (n + j) j' 0 := by
  rw [S4.frobSum_const hl j' q hq a]
  unfold upB
  ring

end Sum

section Core

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

end Core

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

namespace VP

theorem cc_mvExp' {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp h) = 1 := by
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (h ^ k) / (k.factorial : C)) = 1
  simp

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem pullback_two_var_mul (F G : PS C 2 dd) : pull2 Y p (F * G) = pull2 Y p F * pull2 Y p G := by
  unfold pull2
  exact linPull_mul _ _ F G

theorem pullback_two_var_prod {ι : Type} (s : Finset ι) (F : ι → PS C 2 dd) :
    pull2 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull2 Y p (F i) := by
  unfold pull2
  exact linPull_prod _ _ s F

theorem pullback_two_var_one : pull2 Y p (1 : PS C 2 dd) = 1 := by
  have h := pullback_two_var_prod Y p (∅ : Finset Unit) (fun _ => (1 : PS C 2 dd))
  simpa using h

theorem pullS_exp {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (E : PS C 1 dd) (hE : MvPowerSeries.constantCoeff E = 1) :
    pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ ρ : Fin N, rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] E)) := by
  have hprod : pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ b : Fin n, pullS Y p pl (ev (n := n) ![pt C dd b] E) := by
    unfold pullS
    exact linPull_prod _ _ _ _
  rw [hprod]
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map pl →
      pullS Y p pl (ev (n := n) ![pt C dd b] E) = 1 := by
    intro b _ hb
    have hb' : b ∉ Set.range pl := by simpa using hb
    rw [pullS_off (b := b) (hb := hb'), hE, map_one]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map pl)) hoff, Finset.prod_map,
    Fintype.prod_prod_type]
  simp_rw [pullS_col]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [pullback_two_var_prod, rowOf_prod]

end VP

theorem valuation_eq_self_of_unit_germ (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (h2 : UnitSelfSt Y p) (h3 : GermLiftSelfSt Y p H) : ValEqSelfSt Y p H Ls n := by
  intro hs N pl P hP Po hQ kind hk S t ht gr hg
  obtain ⟨U, hUi, hU0, hU⟩ := h2 hs
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hUi hU0
  choose G hGi hG using fun (o : Orb) (ρ : Fin N) => h3 hs o (S o) (t o) (ht o) (gr o ρ) (hg o ρ)
  obtain ⟨co, hco, hQe⟩ := hQ
  refine ⟨∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ), ?_, ?_⟩
  · refine VP.IntS_prod _ fun ρ _ => ?_
    unfold ev
    refine IntS.subst (VP.cc_ptPl pl ρ) (fun q => ?_) (hU'i.mul (VP.IntS_prod _ fun o _ => hGi o ρ))
    obtain ⟨g, i⟩ := q
    fin_cases g <;> exact VP.IntS_X _
  · have hk0 : MvPowerSeries.constantCoeff ((Y.k : C) • Y.B.hL C Y.h Y.w0) = 0 := VP.cc_smul _ (VP.cc_hL Y)
    have hE1 : MvPowerSeries.constantCoeff (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) = 1 := by
      rw [VP.expS_eq _ hk0, VP.cc_mvExp']
    have hrow : ∀ ρ : Fin N,
        rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) *
          rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col]
            (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow)) := by
      intro ρ
      rw [← VP.rowOf_mul, hU, VP.pullback_two_var_mul, VP.pullback_two_var_prod]
      have e2 : (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
          (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) =
          ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
        have e3 : pull2 Y p U' * pull2 Y p U = 1 := by rw [← VP.pullback_two_var_mul, hUU, VP.pullback_two_var_one]
        calc (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
              (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow))
            = (pull2 Y p U' * pull2 Y p U) *
                ((∏ o, pull2 Y p (G o ρ)) * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) := by ring
          _ = ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
              rw [e3, one_mul, ← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun o _ => by rw [hG o ρ, VP.toAllS_mul]
      rw [e2, VP.rowOf_prod]
      exact Finset.prod_congr rfl fun o _ => by rw [VP.rowOf_toAllS, VP.rowCopy_mul_exp]
    have hser : pullS Y p pl ((∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) *
        FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow))) := by
      have hpl : ∀ ρ : Fin N, VP.linPull Y (MS Y p pl)
          (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) =
          rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) := fun ρ => VP.pullS_plane Y p pl ρ _
      rw [VP.expS_copies, show pullS Y p pl (_ * _) = _ from VP.linPull_mul Y _ _ _,
        show VP.linPull Y (MS Y p pl) (∏ b : Fin n, _) = _ from VP.pullS_exp Y p pl _ hE1,
        VP.linPull_prod, Finset.prod_congr rfl fun ρ _ => hpl ρ,
        ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun ρ _ => hrow ρ, Finset.prod_comm]
      exact Finset.prod_congr rfl fun o _ => (map_prod _ _ _).symm
    unfold FBChart.nab nabValN
    rw [VP.logCoordG Y (MS Y p pl) (Ls.cp n) (Ls.uv n) P co
      (fun ℓ hℓ b i => VP.hco_of_img Y p pl (Ls.cp n) (Ls.uv n) ℓ (co ℓ) (hco ℓ hℓ) b i), ← hQe]
    rw [show VP.linPull Y (MS Y p pl) _ = _ from hser, VP.jet_orb]
    exact Finset.prod_congr rfl fun o _ =>
      leaf_holds C V d (fun _ => I0 o) (Fin 2 × Fin dd) (Y.rawSelf (p o)) (H o) N (Po o) (kind o) (hk o) (gr o)

end Formalism.L2.FormalSeriesBounds
end
end

