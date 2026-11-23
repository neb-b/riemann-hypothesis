module

public import Mathlib
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlLeParams
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.AlTop

theorem al_le_rowLen_sub {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (t : HH D) (ht : t ∈ D.host.TT) :
    al L (aL L) t ≤ (((nuD D u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD D u j (false, t)).rowLen 1 : ℕ) : ℝ) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hz : IsTopPl D (false, t) := ⟨rfl, ht⟩
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl L u j hj (false, t) hz
  have hwe : wPl D (j + 1) (false, t) = (((D.hcW u (tauPl D (false, t))).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  obtain ⟨-, h4⟩ := L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hS := L.Sc_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1,
    RowWeightLemmas.nuRow_head D u j hj _ 1 (by omega), hwe]
  unfold al cG kaJ Ranks.N
  push_cast
  linarith

theorem al_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, al (Fm.L x i) (aL (Fm.L x i)) t ≤ (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) :=
  fun Fm => ⟨0, fun x _ _ i u j hj t ht => al_le_rowLen_sub (Fm.L x i) u j hj t ht⟩

end GlobalTheory.AlTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

theorem bT_le_five_quarters {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := lt_trans one_pos hx1
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hLa : 0 ≤ L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    have h3 : 0 < L.LaG * L.sc.b' / D.R.k := by linarith
    have h4 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk).1 h3
    exact ((mul_pos_iff_of_pos_right hb').1 h4).le
  have hr := P.rho_le
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have h5 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le (Real.log_nonneg hx1.le)) hLa) hk.le
  unfold LevelStarExponents.rhoP at hr
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h7 := P.bT_le t
  have h8 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h9 := mul_le_mul_of_nonneg_right h6 hb'.le
  linarith

theorem wPl_windows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 ∧ (IsTopPl (Fm.D x i) z → (Fm.L x i).sc.b' ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ 2 * (Fm.L x i).sc.b') := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := _root_.GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩ := h0 x hx hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) h4
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b' := by
    intro τ t ht
    obtain ⟨a1, a2⟩ := L.win_top (j + 1) (by omega) (by omega) τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le_five_quarters P t
    constructor <;> linarith
  unfold wPl
  refine ⟨?_, ?_, ?_⟩
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · have := (L.win_thick (j + 1) (by omega) (by omega) _ h1).1
      linarith
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).1
      linarith
    · exact (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · exact (L.win_thick (j + 1) (by omega) (by omega) _ h1).2
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).2
      linarith
    · have := (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2
      linarith
  · rintro ⟨hz1, hz2⟩
    refine htop _ ⟨z.2, hz2⟩ ?_
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]

end GlobalTheory.Ggeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLe
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.CapBound

theorem row_le (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr1 : r ≤ 1)
    (hr : r < D.R.k) :
    (((nuD D u j z).rowLen r : ℕ) : ℝ) ≤
      wPl D (j + 1) z - kaJ D (j + 1) + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  rw [nuRowOK D u j hj z r, if_pos h2, RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  unfold kaJ Ranks.N
  push_cast
  linarith

theorem cap_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.fill_eq_wPl Fm
  refine ⟨x0, fun x hx hx1 i u j hj z => ?_⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hx0 x hx hx1 i j hj z]
  split_ifs with hz
  · have h1 := row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx1 i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

end GlobalTheory.CapBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresBasic

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem coef_inv (f : S.Forms) (c : S.Cl) (g : stab ι J (P.y c)) :
    (χ (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef ((f : S.Cl → S.V) c)) = P.coef ((f : S.Cl → S.V) c) := by
  obtain ⟨g, rfl⟩ := (P.stabI c).surjective g
  rw [← P.coef_act, f.2 c g]

theorem ext_dec (f : S.Forms) (γ : Γ) (c : S.Cl) (k : J) :
    P.ext (f : S.Cl → S.V) (ι γ * P.y c * k) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have hs := P.dec_spec (ι γ * P.y c * k)
  have hc : P.decC (ι γ * P.y c * k) = c :=
    (P.reps (ι γ * P.y c * k)).unique ⟨_, _, hs⟩ ⟨γ, k, rfl⟩
  unfold ClassPres.ext
  rw [hc] at hs ⊢
  generalize P.decG (ι γ * P.y c * k) = γ' at hs ⊢
  generalize P.decK (ι γ * P.y c * k) = k' at hs ⊢
  have e : (P.y c)⁻¹ * ι (γ⁻¹ * γ') * P.y c = (k : G) * (k' : G)⁻¹ := by
    have h2 : ι γ' = ι γ * P.y c * k * (k' : G)⁻¹ * (P.y c)⁻¹ := by rw [hs]; group
    rw [map_mul, map_inv, h2]; group
  have hm : γ⁻¹ * γ' ∈ stab ι J (P.y c) := by
    rw [mem_stab, e]; exact J.mul_mem k.2 (J.inv_mem k'.2)
  have hk : stabK ι (⟨_, hm⟩ : stab ι J (P.y c)) = k' * k⁻¹ := by
    apply Subtype.ext
    simp only [stabK]
    rw [e]; simp
  have hi := coef_inv P f c ⟨_, hm⟩
  rw [hk] at hi
  conv_rhs => rw [← hi]
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul]
  congr 1
  · rw [map_mul, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, inv_mul_cancel_right]
  · simp

theorem ext_y (f : S.Forms) (c : S.Cl) :
    P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c) := by
  have := ext_dec P f 1 c 1
  simpa using this

theorem extMem : P.ExtMem := by
  intro f γ h k
  obtain ⟨c, ⟨γ', k', rfl⟩, -⟩ := P.reps h
  have e : ι γ * (ι γ' * P.y c * k') * k = ι (γ * γ') * P.y c * (k' * k : J) := by
    simp [mul_assoc]
  rw [e, ext_dec, ext_dec, map_mul, map_mul, map_smul, smul_smul, Units.val_mul, mul_comm]
  rfl

theorem isom : P.Isom := by
  intro f f'
  unfold adInner CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ext_y, ext_y, P.coef_pair, map_mul, map_inv₀, map_natCast, CSD.wt,
    ← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card]

def bW : Module.Basis S.ιV ℂ W := Module.Basis.mk P.coef_li (by rw [P.coef_span])

theorem bW_apply (j : S.ιV) : bW P j = P.coef (S.bV j) := by simp [bW]

theorem repr_coef (x : S.V) (j : S.ιV) : (bW P).repr (P.coef x) j = σ (S.bV.repr x j) := by
  have : P.coef x = ∑ i, σ (S.bV.repr x i) • bW P i := by
    conv_lhs => rw [← S.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ, bW_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem coef_injective : Function.Injective P.coef := by
  intro x x' h
  apply S.bV.repr.injective
  ext j
  apply σ.injective
  rw [← repr_coef P, ← repr_coef P, h]

theorem extL_injective : Function.Injective P.extL := by
  intro f f' h
  apply Subtype.ext
  funext c
  apply coef_injective P
  rw [← ext_y, ← ext_y]
  exact congrFun h _

theorem eq_of_reps {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ)
    (h : ∀ c, F (P.y c) = F' (P.y c)) : F = F' := by
  funext g
  obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
  rw [hF γ _ k, hF' γ _ k, h]

theorem ext_li : LinearIndependent ℂ (fun i => P.extL (S.basis i)) := by
  letI : Algebra K ℂ := σ.toAlgebra
  let Φ : S.Forms →ₗ[K] (S.Cl × S.ιV → K) :=
    { toFun := fun f p => S.bV.repr ((f : S.Cl → S.V) p.1) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro f f' h
    apply Subtype.ext
    funext c
    apply S.bV.repr.injective
    ext j
    exact congrFun h (c, j)
  have h1 := S.basis.linearIndependent.map' Φ hΦ
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  let Ψ : (G → W) →ₗ[ℂ] (S.Cl × S.ιV → ℂ) :=
    { toFun := fun F p => (bW P).repr (F (P.y p.1)) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  refine LinearIndependent.of_comp Ψ ?_
  have e : (⇑Ψ ∘ fun i => P.extL (S.basis i)) = fun i => ⇑(algebraMap K ℂ) ∘ (⇑Φ ∘ ⇑S.basis) i := by
    funext i p
    show (bW P).repr (P.ext _ (P.y p.1)) p.2 = σ (S.bV.repr ((S.basis i : S.Cl → S.V) p.1) p.2)
    rw [ext_y, repr_coef]
  rw [e]
  exact h2


open Classical in
def avgForm (S : CSD K) (c : S.Cl) (x : S.V) : S.Forms :=
  ⟨Pi.single c (∑ g : S.Gam c, S.ρ c g x), by
    intro c' γ
    by_cases h : c' = c
    · subst h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Pi.single_eq_same, map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft γ) _ _ fun _ => rfl
    · simp [Pi.single_eq_of_ne h]⟩

theorem ext_span : Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact extMem P f
  · intro F hF
    have hmem : ∀ M : Submodule ℂ (G → W), (∀ f, P.extL f ∈ M) →
        (∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j))) ∈ M := fun M hM =>
      M.sum_mem fun c _ => M.sum_mem fun j _ => M.smul_mem _ (hM _)
    have key : F = ∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j)) := by
      refine eq_of_reps P hF (hmem _ (extMem P)) fun c => ?_
      simp only [Finset.sum_apply, Pi.smul_apply, ClassPres.extL_apply, ext_y]
      rw [Finset.sum_eq_single c]
      · have hg : ∀ g : S.Gam c, ∑ j, (bW P).repr (F (P.y c)) j • P.coef (S.ρ c g (S.bV j)) = F (P.y c) := by
          intro g
          have h1 := hF (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
          rw [stabK_spec] at h1
          conv_rhs => rw [h1, ← (bW P).sum_repr (F (P.y c))]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [P.coef_act, map_sum, map_smul, Finset.smul_sum, bW_apply]
          exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [avgForm, Pi.single_eq_same, map_sum, mul_smul, ← Finset.smul_sum]
        simp only [Finset.smul_sum (s := (Finset.univ : Finset (S.Gam c)))]
        rw [Finset.sum_comm]
        simp only [hg, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
        exact_mod_cast Fintype.card_ne_zero
      · intro c' _ hc
        simp [avgForm, Pi.single_eq_of_ne (Ne.symm hc)]
      · simp
    rw [key]
    exact hmem _ fun f => Submodule.subset_span ⟨f, rfl⟩

end GlobalTheory.PresBasic

namespace GlobalTheory

theorem classPres_basic : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.Isom ∧ P.ExtBij ∧ (∀ (f : S.Forms) c, P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c)) ∧ Function.Injective P.extL :=
  fun _ _ _ _ _ _ P => ⟨PresBasic.extMem P, PresBasic.isom P, ⟨PresBasic.ext_li P, PresBasic.ext_span P⟩,
    PresBasic.ext_y P, PresBasic.extL_injective P⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoeEqOfPowEqOne
section
noncomputable section

namespace GlobalTheory.ThBe0

open Formalism.MainNotions.GL3Theta IsLocalRing Polynomial

theorem exists_coe_eq_of_pow_eq_one (l : ℕ) [Fact l.Prime] (ζ : ℂ_[l]) (n : ℕ) (hn : 0 < n)
    (h : ζ ^ n = 1) : ∃ a : PadicAlgCl l, (a : ℂ_[l]) = ζ ∧ a ^ n = 1 := by
  have hs : (X ^ n - C 1 : (PadicAlgCl l)[X]).Splits := IsAlgClosed.splits _
  have hne : (X ^ n - C 1 : (PadicAlgCl l)[X]) ≠ 0 := X_pow_sub_C_ne_zero hn 1
  have hr : ((X ^ n - C 1 : (PadicAlgCl l)[X]).map (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot ζ := by
    simp [h]
  obtain ⟨a, ha⟩ := hs.mem_range_of_isRoot hne hr
  refine ⟨a, ha, (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩
  rw [map_pow, ha, h, map_one]

theorem exists_gal_pow (l : ℕ) [Fact l.Prime] :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l,
      ∀ (x : PadicAlgCl l) (m : ℕ), Nat.Coprime m l → x ^ m = 1 → g x = x ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have hl : l.Prime := Fact.out
  have : NeZero l := ⟨hl.ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  rw [hcard] at hφ
  refine ⟨φ, fun x m hm hx => hφ x m (fun h => ?_) hx⟩
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
  exact (hl.coprime_iff_not_dvd.1 hm.symm) h

theorem isFrob_of_rootOfUnity {l : ℕ} [Fact l.Prime] (σ : ℂ_[l] →+* ℂ_[l]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[l]) (n : ℕ), 0 < n → Nat.Coprime n l → ζ ^ n = 1 → σ ζ = ζ ^ l) : IsFrob σ := by
  have hl : l.Prime := Fact.out
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine ⟨hσ, fun x hx => ?_⟩
  have hcl : IsClosed (Wp l : Set ℂ_[l]) := Subring.isClosed_topologicalClosure _
  have hA : ∀ x ∈ Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1},
      ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y := by
    intro x hx
    have hW : ∀ {x}, x ∈ Subring.closure
        {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} → x ∈ Wp l :=
      fun h => Subring.le_topologicalClosure _ h
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨n, hn, hnl, h⟩ := hx
      exact ⟨0, zero_mem _, by simp [hζ x n hn hnl h]⟩
    | zero => exact ⟨0, zero_mem _, by simp [hl.ne_zero]⟩
    | one => exact ⟨0, zero_mem _, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (⟨x, hW hx⟩ : Wp l) ⟨y, hW hy⟩
      have hr' := congrArg Subtype.val hr
      push_cast at hr'
      refine ⟨a + b - x * y * r, sub_mem (add_mem ha hb)
        (mul_mem (mul_mem (hW hx) (hW hy)) r.2), ?_⟩
      rw [map_add (f := _), ea, eb, hr']
      ring
    | neg x hx ihx =>
      obtain ⟨a, ha, ea⟩ := ihx
      rcases hl.eq_two_or_odd' with h2 | ho
      · refine ⟨-a - x ^ l, sub_mem (neg_mem ha) (pow_mem (hW hx) _), ?_⟩
        have he : Even l := h2 ▸ even_two
        have h2' : (l : ℂ_[l]) = 2 := by exact_mod_cast h2
        rw [map_neg, ea, he.neg_pow]
        linear_combination (x ^ l) * h2'
      · refine ⟨-a, neg_mem ha, ?_⟩
        rw [map_neg, ea, ho.neg_pow]
        ring
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      refine ⟨a * y ^ l + x ^ l * b + l * (a * b), add_mem (add_mem (mul_mem ha (pow_mem (hW hy) _))
        (mul_mem (pow_mem (hW hx) _) hb)) (mul_mem (natCast_mem _ _) (mul_mem ha hb)), ?_⟩
      rw [map_mul, ea, eb, mul_pow]
      ring
  have hf : Continuous fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹ := by fun_prop
  have hx' : x ∈ (fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹) ⁻¹' (Wp l : Set ℂ_[l]) := by
    refine closure_minimal (fun z hz => ?_) (hcl.preimage hf) hx
    obtain ⟨y, hy, e⟩ := hA z hz
    have : (σ z - z ^ l) * (l : ℂ_[l])⁻¹ = y := by
      rw [e]; field_simp; ring
    simpa [this] using hy
  refine ⟨_, hx', ?_⟩
  field_simp
  ring

end GlobalTheory.ThBe0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprimeStatement
section
open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime : ∀ (G : GDatum) (N : ℕ), 0 < N → ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  first | (exact @GlobalTheory.GoodPrime.exists_datum) | (exact GlobalTheory.GoodPrime.exists_datum) | (intros; apply GlobalTheory.GoodPrime.exists_datum  <;> assumption)
end

