module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDet
section
noncomputable section

namespace GlobalTheory.StabMove

section Adelic

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}


set_option maxHeartbeats 1000000 in
theorem exists_carries {V W : HSp D} (hV : V = W) {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {U : Unf Xo c σ r}
    {dict : GA D V → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k))
    (hL : DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    {s : Dw.La →ₗ[𝓞 D.host.E] Dw.La} {κ : GA D W}
    (hκ : Induces W l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) s κ) (h : GA D W) :
    (Formalism.IndefR.FWT.castDict hV dict h).2 ∈ (U.X (Formalism.IndefR.FWT.castDict hV dict h).1).dom ∧
      ∃ δ, ∃ hc : Carries φ s (Formalism.IndefR.FWT.castDict hV dict h).1 (Formalism.IndefR.FWT.castDict hV dict (h * κ)).1 δ,
        (Formalism.IndefR.FWT.castDict hV dict (h * κ)).2 =
          lact δ (castFr hc.mt.psi (Formalism.IndefR.FWT.castDict hV dict h).2) := by
  subst hV
  subst hr
  change DictLat U V rfl dict io e F ik φ th x₀ at hL
  change Induces V l io s κ at hκ
  refine ⟨hdom h, ?_⟩
  change ∃ δ, ∃ hc : Carries φ s (dict h).1 (dict (h * κ)).1 δ,
      (dict (h * κ)).2 = lact δ (castFr hc.mt.psi (dict h).2)
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0 := fun k k' => (hW k).2.trans (hW k').2.symm
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := _root_.GlobalTheory.Member.Arch.archM_spec D V θ hθ
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * κ)
  have e₀ : γ₂ * (h * κ) = γ₂ * γ₁⁻¹ * (γ₁ * h) * κ := by group
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
  obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) s (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hL.1.1 _) (hL.1.1 _) δ hδu hδf hκ.2.1 hκ.2.2
    ⟨hΛ₁, hm₁⟩ (by rw [← e₀]; exact ⟨hΛ₂, hm₂⟩)
  have hmt : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
    refine ⟨Finset.ext fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm,
      hxi _ _, fun u v => by rw [hG, hG]; exact hδu u v, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨v, hv⟩
      rw [show v = (φ (dict h).1 a : Fin V.rank → D.host.E) by rw [ha], ← hgam]
      exact (φ _ _).2
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨_, hv⟩
      obtain ⟨b, rfl⟩ := gam.surjective a
      have h1 := congrArg (fun u => (δ⁻¹).1 *ᵥ u) ((hgam b).symm.trans (congrArg Subtype.val ha))
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
      rw [← h1]
      exact (φ _ _).2
  refine ⟨δ, ⟨hmt, by rw [hG, hG], gam, e₁, t₁, hgam⟩, funext fun τ => ?_⟩
  change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hmt.mem τ⟩
  rw [hf₁, hf₂, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1),
    GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ ⟨τ.1, hmt.mem τ⟩) (hθ τ.1), e₀, (hAr τ.1).2.1, (hAr τ.1).2.1,
    (hAr τ.1).2.2.1 κ hκ.1, hδa τ.1 _ (hθ τ.1), Matrix.mul_one, ← Matrix.mul_assoc]
  rfl


set_option maxHeartbeats 1000000 in
theorem rdU_eq_of_carries_self (T : CoreJ D) (hT : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)}
    {F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1)}
    {ik : (T.U j σ).Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ}
    (hP : HasPeriods φ) {G : Type} [Group G]
    {lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)}
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (a : G) {w : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f : Rul (T.Q.Xo j) T.Q.c} (hf : f ∈ sec (T.Q.Xo j) T.Q.c w n)
    (p q : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r) (hp : p.2 ∈ ((T.U j σ).X p.1).dom) {δ : GL (Fin D.R.r) D.host.E}
    (hc : Carries φ (lev a).1 p.1 q.1 δ) (hq : q.2 = lact δ (castFr hc.mt.psi p.2)) (hpq : q.1 = p.1) :
    rdU (T.U j σ) (actLev T.Q.c lev a f) p.1 p.2 = rdU (T.U j σ) f q.1 q.2 := by
  obtain ⟨k, x⟩ := p
  obtain ⟨k', x'⟩ := q
  dsimp only at hp hc hq hpq ⊢
  subst hpq
  rw [hq]
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hU := hT.unf _ hj σ hσ
  have hr := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  obtain ⟨hneg, φD, h1, h2, h3⟩ := GlobalTheory.GeoLevel.model_space_of_lawsJ D T hT j hj σ hσ k'
  obtain ⟨h4, hdet⟩ := GlobalTheory.GeoLevel.four_dvd_finrank_and_det_eq_pm_one D
  obtain ⟨ρ, ν, hρ, hν, -⟩ := mvPt_spec hact.total a ((T.U j σ).un k' ⟨x, hp⟩)
  refine _root_.GlobalTheory.GeoLevel.rdU_move_eq D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU
    k' φD h1 h2 h3 hneg δ hc.mt ((hdet _ _ δ hc.mt).imp_right fun h => ⟨h, h4⟩) ρ ν hν.1
    (fun z y' hm => move_eq hσ hr hA hP hc hν z hm) w n hD f hf _
    (actL_mem _ _ _ _ hact.total hact.nat hact.bor _ a hf) (fun y y' hm => ?_) x hp
  have m1 := mvPt_spec hact.total a y
  have m2 : levActR (Xo := T.Q.Xo j) (c := T.Q.c) lev a y y' := ⟨ρ, ν, hρ, hν, hm⟩
  exact (evalAt_actL hact (hT.evalWD _ hj) frMap_trans_id a hf.1 y).trans
    (evalAt_congr_id (hT.evalWD _ hj) frMap_trans_id hf.1 (hact.func a _ y _ _ m1 m2) (hact.func a _ y _ _ m2 m1))

end Adelic

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem phiAt_actLev_of_comp_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR ht hpb hO i σ hσ hV g k hk y hy p hp f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj σ hσ
  obtain ⟨hr, g₀, e, F, ik, φ, th, hio, -, hth, hL⟩ := h.adPin _ hj σ hσ
  obtain ⟨_, hW⟩ := h.modelW _ hj σ hσ
  have hU := h.unf _ hj σ hσ
  have hK := h.levelK _ hj σ hσ
  rw [← h.pins.2.1.1] at hK
  obtain ⟨hio', hK'⟩ := GlobalTheory.DictMove.cast_level hV hK (T.iota _) hr (rank_Wc i) hio
  obtain ⟨k₀, hk₀, hs⟩ := (hO i).2.lift.lev g
  have hI := GlobalTheory.DictMove.induces_of_lift hio' (hR.βW i)
    (fun k hk => hK' k ((GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hR ht hpb i σ hσ hV k).1 hk)) hk₀ hk hs
  obtain ⟨hdom, δ, hc, hq⟩ := exists_carries hV hr (rank_Wc i) (T.iota _) hU hW hL hth hd.2.2.2.1 hI p
  have key := rdU_eq_of_carries_self T h hj hσ hL.1.2 (hO i).2.act.1 g (dom_wtA (κ i))
    ((mem_cusp _ _ _ _ _ _).1 hf).1 _ _ hdom hc hq hp
  obtain ⟨y', hy', hy1⟩ := GlobalTheory.GeoLevel.mu_lift hR ht hpb i hσ hV hk
  obtain rfl : y = y' := (algebraMap T.Q.c.F D.what₂.LL).injective (D.what₂.embLL.injective (hy.trans hy'.symm))
  have hmu := h.muUnit _ hj σ hσ
  rw [GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.castDict_mu_mul hmu.1, ← mul_assoc,
    mul_left_comm (σ y), hy1, mul_one]
  unfold GlobalTheory.GeoLevel.frameRead
  rw [key]

end GlobalTheory.StabMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntriesLeFloorHeight
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem wts_U_le_h0_of_large : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  intro D L P5 j τ hL hv a ha
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hS := L.Sc_pos
  have hη := L.etaSz_pos
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    exact div_pos (mul_pos x0 (Real.exp_pos _)) (Real.exp_pos _)
  have hn : (1 : ℝ) ≤ D.R.n := by unfold Ranks.n; exact_mod_cast (Nat.succ_le_of_lt (Formalism.HC.Frame.ord_pos _) : 1 ≤ _)
  have hU0 := U_nonneg L j τ 0 (by have := rank_eq j; omega)
  have hUa := liftWeightCombinatorialData_U_le_U_zero L j τ a ha
  have hv0 := hv.1 0 (by omega)
  have hcl := L.cloud_v τ ⟨0, by omega⟩
  have hc := c_le L j τ hv

  have ePb : (parOf L j).b = L.sc.b := rfl
  have eh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hbb' := hL.bb'
  have htop := hL.top_le
  simp only [parOf] at hbb' htop
  change 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' < L.sc.b at hbb'

  have hm1 : 1 ≤ D.R.m := by omega
  have key : wj D D.R.m τ ≤ L.sc.b + L.etaSz + 1 ∨
      wj D D.R.m τ ≤ L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz := by
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have hw := (L.win_top D.R.m hm1 le_rfl τ ⟨t, ht1⟩ ht2.symm).2
      have hbt := P5.bT_le ⟨t, ht1⟩
      have hr := P5.rho_le
      unfold LevelStarExponents.rhoP at hr
      have hLa : 0 < L.LaG := by
        have h := P5.S_le
        by_contra hc'
        push_neg at hc'
        have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' hb0.le) (by positivity)
        linarith
      have hNs : 0 ≤ LevelStarExponents.Nstar L := by
        unfold LevelStarExponents.Nstar Scale.delta1; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have h6 : 0 ≤ LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by positivity
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        rw [hx2] at hr
        linarith
      have h7 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h8 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / L.sc.x ^ 2 * L.sc.b' :=
        mul_le_mul_of_nonneg_right h5 hb0.le
      right
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' + L.sc.b' / L.sc.x + 1 / L.sc.x ^ 2 * L.sc.b' := by ring
      rw [this]
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · exact Or.inl (L.win_thick D.R.m hm1 le_rfl τ h2).2
      · have hw := (L.win_thin D.R.m hm1 le_rfl τ ⟨(D.eTau τ).2, h1, h2⟩).2
        right
        have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := by
          unfold Scale.w''
          rw [div_le_iff₀ (by positivity)]
          have hxn : 1 ≤ L.sc.x * (D.R.n : ℝ) := by nlinarith
          have := mul_le_mul_of_nonneg_left hxn hb0.le
          linarith
        have hpos : 0 ≤ L.sc.b' * (1 / L.sc.x + 1 / L.sc.x ^ 2) := by positivity
        nlinarith
  have hU0h : ((wts L j).U (parOf L j) τ 0 : ℝ) ≤ (parOf L j).h := by
    rw [eh]
    rcases key with h | h
    · nlinarith
    · have h2b : 2 * L.sc.b' < L.sc.b := by
        have : 2 * L.sc.b' ≤ 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' := by
          have : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.t : ℝ) := by nlinarith
          nlinarith
        linarith
      linarith
  have hfl : ((wts L j).U (parOf L j) τ 0).toNat ≤ Formalism.CohomologicalDescent.ShortWeightBounds.h0 (parOf L j) := by
    unfold Formalism.CohomologicalDescent.ShortWeightBounds.h0
    apply Nat.le_floor
    have : (((wts L j).U (parOf L j) τ 0).toNat : ℝ) = ((wts L j).U (parOf L j) τ 0 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hU0
    rw [this]; exact hU0h
  omega

end GlobalTheory.ExpTie.Lift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntryValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift
variable {D : D7}

theorem U_sub_c_eq_w (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ =
      (((lamL j τ).w ⟨a, ha⟩ : ℤ) : ℝ) + ((Vc D j).rank : ℝ) / 2 - a := by
  have h1 := lamT_of_lt j τ a ha
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  show ((Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a : ℤ) : ℝ) - cT j τ = _
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN cT
  push_cast
  rw [h2]
  ring

theorem valsAt_of_isLamPrime : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  intro D L j τ h
  obtain ⟨hj, W, hk, hm, ht, hJ, he, hv, hb, hw⟩ := h
  obtain ⟨k, m, t, J, e, v, b⟩ := W
  simp only at hk hm ht hJ he hv hb
  subst hk hm ht hJ
  have hN := rank_eq j
  have hK := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hjm := j.2
  have hrk : ((Vc D j).rank : ℚ) = (D.R.k : ℚ) + D.R.m + D.R.t - 1 := by
    rw [hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hmj : ((D.R.m - ((j : ℕ) + 1) : ℕ) : ℚ) = (D.R.m : ℚ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk1 : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr1 : D.R.k + D.R.m - 1 + D.R.t = (Vc D j).rank := by omega
  have hp : D.R.k + ((j : ℕ) + 1) - 1 = D.R.k + j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hal : a < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ a hal]
    have hq := hw ⟨a, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj] at hq
    have hv' : ((v (a + 1 + 1) : ℤ) : ℚ) = (D.hc τ).v ⟨a, ha⟩ := hv ⟨a, ha⟩
    have hQ : (((lamL j τ).w ⟨a, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - a = (D.hc τ).v ⟨a, ha⟩ := by
      rw [hq, ← hv']; push_cast; ring
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this
    exact this
  · intro i hi
    have hal : D.R.k - 1 + i < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj, show D.R.k - 1 + (i : ℕ) + 1 - (D.R.k - 1) = (i : ℕ) + 1 by omega,
      show D.R.k - 1 + (i : ℕ) + 1 = D.R.k + i by omega] at hq
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, hk1]
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this
  · intro s hs
    have hal : D.R.k + j + s < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : D.R.k + ↑j + s + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t := by omega
    simp only [c3, if_true] at hq
    rw [hp, hmj] at hq
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k + j + s : ℕ) : ℚ) =
        -(D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ + ((D.R.t : ℚ) - 1) / 2 - s := by
      push_cast at hq he ⊢
      linarith
    have hwj : wj D ((j : ℕ) + 1) τ = (((D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dite_eq_left hj.2]
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    rw [hwj]
    push_cast at this ⊢
    linarith
  · intro i hi
    have hal : D.R.k - 1 + i + D.R.t < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : ¬ (D.R.k - 1 + (i : ℕ) + D.R.t + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t) := by omega
    simp only [c3, if_false] at hq
    rw [show D.R.m - ((j : ℕ) + 1) + 1 - (D.R.m - ((j : ℕ) + 1) + 1 - (D.R.k - 1 + (i : ℕ) + D.R.t + 1 - (D.R.k + ((j : ℕ) + 1) - 1) - D.R.t))
        = (i : ℕ) - j by omega] at hq
    rw [show (j : ℕ) + 1 + ((i : ℕ) - j) = (i : ℕ) + 1 by omega, hp, hmj] at hq
    have hij : (((i : ℕ) - (j : ℕ) : ℕ) : ℚ) = (i : ℚ) - j := by
      rw [Nat.cast_sub (by omega)]
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i + D.R.t : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, Nat.cast_add, hk1]
      rw [hij] at hq
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoNonThickPlaceCentreWidth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

variable {D : Formalism.BasicNotions.D7}

theorem other_of_not_thick (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau)
    (hv : GlobalTheory.ExpTie.Lift.ValsAt L j τ) (hT : τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2) :
    ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  classical
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m

  have hw : ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ L.Sc + (GlobalTheory.ExpTie.Lift.wts L j).c τ := by
    have hU := U_last L j τ
    have h0 := hv.1 0 (by omega)
    have hcv := (L.cloud_v τ ⟨0, by omega⟩).2
    have hwd : (GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ = (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 := by
      show (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 - (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ ((Vc D j).rank - 1) = _
      rw [hU, sub_zero]
    rw [hwd]
    linarith
  have hc := c_le L j τ hv
  have hnt : (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces := by
    intro h
    apply hT
    simp only [wts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have he : (GlobalTheory.ExpTie.Lift.wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
      unfold Host.topPlaces at htop
      simpa using htop
    have x1 := L.sc.one_lt_alt
    have x0 : 0 < L.sc.x := by linarith
    have hb0 : 0 < L.sc.b' := by
      have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
      have hb : 0 < L.sc.b := by unfold Scale.b; positivity
      unfold Scale.b' Scale.a
      positivity
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    have hLa : 0 < L.LaG := by
      have h1 := P5.S_le
      have h2 := L.Sc_pos
      by_contra hn
      push_neg at hn
      have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hb0.le) hk0.le
      linarith
    have hbT : ((L.bT ⟨t, ht1⟩ : ℝ)) ≤ L.sc.b' * (1 + 1 / L.sc.x ^ 2) := by
      have h1 := P5.bT_le ⟨t, ht1⟩
      have h2 := P5.rho_le
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      unfold LevelStarExponents.rhoP at h2
      rw [hx2] at h2
      have hq : 0 ≤ 1 / L.sc.x ^ 2 := by positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        linarith
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h6 := mul_le_mul_of_nonneg_right h5 hb0.le
      nlinarith
    have a := L.bT_ge ⟨t, ht1⟩
    have wj1 := L.win_top ((j : ℕ) + 1) (by omega) (by omega) τ ⟨t, ht1⟩ ht2.symm
    have wjm := L.win_top D.R.m (by omega) le_rfl τ ⟨t, ht1⟩ ht2.symm
    refine ⟨⟨(L.bT ⟨t, ht1⟩ : ℝ), a, hbT, ?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' * (1 + 1 / L.sc.x ^ 2) + L.sc.b' / L.sc.x := by ring
      linarith [wjm.2]
  · right
    have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, htop, hnt⟩
    have wj1 := L.win_thin ((j : ℕ) + 1) (by omega) (by omega) τ hthin
    have wjm := L.win_thin D.R.m (by omega) le_rfl τ hthin
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.w'' D.R.n + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      linarith [wjm.2]

end GlobalTheory.ExpTie.Lift
end

