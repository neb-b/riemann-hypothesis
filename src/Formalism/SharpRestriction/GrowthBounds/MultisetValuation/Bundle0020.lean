module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0019
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveSecondVariable
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser IsLawOfLog cob at1 in3 d1 swap2 DivAB BetaHyp UnrOK)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable {p : ℕ} [hp : Fact p.Prime]

theorem sx_pair_hasSubst {τ : Type} {u v : MvPowerSeries τ (K0 p)} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (sx_two (τ := τ) hu hv)

theorem sx_subst_pair {τ τ' : Type} {b : τ → MvPowerSeries τ' (K0 p)} (hb : MvPowerSeries.HasSubst b)
    {u v : MvPowerSeries τ (K0 p)} (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    (H : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries.subst b (MvPowerSeries.subst ![u, v] H) =
      MvPowerSeries.subst ![MvPowerSeries.subst b u, MvPowerSeries.subst b v] H := by
  rw [MvPowerSeries.subst_comp_subst_apply (sx_pair_hasSubst hu hv) hb]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem sx_subst_swap {τ : Type} {u v : MvPowerSeries τ (K0 p)} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) (H : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries.subst ![u, v] (swap2 H) = MvPowerSeries.subst ![v, u] H := by
  unfold swap2
  rw [sx_subst_pair (sx_pair_hasSubst hu hv) (sx_cX 1) (sx_cX 0), MvPowerSeries.subst_X (sx_pair_hasSubst hu hv),
    MvPowerSeries.subst_X (sx_pair_hasSubst hu hv)]
  rfl

theorem biadditive_second_variable {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    Formalism.InvariantFactorPaths.G7.Simeq (d1 F (swap2 (inParam p be))) 0 := by
  have h1 := integralExp_param_of_equiv_zero p h.add2
  rw [th_inParam_sub, th_inParam_sub,
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] F) (sx_cX 0)
      (by rw [map_add (f := _), sx_cX, sx_cX, add_zero]) (sx_cX 0) (sx_law_const hF _ _ (sx_cX 1) (sx_cX 2)) (sx_eX 0)
      (by rw [sx_log_law hF _ _ (sx_cX 1) (sx_cX 2), sx_inParam_add, sx_eX, sx_eX]),
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.X 1) (sx_cX 0) (sx_cX 1) (sx_cX 0) (sx_cX 1) (sx_eX 0) (sx_eX 1),
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.X 2) (sx_cX 0) (sx_cX 2) (sx_cX 0) (sx_cX 2) (sx_eX 0) (sx_eX 2)]
    at h1
  have h2 := integralExp_rename p (![2, 0, 1] : Fin 3 → Fin 3) h1
  have hb : MvPowerSeries.HasSubst (fun k : Fin 3 =>
      (MvPowerSeries.X ((![2, 0, 1] : Fin 3 → Fin 3) k) : MvPowerSeries (Fin 3) (K0 p))) := th_ren_hasSubst _
  rw [th_ren_sub, th_ren_sub] at h2
  unfold ren at h2
  rw [sx_subst_pair hb (sx_cX 0) (sx_law_const hF _ _ (sx_cX 1) (sx_cX 2)),
    sx_subst_pair hb (sx_cX 1) (sx_cX 2), sx_subst_pair hb (sx_cX 0) (sx_cX 1), sx_subst_pair hb (sx_cX 0) (sx_cX 2),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h2
  refine equiv_zero_of_integralExp p ?_
  unfold d1 in3
  rw [sx_subst_swap (sx_law_const hF _ _ (sx_cX 0) (sx_cX 1)) (sx_cX 2), sx_subst_swap (sx_cX 0) (sx_cX 2),
    sx_subst_swap (sx_cX 1) (sx_cX 2)]
  exact h2

theorem sx_root (ζ : K0 p) (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    ∃ w : WW p, wK p w = ζ ∧ (sigW p)^[2] w = w ∧ wK p (sigW p w) = ζ ^ p := by
  have hN : 0 < p ^ 2 - 1 := by
    have := hp.out.two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have := Formalism.FG.WittVectorsCharZero.neZero_cast p 2 (by norm_num)
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (kb p) (p ^ 2 - 1)
  have hinj : Function.Injective (WittVector.teichmuller p : kb p →* WW p) := by
    intro a b h
    have := congrArg (fun x => WittVector.coeff x 0) h
    simpa [WittVector.teichmuller_coeff_zero] using this
  have h0 : IsPrimitiveRoot (wK p (WittVector.teichmuller p ξ)) (p ^ 2 - 1) :=
    (hξ.map_of_injective hinj).map_of_injective (IsFractionRing.injective (WW p) (K0 p))
  have : NeZero (p ^ 2 - 1) := ⟨hN.ne'⟩
  obtain ⟨k, _, hk⟩ := h0.eq_pow_of_pow_eq_one hζ
  have hfr : ∀ x : kb p, sigW p (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ p := by
    intro x
    unfold sigW
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have hx : (ξ ^ k) ^ (p ^ 2 - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  refine ⟨WittVector.teichmuller p (ξ ^ k), ?_, ?_, ?_⟩
  · rw [map_pow]
    show algebraMap (WW p) (K0 p) ((WittVector.teichmuller p ξ) ^ k) = ζ
    rw [map_pow]; exact hk
  · show sigW p (sigW p _) = _
    rw [hfr, map_pow, hfr, ← pow_mul, ← map_pow, ← sq]
    congr 1
    have e : p ^ 2 = (p ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hx, one_mul]
  · rw [hfr, map_pow]
    show algebraMap (WW p) (K0 p) (((WittVector.teichmuller p ξ) ^ k) ^ p) = ζ ^ p
    rw [map_pow, map_pow, ← hk]

theorem sx_conj {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) (ζ : K0 p) (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
                MvPowerSeries (Fin 2) (K0 p)), MvPowerSeries.X 1] (inParam p be))
              (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 p)),
                MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] (inParam p be)) := by
  obtain ⟨w, hw, hw2, hwp⟩ := sx_root ζ hζ
  have hζp : (ζ ^ p) ^ (p ^ 2 - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hc : ∀ (z : K0 p) (i : Fin 2), MvPowerSeries.constantCoeff
      (MvPowerSeries.C z * (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p))) = 0 := by
    intro z i; rw [map_mul, sx_cX, mul_zero]
  have hl : ∀ (z : K0 p) (i : Fin 2), z ^ (p ^ 2 - 1) = 1 →
      PowerSeries.subst (MvPowerSeries.C z * (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p))) (logF p) =
        inParam p (MvPowerSeries.C z * MvPowerSeries.X i) := by
    intro z i hz
    rw [sx_inParam_C_mul, sx_inParam_X, sx_logF_eq,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.lgF_subst_C_mul hz hp.out.two_le _ (sx_cX i)]
    unfold sx_lX
    rw [sx_logF_eq]
  have h0 := h.conj w hw2
  have h1 : Simeq p (sub2 p be (MvPowerSeries.C ζ * MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) (K0 p))
      (sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1)) := by
    rw [← hwp, ← hw]
    exact h0
  have h2 := sx_simeq_of p h1
  rw [param_substitution_pair be _ _ (MvPowerSeries.C ζ * MvPowerSeries.X 0) (MvPowerSeries.X 1) (hc ζ 0) (sx_cX 1) (hc ζ 0) (sx_cX 1)
      (hl ζ 0 hζ) (sx_eX 1),
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1) (sx_cX 0) (hc _ 1) (sx_cX 0) (hc _ 1)
      (sx_eX 0) (hl _ 1 hζp)] at h2
  exact h2

theorem sx_betaHyp {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    BetaHyp p F (inParam p be) :=
  ⟨sx_divAB p h, biadditive_first_variable hF h, biadditive_second_variable hF h, fun ζ hζ => sx_conj h ζ hζ⟩

theorem sx_unrOK (h2 : 2 < p) : UnrOK (K0 p) p (sigK p).toRingHom :=
  ⟨hp.out, h2, sx_norm_p p, Formalism.InvariantFactorPaths.G7.WModel.abv_value p, sx_sig_frob p⟩

theorem restBeta (p : ℕ) [hp : Fact p.Prime] : RestBeta p := by
  intro h5 _ be hbe
  have := sx_ultra p
  have := Formalism.InvariantFactorPaths.G7.WModel.complete p
  obtain ⟨F, hF⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (K0 p) p hp.out (sx_norm_p p)).1
  obtain ⟨ζ0, hζ0⟩ := Formalism.FG.witt_teichmuller_root p 2 (by norm_num)
  obtain ⟨c, hc, hcc, hS⟩ := Formalism.InvariantFactorPaths.G7.Top.betaIsG (K0 p) p (sigK p).toRingHom (sx_unrOK (by omega))
    ⟨wK p ζ0, hζ0.map_of_injective (IsFractionRing.injective (WW p) (K0 p))⟩ F hF (inParam p be) (sx_betaHyp hF hbe)
  obtain ⟨w, rfl⟩ := (sx_norm_le_one_iff p c).1 hc
  have hs : ∀ x : WW p, (sigK p).toRingHom (algebraMap (WW p) (K0 p) x) = algebraMap (WW p) (K0 p) (sigW p x) := by
    intro x
    rw [sx_sigK_eq, Formalism.InvariantFactorPaths.G7.WModel.sig_coe]
    rfl
  rw [hs] at hS hcc
  rw [hs] at hcc
  refine ⟨w, IsFractionRing.injective (WW p) (K0 p) hcc, ?_⟩
  exact integralExp_of_equiv p hS

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EbWMapDomain
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {σ κ τ τ' K : Type} [Field K]

def eb_w (F : MvPowerSeries σ K) (n : σ →₀ ℕ) : K :=
  (∏ x ∈ n.support, ((n x).factorial : K)) * MvPowerSeries.coeff n F

def eb_J (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) : MvPolynomial τ K :=
  ∑ n ∈ Q.support, eb_w F n • AddMonoidAlgebra.coeff Q n

theorem eb_J_subset (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : eb_J F Q = ∑ n ∈ S, eb_w F n • AddMonoidAlgebra.coeff Q n := by
  unfold eb_J
  apply Finset.sum_subset h
  intro n _ hn
  rw [MvPolynomial.notMem_support_iff.1 hn, smul_zero]

theorem eb_applyD (P : MvPolynomial σ (MvPolynomial τ ℤ)) (F : MvPowerSeries σ K) :
    applyD P F = eb_J F (MvPolynomial.map (MvPolynomial.map (Int.castRingHom K)) P) := by
  rw [eb_J_subset F _ P.support (MvPolynomial.support_map_subset _ _)]
  unfold applyD eb_w
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map]

theorem eb_w_mapDomain (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K) (n : κ →₀ ℕ) :
    eb_w F (n.mapDomain ε) = eb_w (resV ε F) n := by
  classical
  unfold eb_w
  rw [Finsupp.mapDomain_support_of_injective hε, Finset.prod_image (fun a _ b _ h => hε h)]
  congr 1
  apply Finset.prod_congr rfl
  intro y _
  rw [Finsupp.mapDomain_apply_of_injective hε]

theorem eb_J_rename (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K)
    (Q : MvPolynomial κ (MvPolynomial τ K)) : eb_J F (MvPolynomial.rename ε Q) = eb_J (resV ε F) Q := by
  classical
  unfold eb_J
  rw [MvPolynomial.support_rename_of_injective hε,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hε h)]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_rename_mapDomain ε hε, eb_w_mapDomain ε hε]

theorem eb_J_map (φ : τ' → τ) (G : MvPowerSeries κ K) (Pc : MvPolynomial κ (MvPolynomial τ' K)) :
    eb_J G (MvPolynomial.map (MvPolynomial.rename φ : MvPolynomial τ' K →ₐ[K] MvPolynomial τ K).toRingHom Pc) =
      MvPolynomial.rename φ (Formalism.DworkPowerSeriesWeights.jetPairPoly Pc G) := by
  rw [eb_J_subset G _ Pc.support (MvPolynomial.support_map_subset _ _)]
  unfold Formalism.DworkPowerSeriesWeights.jetPairPoly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.rename_C, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 2
  unfold eb_w Formalism.DworkPowerSeriesWeights.mfact Finsupp.prod
  rw [Nat.cast_prod]

end Gen

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_phi (v : X.Pl) (j : ℕ) : ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j) → X.FrI j :=
  fun y => ⟨v, ((ea_e X v).symm y.1, y.2.1.val, y.2.2)⟩

theorem eb_phi_inj (v : X.Pl) (j : ℕ) : Function.Injective (eb_phi X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [eb_phi, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, Fin.ext h2, h3]

theorem eb_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

theorem eb_fac (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) (s : ea_S X v) (c : Fin (ea_colN X v j s)) :
    MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
      (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
      (Matrix.of fun (r r' : Fin (ea_hts X v j s c)) =>
        (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X
            (s, (⟨r.val, lt_of_lt_of_le r.isLt (ea_hp X v j s c)⟩ : Fin (NN X.G.P.m X.t j)), a)) *
          MvPolynomial.X (s, a, ea_Ic X v j I s c r') :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K'))).det) =
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.colFac j I v ((ea_e X v).symm s) c.val) := by
  unfold Sys.colFac
  rw [RingHom.map_det, AlgHom.map_det, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun r r' => ?_)
  change _ = MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (∑ a : Fin (NN X.G.P.m X.t j),
    MvPolynomial.C (MvPolynomial.X (⟨v, ((ea_e X v).symm s, r.val, a)⟩ : X.FrI j)) *
      MvPolynomial.X (⟨v, ((ea_e X v).symm s, a, I v ((ea_e X v).symm s) c.val r'.val)⟩ : X.ZA j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.rename_C, MvPolynomial.rename_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NeNeedPrice
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def nd_NeedSize : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D),
    Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D, nc_Size D L Y u w hg t0 j

def PriceBound (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem nc_need3_of (C₀ : ℝ) (hS : nd_NeedSize) (hP : PriceBound C₀) : nc_Need3 C₀ :=
  fun D L X Y K _ _ h3 h4 hSz hT hL u w hg hlog t0 ht0 j hj =>
    ⟨hS D L X Y hSz hT hL u w hg hlog t0 ht0 j hj, hP D L X Y K h3 h4 hSz hT hL u w hg hlog t0 ht0 j hj⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmRestNormOfPlace
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_restNorm (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : ea_RestNorm Y := by
  obtain ⟨K', nf, ac, um, -, hpn, hball, vp, hvp⟩ := nm_ext Y h
  letI : Algebra (K0 p) K' := ((algebraMap Y.Kc K').comp (algebraMap (K0 p) Y.Kc)).toAlgebra
  haveI : IsScalarTower (K0 p) Y.Kc K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨ea_NormExt.mk K' vp hvp hpn hball⟩

theorem nm_restNorm_of_place (Y : Pend X) (v : X.Pl) : ea_RestNorm Y := nm_restNorm Y (nm_pinv_of_place Y v)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

