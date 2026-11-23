module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelSumOfClassData
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GShiftRowGenMonomial
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LambdaIndexTwo
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem lambda_index_one (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 1 = G.P.lam0 v s ⟨0, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨le_rfl, by omega⟩]

theorem lambda_index_two (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 2 = G.P.lam0 v s ⟨1, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨by omega, by omega⟩]

theorem nc_w_ge (s : Fin (G.P.n' v)) (j : ℕ) (hj : 1 ≤ j) : Fl.w v 1 s ≤ Fl.w v j s := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih => exact le_trans ih (Fl.w_mono v s l hl)

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem vt_nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  exact Int.toNat_le_toNat (by have := h hab; omega)

theorem vt_deltaLTw_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    deltaLTw O Kf m lam g ≤ nablaLTw O Kf m lam g := by
  unfold deltaLTw nablaLTw
  apply Submodule.map_mono
  unfold deltaL nablaL
  apply Submodule.comap_mono
  apply Submodule.map_mono
  exact weylLeDual O (m + 1) (m + 1) le_rfl (nuOf lam) (vt_nuOf_antitone hlam)

theorem lowest_invariant_le_delta {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) ≤ deltaLTw O Kf m lam g := by
  unfold Dl0
  rw [if_pos hlam]
  exact iInf₂_le g ⟨hg, rfl⟩

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def vt_G (P : Places p O Kf) : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := PEmpty
  lev := fun x => x.elim
  e := 0

theorem vt_HtenW_le (P : Places p O Kf) (v : Fin P.nV) (Lv : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
    (hLv : IsLattice (P.W v) Lv) :
    ∀ z ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val Lv), z ∈ Vsp Kf (P.lam0 v) := by
  obtain ⟨g, hg, rfl⟩ := hLv
  have hle : HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) ≤
      (Vsp Kf (P.lam0 v)).restrictScalars O := by
    unfold HtenW tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone (P.lam0 v) (P.dom v) s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    have e : extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g) = colSpan O (la_tw (P.ι v) (P.σ v) s.val g) :=
      la_extO_G (vt_G P) v s.val g
    rw [e] at h1
    have hd := la_tw_det (P.ι v) (P.σ v) s.val g hg
    exact la_nablaLTw_le _ _ _ hd _ (vt_deltaLTw_le O Kf _ _ hanti _ (lowest_invariant_le_delta _ _ hanti _ hd h1))
  exact fun z hz => hle hz

theorem vt_HtupW_le (P : Places p O Kf) (L : P.Tup) (hL : P.IsLatTup L) : ∀ z ∈ P.HtupW L, z ∈ P.Vtup := by
  have hle : P.HtupW L ≤ P.Vtup.restrictScalars O := by
    unfold Places.HtupW Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, fun v => vt_HtenW_le P v (L v) (hL v) _ (hF v), rfl⟩
  exact fun z hz => hle hz

end Formalism.MainNotions.FormalGroupSystem.Pf

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem vt_FQ {p : ℕ} [Fact p.Prime] (X : Sys p) {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j)
    (L : (X.Pj j).Tup) : F c L ∈ (X.Pj j).Vtup := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    have h := (mem_Int_iff X j x).1 hx
    by_cases hL : (X.Pj j).IsLatTup L
    · exact vt_HtupW_le (X.Pj j) L hL _ (h.1 c L hL)
    · rw [h.2.1 c L hL]; exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmPinvOfPlace
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_pinv_of_eO (Y : Pend X) (he : 0 < X.eO) : (p : Y.Kc)⁻¹ ∉ Y.Oc := by
  intro hmem
  have hinj := algebraMap_inj Y he
  have hpO : (p : X.G.O) ≠ 0 := fun h0 =>
    pow_ne_zero _ X.unif.ne_zero (X.eO_spec.eq_zero_iff.mp h0)
  have hpK : (p : X.G.Kf) ≠ 0 := by
    have := (map_ne_zero_iff _ hinj).mpr hpO
    rwa [map_natCast] at this
  have h1 : algebraMap X.G.Kf Y.Kc ((p : X.G.Kf)⁻¹) ∈ Y.Oc := by
    rwa [map_inv₀, map_natCast]
  obtain ⟨a, ha⟩ := (mem_intK (X := X)).mp ((Y.Oc_K _).mp h1)

  have h1eq : (p : X.G.O) * a = 1 := hinj (by
    rw [map_mul, ha, map_natCast, mul_inv_cancel₀ hpK, map_one])
  have hpu : IsUnit (p : X.G.O) := IsUnit.of_mul_eq_one _ h1eq
  exact X.unif.not_isUnit
    ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp he)).mp (X.eO_spec.isUnit_iff.mp hpu))

theorem nm_pinv_of_place (Y : Pend X) (v : X.Pl) : (p : Y.Kc)⁻¹ ∉ Y.Oc :=
  nm_pinv_of_eO Y (eO_pos X v)

theorem nm_hyp (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : nm_Hyp Y.Oc p :=
  ⟨hp.out.one_lt, Y.Oc_val, Y.Oc_rank1, h⟩

theorem nm_ext (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra Y.Kc K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ‖(p : K')‖ = (p : ℝ)⁻¹ ∧ (∀ x : Y.Kc, ‖algebraMap Y.Kc K' x‖ ≤ 1 ↔ x ∈ Y.Oc) ∧
      ∃ vp : K', vp ^ (p ^ 2 - 1) = (p : K') := by
  have hH := nm_hyp Y h
  have hc : 1 < nm_abs hH ((p : Y.Kc)⁻¹) := by
    rw [map_inv₀]
    show 1 < (nm_N Y.Oc p (p : Y.Kc))⁻¹
    rw [nm_N_p hH, inv_inv]
    exact nm_pR hH
  obtain ⟨K', i1, i2, hu, hac, hn⟩ :=
    nm_extG (nm_abs hH) (fun x y => nm_N_add hH x y) ((p : Y.Kc)⁻¹) hc
  refine ⟨K', i1, i2, hu, hac, ?_, ?_, ?_⟩
  · have := hn (p : Y.Kc)
    rw [map_natCast] at this
    exact this.trans (nm_N_p hH)
  · intro x
    rw [hn x]
    exact nm_N_le_one hH x
  · have h2 : 2 ≤ p := hp.out.two_le
    have hpos : 0 < p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    exact IsAlgClosed.exists_pow_nat_eq (p : K') hpos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem tm_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  have hres := (P.setting v).res_card
  have hfin : Finite (P.W v ⧸ Ideal.span {(p : P.W v)}) := by
    apply Nat.finite_of_card_ne_zero
    rw [hres]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  exact ef_edges_finite_gen p (P.n' v) i (P.m + 1) hfin L

def tmE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (tm_fin P v i L).toFinset

theorem tm_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ tmE P v i (L v), F (Function.update L v L'') := by
  show (∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
      (_ : L'' ∈ {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L v⟩}),
      F (Function.update L v L'')) = _
  exact finsum_mem_eq_finite_toFinset_sum _ (tm_fin P v i (L v))

theorem tm_zero (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (hF : ∀ L, ¬ P.IsLatTup L → F L = 0) (L : P.Tup)
    (hL : ¬ P.IsLatTup L) : P.Tminus v i F L = 0 := by
  rw [tm_eq]
  apply Finset.sum_eq_zero
  intro L'' hL''
  apply hF
  intro hlat
  apply hL
  show ∀ w, IsLattice (P.W w) (L w)
  intro w
  by_cases hw : w = v
  · subst hw
    have he : IsEdge p (P.n' w) i ⟨L'', L w⟩ := (tm_fin P w i (L w)).mem_toFinset.mp hL''
    exact he.2.1
  · simpa [Function.update, hw] using hlat w

theorem smul_update (C : Level P) (γ : C.Γ) (v : Fin P.nV) (L : P.Tup)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    C.smul γ (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) =
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (C.smul γ L) v (A.map (nt_phi (P.W v) (C.act v γ))) := by
  funext w
  by_cases hw : w = v
  · subst hw
    simp [Function.update, Level.smul, nt_phi]
  · simp [Function.update, hw, Level.smul, nt_phi]

theorem tm_equiv (C : Level P) (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp)
    (hF' : ∀ (γ : C.Γ) (L : P.Tup), F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L)) (γ : C.Γ) (L : P.Tup) :
    P.Tminus v i F (C.smul γ L) = (C.χ γ : O) • C.actX γ (P.Tminus v i F L) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tm_eq, tm_eq, map_sum, Finset.smul_sum]
  symm
  apply Finset.sum_nbij' (fun A => A.map (nt_phi (P.W v) (C.act v γ)))
    (fun A => A.map (nt_phi (P.W v) (C.act v γ)⁻¹))
  · intro A hA
    have hA' : IsEdge p (P.n' v) i ⟨A, L v⟩ := (tm_fin P v i (L v)).mem_toFinset.mp hA
    exact (tm_fin P v i (C.smul γ L v)).mem_toFinset.mpr (nt_edge_map p (P.n' v) i (C.act v γ) A (L v) hA')
  · intro B hB
    have hB' : IsEdge p (P.n' v) i ⟨B, (L v).map (nt_phi (P.W v) (C.act v γ))⟩ :=
      (tm_fin P v i (C.smul γ L v)).mem_toFinset.mp hB
    have h2 := nt_edge_map p (P.n' v) i (C.act v γ)⁻¹ B ((L v).map (nt_phi (P.W v) (C.act v γ))) hB'
    rw [nt_map_inv] at h2
    exact (tm_fin P v i (L v)).mem_toFinset.mpr h2
  · intro A _
    exact nt_map_inv _ _
  · intro B _
    exact nt_map_inv' _ _
  · intro A _
    have h := hF' γ (Function.update L v A)
    rw [smul_update] at h
    exact h.symm

end Gen

variable {p : ℕ} [Fact p.Prime]

theorem restTmEquiv (X : Sys p) : RestTmEquiv X := by
  intro J v i F hF
  refine ⟨fun c L hL => ?_, fun c γ L => ?_⟩
  · exact tm_zero (X.Pj J) (X.vJ J v) i (F c) (fun L' hL' => hF.1 c L' hL') L hL
  · exact tm_equiv (X.Pj J) (X.Lv.lev J c) (X.vJ J v) i (F c) (fun γ' L' => hF.2 c γ' L') γ L

theorem formB (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) : FormB X Y :=
  formB_of D Y hA (restTmEquiv X)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TsumRatTail
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

theorem tsum_rat_tail (g : ℕ → ℚ) (hs : Summable (fun e => (g e : ℝ))) (E N : ℕ) (Q : ℚ) (hQ1 : 1 < Q)
    (h4 : ∀ e, E ≤ e → g (e + N) = g e / Q) : ∃ q : ℚ, ∑' e, (g e : ℝ) = q := by
  have hsE : Summable (fun i => (g (i + E) : ℝ)) := (summable_nat_add_iff E).2 hs
  have h1 := hsE.sum_add_tsum_nat_add N
  have h2 : ∀ i, (g (i + N + E) : ℝ) = (g (i + E) : ℝ) / Q := by
    intro i
    rw [show i + N + E = i + E + N by omega, h4 (i + E) (by omega)]
    push_cast
    try rfl
  simp only [h2] at h1
  rw [tsum_div_const] at h1
  have h0 := hs.sum_add_tsum_nat_add E
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hQ1' : (Q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hT : ∑' i, (g (i + E) : ℝ) = (∑ i ∈ range N, (g (i + E) : ℝ)) * Q / (Q - 1) := by
    rw [eq_div_iff hQ1']
    field_simp at h1
    linarith
  refine ⟨∑ i ∈ range E, g i + (∑ i ∈ range N, g (i + E)) * Q / (Q - 1), ?_⟩
  rw [← h0, hT]
  push_cast
  ring

def fqT (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) : ℚ :=
  if 2 * e + 1 ∈ Ds then 0 else max ((α : ℚ) / (P : ℚ) ^ (2 * e + 1) - (c e : ℚ)) 0

theorem fqT_cast (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) :
    (if 2 * e + 1 ∈ Ds then (0 : ℝ) else max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) =
      (fqT P α c Ds e : ℝ) := by
  unfold fqT
  split_ifs
  · simp
  · push_cast
    try rfl

theorem tsum_rat (P N : ℕ) (hP : 2 ≤ P) (hN : 0 < N) (α : ℤ) (c : ℕ → ℤ) (hc : ∀ e, c (e + N) = c e)
    (Ds : Finset ℕ) :
    ∃ q : ℚ, ∑' e : ℕ, (if 2 * e + 1 ∈ Ds then (0 : ℝ) else
      max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) = q := by
  simp_rw [fqT_cast]
  by_cases hs : Summable (fun e => (fqT P α c Ds e : ℝ))
  swap
  · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs]; simp⟩
  have hP0 : (0 : ℚ) < P := by exact_mod_cast (by omega : 0 < P)
  have h1 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 2 * e + 1 ∉ Ds := fun e he hmem => by
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  have h2 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ)| * 2 < (P : ℚ) ^ (2 * e + 1) := by
    intro e he
    have a1 : α.natAbs * 2 < P ^ (2 * e + 1) :=
      calc α.natAbs * 2 < 2 * e + 1 := by omega
        _ < 2 ^ (2 * e + 1) := Nat.lt_two_pow_self
        _ ≤ P ^ (2 * e + 1) := Nat.pow_le_pow_left hP _
    have a2 : ((α.natAbs : ℕ) : ℚ) = |(α : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← a2]
    exact_mod_cast a1
  have h2' : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ) / (P : ℚ) ^ (2 * e + 1)| < 1 / 2 := by
    intro e he
    have hpos : (0 : ℚ) < (P : ℚ) ^ (2 * e + 1) := pow_pos hP0 _
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith [h2 e he]
  have hcK : ∀ k e, c (e + k * N) = c e := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih => intro e; rw [Nat.succ_mul, ← add_assoc, hc, ih]
  have h3 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 0 ≤ c e := by
    intro e0 he0
    by_contra hneg
    have hneg : c e0 ≤ -1 := by omega
    have tend := hs.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    have hge : M ≤ e0 + M * N := by nlinarith
    have hlt : (fqT P α c Ds (e0 + M * N) : ℝ) < 1 / 2 := hM _ hge
    have hlt' : fqT P α c Ds (e0 + M * N) < 1 / 2 := by
      have : (fqT P α c Ds (e0 + M * N) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; exact hlt
      exact Rat.cast_lt.1 this
    have hE1 : Ds.sup id + α.natAbs + 1 ≤ e0 + M * N := le_trans he0 (Nat.le_add_right _ _)
    unfold fqT at hlt'
    rw [if_neg (h1 _ hE1), hcK] at hlt'
    have b1 := abs_lt.1 (h2' _ hE1)
    have b2 : ((c e0 : ℤ) : ℚ) ≤ -1 := by exact_mod_cast hneg
    have b3 := le_max_left ((α : ℚ) / (P : ℚ) ^ (2 * (e0 + M * N) + 1) - (c e0 : ℚ)) 0
    linarith [b1.1]
  have h4 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e →
      fqT P α c Ds (e + N) = fqT P α c Ds e / (P : ℚ) ^ (2 * N) := by
    intro e he
    have he' : Ds.sup id + α.natAbs + 1 ≤ e + N := le_trans he (Nat.le_add_right _ _)
    unfold fqT
    rw [if_neg (h1 _ he), if_neg (h1 _ he'), hc]
    have hQ : (0 : ℚ) < (P : ℚ) ^ (2 * N) := pow_pos hP0 _
    rcases (h3 e he).eq_or_lt with h0 | h0
    · rw [← h0]
      simp only [Int.cast_zero, sub_zero]
      have : (α : ℚ) / (P : ℚ) ^ (2 * (e + N) + 1) = (α : ℚ) / (P : ℚ) ^ (2 * e + 1) / (P : ℚ) ^ (2 * N) := by
        rw [div_div, ← pow_add]
        congr 2
        ring
      rw [this, ← max_div_div_right hQ.le, zero_div]
    · have b2 : (1 : ℚ) ≤ ((c e : ℤ) : ℚ) := by exact_mod_cast h0
      have c1 := abs_lt.1 (h2' _ he)
      have c2 := abs_lt.1 (h2' _ he')
      rw [max_eq_right (by linarith [c2.2]), max_eq_right (by linarith [c1.2]), zero_div]
  have hQ1 : (1 : ℚ) < (P : ℚ) ^ (2 * N) := by
    have : (1 : ℚ) < P := by exact_mod_cast (by omega : 1 < P)
    exact one_lt_pow₀ this (by omega)
  exact tsum_rat_tail _ hs _ N _ hQ1 h4

theorem gA_rat {n' k1 : ℕ} (p t : ℕ) (hp : 2 ≤ p) (hn : 0 < n') (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ∃ q : ℚ, gA p t TT lam0 w j = q := by
  have h1 : ∀ s : Fin n', ∃ q : ℚ, ∑' e : ℕ,
      (if 2 * e + 1 ∈ dSet TT s then (0 : ℝ) else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) - (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ)) 0) = q := by
    intro s
    apply tsum_rat p n' hp hn (al TT lam0 s) (fun e => cap t TT lam0 w j (posAdd s (2 * e + 1))) _ (dSet TT s)
    intro e
    have : posAdd s (2 * (e + n') + 1) = posAdd s (2 * e + 1) := by
      unfold posAdd
      apply Fin.ext
      show (s.val + (2 * (e + n') + 1)) % n' = (s.val + (2 * e + 1)) % n'
      have : s.val + (2 * (e + n') + 1) = s.val + (2 * e + 1) + 2 * n' := by ring
      rw [this, Nat.add_mul_mod_self_right]
    simp only [this]
  choose q hq using h1
  refine ⟨∑ s ∈ TT, q s - (∑ s : Fin n', ((NN k1 t j : ℚ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℚ) * (NN k1 t j : ℚ) * lgp p (lsz t TT lam0 w j s)) +
    ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℚ)) ^ 2), ?_⟩
  unfold gA de
  simp only [hq]
  push_cast
  ring

theorem restRat {p : ℕ} [Fact p.Prime] (X : Sys p) : RatCondition X := by
  intro v j
  have h := X.std v
  exact gA_rat p X.t (by have := h.five_le; omega) (by have := h.two_le; omega) _ _ _ j

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

