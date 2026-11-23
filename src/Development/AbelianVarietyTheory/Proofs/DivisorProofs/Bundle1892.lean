module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorCast
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

theorem toNat_floor_cast {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem eQ_succ (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) : DV.eQ D ((i : ℕ) + 1) t = (D.hc t).e i := by
  unfold DV.eQ
  rw [dite_eq_left ⟨Nat.le_add_left _ _, i.2⟩]
  rfl

theorem lamAt_eq (D : D7) (t : D.what₂.Tau) (n : ℕ) : Formalism.L2.NTheta.lamAt (D.hc t) n = DV.sigPar D t n := rfl

theorem aPl_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) t n : ℚ) =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k : ℚ) + i) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have e : DV.aPlusQ D ((i : ℕ) + 1) t n =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    rw [DV.aPlusQ_eq, eQ_succ]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aPlusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t ⟨n, hn⟩
  have h2 := DV.aPlusQ_int D ((i : ℕ) + 1) t n
  unfold aPl
  rw [if_pos hn, lamAt_eq, ← e, toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem aMi_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (c : ℕ) (hc : (i : ℕ) + 1 + c < D.R.m) :
    (aMi D i (D.R.k + i) (D.R.m - ((i : ℕ) + 1)) t (D.R.m - ((i : ℕ) + 1) - 1 - c) : ℚ) =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have e0 : D.R.m - ((i : ℕ) + 1) - (D.R.m - ((i : ℕ) + 1) - 1 - c) = c + 1 := by omega
  have e1 : DV.sigPar D t (D.R.k + i + c) = -(D.hc t).b ⟨(i : ℕ) + 1 + c, hc⟩ := by
    unfold DV.sigPar
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 3
    omega
  have e : DV.aMinusQ D ((i : ℕ) + 1) t c =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
    unfold DV.aMinusQ
    rw [dite_eq_left hc, eQ_succ, e1]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aMinusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) t c hc
  have h2 := DV.aMinusQ_int D ((i : ℕ) + 1) t c
  unfold aMi
  rw [if_pos (by omega), e0, lamAt_eq, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, ← e,
    toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem nV_half (R : Ranks) : ((R.nV / 2 : ℕ) : ℚ) = ((R.r : ℚ) + R.t) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hm := R.two_le_m
  have h1 : R.r + R.t = 2 * (R.nV / 2) := by unfold Ranks.nV Ranks.r; omega
  have h2 : (R.r : ℚ) + R.t = 2 * ((R.nV / 2 : ℕ) : ℚ) := by exact_mod_cast h1
  linarith

def ent (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℚ :=
  DV.sigPar D t n + (D.hc t).e i + n - ((D.R.k : ℚ) + i) + ((D.R.r : ℚ) + 1) / 2 - if n < D.R.k + i then 0 else (D.R.r : ℚ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem inR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

theorem dat_p : (dat p i).p = D.R.k + i := (p.fw.laws.pins.2.2.2 _ (inR i)).1

theorem dat_q : (dat p i).q = D.R.m - ((i : ℕ) + 1) := (p.fw.laws.pins.2.2.2 _ (inR i)).2.1

theorem dat_rank : (dat p i).p + (dat p i).q = D.R.r := by
  have := i.2
  rw [dat_p, dat_q]; unfold Ranks.r; omega

theorem exists_tau (τ : Psi p.T.Q.H) : ∃ t, τ.1 = DV.tauEmb D t :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q p.fw.laws.pins.1 τ.1 τ.2

theorem card_psi : Nat.card (Psi p.T.Q.H) = D.R.f := by
  have hp := p.fw.laws.pins.1
  have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hp.2.2.2 t⟩ : Psi p.T.Q.H)) :=
    ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => by
      obtain ⟨t, ht⟩ := exists_tau p τ
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]

theorem dim_eq : dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  unfold dimFlag Formalism.DegreeFormula.dimFl
  rw [dat_rank, ← Nat.card_eq_fintype_card, card_psi, Nat.choose_two_right]

theorem cols_eq : (p.κ i).n = D.R.nV := by
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega)
  obtain ⟨t⟩ := hne
  exact (p.fw.kap i t).2.2

theorem unit_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem laOf_read (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℚ) = ent D i t n := by
  have hp := p.fw.laws.pins.1
  have hs : (Wc D i).sig (TH.tauE D t) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨k1, k2, -⟩ := p.fw.kap i t
  rw [hs] at k1 k2
  have s1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have s2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1) := rfl
  have hn := n.2
  have e1 := dat_p p i
  have e2 := dat_q p i
  have hh := nV_half D.R
  unfold laOf weightOf ent
  rw [cols_eq, ht]
  beta_reduce
  by_cases h : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h, GlobalTheory.WeightExponents.wtA_tauEmb hp, ext0, dite_eq_left (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), k1]
    have := aPl_cast D i t n h
    simp only [Int.cast_add, Int.cast_natCast, s1]
    rw [this, hh]; ring
  · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + c := ⟨n - (D.R.k + i), by omega⟩
    have e3 : (dat p i).q - 1 - ((n : ℕ) - (dat p i).p) = D.R.m - ((i : ℕ) + 1) - 1 - c := by omega
    rw [if_neg (by omega), if_neg h, e3, conjEmb, GlobalTheory.WeightExponents.conjEmb_eq, GlobalTheory.WeightExponents.wtA_conj hp, ext0,
      dite_eq_left (show D.R.m - ((i : ℕ) + 1) - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 by omega), k2]
    have := aMi_cast D i t c (by omega)
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, s1, s2]
    rw [this, hh, hc]; push_cast; ring

end GlobalTheory.CovTop.WtShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeLevelVectorsEqDimMulLocalTraces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_eq_zero_of_finrank_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (h : Module.finrank ℂ M = 0) : trOn M L = 0 := by
  unfold trOn
  split_ifs with hL
  · by_cases hf : FiniteDimensional ℂ M
    · haveI := hf
      haveI : Subsingleton M := Module.finrank_zero_iff.mp h
      rw [Subsingleton.elim (L.restrict hL) 0, map_zero]
    · rw [LinearMap.trace, dite_eq_right]
      · rfl
      · rintro ⟨s, ⟨b⟩⟩
        exact hf (Module.Finite.of_basis b)
  · rfl

theorem trOn_of_eq_smul {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (c : ℂ) (h : ∀ v ∈ M, L v = c • v) : trOn M L = c * Module.finrank ℂ M := by
  have hM : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [h v hv]; exact M.smul_mem c hv
  unfold trOn
  rw [dite_eq_left hM]
  have hr : L.restrict hM = c • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, h v v.2]
  rw [hr, map_smul, smul_eq_mul]
  by_cases hf : FiniteDimensional ℂ M
  · rw [LinearMap.trace_id]
  · rw [LinearMap.trace, dite_eq_right, Module.finrank_of_not_finite hf]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hf (Module.Finite.of_basis b)

theorem trOn_hop_eq_dimW_mul_finprod_twTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  intro E _ _ _ hU n hn π hπ S hS lam hlam K' hK' σ hσ f hf
  have hTW := fun w => _root_.GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) (σ w)
  have hcongr : ∀ g g' : ∀ w : Pl E, UL n w → ℂ, (∀ w ∈ S, g w = g' w) → hop S K' g = hop S K' g' := by
    intro g g' h
    have : globFn S g = globFn S g' := by
      funext x
      unfold globFn
      exact finprod_mem_congr rfl (fun w hw => by rw [h w hw])
    unfold hop
    rw [this]
  have hfin : {w | ¬ ((f w = ((KL n w : Set (UL n w)).indicator 1) ∧ K' w = KL n w) ∧
      Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1)}.Finite :=
    Filter.eventually_cofinite.1 ((hf.2.and hK'.2).and (_root_.GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one E hU n hn π hπ σ hσ))
  set F := hfin.toFinset with hF
  have hout : ∀ w, w ∉ F → f w = (K' w : Set (UL n w)).indicator 1 ∧
      twTr (σ w).ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = 1 ∧
      (K' w).relIndex (KL n w) = 1 ∧ Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by
    intro w hw
    rw [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    have hr : (K' w).relIndex (KL n w) = 1 := by rw [h2]; exact Subgroup.relIndex_self _
    have hd : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by rw [h2]; exact h3
    refine ⟨by rw [h1, h2], ?_, hr, hd⟩
    rw [(hTW w).2.2.1, hr, hd]
    simp
  set one : ∀ w : Pl E, UL n w → ℂ := fun w => (K' w : Set (UL n w)).indicator 1 with hone
  have key : ∀ U : Finset (Pl E), (↑U : Set (Pl E)) ⊆ S →
      trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
        ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) *
        trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one, one_mul]
    | insert a U ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a U)
      have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hg : IsTest (KL n) K' (fun w => if w ∈ insert a U then f w else one w) := by
        refine ⟨fun w => ?_, ?_⟩
        · by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact hf.1 w
          · simp only [h, if_false]; exact (hTW w).1
        · filter_upwards [hf.2, hK'.2] with w h1 h2
          by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact h1
          · simp only [h, if_false, hone]; rw [h2]
      have hstep := _root_.GlobalTheory.BCT.Peel.trOn_hop_peel E hU n hn π hπ S hS K' hK' _ hg a haS (σ a) (hσ a)
      have hupd : Function.update (fun w => if w ∈ insert a U then f w else one w) a
          ((K' a : Set (UL n a)).indicator 1) = fun w => if w ∈ U then f w else one w := by
        funext w
        by_cases h : w = a
        · subst h
          simp [ha, hone]
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd] at hstep
      simp only [Finset.mem_insert_self, if_true] at hstep
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have e1 : twTr (σ a).ρ (KL n a) (K' a) (one a) LinearMap.id =
          twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id := rfl
      rw [e1]
      calc _ = (trOn (π ⊓ fixed (RF E n) (globLev S K'))
              (hop S K' (fun w => if w ∈ insert a U then f w else one w)) *
            twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id := by ring
        _ = twTr (σ a).ρ (KL n a) (K' a) (f a) LinearMap.id *
            (trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id) := by rw [hstep]; ring
        _ = _ := by rw [ih hUS]; ring
  set U := F.filter (· ∈ S) with hUdef
  have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => (Finset.mem_filter.1 hx).2
  have hfU : hop S K' (fun w => if w ∈ U then f w else one w) = hop S K' f := by
    refine hcongr _ _ fun w hw => ?_
    by_cases h : w ∈ F
    · have : w ∈ U := Finset.mem_filter.2 ⟨h, hw⟩
      simp only [this, if_true]
    · have : w ∉ U := fun h' => h (Finset.mem_filter.1 h').1
      simp only [this, if_false, hone]
      exact ((hout w h).1).symm
  have hkey := key U hUS
  rw [hfU] at hkey

  have hfp : ∀ g : Pl E → ℂ, (∀ w, w ∉ F → g w = 1) → ∏ᶠ w ∈ S, g w = ∏ w ∈ U, g w := by
    intro g hg
    refine finprod_mem_eq_prod_of_subset g ?_ (fun x hx => (Finset.mem_filter.1 hx).2)
    rintro w ⟨hwS, hw1⟩
    by_cases h : w ∈ F
    · exact Finset.mem_filter.2 ⟨h, hwS⟩
    · exact absurd (hg w h) hw1
  have hRf := hfp (fun w => (((K' w).relIndex (KL n w) : ℕ) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.1])
  have hDf := hfp (fun w => (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.2])
  have hTf := hfp (fun w => twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) (fun w hw => by
    rw [(hout w hw).1]; exact (hout w hw).2.1)
  have hbase : trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) =
      (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) :=
    trOn_of_eq_smul _ _ _ fun φ hφ => _root_.GlobalTheory.BCT.hop_indicator_level E hU n hn S hS K' hK' φ (Submodule.mem_inf.1 hφ).2
  have hdim := GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn π hπ S hS lam hlam K' hK' σ hσ
  have hone_w : ∀ w, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      ((((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ * (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) :=
    fun w => (hTW w).2.2.1
  rw [Finset.prod_congr rfl (fun w _ => hone_w w)] at hkey
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at hkey
  rw [hbase, hdim, hRf, hDf] at hkey
  rw [hTf]
  have hR : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => Nat.cast_ne_zero.2 (hTW w).2.1
  by_cases hD : (∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) = 0
  · obtain ⟨w, hwU, hw0⟩ := Finset.prod_eq_zero_iff.1 hD
    have hw0' : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 0 := by exact_mod_cast hw0
    have hT0 : (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) = 0 :=
      Finset.prod_eq_zero hwU ((hTW w).2.2.2 hw0' (f w))
    rw [hT0, mul_zero]
    apply trOn_eq_zero_of_finrank_eq_zero
    have : (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = 0 := by
      rw [hdim, hDf, hD, mul_zero]
    exact_mod_cast this
  · have hne : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        ∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hR) hD
    apply mul_right_cancel₀ hne
    rw [hkey]
    ring

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrors
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefArith

theorem sum_laOf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hq : Dw.q = 0) (hn : Even n) (τ : Psi H) :
    (∑ k, (laOf Dw a n τ k : ℝ)) = (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) + (Dw.p : ℝ) * n / 2 := by
  have hm : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hk : ∀ k : Fin (Dw.p + Dw.q), (laOf Dw a n τ k : ℝ) = (a (τ.1, k) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro k
    have h := k.2
    have hlt : (k : ℕ) < Dw.p := by omega
    simp [laOf, weightOf, hlt]
    norm_cast
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.p + Dw.q)]
  have hs : (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) = ∑ i ∈ Finset.range Dw.p, (a (τ.1, i) : ℝ) := by
    unfold GlobalTheory.DualWeyl.size part
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.mult τ.1), hm]
  rw [hs, hq, add_zero]
  obtain ⟨r, rfl⟩ := hn
  have : (r + r) / 2 = r := by omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, this, hq, add_zero]
  push_cast
  ring

end GlobalTheory.DefArith

namespace GlobalTheory.DefArith

theorem two_defBound_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  intro E _ _ _ H Dw a n kc lo hq hp hn
  have hp0 : (Dw.p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Dw.p := by exact_mod_cast hp
    exact this.ne'

  have hτ : ∀ τ : Psi H, -((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) ≤
      2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) := by
    intro τ
    have hS := sum_laOf_eq Dw a n hq hn τ
    have hsplit : (∑ k, (laOf Dw a n τ k : ℝ)) =
        (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) + ∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq, add_zero]
      ring
    have hb : -(|lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) ≤
        -((∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo) := by
      rw [neg_le_neg_iff]
      calc (∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo
          ≤ |(∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo| := le_abs_self _
        _ = |∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))| * |lo| := abs_mul _ _
        _ ≤ (∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) * |lo| :=
            mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
        _ = |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| := mul_comm _ _
    have he : 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) =
        -((∑ k, (laOf Dw a n τ k : ℝ)) * lo) - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) := by
      rw [hS]
      unfold flatDegVal
      rw [hq]
      field_simp
      ring
    rw [he, hsplit]
    linarith
  have hlog : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hN : 0 ≤ (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) := by positivity
  have hl : -((n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E|) ≤
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    have h1 := le_abs_self (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E)
    have h2 : -|GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ Real.log (2 * Real.pi) / 2 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hN
    nlinarith
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hτ τ
  have eL : -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) -
      (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) =
      ∑ τ : Psi H, (-((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
        |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have eR : 2 * defBound Dw a n (-flatDegVal Dw lo) =
      ∑ τ : Psi H, 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) +
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    unfold defBound
    rw [mul_add, Finset.mul_sum]
  rw [eL, eR]
  linarith

end GlobalTheory.DefArith
end

