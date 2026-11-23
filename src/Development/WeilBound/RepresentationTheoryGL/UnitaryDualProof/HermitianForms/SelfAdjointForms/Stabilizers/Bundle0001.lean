module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ConjCircleEqOne
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_tr_indep {X W : Type} [AddCommGroup X] [AddCommMonoid W] (A L : AddSubgroup X) (T T' : Finset X)
    (hT : IsTr A L T) (hT' : IsTr A L T') (F : X → W) (hF : ∀ a, ∀ d ∈ L, F (a + d) = F a) :
    ∑ t ∈ T, F t = ∑ t ∈ T', F t := by
  classical
  have hσ : ∀ t ∈ T, ∃ s, s ∈ T' ∧ t - s ∈ L := fun t ht => (hT'.2 t (hT.1 t ht)).exists
  have hτ : ∀ s ∈ T', ∃ t, t ∈ T ∧ s - t ∈ L := fun s hs => (hT.2 s (hT'.1 s hs)).exists
  choose! σ hσT hσL using hσ
  choose! τ hτT hτL using hτ
  refine Finset.sum_nbij' σ τ hσT hτT ?_ ?_ ?_
  · intro t ht
    refine (hT.2 t (hT.1 t ht)).unique ⟨hτT _ (hσT t ht), ?_⟩ ⟨ht, by simp⟩
    have e : t - τ (σ t) = (t - σ t) + (σ t - τ (σ t)) := by abel
    rw [e]; exact L.add_mem (hσL t ht) (hτL _ (hσT t ht))
  · intro s hs
    refine (hT'.2 s (hT'.1 s hs)).unique ⟨hσT _ (hτT s hs), ?_⟩ ⟨hs, by simp⟩
    have e : s - σ (τ s) = (s - τ s) + (τ s - σ (τ s)) := by abel
    rw [e]; exact L.add_mem (hτL s hs) (hσL _ (hτT s hs))
  · intro t ht
    have := hF (σ t) _ (hσL t ht)
    rw [← this]; congr 1; abel

theorem isTr_filter {X : Type} [AddCommGroup X] (A A' H : AddSubgroup X) (hHA : H ≤ A) (U : Finset X)
    (hU : IsTr A' H U) (hAA : A ≤ A') [DecidablePred (· ∈ A)] : IsTr A H (U.filter (· ∈ A)) := by
  refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, fun a ha => ?_⟩
  obtain ⟨u, ⟨hu, hau⟩, huniq⟩ := hU.2 a (hAA ha)
  have huA : u ∈ A := by
    have e : u = a - (a - u) := by abel
    rw [e]; exact A.sub_mem ha (hHA hau)
  refine ⟨u, ⟨Finset.mem_filter.2 ⟨hu, huA⟩, hau⟩, fun t ⟨ht, hat⟩ => huniq t ⟨(Finset.mem_filter.1 ht).1, hat⟩⟩

theorem conj_circle_eq_one {z : Circle} (hz : z = 1) : starRingEnd ℂ (z : ℂ) = 1 := by simp [hz]

theorem sum_char {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ}
    {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {R : Finset (Fin (m + 1) → k)}
    (hR : IsTr (ann ψ A) (ann ψ A') R) (u : Fin (m + 1) → k) (hu : u ∈ A') [Decidable (u ∈ A)] :
    ∑ η ∈ R, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) = if u ∈ A then (R.card : ℂ) else 0 := by
  split_ifs with huA
  · rw [Finset.sum_congr rfl fun η hη => conj_circle_eq_one (hR.1 η hη u huA), Finset.sum_const, nsmul_eq_mul,
      mul_one]
  · obtain ⟨η₀, hη₀A, hη₀u⟩ := _root_.GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne k ψ hψ hψ1 (m + 1) A hA.1 hA.2 u huA
    set F : (Fin (m + 1) → k) → ℂ := fun η => starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) with hFdef
    have hF : ∀ a, ∀ d ∈ ann ψ A', F (a + d) = F a := by
      intro a d hd
      simp only [hFdef, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul, hd u hu, Circle.coe_one,
        map_one, mul_one]
    have e := sum_translate_transversal (ann ψ A) (ann ψ A') R hR.1 hR.2 F hF η₀ hη₀A
    have e2 : ∀ η, F (η + η₀) = F η * starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) := by
      intro η
      simp only [hFdef, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    simp only [e2, ← Finset.sum_mul] at e
    have hc : starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) ≠ 1 := by
      intro hc
      apply hη₀u
      have : ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) = 1 := by
        have := congrArg (starRingEnd ℂ) hc
        simpa using this
      exact Circle.coe_inj.1 (by simpa using this)
    have : (∑ η ∈ R, F η) * (starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) - 1) = 0 := by
      rw [mul_sub, mul_one, e, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hc)

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V}

theorem avg_decomp_pf (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') (hAA : A ≤ A') {R T : Finset (Fin (m + 1) → k)}
    (hR : IsTr (ann ψ A) (ann ψ A') R) (hT : IsTr A' A T) (v : V) :
    (R.card : ℂ) • avg ψ h π ξ A v = (T.card : ℂ) • ∑ η ∈ R, avg ψ h π (ξ + η) A' v := by
  classical
  obtain ⟨⟨H, S⟩, hHA, hHo, hHv, hHξ, hS1, hS2⟩ := avgData_exists ψ h π hψ hπ ξ A hA v
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_coset_reps_open_in_compact (Fin (m + 1) → k) A' H hA'.1 hHo (hHA.trans hAA)
  set f : (Fin (m + 1) → k) → V := fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
    with hfdef

  have hav : avg ψ h π ξ A v = ((S.card : ℂ)⁻¹) • ∑ t ∈ S, f t :=
    PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_eq_of_data ψ h π hψ hπ ξ hA v ⟨H, S⟩ ⟨hHA, hHo, hHv, hHξ, hS1, hS2⟩
  have hav' : ∀ η ∈ R, avg ψ h π (ξ + η) A' v =
      ((U.card : ℂ)⁻¹) • ∑ u ∈ U, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) • f u := by
    intro η hη
    have hdat : AvgData ψ h π (ξ + η) A' v ⟨H, U⟩ := by
      refine ⟨hHA.trans hAA, hHo, hHv, fun a ha => ?_, hU1, hU2⟩
      rw [add_dotProduct, AddChar.map_add_eq_mul, hHξ a ha, hR.1 η hη a (hHA ha), one_mul]
    rw [PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_eq_of_data ψ h π hψ hπ (ξ + η) hA' v ⟨H, U⟩ hdat]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hfdef, smul_smul, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    ring_nf

  have hsum : ∑ η ∈ R, avg ψ h π (ξ + η) A' v = ((U.card : ℂ)⁻¹ * (R.card : ℂ)) • ∑ u ∈ U.filter (· ∈ A), f u := by
    rw [Finset.sum_congr rfl hav', ← Finset.smul_sum, Finset.sum_comm]
    have e1 : ∀ u ∈ U, ∑ η ∈ R, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) • f u =
        (if u ∈ A then (R.card : ℂ) else 0) • f u := fun u hu => by
      rw [← Finset.sum_smul, sum_char hψ hψ1 hA hR u (hU1 u hu)]
    rw [Finset.sum_congr rfl e1, Finset.sum_filter, mul_smul]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp

  have hper : ∀ a, ∀ d ∈ H, f (a + d) = f a := by
    intro a d hd
    simp only [hfdef, dotProduct_add, AddChar.map_add_eq_mul, hHξ d hd, mul_one, colEl_add, map_mul,
      Module.End.mul_apply, hHv d hd]
  have hind : ∑ u ∈ U.filter (· ∈ A), f u = ∑ t ∈ S, f t :=
    sum_tr_indep A H _ S (isTr_filter A A' H hHA U ⟨hU1, hU2⟩ hAA) ⟨hS1, hS2⟩ f hper
  have cU : U.card = H.relIndex A' := GlobalTheory.T.card_coset_reps_eq_relIndex _ A' H U (hHA.trans hAA) hU1 hU2
  have cS : S.card = H.relIndex A := GlobalTheory.T.card_coset_reps_eq_relIndex _ A H S hHA hS1 hS2
  have cT : T.card = A.relIndex A' := GlobalTheory.T.card_coset_reps_eq_relIndex _ A' A T hAA hT.1 hT.2
  have cmul : U.card = S.card * T.card := by
    rw [cU, cS, cT, AddSubgroup.relIndex_mul_relIndex H A A' hHA hAA]
  have hS0 : (S.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hS2 0 A.zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨t, ht.1⟩).ne'
  have hT0 : (T.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hT.2 0 A'.zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨t, ht.1⟩).ne'
  rw [hsum, hind, hav, smul_smul, smul_smul, cmul]
  congr 1
  push_cast
  field_simp

end

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ExistsBallPf
section
noncomputable section

open Matrix ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unif' : ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r, ?_, hr1⟩
  first
    | exact hr0
    | exact (Valuation.ne_zero_iff _).1 hr0
    | simpa using hr0

theorem pi_lt_mem_nhds {n : ℕ} {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < γ}) ∈ nhds (0 : Fin n → k) :=
  set_pi_mem_nhds Set.finite_univ fun _ _ => (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ

theorem ball_isLat {n : ℕ} (s : kˣ) :
    IsCompact (ball n s : Set (Fin n → k)) ∧ IsOpen (ball n s : Set (Fin n → k)) := by
  have hs : valuation k (s : k) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  refine ⟨?_, ?_⟩
  · have e : (ball n s : Set (Fin n → k)) =
        Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (s : k)}) := by
      ext x
      exact Iff.intro (fun h i _ => h i) (fun h i => h i (Set.mem_univ i))
    rw [e]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine (ball n s).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (pi_lt_mem_nhds hs) ?_)
    intro x hx i
    exact (hx i (Set.mem_univ i)).le

theorem exists_ball_n {n : ℕ} {A : AddSubgroup (Fin n → k)} (hA : IsCompact (A : Set (Fin n → k))) :
    ∃ s : kˣ, A ≤ ball n s := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
  have hU : (ball n (1 : kˣ) : Set (Fin n → k)) ∈ nhds (0 : Fin n → k) := by
    refine Filter.mem_of_superset (pi_lt_mem_nhds (n := n) (γ := 1) one_ne_zero) ?_
    intro x hx i
    have h := hx i (Set.mem_univ i)
    simp only [Set.mem_ofPred_eq] at h
    simpa using h.le
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem k n _ hA _ hU ϖ hϖ1
  have hpl : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
  have hne : valuation k (ϖ ^ l) ≠ 0 := (Valuation.ne_zero_iff _).2 hpl
  refine ⟨Units.mk0 ((ϖ ^ l)⁻¹) (inv_ne_zero hpl), fun x hx i => ?_⟩
  have h1 := hl x hx i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Units.val_one, map_one] at h1
  simp only [Units.val_mk0]
  calc valuation k (x i) = (valuation k (ϖ ^ l))⁻¹ * (valuation k (ϖ ^ l) * valuation k (x i)) :=
        (inv_mul_cancel_left₀ hne _).symm
    _ ≤ (valuation k (ϖ ^ l))⁻¹ * 1 := by gcongr
    _ = valuation k ((ϖ ^ l)⁻¹) := by rw [mul_one, map_inv₀]

theorem ann_isLat_pf {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {A : AddSubgroup (Fin n → k)}
    (hA : IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k))) :
    IsCompact (ann ψ A : Set (Fin n → k)) ∧ IsOpen (ann ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_ball_n hA.1
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hvs : valuation k (s : k) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  have hδ : γ / valuation k (s : k) ≠ 0 := div_ne_zero hγ hvs
  refine ⟨?_, ?_⟩
  · obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
    have hAn : (A : Set (Fin n → k)) ∈ nhds 0 := hA.2.mem_nhds A.zero_mem
    obtain ⟨l, hl⟩ := _root_.GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem k n _ (ball_isLat (n := n) 1).1 _ hAn ϖ hϖ1
    have hb : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have hsub : (ann ψ A : Set (Fin n → k)) ⊆
        {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (ϖ ^ l * (t ⬝ᵥ x)) = 1} := by
      intro η hη
      show ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (ϖ ^ l * (t ⬝ᵥ η)) = 1
      intro t ht
      have htb : t ∈ ball n 1 := fun j => by
        simpa using (Valuation.mem_integer_iff _ _).mp (ht j)
      have h1 : ψ (η ⬝ᵥ (ϖ ^ l • t)) = 1 := hη _ (hl t htb)
      rw [dotProduct_smul, smul_eq_mul, dotProduct_comm] at h1
      exact h1
    have hcl : IsClosed (ann ψ A : Set (Fin n → k)) := by
      have e : (ann ψ A : Set (Fin n → k)) = ⋂ a ∈ A, {η : Fin n → k | ψ (η ⬝ᵥ a) = 1} := by
        ext η
        simp only [Set.mem_iInter]
        rfl
      rw [e]
      exact isClosed_biInter fun a _ => isClosed_eq (hψ.comp (by unfold dotProduct; fun_prop)) continuous_const
    exact (GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator k ψ hψ hψ1 n _ hb).1.of_isClosed_subset hcl hsub
  · refine (ann ψ A).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (pi_lt_mem_nhds hδ) ?_)
    intro η hη a ha
    apply hball
    have hpos : 0 < valuation k (s : k) := zero_lt_iff.mpr hvs
    show valuation k (∑ j, η j * a j) < γ
    refine Valuation.map_sum_lt _ hγ fun j _ => ?_
    have h1 : valuation k (η j) * valuation k (s : k) < γ := (lt_div_iff₀ hpos).1 (hη j (Set.mem_univ j))
    rw [map_mul]
    have h2 := hs ha j
    exact lt_of_le_of_lt (by gcongr) h1

theorem exists_ball_pf {m : ℕ} {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) :
    ∃ s : kˣ, A ≤ ball (m + 1) s ∧ IsLat (ball (m + 1) s) := by
  obtain ⟨s, hs⟩ := exists_ball_n hA.1
  exact ⟨s, hs, ball_isLat s⟩

theorem exists_big_pf {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} (D : Set (Fin (m + 1) → k))
    (hD : D ∈ nhds (0 : Fin (m + 1) → k)) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ (ann ψ A₁ : Set (Fin (m + 1) → k)) ⊆ D := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
  have hC := ann_isLat_pf hψ hψ1 (ball_isLat (n := m + 1) (1 : kˣ))
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem k (m + 1) _ hC.1 D hD ϖ hϖ1
  have hb : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
  set u : kˣ := Units.mk0 ((ϖ ^ l)⁻¹) (inv_ne_zero hb) with hu
  obtain ⟨s₀, hs₀⟩ := exists_ball_n (n := m + 1) hA₀.1
  obtain ⟨s, h1, h2⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      valuation k (u : k) ≤ valuation k (s : k) := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (u : k)) with h | h
    · exact ⟨u, h, le_rfl⟩
    · exact ⟨s₀, le_rfl, h⟩
  refine ⟨ball (m + 1) s, ball_isLat s, fun x hx i => (hs₀ hx i).trans h1, ?_⟩
  intro η hη
  have hη' : (ϖ ^ l)⁻¹ • η ∈ ann ψ (ball (m + 1) 1) := by
    intro a ha
    have hmem : (ϖ ^ l)⁻¹ • a ∈ ball (m + 1) s := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul]
      have ha' : valuation k (a i) ≤ 1 := by simpa using ha i
      calc valuation k (ϖ ^ l)⁻¹ * valuation k (a i) ≤ valuation k (ϖ ^ l)⁻¹ * 1 := by gcongr
        _ = valuation k (u : k) := by simp [hu]
        _ ≤ _ := h2
    have e := hη _ hmem
    rwa [dotProduct_smul, ← smul_dotProduct] at e
  have := hl _ hη'
  rwa [smul_smul, mul_inv_cancel₀ hb, one_smul] at this

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.VmvMulVecApply
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vmv_sq {m : ℕ} (η : Fin (m + 1) → k) :
    vecMulVec (xi0 k m) η * vecMulVec (xi0 k m) η = η (Fin.last m) • vecMulVec (xi0 k m) η := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, xi0, Pi.single_apply, mul_comm, mul_left_comm]

theorem inv_pair {m : ℕ} (E : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (a c : k) (hE : E * E = a • E)
    (hc : c * (1 + a) = 1) : (1 + E) * (1 - c • E) = 1 ∧ (1 - c • E) * (1 + E) = 1 := by
  have h : E = c • E + (c * a) • E := by
    rw [← add_smul, ← mul_one_add, hc, one_smul]
  constructor
  · rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, hE, smul_smul]
    have h2 : E - (c * a) • E = c • E := by
      rw [sub_eq_iff_eq_add]
      exact h
    rw [sub_add_eq_add_sub, add_sub_assoc, h2, sub_self, add_zero]
  · rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_smul, ← h, add_sub_cancel_right]

def gU {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) : GL (Fin (m + 1)) k :=
  ⟨1 + vecMulVec (xi0 k m) η, 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η,
    (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).1, (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).2⟩

theorem gU_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = 1 + vecMulVec (xi0 k m) η := rfl

theorem gU_inv_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    (((gU η hη)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η := rfl

theorem gU_transpose {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  funext i
  simp [gU_val, Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_vecMulVec, Matrix.mulVec,
    dotProduct, vecMulVec_apply, xi0, Pi.single_apply]
  by_cases h : i = Fin.last m
  · subst h
    simp
  · simp [h, Matrix.one_apply_ne (Ne.symm h)]

theorem gU_det {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (gU η hη) : kˣ) : k) = 1 + η (Fin.last m) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, gU_val, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow]
  simp [xi0, dotProduct_single]

theorem val_dot_le {n : ℕ} (a x : Fin n → k) (γ : ValueGroupWithZero k) (ha : ∀ i, valuation k (a i) ≤ 1)
    (hx : ∀ i, valuation k (x i) ≤ γ) : valuation k (a ⬝ᵥ x) ≤ γ := by
  simp only [dotProduct]
  refine Valuation.map_sum_le _ (fun i _ => ?_)
  rw [Valuation.map_mul]
  calc _ ≤ 1 * γ := mul_le_mul' (ha i) (hx i)
    _ = γ := one_mul γ

theorem vmv_mulVec_apply {m : ℕ} (u v w : Fin (m + 1) → k) (i : Fin (m + 1)) :
    (vecMulVec u v *ᵥ w) i = u i * (v ⬝ᵥ w) := by
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem mem_ball_of {m : ℕ} (c : k) (η x : Fin (m + 1) → k) (hc : valuation k c ≤ 1) (hη : ∀ i, valuation k (η i) ≤ 1)
    (s : kˣ) (hx : x ∈ ball (m + 1) s) : (1 + c • vecMulVec (xi0 k m) η) *ᵥ x ∈ ball (m + 1) s := by
  have hx' : ∀ i, valuation k (x i) ≤ valuation k (s : k) := hx
  show ∀ i, valuation k (((1 + c • vecMulVec (xi0 k m) η) *ᵥ x) i) ≤ valuation k (s : k)
  intro i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply,
    vmv_mulVec_apply, smul_eq_mul]
  refine Valuation.map_add_le _ (hx' i) ?_
  rw [Valuation.map_mul, Valuation.map_mul]
  have hu : valuation k (xi0 k m i) ≤ 1 := by
    unfold xi0
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hd := val_dot_le η x _ hη hx'
  calc _ ≤ 1 * (1 * valuation k (s : k)) := mul_le_mul' hc (mul_le_mul' hu hd)
    _ = _ := by rw [one_mul, one_mul]

theorem good_nbhd_pf {m : ℕ} (K : Subgroup (GL (Fin (m + 1)) k)) (hK : IsOpen (K : Set (GL (Fin (m + 1)) k))) :
    ∃ D ∈ nhds (0 : Fin (m + 1) → k), ∀ η ∈ D, ∃ g ∈ K, nabs k (Matrix.GeneralLinearGroup.det g) = 1 ∧
      (∀ s : kˣ, pre g⁻¹ (ball (m + 1) s) = ball (m + 1) s) ∧
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  have hv : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  have hS : {η : Fin (m + 1) → k | ∀ i, valuation k (η i) < 1} ∈ nhds (0 : Fin (m + 1) → k) := by
    simp only [Set.setOf_forall]
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : (fun η : Fin (m + 1) → k => η i) ⁻¹' {x : k | valuation k x < 1} ∈
        nhds (0 : Fin (m + 1) → k) :=
      ((continuous_apply i).tendsto (0 : Fin (m + 1) → k)) hv
    exact h1
  obtain ⟨U, hU, hUK⟩ := isOpen_induced_iff.1 hK
  let F : (Fin (m + 1) → k) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun η => (1 + vecMulVec (xi0 k m) η,
      MulOpposite.op (1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η))
  have hF : ContinuousAt F 0 := by
    have hE : Continuous fun η : Fin (m + 1) → k => vecMulVec (xi0 k m) η :=
      Continuous.matrix_vecMulVec continuous_const continuous_id
    have h2 : ContinuousAt (fun η : Fin (m + 1) → k => (1 + η (Fin.last m))⁻¹) 0 :=
      ContinuousAt.inv₀ (continuous_const.add (continuous_apply _)).continuousAt (by simp)
    have h3 : ContinuousAt
        (fun η : Fin (m + 1) → k => 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η) 0 :=
      continuousAt_const.sub (h2.smul hE.continuousAt)
    exact ContinuousAt.prodMk (continuous_const.add hE).continuousAt
      (MulOpposite.continuous_op.continuousAt.comp h3)
  have h0 : F 0 ∈ U := by
    have h1 : (1 : GL (Fin (m + 1)) k) ∈ (K : Set (GL (Fin (m + 1)) k)) := K.one_mem
    rw [← hUK] at h1
    have e : F 0 = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) :=
      Prod.ext (by simp [F]) (MulOpposite.unop_injective (by simp [F]))
    rw [e]
    exact h1
  refine ⟨F ⁻¹' U ∩ {η | ∀ i, valuation k (η i) < 1},
    Filter.inter_mem (hF.preimage_mem_nhds (hU.mem_nhds h0)) hS, ?_⟩
  rintro η ⟨hηU, hηv⟩
  have hl : valuation k (1 + η (Fin.last m)) = 1 := Valuation.map_one_add_of_lt _ (hηv _)
  have hne : 1 + η (Fin.last m) ≠ 0 := by
    intro h
    rw [h, map_zero] at hl
    exact zero_ne_one hl
  have hη1 : ∀ i, valuation k (η i) ≤ 1 := fun i => (hηv i).le
  refine ⟨(gU η hne)⁻¹, ?_, ?_, ?_, ?_⟩
  · apply K.inv_mem
    have e : Units.embedProduct _ (gU η hne) = F η :=
      Prod.ext (gU_val η hne) (MulOpposite.unop_injective (gU_inv_val η hne))
    have h1 : gU η hne ∈ Units.embedProduct _ ⁻¹' U := by
      show Units.embedProduct _ (gU η hne) ∈ U
      rw [e]
      exact hηU
    rw [hUK] at h1
    exact h1
  · rw [GlobalTheory.SplitWeil.nabs_eq_one_iff, map_inv, Units.val_inv_eq_inv_val, gU_det, map_inv₀, hl, inv_one]
  · intro s
    rw [inv_inv]
    ext x
    simp only [pre, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, gU_val]
    constructor
    · intro hx
      have hc' : valuation k (-(1 + η (Fin.last m))⁻¹) ≤ 1 := by
        rw [Valuation.map_neg, map_inv₀, hl, inv_one]
      have hmul : (1 + (-(1 + η (Fin.last m))⁻¹) • vecMulVec (xi0 k m) η) *
          (1 + vecMulVec (xi0 k m) η) = 1 := by
        rw [neg_smul, ← sub_eq_add_neg]
        exact (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hne)).2
      have h1 := mem_ball_of _ η _ hc' hη1 s hx
      rwa [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] at h1
    · intro hx
      have h1 := mem_ball_of 1 η x (map_one (valuation k)).le hη1 s hx
      rwa [one_smul] at h1
  · rw [inv_inv]
    exact gU_transpose η hne

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end

