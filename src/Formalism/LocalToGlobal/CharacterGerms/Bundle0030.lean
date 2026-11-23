module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0028
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0029
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0023
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.LogCoordOfDpull
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  set c := MvPowerSeries.constantCoeff f with hc
  have hg : MvPowerSeries.constantCoeff (f - algebraMap C (MvPowerSeries σ C) c) = 0 := by
    simp [hc, MvPowerSeries.algebraMap_apply]
  have hf : f = algebraMap C (MvPowerSeries σ C) c + (f - algebraMap C (MvPowerSeries σ C) c) := by
    ring
  have h1 : MvPowerSeries.subst a (algebraMap C (MvPowerSeries σ C) c) =
      algebraMap C (MvPowerSeries τ C) c := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact (MvPowerSeries.substAlgHom hs).commutes c
  rw [hf, MvPowerSeries.subst_add hs, map_add (f := _), h1, constantCoeff_subst_zero ha hg]
  simp [MvPowerSeries.algebraMap_apply]

private theorem jetAt0_zero_left' {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  simp [jetAt0]

private theorem jetAt0_finset_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left']
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

theorem jet_lin {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv (R := C) (e w) G) := by
  rw [Finset.mul_sum, jetAt0_finset_sum_left, jet_sum_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, jet_mul_X, jet_mul_C, jet_smul_right, dVar_eq_pderiv]

variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

end VP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCHarm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem letter_cast {T : Type} {r : T → ℕ} {n : ℕ} {σ σ' : T} (h : σ = σ') (a : Fin (r σ)) :
    ∃ a' : Fin (r σ'), ∀ b : Fin n, (⟨σ, a, b⟩ : Letter T r n) = ⟨σ', a', b⟩ := by
  subst h
  exact ⟨a, fun b => rfl⟩

section Plane

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem lap_plane (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (o : Orb) (t : ZMod 2)
    (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hno : ∀ ρ g1 g2, g1 ≠ g2 → (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ Q.vars →
      (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars → False) :
    ∑ b, pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
      (subG r tau gm plc Q)) = 0 := by
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map plc →
      pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
        (subG r tau gm plc Q)) = 0 := by
    intro b _ hb
    rw [pderiv_subG_off plc (ℓ := ⟨tau o (t + 1), a2, b⟩), map_zero]
    intro z e
    apply hb
    rw [Finset.mem_map]
    exact ⟨(z.1.1, z.2), Finset.mem_univ _, (congrArg (fun ℓ : Letter T r n => ℓ.2.2) e).symm⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map plc)) hoff, Finset.sum_map, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hf : ∀ col, pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n)
      (pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q)) =
      ∑ g1, ∑ g2, MvPolynomial.C (gm o t col g1 * gm o (t + 1) col g2) *
        subG r tau gm plc (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
          (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) := by
    intro col
    have e2 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t + 1, a2⟩⟩) : AA r tau N) col Q
    have e2' : pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q) = _ := e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2', map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g2 _ => ?_
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
    have e1 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t, a1⟩⟩) : AA r tau N) col
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)
    have e1' : pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) = _ := e1
    rw [e1', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g1 _ => ?_
    rw [map_mul]
    unfold Gm
    ring
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g2 _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_mul, ← map_sum]
  by_cases hg : g1 = g2
  · have hK : ∑ col, gm o t col g1 * gm o (t + 1) col g2 = 0 := by
      have h := gm_hyp o t g2 g1
      rw [if_pos hg.symm] at h
      rw [← h]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    rw [hK, map_zero, zero_mul]
  · have hz : pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
        (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q) = 0 := by
      by_cases h2 : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars
      · have h1 : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∉ Q.vars := fun h1 => hno ρ g1 g2 hg h1 h2
        rw [pderiv_comm', pderiv_eq_zero_of_notMem_vars h1, map_zero]
      · rw [pderiv_eq_zero_of_notMem_vars h2, map_zero]
    rw [hz, map_zero, mul_zero]

end Plane

section Fam

theorem mem_vars_blkProdG {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  first
  | unfold blkProd at hx
  | simp only [blkProd] at hx
  first
  | unfold toAll at hx
  | simp only [toAll] at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨x, hx1, hx2⟩ := h3
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at hx2
  obtain ⟨hb, ho, hw⟩ := hx2
  subst ho
  obtain rfl := eq_of_heq hw
  subst hb
  exact hx1

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}

theorem zmod_two_add_one_add_one_eq : ∀ t : ZMod 2, t + 1 + 1 = t := by
  decide

theorem SelfConjugatePlaceSetting.rowsOK (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) :
    ∃ kind : Fin N → Knd 2, RowsOK (X o).G (X o).Alt
      (prodAll (plAt N pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd 2,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    refine exists_rowsOK (X o) (F o) (Or.inl (H.alt o)) (H.hj o) _ fun g t k hk => ?_
    have hsum : ∀ s, (blkAt L o i).wt (X o) 0 s k + (blkAt L o i).wt (X o) 1 (s + 1) k ≤ gaC o s k := by
      intro s
      rw [← H.wt o s k]
      exact le_sum_map (L o) (fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k) (List.get_mem (L o) i)
    by_cases hg : g = 0
    · subst hg
      have h1 := hsum t
      exact (H.supp o t k (by omega)).2
    · have hg1 : g = 1 := Fin.eq_one_of_ne_zero g hg
      subst hg1
      have h1 := hsum (t + 1)
      rw [zmod_two_add_one_add_one_eq] at h1
      have h2 := (H.supp o (t + 1) k (by omega)).2
      rw [H.rkF_eq o 0 (t + 1)] at h2
      rw [H.rkF_eq o 1 t]
      exact h2
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj N H.plinj o) _ kind hk⟩

theorem lab_eq : ∀ g1 g2 : Fin 2, g1 ≠ g2 → ∀ t : ZMod 2,
    (if g1 = 0 then t else t + 1) = (if g2 = 0 then t + 1 else t + 1 + 1) := by
  decide

theorem SelfConjugatePlaceSetting.no_conj (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (ρ : Fin N) (o : Orb) (g1 g2 : Fin 2) (hne : g1 ≠ g2)
    (t : ZMod 2) (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hx : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ (blkProd X F N L pl).vars)
    (hx' : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ (blkProd X F N L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  have hx1 : ((ρ, ⟨o, ⟨g1, ⟨t, a1⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx
  have hx2 : ((ρ, ⟨o, ⟨g2, ⟨t + 1, a2⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx'
  have h1 := mem_vars_blkProdG hx1
  have h2 := mem_vars_blkProdG hx2
  have ht : tyW (X o).G (⟨g1, ⟨t, a1⟩⟩ : WV fun _ => IIs r tau o) = tyW (X o).G (⟨g2, ⟨t + 1, a2⟩⟩ : WV fun _ => IIs r tau o) :=
    (H.hty o g1 ⟨t, a1⟩).trans ((lab_eq g1 g2 hne t).trans (H.hty o g2 ⟨t + 1, a2⟩).symm)
  exact no_conj_of_rowsOK hk h1 h2 hne ht

end Fam

theorem isotropic_to_std_subst_harmonic : IsotropicToStdSubstHarmonic := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  have hdiag : ∀ b, (∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b'⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl)))) =
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl))) := by
    intro b
    rw [Finset.sum_eq_single b]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b' _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hdiag]
  by_cases hτ : ∃ o t, tau o t = τ
  · obtain ⟨o, t, rfl⟩ := hτ
    obtain ⟨a2', ha2⟩ := letter_cast (n := n) (H.conj o t) a2
    simp only [ha2]
    exact lap_plane plc H.inj H.gm_hyp _ o t a1 a2' fun ρ g1 g2 hne h1 h2 => H.no_conj ρ o g1 g2 hne t a1 a2' h1 h2
  · push Not at hτ
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [pderiv_comm', pderiv_subG_off plc (ℓ := ⟨τ, a1, b⟩), map_zero]
    intro z e
    exact hτ _ _ (congrArg Sigma.fst e).symm

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllOps
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem allSet_add (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    {L L' : ℕ → I g ⊕ JJ I g → C} : L ∈ X.AllSet V g → L' ∈ X.AllSet V g → L + L' ∈ X.AllSet V g := by
  intro hx hy
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, PowerSeries.mk (fun m => (L + L') m n) =
      PowerSeries.mk (fun m => L m n) + PowerSeries.mk (fun m => L' m n) := fun n => by
    ext m
    simp [PowerSeries.coeff_mk]
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add (f := _), map_add (f := _), (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add (f := _), map_add (f := _)]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => (L + L') m (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L m (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

theorem allSet_repar {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.AllSet V g)
    (hxx : ∀ n, PowerSeries.mk (fun m => x' m n) = PowerSeries.subst τ (PowerSeries.mk fun m => x m n)) :
    x' ∈ X.AllSet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.subst τ (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, hint _ (hδ i).2⟩
    exact constantCoeff_subst_zero (σ := Unit) (fun _ => hτ) (hδ i).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [alongCv_repar (fun i => (hγ i).1) hτ, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, PowerSeries.coe_substAlgHom hS, hxx]
  · intro q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [alongCv_repar (fun i => (hγ i).1) hτ, hxx, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add (f := _), map_sub,
      map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [map_smul, PowerSeries.coe_substAlgHom hS, hxx]
    · rw [map_zero]

theorem allSet_teich (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) {L : ℕ → I g ⊕ JJ I g → C} :
    L ∈ X.AllSet V g → (fun n k => c ^ n * L n k) ∈ X.AllSet V g := by
  intro hL
  refine X.allSet_repar (c • PowerSeries.X) (by simp) ?_ hL ?_
  · intro f hf n
    rw [← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale]
    exact (hc.pow n).mul_int (hf n)
  · intro n
    rw [← PowerSeries.rescale_eq_subst]
    ext m
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem allSet_lim (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    {V : VF C} {g : Fin 2} {L : ℕ → ℕ → I g ⊕ JJ I g → C} {L' : ℕ → I g ⊕ JJ I g → C} :
    (∀ k, L k ∈ X.AllSet V g) → VLim V L L' → L' ∈ X.AllSet V g := by
  intro hx hlim
  choose γ lam hγ hlam hL hM using hx
  have hmk : ∀ n : I g ⊕ JJ I g,
      TendsS V (fun k => PowerSeries.mk (fun m => L k m n)) (PowerSeries.mk (fun m => L' m n)) :=
    fun n μ K => hlim K (μ ()) n
  let Lk : ℕ → κ → PowerSeries C := fun k j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))
  let L1 : κ → PowerSeries C := fun j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L' m (Sum.inl c))
  have hLt : ∀ j, TendsS V (fun k => Lk k j) (L1 j) :=
    fun j => LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_smul _ (hmk (Sum.inl c))
  have hγc : ∀ k i, MvPowerSeries.constantCoeff (γ k i) = 0 := fun k i => (hγ k i).1
  have hLkc : ∀ k j, MvPowerSeries.constantCoeff (Lk k j) = 0 := fun k j => by
    show MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))) = 0
    rw [← hL k j]
    exact constantCoeff_subst_zero (hγc k) (hlg0 j)
  have hL1c : ∀ j, MvPowerSeries.constantCoeff (L1 j) = 0 := fun j => by
    have h0 := hLt j 0
    have e : ∀ k, MvPowerSeries.coeff 0 (Lk k j) = 0 := fun k => by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hLkc k j
    simp only [e] at h0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0.unique (tends_const 0)
  have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hexS := MvPowerSeries.hasSubst_of_constantCoeff_zero hex0
  have hγeq : ∀ k i, γ k i = MvPowerSeries.subst (Lk k) (X.ex i) := by
    intro k i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (hγc k)
    have e : Lk k = fun j => MvPowerSeries.subst (γ k) (X.lg j) := funext fun j => (hL k j).symm
    rw [e, ← MvPowerSeries.subst_comp_subst_apply hlgS hS, hexlg, MvPowerSeries.subst_X hS]
  let γ' : κ → PowerSeries C := fun i => MvPowerSeries.subst L1 (X.ex i)
  have hγt : ∀ i, TendsS V (fun k => γ k i) (γ' i) := by
    intro i
    have e : (fun k => γ k i) = fun k => MvPowerSeries.subst (Lk k) (X.ex i) := funext fun k => hγeq k i
    rw [e]
    exact TendsS.subst (f := fun _ => X.ex i) hLkc hL1c hLt (TendsS.const _)
  have hγ' : IsCv V γ' := LimTy.isCv_lim hγt hγ
  have hγ'c : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hL1S := MvPowerSeries.hasSubst_of_constantCoeff_zero hL1c
  have hlog' : ∀ i, alongCv γ' (X.lg i) = L1 i := by
    intro i
    show MvPowerSeries.subst (fun j => MvPowerSeries.subst L1 (X.ex j)) (X.lg i) = L1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hexS hL1S, hlgex, MvPowerSeries.subst_X hL1S]
  let lam' : JJ I g → PowerSeries C := fun q =>
    PowerSeries.mk (fun m => L' m (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0
  have hlamk : ∀ k q, lam k q = PowerSeries.mk (fun m => L k m (Sum.inr q)) +
      alongCv (γ k) (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0 := by
    intro k q
    rw [hM k q]
    ring
  have hlamt : ∀ q, TendsS V (fun k => lam k q) (lam' q) := by
    intro q
    have e : (fun k => lam k q) = fun k => PowerSeries.mk (fun m => L k m (Sum.inr q)) +
        alongCv (γ k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0 :=
      funext fun k => hlamk k q
    rw [e]
    refine ((hmk (Sum.inr q)).add ?_).sub
      (LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_ite _ (LimTy.tendsS_smul _ (hmk (Sum.inl c))))
    exact TendsS.subst (f := fun _ => X.sg (X.u (1 - g) q)) hγc hγ'c hγt (TendsS.const _)
  refine ⟨γ', lam', hγ', LimTy.isCv_lim hlamt hlam, hlog', fun q => ?_⟩
  simp only [lam']
  ring

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace AllStart

variable {C : Type} [Field C]

theorem linAct_sum {dd : ℕ} (φ : Pt C 1 dd) {ι : Type} (S : Finset ι) (w : ι → C) (u : ι → Fin dd → C) :
    linAct φ (∑ c ∈ S, w c • u c) = ∑ c ∈ S, w c • linAct φ (u c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem coeff_one_subst {dd : ℕ} (f : PS C 1 dd)
    (hf : ∀ (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ f = 0)
    (P : Fin 1 × Fin dd → PowerSeries C) (hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0) :
    MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P f) = 0 := by
  have hA : MvPowerSeries.HasSubst P := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
  by_cases hμ : μ.degree ≤ 1
  · rw [hf μ hμ, zero_smul]
  · push_neg at hμ
    have hX : ∀ q, (PowerSeries.X : PowerSeries C) ∣ P q := fun q => PowerSeries.X_dvd_iff.2 (hP0 q)
    have hdeg : μ.degree = ∑ s ∈ μ.support, μ s := rfl
    have h1 : (PowerSeries.X : PowerSeries C) ^ μ.degree ∣ μ.prod fun s e => P s ^ e := by
      rw [hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun s _ => pow_dvd_pow_of_dvd (hX s) _
    have hdvd : (PowerSeries.X : PowerSeries C) ^ 2 ∣ μ.prod fun s e => P s ^ e := (pow_dvd_pow _ hμ).trans h1
    have h2 := (PowerSeries.X_pow_dvd_iff.1 hdvd) 1 (by norm_num)
    rw [show MvPowerSeries.coeff (Finsupp.single () 1) (μ.prod fun s e => P s ^ e) = 0 from h2, smul_zero]

end AllStart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

end Formalism.L2.FormalSeriesBounds
end
end

