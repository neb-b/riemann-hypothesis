module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def ActLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O)
    (ℓ ε : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (B.G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    IsInvPair ε ℓ → ∀ (a : O) (i : Fin d),
      comp1 ℓ (comp1 (B.A.act a) ε) i = ∑ j, C (dLin (B.A.act a) i j) * X ((0 : Fin 1), j)

namespace WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem hom_at {d : ℕ} {O : Type} [CommRing O] (G : FGLaw k d) (A : OAct O G) (a : O) {n : ℕ}
    (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 (A.act a) (addOf G.F u v) = addOf G.F (comp1 (A.act a) u) (comp1 (A.act a) v) := by
  have huv : ∀ j i, constantCoeff ((![u, v] : Fin 2 → Pt k n d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hpt : ∀ (m : ℕ) (j : Fin m) (i : Fin d), constantCoeff (pt k (n := m) d j i) = 0 := fun m j i =>
    MvPowerSeries.constantCoeff_X _
  have hp01 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j <;> exact hpt _ _ _
  have hp0 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hp1 : ∀ j i, constantCoeff ((![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hadd01 : ∀ j i, constantCoeff ((![addOf G.F (pt k (n := 2) d 0) (pt k (n := 2) d 1)] :
      Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ hp01 (G.const i)
  have hc01 : ∀ j i, constantCoeff ((![comp1 (A.act a) (pt k (n := 2) d 0), comp1 (A.act a) (pt k (n := 2) d 1)] :
      Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_ev _ hp0 (A.const a i)
    · exact cc_ev _ hp1 (A.const a i)
  have hev2 : ∀ (j : Fin 2) (l : Fin d), ev (![u, v] : Fin 2 → Pt k n d)
      ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j l) = (![u, v] : Fin 2 → Pt k n d) j l := by
    intro j l
    fin_cases j
    · exact ev_X _ huv 0 l
    · exact ev_X _ huv 1 l
  funext i
  have h := congrArg (ev (![u, v] : Fin 2 → Pt k n d)) (congrFun (A.hom a) i)
  simp only [comp1, FGLaw.add, addOf] at h ⊢
  rw [ev_ev _ _ hadd01 huv, ev_ev _ _ hc01 huv] at h
  convert h using 2
  · funext j l
    fin_cases j
    simp only [addOf, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
    rw [ev_ev _ _ hp01 huv]
    congr 1
    funext j' l'
    exact (hev2 j' l').symm
  · funext j l
    fin_cases j
    · simp only [comp1, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
      rw [ev_ev _ _ hp0 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 0 l').symm
    · simp only [comp1, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
      rw [ev_ev _ _ hp1 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 1 l').symm

theorem dLin_pt {d : ℕ} : dLin (pt k (n := 1) d 0) = 1 := by
  ext i j
  simp only [dLin, pt, Matrix.one_apply, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h2
    apply h
    have h3 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h2
    exact (Prod.mk.inj h3).2.symm

open Formalism.FG.SolveVAux in
theorem action_linear : ActLinSt := by
  have single_of_degree : ∀ {σ : Type} (n : σ →₀ ℕ), n.degree = 1 → ∃ p, n = Finsupp.single p 1 := by
    intro σ n h
    classical
    have hc : Multiset.card (Finsupp.toMultiset n) = 1 := by
      rw [Finsupp.card_toMultiset, ← h]
      rfl
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hc
    refine ⟨p, ?_⟩
    have h2 := congrArg Multiset.toFinsupp hp
    rw [Finsupp.toMultiset_toFinsupp, Multiset.toFinsupp_singleton] at h2
    exact h2
  intro k _ _ d O _ _ B ℓ ε hℓ0 hℓ1 hadd hinv a i
  obtain ⟨hε0, -, hεℓ, hℓε⟩ := hinv
  have hA0 : ∀ i, constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hcc1 : ∀ {n : ℕ} (φ : Pt k 1 d) (w : Pt k n d), (∀ i, constantCoeff (φ i) = 0) →
      (∀ i, constantCoeff (w i) = 0) → ∀ i, constantCoeff (comp1 φ w i) = 0 := fun φ w hφ hw i =>
    cc_ev _ (fun j l => by fin_cases j; exact hw l) (hφ i)
  have hccA : ∀ {n : ℕ} (u v : Pt k n d), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (addOf B.G.F u v i) = 0 := fun u v hu hv i =>
    cc_ev _ (fun j l => by
      fin_cases j
      · exact hu l
      · exact hv l) (B.G.const i)
  have hpt : ∀ {n : ℕ} (w : Pt k n d), (∀ i, constantCoeff (w i) = 0) → comp1 (pt k (n := 1) d 0) w = w := by
    intro n w hw
    funext i
    exact ev_X _ (fun j l => by fin_cases j; exact hw l) 0 i
  have hx : ∀ i, constantCoeff (pt k (n := 2) d 0 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hy : ∀ i, constantCoeff (pt k (n := 2) d 1 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hxy : ∀ i, constantCoeff ((pt k (n := 2) d 0 + pt k (n := 2) d 1) i) = 0 := fun i => by
    simp [pt]
  have hεx := hcc1 ε _ hε0 hx
  have hεy := hcc1 ε _ hε0 hy
  have hAε : ∀ i, constantCoeff (comp1 (B.A.act a) ε i) = 0 := hcc1 _ _ hA0 hε0
  have S1 : comp1 ℓ (addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1))) =
      pt k (n := 2) d 0 + pt k (n := 2) d 1 := by
    rw [add_at B.G ℓ hadd _ _ hεx hεy, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hx, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hy, hℓε, hpt _ hx, hpt _ hy]
  have S2 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← S1, germComp1_germComp1_eq_substitute ε ℓ _ hℓ0 (hccA _ _ hεx hεy), hεℓ, hpt _ (hccA _ _ hεx hεy)]
  have S4 : comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1))) =
      comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0))) +
        comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 1))) := by
    rw [S2, hom_at B.G B.A a _ _ hεx hεy, add_at B.G ℓ hadd _ _ (hcc1 _ _ hA0 hεx) (hcc1 _ _ hA0 hεy)]
  have hF : ∀ w : Pt k 2 d, (∀ i, constantCoeff (w i) = 0) →
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) w = comp1 ℓ (comp1 (B.A.act a) (comp1 ε w)) := by
    intro w hw
    rw [← germComp1_germComp1_eq_substitute _ _ _ hAε hw, ← germComp1_germComp1_eq_substitute _ _ _ hε0 hw]
  have hfadd : comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0) +
        comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 1) := by
    rw [hF _ hxy, hF _ hx, hF _ hy]
    exact S4
  have hlin := addition_linear k d (comp1 ℓ (comp1 (B.A.act a) ε) i) (congrFun hfadd i)
  have hdε : dLin ε = 1 := by
    have h := dLin_comp1 ε ℓ hℓ0
    rw [hεℓ, dLin_pt, hℓ1, mul_one] at h
    exact h.symm
  have hdf : dLin (comp1 ℓ (comp1 (B.A.act a) ε)) = dLin (B.A.act a) := by
    rw [dLin_comp1 ℓ _ hAε, dLin_comp1 _ ε hε0, hℓ1, hdε, one_mul, mul_one]
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : n.degree = 1
  · obtain ⟨p, rfl⟩ := single_of_degree n hn
    obtain ⟨z, j0⟩ := p
    obtain rfl : z = 0 := Subsingleton.elim _ _
    have h1 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j0) 1) (comp1 ℓ (comp1 (B.A.act a) ε) i) =
        dLin (B.A.act a) i j0 := by
      rw [← hdf]
      rfl
    rw [h1, Finset.sum_eq_single j0]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      apply hj
      have h2 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h
      exact (Prod.mk.inj h2).2.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hlin n hn]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (Finsupp.degree_single _ _)

end WickVanishing

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionKillsSeries
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section VF

variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

def vf (c : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) : MvPowerSeries τ k :=
  ∑ t, c t * pderiv (R := k) t G

theorem vf_add (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) : vf c (f + G) = vf c f + vf c G := by
  simp only [vf, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem vf_sub (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) : vf c (f - G) = vf c f - vf c G := by
  simp only [vf, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem vf_sum {ι : Type} (s : Finset ι) (c : τ → MvPowerSeries τ k) (f : ι → MvPowerSeries τ k) :
    vf c (∑ i ∈ s, f i) = ∑ i ∈ s, vf c (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vf, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem vf_C (c : τ → MvPowerSeries τ k) (a : k) : vf c (C a) = 0 := by
  simp [vf, MvPowerSeries.pderiv_C]

theorem vf_zeroc (G : MvPowerSeries τ k) : vf (fun _ => (0 : MvPowerSeries τ k)) G = 0 := by
  simp [vf]

theorem vf_mul (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) :
    vf c (f * G) = vf c f * G + f * vf c G := by
  simp only [vf, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem vf_X (c : τ → MvPowerSeries τ k) (s : τ) : vf c (X s) = c s := by
  classical
  simp [vf, MvPowerSeries.pderiv_X, Pi.single_apply]

end VF

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem liftX_hs : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

def liftHom : PS k 1 d →+* AA k d := (substAlgHom (liftX_hs (d := d) k)).toRingHom

theorem liftHom_apply (f : PS k 1 d) : liftHom k f = liftX k f := by
  simp only [liftHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_apply]
  rfl

theorem liftX_zero : liftX k (0 : PS k 1 d) = 0 := by
  rw [← liftHom_apply, map_zero]

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g := by
  simp only [← liftHom_apply, map_mul]

theorem liftX_sum {ι : Type} (s : Finset ι) (f : ι → PS k 1 d) :
    liftX k (∑ i ∈ s, f i) = ∑ i ∈ s, liftX k (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← liftHom_apply, map_sum]

theorem pderiv_inl_liftX (f : PS k 1 d) (j : Fin d) :
    pderiv (R := k) (Sum.inl j) (liftX k f) = liftX k (pderiv (R := k) ((0 : Fin 1), j) f) := by
  classical
  let e : (Fin 1 × Fin d) ↪ (Fin d ⊕ Fin d) :=
    ⟨fun p => Sum.inl p.2, fun _ _ h => Prod.ext (Subsingleton.elim _ _) (Sum.inl.inj h)⟩
  have hlift (g : PS k 1 d) : liftX k g = rename e g :=
    (MvPowerSeries.rename_eq_subst e g).symm
  simp only [hlift]
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  by_cases hn : n ∈ Set.range (Finsupp.embDomain e)
  · obtain ⟨m, rfl⟩ := hn
    change coeff (Finsupp.embDomain e m + Finsupp.single (e (0, j)) 1) (rename e f) *
      (Finsupp.embDomain e m (e (0, j)) + 1) =
        coeff (Finsupp.embDomain e m) (rename e (pderiv (0, j) f))
    rw [← Finsupp.embDomain_single, ← Finsupp.embDomain_add,
      MvPowerSeries.coeff_embDomain_rename, Finsupp.embDomain_apply_self,
      MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_pderiv]
  · have hshift : n + Finsupp.single (Sum.inl j) 1 ∉ Set.range (Finsupp.embDomain e) :=
      fun h => hn (Finsupp.isLowerSet_range_embDomain e (le_iff_exists_add.mpr ⟨_, rfl⟩) h)
    have he : Finsupp.embDomain e = (Finsupp.mapDomain e : (Fin 1 × Fin d →₀ ℕ) → _) :=
      funext (Finsupp.embDomain_eq_mapDomain e)
    rw [he] at hn hshift
    rw [MvPowerSeries.coeff_rename_eq_zero e f hshift, zero_mul,
      MvPowerSeries.coeff_rename_eq_zero e _ hn]

theorem pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) :
    pderiv (R := k) (Sum.inr i) (liftX k f) = 0 := by
  classical
  let e : (Fin 1 × Fin d) ↪ (Fin d ⊕ Fin d) :=
    ⟨fun p => Sum.inl p.2, fun _ _ h => Prod.ext (Subsingleton.elim _ _) (Sum.inl.inj h)⟩
  have hlift : liftX k f = rename e f := (MvPowerSeries.rename_eq_subst e f).symm
  rw [hlift]
  ext n
  have hshift : n + Finsupp.single (Sum.inr i) 1 ∉ Set.range (Finsupp.mapDomain e) := by
    rintro ⟨m, hm⟩
    have hzero : Finsupp.embDomain e m (Sum.inr i) = 0 := by
      apply Finsupp.embDomain_of_notMem_range
      rintro ⟨p, hp⟩
      exact Sum.inl_ne_inr hp
    rw [Finsupp.embDomain_eq_mapDomain, hm] at hzero
    simp at hzero
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_rename_eq_zero e f hshift, zero_mul, map_zero]

def cf (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) : Fin d ⊕ Fin d → AA k d :=
  Sum.elim (fun j => liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0]
    (pderiv (R := k) ((1 : Fin 2), i) (B.FK k j))))
    (fun i => liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i))

def fm (h : PS k 2 d) (u : Fin d → k) : AA k d := ∑ i : Fin d, (X (Sum.inr i) - liftX k (sgOf k h i)) * C (u i)

theorem cf_inl (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (j : Fin d) :
    cf k B h u φ (Sum.inl j) =
      liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0]
        (pderiv (R := k) ((1 : Fin 2), i) (B.FK k j))) := rfl

theorem cf_inr (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (i : Fin d) :
    cf k B h u φ (Sum.inr i) = liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i) := rfl

theorem nabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (G : AA k d) :
    nabla k B h m u φ G = vf (cf k B h u φ) G - (C (m : k) * fm k h u) * G := by
  unfold nabla vf fm Dx
  rw [Fintype.sum_sum_type]
  simp only [cf_inl, cf_inr, add_mul, Finset.sum_add_distrib]
  ring

theorem vf_cf_liftX (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (g : PS k 1 d) :
    vf (cf k B h u φ) (liftX k g) = liftX k (Dof (B.FK k) u g) := by
  unfold vf
  rw [Fintype.sum_sum_type]
  simp only [cf_inl, pderiv_inl_liftX, pderiv_inr_liftX, mul_zero, Finset.sum_const_zero, add_zero]
  unfold Dof
  rw [liftX_sum]
  simp only [liftX_mul]

theorem connection_kills_series : ConnectionKillsSeries := by
  intro R _ d O _ _ k _ _ _ B h m φ f
  rw [nabla_eq, vf_cf_liftX]
  simp [fm, Dof, liftX_zero]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_add (f := _)]

theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_mul]

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  exact congrFun (MvPowerSeries.coe_substAlgHom ha.hasSubst) f

theorem ev_sub {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f - g) = ev a f - ev a g := by
  rw [← evHom_apply ha, ← evHom_apply ha, ← evHom_apply ha, map_sub]

theorem ev_neg {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by
  rw [← evHom_apply ha, ← evHom_apply ha, map_neg]

theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← evHom_apply ha, map_sum]
  exact Finset.sum_congr rfl (fun x _ => evHom_apply ha (f x))

theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, show (C c : PS k m d) = algebraMap k (PS k m d) c from rfl, AlgHom.commutes]
  rfl

theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  MvPowerSeries.subst_X ha.hasSubst (j, i)

theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  rw [← evHom_apply ha, map_zero]

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  exact MvPowerSeries.subst_comp_subst_apply hb.hasSubst ha.hasSubst f

theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  show MvPowerSeries.subst (fun p : Fin m × Fin d => (X p : PS k m d)) f = f
  rw [show (fun p : Fin m × Fin d => (X p : PS k m d)) = X from rfl, MvPowerSeries.subst_self]
  rfl

theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => MvPowerSeries.constantCoeff_X _

open scoped MvPowerSeries.WithPiTopology in
theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv v (ev a f) = ∑ p : Fin m × Fin d, ev a (pderiv p f) * pderiv v (a p.1 p.2) := by
  classical
  let : UniformSpace k := ⊥
  let b : Fin m × Fin d → PS k n d := fun p => a p.1 p.2
  change pderiv v (subst b f) = ∑ p, subst b (pderiv p f) * pderiv v (b p)
  have hsubst : Continuous (subst b : PS k m d → PS k n d) := continuous_subst ha.hasSubst
  have hderiv {σ : Type} (i : σ) : Continuous (pderiv (R := k) i) := by
    apply continuous_pi
    intro e
    change Continuous (fun g => coeff e (pderiv i g))
    simp only [coeff_pderiv]
    exact (WithPiTopology.continuous_coeff k _).mul continuous_const
  refine congrFun (WithPiTopology.denseRange_toMvPowerSeries.equalizer
    (hderiv v |>.comp hsubst) (continuous_finsetSum _ fun p _ =>
      (hsubst.comp (hderiv p)).mul continuous_const) ?_) f
  funext q
  change pderiv v (subst b (q : PS k m d)) =
    ∑ p, subst b (pderiv p (q : PS k m d)) * pderiv v (b p)
  simp only [pderiv_coe, subst_coe]
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add q r hq hr => simp only [map_add, hq, hr, add_mul, Finset.sum_add_distrib]
  | mul_X q p hq =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hq, smul_eq_mul, smul_eq_mul,
      Finset.mul_sum]
    simp [Pi.single_apply, apply_ite (MvPolynomial.aeval b), add_mul, Finset.sum_add_distrib,
      mul_assoc]

theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

