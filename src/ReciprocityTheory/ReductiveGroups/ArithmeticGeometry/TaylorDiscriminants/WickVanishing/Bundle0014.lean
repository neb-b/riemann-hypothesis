module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0004
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionSecondOfCommute
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem Dof_X (F : Fin d → PS k 2 d) (u : Fin d → k) (j : Fin d) :
    Dof F u (X ((0 : Fin 1), j)) = ∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0]
      (pderiv (R := k) ((1 : Fin 2), i) (F j)) := by
  unfold Dof
  simp only [MvPowerSeries.pderiv_X]
  rw [Finset.sum_eq_single j]
  · simp [Pi.single_apply]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem vf_fm (B : FB R d O) (h : PS k 2 d) (u φ u' : Fin d → k) :
    vf (cf k B h u φ) (fm k h u') = C (∑ i, φ i * u' i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fm, vf_sum, vf_mul, vf_C, mul_zero, add_zero, vf_sub, vf_X, vf_cf_liftX, cf_inr, add_sub_cancel_left,
    map_sum, map_mul]

theorem cf_bracket (hC : GE.DofCommSt) (B : FB R d O) (h : PS k 2 d) (u φ u' φ' : Fin d → k)
    (t : Fin d ⊕ Fin d) : vf (cf k B h u φ) (cf k B h u' φ' t) - vf (cf k B h u' φ') (cf k B h u φ t) = 0 := by
  cases t with
  | inl j =>
    rw [cf_inl, cf_inl, ← Dof_X, ← Dof_X, vf_cf_liftX, vf_cf_liftX, hC R d O k B u u', sub_self]
  | inr i =>
    rw [cf_inr, cf_inr, vf_add, vf_add, vf_C, vf_C, add_zero, add_zero, vf_cf_liftX, vf_cf_liftX,
      hC R d O k B u u', sub_self]

theorem connection_second_of_commute (hC : GE.DofCommSt) : ConnectionCommutator := by
  intro R _ d O _ _ k _ _ _ B h m ξ η G
  obtain ⟨u, φ⟩ := ξ
  obtain ⟨u', φ'⟩ := η
  simp only [nabla_eq]
  rw [vfm_comm]
  have hb : (fun t => vf (cf k B h u φ) (cf k B h u' φ' t) - vf (cf k B h u' φ') (cf k B h u φ t)) =
      fun _ => (0 : AA k d) := funext (cf_bracket k hC B h u φ u' φ')
  rw [hb, vf_zeroc, vf_Cmul, vf_Cmul, vf_fm, vf_fm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [betaH, map_mul, map_sum, map_sub, Finset.sum_sub_distrib]
  ring

theorem connection_second_identity : ConnectionCommutator :=
  connection_second_of_commute invariantDerivations_commute_formal_connection

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FormalGroupLawPointMaps
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace ReciprocityTheory.ChartRestriction.G.TB.PointMapComposition

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def mapPt {n : ℕ} (p : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map (algebraMap R k) (p i)

theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt k (pt R d j) = pt k d j := by
  funext i
  simp [mapPt, pt, MvPowerSeries.map_X]

theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mapPt k (comp1 φ a) = comp1 (mapPt k φ) (mapPt k a) := by
  funext i
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![a] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, l⟩; fin_cases j; exact ha l)
  simp only [mapPt, comp1, ev]
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext p
  rcases p with ⟨j, l⟩
  fin_cases j
  rfl

theorem mapPt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (u v : Pt R n d) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    mapPt k (addOf F u v) = addOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (mapPt k u) (mapPt k v) := by
  funext i
  have hs : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, l⟩; fin_cases j
      · exact hu l
      · exact hv l)
  simp only [mapPt, addOf, ev]
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext p
  rcases p with ⟨j, l⟩
  fin_cases j <;> rfl

def actKO (B : FB R d O) : OAct O (Nab.lawK k B) where
  act a := B.actK k a
  const a i := by simp [FB.actK, B.A.const a i]
  hom a := by
    have h := congrArg (mapPt k) (B.A.hom a)
    have hp0 : ∀ i, constantCoeff (pt R (n := 2) d 0 i) = 0 := LogPf.cc_pt 0
    have hp1 : ∀ i, constantCoeff (pt R (n := 2) d 1 i) = 0 := LogPf.cc_pt 1
    have hadd : ∀ i, constantCoeff (B.G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1) i) = 0 := fun i =>
      constantCoeff_ev (CZ.cons hp0 (CZ.cons hp1 CZ.nil)) (B.G.const i)
    have hc : ∀ (j : Fin 2) i, constantCoeff (comp1 (B.A.act a) (pt R (n := 2) d j) i) = 0 := fun j i =>
      constantCoeff_ev (CZ.cons (LogPf.cc_pt j) CZ.nil) (B.A.const a i)
    rw [mapPt_comp1 k _ _ hadd, mapPt_addOf k _ _ _ hp0 hp1, mapPt_addOf k _ _ _ (hc 0) (hc 1),
      mapPt_comp1 k _ _ hp0, mapPt_comp1 k _ _ hp1, mapPt_pt, mapPt_pt] at h
    exact h
  add_act a b := by
    have h := congrArg (mapPt k) (B.A.add_act a b)
    rw [mapPt_addOf k _ _ _ (B.A.const a) (B.A.const b)] at h
    exact h
  mul_act a b := by
    have h := congrArg (mapPt k) (B.A.mul_act a b)
    rw [mapPt_comp1 k _ _ (B.A.const b)] at h
    exact h
  one_act := by
    have h := congrArg (mapPt k) B.A.one_act
    rw [mapPt_pt] at h
    exact h

end ReciprocityTheory.ChartRestriction.G.TB.PointMapComposition
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyPointZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Int

variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]

def Ig (σ : Type) : Subring (MvPowerSeries σ k) := (MvPowerSeries.map (σ := σ) (algebraMap R k)).range

variable {R k}

theorem ig_map {σ : Type} (f : MvPowerSeries σ R) : MvPowerSeries.map (algebraMap R k) f ∈ Ig R k σ := RingHom.mem_range.mpr ⟨f, rfl⟩

theorem ig_C {σ : Type} (r : R) : (C (algebraMap R k r) : MvPowerSeries σ k) ∈ Ig R k σ := RingHom.mem_range.mpr ⟨C r, by simp⟩

theorem ig_X {σ : Type} (s : σ) : (X s : MvPowerSeries σ k) ∈ Ig R k σ := RingHom.mem_range.mpr ⟨X s, by simp⟩

theorem map_pderiv' {σ : Type} (f : MvPowerSeries σ R) (v : σ) :
    MvPowerSeries.map (algebraMap R k) (pderiv v f) = pderiv v (MvPowerSeries.map (algebraMap R k) f) := by
  ext n
  simp only [coeff_map, coeff_pderiv, map_mul, map_add, map_natCast, map_one]

theorem ig_pderiv {σ : Type} {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) (v : σ) : pderiv v f ∈ Ig R k σ := by
  obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hf
  exact RingHom.mem_range.mpr ⟨pderiv v g, map_pderiv' g v⟩

theorem ig_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, a s ∈ Ig R k τ)
    (hc : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) : subst a f ∈ Ig R k τ := by
  choose a' ha' using fun s => RingHom.mem_range.1 (ha s)
  obtain ⟨f', rfl⟩ := RingHom.mem_range.1 hf
  set b : σ → MvPowerSeries τ R := fun s => a' s - C (constantCoeff (a' s)) with hb
  have hbc : ∀ s, constantCoeff (b s) = 0 := fun s => by simp [hb]
  have hmap : ∀ s, MvPowerSeries.map (algebraMap R k) (b s) = a s := fun s => by
    have e1 : algebraMap R k (constantCoeff (a' s)) = 0 := by
      rw [← hc s, ← ha' s, constantCoeff_map]
    simp [hb, ha' s, e1]
  refine RingHom.mem_range.2 ⟨subst b f', ?_⟩
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero hbc)]
  simp only [hmap]

theorem ig_ev {m n d : ℕ} {a : Fin m → Pt k n d} (hc : CZ a) (ha : ∀ j i, a j i ∈ Ig R k (Fin n × Fin d))
    {f : PS k m d} (hf : f ∈ Ig R k (Fin m × Fin d)) : ev a f ∈ Ig R k (Fin n × Fin d) := by
  unfold ev
  refine ig_subst (a := fun p : Fin m × Fin d => a p.1 p.2) ?_ ?_ hf
  · intro p
    exact ha p.1 p.2
  · intro p
    exact hc p.1 p.2

theorem ig_liftX [Algebra ℚ k] {d : ℕ} {f : PS k 1 d} (hf : f ∈ Ig R k (Fin 1 × Fin d)) :
    liftX k f ∈ Ig R k (Fin d ⊕ Fin d) := by
  unfold liftX
  refine ig_subst ?_ ?_ hf
  · intro p
    exact ig_X _
  · intro p
    exact MvPowerSeries.constantCoeff_X _

theorem ig_of_intAA {σ : Type} {G : MvPowerSeries σ k} (hG : IntAA (R := R) k G) : G ∈ Ig R k σ := by
  unfold IntAA at hG
  refine RingHom.mem_range.mpr ⟨(fun n => (hG n).choose : MvPowerSeries σ R), ?_⟩
  ext n
  exact (hG n).choose_spec

theorem cc_ev' {K : Type} [CommRing K] {m n d : ℕ} {a : Fin m → Pt K n d} (ha : CZ a) (f : PS K m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']

theorem pderiv_expS [Algebra ℚ k] {n d : ℕ} {f : PS k n d} (hf : constantCoeff f = 0) (v : Fin n × Fin d) :
    pderiv v (FB.expS k f) = FB.expS k f * pderiv v f := by
  rw [FB.expS, Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]

theorem ig_dlog [Algebra ℚ k] {n d : ℕ} (U : PS R n d) (hU : constantCoeff U = 1) (H : PS k n d)
    (hH : constantCoeff H = 0) (he : MvPowerSeries.map (algebraMap R k) U = FB.expS k H) (v : Fin n × Fin d) :
    pderiv v H ∈ Ig R k (Fin n × Fin d) := by
  have h1 : pderiv v (MvPowerSeries.map (algebraMap R k) U) =
      MvPowerSeries.map (algebraMap R k) U * pderiv v H := by
    rw [he]
    exact pderiv_expS hH v
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 :=
    MvPowerSeries.mul_invOfUnit U 1 (by rw [hU, Units.val_one])
  have h2 : pderiv v H =
      MvPowerSeries.map (algebraMap R k) (MvPowerSeries.invOfUnit U 1 * pderiv v U) := by
    rw [map_mul, map_pderiv', h1, ← mul_assoc, ← map_mul, mul_comm (MvPowerSeries.invOfUnit U 1) U,
      hinv, map_one, one_mul]
  rw [h2]
  exact ig_map _

end Int

section Fam

variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {d : ℕ}

theorem ig_pt {n : ℕ} (j : Fin n) (i : Fin d) : pt k d j i ∈ Ig R k (Fin n × Fin d) := by
  unfold pt
  exact ig_X _

theorem integral_family_point_zero : ∀ j i, (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) j i ∈ Ig R k (Fin 1 × Fin d) := by
  intro j i
  fin_cases j
  · first
      | exact ig_pt 0 i
      | simpa using ig_pt (R := R) (k := k) (0 : Fin 1) i
  · first
      | exact (Ig R k _).zero_mem
      | simpa using (Ig R k (Fin 1 × Fin d)).zero_mem

theorem integral_family_pair_zero : ∀ j i, (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j i ∈ Ig R k (Fin 2 × Fin d) := by
  intro j i
  fin_cases j
  · first
      | exact ig_pt 0 i
      | simpa using ig_pt (R := R) (k := k) (0 : Fin 2) i
  · first
      | exact ig_pt 1 i
      | simpa using ig_pt (R := R) (k := k) (1 : Fin 2) i
  · first
      | exact (Ig R k _).zero_mem
      | simpa using (Ig R k (Fin 2 × Fin d)).zero_mem

end Fam

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

