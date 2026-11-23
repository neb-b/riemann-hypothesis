module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemValInOfInvariantAndValuesMemPow
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.mem_valIn_of_invariant_and_values_mem_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (k c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ f ∈ X.Sp τ θ U, (∀ y ∈ X.I.Nm c, X.rp A m y f - f ∈ X.valIn A m k) → (∀ i j, f (x i) j ∈ maximalIdeal A ^ k) → f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U k c N x hx f hf hy h0
  have hv : ∀ F : X.Fn A m, F ∈ X.valIn A m k ↔ ∀ g i, F g i ∈ maximalIdeal A ^ k := fun F => by
    simp [Frame.valIn, Submodule.mem_pi]
  have hrp : ∀ (b : Gp) (g : Ga × Gp), X.rp A m b f g = f (g * (1, b)) := fun _ _ => rfl
  obtain ⟨⟨h1, h2, h3, -⟩, h4⟩ := hf
  rw [hv]
  intro g
  obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨n, hn, t, ht, y, hy', rfl⟩ := (iwMem Gp X.I c b).1.1 hb
  have a1 : ∀ j, f (x i * ((u : Ga), 1)) j ∈ maximalIdeal A ^ k := by
    intro j
    have e := congrFun (h4 u⁻¹ (inv_mem hu)) (x i * ((u : Ga), 1))
    rw [Frame.ra_apply] at e
    have e2 : x i * ((u : Ga), (1 : Gp)) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = x i := by
      ext <;> simp
    rw [← e, e2]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h0 _ l)
  have a2 : ∀ j, f (x i * ((u : Ga), 1) * (1, n)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h2 n hn]
    exact a1 j
  have a3 : ∀ j, f (x i * ((u : Ga), 1) * (1, n) * (1, t)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h3 ⟨t, ht⟩]
    exact Ideal.mul_mem_left _ _ (a2 j)
  intro j
  have a4 := add_mem ((hv _).1 (hy y hy') (x i * ((u : Ga), 1) * (1, n) * (1, t)) j) (a3 j)
  rw [Pi.sub_apply, Pi.sub_apply, sub_add_cancel, hrp] at a4
  rw [mul_assoc, h1]
  convert a4 using 2
  ext <;> simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDetEqOne
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc Matrix

private theorem scal_mem {O L : Type} [CommRing O] [CommRing L] [Algebra O L] (u : Lˣ)
    (d : (integralClosure O L)ˣ)
    (h : u ^ 2 * Units.map ((integralClosure O L).val : integralClosure O L →* L) d = 1) :
    ∃ w : (integralClosure O L)ˣ, Units.map ((integralClosure O L).val : integralClosure O L →* L) w = u := by
  have h1 : u ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have h2 : u⁻¹ ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d := by
    rw [inv_pow, h1, map_inv, inv_inv]
  have i1 : IsIntegral O (u : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h1]
    exact ((d⁻¹ : (integralClosure O L)ˣ) : integralClosure O L).2
  have i2 : IsIntegral O ((u⁻¹ : Lˣ) : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h2]
    exact (d : integralClosure O L).2
  exact ⟨⟨⟨u, i1⟩, ⟨(u⁻¹ : Lˣ), i2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Units.ext rfl⟩

theorem UpperTheory.orbitalFiber_det_eq_one :
    UpperTheory.V.Z.Sym.Glob.Fib.DetOne := by
  intro O K _ _ _ Δ g hg hs
  have hn : (ZD Δ).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have : x * n * x⁻¹ = n := by
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hn
      rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hz]
      apply Units.ext
      exact ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm).eq
    rwa [this]
  obtain ⟨s, hsz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine mul_mem ?_ hk
  obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hsz
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_subgroupOf.1 hk
  have hd : GeneralLinearGroup.det ((s : GL (Fin 2) (Lsq K Δ)) * (k : GL (Fin 2) (Lsq K Δ))) = 1 := hs
  rw [map_mul, ← hz, ← hk₀] at hd
  obtain ⟨w, hw⟩ := scal_mem (O := O) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)
    (GeneralLinearGroup.det k₀) (by
      rw [← hd]
      congr 1
      · apply Units.ext
        simp [pow_two])
  refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.scalar (Fin 2) w, ?_⟩
  rw [← hz, MonoidHom.comp_apply, ← hw]
  apply Units.ext
  ext i j : 1
  by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetConj
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private lemma zd_comm {K : Type} [Field K] {Δ : K} {z : DX Δ} (hz : z ∈ ZD Δ) (g : DX Δ) : z * g = g * z := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.val_mul]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq

private lemma conj_sup {G : Type} [Group G] (Z J : Subgroup G) (f : G → ℂ)
    (hZ : ∀ z ∈ Z, ∀ g, z * g = g * z) (hJ : ∀ u ∈ J, ∀ g, f (u⁻¹ * g * u) = f g) :
    ∀ u ∈ Z ⊔ J, ∀ g, f (u⁻¹ * g * u) = f g := by
  let S : Subgroup G :=
    { carrier := {u | ∀ g, f (u⁻¹ * g * u) = f g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        have : (a * b)⁻¹ * g * (a * b) = b⁻¹ * (a⁻¹ * g * a) * b := by group
        rw [this, hb, ha]
      inv_mem' := by
        intro a ha g
        rw [← ha]
        congr 1
        group }
  have h : Z ⊔ J ≤ S := by
    refine sup_le (fun z hz g => ?_) (fun u hu => hJ u hu)
    rw [mul_assoc, ← hZ z hz, inv_mul_cancel_left]
  exact fun u hu => h hu

theorem UpperTheory.orbitalFiber_fixedSet_conj :
    UpperTheory.V.Z.Sym.Glob.Fib.FSConj := by
  intro F _ _ Δ D hD t ht u hu g
  unfold Dat.FS
  refine finprod_congr fun v => ?_
  have huv : u.1 v ∈ ZD _ ⊔ D.J2v v := by
    simp only [Dat.UZ, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hu
    exact hu v
  show D.fSv t v ((u.1 v)⁻¹ * g.1 v * u.1 v) = D.fSv t v (g.1 v)
  refine conj_sup _ _ (D.fSv t v) (fun z hz => zd_comm hz) ?_ _ huv _
  intro k hk y
  unfold Dat.fSv
  unfold Dat.J2v at hk
  by_cases hv : v ∈ D.Sg
  · simp only [if_pos hv] at hk ⊢
    have H := (hD.sig v hv).S_inv (t v) (ht v hv)
    rw [(H k hk _).2, (H _ (inv_mem hk) _).1]
  · simp only [if_neg hv] at hk ⊢
    congr 1
    apply propext
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetSupport
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix

private theorem hasTr_conj {K : Type} [Field K] {Δ : K} (γ h : DX Δ) (s : K) (hs : HasTr γ s) :
    HasTr (h⁻¹ * γ * h) s := by
  have e : Glob.mt (h⁻¹ * γ * h) = ((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) * Glob.mt γ * Glob.mt h := by
    rfl
  have e1 : Glob.mt h * (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = 1 :=
    Units.mul_inv _
  refine ⟨?_, ?_⟩
  · rw [e, det_mul_comm, ← mul_assoc, e1, one_mul, hs.1]
  · rw [e, trace_mul_comm, ← mul_assoc, e1, one_mul, hs.2]

private theorem hasTr_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (γ : DX Δ) (γ' : DX (f Δ)) (s : K)
    (h : Glob.mt γ' = (Glob.mt γ).map (lmap f Δ)) (hs : HasTr γ s) : HasTr γ' (f s) := by
  refine ⟨?_, ?_⟩
  · rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs.1, map_one]
  · rw [h, ← AddMonoidHom.map_trace, hs.2]
    ext <;> simp [lmap]

private theorem ne_zero_of_finprod {I : Type} (f : I → ℂ) (hf : (Function.mulSupport f).Finite) (h : ∏ᶠ i, f i ≠ 0) (i : I) :
    f i ≠ 0 := by
  intro h0
  apply h
  rw [finprod_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := i) ?_ h0
  simp [h0]

theorem UpperTheory.orbitalFiber_fixedSet_support :
    UpperTheory.V.Z.Sym.Glob.Fib.FSSupp := by
  intro F _ _ Δ D hD ι hι t ht γ s g hs hne v hv
  have hconj : HasTr ((g⁻¹ * ι γ * g).1 v) (cv v s) :=
    hasTr_conj ((ι γ).1 v) (g.1 v) _ (hasTr_map (cv v) γ _ s (hι γ v) hs)
  generalize g⁻¹ * ι γ * g = x at hconj hne
  have hfin : (Function.mulSupport fun w => D.fSv t w (x.1 w)).Finite := by
    have h1 : {w | ¬ x.1 w ∈ KD (cv w Δ) (Ov w)}.Finite := Filter.eventually_cofinite.1 x.2
    refine (h1.union D.Sg.finite_toSet).subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
    apply hw
    simp only [Dat.fSv, if_neg hc.2, Glob.one, if_pos hc.1]
  have h := ne_zero_of_finprod _ hfin hne v
  simp only [Dat.fSv, if_pos hv] at h
  exact (hD.sig v hv).S_supp _ (ht v hv) _ _ hconj h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberHasTraceLaw
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
private theorem UpperTheory.star_diagonal_entry_eq {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    star (mt γ 0 0) = mt γ 1 1 := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) (γ : GL (Fin 2) (Lsq K Δ)) =
      (wJ Δ)⁻¹ * (γ : GL (Fin 2) (Lsq K Δ)) * ((wJ Δ)⁻¹)⁻¹ := γ.2
  have h1 := congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) h
  have hw : (((wJ Δ)⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, -1; 1, 0] := rfl
  have hw' : ((wJ Δ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, 1; -1, 0] := rfl
  simp only [inv_inv, Units.val_mul, hw, hw'] at h1
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] using h1

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
theorem UpperTheory.orbitalFiber_hasTraceLaw :
    UpperTheory.V.Z.Sym.Glob.Fib.HasTrLaw := by
  intro K _ Δ γ
  have hmem : γ ∈ SU Δ ↔ (mt γ).det = 1 := by
    rw [SU, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hmem]
    constructor
    · intro hd
      refine ⟨(mt γ).trace.re, hd, ?_⟩
      have := UpperTheory.star_diagonal_entry_eq γ
      ext
      · simp
      · rw [Matrix.trace_fin_two, ← this]
        simp
    · rintro ⟨s, hs, _⟩
      exact hs
  · intro s s' hs hs'
    have := congrArg QuadraticAlgebra.re (hs.2.symm.trans hs'.2)
    simpa using this
  · intro h s
    have e : mt (h * γ * h⁻¹) = ((h : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt γ *
        (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := rfl
    unfold HasTr
    rw [e, Matrix.det_units_conj, Matrix.trace_units_conj]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPairCorrespondence
section
open MulAction UpperTheory.V.Z.Sym

private structure PairSp (H G : Type) [Group G] (U : Subgroup G) : Type where
  fst : H
  snd : G ⧸ U

@[instance_reducible] private def pairAct {H G : Type} [Group H] [Group G] (j : H →* G) (U : Subgroup G) :
    MulAction H (PairSp H G U) where
  smul h p := ⟨h * p.1 * h⁻¹, j h • p.2⟩
  one_smul p := by
    show (⟨(1 : H) * p.1 * (1 : H)⁻¹, j 1 • p.2⟩ : PairSp H G U) = p
    simp
  mul_smul a b p := by
    show (⟨a * b * p.1 * (a * b)⁻¹, j (a * b) • p.2⟩ : PairSp H G U) =
      ⟨a * (b * p.1 * b⁻¹) * a⁻¹, j a • j b • p.2⟩
    simp [mul_assoc, mul_smul]

private theorem out_eq_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem pair_inv_mul_eq_of_mul_self_eq_one {H G : Type} [Group H] [Group G] (a b o u : G) (key : a⁻¹ * (b * a) = b) :
    (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * (o⁻¹ * b * o) * u := by
  calc (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * o⁻¹ * (a⁻¹ * (b * a)) * o * u := by group
    _ = u⁻¹ * (o⁻¹ * b * o) * u := by rw [key]; group

theorem UpperTheory.orbitalFiber_pair_correspondence :
    UpperTheory.V.Z.Sym.Glob.Fib.Pair := by
  classical
  intro H G I _ _ j H₀ U c f δ Hi _ φ hcen hfix hc hf hfin hT hidx hrange hδ hcov
  letI : MulAction H (PairSp H G U) := pairAct j U
  letI : MulAction H (G ⧸ U) := MulAction.compHom (G ⧸ U) j
  letI : ∀ i, MulAction (Hi i) (G ⧸ U) := fun i => MulAction.compHom (G ⧸ U) (j.comp (φ i))
  have hnorm : H₀.Normal := ⟨fun n hn g => by
    have hc' := Subgroup.mem_center_iff.1 (hcen hn) g
    rw [hc', mul_inv_cancel_right]
    exact hn⟩
  have hout : ∀ (a : G) (y : G ⧸ U), ∃ u ∈ U, ((a • y : G ⧸ U).out) = a * y.out * u := by
    intro a y
    have hy : (a • y : G ⧸ U) = ((a * y.out : G) : G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [hy]
    exact out_eq_mul U _
  let K' : PairSp H G U → ℂ := fun p => c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
  have hKinv : ∀ (h : H) (p : PairSp H G U), K' (h • p) = K' p := by
    intro h p
    obtain ⟨u, hu, he⟩ := hout (j h) p.2
    show c (h * p.1 * h⁻¹) * f ((j h • p.2).out⁻¹ * j (h * p.1 * h⁻¹) * (j h • p.2).out) =
      c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
    rw [hc, he, map_mul, map_mul, map_inv]
    congr 1
    rw [show (j h * p.2.out * u)⁻¹ * (j h * j p.1 * (j h)⁻¹) * (j h * p.2.out * u) =
        u⁻¹ * (p.2.out⁻¹ * j p.1 * p.2.out) * u by group]
    exact hf u hu _
  have hfib : ∀ x : G ⧸ U, {p : PairSp H G U | p.2 = x ∧ K' p ≠ 0}.Finite := by
    intro x
    refine ((hfin x.out).image (fun γ => (⟨γ, x⟩ : PairSp H G U))).subset ?_
    rintro ⟨γ, y⟩ ⟨hy, hne⟩
    change y = x at hy
    subst hy
    exact ⟨γ, hne, rfl⟩
  obtain ⟨T, hTc⟩ := hT
  have hT'fin : (⋃ s ∈ T, {p : PairSp H G U | p.2 = (s : G ⧸ U) ∧ K' p ≠ 0}).Finite :=
    Set.Finite.biUnion T.finite_toSet (fun s _ => hfib _)
  have hcoverP : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ h : H, ∃ s ∈ hT'fin.toFinset, p = h • s := by
    intro p hp
    obtain ⟨γ0, s, hs, u, hu, he⟩ := hTc p.2.out
    refine ⟨γ0, γ0⁻¹ • p, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_, ?_⟩
      · show j γ0⁻¹ • p.2 = (s : G ⧸ U)
        conv_lhs => rw [← QuotientGroup.out_eq' p.2, he]
        show ((j γ0⁻¹ * (j γ0 * s * u) : G) : G ⧸ U) = s
        rw [QuotientGroup.eq, map_inv]
        simpa [mul_assoc] using U.inv_mem hu
      · rw [hKinv]
        exact hp
    · rw [smul_smul, mul_inv_cancel, one_smul]
  have hfixP : ∀ z ∈ H₀, ∀ p : PairSp H G U, z • p = p := by
    intro z hz p
    obtain ⟨γ, y⟩ := p
    show (⟨z * γ * z⁻¹, j z • y⟩ : PairSp H G U) = ⟨γ, y⟩
    rw [← Subgroup.mem_center_iff.1 (hcen hz) γ, mul_inv_cancel_right, hfix z hz y]
  have hpush := UpperTheory.orbitalFiber_pushforward H (PairSp H G U) (G ⧸ U) H₀ (fun p => p.2) K' hnorm
    (fun _ _ => rfl) hfixP hKinv ⟨hT'fin.toFinset, hcoverP⟩ hfib (fun p _ => hidx p.2)
  have hfibsum : ∀ x : G ⧸ U, (∑ᶠ (p : PairSp H G U) (_ : p.2 = x), K' p) =
      ∑ᶠ γ : H, c γ * f (x.out⁻¹ * j γ * x.out) := by
    intro x
    have hr : ∀ p : PairSp H G U,
        (p.2 = x) = (p ∈ Set.range (fun γ : H => (⟨γ, x⟩ : PairSp H G U))) := by
      intro p
      apply propext
      constructor
      · intro hp
        exact ⟨p.1, by rw [← hp]⟩
      · rintro ⟨γ, rfl⟩
        rfl
    simp only [hr]
    rw [finsum_mem_range (fun a b hab => congrArg PairSp.fst hab)]
  have hcomm : ∀ i (a : Hi i), φ i a * δ i * (φ i a)⁻¹ = δ i := by
    intro i a
    rw [(hrange i (φ i a)).1 ⟨a, rfl⟩, mul_inv_cancel_right]
  have hequi : ∀ i (a : Hi i) (y : G ⧸ U),
      (⟨δ i, a • y⟩ : PairSp H G U) = φ i a • (⟨δ i, y⟩ : PairSp H G U) := by
    intro i a y
    show (⟨δ i, j (φ i a) • y⟩ : PairSp H G U) = ⟨φ i a * δ i * (φ i a)⁻¹, j (φ i a) • y⟩
    rw [hcomm]
  have hkiinv : ∀ i (a : Hi i) (y : G ⧸ U),
      c (δ i) * f ((a • y).out⁻¹ * j (δ i) * (a • y).out) = c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) := by
    intro i a y
    obtain ⟨u, hu, he⟩ := hout (j (φ i a)) y
    show c (δ i) * f ((j (φ i a) • y).out⁻¹ * j (δ i) * (j (φ i a) • y).out) = _
    rw [he, pair_inv_mul_eq_of_mul_self_eq_one (H := H) _ _ _ _ ?_, hf u hu]
    have h1 := (hrange i (φ i a)).1 ⟨a, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_left]
  have hcovD : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ i, ∃ y : G ⧸ U, ∃ h : H,
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 ∧ p = h • (⟨δ i, y⟩ : PairSp H G U) := by
    rintro ⟨γ, y⟩ hp
    obtain ⟨i, h, hγ⟩ := hcov γ y.out hp
    refine ⟨i, j h⁻¹ • y, h, ?_, ?_⟩
    · have h2 := hKinv h⁻¹ ⟨γ, y⟩
      have h3 : h⁻¹ * γ * h⁻¹⁻¹ = δ i := by rw [hγ]; group
      change c (h⁻¹ * γ * h⁻¹⁻¹) * f ((j h⁻¹ • y).out⁻¹ * j (h⁻¹ * γ * h⁻¹⁻¹) * (j h⁻¹ • y).out) =
        K' ⟨γ, y⟩ at h2
      rw [h3] at h2
      rw [h2]
      exact hp
    · show (⟨γ, y⟩ : PairSp H G U) = ⟨h * δ i * h⁻¹, j h • j h⁻¹ • y⟩
      rw [← hγ, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have huniq : ∀ (i i' : I) (y y' : G ⧸ U) (h : H),
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 → c (δ i') * f (y'.out⁻¹ * j (δ i') * y'.out) ≠ 0 →
      h • (⟨δ i, y⟩ : PairSp H G U) = ⟨δ i', y'⟩ → i = i' ∧ h ∈ (φ i).range := by
    intro i i' y y' h _ _ he
    have h1 : h * δ i * h⁻¹ = δ i' := congrArg PairSp.fst he
    have hii := hδ i i' h h1.symm
    subst hii
    refine ⟨rfl, (hrange i h).2 ?_⟩
    calc h * δ i = h * δ i * h⁻¹ * h := by group
      _ = δ i * h := by rw [h1]
  have hdec := UpperTheory.orbitalFiber_decomposition H (PairSp H G U) I H₀ K' Hi (fun _ => G ⧸ U) φ
    (fun i y => (⟨δ i, y⟩ : PairSp H G U))
    (fun i y => c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)) hnorm hKinv ⟨hT'fin.toFinset, hcoverP⟩
    hequi (fun _ _ _ hab => congrArg PairSp.snd hab) hkiinv (fun _ _ _ => rfl) hcovD huniq
  show gq H₀ (fun y : G ⧸ U => ∑ᶠ γ : H, c γ * f (y.out⁻¹ * j γ * y.out)) = _
  simp only [← hfibsum]
  rw [← hpush, hdec]
  apply finsum_congr
  intro i
  exact (UpperTheory.orbitalFiber_of_bot (Hi i) (G ⧸ U) (Subgroup.comap (φ i) H₀)
    (fun y => f (y.out⁻¹ * j (δ i) * y.out))).1 (c (δ i))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UOperatorPowEventuallyInvariantModPow
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_one {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c d : ℕ) (hcd : c ≤ d) (v : M) (hN : v ∈ fixd π I.N) (hT : v ∈ fixd π (I.Tc c))
    (hm : v ∈ fixd π (I.Nm (d + 1))) :
    I.uOp π I.z v ∈ fixd π I.N ∧ I.uOp π I.z v ∈ fixd π (I.Tc c) ∧ I.uOp π I.z v ∈ fixd π (I.Nm d) := by
  obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π I.z I.z I.z_mem I.z_mem v hN
  refine ⟨h1, fun t ht => by rw [h2 t (I.Tc_le c ht), hT t ht], fun y hy => ?_⟩
  exact (uOpLevel G I A M π d).2.1 v hN (fun t ht => hT t (I.Tc_anti hcd ht)) hm y (Subgroup.mem_sup_right hy)

private theorem lower_many {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c n : ℕ) : ∀ v : M, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) →
      v ∈ fixd π (I.Nm (c + n)) → (I.uOp π I.z ^ n) v ∈ fixd π (I.Nm c) := by
  induction n with
  | zero => exact fun v _ _ hm => by simpa using hm
  | succ n ih =>
    intro v hN hT hm
    obtain ⟨h1, h2, h3⟩ := lower_one I π c (c + n) (Nat.le_add_right c n) v hN hT hm
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ h1 h2 h3

theorem UpperTheory.uOperator_pow_eventually_invariant_mod_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ f ∈ X.Amb m θ, ∀ k c : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ y ∈ X.I.Nm c, X.rp A m y ((X.U A m X.I.z ^ n) f) - (X.U A m X.I.z ^ n) f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m θ _ f hf k c hc
  obtain ⟨-, h2, h3, h4⟩ := hf
  obtain ⟨c1, hc1⟩ := h4 k
  refine ⟨c1, fun n hn y hy => ?_⟩
  let φ : X.Fn A m →ₗ[A] X.Fn (A ⧸ maximalIdeal A ^ k) m := X.mapFn
  have hφ : ∀ f g i, φ f g i = Ideal.Quotient.mk _ (f g i) := fun _ _ _ => rfl
  have hnat : ∀ b f, φ (X.rp A m b f) = X.rp _ m b (φ f) := fun _ _ => rfl
  have hN : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.N := fun x hx => by rw [← hnat, h2 x hx]
  have hT : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Tc c) := fun t ht => by
    have ht' := X.I.Tc_le _ ht
    have := hc ⟨t, ht'⟩⁻¹ (inv_mem ht)
    rw [← hnat, h3 ⟨t, ht'⟩]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    have h6 := Ideal.mul_mem_right (f g i) _ this
    rw [map_inv] at h6
    convert h6 using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hm : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Nm (c + n)) := fun w hw => by
    rw [← hnat]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    exact hc1 w (X.I.Nm_anti (by omega) hw) g i
  have hpow : ∀ j : ℕ, φ ((X.U A m X.I.z ^ j) f) =
      (X.I.uOp (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.z ^ j) (φ f) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp (A ⧸ maximalIdeal A ^ k) m) φ.toAddMonoidHom X.I.z X.I.z_mem _
        (fun _ _ => rfl)
  have h7 := lower_many X.I (X.rp (A ⧸ maximalIdeal A ^ k) m) c n _ hN hT hm y hy
  rw [← hpow, ← hnat] at h7
  simp only [Frame.valIn, Submodule.mem_pi]
  intro g _ i _
  have h9 := congrFun (congrFun h7 g) i
  rw [hφ, hφ, Ideal.Quotient.eq] at h9
  exact h9
end

