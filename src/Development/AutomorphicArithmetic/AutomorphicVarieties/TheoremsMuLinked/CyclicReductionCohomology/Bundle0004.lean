module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.CountFix
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Count

variable {R : Type} [CommRing R] {n : ℕ}

private abbrev UU (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

private theorem card_UU : Nat.card (UU n) = n.choose 2 := by
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  rw [Finset.card_univ, Fintype.card_fin, Finset.univ_product_univ] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← h]

private def upM (f : UU n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else 0

private theorem upM_inj (u : R) : Function.Injective fun f : UU n → R => upM f - u • (upM f)ᵀ := by
  intro f f' e
  funext ⟨⟨i, j⟩, h⟩
  have h : i < j := h
  have h' : ¬ j < i := not_lt.2 h.le
  have := congrFun (congrFun e i) j
  simpa [upM, h, h'] using this

private theorem count_fix [Finite R] {A B : Matrix (Fin n) (Fin n) R} (h1 : A * B = 1)
    (T : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R) (hT : ∀ Z, T Z = -(A * Zᵀ * B))
    (hTT : ∀ Z, T (T Z) = Z) : Nat.card R ^ n.choose 2 ≤ Nat.card {Z // T Z = Z} := by
  have h2 : B * A = 1 := mul_eq_one_comm.1 h1
  have k : ∀ Z, A * Bᵀ * Z * (Aᵀ * B) = Z := fun Z => by
    have := hTT Z
    rw [hT, hT] at this
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have k1 : A * Bᵀ * (Aᵀ * B) = 1 := by simpa using k 1
  have k2 : Aᵀ * B * (A * Bᵀ) = 1 := mul_eq_one_comm.1 k1
  have k3 : ∀ Z, Z * (Aᵀ * B) = Aᵀ * B * Z := fun Z => by
    conv_rhs => rw [← k Z]
    rw [← Matrix.mul_assoc (Aᵀ * B), ← Matrix.mul_assoc (Aᵀ * B), k2, Matrix.one_mul]
  obtain ⟨u, hu⟩ : Aᵀ * B ∈ Set.range (Matrix.scalar (Fin n)) := by
    rw [← Matrix.center_eq_range]
    exact Semigroup.mem_center_iff.2 k3
  have hu' : Aᵀ * B = u • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← hu, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have a1 : Aᵀ = u • A := by
    calc Aᵀ = Aᵀ * B * A := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = u • A := by rw [hu', Matrix.smul_mul, Matrix.one_mul]
  have a2 : u • u • A = A := by
    have := congrArg Matrix.transpose a1
    rw [Matrix.transpose_transpose, Matrix.transpose_smul, a1] at this
    exact this.symm
  have a3 : ∀ X : Matrix (Fin n) (Fin n) R, u • u • X = X := fun X => by
    calc u • u • X = (u • u • A) * (B * X) := by
          rw [Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = X := by rw [a2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  let F : (UU n → R) → {Z // T Z = Z} := fun f =>
    ⟨A * (upM f - u • (upM f)ᵀ), by
      rw [hT, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hu', Matrix.mul_smul, Matrix.mul_one,
        ← Matrix.mul_neg, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_transpose, smul_sub, a3,
        neg_sub]⟩
  have hF : Function.Injective F := by
    intro f f' e
    have e' : A * (upM f - u • (upM f)ᵀ) = A * (upM f' - u • (upM f')ᵀ) := congrArg Subtype.val e
    have e'' := congrArg (B * ·) e'
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul] at e''
    exact upM_inj u e''
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fun, card_UU] at this

end Count

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (X Y : Matrix (Fin n) (Fin n) O) :
    red m X * red m Y = red m (X * Y) := (Matrix.map_mul (f := Ideal.Quotient.mk (maximalIdeal O ^ m))).symm

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

private theorem red_inv {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (X : GL (Fin n) O) :
    red m (X : Matrix (Fin n) (Fin n) O) * red m ((X⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
  rw [red_mul, Units.mul_inv, red_one]

theorem UpperTheory.V.Th.pow_choose_two_le_card_fixed_ad0_of_odd_involution :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)) (c' : G.Γ), l ≠ 2 → IsAd0 h y m rep → c' * c' = 1 → G.η c' = -1 → Nat.card (ResidueField O) ^ (m * n.choose 2) ≤ Nat.card {Z : Mm O n m // rep c' Z = Z} := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep c' _ hA hc hη
  obtain ⟨f1, f2, -⟩ := (UpperTheory.V.Th.omFacts l O).2 m
  haveI := f1
  let g : G.G₀ := ⟨c' * G.c⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_inv, hη, G.η_c, mul_inv_cancel]⟩
  have hg : c' = (g : G.Γ) * G.c := by simp [g]
  have p1 := red_inv m y.P
  have p2 := mul_eq_one_comm.1 p1
  have r1 : y.ρm h m g * y.ρm h m g⁻¹ = 1 := by
    have := red_inv m (y.ρ (h.p₀ g))
    rw [← map_inv, ← map_inv] at this
    exact this
  rw [pow_mul, ← f2]
  refine count_fix (A := y.ρm h m g * red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O))
    (B := red m y.P * y.ρm h m g⁻¹) ?_ (rep c') (fun Z => ?_) fun Z => ?_
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (y.ρm h m g⁻¹), p2, Matrix.one_mul, r1]
  · have a1 := hA.1 g (rep G.c Z)
    have a2 := hA.2 Z
    rw [one_smul] at a1 a2
    have a3 : rep G.c Z = -(red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (Zᵀ * red m y.P)) := by
      rw [← Matrix.mul_neg, ← a2, ← Matrix.mul_assoc, p2, Matrix.one_mul]
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    refine a1.trans ?_
    rw [a3]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · rw [← Module.End.mul_apply, ← map_mul, hc, map_one, Module.End.one_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PairOLin
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem pairO_lin (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R) (k : ℕ)
    (hk : ∀ x : R, l ^ k • x = 0) (τ : R →+ ZMod (l ^ k)) (a : ℤ_[l]) (x : R) :
    τ (φ a * x) = PadicInt.toZModPow k a * τ x := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set n : ℕ := (PadicInt.toZModPow k a).val with hn
  have h1 : a - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨b, hb⟩ := h1
  have h2 : a = (n : ℤ_[l]) + (l : ℤ_[l]) ^ k * b := by rw [← hb]; ring
  have h3 : φ a * x = n • x := by
    have := hk (φ b * x)
    rw [nsmul_eq_mul, Nat.cast_pow] at this
    rw [h2, map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_mul, mul_assoc, this, add_zero, nsmul_eq_mul]
  rw [h3, map_nsmul, nsmul_eq_mul, hn, ZMod.natCast_zmod_val]

private theorem pairO_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : Irreducible t)
    (m : ℕ) (x : Om O (m + 1)) (hx : x ≠ 0) : ∃ z, x * z = Ideal.Quotient.mk _ (t ^ m) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy ht
  have hn : n ≤ m := by
    by_contra h
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_left (pow_dvd_pow t (by omega)) _
  refine ⟨Ideal.Quotient.mk _ ((u⁻¹ : Oˣ) * t ^ (m - n)), ?_⟩
  rw [← map_mul]
  congr 1
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add]
  congr 1
  omega

theorem UpperTheory.V.Th.pairO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (m : ℕ), ∃ (k : ℕ) (τ : Om O m →+ ZMod (l ^ k)), 0 < k ∧ (∀ x, (∀ z, τ (x * z) = 0) → x = 0) ∧ ∀ (a : ℤ_[l]) x, τ (algebraMap O (Om O m) (algebraMap ℤ_[l] O a) * x) = PadicInt.toZModPow k a * τ x := by
  intro l _ O _ _ _ _ _ m
  obtain ⟨hfin, -, hkill, -⟩ := (UpperTheory.V.Th.omFacts l O).2 m
  have hk : ∀ x : Om O m, l ^ (m + 1) • x = 0 := fun x => by
    rw [pow_succ, mul_smul, hkill]
  have main : ∃ τ : Om O m →+ ZMod (l ^ (m + 1)), ∀ x, (∀ z, τ (x * z) = 0) → x = 0 := by
    cases m with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      simpa using hkill x
    | succ m =>
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible O
      haveI : NeZero (l ^ (m + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      letI : Module (ZMod (l ^ (m + 1 + 1))) (Om O (m + 1)) := AddCommGroup.zmodModule hk
      have h0 : (Ideal.Quotient.mk _ (t ^ m) : Om O (m + 1)) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          pow_dvd_pow_iff ht.ne_zero ht.not_isUnit]
        omega
      have h1 := (UpperTheory.V.Th.dualZ (l ^ (m + 1 + 1)) (Om O (m + 1))).2.1 (Ideal.Quotient.mk _ (t ^ m))
      obtain ⟨f, hf⟩ := not_forall.mp (mt h1 h0)
      refine ⟨f.toAddMonoidHom, fun x hx => ?_⟩
      by_contra hx0
      obtain ⟨z, hz⟩ := pairO_dvd O t ht m x hx0
      have := hx z
      rw [hz] at this
      exact hf this
  obtain ⟨τ, hτ⟩ := main
  exact ⟨m + 1, τ, Nat.succ_pos m, hτ, fun a x =>
    pairO_lin l (Om O m) ((algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)) (m + 1) hk τ a x⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PlKill
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have := hz 1 1
  rw [mul_one, inv_one, h1, c1, one_mul, mul_one, one_smul] at this
  exact left_eq_add.1 this

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, tw_inv ρ h1 hm hg, hg, hc, one_mul, mul_one, one_smul]

include h1 hm c1 hz in
private theorem tw_pow {g : K} (hg : ρ g = 1) (hc : χ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact ⟨h1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
  | succ k ih =>
    rw [pow_succ', hm, tw_add ρ z χ h1 hm hz hg hc, hg, ih.1, ih.2, one_mul, succ_nsmul']
    exact ⟨rfl, rfl⟩

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ χ g = 1 ∧ z g = 0}
      one_mem' := ⟨h1, c1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [hm, ha.1, hb.1, one_mul], by rw [cm, ha.2.1, hb.2.1, one_mul],
        by rw [tw_add ρ z χ h1 hm hz ha.1 ha.2.1, ha.2.2, hb.2.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨tw_inv ρ h1 hm ha.1, tw_inv χ c1 cm ha.2.1, by
        have := tw_add ρ z χ h1 hm hz ha.1 ha.2.1 a⁻¹
        rw [mul_inv_cancel, twisted_cocycle_apply_one ρ z χ h1 c1 hz, ha.2.2, zero_add] at this
        exact this.symm⟩ }
  have hN : S.Normal := ⟨fun u hu g => ⟨by
      rw [hm, hm, hu.1, mul_one, ← hm, mul_inv_cancel, h1], by
      rw [cm, cm, hu.2.1, mul_one, ← cm, mul_inv_cancel, c1], by
      rw [mul_assoc, hz, tw_add ρ z χ h1 hm hz hu.1 hu.2.1, hu.2.2, zero_add, ← hz, mul_inv_cancel,
        twisted_cocycle_apply_one ρ z χ h1 c1 hz]⟩⟩
  have hO : IsOpen (S : Set K) := (cρ {1}).inter ((cχ {1}).inter (cz {0}))
  exact ⟨⟨⟨S, hO⟩, hN⟩, fun g => Iff.rfl⟩

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem pow_mem_of_PL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (V : Set Γ) (hV : IsOpen V) (hle : (PL l H : Set Γ) ⊆ V) : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ V := by
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U}
  haveI : Nonempty ι := ⟨⟨⟨⊤, Subgroup.normal_top⟩, fun h _ => ⟨0, trivial⟩⟩⟩
  have hd : Directed (· ⊇ ·) fun U : ι => (U.1 : Set Γ) := by
    intro U U'
    refine ⟨⟨U.1 ⊓ U'.1, fun h hh => ?_⟩, fun a ha => ha.1, fun a ha => ha.2⟩
    obtain ⟨e, he⟩ := U.2 h hh
    obtain ⟨e', he'⟩ := U'.2 h hh
    refine ⟨e + e', ?_, ?_⟩
    · rw [pow_add, pow_mul]
      exact U.1.toSubgroup.pow_mem he _
    · rw [pow_add, mul_comm, pow_mul]
      exact U'.1.toSubgroup.pow_mem he' _
  have hs : Vᶜ ∩ ⋂ U : ι, (U.1 : Set Γ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ha => ha.1 (hle ?_)
    have := Set.mem_iInter.1 ha.2
    simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf]
    exact fun U hU => this ⟨U, hU⟩
  obtain ⟨U, hU⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed (fun U : ι => (U.1 : Set Γ))
    (fun U => U.1.toOpenSubgroup.isClosed) (Set.disjoint_iff_inter_eq_empty.mpr hs) hd
  intro h hh
  obtain ⟨e, he⟩ := U.2 h hh
  refine ⟨e, ?_⟩
  by_contra hn
  exact Set.disjoint_left.1 hU hn he

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y0
  have hp : (0 : ℝ) < (l : ℝ) ^ (-m : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds y0 hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← sub_eq_zero, ← map_sub, hc, map_mul, map_pow, map_natCast, hl, zero_mul]

private theorem pow_one_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) (a : ℤ_[l]) (ha : PadicInt.toZMod a = 1) : f (a ^ l ^ m) = 1 := by
  have : a - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, ha, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub this m
  rw [one_pow] at hc
  rw [eq_add_of_sub_eq hc, map_add (f := _), map_mul, map_pow, map_natCast, pow_succ, hl]
  simp

private theorem rho_pow (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ)
    (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1)
    (hc : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g)) (g : G0.G₀)
    (hg : (g : G0.Γ) ∈ T.H) : ∃ e : ℕ, red m (mat y.ρ (g ^ l ^ e)) = 1 := by
  obtain ⟨e, g', h1, h2⟩ := pow_mem_of_PL l T.H.toSubgroup _
    (G0.η_open.isOpenMap_subtype_val _ (hc.isOpen_fiber 1)) (fun a ha => by
    have hη : a ∈ G0.η.ker := by
      have ha' := ha
      simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf] at ha'
      exact ha' ⟨⟨G0.η.ker, G0.η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
        ⟨0, by rw [pow_zero, pow_one]; exact T.H_η h hh⟩
    refine ⟨⟨a, hη⟩, ?_, rfl⟩
    show red m (mat y.ρ _) = 1
    simp [red, mat, hPL ⟨a, hη⟩ ha]) g hg
  have h3 : g' = g ^ l ^ e := Subtype.ext h2
  subst h3
  exact ⟨e, h1⟩

theorem UpperTheory.V.Th.plKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (G : Glob l L) (h : G.Hom G0), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ z : G.G₀ → Mm O n m, IsLocallyConstant z → (∀ g g', z (g * g') = z g + epsm O G m g • (y.ρm h m g * z g' * y.ρm h m g⁻¹)) → ∀ g : G.G₀, (g : G.Γ) ∈ PL l (T.H.toSubgroup.comap h.p) → z g = 0 ∧ y.ρm h m g = 1 ∧ epsm O G m g = 1 := by
  intro l _ L G0 T O _ _ _ _ _ n y m G h hPL z cz hz g hg
  obtain ⟨-, -, hk, -⟩ := (omFacts l O).2 m
  have hl : (l : Om O m) ^ m = 0 := by
    have := hk 1
    rwa [nsmul_eq_mul, mul_one, Nat.cast_pow] at this
  have hp : Continuous fun g : G.G₀ => h.p₀ g :=
    Continuous.subtype_mk (h.cont.comp continuous_subtype_val) _
  have h0 : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g) := tw_lc _ fun i j => y.cont i j m
  have c1 : IsLocallyConstant fun g : G.G₀ => y.ρm h m g := h0.comp_continuous hp
  let f : ℤ_[l] →+* Om O m := (algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)
  have c2 : IsLocallyConstant fun g : G.G₀ => epsm O G m g :=
    (lc_padic f m hl).comp_continuous (Units.continuous_val.comp (G.ε_cont.comp continuous_subtype_val))
  have r1 : y.ρm h m 1 = 1 := by simp [Pt.ρm, red, mat]
  have r2 : ∀ a b, y.ρm h m (a * b) = y.ρm h m a * y.ρm h m b := fun a b => by
    simp [Pt.ρm, red, mat, Matrix.map_mul]
  have e1 : epsm O G m ((1 : G.G₀) : G.Γ) = 1 := by simp [epsm]
  have em : ∀ a b : G.G₀, epsm O G m ((a * b : G.G₀) : G.Γ) = epsm O G m a * epsm O G m b := by
    intro a b
    simp [epsm]
  obtain ⟨U, hU⟩ := tw_U (K := G.G₀) (fun g => y.ρm h m g) z (fun g => epsm O G m g) r1 r2 e1 em hz c1 c2 cz
  haveI := T.H.isNormal'
  have hsub := pl_sub l G.Γ (T.H.toSubgroup.comap h.p) G.η.ker G.η_open
    (fun a ha => by rw [MonoidHom.mem_ker, ← h.η]; exact T.H_η _ ha) U fun a ha => by
    obtain ⟨e, he⟩ := rho_pow l L G0 T O n y m hPL h0 (h.p₀ a) ha
    have he' : y.ρm h m (a ^ l ^ e) = 1 := by rw [Pt.ρm, map_pow]; exact he
    have hε : ∀ b : G.G₀, h.p b ∈ T.H → epsm O G m ((b ^ l ^ m : G.G₀) : G.Γ) = 1 := fun b hb => by
      have := pow_one_padic f m hl _ (T.H_ε _ hb)
      rw [h.ε] at this
      rw [← this]
      simp [epsm, f]
    have hρp : ∀ (b : G.G₀) (k : ℕ), y.ρm h m b = 1 → y.ρm h m (b ^ k) = 1 := fun b k hb => by
      induction k with
      | zero => rw [pow_zero]; exact r1
      | succ k ih => rw [pow_succ, r2, ih, hb, one_mul]
    have hH : ∀ k : ℕ, h.p ((a ^ k : G.G₀) : G.Γ) ∈ T.H := fun k => (T.H.toSubgroup.comap h.p).pow_mem ha k
    have := tw_pow (K := G.G₀) (fun g => y.ρm h m g) z (fun g => epsm O G m g) r1 r2 e1 hz
      (hρp _ (l ^ m) he') (hε _ (hH _)) (l ^ m)
    refine ⟨e + m + m, (hU _).2 ⟨?_, ?_, ?_⟩⟩
    · rw [pow_add, pow_add, pow_mul, pow_mul]
      exact this.1
    · rw [pow_add, pow_mul]
      exact hε _ (hH _)
    · rw [pow_add, pow_add, pow_mul, pow_mul]
      exact this.2.trans (Matrix.ext fun i j => hk _)
  obtain ⟨u1, u2, u3⟩ := (hU g).1 (hsub g hg)
  exact ⟨u3, u1, u2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedSmul
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B := by
  ext i j
  simp [red]

private theorem red_smul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (a : O) (A : Matrix (Fin n) (Fin n) O) :
    red m (a • A) = algebraMap O (Om O m) a • red m A := by
  ext i j
  simp [red]

theorem UpperTheory.V.Th.h0v0O :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (D : Subgroup G0.G₀), y.N4 D → ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∀ g ∈ D, epsm O G0 m (g : G0.G₀) • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) = Y}.ncard ≤ Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ _ _ n y D hN
  let M : G0.G₀ → Matrix (Fin n) (Fin n) O := fun g => mat y.ρ g
  let e : G0.G₀ → O := fun g => algebraMap ℤ_[l] O (G0.ε (g : G0.Γ))
  let Φ : D → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O := fun s =>
    e s • LinearMap.mulLeft O (M s) - LinearMap.mulRight O (M s)
  have hΦ : ∀ s Z, Φ s Z = e s • (M s * Z) - Z * M s := fun s Z => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n D Φ
  have hker : (⨅ s, (Φ s).ker) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_iInf] at hZ
    rw [Submodule.mem_bot]
    apply hN Z
    intro g hg
    have h1 := hZ ⟨g, hg⟩
    rw [LinearMap.mem_ker, hΦ, sub_eq_zero] at h1
    exact h1
  have hfin : Module.finrank O ↥(⨅ s, (Φ s).ker) = 0 := by
    rw [hker]
    exact finrank_bot O _
  refine ⟨C, fun m => ?_⟩
  have hone : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    unfold red
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : ∀ g : G0.G₀, y.ρ0 m g * y.ρ0 m g⁻¹ = 1 ∧ y.ρ0 m g⁻¹ * y.ρ0 m g = 1 := by
    intro g
    simp only [Pt.ρ0, ← red_mul', ← map_mul, mul_inv_cancel, inv_mul_cancel, map_one, hone, and_self]
  have hred : ∀ (g : G0.G₀) (Z : Matrix (Fin n) (Fin n) O),
      red m (e g • (M g * Z) - Z * M g) = epsm O G0 m g • (y.ρ0 m g * red m Z) - red m Z * y.ρ0 m g := by
    intro g Z
    rw [red_sub', red_smul', red_mul', red_mul']
    rfl
  have hset : {Y : Mm O n m | ∀ g ∈ D, epsm O G0 m (g : G0.G₀) • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) = Y} =
      {Y : Mm O n m | ∃ Y' : Matrix (Fin n) (Fin n) O, red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0} := by
    ext Y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨Y.map (Function.surjInv Ideal.Quotient.mk_surjective), ?_, fun s => ?_⟩
      · ext i j
        simp [red, Function.surjInv_eq]
      · have hY : red m (Y.map (Function.surjInv Ideal.Quotient.mk_surjective)) = Y := by
          ext i j
          simp [red, Function.surjInv_eq]
        rw [hΦ, hred, hY, sub_eq_zero]
        have h1 := h s s.2
        calc epsm O G0 m (s : G0.G₀) • (y.ρ0 m s * Y)
            = (epsm O G0 m (s : G0.G₀) • (y.ρ0 m s * Y * y.ρ0 m (s : G0.G₀)⁻¹)) * y.ρ0 m s := by
              rw [Matrix.smul_mul, mul_assoc (y.ρ0 m s * Y), (hinv s).2, mul_one]
          _ = Y * y.ρ0 m s := by rw [h1]
    · rintro ⟨Y', rfl, h⟩ g hg
      have h1 := h ⟨g, hg⟩
      rw [hΦ, hred, sub_eq_zero] at h1
      calc epsm O G0 m g • (y.ρ0 m g * red m Y' * y.ρ0 m g⁻¹)
          = (epsm O G0 m g • (y.ρ0 m g * red m Y')) * y.ρ0 m g⁻¹ := by rw [Matrix.smul_mul]
        _ = red m Y' * y.ρ0 m g * y.ρ0 m g⁻¹ := by rw [h1]
        _ = red m Y' := by rw [mul_assoc, (hinv g).1, mul_one]
  rw [hset]
  have h2 := hC m
  rw [hfin, mul_zero, zero_add] at h2
  exact h2
end

