module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocC
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem graph_ext {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [T2Space Y]
    (I : Subgroup G) (σ : G) (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, 0 < n → ∃ U : Subgroup G, U.Normal ∧ IsOpen (U : Set G) ∧ I ≤ U ∧
      ∀ k : ℤ, σ ^ k ∈ U → (n : ℤ) ∣ k) (y : Y) :
    ∃ f : G →* Y, Continuous f ∧ (∀ g ∈ I, f g = 1) ∧ f σ = y := by
  set Δ : Subgroup (G × Y) := I.prod ⊥ ⊔ Subgroup.zpowers (σ, y) with hΔ
  set Γ : Subgroup (G × Y) := Δ.topologicalClosure with hΓ
  have hΓc : IsClosed (Γ : Set (G × Y)) := Δ.isClosed_topologicalClosure
  have hIΓ : ∀ g ∈ I, (g, (1 : Y)) ∈ Γ := fun g hg =>
    Δ.le_topologicalClosure ((le_sup_left : I.prod ⊥ ≤ Δ) ⟨hg, rfl⟩)
  have hσΓ : (σ, y) ∈ Γ :=
    Δ.le_topologicalClosure ((le_sup_right : Subgroup.zpowers (σ, y) ≤ Δ) (Subgroup.mem_zpowers _))
  have hsurj : Γ.map (MonoidHom.fst G Y) = ⊤ := by
    rw [eq_top_iff, ← hd]
    refine Subgroup.topologicalClosure_minimal _ (sup_le (fun g hg => ⟨_, hIΓ g hg, rfl⟩) ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨_, hσΓ, rfl⟩
    · exact isClosedMap_fst_of_compactSpace _ hΓc
  have hker : ∀ z : Y, ((1 : G), z) ∈ Γ → z = 1 := by
    intro z hz
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := Y) (U := {z}ᶜ)
      isOpen_compl_singleton (fun h => hne (Set.mem_singleton_iff.1 h).symm)
    haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨U, hUn, hUo, hIU, hUk⟩ := hU N.toSubgroup.index (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
    have hle : Γ ≤ U.prod N.toSubgroup ⊔ Subgroup.zpowers (σ, y) := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le_sup_right (Subgroup.prod_mono hIU bot_le) _) ?_
      refine Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_left ?_)
      exact hUo.prod N.isOpen
    have h1 := hle hz
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h1
    obtain ⟨⟨u, w⟩, ⟨hu, hw⟩, _, ⟨k, rfl⟩, h⟩ := h1
    have e1 : u * σ ^ k = 1 := congrArg Prod.fst h
    have e2 : w * y ^ k = z := congrArg Prod.snd h
    have h2 : σ ^ k ∈ U := by
      rw [← (inv_eq_of_mul_eq_one_right e1)]
      exact U.inv_mem hu
    obtain ⟨c, rfl⟩ := hUk k h2
    have h3 : z ∈ N.toSubgroup := by
      rw [← e2, zpow_mul, zpow_natCast]
      exact N.toSubgroup.mul_mem hw (N.toSubgroup.zpow_mem (N.toSubgroup.pow_index_mem y) c)
    exact hN h3 rfl
  obtain ⟨f, hf⟩ := Subgroup.exists_eq_graph (G := Γ) (by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
      obtain rfl : a = a' := h
      have := hker (b⁻¹ * b') (by simpa using Γ.mul_mem (Γ.inv_mem hab) hab')
      obtain rfl : b = b' := inv_mul_eq_one.1 this
      rfl
    · intro g
      obtain ⟨p, hp, rfl⟩ : g ∈ Γ.map (MonoidHom.fst G Y) := by rw [hsurj]; trivial
      exact ⟨⟨p, hp⟩, rfl⟩)
  have hmem : ∀ a b, (a, b) ∈ Γ ↔ f a = b := fun a b => by rw [hf]; rfl
  refine ⟨f, continuous_iff_isClosed.2 fun C hC => ?_, fun g hg => (hmem _ _).1 (hIΓ g hg), (hmem _ _).1 hσΓ⟩
  have : f ⁻¹' C = Prod.fst '' ((Γ : Set (G × Y)) ∩ Prod.snd ⁻¹' C) := by
    ext g
    constructor
    · intro hg
      exact ⟨(g, f g), ⟨(hmem _ _).2 rfl, hg⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨h1, h2⟩, rfl⟩
      show f a ∈ C
      rw [(hmem _ _).1 h1]
      exact h2
  rw [this]
  exact isClosedMap_fst_of_compactSpace _ (hΓc.inter (hC.preimage continuous_snd))

private theorem root_eq_one {v : ℕ} [Fact v.Prime] {m : ℕ} (hm : ¬ v ∣ m) {η : Om v} (hη : η ^ m = 1)
    (h : ‖η - 1‖ < 1) : η = 1 :=
  _root_.UpperTheory.Reformulated.B.Qe14.root_eq_one hm hη h

private theorem exists_level {v : ℕ} [Fact v.Prime] (σ : GQ v)
    (hσ : UpperTheory.V.Loc.IsFrob (v := v) σ) (n : ℕ) (hn : 0 < n) :
    ∃ U : Subgroup (GQ v), U.Normal ∧ IsOpen (U : Set (GQ v)) ∧ Iq v ≤ U ∧ ∀ k : ℤ, σ ^ k ∈ U → (n : ℤ) ∣ k := by
  have hv : v.Prime := Fact.out
  have h1 : 1 < v ^ n := Nat.one_lt_pow hn.ne' hv.one_lt
  obtain ⟨m, hm⟩ : ∃ m, m = v ^ n - 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hvm : ¬ v ∣ m := by
    intro h
    have h2 : v ∣ v ^ n := dvd_pow_self v hn.ne'
    have e : v ^ n = m + 1 := by omega
    rw [e] at h2
    exact hv.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m : Om v) := ⟨by exact_mod_cast hm0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) m
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0.ne'
  have hnorm : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 this
  have hg : ∀ g : GQ v, (g ζ) ^ m = 1 := fun g => by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hσζ : σ ζ = ζ ^ v := by
    have hz : ζ ^ v ≠ 0 := pow_ne_zero _ hζ0
    rw [← div_eq_one_iff_eq hz]
    refine root_eq_one hvm ?_ ?_
    · rw [div_pow, hg, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, div_one]
    · rw [div_sub_one hz, norm_div, norm_pow, hnorm, one_pow, div_one]
      exact hσ ζ hnorm.le
  have hpow : ∀ k : ℕ, (σ ^ k) ζ = ζ ^ v ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσζ, ← pow_mul, ← pow_succ']
  refine ⟨MulAction.stabilizer (GQ v) ζ, ⟨fun g hgζ h => ?_⟩, stabilizer_isOpen_of_isIntegral ζ, fun g hgI => ?_,
    fun k hk => ?_⟩
  · have hgζ' : g ζ = ζ := hgζ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hg h⁻¹)
    show h (g (h⁻¹ ζ)) = ζ
    rw [← hi, map_pow, hgζ', hi, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  · exact hgI ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm0, hvm, hζ.pow_eq_one⟩⟩
  · have hk' : σ ^ k.natAbs ∈ MulAction.stabilizer (GQ v) ζ := by
      rcases Int.natAbs_eq k with e | e
      · rwa [e, zpow_natCast] at hk
      · rwa [e, zpow_neg, zpow_natCast, inv_mem_iff] at hk
    have h2 : (σ ^ k.natAbs) ζ = ζ := hk'
    rw [hpow] at h2
    rw [Int.natCast_dvd]
    generalize k.natAbs = j at h2
    have hj : 0 < v ^ j := pow_pos hv.pos j
    have h3 : ζ ^ (v ^ j - 1) = 1 := by
      apply mul_right_cancel₀ hζ0
      rw [← pow_succ, Nat.sub_add_cancel hj, h2, one_mul]
    have h4 : v ^ n - 1 ∣ v ^ j - 1 := hm ▸ (hζ.pow_eq_one_iff_dvd _).1 h3
    have h5 := Nat.pow_sub_one_gcd_pow_sub_one v n j
    rw [Nat.gcd_eq_left h4] at h5
    have h6 : 0 < v ^ n.gcd j := pow_pos hv.pos _
    have h7 : v ^ n = v ^ n.gcd j := by omega
    exact Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective hv.two_le h7).symm

theorem UpperTheory.V.Loc.frobFree :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), UpperTheory.V.Loc.IsFrob (v := v) σ →
      ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [T2Space Y] (y : Y), ∃ f : GQ v →* Y, Continuous f ∧ (∀ g ∈ Iq v, f g = 1) ∧ f σ = y := by
  intro v _ σ hσ Y _ _ _ _ _ _ y
  have hd : (Iq v ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ := by
    have hv : v.Prime := Fact.out
    have level : ∀ {x : Om v}, x ∈ MaximalUnramifiedExtension v →
        ∃ m : ℕ, ¬ v ∣ m ∧
          ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) → g x = h x := by
      intro x hx
      have combine : ∀ {a b : Om v},
          (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) → g a = h a) →
          (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) → g b = h b) →
          ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) →
            g a = h a ∧ g b = h b := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h ?_, hb g h ?_⟩⟩
        · exact fun z hz => hgh z (by rw [pow_mul, hz, one_pow])
        · exact fun z hz => hgh z (by rw [mul_comm, pow_mul, hz, one_pow])
      unfold MaximalUnramifiedExtension at hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
        obtain ⟨m, -, hm, hxm⟩ := hx
        exact ⟨m, hm, fun g h hgh => hgh x hxm⟩
      | algebraMap x =>
        exact ⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, hm, h⟩ := combine hx hy
        exact ⟨m, hm, fun g k hgk => by rw [map_add, map_add, (h g k hgk).1, (h g k hgk).2]⟩
      | inv x _ hx =>
        obtain ⟨m, hm, h⟩ := hx
        exact ⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨m, hm, h⟩ := combine hx hy
        exact ⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩
    let H : ClosedSubgroup (GQ v) :=
      ⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have hH := InfiniteGalois.fixingSubgroup_fixedField H
    have hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v)) := Subgroup.le_topologicalClosure _
    refine eq_top_iff.mpr fun g _ => ?_
    change g ∈ (H : Subgroup (GQ v))
    rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxK : x ∈ MaximalUnramifiedExtension v := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v),
        IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (hle (Subgroup.mem_sup_left hf))
    obtain ⟨m, hm, h⟩ := level hxK
    obtain ⟨j, hj⟩ := KStar.IdealValuations.exists_pow_of_aut g hm
    have frob_pow (z : Om v) (hz : z ^ m = 1) (k : ℕ) : (σ ^ k) z = z ^ v ^ k := by
      have hm0 : m ≠ 0 := fun e => hm (e ▸ dvd_zero v)
      have hnorm : ‖z‖ = 1 := by
        apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp
        rw [← norm_pow, hz, norm_one]
      have hσz : σ z = z ^ v := by
        refine KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm ?_ ?_ (hσ z hnorm.le)
        · rw [← map_pow, hz, map_one]
        · rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσz, ← pow_mul, ← pow_succ']
    rw [h g (σ ^ j) fun z hz => (hj z hz).trans (frob_pow z hz j).symm]
    exact hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))
  exact graph_ext (Iq v) σ hd (exists_level σ hσ) y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v)

omit [CharZero Ω] in
private theorem iof_mem (x : Ω) : x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := Examples₂.LB.mem_placeJ j x

omit [CharZero Ω] in
private theorem iof_lt (x : Ω) : (placeJ j).valuation x < 1 ↔ ‖j x‖ < 1 :=
  Examples₂.LB.val_lt_one_iff (iof_mem j) x

omit [CharZero Ω] in
private theorem iof_le (x : Ω) : (placeJ j).valuation x ≤ 1 ↔ ‖j x‖ ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, iof_mem]

private theorem iof_add {x y : Om v} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Qk7.iof_add hx hy

private theorem iof_pow {x y : Om v} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [e]
    refine iof_add ?_ ?_
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt ih
    · rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)).trans_lt h

variable [IsAlgClosure ℚ Ω]

private theorem iof_dense : DenseRange j :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  Examples₂.LB.denseRange_emb v j

private theorem iof_pw (σ : GQ v) (n : ℕ) :
    (∀ x : Om v, ‖x‖ ≤ 1 → ‖σ x - x ^ n‖ < 1) ↔
      ∀ y : Ω, (placeJ j).valuation y ≤ 1 → (placeJ j).valuation (iota j σ y - y ^ n) < 1 := by
  simp only [iof_le, iof_lt, map_sub, map_pow, iota_spec]
  refine ⟨fun h y hy => h _ hy, fun h x hx => ?_⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (iof_dense j) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy' : ‖j y - x‖ < 1 := by rwa [norm_sub_rev]
  have hy1 : ‖j y‖ ≤ 1 := by
    have e : j y = (j y - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy'.le hx)
  have e : σ x - x ^ n = σ (x - j y) + ((σ (j y) - j y ^ n) + (j y ^ n - x ^ n)) := by
    rw [map_sub]; ring
  rw [e]
  exact iof_add (by rwa [Examples₂.LB.norm_aut]) (iof_add (h y hy1) (iof_pow hy1 hx hy' n))

private theorem iof_dec (σ : GQ v) : iota j σ ∈ Dec (F := ℚ) (placeJ j) := by
  rw [mem_Dec]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← map_inv, iof_mem, iof_mem,
    iota_spec, Examples₂.LB.norm_aut]

private theorem iof_range : (iota j).range = Dec (F := ℚ) (placeJ j) := by
  ext g
  constructor
  · rintro ⟨σ, rfl⟩
    exact iof_dec j σ
  · intro hg
    obtain ⟨σ, hσ⟩ := Examples₂.LB.exists_ext (E := ℚ) (iof_mem j) g hg
    exact ⟨σ, AlgEquiv.ext fun x => j.injective (by rw [iota_spec, hσ])⟩

private theorem iof_inj : Function.Injective (iota j) := by
  intro σ τ h
  refine AlgEquiv.ext fun y => ?_
  have e : σ ∘ j = τ ∘ j := funext fun x => by
    show σ (j x) = τ (j x)
    rw [← iota_spec, ← iota_spec, h]
  exact congrFun ((iof_dense j).equalizer (Examples₂.LB.continuous_aut _) (Examples₂.LB.continuous_aut _) e) y

private theorem iof_cont : Continuous (iota j) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨M, hM, hMU⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω U).mp hU
  let b := Module.finBasis ℚ M
  let N : IntermediateField ℚ_[v] (Om v) :=
    IntermediateField.adjoin ℚ_[v] (Set.range fun i => j (b i : Ω))
  have hN : FiniteDimensional ℚ_[v] N :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((IntermediateField.fixingSubgroup_isOpen N).mem_nhds
    (show (1 : GQ v) ∈ N.fixingSubgroup from one_mem _)) fun σ hσ => hMU ?_
  have hb : ∀ i, iota j σ (b i : Ω) = (b i : Ω) := fun i => j.injective (by
    rw [iota_spec]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩))
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have e : (iota j σ).toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap := b.ext hb
  exact LinearMap.congr_fun e ⟨x, hx⟩

private theorem iof_ine (σ : GQ v) : iota j σ ∈ Ine (F := ℚ) (placeJ j) ↔ σ ∈ Iq v := by
  have h := iof_pw j σ 1
  simp only [pow_one] at h
  rw [(iqBasic v).2.2.1 σ, h]
  exact ⟨fun hg => hg.2, fun hg => ⟨iof_dec j σ, hg⟩⟩

private theorem iof_cyc (l : ℕ) [Fact l.Prime] (σ : GQ v) :
    cycZ ℚ Ω l (iota j σ) = UpperTheory.V.Loc.cyc v l σ := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective j.injective
  have ha : iota j σ ζ = ζ ^ (((cycZ ℚ Ω l (iota j σ) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω (iota j σ)) ζ hζ.pow_eq_one
  have hb : σ (j ζ) = j ζ ^ (((UpperTheory.V.Loc.cyc v l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) _ hζ'.pow_eq_one
  rw [← iota_spec, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

omit [IsAlgClosure ℚ Ω] in
private theorem iof_place (w : HeightOneSpectrum (𝓞 ℚ)) :
    IsPlaceOver (placeJ j) w ↔ ((v : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have h0 : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
    rw [iof_lt, map_natCast]
    have h1 : ‖((v : ℕ) : PadicAlgCl v)‖ = ‖((v : ℕ) : ℚ_[v])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  constructor
  · intro h
    refine (h _).1 ?_
    simpa using h0
  · intro h
    have e : Examples₂.LB.vQ v = w := HeightOneSpectrum.ext
      ((Examples₂.LB.vQ v).isMaximal.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h))
    rw [← e]
    exact Examples₂.LB.isPlaceOver_vQ _ h0

end SlopeTestRemainingChoices

theorem UpperTheory.V.Loc.iotaFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v), IsEmbedding (iota j) ∧ (iota j).range = Dec (F := ℚ) (placeJ j) ∧ (Ine (F := ℚ) (placeJ j)).comap (iota j) = Iq v ∧ (Iq v).map (iota j) = Ine (F := ℚ) (placeJ j) ∧ (∀ (l : ℕ) [Fact l.Prime], (cycZ ℚ Ω l).comp (iota j) = UpperTheory.V.Loc.cyc v l) ∧ (∀ w : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver (placeJ j) w ↔ ((v : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) ∧ ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ ↔ Formalism.ConjugateSelfDual.IsFrob (F := ℚ) (placeJ j) v (iota j σ) := by
  intro Ω _ _ _ v _ j
  haveI : IsGalois ℚ_[v] (Om v) := {}
  refine ⟨((iof_cont j).isClosedEmbedding (iof_inj j)).isEmbedding, iof_range j, Subgroup.ext (iof_ine j), ?_,
    fun l _ => MonoidHom.ext (iof_cyc j l), iof_place j, fun σ => ?_⟩
  · ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (iof_ine j σ).2 hσ
    · intro hg
      have h1 : g ∈ (iota j).range := by
        rw [iof_range]
        exact hg.1
      obtain ⟨σ, rfl⟩ := h1
      exact ⟨σ, (iof_ine j σ).1 hg, rfl⟩
  · exact (iof_pw j σ v).trans ⟨fun hg => ⟨iof_dec j σ, hg⟩, fun hg => hg.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemGKBot
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.R0

variable {l : ℕ} [Fact l.Prime]

theorem mem_Dcr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bcr l) :
    x ∈ Dcr φ ρ ↔ ∀ g, actC φ ρ g x = x := by
  simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_Ddr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bdr l) :
    x ∈ Ddr φ ρ ↔ ∀ g, actD φ ρ g x = x := by
  simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_GK_bot (g : GQ l) : g ∈ GK (botExt l) := by simp [GK, botExt]

variable {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E]
  [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

theorem char_cr (κ : GQ l →* Eˣ) (h : IsCr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bcr l, (∀ g, actC (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Dcr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hdom : IsDomain (PP l).R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  have hc := (isCrField (botExt l) _).1.1 ((isCrIff (botExt l) _).1.1 h)
  have hf : GlobalTheory.RegularRing.FracInv ((PP l).PD (botExt l)) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l _ _ T _ y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [(PP l).PD_actB, (PP l).PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit ((PP l).PD (botExt l)) := by
    intro b hb h
    refine (_root_.GlobalTheory.MemLoc.tied_regular_and_onto l _ _ T).1 (botExt l) b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← (PP l).PD_actB (botExt l) ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.TiedSpan.exists_sum_of_isCrys _ hf hu _ hc 1
  have h0 : finrank ℚ_[l] ↥(K0 (botExt l)) = 1 := by
    rw [show K0 (botExt l) = ⊥ from bot_inf_eq _, IntermediateField.finrank_bot]
  rw [IsCrys, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actC (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actC actVB
    congr 2
    ext b
    exact ((PP l).PD_actB (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQ g)
    (fun b hb => ((PP l).PD L).invB b fun g => by rw [(PP l).PD_actB]; exact hb g) (fun g => (κ g : E))
    (actC (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulC E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Dcr _ _ _).1 hy)

theorem char_dr (κ : GQ l →* Eˣ) (h : IsDr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bdr l, (∀ g, actD (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Ddr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥L.1, y = smulD E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.RegularRing.isField_of_tied T
  have := hF.nontrivial
  have hc := (isCrField (botExt l) _).2.1.1 ((isCrIff (botExt l) _).2.1 h)
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ _ hF hc 1
  have h0 : finrank ℚ_[l] ↥(botExt l).1 = 1 := IntermediateField.finrank_bot
  rw [IsDR, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actD (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actD actVdR
    congr 2
    ext b
    exact ((PP l).PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQdR g)
    (fun b hb => ((PP l).PD L).invdR b fun g => by rw [(PP l).PD_actdR]; exact hb g) (fun g => (κ g : E))
    (actD (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulD E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Ddr _ _ _).1 hy)

end UpperTheory.V.Loc.R0
end

