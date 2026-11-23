module

public import Formalism.SatakeDualWeyl.Statement
public import Lemmata.NearbyExistence.ExistsNear

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions
section
namespace Formalism.UG.P

open Matrix MvPolynomial

theorem linSubst_comp (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (Formalism.UG.linSubst O n M).comp (Formalism.UG.linSubst O n N) = Formalism.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem linSubst_one (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Formalism.UG.linSubst, Matrix.one_apply]

theorem polynomial_action_mul_holds : Formalism.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold Formalism.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AssocFin
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

private lemma smul_quotient_mk (g x : G) : (g • (x : G ⧸ K)) = ((g * x : G) : G ⧸ K) := rfl

private lemma subgroup_smul_quotient_mk (k : K) (x : G) : (k • (x : G ⧸ K)) = (((k : G) * x : G) : G ⧸ K) := rfl

theorem stabilizer_coset_eq (s : G) :
    MulAction.stabilizer K ((s : G ⧸ K)) = (K.map (MulAut.conj s).toMonoidHom).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map, subgroup_smul_quotient_mk,
    QuotientGroup.eq]
  constructor
  · intro hk
    refine ⟨s⁻¹ * k * s, ?_, ?_⟩
    · have := K.inv_mem hk
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨t, ht, hts⟩
    rw [← hts]
    simpa [MulAut.conj_apply, mul_assoc] using K.inv_mem ht

theorem orbit_coset_finite (hK : IsCommensurated K) (s : G) :
    (MulAction.orbit K ((s : G ⧸ K))).Finite := by
  unfold IsCommensurated at hK
  let H := (K.map (MulAut.conj s).toMonoidHom).subgroupOf K
  haveI : H.FiniteIndex := ⟨hK s⟩
  haveI : Finite (K ⧸ MulAction.stabilizer K ((s : G ⧸ K))) := by
    rw [stabilizer_coset_eq K s]
    exact Subgroup.finite_quotient_of_finiteIndex
  exact Set.finite_coe_iff.mp ((MulAction.orbitEquivQuotientStabilizer K _).finite_iff.mpr this)

theorem finite_supp_translate (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (h : G) :
    {x : G ⧸ K | f (h * x.out) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s).image (fun y : G ⧸ K => h⁻¹ • y)).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a • ((s : G ⧸ K)), ⟨a, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk]
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  have hx' : x.out = h⁻¹ * ((a : G) * s * b) := by rw [← hab]; group
  rw [hx']
  convert b.2 using 1
  group

theorem finite_supp_inv (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (g : G) :
    {y : G ⧸ K | f (y.out⁻¹ * g) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s⁻¹).image (fun y : G ⧸ K => g • y)).subset ?_
  intro y hy
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hy
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨b⁻¹ • (((s⁻¹ : G)) : G ⧸ K), ⟨b⁻¹, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk, Subgroup.coe_inv]
  rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
  have hy' : y.out = g * ((a : G) * s * b)⁻¹ := by rw [← hab]; group
  rw [hy']
  convert K.inv_mem a.2 using 1
  group

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := Iff.rfl

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (@DoubleCoset.eq _ _ Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Rep

theorem automorphic_forms_level_finite_holds : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

abbrev conjInter (K : Subgroup G) (s : G) : Subgroup K :=
  (K.map (MulAut.conj s).toMonoidHom).subgroupOf K

theorem finite_quot_conjInter {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    Finite (K ⧸ conjInter K s) := by
  unfold IsCommensurated at hK
  haveI : (conjInter K s).FiniteIndex := ⟨hK s⟩
  exact Subgroup.finite_quotient_of_finiteIndex

theorem mul_eq_out_mul (K : Subgroup G) (s : G) (k : K) :
    ∃ k' : K, (k : G) * s =
      (((QuotientGroup.mk k : K ⧸ conjInter K s).out : K) : G) * s * k' := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (conjInter K s) k
  have hmem : ((h⁻¹ : conjInter K s) : K) ∈ conjInter K s := (h⁻¹).2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hmem
  obtain ⟨m, hmK, hm⟩ := hmem
  refine ⟨⟨m, hmK⟩, ?_⟩
  rw [hh]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv] at hm
  have hm' : s * m = ((h : K) : G)⁻¹ * s := by
    rw [← hm]; group
  simp only [Subgroup.coe_mul]
  rw [mul_assoc _ s, hm']
  group

theorem finite_cosets_in_doset {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * s * b}.Finite := by
  haveI := finite_quot_conjInter hK s
  refine (Set.finite_range
    (fun y : K ⧸ conjInter K s => ((((y.out : K) : G) * s : G) : G ⧸ K))).subset ?_
  rintro x ⟨a, b, hx⟩
  obtain ⟨k', hk'⟩ := mul_eq_out_mul K s a
  refine ⟨QuotientGroup.mk a, ?_⟩
  dsimp only
  have hxx : (QuotientGroup.mk x.out : G ⧸ K) = x := Quotient.out_eq x
  rw [← hxx, hx, hk', QuotientGroup.eq]
  have e : ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s)⁻¹ *
      ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s * k' * b) = k' * b := by
    group
  rw [e]
  exact K.mul_mem k'.2 b.2

theorem finite_support_cosets {k : Type} [Zero k] {K : Subgroup G} (hK : IsCommensurated K)
    {f : G → k} (hf : FinDosetSupp K f) :
    {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ => finite_cosets_in_doset hK s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, h⟩ := hS _ hx
  exact Set.mem_biUnion hs ⟨a, b, h⟩

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
section
namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]

theorem glint_mem_range_of_integral (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have inj : Function.Injective (RingHom.mapMatrix (m := n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext : 1
  simp only [bc, Units.coe_map]
  exact hA

theorem glint_conj_integral (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h : GL n O) (hh : redGL (n := n) (Ideal.span {c * c}) h = 1) :
    ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) ∈
      (RingHom.mapMatrix (m := n) O.subtype).range := by
  have hm : RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) =
      RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by
    rw [map_one]; exact congrArg Units.val hh
  have hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c} := by
    intro a b
    rw [← Ideal.Quotient.eq]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm a) b
  choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)
  let E : Matrix n n O := Matrix.of e
  have hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) =
      (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L) := by
    intro a b
    have h1 := he a b
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hab
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
  have hkey : ((bc (n := n) O.subtype h : GL n L) : Matrix n n L) =
      1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by
    ext a b
    simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      E, Matrix.of_apply, Subring.coe_subtype]
    exact hL a b
  have hcalc : ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) =
      1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E *
        ((c : L) • (g : Matrix n n L)) := by
    rw [Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hcalc]
  exact add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)

theorem glint_princ_le_map_conj (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    princ (n := n) O.subtype (Ideal.span {c * c}) ≤
      (GLint n O).map (MulAut.conj g).toMonoidHom := by
  intro k hk
  simp only [princ, congPre] at hk
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hk
  have hh' : redGL (n := n) (Ideal.span {c * c}) h = 1 := by
    simpa only [Subgroup.mem_comap, Subgroup.mem_bot] using hh
  have hh'' : redGL (n := n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]
  refine Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩
  · apply glint_mem_range_of_integral
    · exact glint_conj_integral O g c hg hg' h hh'
    · have : (g⁻¹ * bc (n := n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by
        rw [map_inv]; group
      rw [this]
      exact glint_conj_integral O g c hg hg' h⁻¹ hh''
  · simp [MulAut.conj_apply, mul_assoc]

theorem glint_princ_relIndex_ne_zero (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by
  classical
  have : Finite (Matrix n n (O ⧸ I)) := inferInstanceAs (Finite (n → n → O ⧸ I))
  have hN : (redGL (n := n) I).ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hsup : ((redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by
    intro h
    apply hN
    have hd := Subgroup.index_dvd_of_le
      (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  have hprinc : princ (n := n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by
    unfold princ congPre
    rw [MonoidHom.comap_bot]
  rw [hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact hsup

theorem glint_exists_denom (A : ValuationSubring L) (g : GL n L) :
    ∃ c : A.toSubring, c ≠ 0 ∧
      (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) A.toSubring.subtype).range ∧
      (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈
        (RingHom.mapMatrix (m := n) A.toSubring.subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → L := fun i => match i with
    | .inl p => (g : Matrix n n L) p.1 p.2
    | .inr p => ((g⁻¹ : GL n L) : Matrix n n L) p.1 p.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) f
  have hmem : ∀ i, (b : L) * f i ∈ A := by
    intro i
    obtain ⟨y, hy⟩ := hb i
    rw [Algebra.smul_def] at hy
    have : (b : L) * f i = (y : L) := hy.symm
    rw [this]; exact y.2
  refine ⟨⟨(b : A), (b : A).2⟩, ?_, ?_, ?_⟩
  · intro h0
    apply nonZeroDivisors.ne_zero b.2
    exact Subtype.ext (congrArg Subtype.val h0)
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * (g : Matrix n n L) i j, hmem (.inl (i, j))⟩, ?_⟩
    ext i j
    simp
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * ((g⁻¹ : GL n L) : Matrix n n L) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j
    simp

end Generic

section Adic

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem glint_exists_approx (x : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v ((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  first | exact Bl.NearbyExistence.goal1 .. | (apply Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply @Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> first | assumption | infer_instance)

theorem glint_finite_residueField :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  have hs : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  exact Finite.of_surjective _ hs

theorem glint_finite_quotient_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : Finite (IsLocalRing.ResidueField R)) (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key : ∀ k : ℕ, Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Ideal.one_eq_top]
      exact Finite.of_fintype (R ⧸ ⊤)
    | succ k ih =>
      have hle : IsLocalRing.maximalIdeal R ^ (k + 1) ≤ IsLocalRing.maximalIdeal R ^ k :=
        Ideal.pow_le_pow_right (by simp)
      replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.toEquiv
      suffices Finite (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))
          (IsLocalRing.maximalIdeal R ^ k)) from
        .of_ideal_quotient (.map (Ideal.Quotient.mk _) (IsLocalRing.maximalIdeal R ^ k))
      exact @Finite.of_equiv _ _ h
        ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal _)
          (IsDiscreteValuationRing.not_a_field _) k).trans
          (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ k))
  have : I = IsLocalRing.maximalIdeal R ^ m := by
    rw [hm, hmax, Ideal.span_singleton_pow]
  rw [this]
  exact key m

end Adic

theorem GL_integral_hecke_commute : Formalism.UG.GLintComm := by
  intro F _ _ v n g
  obtain ⟨c, hc0, hg, hg'⟩ := glint_exists_denom (v.adicCompletionIntegers F) g
  have hP := glint_princ_le_map_conj (v.adicCompletionIntegers F).toSubring g c hg hg'
  have hres : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := glint_finite_residueField v
  have hI : Ideal.span {c * c} ≠ (⊥ : Ideal (v.adicCompletionIntegers F).toSubring) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hc0
  have hfin : Finite ((v.adicCompletionIntegers F).toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hres _ hI
  have hne := glint_princ_relIndex_ne_zero (n := Fin n) (v.adicCompletionIntegers F).toSubring
    (Ideal.span {c * c})
  have hd := Subgroup.relIndex_dvd_of_le_left (bc (n := Fin n) (v.adicCompletionIntegers F).toSubring.subtype).range hP
  intro h0
  apply hne
  unfold GLint at h0 hd
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

end Formalism.UG.P
end

