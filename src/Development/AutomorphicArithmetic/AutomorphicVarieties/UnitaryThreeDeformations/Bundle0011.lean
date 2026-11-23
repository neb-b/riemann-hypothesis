module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostEx
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base

private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : Pl where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

private theorem fin_above {n : ℕ} (hn : n ≠ 0) : {v : Pl | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {((n : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact hv

private theorem cls_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (S : Set Pl)
    (hS : ∀ v ∉ S, ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ μ : GS Ω S →* (ZMod M)ˣ, μ.comp (toGS Ω S) = Chr.cls ℚ Ω M := by
  obtain ⟨hopen, -, -, -, hine⟩ := Chr.clsFacts ℚ Ω M
  obtain ⟨-, -, -, hpl⟩ := Kum.placeDict ℚ Ω
  have hle : NS Ω S ≤ (Chr.cls ℚ Ω M).ker := by
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    have hn : ¬ A.valuation ((M : ℕ) : Ω) < 1 := by
      rw [hpl A v M hA]
      exact hS v hv
    exact hine A hn hσA
  exact ⟨QuotientGroup.lift (NS Ω S) (Chr.cls ℚ Ω M) hle, QuotientGroup.lift_comp_mk' _ _ _⟩

private theorem cc_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, j, hj⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) (fun q => by simp), j, fun x => hj x⟩

end

theorem UpperTheory.V.UnitaryThreeInertia.exists_hostFrame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∃ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hd
  have hl : l.Prime := Fact.out
  have hlN : l * N ≠ 0 := Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)
  set S : Finset Pl := (fin_above hlN).toFinset with hSdef
  have hmem : ∀ v : Pl, v ∈ S ↔ (((l * N : ℕ)) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal :=
    fun v => Set.Finite.mem_toFinset _
  have hout : ∀ m : ℕ, m ∣ l * N → ∀ v ∉ (S : Set Pl),
      ((m : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro m hm v hv hmv
    apply hv
    rw [Finset.mem_coe, hmem]
    obtain ⟨k, hk⟩ := hm
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hmv
  have h4 : ∀ v ∉ (S : Set Pl), ((4 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro v hv h4v
    have h2 : ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
      have h22 : ((4 : ℕ) : NumberField.RingOfIntegers ℚ) =
          ((2 : ℕ) : NumberField.RingOfIntegers ℚ) * ((2 : ℕ) : NumberField.RingOfIntegers ℚ) := by
        rw [← Nat.cast_mul]
      rw [h22] at h4v
      rcases v.isPrime.mem_or_mem h4v with h | h <;> exact h
    exact hout 2 (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hd.N_even) l) v hv h2
  obtain ⟨μN, hμN⟩ := cls_exists Ω N (S : Set Pl) (hout N (dvd_mul_left N l))
  obtain ⟨μ4, hμ4⟩ := cls_exists Ω 4 (S : Set Pl) h4
  obtain ⟨χl, hχl⟩ :=
    Formalism.GaloisCohomology.chi_exists (F := ℚ) (Ω := Ω) l (S : Set Pl) (hout l (dvd_mul_right l N))
  obtain ⟨σ, hσ⟩ := cc_exists Ω
  let A : S → ValuationSubring Ω := fun v => Classical.choose (exists_isPlaceOver Ω (v : Pl))
  have hA := fun v : S => Classical.choose_spec (exists_isPlaceOver Ω (v : Pl))
  have hvl : vQ hl ∈ S := by
    rw [hmem]
    exact Ideal.mem_span_singleton.mpr ⟨(N : NumberField.RingOfIntegers ℚ), by push_cast; ring⟩
  let F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S :=
    { π := toGS Ω (S : Set Pl)
      η := (MulChar.toUnitHom ZMod.χ₄).comp μ4
      Ψ := ((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN
      c := toGS Ω (S : Set Pl) σ
      D := fun v => Dec (A v)
      I := fun v => Ine (A v)
      vl := ⟨vQ hl, hvl⟩
      Sb := {v | ∃ p ∈ Sb l ψ, (p : NumberField.RingOfIntegers ℚ) ∈ (v : Pl).asIdeal} }
  refine ⟨S, A, F, ?_⟩
  refine ⟨hmem, hA, rfl, ?_, ?_, ⟨σ, hσ, rfl⟩, fun _ => rfl, fun _ => rfl, ?_, fun _ => Iff.rfl⟩
  · show ((MulChar.toUnitHom ZMod.χ₄).comp μ4).comp (toGS Ω (S : Set Pl)) = eta4 Ω
    rw [MonoidHom.comp_assoc, hμ4]
    unfold eta4 UpperTheory.V.Chr.dirG
    rfl
  · show (((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN).comp (toGS Ω (S : Set Pl)) = _
    unfold UpperTheory.V.Chr.Psi UpperTheory.V.Chr.dirG UpperTheory.V.Base.chiO
    rw [← hχl, ← hμN]
    ext τ
    simp
  · exact Ideal.mem_span_singleton_self _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostPhi
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, ?_⟩
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    by_contra hg
    have hgN : g ∉ N := fun h => hg ((QuotientGroup.eq_one_iff g).mpr h)
    have hcl := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G) ⟨N, hN⟩
    have hnot : g ∉ sInf {K : Subgroup G | IsOpen (K : Set G) ∧ ((⟨N, hN⟩ : ClosedSubgroup G) : Subgroup G) ≤ K} := by
      rw [← hcl]
      exact hgN
    rw [Subgroup.mem_sInf] at hnot
    push_neg at hnot
    obtain ⟨K, ⟨hKo, hNK⟩, hgK⟩ := hnot
    have hNK' : N ≤ K := hNK
    have hpre : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' ((QuotientGroup.mk : G → G ⧸ N) '' (K : Set G)) = K := by
      ext y
      constructor
      · rintro ⟨k, hk, hky⟩
        have h1 : k⁻¹ * y ∈ N := QuotientGroup.eq.mp hky
        simpa using K.mul_mem hk (hNK' h1)
      · intro hy
        exact ⟨y, hy, rfl⟩
    have hclo : IsClopen ((QuotientGroup.mk : G → G ⧸ N) '' (K : Set G)) := by
      rw [← (QuotientGroup.isQuotientMap_mk N).isClopen_preimage, hpre]
      exact ⟨K.isClosed_of_isOpen hKo, hKo⟩
    have hsub := hclo.connectedComponent_subset (x := 1) ⟨1, K.one_mem, rfl⟩
    obtain ⟨k, hk, hkg⟩ := hsub hx
    apply hgK
    have h2 : k⁻¹ * g ∈ N := QuotientGroup.eq.mp hkg
    simpa using K.mul_mem hk (hNK' h2)

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h1 : (QuotientGroup.mk (g⁻¹ * x.out) : Γ ⧸ H) = QuotientGroup.mk ((g⁻¹ • x).out) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have h2 := QuotientGroup.eq.mp h1
  simpa [_root_.mul_inv_rev, mul_assoc] using h2

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  unfold PhiCond
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage]
      have hpre : (QuotientGroup.mk : Γ → Γ ⧸ H) ⁻¹' {(g : Γ ⧸ H)} = (fun y => g⁻¹ * y) ⁻¹' (H : Set Γ) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
        rw [QuotientGroup.eq, ← H.inv_mem_iff]
        simp [_root_.mul_inv_rev]
      rw [hpre]
      exact hH.preimage (continuous_const.mul continuous_id)
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  have hcont : ReciprocityTheory.Gal.ContAction (permR (ZMod n) H) := by
    unfold ReciprocityTheory.Gal.ContAction
    apply continuous_prod_of_discrete_right.mpr
    intro m
    apply continuous_pi
    intro x
    simp only [permR_apply]
    exact (continuous_of_discreteTopology (f := m)).comp (continuous_inv.smul continuous_const)
  haveI := h (Γ ⧸ H → ZMod n) (permR (ZMod n) H) hcont
  let cf : (H →* Multiplicative (ZMod n)) → Γ → Γ ⧸ H → ZMod n := fun φ g x =>
    Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩)
  have hcoc : ∀ (φ : H →* Multiplicative (ZMod n)) (g k : Γ),
      cf φ (g * k) = cf φ g + permR (ZMod n) H g (cf φ k) := by
    intro φ g k
    funext x
    simp only [cf, permR_apply, Pi.add_apply]
    rw [← toAdd_mul, ← map_mul]
    refine congrArg (fun y => Multiplicative.toAdd (φ y)) ?_
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [_root_.mul_inv_rev, mul_smul]
    group
  have hcont_c : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous (cf φ) := by
    intro φ hφ
    have hK : IsOpen (Subtype.val '' (φ.ker : Set H) : Set Γ) := hH.isOpenMap_subtype_val _ hφ
    let U : Set Γ := ⋂ y : Γ ⧸ H, (fun u => (y.out)⁻¹ * u * y.out) ⁻¹' (Subtype.val '' (φ.ker : Set H))
    have hUo : IsOpen U :=
      isOpen_iInter_of_finite (fun y => hK.preimage ((continuous_const.mul continuous_id).mul continuous_const))
    have h1U : (1 : Γ) ∈ U := by
      simp only [U, Set.mem_iInter, Set.mem_preimage]
      intro y
      exact ⟨1, φ.ker.one_mem, by simp⟩
    have hzero : ∀ u ∈ U, cf φ u = 0 := by
      intro u hu
      funext y
      obtain ⟨k, hk, hkv⟩ := Set.mem_iInter.mp hu y
      have hkv' : (k : Γ) = (y.out)⁻¹ * u * y.out := hkv
      have hmem : (y.out)⁻¹ * u * y.out ∈ H := by
        rw [← hkv']
        exact k.2
      have huy : u • y = y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have := H.inv_mem hmem
        simpa [_root_.mul_inv_rev, mul_assoc] using this
      have hy : u⁻¹ • y = y := inv_smul_eq_iff.mpr huy.symm
      have hel : (⟨(y.out)⁻¹ * u * (u⁻¹ • y).out, sec_mem H u y⟩ : H) = k := by
        apply Subtype.ext
        simp only
        rw [hy]
        exact hkv'.symm
      simp only [cf, Pi.zero_apply]
      rw [hel, φ.mem_ker.mp hk, toAdd_one]
    rw [continuous_iff_continuousAt]
    intro g
    have hnb : (fun g' => g⁻¹ * g') ⁻¹' U ∈ nhds g :=
      (hUo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1U)
    refine (continuousAt_const : ContinuousAt (fun _ : Γ => cf φ g) g).congr ?_
    filter_upwards [hnb] with g' hg'
    have h2 := hcoc φ g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hzero _ hg', map_zero, add_zero] at h2
    exact h2.symm
  let Φ : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → H1 (permR (ZMod n) H) :=
    fun φ => Submodule.Quotient.mk
      (⟨cf φ.1, by unfold Z1; exact ⟨hcont_c φ.1 φ.2, hcoc φ.1⟩⟩ : Z1 (permR (ZMod n) H))
  have hinj : Function.Injective Φ := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ heq
    apply Subtype.ext
    simp only [Φ] at heq
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at heq
    unfold B1 at heq
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp heq
    ext k
    have ho : ((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out) ∈ H := by
      have h0 : (QuotientGroup.mk ((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out) : Γ ⧸ H) = QuotientGroup.mk 1 :=
        QuotientGroup.out_eq' _
      have := QuotientGroup.eq.mp h0
      simpa using this
    set o := ((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out) with ho_def
    have hhH : o * (k : Γ) * o⁻¹ ∈ H := H.mul_mem (H.mul_mem ho k.2) (H.inv_mem ho)
    have hx₀ : (o * (k : Γ) * o⁻¹)⁻¹ • (QuotientGroup.mk (1 : Γ) : Γ ⧸ H) = QuotientGroup.mk 1 := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simpa using hhH
    have hk' : (⟨((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out)⁻¹ * (o * (k : Γ) * o⁻¹) *
        ((o * (k : Γ) * o⁻¹)⁻¹ • (QuotientGroup.mk (1 : Γ) : Γ ⧸ H)).out,
        sec_mem H _ _⟩ : H) = k := by
      apply Subtype.ext
      simp only
      rw [hx₀, ← ho_def]
      group
    have hev := congrFun (congrFun hm (o * (k : Γ) * o⁻¹)) (QuotientGroup.mk 1)
    unfold ReciprocityTheory.Gal.d0 at hev
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, permR_apply,
      Submodule.coe_sub, Submodule.subtype_apply] at hev
    rw [hx₀, sub_self] at hev
    simp only [cf] at hev
    rw [hk'] at hev
    have hfin : Multiplicative.toAdd (φ k) - Multiplicative.toAdd (ψ k) = (0 : ZMod n) := hev.symm
    have h4 : Multiplicative.toAdd (φ k) = Multiplicative.toAdd (ψ k) := sub_eq_zero.mp hfin
    exact Multiplicative.toAdd.injective h4
  exact Finite.of_injective Φ hinj

theorem UpperTheory.V.UnitaryThreeInertia.hostFrame_phi :
    GlobalFiniteness → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    PhiCond (Gam Ω S) l ∧ CompactSpace (Gam Ω S) ∧ T2Space (Gam Ω S) ∧ TotallyDisconnectedSpace (Gam Ω S) ∧ CompactSpace (Formalism.ConjugateSelfDual.G ℚ Ω) ∧ T2Space (Formalism.ConjugateSelfDual.G ℚ Ω) ∧ TotallyDisconnectedSpace (Formalism.ConjugateSelfDual.G ℚ Ω) := by
  intro hGF Ω _ _ _ l _ c N _ e ψ o₁ _hD S A F hF
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hT2 : T2Space (Gam Ω S) := by
    haveI : IsClosed (NS Ω (↑S : Set Pl) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := isClosed_NS (F := ℚ) Ω _
    unfold Gam
    infer_instance
  have hTD : TotallyDisconnectedSpace (Gam Ω S) := by
    unfold Gam
    exact totDisc_quot _ (isClosed_NS (F := ℚ) Ω _)
  have hCA : ReciprocityTheory.Gal.ContainsAbove (F := ℚ) S l := by
    unfold ReciprocityTheory.Gal.ContainsAbove
    intro v hv
    apply (hF.mem v).mpr
    simpa [Nat.cast_mul, mul_comm] using Ideal.mul_mem_right (N : NumberField.RingOfIntegers ℚ) v.asIdeal hv
  unfold GlobalFiniteness at hGF
  have key : ∀ k : ℕ, k = l ^ 1 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod k) M] [TopologicalSpace M]
      [DiscreteTopology M] [Finite M] (ρ : Representation (ZMod k) (Gam Ω S) M),
      ReciprocityTheory.Gal.ContAction ρ → Finite (H1 ρ) := by
    intro k hk
    subst hk
    intro M _ _ _ _ _ ρ hρ
    have hGFa := hGF ℚ Ω l 1 M S ρ
    unfold ReciprocityTheory.Gal.GlobalFinitenessAt at hGFa
    exact (hGFa Nat.one_pos hCA hρ).2.1
  have hPhi : PhiCond (Gam Ω S) l := by
    apply phi_condition_of_finite_cohomology l
    intro M _ _ _ _ _ ρ hρ
    exact key l (pow_one l).symm M ρ hρ
  exact ⟨hPhi, inferInstance, hT2, hTD, inferInstance, inferInstance, inferInstance⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocalEulerCharacteristicRationals
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem ef_eq_one (v : Pl) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI : Fintype ((v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hmem : v.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) :=
    ⟨inferInstance, ⟨rfl⟩⟩
  have hle := Finset.single_le_sum
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v.asIdeal, hmem⟩ : (v.asIdeal.under ℤ).primesOver _))
  have he := Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal
  have hf := Ideal.inertiaDeg_pos v.asIdeal ℤ
  simp only at hle
  rw [hsum] at hle
  have := Nat.mul_pos he hf
  omega

theorem UpperTheory.local_euler_characteristic_rationals :
    LocalFiniteness → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : Pl) (ρ : Representation k (Dec (F := ℚ) A) M),
        Formalism.ConjugateSelfDual.IsPlaceOver A v → ContAction ρ →
        Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M) ∧
          (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ)) := by
  intro hFin hEC Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ A v ρ hv hc
  classical
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  let φ : ZMod (l ^ 1) →+* k := ZMod.castHom (dvd_refl _) k
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M φ
  haveI : LinearMap.CompatibleSMul M M (ZMod (l ^ 1)) k := ⟨fun f c x => f.map_smul (φ c) x⟩
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := ℚ) A) M :=
    { toFun := fun g => (ρ g).restrictScalars (ZMod (l ^ 1))
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }
  have hc' : ContAction ρ' := hc
  have hF := hFin ℚ Ω l 1 M A ρ' v one_pos hv hc'
  have hE := hEC ℚ Ω l 1 M A ρ' v one_pos hv hc'
  have e1 : H1 ρ' ≃ H1 ρ := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ' ≃ H2 ρ := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e0 : ↥(H0 ρ') ≃ ↥(H0 ρ) := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  haveI := hF.2.1
  haveI := hF.2.2.1
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k M := Module.Finite.of_finite
  haveI : Module.Finite k ↥(H0 ρ) := Module.Finite.of_finite
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have inj := Nat.pow_right_injective (show 2 ≤ Nat.card k by omega)
  have c1 : Nat.card (H1 ρ') = Nat.card k ^ finrank k (H1 ρ) := by
    rw [Nat.card_congr e1]; exact Module.natCard_eq_pow_finrank
  have c2 : Nat.card (H2 ρ') = Nat.card k ^ finrank k (H2 ρ) := by
    rw [Nat.card_congr e2]; exact Module.natCard_eq_pow_finrank
  have c0 : Nat.card ↥(H0 ρ') = Nat.card k ^ finrank k ↥(H0 ρ) := by
    rw [Nat.card_congr e0]; exact Module.natCard_eq_pow_finrank
  have cM : Nat.card M = Nat.card k ^ finrank k M := Module.natCard_eq_pow_finrank
  have hd : locDeg v = 1 := ef_eq_one v
  refine ⟨inferInstance, inferInstance, fun hl => ?_, fun hl => ?_⟩
  · have h := hE.1 hl
    rw [c1, c0, c2, cM, hd, pow_one, ← pow_add, ← pow_add] at h
    exact inj h
  · have h := hE.2 hl
    rw [c1, c0, c2, ← pow_add] at h
    exact inj h
end

