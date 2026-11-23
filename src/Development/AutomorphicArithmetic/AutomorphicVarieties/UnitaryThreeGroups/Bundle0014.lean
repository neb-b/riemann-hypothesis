module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GaloisGroupPhiCondition
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  haveI : TotallySeparatedSpace (G ⧸ N) := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : x⁻¹ * y ∉ ((ClosedSubgroup.mk N hN : ClosedSubgroup G) : Subgroup G) :=
      fun h => hab (QuotientGroup.eq.2 h)
    rw [ProfiniteGrp.closedSubgroup_eq_sInf_open (ClosedSubgroup.mk N hN), Subgroup.mem_sInf] at hxy
    push_neg at hxy
    obtain ⟨U, ⟨hUo, hNU⟩, hyU⟩ := hxy
    let W : Set G := {g | x⁻¹ * g ∈ U}
    have hWo : IsOpen W := by
      show IsOpen ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))
      exact hUo.preimage (continuous_const.mul continuous_id)
    have hWc : IsClosed W := by
      show IsClosed ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))
      exact (Subgroup.isClosed_of_isOpen U hUo).preimage (continuous_const.mul continuous_id)
    have hsat : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) = W := by
      ext g
      constructor
      · rintro ⟨h, hh, he⟩
        have hn := QuotientGroup.eq.1 he
        show x⁻¹ * g ∈ U
        have := U.mul_mem hh (hNU hn)
        simpa [mul_assoc] using this
      · intro hg
        exact ⟨g, hg, rfl⟩
    refine ⟨QuotientGroup.mk '' W, ⟨?_, QuotientGroup.isOpenMap_coe W hWo⟩, ⟨x, by simp [W], rfl⟩, ?_⟩
    · rw [← (QuotientGroup.isQuotientMap_mk N).isCoinducing.isClosed_preimage, hsat]
      exact hWc
    · intro hy
      have hy' : y ∈ (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) := hy
      rw [hsat] at hy'
      exact hyU hy'
  infer_instance

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h1 : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have h2 := QuotientGroup.eq.1 h1
  simpa [mul_assoc] using h2

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  classical
  intro H hH
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have getN : ∀ W : Set Γ, IsClopen W → (1 : Γ) ∈ W →
      ∃ N : Subgroup Γ, N.Normal ∧ IsOpen (N : Set Γ) ∧ (N : Set Γ) ⊆ W := by
    intro W hW h1
    obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW h1
    exact ⟨N.toOpenSubgroup, N.isNormal', N.toOpenSubgroup.isOpen, hN⟩
  have triv : ∀ N : Subgroup Γ, N.Normal → (N : Set Γ) ⊆ H → ∀ k ∈ N, ∀ y : Γ ⧸ H, k • y = y := by
    intro N hN hNH k hk y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    show ((k * z : Γ) : Γ ⧸ H) = z
    apply QuotientGroup.eq.2
    apply hNH
    have := hN.conj_mem k⁻¹ (N.inv_mem hk) z⁻¹
    simpa [mul_assoc] using this
  have lc : ∀ {X : Type} [TopologicalSpace X] [DiscreteTopology X] (F : Γ → X) (N : Subgroup Γ),
      IsOpen (N : Set Γ) → (∀ g, ∀ k ∈ N, F (g * k) = F g) → Continuous F := by
    intro X _ _ F N hN hF
    rw [continuous_discrete_rng]
    intro b
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun k => g⁻¹ * k) ⁻¹' (N : Set Γ), ?_, ?_, ?_⟩
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
      have := hF g _ hk
      simpa [hg] using this
    · exact hN.preimage (continuous_const.mul continuous_id)
    · show g⁻¹ * g ∈ (N : Set Γ)
      simp [N.one_mem]
  let M := Γ ⧸ H → ZMod n
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let ρ := permR (ZMod n) H
  obtain ⟨N0, hN0n, hN0o, hN0H⟩ := getN (H : Set Γ) ⟨Subgroup.isClosed_of_isOpen H hH, hH⟩ H.one_mem
  have ρmul : ∀ g, ∀ k ∈ N0, ρ (g * k) = ρ g := by
    intro g k hk
    apply LinearMap.ext
    intro f
    funext x
    show f ((g * k)⁻¹ • x) = f (g⁻¹ • x)
    rw [_root_.mul_inv_rev, mul_smul, triv N0 hN0n hN0H k⁻¹ (N0.inv_mem hk)]
  have hcont : ContAction ρ := by
    show Continuous fun p : Γ × M => ρ p.1 p.2
    rw [continuous_discrete_rng]
    intro b
    rw [isOpen_iff_forall_mem_open]
    rintro ⟨g, f⟩ hg
    refine ⟨((fun k => g⁻¹ * k) ⁻¹' (N0 : Set Γ)) ×ˢ {f}, ?_, ?_, ?_⟩
    · rintro ⟨k, f'⟩ ⟨hk, hf'⟩
      simp only [Set.mem_singleton_iff] at hf'
      subst hf'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
      rw [← hg]
      have e : k = g * (g⁻¹ * k) := by group
      rw [e, ρmul g _ hk]
    · exact (hN0o.preimage (continuous_const.mul continuous_id)).prod (isOpen_discrete _)
    · exact ⟨by show g⁻¹ * g ∈ (N0 : Set Γ); simp [N0.one_mem], rfl⟩
  let c : (H →* Multiplicative (ZMod n)) → Γ → M := fun φ g x =>
    Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩)
  have hcoc : ∀ φ : H →* Multiplicative (ZMod n), ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h) := by
    intro φ g h
    funext x
    show Multiplicative.toAdd (φ ⟨_, sec_mem H (g * h) x⟩) =
      Multiplicative.toAdd (φ ⟨_, sec_mem H g x⟩) + Multiplicative.toAdd (φ ⟨_, sec_mem H h (g⁻¹ • x)⟩)
    rw [← toAdd_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev, mul_smul]
    group
  have hZ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → c φ ∈ Z1 ρ := by
    intro φ hφ
    show Continuous (c φ) ∧ ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h)
    refine ⟨?_, hcoc φ⟩
    let K : Subgroup Γ := φ.ker.map H.subtype
    have hKo : IsOpen (K : Set Γ) := by
      simp only [K]
      rw [Subgroup.coe_map, Subgroup.coe_subtype]
      exact hH.isOpenMap_subtype_val _ hφ
    have hKH : (K : Set Γ) ⊆ H := by
      intro k hk
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hk
      exact y.2
    obtain ⟨N, hNn, hNo, hNK⟩ := getN (K : Set Γ) ⟨Subgroup.isClosed_of_isOpen K hKo, hKo⟩ K.one_mem
    have hk0 : ∀ k ∈ N, c φ k = 0 := by
      intro k hk
      funext x
      have hfix : k⁻¹ • x = x := triv N hNn (hNK.trans hKH) k⁻¹ (N.inv_mem hk) x
      have hmem : (x.out)⁻¹ * k * (k⁻¹ • x).out ∈ K := by
        rw [hfix]
        apply hNK
        have := hNn.conj_mem k hk (x.out)⁻¹
        simpa using this
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hmem
      show Multiplicative.toAdd (φ ⟨_, sec_mem H k x⟩) = 0
      have hyy : (⟨_, sec_mem H k x⟩ : H) = y := Subtype.ext hye.symm
      rw [hyy, MonoidHom.mem_ker.1 hy]
      rfl
    apply lc (c φ) N hNo
    intro g k hk
    rw [hcoc φ g k, hk0 k hk, map_zero, add_zero]
  let F : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → H1 ρ :=
    fun φ => Submodule.Quotient.mk ⟨c φ.1, hZ φ.1 φ.2⟩
  have hfin : Finite (H1 ρ) := h M ρ hcont
  refine Finite.of_injective F ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
  have hq := (Submodule.Quotient.eq _).1 hEq
  rw [Submodule.mem_comap] at hq
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hq
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  let x0 : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hfix : (h : Γ)⁻¹ • x0 = x0 := by
    show (((h : Γ)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    apply QuotientGroup.eq.2
    simpa using h.2
  have ht : x0.out ∈ H := by
    have e : ((x0.out : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H) := QuotientGroup.out_eq' x0
    have := QuotientGroup.eq.1 e
    simpa using this
  have hval : ∀ χ : H →* Multiplicative (ZMod n), c χ h x0 = Multiplicative.toAdd (χ h) := by
    intro χ
    show Multiplicative.toAdd (χ ⟨_, sec_mem H h x0⟩) = _
    have hel : (⟨_, sec_mem H h x0⟩ : H) = (⟨x0.out, ht⟩ : H)⁻¹ * h * ⟨x0.out, ht⟩ := by
      apply Subtype.ext
      simp [hfix]
    rw [hel]
    congr 1
    rw [map_mul, map_mul, map_inv, mul_comm (χ ⟨x0.out, ht⟩)⁻¹ (χ h), mul_assoc, inv_mul_cancel, mul_one]
  have hx := congrFun (congrFun hm h) x0
  have hL : (d0 ρ m) h x0 = 0 := by
    show m ((h : Γ)⁻¹ • x0) - m x0 = 0
    rw [hfix, sub_self]
  have hR : (d0 ρ m) h x0 = c φ h x0 - c ψ h x0 := hx
  have hcc : c φ h x0 = c ψ h x0 := sub_eq_zero.1 (hR.symm.trans hL)
  rw [hval φ, hval ψ] at hcc
  exact hcc

theorem UpperTheory.galois_group_phi_condition :
    GlobalFiniteness → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))), ContainsAbove S l →
          PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) l ∧ CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) ∧ T2Space (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) ∧ TotallyDisconnectedSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := by
  intro hGF Ω _ _ _ l _ S hS
  haveI : IsClosed ((NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Set (G ℚ Ω))) := isClosed_NS Ω _
  refine ⟨?_, inferInstance, inferInstance, totDisc_quot _ (isClosed_NS Ω _)⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero 1 (Fact.out : l.Prime).ne_zero⟩
  have key := phi_condition_of_finite_cohomology (Γ := GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1)
    (fun M _ _ _ _ _ ρ hc => (hGF ℚ Ω l 1 M S ρ one_pos hS hc).2.1)
  rwa [pow_one] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GlobalEulerCharacteristicOdd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.global_euler_characteristic_odd :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
                   ∀ ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M, ContAction ρ → (∃ g : G ℚ Ω, cycMod ℚ Ω l 1 g = -1 ∧ ρ (toGS Ω _ g) = 1) →
                   ∀ x : ∀ v : S, H2 (ρ.comp ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A v)).subtype) : Representation k _ M), ∃ z : H2 ρ,
                     ∀ v, resH2 ρ ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A v)).subtype) ((continuous_toGS Ω _).comp continuous_subtype_val) z = x v := by
  intro hPT Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ hl S A hS hA ρ hρ hg x
  obtain ⟨g, hg1, hg2⟩ := hg
  haveI : Finite M := Module.finite_of_finite k
  have hp : l.Prime := Fact.out
  choose κ hκ using fun v => Submodule.Quotient.mk_surjective _ (x v)
  have hn : ((l - 1 : ℕ) : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 g : (ZMod (l ^ 1))ˣ) := by
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_one]
    rw [hg1, Nat.cast_sub hp.one_le, h0]
    simp
  have hne : (1 : k) ≠ ((l - 1 : ℕ) : k) := by
    rw [Nat.cast_sub hp.one_le, CharP.cast_eq_zero k l, Nat.cast_one]
    intro h
    have h2 : ((2 : ℕ) : k) = 0 := by
      push_cast
      linear_combination h
    rw [CharP.cast_eq_zero_iff k l] at h2
    exact hl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  obtain ⟨z, hz⟩ := UpperTheory.global_cohomology_finite_set hPT Ω l hl k M S A ρ hS hA hρ
    ⟨g, 1, l - 1, fun m => by rw [one_smul]; exact (congrArg (fun f : Module.End k M => f m) hg2), hn, hne⟩ κ
  refine ⟨Submodule.Quotient.mk z, fun v => ?_⟩
  rw [← hκ v]
  exact (Submodule.Quotient.eq _).2 (hz v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.InertiaLeNormalIffKerLeAndInertiaLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem valuation_natCast_lt_one_iff_mem_asIdeal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (hA : IsPlaceOver A v) :
    A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hA ((l : ℕ) : 𝓞 ℚ)
  simpa using h

theorem UpperTheory.inertia_le_normal_iff_ker_le_and_inertia_le :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
          (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) → ∀ (H : Subgroup (G ℚ Ω)) [H.Normal], (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ H →
          ∀ (M : Subgroup (G ℚ Ω)) [M.Normal], IsClosed (M : Set (G ℚ Ω)) →
          ((∀ g, (∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A' ∧ g ∈ H) → g ∈ M) ↔
            ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ M ∧ ∀ v : S, v ≠ v₀ → Ine (F := ℚ) (A v) ⊓ H ≤ M)) := by
  intro Ω _ _ _ l _ S A v₀ hS hA hv₀ H _ hH M _ hM
  have hker : (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker = NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    simp [toGS, QuotientGroup.ker_mk']
  have hin : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ (S : Set (HeightOneSpectrum (𝓞 ℚ))) →
      IsPlaceOver B w → (Ine (F := ℚ) B : Set (G ℚ Ω)) ⊆ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro B w hw hB g hg
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, B, hB, hg⟩
  constructor
  · intro h
    constructor
    · rw [hker]
      apply Subgroup.topologicalClosure_minimal _ _ hM
      apply Subgroup.normalClosure_le_normal
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨w, hw, B, hB, hgB⟩ := hg
      have hgI : g ∈ Ine (F := ℚ) B := hgB
      apply h g
      refine ⟨B, ?_, hgI, ?_⟩
      · rw [valuation_natCast_lt_one_iff_mem_asIdeal l B w hB]
        intro hl
        exact hw (by simpa using hS w hl)
      · apply hH
        rw [hker]
        exact hin B w hw hB hgI
    · intro v hv g hg
      rw [Subgroup.mem_inf] at hg
      apply h g
      refine ⟨A v, ?_, hg.1, hg.2⟩
      rw [valuation_natCast_lt_one_iff_mem_asIdeal l (A v) v.1 (hA v), hv₀]
      exact hv
  · rintro ⟨h1, h2⟩ g ⟨B, hBl, hgB, hgH⟩
    by_cases hBt : B = ⊤
    · subst hBt
      rw [(Kum.placeDict ℚ Ω).1] at hgB
      rw [Subgroup.mem_bot] at hgB
      subst hgB
      exact M.one_mem
    obtain ⟨w, hw⟩ := (Kum.placeDict ℚ Ω).2.1 B hBt
    by_cases hwS : w ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    · let u : S := ⟨w, hwS⟩
      have hu0 : u ≠ v₀ := by
        intro hu
        rw [← hv₀ u] at hu
        exact hBl ((valuation_natCast_lt_one_iff_mem_asIdeal l B w hw).2 hu)
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hA u) hw
      rw [← hσ] at hgB
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (A u) := ((ML.placeBasic Ω).2.2.2.2.2.2.2.2.2 (A u) σ).2.1 g |>.1 hgB
      have hcH : σ⁻¹ * g * σ ∈ H := by
        have := ‹H.Normal›.conj_mem g hgH σ⁻¹
        simpa [mul_assoc] using this
      have hcM := h2 u hu0 (Subgroup.mem_inf.2 ⟨hc, hcH⟩)
      have := ‹M.Normal›.conj_mem _ hcM σ
      simpa [mul_assoc] using this
    · apply h1
      rw [hker]
      exact hin B w hwS hw hgB
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MemGalOfQuadraticOfFixesDiscrRootsOfUnity
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base

private theorem UpperTheory.exists_fixed_square_root_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (g : Ω →+* Ω) (n : ℕ) :
    Odd n → (∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ) →
      ∃ m : ℤ, m.natAbs = n ∧ m % 4 = 1 ∧ ∃ s : Ω, s ^ 2 = m ∧ g s = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hg
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, rfl, rfl, 1, by norm_num, map_one g⟩
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      rw [← hp_def] at hk
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hk
        obtain ⟨a, ha⟩ := hn
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · obtain ⟨a, ha⟩ := hn
          rw [h, mul_zero] at hk
          omega
        · exact h
      have hkn : k < n := by
        rw [hk]
        have := hp.two_le
        nlinarith
      have hkodd : Odd k := (Nat.odd_mul.mp (hk ▸ hn)).2
      obtain ⟨m', hm'abs, hm'4, s', hs'sq, hgs'⟩ :=
        ih k hkn hkodd (fun ζ hζ => hg ζ (by rw [hk, pow_mul', hζ, one_pow]))
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
      obtain ⟨⟨x, hx⟩, hall⟩ := CF.gauss Ω p ζ hp2 hζ
      have hgz : g ζ = ζ ^ 1 := by
        rw [pow_one]
        exact hg ζ (by rw [hk, pow_mul, hζ.pow_eq_one, one_pow])
      have hgx : g x = x := by
        have := (hall x hx).2 g 1 hgz
        simpa [legendreSym.at_one] using this
      have hps : (CF.pStar p).natAbs = p := by
        simp [CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
      have hp4 : CF.pStar p % 4 = 1 := by
        obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
        clear_value p
        rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
        · have e : p / 2 = 2 * c := by omega
          have hpz : (p : ℤ) = 4 * c + 1 := by omega
          rw [CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
        · have e : p / 2 = 2 * c + 1 := by omega
          have hpz : (p : ℤ) = 4 * c + 3 := by omega
          rw [CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
      refine ⟨CF.pStar p * m', ?_, ?_, x * s', ?_, ?_⟩
      · rw [Int.natAbs_mul, hps, hm'abs, hk]
      · rw [Int.mul_emod, hp4, hm'4]
        rfl
      · rw [mul_pow, hx, hs'sq]
        push_cast
        ring
      · rw [map_mul, hgx, hgs']

theorem UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → Odd (discr K).natAbs → ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (discr K).natAbs = 1 → g ζ = ζ) → g ∈ galOf ℚ K Ω := by
  intro Ω _ _ _ K _ _ _ hK hodd g hg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨m, hmabs, hm4, s, hs, hgs⟩ :=
    UpperTheory.exists_fixed_square_root_odd (g : Ω →+* Ω) (discr K).natAbs hodd (fun ζ h => by simpa using hg ζ h)
  have hd4 : discr K % 4 = 1 := by
    have h2 : Odd (discr K) := Int.natAbs_odd.mp hodd
    rcases GlobalTheory.QuadraticZeta.discr_mod_four hK with h | h
    · obtain ⟨c, hc⟩ := h2
      omega
    · exact h
  have hm : m = discr K := by
    rcases Int.natAbs_eq_natAbs_iff.mp hmabs with h | h
    · exact h
    · rw [h] at hm4
      omega
  subst hm
  have hgs' : g s = s := by simpa using hgs
  obtain ⟨b, t, n, hb0, hb1, hd⟩ := GlobalTheory.QuadraticZeta.exists_basis hK
  set θ : Ω := algebraMap K Ω ((b 1 : 𝓞 K) : K) with hθ
  have hθ2 : θ ^ 2 = t * θ - n := by
    have := congrArg (fun z : 𝓞 K => algebraMap K Ω (z : K)) hb1
    simpa [hθ] using this
  have hy : (2 * θ - t) ^ 2 = s ^ 2 := by
    rw [hs, hd]
    push_cast
    linear_combination 4 * hθ2
  have hgθ : g θ = θ := by
    have hgy : g (2 * θ - t) = 2 * θ - t := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
      · rw [h, hgs']
      · rw [h, map_neg, hgs']
    have e : 2 * g θ - t = 2 * θ - t := by
      rw [← hgy, map_sub, map_mul, map_ofNat, map_intCast]
    linear_combination (1 / 2 : Ω) * e
  have hint : ∀ a : 𝓞 K, g (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K) := by
    intro a
    have e : algebraMap K Ω (a : K) = ((b.repr a 0 : ℤ) : Ω) + ((b.repr a 1 : ℤ) : Ω) * θ := by
      conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b hb0 a]
      simp [hθ]
    rw [e, map_add (f := _), map_mul, map_intCast, map_intCast, hgθ]
  change ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x
  intro x
  obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  rw [map_div₀, map_div₀]
  exact congrArg₂ (· / ·) (hint a) (hint c)
end

