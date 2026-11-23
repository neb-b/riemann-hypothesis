module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionDecompositionGroups
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem open_toZMod (l : ℕ) [Fact l.Prime] : IsOpen {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
  have hS : {x : ℤ_[l] | PadicInt.toZMod x = 1} = {x | ‖x - 1‖ < 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
  rw [hS]
  exact isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem UpperTheory.frame_criterion_decomposition_groups :
    UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic := by
  unfold UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hK g hg hc M' hM'
  let ρ : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hemb : Continuous (galEmb ℚ (W.Lp L) Ω) := (galEmbTop ℚ (W.Lp L) Ω).1.continuous
  have hρ : Continuous ρ := by
    have hto : Continuous (toUpl Ω L) := continuous_induced_rng.2 hemb
    exact k.p_cont.comp hto
  let U1 : Subgroup (G (W.Lp L) Ω) := Φ.Ψ.ker.comap ρ
  let U2 : Subgroup (G (W.Lp L) Ω) :=
    ((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom).comp (cycZ (W.Lp L) Ω l)).ker
  let U3 : Subgroup (G (W.Lp L) Ω) := (η.comp (galEmb ℚ (W.Lp L) Ω)).ker
  have hU2 : ∀ τ, τ ∈ U2 ↔ PadicInt.toZMod (cycZ (W.Lp L) Ω l τ : ℤ_[l]) = 1 := by
    intro τ
    simp [U2, MonoidHom.mem_ker, Units.ext_iff]
  have hfix : ∀ τ : G (W.Lp L) Ω, τ ∈ galOf (W.Lp L) L Ω ↔ τ ∈ U3 := by
    intro τ
    change _ ↔ η (galEmb ℚ (W.Lp L) Ω τ) = 1
    rw [← k.mem_range_resP τ, mem_galOf]
    constructor
    · intro hτ
      exact ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), AlgEquiv.ext fun y => rfl⟩
    · rintro ⟨t, rfl⟩ x
      exact t.commutes x
  have hO1 : IsOpen (U1 : Set (G (W.Lp L) Ω)) := hK.preimage hρ
  have hO2 : IsOpen (U2 : Set (G (W.Lp L) Ω)) := by
    have hset : (U2 : Set (G (W.Lp L) Ω)) =
        (fun τ => (cycZ (W.Lp L) Ω l τ : ℤ_[l])) ⁻¹' {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
      ext τ
      exact hU2 τ
    rw [hset]
    exact (open_toZMod l).preimage (Units.continuous_val.comp (continuous_cycZ (W.Lp L) Ω l))
  have hO3 : IsOpen (U3 : Set (G (W.Lp L) Ω)) := by
    have hset : (U3 : Set (G (W.Lp L) Ω)) = galOf (W.Lp L) L Ω := by
      ext τ
      exact (hfix τ).symm
    rw [hset]
    exact (galEmbTop (W.Lp L) L Ω).2.1
  haveI hN1 : U1.Normal := (Φ.Ψ.normal_ker).comap ρ
  let U : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U2 ⊓ U3
  haveI : U.Normal := inferInstance
  have hOU : IsOpen (U : Set (G (W.Lp L) Ω)) := (hO1.inter hO2).inter hO3
  let g' : G (W.Lp L) Ω := W.resP L Ω g
  obtain ⟨w, A, p, σ', -, hp, hpM, -, hpw, hnorm, -, hA, hIne, hFrob, hσU⟩ :=
    Loc.v00 U hOU g' ∅ M' hM'
  have hg'1 : g' ∈ U1 := hg
  have hg'3 : g' ∈ U3 := (k.mem_range_resP g').1 ⟨g, rfl⟩
  have hσeq : σ' = g' * (σ'⁻¹ * g')⁻¹ := by group
  have hσ1 : σ' ∈ U1 := by
    rw [hσeq]
    exact U1.mul_mem hg'1 (U1.inv_mem hσU.1.1)
  have hσ3 : σ' ∈ U3 := by
    rw [hσeq]
    exact U3.mul_mem hg'3 (U3.inv_mem hσU.2)
  have hσ2 : σ' ∉ U2 := by
    intro h
    have h2 := U2.mul_mem h hσU.1.2
    rw [mul_inv_cancel_left] at h2
    exact hc ((hU2 g').1 h2)
  let H : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U3
  have hOH : IsOpen (H : Set (G (W.Lp L) Ω)) := hO1.inter hO3
  have hIH : Ine A ≤ H := fun τ hτ => ⟨(hIne hτ).1.1, (hIne hτ).2⟩
  have hFrob' : IsFrob A (normV w) σ' := by
    rw [hnorm]
    exact hFrob
  have hDec : (Dec A : Subgroup (G (W.Lp L) Ω)) ≤ H :=
    Kum.decGen (W.Lp L) Ω A w σ' H hA hFrob' hOH hIH ⟨hσ1, hσ3⟩
  refine ⟨w, A, p, hp, hpM, hnorm, hpw, hA, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (k.mem_range_resP τ).2 (hDec hτ).2
  · intro t ht
    have ht' : W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω)) := ht
    exact (hDec ht').1
  · obtain ⟨t, ht⟩ := (k.mem_range_resP σ').2 hσ3
    refine ⟨t, ?_, ?_⟩
    · change W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω))
      rw [ht]
      exact hFrob.1
    · change PadicInt.toZMod (cycZ (W.Lp L) Ω l (W.resP L Ω t) : ℤ_[l]) ≠ 1
      rw [ht]
      exact fun h => hσ2 ((hU2 σ').2 h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionGaloisEquivariance
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem val_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) (A : ValuationSubring Ω) (x : Ω) :
    (g • A).valuation (g x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ y : Ω, g.toRingEquiv y ∈ g • A ↔ y ∈ A := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).1 hy
      have hzy' : g z = g y := hzy
      rw [g.injective hzy'] at hz
      exact hz
    · intro hy
      exact ValuationSubring.smul_mem_pointwise_smul g y A hy
  exact val_lt_one key x

open scoped Pointwise in
private theorem place_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) : IsPlaceOver (g • A) v := by
  intro x
  have hx : g ((algebraMap F Ω) (x : F)) = (algebraMap F Ω) (x : F) := g.commutes _
  rw [← hx, val_smul]
  exact h x

open scoped Pointwise in
theorem UpperTheory.frame_criterion_galois_equivariance :
    UpperTheory.V.Pr.CrE := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hB
  have hsm : ∀ (τ : G (W.Lp L) Ω) (X : ValuationSubring Ω),
      τ • X = ((toUpl Ω L τ : upl Ω L) : Gal(Ω/ℚ)) • X := by
    intro τ X
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : ((toUpl Ω L τ : upl Ω L) : Gal(Ω/ℚ))⁻¹ = ((toUpl Ω L τ⁻¹ : upl Ω L) : Gal(Ω/ℚ)) := by
      rw [map_inv]
      rfl
    rw [hinv]
    rfl
  have hpl : ∀ w : Φ.V, (k.pl w).valuation (l : Ω) < 1 := by
    intro w
    obtain ⟨γ, -, hγ⟩ := k.pl_conj w
    have h1 := (val_smul γ B (l : Ω)).2 hB
    rw [map_natCast] at h1
    rw [hγ]
    exact h1
  have hpick : ∀ v : W.Vl l L, ∃ w : Φ.V, IsPlaceOver (k.pl w) (v : W.Plc (W.Lp L)) := by
    intro v
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (v : W.Plc (W.Lp L))
    have hlA : A.valuation (l : Ω) < 1 := by
      rw [natCast_place hA]
      exact v.2
    obtain ⟨w, ⟨u, hu, hAu⟩, -⟩ := k.pl_all A hlA
    obtain ⟨g, hg⟩ := toUpl_surj (Ω := Ω) (L := L) (⟨u, hu⟩⁻¹)
    refine ⟨w, ?_⟩
    have heq : g • A = k.pl w := by
      rw [hsm, hg, hAu]
      change u⁻¹ • u • k.pl w = k.pl w
      rw [inv_smul_smul]
    rw [← heq]
    exact place_smul g hA
  choose e he using hpick
  have hinj : Function.Injective e := by
    intro v v' hvv
    have h2 := he v'
    rw [← hvv] at h2
    exact Subtype.ext (eq_of_isPlaceOver (he v) h2)
  have hsurj : Function.Surjective e := by
    intro w
    have hfacts := places (W.Lp L) Ω l (k.pl w)
    have hne : k.pl w ≠ ⊤ := by
      intro htop
      exact (hfacts.2.1 htop).2 (hpl w)
    obtain ⟨v0, hv0⟩ := hfacts.1 hne
    have hl0 : ((l : 𝓞 (W.Lp L))) ∈ v0.asIdeal := (natCast_place hv0 l).1 (hpl w)
    let v : W.Vl l L := ⟨v0, hl0⟩
    refine ⟨v, ?_⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (he v) hv0
    obtain ⟨w', -, huniq⟩ := k.pl_all (k.pl w) (hpl w)
    have hw : w = w' := huniq w ⟨1, one_mem _, (one_smul _ _).symm⟩
    have hev : e v = w' := huniq (e v) ⟨_, (toUpl Ω L τ).2, by rw [← hsm, hτ]⟩
    rw [hw, hev]
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, he⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionKernel
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : W.Plc k} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hlift : IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hmem : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨σ, fun τ hτ => ?_⟩
  have h1 := conjGal_mem_Ine hlift hmem hτ
  have heq : conjGal hlift τ = σ⁻¹ * τ * σ := AlgEquiv.ext fun x => rfl
  rw [← heq]
  exact h1

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (W.Plc k)} {A : ValuationSubring Ω} {v : W.Plc k} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem normal_map {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (N : Subgroup F.G₀) (hN : N.Normal)
    (hc : ∀ g ∈ N, F.conj g ∈ N) : (N.map F.η.ker.subtype).Normal := by
  constructor
  rintro _ ⟨m, hm, rfl⟩ γ
  by_cases hγ : F.η γ = 1
  · exact ⟨⟨γ, hγ⟩ * m * (⟨γ, hγ⟩ : F.G₀)⁻¹, hN.conj_mem m hm _, rfl⟩
  · have hγ' : F.η γ = -1 := (Int.units_eq_one_or _).resolve_left hγ
    have h0 : F.η (F.c⁻¹ * γ) = 1 := by
      rw [map_mul, map_inv, F.η_c, hγ']
      simp
    let γ0 : F.G₀ := ⟨F.c⁻¹ * γ, h0⟩
    refine ⟨F.conj (γ0 * m * γ0⁻¹), hc _ (hN.conj_mem m hm γ0), ?_⟩
    show F.c * (F.c⁻¹ * γ * (m : F.Γ) * (F.c⁻¹ * γ)⁻¹) * F.c⁻¹ = γ * (m : F.Γ) * γ⁻¹
    group

theorem UpperTheory.frame_criterion_kernel :
    UpperTheory.V.Pr.CrKer := by
  unfold UpperTheory.V.Pr.CrKer
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS π hπ N hN hNc hNconj hIu hI0
  let N' : Subgroup V.frame.Γ := N.map V.frame.η.ker.subtype
  haveI hN'n : N'.Normal := normal_map V.frame N hN hNconj
  have hG0c : IsClosed (V.frame.η.ker : Set V.frame.Γ) :=
    Subgroup.isClosed_of_isOpen _ V.frame.η_open
  have hN'c : IsClosed (N' : Set V.frame.Γ) := by
    rw [Subgroup.coe_map]
    exact hG0c.isClosedEmbedding_subtypeVal.isClosedMap _ hNc
  let K : Subgroup (G (W.Lp L) Ω) := N'.comap (toGS Ω V.S')
  have hKc : IsClosed (K : Set (G (W.Lp L) Ω)) := hN'c.preimage (continuous_toGS Ω V.S')
  haveI hKn : K.Normal := hN'n.comap _
  let Kup : Subgroup (upl Ω L) := K.map (toUpl Ω L)
  haveI hKupn : Kup.Normal := hKn.map _ toUpl_surj
  have hind : Topology.IsInducing (toUpl Ω L) :=
    (Topology.IsInducing.subtypeVal.of_comp_iff).1 (galEmbTop ℚ (W.Lp L) Ω).1.isInducing
  have hKupc : IsClosed (Kup : Set (upl Ω L)) := by
    obtain ⟨t, ht, hpre⟩ := hind.isClosed_iff.1 hKc
    rw [Subgroup.coe_map, ← hpre, Set.image_preimage_eq t toUpl_surj]
    exact ht
  have hgen : ∀ u : upl Ω L, ∀ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 →
      (u : G ℚ Ω) ∈ Ine B' → barChar O Ψ (u : G ℚ Ω) = 1 → u ∈ Kup := by
    intro u B' hl hIne hbar
    obtain ⟨τ, hτ⟩ := toUpl_surj (Ω := Ω) (L := L) u
    refine ⟨τ, ?_, hτ⟩
    have hτI : τ ∈ Ine (F := W.Lp L) B' := by
      rw [← hτ] at hIne
      exact hIne
    by_cases htop : B' = ⊤
    · have hbot := ((places (W.Lp L) Ω l B').2.1 htop).1
      rw [hbot] at hτI
      rw [Subgroup.mem_bot.1 hτI]
      exact K.one_mem
    obtain ⟨v, hv⟩ := (places (W.Lp L) Ω l B').1 htop
    by_cases hvS : v ∈ V.S'
    · have hvS' : v ∈ s.S := hS ▸ hvS
      obtain ⟨h, hh⟩ := conj_ine (s.hA v) hv
      have hτ' := hh τ hτI
      obtain ⟨t, ht⟩ := s.unr (s.A v) v (s.hA v) hτ'
      have htI : t ∈ Ine (F := L) (s.A v) := by
        have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) (s.A v) := by
          rw [ht]
          exact hτ'
        exact h1
      have hprN : V.pr t ∈ N := by
        rcases hvS' with hlv | hvSt | hv0
        · exfalso
          exact hl ((natCast_place hv l).2 hlv)
        · apply hIu ⟨v, hvSt⟩ (V.pr t) ⟨t, htI, rfl⟩
          rw [hπ t, k.galois_link_projection_coe, k.psi]
          change barChar O Ψ (galEmb ℚ (W.Lp L) Ω (W.resP L Ω t)) = 1
          rw [ht, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
            mul_comm ((barChar O Ψ) ((galEmb ℚ (W.Lp L) Ω) h))⁻¹ _, inv_mul_cancel_right]
          have hu : (galEmb ℚ (W.Lp L) Ω) τ = (u : G ℚ Ω) := by
            rw [← hτ]
            rfl
          rw [hu]
          exact hbar
        · apply hI0
          subst hv0
          exact ⟨t, htI, rfl⟩
      have hτ'N : toGS Ω V.S' (h⁻¹ * τ * h) ∈ N' := by
        refine ⟨V.pr t, hprN, ?_⟩
        change toGS Ω V.S' (W.resP L Ω t) = _
        rw [ht]
      have hconj := hN'n.conj_mem _ hτ'N (toGS Ω V.S' h)
      have heq : toGS Ω V.S' h * toGS Ω V.S' (h⁻¹ * τ * h) * (toGS Ω V.S' h)⁻¹ = toGS Ω V.S' τ := by
        simp only [map_mul, map_inv]
        group
      change toGS Ω V.S' τ ∈ N'
      rw [← heq]
      exact hconj
    · change toGS Ω V.S' τ ∈ N'
      rw [ine_NS hvS hv hτI]
      exact N'.one_mem
  have hpker : k.p.ker ≤ Kup := by
    rw [k.p_ker]
    apply Subgroup.topologicalClosure_minimal _ _ hKupc
    apply Subgroup.normalClosure_le_normal
    rintro u ⟨B', hl, hIne, -, hbar⟩
    exact hgen u B' hl hIne hbar
  intro g0 hg0
  obtain ⟨g, rfl⟩ := pr_surj V g0
  have hp0 : k.p0 g = 1 := by
    rw [← hπ g]
    exact hg0
  have hpk : toUpl Ω L (W.resP L Ω g) ∈ k.p.ker := by
    rw [MonoidHom.mem_ker, ← k.galois_link_projection_coe, hp0]
    rfl
  obtain ⟨τ, hτK, hτeq⟩ := hpker hpk
  have hτg : τ = W.resP L Ω g := toUpl_inj hτeq
  obtain ⟨m, hm, hmeq⟩ := hτK
  have hpr : V.pr g = m := by
    apply Subtype.ext
    change toGS Ω V.S' (W.resP L Ω g) = (m : V.frame.Γ)
    rw [← hτg]
    exact hmeq.symm
  rw [hpr]
  exact hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionLambdaCharacters
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_lambda_characters :
    UpperTheory.V.Pr.CrLam := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k v A hA hM
  haveI := Φ.cv v
  haveI := Φ.t2v v
  obtain ⟨hemb, -, -⟩ := galEmbTop ℚ L Ω
  let e1 : Dec (F := L) A →* G ℚ Ω := (galEmb ℚ L Ω).comp (Dec (F := L) A).subtype
  let e2 : Φ.Gv v →* G ℚ Ω := (upl Ω L).subtype.comp (k.j v)
  have he1 : Function.Injective e1 := hemb.injective.comp Subtype.val_injective
  have he2 : Function.Injective e2 := Subtype.val_injective.comp (k.j_inj v)
  have hrange : e1.range = e2.range := by
    ext τ
    constructor
    · rintro ⟨g, rfl⟩
      have hup : e1 g ∈ upl Ω L := by
        have := galEmb_mem ℚ L Ω (g : G L Ω)
        rw [k.gal] at this
        exact this.1
      have hdec : e1 g ∈ Dec (F := ℚ) (k.pl v) := by
        show galEmb ℚ L Ω g ∈ _
        rw [← hA, galEmb_mem_Dec]
        exact g.2
      obtain ⟨x, hx⟩ := (k.j_range v ⟨_, hup⟩).2 hdec
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      have hdec : e2 x ∈ Dec (F := ℚ) A := by
        rw [hA]
        exact (k.j_range v (k.j v x)).1 ⟨x, rfl⟩
      have hup : e2 x ∈ upl Ω L := (k.j v x).2
      have hker : e2 x ∈ η.ker := k.split A hM ⟨hdec, hup⟩
      have hfix : e2 x ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨hup, hker⟩
      let g : G L Ω := AlgEquiv.ofRingEquiv (f := (e2 x).toRingEquiv) (fun y => hfix y)
      have hg : galEmb ℚ L Ω g = e2 x := by
        ext y
        rfl
      have hgd : g ∈ Dec (F := L) A := by
        rw [← galEmb_mem_Dec (k := ℚ), hg]
        exact hdec
      exact ⟨⟨g, hgd⟩, hg⟩
  let m : Dec (F := L) A ≃* Φ.Gv v :=
    (MonoidHom.ofInjective he1).trans ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective he2).symm)
  have hm : ∀ g, e2 (m g) = e1 g := by
    intro g
    have := MonoidHom.ofInjective_apply he2 (x := m g)
    rw [← this, ← MonoidHom.ofInjective_apply he1 (x := g)]
    simp [m]
  have hinv : Continuous m.symm := by
    have hcomp : e1 ∘ m.symm = e2 := by
      funext x
      rw [Function.comp_apply, ← hm, MulEquiv.apply_symm_apply]
    have he1emb : Topology.IsEmbedding e1 := hemb.comp Topology.IsEmbedding.subtypeVal
    rw [he1emb.continuous_iff, hcomp]
    exact continuous_subtype_val.comp (k.j_cont v)
  have hfwd : Continuous m := by
    have := hinv.continuous_symm_of_equiv_compact_to_t2 (f := m.symm.toEquiv)
    simpa using this
  refine ⟨{ m with continuous_toFun := hfwd, continuous_invFun := hinv }, fun g => ?_⟩
  exact hm g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionProjection
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_projection :
    UpperTheory.V.Pr.CrPi := by
  unfold UpperTheory.V.Pr.CrPi
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS
  have hup : Continuous (toUpl Ω L) := by
    unfold UpperTheory.V.Pr.toUpl
    exact (continuous_restrictScalarsHom ℚ (W.Lp L) Ω).subtype_mk _
  let f : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hf : Continuous f := k.p_cont.comp hup
  have hclosed : IsClosed (f.ker : Set (G (W.Lp L) Ω)) := by
    have h := (isClosed_singleton (x := (1 : Φ.Γ))).preimage hf
    exact h
  have hNS : NS Ω V.S' ≤ f.ker := by
    unfold ReciprocityTheory.Gal.NS
    apply Subgroup.topologicalClosure_minimal _ _ hclosed
    apply Subgroup.normalClosure_le_normal
    intro t ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at ht
    obtain ⟨v, hv, A, hA, ht⟩ := ht
    rw [hS] at hv
    unfold UpperTheory.V.W.HidaSetting.S at hv
    simp only [Set.mem_setOf_eq, not_or] at hv
    obtain ⟨hl, hSt, -⟩ := hv
    have hMv := fun hM => hSt ((x.St v).2 ⟨hM, hl⟩)
    have hti : galEmb ℚ (W.Lp L) Ω t ∈ Ine A := (galEmb_mem_Ine A t).2 ht
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show k.p (toUpl Ω L t) = 1
    rw [← MonoidHom.mem_ker, k.p_ker]
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    refine ⟨A, ?_, hti, ?_, ?_⟩
    · rw [natCast_place hA]
      exact hl
    · exact k.unr A ⟨hti, (toUpl Ω L t).2⟩
    · have hΨ : Ψ (galEmb ℚ (W.Lp L) Ω t) = 1 :=
        x.unr A (by rw [natCast_place hA]; exact hMv) hti
      unfold barChar
      show Units.map _ (Ψ (galEmb ℚ (W.Lp L) Ω t)) = 1
      rw [hΨ, map_one]
  let πt : GS Ω V.S' →* Φ.Γ := QuotientGroup.lift (NS Ω V.S') f hNS
  have hπt : ∀ t, πt (toGS Ω V.S' t) = f t := fun t => rfl
  have hπtc : Continuous πt := continuous_coinduced_dom.2 hf
  have hmem : ∀ y : V.η.ker, πt y.1 ∈ Φ.del.ker := by
    intro y
    obtain ⟨g, hg⟩ := pr_surj V y
    rw [← hg]
    exact (k.p0 g).2
  let π : V.η.ker →* Φ.del.ker := (πt.comp V.η.ker.subtype).codRestrict _ hmem
  have hcs : f s.c = Φ.c := by
    obtain ⟨h, hpc⟩ := k.c
    have h2 : toUpl Ω L s.c = ⟨σ, h⟩ := Subtype.ext x.c
    show k.p (toUpl Ω L s.c) = Φ.c
    rw [h2, hpc]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · exact (hπtc.comp continuous_subtype_val).subtype_mk _
  · intro g
    rfl
  · intro y0
    let y : V.η.ker := y0
    apply Subtype.ext
    show πt (toGS Ω V.S' s.c * y.1 * (toGS Ω V.S' s.c)⁻¹) = Φ.c * πt y.1 * Φ.c⁻¹
    rw [map_mul, map_mul, map_inv, hπt, hcs]
  · intro y0
    let y : V.η.ker := y0
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y.1
    show Φ.eps (πt y.1) = V.ε y.1
    have ht' : toGS Ω V.S' t = y.1 := ht
    rw [← ht', hπt]
    show Φ.eps (k.p (toUpl Ω L t)) = V.ε (toGS Ω V.S' t)
    rw [k.eps, ← MonoidHom.comp_apply V.ε, V.hε]
    rfl
end

