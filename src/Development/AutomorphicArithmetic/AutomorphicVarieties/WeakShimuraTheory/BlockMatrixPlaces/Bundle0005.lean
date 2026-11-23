module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UrCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.gwCount :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → (∀ m, ρ c m = -m) → (Function.Bijective fun m => ρ s m - m) →
          ∀ P : Submodule R M, (∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P, ρ h x ∈ P) → Nat.card P ≤ Nat.card (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := by
  classical
  intro hC Ω _ _ _ l hl S c s B hP R M _ _ _ _ ρ r hr hlc K hK hun hc hs P hPs
  have hfin := zcFin hC.gf S c s B hP R M ρ r hr hlc K hK hun (P : Set M)
  haveI : Finite (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := hfin
  obtain ⟨S', Av, v0, hS', hAv, hB, hv0, hNS⟩ := placeSet (l := l) S B hP.prime hP.mem hP.ovl
  subst hB
  have hr1 : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr1
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hcl : IsClosed (ρ.ker : Set (G ℚ Ω)) := by
    have e : (ρ.ker : Set (G ℚ Ω)) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isClosed_iInter fun m => ((hlc m).isClopen_fiber m).1
  have hN := hNS ρ.ker inferInstance hcl fun A hA => (hun A hA).trans hK
  let ρ1 : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  let σ : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ1 fun g hg => LinearMap.ext fun m => show ρ g m = m by
      rw [show ρ g = 1 from hN hg]; rfl
  have hσ : ∀ g m, σ (toGS Ω _ g) m = ρ g m := fun _ _ => rfl
  have hcont : ContAction σ := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hlc m).continuous
  have hloc : ∀ v, ContAction (σ.comp (locFam S' Av v)) := fun v =>
    Continuous.comp (f := fun p : Dec (F := ℚ) (Av v) × M => (locFam S' Av v p.1, p.2)) hcont
      (((continuous_locFam S' Av v).comp continuous_fst).prodMk continuous_snd)
  let P' : Submodule (ZMod (l ^ (r + 1))) M := AddSubgroup.toZModSubmodule _ P.toAddSubgroup
  obtain ⟨L0, hL0, hL0'⟩ := plusCard hC.loc.lf hC.loc.le (r + 1) M (Av v0) v0.1 (σ.comp (locFam S' Av v0))
    r.succ_pos (hAv v0) hv0 (hloc v0) P' (fun h x hx => hPs h.1 h.2 x hx) ⟨⟨s, hP.dec⟩, hs⟩
  let L : LocCond σ (locFam S' Av) := Function.update
    (fun v => H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) v0 L0
  have hLv0 : L v0 = L0 := Function.update_self ..
  have hLv : ∀ v, v ≠ v0 →
      L v = H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v))) :=
    fun v hv => Function.update_of_ne hv ..
  have h1 := gwIneq hC.gf hC.gw (r + 1) M S' σ r.succ_pos hP.odd hS' hcont c hP.cc hc Av hAv v0 s hP.dec hP.cyc hs L
    fun v hv => by
      obtain ⟨φ, -, h1, h2⟩ := GC.decZhat ℚ Ω v.1 (Av v) (hAv v)
      rw [hLv v hv, urCard _ _ _ _ (hloc v) _ φ h1 h2]
  have h2 : Function.Bijective fun m : M => m + m := by
    refine Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero (AddMonoidHom.id M + AddMonoidHom.id M)).2 ?_)
    intro m hm
    have hm2 : 2 • m = 0 := by rw [two_smul]; exact hm
    have hco : Nat.Coprime 2 (l ^ r) :=
      ((Nat.coprime_primes Nat.prime_two hl.out).2 hP.odd.symm).pow_right _
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm2) (addOrderOf_dvd_of_nsmul_eq_zero (hr m))
    rw [hco.gcd_eq_one, Nat.dvd_one] at this
    exact AddMonoid.addOrderOf_eq_one_iff.1 this
  obtain ⟨f, hf⟩ := selToZc (l := l) _ M S' σ hcont h2 c hc Av hAv v0 hv0 (P : Set M) K
    (fun g hg m => show ρ g m = m by rw [show ρ g = 1 from hK hg]; rfl) L (fun v hv => (hLv v hv).le)
    (fun z hz => hL0' z (hLv0 ▸ hz))
  rw [hLv0] at h1
  exact hL0.trans (h1.trans (Nat.card_le_card_of_injective f hf))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UpSupUp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

end UpperTheory.V.Ws.Bl

private theorem mem_ideal_smul_module_of_entries_mem {A : Type} [CommRing A] (I : Ideal A) (Y : uM A)
    (hY : ∀ i j, (Y : M4 A) i j ∈ I) : Y ∈ I • (⊤ : Submodule A (uM A)) := by
  have h1 : (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,-1,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h2 : (!![0,0,0,0; 0,0,1,0; 0,0,0,0; 0,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h3 : (!![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  obtain ⟨hz, ha⟩ := Y.2
  have h32 : (Y : M4 A) 3 2 = -(Y : M4 A) 1 0 := by
    have h := congrFun (congrFun ha 3) 2
    simp [adj, sgn] at h
    rw [h, neg_neg]
  have hd : Y = (Y : M4 A) 1 0 • (⟨_, h1⟩ : uM A) + (Y : M4 A) 1 2 • (⟨_, h2⟩ : uM A)
      + (Y : M4 A) 3 0 • (⟨_, h3⟩ : uM A) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h32] <;> exact hz _ _ (by decide)
  rw [hd]
  exact add_mem (add_mem (Submodule.smul_mem_smul (hY 1 0) trivial)
    (Submodule.smul_mem_smul (hY 1 2) trivial)) (Submodule.smul_mem_smul (hY 3 0) trivial)

private theorem isLocallyConstant_mkQ_adU_of_adicCont {A : Type} [CommRing A] [IsLocalRing A] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [ContinuousInv Γ] (r : Γ →* M4 A) (hb : BG r)
    (hc : ∀ i j, AdicCont (maximalIdeal A) fun g => r g i j) (n : ℕ) (x : uM A) :
    IsLocallyConstant fun g => (lev A (uM A) n).mkQ ((adU hb g) x) := by
  let φ := (Ideal.Quotient.mk (maximalIdeal A ^ n)).mapMatrix (m := Fin 4)
  have hq : ∀ (f : Γ → M4 A), (∀ i j, AdicCont (maximalIdeal A) fun g => f g i j) →
      IsLocallyConstant fun g => φ (f g) := by
    intro f hf
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro M
    have hM : (fun g => φ (f g)) ⁻¹' {M} =
        ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) (f g i j)) ⁻¹' {M i j} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro h i j
        rw [← h]
        rfl
      · intro h
        ext i j
        exact h i j
    rw [hM]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j n).isOpen_fiber _
  have hP : IsLocallyConstant fun g => (φ (r g), φ (r g⁻¹)) :=
    (hq _ hc).prodMk (hq (fun g => r g⁻¹) fun i j N => (hc i j N).comp_continuous continuous_inv)
  have key : ∀ g' g : Γ, (φ (r g'), φ (r g'⁻¹)) = (φ (r g), φ (r g⁻¹)) →
      (lev A (uM A) n).mkQ ((adU hb g') x) = (lev A (uM A) n).mkQ ((adU hb g) x) := by
    intro g' g hgg
    obtain ⟨e1, e2⟩ := Prod.mk.inj hgg
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply mem_ideal_smul_module_of_entries_mem
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h0 : φ ((↑((adU hb g') x - (adU hb g) x) : M4 A)) = 0 := by
      rw [Submodule.coe_sub]
      change φ (r g' * (x : M4 A) * r g'⁻¹ - r g * (x : M4 A) * r g⁻¹) = 0
      simp only [map_sub, map_mul, e1, e2, sub_self]
    simpa [φ] using congrFun (congrFun h0 i) j
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have hy : (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y} =
      ⋃ g ∈ (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y},
        (fun g => (φ (r g), φ (r g⁻¹))) ⁻¹' {(φ (r g), φ (r g⁻¹))} := by
    ext g'
    constructor
    · intro h
      exact Set.mem_biUnion h rfl
    · intro h
      obtain ⟨g, hg, hgg⟩ := Set.mem_iUnion₂.1 h
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg hgg ⊢
      rw [← hg]
      exact key g' g hgg
  rw [hy]
  exact isOpen_biUnion fun g _ => hP.isOpen_fiber _

private theorem isSUp_mul_mul_of_isUp_isSUp_isUp {A : Type} [CommRing A] (P N Q : M4 A) (hP : IsUp P) (hN : IsSUp N)
    (hQ : IsUp Q) : IsSUp (P * N * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hli : l < i
  · rw [hP i l hli, zero_mul, zero_mul]
  by_cases hkl : k ≤ l
  · rw [hN l k hkl, mul_zero, zero_mul]
  rw [hQ k j (by omega), mul_zero]

theorem UpperTheory.V.Ws.Bl.latU :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (r : G ℚ Ω →* M4 A) (u : M4 A) (h : BlockDiagonalOrdinaryGSpRep S c s B r u),
          Lat (adU h.bg) (Dec (F := ℚ) B) (uPlus u) ∧ (∀ Y, adU h.bg c Y = -Y) ∧ r.ker ≤ (adU h.bg).ker := by
  intro Ω _ _ _ l _ S c s B hp A _ _ _ r u h
  have hinv : ∀ g, r g = 1 → r g⁻¹ = 1 := by
    intro g hg
    calc r g⁻¹ = r g⁻¹ * r g := by rw [hg, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have huu : u * adj u = 1 := by
    have h1 : adj u * u = 1 := by
      have := h.sp
      simpa [IsGSp] using this
    exact mul_eq_one_comm.1 h1
  refine ⟨⟨fun n x => isLocallyConstant_mkQ_adU_of_adicCont r h.bg h.cont n x, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg Y hY
    have hg' : g⁻¹ ∈ Dec (F := ℚ) B := (Dec (F := ℚ) B).inv_mem hg
    change IsSUp (adj u * (r g * (Y : M4 A) * r g⁻¹) * u)
    have he : adj u * (r g * (Y : M4 A) * r g⁻¹) * u
        = (adj u * r g * u) * (adj u * (Y : M4 A) * u) * (adj u * r g⁻¹ * u) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc u (adj u), huu, Matrix.one_mul, ← Matrix.mul_assoc u (adj u), huu,
        Matrix.one_mul]
    rw [he]
    exact isSUp_mul_mul_of_isUp_isSUp_isUp _ _ _ (h.flag g hg) hY (h.flag _ hg')
  · intro a Y ha hY
    change IsSUp (adj u * ((a • Y : uM A) : M4 A) * u) at hY
    change IsSUp (adj u * (Y : M4 A) * u)
    intro i j hij
    have h0 := hY i j hij
    rw [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left ha
  · exact flagVec A (r s) u (h.bg.blk s) h.sep h.sp (h.flag s hp.dec) h.char
  · exact ⟨s, hp.dec, adBij A (G ℚ Ω) r h.bg s h.sep⟩
  · intro Y
    have hc2 : r c * r c = 1 := by
      rw [h.cc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [eAB]
    have hci : r c⁻¹ = r c := by
      calc r c⁻¹ = r c⁻¹ * (r c * r c) := by rw [hc2, Matrix.mul_one]
        _ = r (c⁻¹ * c) * r c := by rw [map_mul, Matrix.mul_assoc]
        _ = r c := by rw [inv_mul_cancel, map_one, Matrix.one_mul]
    obtain ⟨hz, _⟩ := Y.2
    apply Subtype.ext
    change r c * (Y : M4 A) * r c⁻¹ = -(Y : M4 A)
    rw [hci, h.cc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eAB, hz 0 0 (by decide), hz 0 1 (by decide), hz 0 2 (by decide), hz 0 3 (by decide),
        hz 1 1 (by decide), hz 1 3 (by decide), hz 2 0 (by decide), hz 2 1 (by decide),
        hz 2 2 (by decide), hz 2 3 (by decide), hz 3 1 (by decide), hz 3 3 (by decide)]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    change r g * (Y : M4 A) * r g⁻¹ = (Y : M4 A)
    rw [hg, hinv g hg, Matrix.one_mul, Matrix.mul_one]
end

