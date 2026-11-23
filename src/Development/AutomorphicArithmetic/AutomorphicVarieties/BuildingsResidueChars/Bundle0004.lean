module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NnDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPinningElementsOfLocAb
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

section
open UpperTheory.V.W

end

private theorem exists_pow_l_pow_eq_one_of_mem_muG {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : G →* Rˣ) (hψc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R))
    (g : G) (hg : g ∈ UpperTheory.V.W.muG l G) : ∃ n : ℕ, ψ g ^ (l ^ n) = 1 := by
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.1 hg
  refine ⟨n, ?_⟩
  have h1 : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hn
  have hker : (commutator G).topologicalClosure ≤ ψ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker ψ)
      (isClosed_ker_of_adicCont ψ hψc)
  rw [← map_pow]
  exact hker h1

theorem UpperTheory.exists_pinning_elements_of_locAb :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G) (d : ℕ), UpperTheory.V.W.LocAb l G I d → ∃ s : Fin d → G, (∀ k, s k ∈ I) ∧ Pins l I (Set.range s) := by
  intro l _ G _ _ _ _ I d A
  have hlp : l.Prime := Fact.out
  have hs : ∀ k : Fin d, ∃ g ∈ I,
      A.a g = Multiplicative.ofAdd ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) :=
    fun k => (A.inertia _).2 rfl
  choose s hsI hsa using hs
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ hl ψ hψc hψI hψs g hg
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hlp).2 hl
  have hsk : ∀ k, ψ (s k) = 1 := fun k => hψs _ ⟨k, rfl⟩
  have hq : ∀ (N : ℕ) (u : Rˣ),
      Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N) u = 1 ↔
        (u : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N u
    rw [Units.ext_iff]
    show Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) = 1 ↔ _
    rw [← map_one (Ideal.Quotient.mk (maximalIdeal R ^ N)), Ideal.Quotient.eq]
  let ρN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N =>
    (Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N)).comp ψ
  have hloc : ∀ N, IsLocallyConstant (ρN N) := fun N => (adicCont_units _ _).1 hψc N
  haveI hfin1 : Finite (ρN 1).range := (hloc 1).range_finite.to_subtype
  set M := Nat.card (ρN 1).range with hMdef
  have hM0 : M ≠ 0 := Nat.card_pos.ne'
  have hres : ∀ g, ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro g
    have h1 := congrArg (fun u : (ρN 1).range => (u : (R ⧸ maximalIdeal R ^ 1)ˣ))
      (pow_card_eq_one' (G := (ρN 1).range) (x := ⟨ρN 1 g, g, rfl⟩))
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← hMdef] at h1
    rw [← map_pow] at h1
    simpa using (hq 1 _).1 h1
  have hmu : ∀ g ∈ UpperTheory.V.W.muG l G, ψ g ^ M = 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := exists_pow_l_pow_eq_one_of_mem_muG ψ hψc g hg
    apply Units.ext
    refine eq_one_of_pow hl (hres g) (pow_ne_zero n hlp.ne_zero) ?_
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hn, one_pow, Units.val_one]
  let φN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N => (powMonoidHom M).comp (ρN N)
  have hφloc : ∀ N, IsLocallyConstant (φN N) := fun N => (hloc N).comp (fun u => u ^ M)
  have hφ : ∀ N g, φN N g = 1 ↔ ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N g
    rw [← hq]
    rw [map_pow]
    exact Iff.rfl
  have hφp : ∀ N g, (φN N g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, hφ]
    set y := ((ψ g ^ M : Rˣ) : R) - 1 with hy
    have hym : y ∈ maximalIdeal R := hres g
    have : (((ψ g ^ M) ^ (l ^ N) : Rˣ) : R) = 1 + y ^ (l ^ N) := by
      rw [Units.val_pow_eq_pow_val, show ((ψ g ^ M : Rˣ) : R) = 1 + y by rw [hy]; ring,
        add_pow_char_pow, one_pow]
    rw [map_pow, ← pow_mul, mul_comm (l ^ N) M, pow_mul, this, add_sub_cancel_left]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hlp.one_lt).le (Ideal.pow_mem_pow hym _)
  have hK : ∀ N, A.a.ker ≤ (φN N).ker := by
    intro N
    haveI : Finite (φN N).range := (hφloc N).range_finite.to_subtype
    have hP : IsPGroup l (φN N).range := by
      rintro ⟨x, g, rfl⟩
      exact ⟨N, Subtype.ext (hφp N g)⟩
    have := A.univ (φN N).range hP (φN N).rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact (hφloc N).isOpen_fiber 1)
      (by
        intro g hg
        rw [MonoidHom.ker_rangeRestrict]
        exact (hφ N g).2 (by rw [hmu g hg, Units.val_one, sub_self]; exact zero_mem _))
    rwa [MonoidHom.ker_rangeRestrict] at this
  have hclosed : ∀ N, IsClosed ((Subgroup.map A.a (φN N).ker : Subgroup _) :
      Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))) := by
    intro N
    rw [Subgroup.coe_map]
    exact (((hφloc N).isClosed_fiber 1).isCompact.image A.cont).isClosed
  have hmem : ∀ N (x : Fin d → ℤ_[l]),
      Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker := by
    intro N
    have hint : ∀ z : Fin d → ℤ, Multiplicative.ofAdd ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) ∈
        Subgroup.map A.a (φN N).ker := by
      intro z
      have he : ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) =
          ∑ k, z k • ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) := by
        refine Prod.ext ?_ ?_
        · funext j
          rw [Prod.fst_sum, Finset.sum_apply]
          simp [Pi.single_apply]
        · rw [Prod.snd_sum]
          simp
      rw [he, ofAdd_sum]
      refine Subgroup.prod_mem _ fun k _ => ?_
      rw [ofAdd_zsmul]
      refine Subgroup.zpow_mem _ ?_ _
      refine ⟨s k, ?_, hsa k⟩
      exact (hφ N (s k)).2 (by rw [hsk, one_pow, Units.val_one, sub_self]; exact zero_mem _)
    have hT : IsClosed {x : Fin d → ℤ_[l] |
        Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker} :=
      (hclosed N).preimage (continuous_ofAdd.comp (continuous_id.prodMk continuous_const))
    have hD : DenseRange (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l])) :=
      DenseRange.piMap fun _ => PadicInt.denseRange_intCast
    intro x
    have hx : x ∈ closure (Set.range (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l]))) := by
      rw [hD.closure_eq]
      exact Set.mem_univ x
    exact hT.closure_subset_iff.2 (by rintro _ ⟨z, rfl⟩; exact hint z) hx
  have hgN : ∀ N, φN N g = 1 := by
    intro N
    obtain ⟨x, hx⟩ : ∃ x, A.a g = Multiplicative.ofAdd x := ⟨Multiplicative.toAdd (A.a g), rfl⟩
    have hx2 : x.2 = 0 := (A.inertia x).1 ⟨g, hg, hx⟩
    obtain ⟨h, hh, hah⟩ := hmem N x.1
    have hk : h⁻¹ * g ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hah, hx, inv_mul_eq_one, ← hx2]
    have := hK N hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 hh, inv_one, one_mul] at this
    exact this
  have hzero : ((ψ g ^ M : Rˣ) : R) - 1 = 0 := by
    have : ((ψ g ^ M : Rˣ) : R) - 1 ∈ ⨅ N, maximalIdeal R ^ N :=
      Ideal.mem_iInf.2 fun N => (hφ N g).1 (hgN N)
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
      Ideal.mem_bot] at this
  apply Units.ext
  refine eq_one_of_pow hl (hψI g hg) hM0 ?_
  rw [← Units.val_pow_eq_pow_val]
  exact sub_eq_zero.1 hzero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberCardFormula
section
theorem UpperTheory.orbitalFiber_card_formula : UpperTheory.V.Z.Sym.Glob.Fib.CardFib := by
  intro G _ S U U' x Ux s₀ hS hU hx
  classical
  have hmem : ∀ w : ↥(U' ⊓ S), (s₀ : G) * x * (w : G) * x⁻¹ ∈ S := by
    intro w
    have h1 := S.mul_mem s₀.2 (hS.conj_mem (w : G) (Subgroup.mem_inf.1 w.2).2 x)
    simpa [mul_assoc] using h1
  let g : ↥(U' ⊓ S) → ↥S ⧸ Ux := fun w => ((⟨_, hmem w⟩ : ↥S) : ↥S ⧸ Ux)
  have hg : ∀ w w' : ↥(U' ⊓ S), g w = g w' ↔ (w : G)⁻¹ * (w' : G) ∈ U := by
    intro w w'
    simp only [g]
    rw [QuotientGroup.eq, hx]
    have e : x⁻¹ * (((⟨_, hmem w⟩ : ↥S)⁻¹ * ⟨_, hmem w'⟩ : ↥S) : G) * x = (w : G)⁻¹ * (w' : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
  have hgT : ∀ w, g w ∈ {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} := by
    intro w
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Ux (⟨_, hmem w⟩ : ↥S)
    simp only [Set.mem_setOf_eq, g]
    rw [hk, QuotientGroup.eq]
    have hkU : x⁻¹ * ((k : ↥S) : G) * x ∈ U' := hU ((hx k).1 k.2)
    have e : ((((⟨_, hmem w⟩ : ↥S) * (k : ↥S) : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x) =
        (x⁻¹ * ((k : ↥S) : G) * x)⁻¹ * ((w : G))⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact U'.mul_mem (U'.inv_mem hkU) (U'.inv_mem (Subgroup.mem_inf.1 w.2).1)
  rw [← Nat.card_coe_set_eq]
  unfold Subgroup.relIndex Subgroup.index
  let F : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S) →
      {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} :=
    Quotient.lift (fun w => ⟨g w, hgT w⟩) (fun a b hab => Subtype.ext ((hg a b).2 (by
      have h := QuotientGroup.leftRel_apply.1 hab
      simpa [Subgroup.mem_subgroupOf] using h)))
  refine (Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h := congrArg Subtype.val hab
    change g a = g b at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using (hg a b).1 h
  · rintro ⟨s, hs⟩
    rw [Set.mem_setOf_eq] at hs
    have hwS : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ S := by
      simpa using hS.conj_mem _ (S.mul_mem (S.inv_mem s₀.2) (Quotient.out s).2) x⁻¹
    have hwU : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ U' := by
      have h1 := QuotientGroup.eq.1 hs
      have e : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x =
          ((((Quotient.out s : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x))⁻¹ := by
        group
      rw [e]
      exact U'.inv_mem h1
    refine ⟨((⟨_, Subgroup.mem_inf.2 ⟨hwU, hwS⟩⟩ : ↥(U' ⊓ S)) : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S)),
      Subtype.ext ?_⟩
    change g _ = s
    conv_rhs => rw [← QuotientGroup.out_eq' s]
    simp only [g]
    congr 1
    apply Subtype.ext
    dsimp only
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition
section
open MulAction

private theorem fib_abs {O I : Type} {P : I → Type} (F : ∀ i, P i → O) (S : ∀ i, Set (P i)) (B : Set O) (hB : B.Finite)
    (w : O → ℂ) (wi : ∀ i, P i → ℂ) (hw : ∀ o, o ∉ B → w o = 0) (hwi : ∀ i p, p ∉ S i → wi i p = 0)
    (hF : ∀ i, ∀ p ∈ S i, F i p ∈ B ∧ wi i p = w (F i p)) (hs : ∀ o ∈ B, ∃ i, ∃ p ∈ S i, F i p = o)
    (hij : ∀ i j, ∀ p ∈ S i, ∀ q ∈ S j, F i p = F j q → i = j) (hinj : ∀ i, Set.InjOn (F i) (S i)) :
    ∑ᶠ o, w o = ∑ᶠ i, ∑ᶠ p, wi i p := by
  classical
  have h1 : ∀ i, ∑ᶠ p, wi i p = ∑ᶠ o ∈ F i '' S i, w o := by
    intro i
    rw [finsum_mem_image (hinj i), finsum_mem_def]
    congr 1
    funext p
    by_cases hp : p ∈ S i
    · rw [Set.indicator_of_mem hp, (hF i p hp).2]
    · rw [Set.indicator_of_notMem hp, hwi i p hp]
  have hsub : ∀ i, F i '' S i ⊆ B := by
    rintro i _ ⟨p, hp, rfl⟩
    exact (hF i p hp).1
  have hI : {i | (S i).Nonempty}.Finite := by
    let g : {i | (S i).Nonempty} → B := fun i => ⟨F i.1 i.2.some, (hF _ _ i.2.some_mem).1⟩
    have hg : Function.Injective g := fun i j h =>
      Subtype.ext (hij _ _ _ i.2.some_mem _ j.2.some_mem (congrArg Subtype.val h))
    haveI := hB.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg)
  have hU : B = ⋃ i ∈ {i | (S i).Nonempty}, F i '' S i := by
    ext o
    simp only [Set.mem_iUnion]
    constructor
    · intro ho
      obtain ⟨i, p, hp, rfl⟩ := hs o ho
      exact ⟨i, ⟨p, hp⟩, p, hp, rfl⟩
    · rintro ⟨i, _, ho⟩
      exact hsub i ho
  have h2 : ∑ᶠ o, w o = ∑ᶠ o ∈ B, w o := by
    rw [finsum_mem_def]
    congr 1
    funext o
    by_cases ho : o ∈ B
    · rw [Set.indicator_of_mem ho]
    · rw [Set.indicator_of_notMem ho, hw o ho]
  rw [h2, hU, finsum_mem_biUnion _ hI (fun i _ => hB.subset (hsub i)), finsum_mem_def]
  · congr 1
    funext i
    by_cases hi : i ∈ {i | (S i).Nonempty}
    · rw [Set.indicator_of_mem hi, h1]
    · rw [Set.indicator_of_notMem hi, h1]
      have : S i = ∅ := Set.not_nonempty_iff_eq_empty.1 hi
      rw [this, Set.image_empty, finsum_mem_empty]
  · intro i _ j _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    exact hne (hij i j p hp q hq h.symm)

private theorem rel_smul {H X : Type} [Group H] [MulAction H X] (H₀ : Subgroup H) (hn : H₀.Normal) (h : H) (x : X) :
    H₀.relIndex (stabilizer H (h • x)) = H₀.relIndex (stabilizer H x) := by
  have h0 : H₀.map (MulAut.conj h).toMonoidHom = H₀ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hn.conj_mem y hy h
    · intro hz
      refine ⟨h⁻¹ * z * h, ?_, ?_⟩
      · simpa using hn.conj_mem z hz h⁻¹
      · simp [mul_assoc]
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← h0]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

private theorem out_mk {H X : Type} [Group H] [MulAction H X] (x : X) :
    ∃ h : H, (Quotient.mk (orbitRel H X) x).out = h • x := by
  have : (Quotient.mk (orbitRel H X) x).out ∈ orbit H x :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) x)))
  obtain ⟨h, hh⟩ := this
  exact ⟨h, hh.symm⟩

private theorem mk_smul {H X : Type} [Group H] [MulAction H X] (h : H) (x : X) :
    Quotient.mk (orbitRel H X) (h • x) = Quotient.mk (orbitRel H X) x :=
  Quotient.sound (orbitRel_apply.2 ⟨h, rfl⟩)

theorem UpperTheory.orbitalFiber_decomposition :
    UpperTheory.V.Z.Sym.Glob.Fib.Decomp := by
  intro H X I _ _ H₀ k Hi Yi _ _ φ e ki hn hk hT he hinj hki hke hs hu
  unfold UpperTheory.V.Z.Sym.gq
  have hex : ∀ x x' : X, Quotient.mk (orbitRel H X) x' = Quotient.mk (orbitRel H X) x → ∃ h : H, h • x = x' :=
    fun x x' h => orbitRel_apply.1 (Quotient.exact h)
  refine fib_abs (fun i (p : orbitRel.Quotient (Hi i) (Yi i)) => (Quotient.mk (orbitRel H X) (e i p.out) : orbitRel.Quotient H X))
    (fun i => {p | ki i p.out ≠ 0}) {o | k o.out ≠ 0} ?_ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨T, hT⟩ := hT
    refine (T.finite_toSet.image (Quotient.mk (orbitRel H X))).subset fun o ho => ?_
    obtain ⟨h, s, hs, ho⟩ := hT _ ho
    refine ⟨s, hs, ?_⟩
    rw [← mk_smul h s, ← ho]
    exact Quotient.out_eq o
  · intro o ho
    have : k o.out = 0 := not_not.1 ho
    rw [this, zero_div]
  · intro i p hp
    have : ki i p.out = 0 := not_not.1 hp
    rw [this, zero_div]
  · intro i p hp
    have hp' : ki i p.out ≠ 0 := hp
    obtain ⟨h, hh⟩ := out_mk (H := H) (e i p.out)
    have hv : k (Quotient.mk (orbitRel H X) (e i p.out)).out = ki i p.out := by rw [hh, hk, hke i _ hp']
    refine ⟨fun h0 => hp' (hv ▸ h0), ?_⟩
    have hst : (stabilizer (Hi i) p.out).map (φ i) = stabilizer H (e i p.out) := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [mem_stabilizer_iff, ← he, mem_stabilizer_iff.1 ha]
      · intro hg
        obtain ⟨_, a, rfl⟩ := hu i i _ _ g hp' hp' hg
        refine ⟨a, hinj i ?_, rfl⟩
        rw [he]
        exact hg
    show _ = k (Quotient.mk (orbitRel H X) (e i p.out)).out /
      (H₀.relIndex (stabilizer H (Quotient.mk (orbitRel H X) (e i p.out)).out) : ℂ)
    rw [hv, hh, rel_smul H₀ hn, Subgroup.relIndex_comap, hst]
  · intro o ho
    obtain ⟨i, y, h, hy, hx⟩ := hs _ ho
    obtain ⟨a, ha⟩ := out_mk (H := Hi i) y
    refine ⟨i, Quotient.mk (orbitRel (Hi i) (Yi i)) y, ?_, ?_⟩
    · show ki i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out ≠ 0
      rwa [ha, hki]
    · show Quotient.mk (orbitRel H X) (e i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out) = o
      rw [ha, he, mk_smul, ← mk_smul h, ← hx]
      exact Quotient.out_eq o
  · intro i j p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ hpq.symm
    exact (hu i j _ _ h hp hq hh).1
  · intro i p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ (Eq.symm hpq)
    obtain ⟨_, a, rfl⟩ := hu i i _ _ h hp hq hh
    rw [← he] at hh
    have h3 := hinj i hh
    rw [← Quotient.out_eq p, ← Quotient.out_eq q, ← h3]
    exact (mk_smul a _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberIndexFinite
section
namespace UpperTheory

private lemma relIndex_normal_sup {Γ : Type} [Group Γ] (N A C : Subgroup Γ) [N.Normal] (hN : N ≤ A)
    (h : A.relIndex C ≠ 0) : A.relIndex (N ⊔ C) ≠ 0 := by
  have hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hN]
  have key : ∀ K : Subgroup Γ, A.relIndex K = (A.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N)) := by
    intro K
    rw [← Subgroup.relIndex_comap, hA]
  have hm : (N ⊔ C).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  rw [key, hm, ← key]
  exact h

theorem orbitalFiber_index_finite : V.Z.Sym.Glob.Fib.IndexFin := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ hS hΓ₁ hT h0
  obtain ⟨T, hT⟩ := hT
  have hAC : (Γ₁ ⊔ Γ₀).relIndex (U'.comap ι) ≠ 0 := by
    intro h
    apply h0
    have := Subgroup.relIndex_dvd_of_le_left (U'.comap ι) (le_sup_right : Γ₀ ≤ Γ₁ ⊔ Γ₀)
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this
  have h1 : (Γ₁ ⊔ Γ₀).relIndex (Γ₁ ⊔ U'.comap ι) ≠ 0 :=
    relIndex_normal_sup Γ₁ _ _ le_sup_left hAC
  have pick : ∀ b : ((S ⊔ U').comap ι : Subgroup Γ), ∃ t, t ∈ T ∧ ∃ h ∈ Γ₁, ∃ u ∈ U',
      ι (b : Γ) = ι h * t * u := by
    intro b
    have hb : ι (b : Γ) ∈ S ⊔ U' := b.2
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hb
    obtain ⟨s, hs, u, hu, e⟩ := hb
    obtain ⟨h, hh, t, ht, u₂, hu₂, rfl⟩ := hT s hs
    exact ⟨t, ht, h, hh, u₂ * u, U'.mul_mem hu₂ hu, by rw [← e]; group⟩
  choose f hfT hf using pick
  have h2 : (Γ₁ ⊔ U'.comap ι).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    have inj : Function.Injective
        (fun q : ((S ⊔ U').comap ι : Subgroup Γ) ⧸ (Γ₁ ⊔ U'.comap ι).subgroupOf ((S ⊔ U').comap ι) =>
          (⟨f q.out, hfT _⟩ : T)) := by
      intro q q' hq
      have hq' : f q.out = f q'.out := congrArg Subtype.val hq
      rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      generalize q.out = a at hq'
      generalize q'.out = b at hq'
      obtain ⟨h, hh, u, hu, ha⟩ := hf a
      obtain ⟨h', hh', u', hu', hb⟩ := hf b
      rw [← hq'] at hb
      have hx : (a : Γ)⁻¹ * (h' * h⁻¹) * a ∈ Γ₁ := by
        simpa using hΓ₁.conj_mem (h' * h⁻¹) (Γ₁.mul_mem hh' (Γ₁.inv_mem hh)) (a : Γ)⁻¹
      have hc : (a : Γ)⁻¹ * h * h'⁻¹ * b ∈ U'.comap ι := by
        have : ι ((a : Γ)⁻¹ * h * h'⁻¹ * b) = u⁻¹ * u' := by
          simp only [map_mul, map_inv, ha, hb]
          group
        rw [Subgroup.mem_comap, this]
        exact U'.mul_mem (U'.inv_mem hu) hu'
      have e : (((a⁻¹ * b : ((S ⊔ U').comap ι : Subgroup Γ))) : Γ)
          = ((a : Γ)⁻¹ * (h' * h⁻¹) * a) * ((a : Γ)⁻¹ * h * h'⁻¹ * b) := by
        push_cast
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
    haveI := Finite.of_injective _ inj
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans h1 h2

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot
section
open MulAction in
theorem UpperTheory.orbitalFiber_of_bot :
    UpperTheory.V.Z.Sym.Glob.Fib.Bot := by
  intro H Y _ _ H₀ k
  have hmul : ∀ (a : ℂ) (g : orbitRel.Quotient H Y → ℂ), ∑ᶠ o, a * g o = a * ∑ᶠ o, g o :=
    fun a g => by simpa only [smul_eq_mul] using (smul_finsum a g).symm
  refine ⟨fun a => ?_, fun hc htriv => ?_⟩
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    exact finsum_congr fun o => mul_div_assoc _ _ _
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    refine finsum_congr fun o => ?_
    have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
    have h := Subgroup.relIndex_mul_relIndex ⊥ H₀ (stabilizer H o.out) bot_le hle
    rw [Subgroup.relIndex_bot_left] at h
    have hc' : (Nat.card H₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
    rw [← h, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hc']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSupportFinite
section
theorem UpperTheory.orbitalFiber_support_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.SuppFin := by
  intro Γ G V _ _ _ _ B hB h0 f hf g
  have hK : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := by
    have h := hB.stab g
    rw [h0, Subgroup.relIndex_bot_left] at h
    exact Nat.finite_of_card_ne_zero h
  have hKs : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup Γ) : Set Γ).Finite := Set.toFinite _
  have hfib : ∀ x : G ⧸ B.U, ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}).Finite := by
    intro x
    rcases Set.eq_empty_or_nonempty ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}) with he | ⟨γ₀, h₀⟩
    · rw [he]; exact Set.finite_empty
    · refine (hKs.image (fun k => γ₀ * k)).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
      have e : ((g⁻¹ * B.ι γ₀ * g : G) : G ⧸ B.U) = ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U) :=
        (Set.mem_singleton_iff.1 h₀).trans (Set.mem_singleton_iff.1 hγ).symm
      refine ⟨_, QuotientGroup.eq.1 e, ?_⟩
      simp [mul_assoc]
  refine (hf.fin.preimage' (f := fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) fun x _ => hfib x).subset ?_
  intro γ hγ h
  apply hγ
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (g⁻¹ * B.ι γ * g)
  have hr := hf.right u (g⁻¹ * B.ι γ * g)
  change f (((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U).out) = 0 at h
  change f (g⁻¹ * B.ι γ * g * u) = _ at hr
  rw [hu, hr] at h
  exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)
end

