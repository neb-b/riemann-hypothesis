module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ChartOfFlat
section
open PrimeSpectrum in
private theorem UpperTheory.V.Pr.exp_product_chart_local {X : Type} [TopologicalSpace X] {C : Type} [CommRing C]
    {j : PrimeSpectrum C → X} (hj : Topology.IsOpenEmbedding j) {Z : Set X} (hZ : IsIrreducible Z)
    {c : PrimeSpectrum C} (hc : j c ∈ Z) :
    ∃ q : PrimeSpectrum C, q ⤳ c ∧ Z ⊆ closure {j q} := by
  have h1 : IsIrreducible (j ⁻¹' Z) := ⟨⟨c, hc⟩, hZ.isPreirreducible.preimage hj⟩
  obtain ⟨q, hq⟩ := QuasiSober.sober h1.closure isClosed_closure
  refine ⟨q, hq.specializes (subset_closure hc), ?_⟩
  have h2 : Z ⊆ closure (Z ∩ Set.range j) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hZ.isPreirreducible hj.isOpen_range
      ⟨j c, hc, c, rfl⟩
  refine h2.trans (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨hy, y, rfl⟩
  have h3 : q ⤳ y := hq.specializes (subset_closure hy)
  exact specializes_iff_mem_closure.mp (h3.map hj.continuous)

open PrimeSpectrum in
theorem UpperTheory.V.Pr.chartOfFlat :
    UpperTheory.V.Pr.ChartOfFlat := by
  intro X _ C _ j hj R _ _ _ _
  have hg : GeneralizingMap (PrimeSpectrum.comap (algebraMap C R)) :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance
  have hc : Continuous (j ∘ PrimeSpectrum.comap (algebraMap C R)) :=
    hj.continuous.comp (PrimeSpectrum.continuous_comap _)
  refine ⟨hc, rfl, ?_, ?_⟩
  · intro P hP
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro Z hZ hle
    have hmem : j (PrimeSpectrum.comap (algebraMap C R) P) ∈ Z := hle (subset_closure rfl)
    obtain ⟨q, hq, hZq⟩ := UpperTheory.V.Pr.exp_product_chart_local hj hZ hmem
    obtain ⟨P', hP', rfl⟩ := hg hq
    have h1 : P' ≤ P := (PrimeSpectrum.le_iff_specializes _ _).mpr hP'
    have h2 : P.asIdeal ≤ P'.asIdeal := hP.2 ⟨P'.isPrime, bot_le⟩ h1
    have h3 : P' = P := le_antisymm h1 h2
    subst h3
    exact hZq
  · intro Y hY hx
    obtain ⟨q, hq, hYq⟩ := UpperTheory.V.Pr.exp_product_chart_local hj hY.1 hx
    obtain ⟨P', -, rfl⟩ := hg hq
    obtain ⟨p, hp, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := P'.asIdeal) bot_le
    refine ⟨⟨p, hp.1.1⟩, hp, ?_⟩
    have h1 : (⟨p, hp.1.1⟩ : PrimeSpectrum R) ⤳ P' := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 : Y ⊆ closure {(j ∘ PrimeSpectrum.comap (algebraMap C R)) ⟨p, hp.1.1⟩} :=
      hYq.trans (closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp (h1.map hc))) isClosed_closure)
    exact Set.Subset.antisymm (hY.2 isIrreducible_singleton.closure h2) h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GlobOfCharts
section
open IsLocalRing in
theorem UpperTheory.V.Pr.globOfCharts :
    UpperTheory.V.Pr.GlobOfCharts := by
  intro X _ M hTI hG x R _ _ _ f hC L hLT hLG hConcl
  have eG : ∀ P, P ∈ L.Good ↔ f P ∈ M.Good := fun P => by rw [hLG]; rfl
  have eT : ∀ P, P ∈ L.TI ↔ f P ∈ M.TI := fun P => by rw [hLT]; rfl
  have hsub : ∀ P : PrimeSpectrum R, f P ∈ M.Good → closure {f P} ⊆ M.Good :=
    fun P h => hG.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  have hmeet : ∀ P : PrimeSpectrum R, (closure {f P} ∩ M.TI).Nonempty → f P ∈ M.TI := by
    rintro P ⟨y, hy, hyT⟩
    obtain ⟨z, hzT, hz⟩ := mem_closure_iff.mp hy _ hTI hyT
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzT
  refine ⟨?_, ?_, ?_⟩
  · intro hD Y Y' hY hY' hxY hxY' hYg
    obtain ⟨P, hPm, rfl⟩ := hC.onto Y hY.1 hxY
    obtain ⟨P', hP'm, rfl⟩ := hC.onto Y' hY'.1 hxY'
    have hPG : P ∈ L.Good := (eG P).mpr (hYg (subset_closure (Set.mem_singleton _)))
    have hPT : P ∈ L.TI := (eT P).mpr (hmeet P hY.2)
    have h' := hConcl P hPG hPT (hD P hPm) P' ((eT P').mpr (hmeet P' hY'.2)) hP'm
    exact hsub P' ((eG P').mp h')
  · intro hall
    refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
      mem_irreducibleComponent⟩
    obtain ⟨P, hPm, hPY⟩ :=
      hC.onto _ (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent
    refine ⟨f P, ?_, (eT P).mp (hall P hPm)⟩
    rw [← hPY]
    exact subset_closure (Set.mem_singleton _)
  · rintro ⟨I, hIG, hIT, hID⟩
    obtain ⟨p, hpm, hpI⟩ :=
      Ideal.exists_minimalPrimes_le (J := I.asIdeal) (bot_le : (⊥ : Ideal R) ≤ I.asIdeal)
    haveI hpp : p.IsPrime := hpm.1.1
    let P : PrimeSpectrum R := ⟨p, hpp⟩
    have hPmin : P.asIdeal ∈ minimalPrimes R := hpm
    have hopen : IsOpen L.TI := by
      rw [hLT]
      exact hTI.preimage hC.cont
    have hPT : P ∈ L.TI := by
      have hcl : I ∈ closure ({P} : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.le_iff_mem_closure P I).mp hpI
      obtain ⟨z, hzT, hz⟩ := mem_closure_iff.mp hcl _ hopen hIT
      rw [Set.mem_singleton_iff] at hz
      rw [← hz]
      exact hzT
    have hPG := hConcl I hIG hIT hID P hPT hPmin
    exact ⟨closure {f P}, ⟨hC.min P hPmin, f P, subset_closure (Set.mem_singleton _), (eT P).mp hPT⟩,
      hsub P ((eG P).mp hPG)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GlobProp
section
theorem UpperTheory.V.Pr.globProp :
    UpperTheory.V.Pr.GlobProp := by
  intro X _ _ M hM
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have key : ∀ Y, M.CompI Y → Y ⊆ M.Good := by
    by_contra hne
    push_neg at hne
    obtain ⟨Yb, hYb, hYbn⟩ := hne
    set G : Set X := ⋃ Y ∈ {Y | M.CompI Y ∧ Y ⊆ M.Good}, Y with hG
    set B : Set X := ⋃ Y ∈ {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good}, Y with hB
    have hGc : IsClosed G :=
      (hfin.subset (t := {Y | M.CompI Y ∧ Y ⊆ M.Good}) (fun Y hY => hY.1.1)).isClosed_biUnion
        (fun Y hY => isClosed_of_mem_irreducibleComponents Y hY.1.1)
    have hBc : IsClosed B :=
      (hfin.subset (t := {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good}) (fun Y hY => hY.1.1)).isClosed_biUnion
        (fun Y hY => isClosed_of_mem_irreducibleComponents Y hY.1.1)
    have hcov : M.Core ⊆ G ∪ B := by
      intro x hx
      have h1 : x ∈ closure (M.Cl \ M.EE) := hM.dense hx
      have h2 : M.Cl \ M.EE ⊆ G ∪ B := by
        intro y hy
        obtain ⟨Y, hY, hyY⟩ := hM.off y hy
        by_cases hg : Y ⊆ M.Good
        · exact Or.inl (Set.mem_biUnion (show Y ∈ {Y | M.CompI Y ∧ Y ⊆ M.Good} from ⟨hY, hg⟩) hyY)
        · exact Or.inr (Set.mem_biUnion (show Y ∈ {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good} from ⟨hY, hg⟩) hyY)
      exact (hGc.union hBc).closure_subset_iff.mpr h2 h1
    obtain ⟨Ys, hYs, hYsg⟩ := hM.seed
    have hG' : (M.Core ∩ G).Nonempty := by
      obtain ⟨x, hxY, hxC⟩ := hM.meets Ys hYs
      exact ⟨x, hxC, Set.mem_biUnion (show Ys ∈ {Y | M.CompI Y ∧ Y ⊆ M.Good} from ⟨hYs, hYsg⟩) hxY⟩
    have hB' : (M.Core ∩ B).Nonempty := by
      obtain ⟨x, hxY, hxC⟩ := hM.meets Yb hYb
      exact ⟨x, hxC, Set.mem_biUnion (show Yb ∈ {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good} from ⟨hYb, hYbn⟩) hxY⟩
    obtain ⟨x, hxC, hxG, hxB⟩ := isPreconnected_closed_iff.mp hM.conn G B hGc hBc hcov hG' hB'
    obtain ⟨z, hzGB, hzCl⟩ := hM.jac (G ∩ B) (hGc.inter hBc) ⟨x, ⟨hxG, hxB⟩, hxC⟩
    rw [hG, hB] at hzGB
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hzGB
    obtain ⟨⟨Y, ⟨hY, hYg⟩, hzY⟩, ⟨Y', ⟨hY', hY'n⟩, hzY'⟩⟩ := hzGB
    exact hY'n (hM.loc z hzCl Y Y' hY hY' hzY hzY' hYg)
  intro x hx
  exact key (irreducibleComponent x)
    ⟨irreducibleComponent_mem_irreducibleComponents x, ⟨x, mem_irreducibleComponent, hx⟩⟩
    mem_irreducibleComponent
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LocProp
section
open UpperTheory.V.Pr in
private theorem UpperTheory.V.Pr.exists_prime_qdim {R : Type} [CommRing R] (J : Ideal R) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ qdim J) :
    ∃ I : PrimeSpectrum R, J ≤ I.asIdeal ∧ (n : WithBot ℕ∞) ≤ qdim I.asIdeal := by
  rw [qdim, ringKrullDim_quotient] at h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h
  refine ⟨(l 0).1, fun y hy => (l 0).2 hy, ?_⟩
  rw [qdim, ringKrullDim_quotient]
  apply Order.le_krullDim_iff.mpr
  refine ⟨{ length := l.length, toFun := fun i => ⟨(l i).1, ?_⟩, step := fun i => ?_ }, hl⟩
  · rw [PrimeSpectrum.mem_zeroLocus]
    exact (show (l 0).1.asIdeal ≤ (l i).1.asIdeal from l.monotone (Fin.zero_le i))
  · exact l.step i

theorem UpperTheory.V.Pr.locProp :
    UpperTheory.V.Pr.LocProp := by
  intro R _ _ L hL I hIg hIti hIbig P hPti hPmin
  have hW : ∀ p ∈ L.Nice, (∃ P ≤ p, P ∈ L.TI ∧ P ∈ L.Good) →
      ∀ P' ≤ p, P' ∈ L.TI → P' ∈ L.Good := by
    intro p hp hS
    rcases hL.nice_type p hp with hpt | hpt
    · obtain ⟨Q, hQp, _, hQg⟩ := hS
      have hpg := hL.good_up Q p hQp hQg
      intro P' hP' _
      exact hL.p1 p hp hpt hpg P' hP'
    · exact hL.p23 p hp hpt p Relation.ReflTransGen.refl hS
  let Inv : PrimeSpectrum R → Prop := fun Q =>
    (Q ∈ L.TI → Q ∈ L.Good) ∧ ((Q ∈ L.TI ∧ Q ∈ L.Good) ∨
      (Q ∈ L.Thick ∧ ∃ p0 ∈ L.Nice, p0 ∈ L.TE ∧ (∃ P ≤ p0, P ∈ L.TI ∧ P ∈ L.Good) ∧
        ∃ p ∈ L.Nice, p ∈ L.TE ∧ Q ≤ p ∧ Relation.ReflTransGen L.Link p0 p))
  have K : ∀ Q, L.Comp Q → Inv Q → ∀ M : PrimeSpectrum R, Q ≤ M →
      (L.D1 : WithBot ℕ∞) ≤ qdim M.asIdeal →
      ∃ p ∈ L.Nice, M ≤ p ∧ ∀ P' ≤ p, P' ∈ L.TI → P' ∈ L.Good := by
    intro Q hQc hQ M hQM hM
    rcases hQ.2 with ⟨hti, hg⟩ | ⟨hth, p0, hp0n, hp0e, hS, p, hpn, hpe, hQp, hrt⟩
    · have hMg := hL.good_up Q M hQM hg
      obtain ⟨p, hpn, hMp⟩ := hL.nice_good M hMg hM
      exact ⟨p, hpn, hMp, hW p hpn ⟨Q, le_trans hQM hMp, hti, hg⟩⟩
    · obtain ⟨p', hp'n, hp'e, hMp'⟩ := hL.nice_thick Q hth hQc M hQM hM
      exact ⟨p', hp'n, hMp', hL.p23 p0 hp0n hp0e p'
        (hrt.tail ⟨hpn, hpe, hp'n, hp'e, Q, hth, hQc, hQp, le_trans hQM hMp'⟩) hS⟩
  have step : ∀ Q Q', L.Adj Q Q' → Inv Q → Inv Q' := by
    intro Q Q' hadj hQ
    obtain ⟨hQc, hQ'c, hbig⟩ := hadj
    obtain ⟨M, hJM, hM⟩ := UpperTheory.V.Pr.exists_prime_qdim _ _ hbig
    have hQM : Q ≤ M := show Q.asIdeal ≤ M.asIdeal from le_trans le_sup_left hJM
    have hQ'M : Q' ≤ M := show Q'.asIdeal ≤ M.asIdeal from le_trans le_sup_right hJM
    obtain ⟨p, hpn, hMp, hWp⟩ := K Q hQc hQ M hQM hM
    by_cases hQ'ti : Q' ∈ L.TI
    · have hg := hWp Q' (le_trans hQ'M hMp) hQ'ti
      exact ⟨fun _ => hg, Or.inl ⟨hQ'ti, hg⟩⟩
    · have hth : Q' ∈ L.Thick := (hL.dich Q' hQ'c).resolve_left hQ'ti
      refine ⟨fun h => absurd h hQ'ti, Or.inr ⟨hth, ?_⟩⟩
      obtain ⟨p', hp'n, hp'e, hMp'⟩ := hL.nice_thick Q' hth hQ'c M hQ'M hM
      rcases hQ.2 with ⟨hti, hg⟩ | ⟨hQth, p0, hp0n, hp0e, hS, p1, hp1n, hp1e, hQp1, hrt⟩
      · exact ⟨p', hp'n, hp'e, ⟨Q, le_trans hQM hMp', hti, hg⟩, p', hp'n, hp'e,
          le_trans hQ'M hMp', Relation.ReflTransGen.refl⟩
      · exact ⟨p0, hp0n, hp0e, hS, p', hp'n, hp'e, le_trans hQ'M hMp',
          hrt.tail ⟨hp1n, hp1e, hp'n, hp'e, Q, hQth, hQc, hQp1, le_trans hQM hMp'⟩⟩
  obtain ⟨q, hq, hqI⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I.asIdeal) bot_le
  let P0 : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hP0I : P0 ≤ I := show q ≤ I.asIdeal from hqI
  have hP0ti : P0 ∈ L.TI := hL.ti_down P0 I hP0I hIti
  have hP0c : L.Comp P0 := hL.comp P0 hP0ti hq
  obtain ⟨p, hpn, hIp⟩ := hL.nice_good I hIg hIbig
  have hP0g := hW p hpn ⟨I, hIp, hIti, hIg⟩ P0 (le_trans hP0I hIp) hP0ti
  have hP0 : Inv P0 := ⟨fun _ => hP0g, Or.inl ⟨hP0ti, hP0g⟩⟩
  have hall : ∀ Q, Relation.ReflTransGen L.Adj P0 Q → Inv Q := by
    intro Q hch
    induction hch with
    | refl => exact hP0
    | tail _ hadj ih => exact step _ _ hadj ih
  exact (hall P (hL.chain P0 P hP0c (hL.comp P hPti hPmin))).1 hPti
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx
section
open IsLocalRing

private theorem UpperTheory.V.Pr.npe_height_le_one {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)

private theorem UpperTheory.V.Pr.npe_dim_one {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (Q : Ideal R) [Q.IsPrime] {f : R} (hfm : f ∈ maximalIdeal R) (hf : f ∉ Q) :
    ∃ p : Ideal R, p.IsPrime ∧ Q ≤ p ∧ f ∉ p ∧ ringKrullDim (R ⧸ p) = 1 := by
  obtain ⟨p, ⟨hp, hQp, hfp⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {p : Ideal R | p.IsPrime ∧ Q ≤ p ∧ f ∉ p}
    ⟨Q, inferInstance, le_rfl, hf⟩
  refine ⟨p, hp, hQp, hfp, ?_⟩
  haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hf0 : Ideal.Quotient.mk p f ≠ 0 := fun h => hfp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hh : (maximalIdeal (R ⧸ p)).height ≤ 1 := by
    refine UpperTheory.V.Pr.npe_height_le_one _ hf0 fun P hP hP0 _ => ?_
    by_contra hfP
    have hle : p ≤ P.comap (Ideal.Quotient.mk p) := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem
    refine hmax (P.comap (Ideal.Quotient.mk p))
      ⟨Ideal.comap_isPrime _ _, hQp.trans hle, hfP⟩ (lt_of_le_of_ne hle fun e => hP0 ?_)
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : x ∈ p := by rw [e]; exact hy
    exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr this)
  have hfm' : Ideal.Quotient.mk p f ∈ maximalIdeal (R ⧸ p) := by
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    exact map_nonunit _ f hfm
  have hlt : (⊥ : Ideal (R ⧸ p)) < maximalIdeal (R ⧸ p) :=
    bot_lt_iff_ne_bot.mpr fun e => hf0 (by simpa [e] using hfm')
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (maximalIdeal (R ⧸ p)).height = 1 := le_antisymm hh (le_trans le_add_self h1)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h2]
  rfl

private theorem UpperTheory.V.Pr.npe_chain {R : Type} [CommRing R] (q : LTSeries (PrimeSpectrum R))
    (J : Ideal R) (N : ℕ) (hN : N + 1 ≤ q.length) (hJ : J ≤ (q ⟨1, by omega⟩).asIdeal) :
    (N : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient, Order.le_krullDim_iff]
  exact ⟨{ length := N
           toFun := fun i => ⟨q ⟨i + 1, by omega⟩,
             hJ.trans (q.monotone (a := ⟨1, by omega⟩) (b := ⟨i + 1, by omega⟩) (by simp [Fin.le_def]))⟩
           step := fun i => q.strictMono (by simp [Fin.lt_def]) }, rfl⟩

theorem UpperTheory.V.Pr.nicePrimeEx :
    UpperTheory.V.Pr.NicePrimeEx := by
  classical
  intro R _ _ _ ϖ hϖ N hN ι _ a ha I hI
  rw [UpperTheory.V.Pr.qdim, ringKrullDim_quotient, Order.le_krullDim_iff] at hI
  obtain ⟨l, hl⟩ := hI
  obtain ⟨s, hs, hI0, hlast⟩ : ∃ s : LTSeries (PrimeSpectrum R), N + 1 ≤ s.length ∧
      I ≤ s.head.asIdeal ∧ ϖ ∈ s.last.asIdeal := by
    let t : LTSeries (PrimeSpectrum R) := l.map Subtype.val (fun _ _ h => h)
    have ht : t.length = N + 1 := hl
    have hh : I ≤ t.head.asIdeal := l.head.2
    have hle : t.last ≤ closedPoint R := le_maximalIdeal t.last.2.ne_top
    rcases hle.eq_or_lt with e | hlt
    · exact ⟨t, ht.ge, hh, by rw [e]; exact hϖ⟩
    · exact ⟨t.snoc _ hlt, by simp [ht], by simpa using hh, by rw [RelSeries.last_snoc]; exact hϖ⟩
  obtain ⟨q, hq1, hqlen, hqh, -⟩ := PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last s hlast
  have hq : N + 1 ≤ q.length := hqlen ▸ hs
  have e1 : (1 : Fin (q.length + 1)) = ⟨1, by omega⟩ := by
    ext; simp [Nat.mod_eq_of_lt (show 1 < q.length + 1 by omega)]
  rw [e1] at hq1
  set Q := q ⟨1, by omega⟩ with hQ
  have hIQ : I ≤ Q.asIdeal := by
    rw [hqh] at hI0
    exact hI0.trans (q.monotone (a := 0) (Fin.zero_le _))
  have hQ2 : Q < q ⟨2, by omega⟩ := q.strictMono (by simp [Fin.lt_def])
  obtain ⟨g, hg, hgQ⟩ := SetLike.exists_of_lt (show Q.asIdeal < (q ⟨2, by omega⟩).asIdeal from hQ2)
  have hgm : g ∈ maximalIdeal R := le_maximalIdeal (q ⟨2, by omega⟩).2.ne_top hg
  have hna : ∀ i, ∃ x ∈ a i, x ∉ Q.asIdeal := fun i =>
    SetLike.not_le_iff_exists.mp fun h => (UpperTheory.V.Pr.npe_chain q (a i) N hq h).not_gt (ha i)
  choose x hxa hxQ using hna
  haveI := Fintype.ofFinite ι
  have hf : g * ∏ i, x i ∉ Q.asIdeal := fun h => by
    rcases Q.2.mem_or_mem h with h | h
    · exact hgQ h
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hxQ i hi
  obtain ⟨p, hp, hQp, hfp, hd⟩ := UpperTheory.V.Pr.npe_dim_one Q.asIdeal (Ideal.mul_mem_right _ _ hgm) hf
  refine ⟨p, hp, hIQ.trans hQp, hd, hQp hq1, fun i hi => hfp (Ideal.mul_mem_left _ _ ?_)⟩
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem x (Finset.mem_univ i)) (hi (hxa i))
end

