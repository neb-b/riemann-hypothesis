module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CloseMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.close_map :
    ∀ (Ph B Z : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (p : ∀ N, Γ N →* Z) (po : B →* Z) (U : Ultrafilter ℕ) (a : ∀ N, Γ N) (b : B) (z : Z), Continuous (po.comp πo) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), ∀ g, p N (π N g) * (po (πo g))⁻¹ ∈ W) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), p N (a N) * z⁻¹ ∈ W) → po b = z := by
  intro Ph B Z _ _ _ _ _ _ _ _ _ _ _ Γ _ π πo p po U a b z hf hp hclose ha
  set f : Ph →* Z := po.comp πo with hfdef
  have key : ∀ W : OpenNormalSubgroup Z, po b * z⁻¹ ∈ W := by
    intro W
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap f, W.isOpen.preimage hf⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' f }
    obtain ⟨N, h1, h2, h3⟩ := ((hp W).and ((hclose V).and (ha W))).exists
    obtain ⟨g, g', hg, hg', hV⟩ := h2
    have hV' : f (g⁻¹ * g') ∈ W := hV
    have e1 := h1 g
    rw [hg] at e1
    have hb : po b = f g' := by simp [hfdef, hg']
    have hn : f g' * (f g)⁻¹ ∈ W := by
      have hc := W.isNormal'.conj_mem _ hV' (f g)
      have he : f g * f (g⁻¹ * g') * (f g)⁻¹ = f g' * (f g)⁻¹ := by
        simp [map_mul, map_inv, mul_assoc]
      rw [he] at hc
      exact hc
    have hx : po b * z⁻¹ = (f g' * (f g)⁻¹) * (p N (a N) * (f g)⁻¹)⁻¹ * (p N (a N) * z⁻¹) := by
      rw [hb]; group
    rw [hx]
    exact W.mul_mem (W.mul_mem hn (W.inv_mem e1)) h3
  by_contra hne
  have hx1 : po b * z⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := po b * z⁻¹)) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CommLim
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem eventually_le_of_le_atTop {U : Filter ℕ} (h : U ≤ atTop) (n : ℕ) : ∀ᶠ N in U, n ≤ N :=
  h (eventually_ge_atTop n)

theorem UpperTheory.V.Pa.comm_lim :
    ∀ (l : ℕ) [Fact l.Prime] (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B] [TotallyDisconnectedSpace B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (ph ta : ∀ N, Γ N) (q : ℕ → ℕ) (a b : B), (U : Filter ℕ) ≤ atTop → (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → Continuous πo → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ V.toSubgroup = πo.ker ⊔ V.toSubgroup) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ph N) a) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ta N) b) → (∀ N, q N ≡ 1 [MOD l ^ N]) → (∀ N, (ph N)⁻¹ * ta N * ph N = ta N ^ q N) → (∀ N (W : OpenNormalSubgroup (Γ N)), ∃ e : ℕ, ta N ^ l ^ e ∈ W) → a * b = b * a := by
  intro l _ Ph B _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π πo U ph ta q a b hUa hπ hπo hker hph hta hq hrel hlw
  have hl : l.Prime := Fact.out
  have key : ∀ W : OpenNormalSubgroup B, (a * b)⁻¹ * (b * a) ∈ W.toSubgroup := by
    intro W
    haveI : W.toSubgroup.Normal := W.isNormal'
    haveI : Finite (B ⧸ W.toSubgroup) :=
      W.toSubgroup.quotient_finite_of_isOpen W.toOpenSubgroup.isOpen
    haveI : W.toSubgroup.FiniteIndex := W.toSubgroup.finiteIndex_of_finite_quotient
    have hn0 : W.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap πo, W.toOpenSubgroup.isOpen.preimage hπo⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' πo }
    have hVmem : ∀ x, x ∈ V.toSubgroup ↔ πo x ∈ W.toSubgroup := fun x => Iff.rfl
    obtain ⟨N, hNn, hk, h1, h2⟩ := ((eventually_le_of_le_atTop hUa W.toSubgroup.index).and
      ((hker V).and ((hph V).and (hta V)))).exists
    obtain ⟨g1, g1', e1, e1', hg1⟩ := h1
    obtain ⟨g2, g2', e2, e2', hg2⟩ := h2
    have hkV : (π N).ker ≤ V.toSubgroup := by
      have : (π N).ker ≤ πo.ker ⊔ V.toSubgroup := hk ▸ le_sup_left
      refine this.trans (sup_le ?_ le_rfl)
      intro x hx
      rw [hVmem, MonoidHom.mem_ker.mp hx]
      exact W.toSubgroup.one_mem
    set mk : B →* B ⧸ W.toSubgroup := QuotientGroup.mk' W.toSubgroup with hmk
    have eqmk : ∀ x y : Ph, x⁻¹ * y ∈ V.toSubgroup → mk (πo x) = mk (πo y) := by
      intro x y h
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := (hVmem _).mp h
      simpa [map_mul, map_inv] using this
    have hA : mk (πo g1) = mk a := by rw [← e1']; exact eqmk _ _ hg1
    have hB : mk (πo g2) = mk b := by rw [← e2']; exact eqmk _ _ hg2
    have hrelq : (mk a)⁻¹ * mk b * mk a = mk b ^ q N := by
      have hk1 : (g1⁻¹ * g2 * g1) ⁻¹ * g2 ^ q N ∈ V.toSubgroup := by
        apply hkV
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, map_pow, e1, e2, hrel N]
        group
      have := eqmk _ _ hk1
      simp only [map_mul, map_inv, map_pow, hA, hB] at this
      exact this
    have hW'ex : ∃ W' : OpenNormalSubgroup (Γ N), ∀ x, π N x ∈ W'.toSubgroup → x ∈ V.toSubgroup := by
      have hVc : IsClosed ((V.toSubgroup : Set Ph)ᶜ) := V.toOpenSubgroup.isOpen.isClosed_compl
      have hcm : IsClosedMap (π N) := (hπ N).1.isClosedMap
      have hS : IsOpen ((π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ) := (hcm _ hVc).isOpen_compl
      have h1S : (1 : Γ N) ∈ (π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ := by
        rintro ⟨x, hx, hx1⟩
        exact hx (hkV (MonoidHom.mem_ker.mpr hx1))
      obtain ⟨W', hW'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1S
      refine ⟨W', fun x hx => ?_⟩
      by_contra hxV
      exact hW' hx ⟨x, hxV, rfl⟩
    obtain ⟨W', hW'⟩ := hW'ex
    obtain ⟨e, he⟩ := hlw N W'
    have hbe : mk b ^ l ^ e = 1 := by
      have h3 : g2 ^ l ^ e ∈ V.toSubgroup := hW' _ (by rw [map_pow, e2]; exact he)
      have h' := eqmk 1 (g2 ^ l ^ e) (by simpa using h3)
      simp only [map_one, map_pow, hB] at h'
      exact h'.symm
    have hbn : mk b ^ W.toSubgroup.index = 1 := by
      rw [← map_pow, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact W.toSubgroup.pow_index_mem b
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hbe)
    have hc1 : l ^ c ≤ W.toSubgroup.index := by
      rw [← hc]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hbn)
    have hc2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have hdiv : orderOf (mk b) ∣ l ^ N := by
      rw [hc]
      exact pow_dvd_pow l (by omega)
    have hbq : mk b ^ q N = mk b := by
      have h4 : q N ≡ 1 [MOD orderOf (mk b)] := Nat.ModEq.of_dvd hdiv (hq N)
      simpa using pow_eq_pow_iff_modEq.mpr h4
    have hcomm : mk a * mk b = mk b * mk a := by
      rw [hbq] at hrelq
      calc mk a * mk b = mk a * ((mk a)⁻¹ * mk b * mk a) := by rw [hrelq]
        _ = mk b * mk a := by group
    have h5 : mk (a * b) = mk (b * a) := by simp only [map_mul, hcomm]
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h5
    exact h5
  by_contra hne
  have hx1 : (a * b)⁻¹ * (b * a) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := (a * b)⁻¹ * (b * a))) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EltLim
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.elt_lim :
    ∀ (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (a : ∀ N, Γ N), (∀ N, Function.Surjective (π N)) → ∃ b : B, ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b := by
  intro Ph B _ _ _ _ _ _ Γ _ π πo U a hπ
  choose g hg using fun N => hπ N (a N)
  obtain ⟨b, hb⟩ := (exists_lim_elt Ph ℕ U fun N => (π N).ker).1 g
  refine ⟨πo b, fun V => (hb V).mono fun N h => ⟨g N, b, hg N, rfl, ?_⟩⟩
  simpa using V.toSubgroup.inv_mem h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem mem_PL {l : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] {H : Subgroup Γ} {x : Γ} :
    x ∈ PL (l := l) H ↔ ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U.toSubgroup := by
  simp only [PL, Subgroup.mem_iInf]

private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

private theorem exists_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  have : Finite (Γ ⧸ K) := K.quotient_finite_of_isOpen hK
  have : K.FiniteIndex := K.finiteIndex_of_finite_quotient
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  have hCo : IsOpen (K.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K.normalCore_isClosed hKc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨K.normalCore, hCo⟩
      isNormal' := K.normalCore_normal }
  exact ⟨C, Subgroup.normal_le_normalCore.mpr hP, K.normalCore_le⟩

theorem UpperTheory.V.Pa.pl_props :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
      [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
      (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) →
      (PL (l := l) H).Normal ∧ IsClosed (PL (l := l) H : Set Γ) ∧ PL (l := l) H ≤ H ∧
      (∀ U : OpenNormalSubgroup Γ, PL (l := l) H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) ∧
      (PL (l := l) H = ⊥ ↔ IsProL l H) ∧ PL (l := l) H = proLResOf l H := by
  intro l _ Γ _ _ _ _ _ H _ hHo
  have hHc : IsClosed (H : Set Γ) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have cond_le : ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) →
      PL (l := l) H ≤ U.toSubgroup :=
    fun U hU x hx => mem_PL.mp hx U hU
  have hnorm : (PL (l := l) H).Normal :=
    ⟨fun x hx g => mem_PL.mpr fun U hU => U.isNormal'.conj_mem _ (mem_PL.mp hx U hU) g⟩
  have hclosed : IsClosed (PL (l := l) H : Set Γ) := by
    simp only [PL, Subgroup.coe_iInf]
    exact isClosed_iInter fun U => isClosed_iInter fun _ => U.toOpenSubgroup.isClosed
  let HU : OpenNormalSubgroup Γ := { toOpenSubgroup := ⟨H, hHo⟩, isNormal' := inferInstance }
  have hle : PL (l := l) H ≤ H := by
    have hc : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ HU := by
      intro h hh
      refine ⟨0, ?_⟩
      rw [pow_zero, pow_one]
      exact hh
    exact cond_le HU hc
  have hPn : (proLResOf l H).Normal := by
    constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let c : H →* H := (MulAut.conjNormal g).toMonoidHom
    have hc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    refine Subgroup.mem_map.mpr ⟨c y, mem_proLRes.mpr ?_, ?_⟩
    · intro N hN
      let M : OpenNormalSubgroup H :=
        { toSubgroup := N.toSubgroup.comap c
          isOpen' := N.isOpen.preimage hc
          isNormal' := Subgroup.Normal.comap N.isNormal' c }
      have hM : IsPGroup l (H ⧸ M.toSubgroup) := by
        rw [pq_iff] at hN ⊢
        intro z
        obtain ⟨k, hk⟩ := hN (c z)
        exact ⟨k, by simpa [M, map_pow] using hk⟩
      exact mem_proLRes.mp hy M hM
    · simp [c, MulAut.conjNormal_apply]
  have hPc : IsClosed (proLResOf l H : Set Γ) := by
    unfold proLResOf
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hHc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)
  have hPcond (U : OpenNormalSubgroup Γ) (hU : proLResOf l H ≤ U.toSubgroup)
      (h : Γ) (hh : h ∈ H) : ∃ e : ℕ, h ^ l ^ e ∈ U.toSubgroup := by
    classical
    have : CompactSpace H := isCompact_iff_compactSpace.mp hHc.isCompact
    let K := U.toSubgroup.comap H.subtype
    have hKo : IsOpen (K : Set H) := U.isOpen.preimage continuous_subtype_val
    have hleK : proLRes l H ≤ K := Subgroup.map_le_iff_le_comap.mp hU
    let ι := {N : OpenNormalSubgroup H // IsPGroup l (H ⧸ N.toSubgroup)}
    let t : ι → Set H := fun i => i.1.toSubgroup
    have hdisjoint : Disjoint (K : Set H)ᶜ (⋂ i, t i) := by
      simp only [Set.disjoint_left, Set.mem_compl_iff, Set.mem_iInter]
      intro y hy hall
      exact hy (hleK (mem_proLRes.mpr fun N hN => hall ⟨N, hN⟩))
    obtain ⟨s, hs⟩ := hKo.isClosed_compl.isCompact.elim_finite_subfamily_closed t
      (fun i => i.1.toOpenSubgroup.isClosed) hdisjoint
    let g : H := ⟨h, hh⟩
    have hk (i : ι) : ∃ k : ℕ, g ^ l ^ k ∈ i.1.toSubgroup :=
      (pq_iff l H _).mp i.2 g
    choose k hk using hk
    refine ⟨∑ i ∈ s, k i, ?_⟩
    change g ^ l ^ (∑ i ∈ s, k i) ∈ K
    by_contra hg
    apply Set.disjoint_left.mp hs hg
    simp only [Set.mem_iInter]
    intro i hi
    have hki : k i ≤ ∑ j ∈ s, k j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    have hpow : l ^ (∑ j ∈ s, k j) = l ^ k i * l ^ (∑ j ∈ s, k j - k i) := by
      rw [← pow_add, Nat.add_sub_cancel' hki]
    change g ^ l ^ (∑ j ∈ s, k j) ∈ i.1.toSubgroup
    rw [hpow, pow_mul]
    exact Subgroup.pow_mem _ (hk i) _
  have heq : PL (l := l) H = proLResOf l H := by
    have := hPn
    apply le_antisymm
    · intro x hx
      by_contra hxP
      have hsI := ProfiniteGrp.closedSubgroup_eq_sInf_open
        (⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ)
      have h2 : x ∉ ((⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ) : Subgroup Γ) := hxP
      rw [hsI, Subgroup.mem_sInf] at h2
      push Not at h2
      obtain ⟨K, ⟨hKo, hPK⟩, hxK⟩ := h2
      obtain ⟨U, hPU, hUK⟩ := exists_core K (proLResOf l H) hKo hPK
      exact hxK (hUK (mem_PL.mp hx U (hPcond U hPU)))
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_PL]
      intro U hU
      let N : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨U.toSubgroup.comap H.subtype,
            U.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩
          isNormal' := Subgroup.Normal.comap U.isNormal' _ }
      have : N.toSubgroup.Normal := N.isNormal'
      have hpg : IsPGroup l (H ⧸ N.toSubgroup) :=
        (pq_iff l H _).mpr fun g => hU g g.2
      exact mem_proLRes.mp hy N hpg
  have hiff : ∀ U : OpenNormalSubgroup Γ,
      PL (l := l) H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
    intro U
    refine ⟨fun h => ?_, cond_le U⟩
    exact hPcond U (heq ▸ h)
  have hbot : PL (l := l) H = ⊥ ↔ IsProL l H := by
    rw [isProL_iff]
    constructor
    · intro hb N g
      let K : Subgroup Γ := N.toSubgroup.map H.subtype
      have hKo : IsOpen (K : Set Γ) := by
        rw [Subgroup.coe_map]
        exact hHo.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
      obtain ⟨U, -, hUK⟩ := exists_core K ⊥ hKo bot_le
      obtain ⟨e, he⟩ := (hiff U).mp (by rw [hb]; exact bot_le) g g.2
      refine ⟨e, ?_⟩
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp (hUK he)
      have hy' : y = g ^ l ^ e := Subtype.ext hyg
      rw [← hy']
      exact hy
    · intro hP
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have key : ∀ W : OpenNormalSubgroup Γ, x ∈ W.toSubgroup := by
        intro W
        apply cond_le W _ hx
        intro h hh
        let N : OpenNormalSubgroup H :=
          { toOpenSubgroup := ⟨W.toSubgroup.comap H.subtype,
              W.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩
            isNormal' := Subgroup.Normal.comap W.isNormal' _ }
        obtain ⟨k, hk⟩ := hP N ⟨h, hh⟩
        exact ⟨k, hk⟩
      by_contra hne
      obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (isOpen_compl_singleton (x := x)) (by simpa [eq_comm] using hne)
      exact hU (key U) rfl
  exact ⟨hnorm, hclosed, hle, hiff, hbot, heq⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlSub
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_sub :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H K : Subgroup Γ) [H.Normal] [K.Normal], IsOpen (K : Set Γ) → H ≤ K → ∀ U : OpenNormalSubgroup K, (∀ h : K, (h : Γ) ∈ H → ∃ e : ℕ, h ^ l ^ e ∈ U) → ∀ g : K, (g : Γ) ∈ PL (l := l) H → g ∈ U := by
  intro l _ Γ _ _ _ _ _ H K _ _ hK hHK U hU g hg
  have hl : l.Prime := Fact.out
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  haveI : U.toSubgroup.FiniteIndex := U.toOpenSubgroup.toSubgroup.finiteIndex_of_finite_quotient
  haveI : U.toSubgroup.Normal := U.isNormal'
  have hn0 : U.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have lem : ∀ k : K, (k : Γ) ∈ H → k ^ l ^ U.toSubgroup.index ∈ U.toSubgroup := by
    intro k hk
    obtain ⟨e, he⟩ := hU k hk
    set q : K ⧸ U.toSubgroup := (QuotientGroup.mk k : K ⧸ U.toSubgroup)
    have hqe : q ^ l ^ e = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact he
    have hqn : q ^ U.toSubgroup.index = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact U.toSubgroup.pow_index_mem k
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hqe)
    have h1 : l ^ a ≤ U.toSubgroup.index := by
      rw [← ha]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hqn)
    have h2 : a < l ^ a := Nat.lt_pow_self hl.one_lt
    have h3 : orderOf q ∣ l ^ U.toSubgroup.index := by
      rw [ha]
      exact pow_dvd_pow l (by omega)
    have hq : q ^ l ^ U.toSubgroup.index = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
    exact hq
  let O : Subgroup Γ := U.toSubgroup.map K.subtype
  have hOo : IsOpen (O : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hK.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen
  have hOc : IsClosed (O : Set Γ) := OpenSubgroup.isClosed ⟨O, hOo⟩
  haveI : Finite (Γ ⧸ O) := O.quotient_finite_of_isOpen hOo
  haveI : O.FiniteIndex := O.finiteIndex_of_finite_quotient
  have hCo : IsOpen (O.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.normalCore_isClosed hOc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨O.normalCore, hCo⟩
      isNormal' := O.normalCore_normal }
  have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ C.toOpenSubgroup := by
    intro h hh
    refine ⟨U.toSubgroup.index, ?_⟩
    show ∀ b : Γ, b * h ^ l ^ U.toSubgroup.index * b⁻¹ ∈ O
    intro b
    rw [← conj_pow]
    have hbH : b * h * b⁻¹ ∈ H := ‹H.Normal›.conj_mem h hh b
    have hm := lem ⟨b * h * b⁻¹, hHK hbH⟩ hbH
    exact Subgroup.mem_map.mpr ⟨_, hm, rfl⟩
  have hgC : (g : Γ) ∈ C.toOpenSubgroup := by
    unfold PL at hg
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg C) hcond
  have hgO : (g : Γ) ∈ O := O.normalCore_le hgC
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgO
  have : x = g := Subtype.ext hxg
  rw [← this]
  exact hx
end

