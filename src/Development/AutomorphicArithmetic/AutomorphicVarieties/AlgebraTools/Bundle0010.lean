module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResMap
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff {l : ℕ} {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

theorem UpperTheory.V.AlgebraTools.proLRes_map :
    ∀ (l : ℕ) [Fact l.Prime] (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (f : G →* H), Continuous f → Function.Surjective f →
      (proLRes l G).map f = proLRes l H := by
  intro l _ G H _ _ _ _ _ _ _ _ _ _ f hf hs
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap, mem_proLRes]
    intro N hN
    rw [pq_iff] at hN
    let M : OpenNormalSubgroup G :=
      { toOpenSubgroup := OpenSubgroup.comap f hf N.toOpenSubgroup
        isNormal' := Subgroup.Normal.comap inferInstance f }
    haveI : (M.toOpenSubgroup : Subgroup G).Normal := M.isNormal'
    have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro x
      obtain ⟨k, hk⟩ := hN (f x)
      refine ⟨k, ?_⟩
      show x ^ l ^ k ∈ OpenSubgroup.comap f hf N.toOpenSubgroup
      rw [OpenSubgroup.mem_comap, map_pow]
      exact hk
    have := (mem_proLRes.mp hg) M hM
    exact (OpenSubgroup.mem_comap (hf := hf)).mp this
  · intro h hh
    rw [mem_proLRes] at hh
    let t : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} → Set G :=
      fun N => f ⁻¹' {h} ∩ (N.1.toOpenSubgroup : Set G)
    let T0 : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := by simpa using Subgroup.normal_top }
    haveI : (T0.toOpenSubgroup : Subgroup G).Normal := T0.isNormal'
    have htop : IsPGroup l (G ⧸ (T0.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro g
      refine ⟨0, ?_⟩
      show g ^ l ^ 0 ∈ (⊤ : OpenSubgroup G)
      simp
    haveI : Nonempty {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} := ⟨⟨_, htop⟩⟩
    have hcl : ∀ i, IsClosed (t i) := fun i =>
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (fun x1 x2 => x1 ⊇ x2) t := by
      intro i j
      have hK : IsPGroup l (G ⧸ ((i.1 ⊓ j.1).toOpenSubgroup : Subgroup G)) := by
        rw [pq_iff]
        intro g
        obtain ⟨a, ha⟩ := (pq_iff _).mp i.2 g
        obtain ⟨b, hb⟩ := (pq_iff _).mp j.2 g
        refine ⟨a + b, ?_⟩
        have e1 : g ^ l ^ (a + b) = (g ^ l ^ a) ^ l ^ b := by rw [pow_add, pow_mul]
        have e2 : g ^ l ^ (a + b) = (g ^ l ^ b) ^ l ^ a := by rw [add_comm, pow_add, pow_mul]
        have m1 : g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup : Subgroup G) := e1 ▸ pow_mem ha _
        have m2 : g ^ l ^ (a + b) ∈ (j.1.toOpenSubgroup : Subgroup G) := e2 ▸ pow_mem hb _
        show g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)
        exact OpenSubgroup.mem_inf.mpr ⟨m1, m2⟩
      refine ⟨⟨i.1 ⊓ j.1, hK⟩, ?_, ?_⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).1⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).2⟩
    have hnon : ∀ i, (t i).Nonempty := by
      intro i
      have hNcl : IsClosed ((i.1.toOpenSubgroup : Subgroup G) : Set G) := i.1.toOpenSubgroup.isClosed
      have hMcl : IsClosed (((i.1.toOpenSubgroup : Subgroup G).map f : Subgroup H) : Set H) := by
        rw [Subgroup.coe_map]
        exact hf.isClosedMap _ hNcl
      haveI : (i.1.toOpenSubgroup : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      haveI : ((i.1.toOpenSubgroup : Subgroup G).map f).FiniteIndex := by
        rw [Subgroup.finiteIndex_iff]
        intro h0
        have hd := Subgroup.index_map_dvd (i.1.toOpenSubgroup : Subgroup G) hs
        rw [h0, zero_dvd_iff] at hd
        exact (Subgroup.finiteIndex_iff.mp inferInstance) hd
      let M : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨(i.1.toOpenSubgroup : Subgroup G).map f,
            Subgroup.isOpen_of_isClosed_of_finiteIndex _ hMcl⟩
          isNormal' := Subgroup.Normal.map inferInstance f hs }
      haveI : (M.toOpenSubgroup : Subgroup H).Normal := M.isNormal'
      have hM : IsPGroup l (H ⧸ (M.toOpenSubgroup : Subgroup H)) := by
        rw [pq_iff]
        intro y
        obtain ⟨x, rfl⟩ := hs y
        obtain ⟨k, hk⟩ := (pq_iff _).mp i.2 x
        refine ⟨k, ?_⟩
        show f x ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G).map f
        exact ⟨x ^ l ^ k, hk, map_pow f x _⟩
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp (hh M hM)
      exact ⟨x, hfx, hx⟩
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon
      (fun i => (hcl i).isCompact) hcl
    rw [Set.mem_iInter] at hg
    refine ⟨g, ?_, (hg (Classical.arbitrary _)).1⟩
    rw [SetLike.mem_coe, mem_proLRes]
    intro N hN
    exact (hg ⟨N, hN⟩).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpStep
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.splitAlg_succ_equiv :
    ∀ (R : Type) [CommRing R] (n : ℕ) (P : Polynomial R), P.Monic → P.natDegree = n + 1 →
      ∃ (_ : Algebra (AdjoinRoot P) (SplitAlg P (n + 1))) (_ : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1))),
        algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 ∧
        ∃ e : SplitAlg P (n + 1) ≃ₐ[AdjoinRoot P]
            SplitAlg ((P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P))) n,
          ∀ i : Fin n, e (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root _ n i := by
  intro R _ n P hP hdeg
  have hroot0 : Polynomial.eval₂ (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) P = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, ← SplitAlg.prod_root, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  let φ : AdjoinRoot P →+* SplitAlg P (n + 1) :=
    AdjoinRoot.lift (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) hroot0
  letI alg : Algebra (AdjoinRoot P) (SplitAlg P (n + 1)) := φ.toAlgebra
  have hφ : ∀ r : R, algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (algebraMap R (AdjoinRoot P) r)
      = algebraMap R (SplitAlg P (n + 1)) r := fun r => AdjoinRoot.lift_of hroot0
  haveI tower : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1)) :=
    IsScalarTower.of_algebraMap_eq (fun r => (hφ r).symm)
  have hr0 : algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 :=
    AdjoinRoot.lift_root hroot0
  refine ⟨alg, tower, hr0, ?_⟩
  set Q := (P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) with hQ
  have hfac : P.map (algebraMap R (AdjoinRoot P)) = (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) * Q := by
    rw [hQ, eq_comm, Polynomial.mul_divByMonic_eq_iff_isRoot, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.isRoot_root P
  have hmapS : P.map (algebraMap R (SplitAlg P (n + 1)))
      = (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) 0))
        * Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    rw [IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg P (n + 1)), ← Polynomial.map_map, hfac,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hr0]
  have hg : ∏ i : Fin n, (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) i.succ))
      = Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    have h1 := SplitAlg.prod_root P (n + 1)
    rw [Fin.prod_univ_succ, hmapS] at h1
    exact (Polynomial.monic_X_sub_C _).isRegular.left h1
  let g : SplitAlg Q n →ₐ[AdjoinRoot P] SplitAlg P (n + 1) :=
    SplitAlg.lift Q n (fun i => SplitAlg.root P (n + 1) i.succ) hg
  let a : Fin (n + 1) → SplitAlg Q n :=
    Fin.cons (algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P)) (SplitAlg.root Q n)
  have hf : ∏ i, (Polynomial.X - Polynomial.C (a i)) = P.map (algebraMap R (SplitAlg Q n)) := by
    rw [Fin.prod_univ_succ]
    simp only [a, Fin.cons_zero, Fin.cons_succ]
    rw [SplitAlg.prod_root, IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg Q n), ← Polynomial.map_map,
      hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  let f : SplitAlg P (n + 1) →ₐ[R] SplitAlg Q n := SplitAlg.lift P (n + 1) a hf
  have hf0 : f (SplitAlg.root P (n + 1) 0) = algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P) := by
    simp only [f, SplitAlg.lift_root, a, Fin.cons_zero]
  have hfs : ∀ i : Fin n, f (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root Q n i := by
    intro i
    simp only [f, SplitAlg.lift_root, a, Fin.cons_succ]
  have hfK : f.comp (IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg P (n + 1)))
      = IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg Q n) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom', hr0, hf0]
  let fK : SplitAlg P (n + 1) →ₐ[AdjoinRoot P] SplitAlg Q n :=
    { f with commutes' := fun k => DFunLike.congr_fun hfK k }
  have hgs : ∀ i : Fin n, g (SplitAlg.root Q n i) = SplitAlg.root P (n + 1) i.succ := by
    intro i
    exact SplitAlg.lift_root Q n _ hg i
  refine ⟨AlgEquiv.ofAlgHom fK g ?_ ?_, ?_⟩
  · apply SplitAlg.hom_ext
    intro i
    show f (g (SplitAlg.root Q n i)) = SplitAlg.root Q n i
    rw [hgs, hfs]
  · apply AlgHom.restrictScalars_injective R
    apply SplitAlg.hom_ext
    intro i
    show g (f (SplitAlg.root P (n + 1) i)) = SplitAlg.root P (n + 1) i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hf0, AlgHom.commutes, hr0]
    · rw [hfs, hgs]
  · intro i
    exact hfs i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnAlgMapSmulMem
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.tnAlg_smul_mem {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R) (a : A) {y : M}
    (hy : y ∈ (I • ⊤ : Submodule R M)) : a • y ∈ (I • ⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul A r n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro u v hu hv
    rw [smul_add]
    exact Submodule.add_mem _ hu hv

private theorem UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem {R A M : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R)
    {a : A} (ha : a ∈ I.map (algebraMap R A)) (y : M) : a • y ∈ (I • ⊤ : Submodule R M) := by
  unfold Ideal.map at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨r, hr, rfl⟩ := hb
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [add_smul]; exact Submodule.add_mem _ hb hc
  | smul b c _ hc =>
    rw [smul_eq_mul, mul_smul]
    exact UpperTheory.V.AlgebraTools.tnAlg_smul_mem I b hc

private theorem UpperTheory.V.AlgebraTools.tnAlg_mem_radical {R A : Type} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] {a : A}
    (ha : ∀ n : Ideal A, n.IsMaximal → a ∈ n) :
    a ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).radical := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  apply ha
  have hle' : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R A) P := by
    intro r hr
    rw [Ideal.mem_comap]
    exact hle (Ideal.mem_map_of_mem _ hr)
  have hne : Ideal.comap (algebraMap R A) P ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
  have hc : Ideal.comap (algebraMap R A) P = IsLocalRing.maximalIdeal R :=
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle').symm
  have hcm : (Ideal.comap (algebraMap R A) P).IsMaximal := by
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P hcm

theorem UpperTheory.V.AlgebraTools.topNil_eq_idem :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A κ : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (t : κ → A),
      ∃ e : A, IsIdempotentElem e ∧ (∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n)) ∧
        ∀ (M : Type) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Finite R M] (x : M),
          x ∈ topNil (IsLocalRing.maximalIdeal R) (fun i => (Algebra.lsmul R R M (t i) : Module.End R M)) ↔ e • x = x := by
  intro R _ _ _ _ A κ _ _ _ t
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨e, he, hT⟩ := GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian R (S := A)
    {n : MaximalSpectrum A | ∀ i, t i ∈ n.asIdeal}
  have hmax : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n) := fun n hn => hT ⟨n, hn⟩
  refine ⟨e, he, hmax, ?_⟩
  intro M _ _ _ _ _ x
  have hpow : ∀ (a : A) (r : ℕ) (y : M),
      ((Algebra.lsmul R R M a : Module.End R M) ^ r) y = a ^ r • y := by
    intro a r y
    rw [← map_pow, Algebra.lsmul_coe]
  rw [mem_topNil_iff_exists]
  simp only [hpow]
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : ∀ j : ℕ, ∀ a : A, ∀ y ∈ (m ^ j • ⊤ : Submodule R M), a • y ∈ (m ^ j • ⊤ : Submodule R M) :=
    fun j a y hy => UpperTheory.V.AlgebraTools.tnAlg_smul_mem (m ^ j) a hy
  constructor
  · intro hx
    set y := x - e • x with hy
    have hey : e • y = 0 := by rw [hy, smul_sub, smul_smul, he.eq, sub_self]
    suffices y = 0 by rw [sub_eq_zero] at this; exact this.symm
    have hall : ∀ j : ℕ, y ∈ (m ^ j • ⊤ : Submodule R M) := by
      intro j
      let P : Submodule A M :=
        { carrier := (m ^ j • ⊤ : Submodule R M)
          add_mem' := fun ha hb => Submodule.add_mem _ ha hb
          zero_mem' := Submodule.zero_mem _
          smul_mem' := fun a _ hb => hA j a _ hb }
      let K : Ideal A := P.comap (LinearMap.toSpanSingleton A M y)
      have hKe : e ∈ K := by
        show e • y ∈ P
        rw [hey]
        exact P.zero_mem
      have hKt : ∀ i, t i ∈ K.radical := by
        intro i
        obtain ⟨r, hr⟩ := hx i j
        refine ⟨r, ?_⟩
        show t i ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)
        rw [hy, smul_sub]
        refine Submodule.sub_mem _ hr ?_
        rw [smul_comm (t i ^ r) e x]
        exact hA j e _ hr
      have htop : K.radical = ⊤ := by
        by_contra hne
        obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal _ hne
        exact ((hmax n hn).mpr (fun i => hle (hKt i))) (hle (Ideal.le_radical hKe))
      have h1 : (1 : A) ∈ K.radical := htop ▸ Submodule.mem_top
      obtain ⟨r, hr⟩ := h1
      have h2 : (1 : A) ^ r • y ∈ (m ^ j • ⊤ : Submodule R M) := hr
      rw [one_pow, one_smul] at h2
      exact h2
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) m
      (by rw [hm, IsLocalRing.ringJacobson_eq_maximalIdeal])
    have hyi : y ∈ (⨅ i, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at hyi
    exact hyi
  · intro hx i j
    have hin : ∀ n : Ideal A, n.IsMaximal → t i * e ∈ n := by
      intro n hn
      by_cases h : e ∈ n
      · exact n.mul_mem_left _ h
      · exact n.mul_mem_right _ ((hmax n hn).mp h i)
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.tnAlg_mem_radical (R := R) hin
    refine ⟨N * j, ?_⟩
    have hex : ∀ k : ℕ, e ^ k • x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hx, ih]
    have hmem : (t i * e) ^ (N * j) ∈ (m ^ j).map (algebraMap R A) := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_mem_pow hN j
    have h3 := UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem (m ^ j) hmem x
    rwa [mul_pow, mul_smul, hex] at h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TrinvBaseChange
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.trinv_baseChange :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) (B' : Type) [CommRing B'] [Algebra B B'], ∃ T' : TrInv B' (B' ⊗[B] E), (∀ y, T'.st (1 ⊗ₜ y) = 1 ⊗ₜ T.st y) ∧ ∀ y, T'.tr (1 ⊗ₜ y) = algebraMap B B' (T.tr y) := by
  intro B E _ _ _ T B' _ _
  let s : B' ⊗[B] E →ₗ[B'] B' ⊗[B] E := T.st.baseChange B'
  let t : B' ⊗[B] E →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ T.tr.baseChange B'
  have hs : ∀ (a : B') (y : E), s (a ⊗ₜ y) = a ⊗ₜ T.st y := fun a y => by simp [s]
  have ht : ∀ (a : B') (y : E), t (a ⊗ₜ y) = T.tr y • a := fun a y => by simp [t]
  refine ⟨⟨s, ?_, ?_, t, ?_, ?_⟩, fun y => hs 1 y, fun y => ?_⟩
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, hs, T.st_mul, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, T.st_st]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, ht, T.tr_comm u v, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, ht, T.tr_st]
  · show t (1 ⊗ₜ y) = _
    rw [ht, Algebra.algebraMap_eq_smul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
section
noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section ULim

variable {ι R : Type} [CommRing R] (F : Filter ι) (I : ℕ → Ideal R)
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def uNull : Submodule R (∀ i, M i) where
  carrier := {p | ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i))}
  add_mem' ha hb j := ((ha j).and (hb j)).mono fun _ h => add_mem h.1 h.2
  zero_mem' _ := Eventually.of_forall fun _ => zero_mem _
  smul_mem' c _ h j := (h j).mono fun _ h => Submodule.smul_mem _ c h


abbrev ULim : Type := (∀ i, M i) ⧸ uNull F I M

def ULim.mk : (∀ i, M i) →ₗ[R] ULim F I M := (uNull F I M).mkQ

theorem ULim.mk_surjective : Function.Surjective (ULim.mk F I M) := Submodule.mkQ_surjective _

variable {F I M} in
theorem ULim.mk_eq_zero {p : ∀ i, M i} :
    ULim.mk F I M p = 0 ↔ ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i)) := by
  show (uNull F I M).mkQ p = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl


variable {I M} in
def ULim.map {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) : ULim F I M →ₗ[R] ULim F I' M' :=
  Submodule.mapQ _ _ (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) fun p hp j =>
    (hp j).mono fun i hi => by
      have h1 : f i (p i) ∈ Submodule.map (f i) (I j • ⊤ : Submodule R (M i)) := ⟨_, hi, rfl⟩
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono (h j) le_top h1

variable {I M} in
theorem ULim.map_mk {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) (p : ∀ i, M i) :
    ULim.map F h f (ULim.mk F I M p) = ULim.mk F I' M' fun i => f i (p i) := rfl

def ULim.scal (r : ι → R) : ULim F I M →ₗ[R] ULim F I M :=
  ULim.map F (fun _ => le_rfl) fun i => r i • LinearMap.id



end ULim

section QReg

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def QRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) (J : Ideal R) (a : ℕ) : Prop :=
  ∀ c : GlobalTheory.MonoDeg σ a → M,
    ∑ α, GlobalTheory.monoVal y α.1 • c α ∈ ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ ((Ideal.span (Set.range y) ⊔ J) • ⊤ : Submodule R M)

theorem isQuasiRegularSeq_iff_qRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) :
    GlobalTheory.IsQuasiRegularSeq M y ↔ ∀ a, QRegAt M y ⊥ a := by
  unfold GlobalTheory.IsQuasiRegularSeq QRegAt
  simp only [sup_bot_eq]

end QReg

end UpperTheory.V.AlgebraTools
end
end

