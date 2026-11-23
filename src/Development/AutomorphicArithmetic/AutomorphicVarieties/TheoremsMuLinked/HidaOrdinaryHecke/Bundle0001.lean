module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.AnnFin
section
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.annFin :
    ∀ {O A T M : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing T] [Algebra O T] [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A →ₐ[O] O) (μ : T →+* Module.End A M), (∀ (o : O) (y : M), μ (algebraMap O T o) y = algebraMap O A o • y) → ∃ I : Ideal T, (∀ t, t ∈ I ↔ ∀ y : M, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A M)) ∧ Module.Finite O (T ⧸ I) := by
  intro O A T M _ _ _ _ _ _ _ _ _ x μ hμ
  classical
  set N : Submodule A M := (RingHom.ker x • ⊤ : Submodule A M) with hN
  have hmap : ∀ (f : Module.End A M) (y : M), y ∈ N → f y ∈ N := by
    intro f y hy
    have h : N.map f ≤ N := by
      rw [hN, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h ⟨y, hy, rfl⟩
  let I : Ideal T :=
    { carrier := {t | ∀ y : M, μ t y ∈ N}
      add_mem' := by
        intro a b ha hb
        have ha' : ∀ y : M, μ a y ∈ N := ha
        have hb' : ∀ y : M, μ b y ∈ N := hb
        show ∀ y : M, μ (a + b) y ∈ N
        intro y
        rw [map_add (f := _), LinearMap.add_apply]
        exact N.add_mem (ha' y) (hb' y)
      zero_mem' := by
        show ∀ y : M, μ 0 y ∈ N
        intro y
        rw [map_zero, LinearMap.zero_apply]
        exact N.zero_mem
      smul_mem' := by
        intro c t ht
        have ht' : ∀ y : M, μ t y ∈ N := ht
        show ∀ y : M, μ (c • t) y ∈ N
        intro y
        rw [smul_eq_mul, map_mul, Module.End.mul_apply]
        exact hmap _ _ (ht' y) }
  refine ⟨I, fun t => Iff.rfl, ?_⟩
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  letI : Module O M := Module.compHom M (algebraMap O A)
  haveI : IsScalarTower O A M := ⟨fun o a m => by
    show (o • a) • m = algebraMap O A o • (a • m)
    rw [Algebra.smul_def, mul_smul]⟩
  let N' : Submodule O M := N.restrictScalars O
  have hspanA : ∀ y : M, y ∈ Submodule.span A (Set.range s) := fun y => hs ▸ Submodule.mem_top
  have hfinQ : Module.Finite O (M ⧸ N') := by
    refine ⟨(Submodule.fg_def).2 ⟨_, Set.finite_range (fun i => N'.mkQ (s i)), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := N'.mkQ_surjective q
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      have hd : a - algebraMap O A (x a) ∈ RingHom.ker x := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
      have he : N'.mkQ (a • z) = x a • N'.mkQ z := by
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
          Submodule.restrictScalars_mem]
        show a • z - algebraMap O A (x a) • z ∈ N
        rw [← sub_smul, hN]
        exact Submodule.smul_mem_smul hd Submodule.mem_top
      rw [he]
      exact Submodule.smul_mem _ _ hz
  let φ : T →ₗ[O] (Fin n → M ⧸ N') :=
    { toFun := fun t i => N'.mkQ (μ t (s i))
      map_add' := by
        intro a b
        funext i
        simp [map_add (f := _)]
      map_smul' := by
        intro o t
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hμ]
        exact N'.mkQ.map_smul o (μ t (s i)) }
  have hker : LinearMap.ker φ ≤ LinearMap.ker (Ideal.Quotient.mkₐ O I).toLinearMap := by
    intro t ht
    rw [LinearMap.mem_ker] at ht ⊢
    have hti : ∀ i, μ t (s i) ∈ N := by
      intro i
      have h1 := congrFun ht i
      change N'.mkQ (μ t (s i)) = 0 at h1
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem] at h1
    have htI : t ∈ I := by
      show ∀ y : M, μ t y ∈ N
      intro y
      refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)
      · rintro _ ⟨i, rfl⟩
        exact hti i
      · rw [map_zero]
        exact N.zero_mem
      · intro a b _ _ ha hb
        rw [map_add (f := _)]
        exact N.add_mem ha hb
      · intro a z _ hz
        rw [LinearMap.map_smul]
        exact N.smul_mem a hz
    show Ideal.Quotient.mkₐ O I t = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact htI
  haveI : Module.Finite O (LinearMap.range φ) := Module.IsNoetherian.finite O _
  haveI : Module.Finite O (T ⧸ LinearMap.ker φ) := Module.Finite.equiv (φ.quotKerEquivRange).symm
  exact Module.Finite.of_surjective ((LinearMap.ker φ).liftQ _ hker) (by
    intro q
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨Submodule.Quotient.mk t, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.ClosedSub
section
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.closedSub :
    ∀ {O T : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] [Algebra O T] (I : Ideal T) [Module.Finite O (T ⧸ I)] (S : Subalgebra O T) (t : T), (∀ N : ℕ, ∃ s ∈ S, t - s ∈ maximalIdeal T ^ N) → ∃ s ∈ S, t - s ∈ I := by
  intro O T _ _ _ _ _ _ I _ S t ht
  let q : T →ₐ[O] T ⧸ I := Ideal.Quotient.mkₐ O I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective O I
  haveI : IsNoetherian O (T ⧸ I) := inferInstance
  haveI : IsNoetherianRing (T ⧸ I) := isNoetherian_of_tower O inferInstance
  haveI : Algebra.IsIntegral O (T ⧸ I) := inferInstance
  set K : Ideal (T ⧸ I) := (maximalIdeal T).map q with hK
  set J : Ideal (T ⧸ I) := (maximalIdeal O).map (algebraMap O (T ⧸ I)) with hJ
  have hKJ : K ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    have hc : (P.comap (algebraMap O (T ⧸ I))).IsMaximal := by
      have h1 : maximalIdeal O ≤ P.comap (algebraMap O (T ⧸ I)) := Ideal.map_le_iff_le_comap.mp hJP
      have h2 : (P.comap (algebraMap O (T ⧸ I))).IsPrime := Ideal.comap_isPrime _ _
      rw [← (maximalIdeal.isMaximal O).eq_of_le h2.ne_top h1]
      exact maximalIdeal.isMaximal O
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P hc
    have h3 : (P.comap q).IsMaximal := Ideal.comap_isMaximal_of_surjective q hq
    have h4 : P.comap q = maximalIdeal T := IsLocalRing.eq_maximalIdeal h3
    rw [hK, Ideal.map_le_iff_le_comap, h4]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hKJ (IsNoetherian.noetherian K)
  let Sb : Submodule O (T ⧸ I) := (Subalgebra.toSubmodule S).map q.toLinearMap
  have hmem : ∀ k : ℕ, Sb.mkQ (q t) ∈ ((maximalIdeal O) ^ k • ⊤ : Submodule O ((T ⧸ I) ⧸ Sb)) := by
    intro k
    obtain ⟨s, hs, hts⟩ := ht (n * k)
    have h1 : q (t - s) ∈ K ^ (n * k) := by
      rw [hK, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hts
    have h2 : q (t - s) ∈ J ^ k := by
      rw [pow_mul] at h1
      first
        | exact Ideal.pow_right_mono hn k h1
        | exact pow_le_pow_left' hn k h1
    have h3 : q (t - s) ∈ ((maximalIdeal O) ^ k • ⊤ : Submodule O (T ⧸ I)) := by
      rw [Ideal.smul_top_eq_map, Ideal.map_pow]
      exact h2
    have h4 : Sb.mkQ (q t) = Sb.mkQ (q (t - s)) := by
      rw [map_sub, map_sub, eq_comm, sub_eq_self]
      exact (Submodule.Quotient.mk_eq_zero Sb).mpr ⟨s, hs, rfl⟩
    have h5 := Submodule.mem_map_of_mem (f := Sb.mkQ) h3
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h5
    rw [h4]
    exact h5
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := O) (M := (T ⧸ I) ⧸ Sb)
    (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
  have h0 : Sb.mkQ (q t) = 0 := by
    have hi : Sb.mkQ (q t) ∈ (⨅ i : ℕ, (maximalIdeal O) ^ i • ⊤ : Submodule O ((T ⧸ I) ⧸ Sb)) :=
      Submodule.mem_iInf _ |>.mpr hmem
    rw [hbot] at hi
    exact hi
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨s, hs, hsq⟩ := h0
  refine ⟨s, hs, ?_⟩
  exact Ideal.Quotient.eq.mp hsq.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.EigKill
section
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill :
    ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (φ : Module.End K V) (k : ℕ) (F : V), F ∈ ⨆ μ : K, φ.eigenspace μ → (φ ^ k) F = 0 → φ F = 0 := by
  intro K V _ _ _ φ k F hF hk
  have hdisj := Module.End.eigenspaces_iSupIndep φ 0
  set S := ⨆ (μ : K) (_ : μ ≠ 0), φ.eigenspace μ with hS
  have hinv : ∀ z ∈ S, φ z ∈ S := by
    have hle : S ≤ S.comap φ := by
      refine iSup₂_le fun μ hμ => ?_
      intro v hv
      rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.1 hv]
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (Submodule.smul_mem _ _ hv))
    exact fun z hz => hle hz
  have hinj : ∀ z ∈ S, φ z = 0 → z = 0 := by
    intro z hz h0
    have hz0 : z ∈ φ.eigenspace 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact h0
    exact Submodule.disjoint_def.1 hdisj z hz0 hz
  have hpow : ∀ n : ℕ, ∀ z ∈ S, (φ ^ n) z = 0 → z = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ h
      simpa using h
    | succ n ih =>
      intro z hz h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hinj z hz (ih _ (hinv z hz) h)
  rw [iSup_split_single _ (0 : K)] at hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
  have hy' : φ y = 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hy
    exact hy
  cases k with
  | zero =>
    have h0 : y + z = 0 := by simpa using hk
    rw [h0, map_zero]
  | succ k =>
    have hyk : (φ ^ (k + 1)) y = 0 := by
      rw [pow_succ, Module.End.mul_apply, hy', map_zero]
    rw [map_add (f := _), hyk, zero_add] at hk
    rw [map_add (f := _), hy', hpow _ z hz hk, map_zero, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.KerSp
section
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.kerSp :
    ∀ {A K M W : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module K W] (Y0 Y : Submodule A M) [Module.Free A Y0] (e : Module.End A Y0), IsIdempotentElem e → Y ≤ Y0 → (∀ y : Y0, (y : M) ∈ Y ↔ e y = y) → ∀ (χ : A →+* K) (sp : M → W), (∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') → (∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f) → (∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i)) → ∀ f : Y, sp f = 0 ↔ f ∈ (RingHom.ker χ • ⊤ : Submodule A Y) := by
  intro A K M W _ _ _ _ _ _ Y0 Y _ e he hYY0 hiff χ sp hadd hsmul hli f
  classical
  have hsp0 : sp 0 = 0 := by
    simpa using hadd 0 Y0.zero_mem 0 Y0.zero_mem
  have hsum : ∀ {ι : Type} (s : Finset ι) (g : ι → M), (∀ i, g i ∈ Y0) →
      sp (∑ i ∈ s, g i) = ∑ i ∈ s, sp (g i) := by
    intro ι s g hg
    induction s using Finset.induction_on with
    | empty => simp [hsp0]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hadd _ (hg a) _ (Y0.sum_mem (fun i _ => hg i)), ih]
  constructor
  · intro h0
    let b := Module.Free.chooseBasis A Y0
    let y0 : Y0 := ⟨f, hYY0 f.2⟩
    have hey : e y0 = y0 := (hiff y0).1 f.2
    have hy0 : y0 = ∑ i ∈ (b.repr y0).support, b.repr y0 i • b i := by
      conv_lhs => rw [← b.linearCombination_repr y0]
      rw [Finsupp.linearCombination_apply]
      rfl
    have hf : (f : M) = ∑ i ∈ (b.repr y0).support, b.repr y0 i • ((b i : Y0) : M) := by
      have h := congrArg (fun z : Y0 => (z : M)) hy0
      rw [show (f : M) = (y0 : M) from rfl]
      refine h.trans ?_
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    have hspf : sp (f : M) = ∑ i ∈ (b.repr y0).support, χ (b.repr y0 i) • sp ((b i : Y0) : M) := by
      rw [hf, hsum _ _ (fun i => Y0.smul_mem _ (b i).2)]
      exact Finset.sum_congr rfl (fun i _ => hsmul _ (b i).2 _)
    rw [h0] at hspf
    have hc : ∀ i ∈ (b.repr y0).support, χ (b.repr y0 i) = 0 :=
      linearIndependent_iff'.1 (hli _ b) _ (fun i => χ (b.repr y0 i)) hspf.symm
    have hz : ∀ i, ((e (b i) : Y0) : M) ∈ Y := fun i =>
      (hiff (e (b i))).2 (by rw [← Module.End.mul_apply, he.eq])
    have hfY : f = ∑ i ∈ (b.repr y0).support, b.repr y0 i • (⟨_, hz i⟩ : Y) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have h1 : (f : M) = ((e y0 : Y0) : M) := by rw [hey]
      rw [h1]
      conv_lhs => rw [hy0]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    rw [hfY]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    exact Submodule.smul_mem_smul ((RingHom.mem_ker).2 (hc i hi)) Submodule.mem_top
  · intro hf
    refine Submodule.smul_induction_on (p := fun g : Y => sp (g : M) = 0) hf ?_ ?_
    · intro r hr y _
      show sp ((r • y : Y) : M) = 0
      rw [Submodule.coe_smul, hsmul _ (hYY0 y.2) r, (RingHom.mem_ker).1 hr, zero_smul]
    · intro y z hy hz
      have hy' : sp (y : M) = 0 := hy
      have hz' : sp (z : M) = 0 := hz
      show sp ((y + z : Y) : M) = 0
      rw [Submodule.coe_add, hadd _ (hYY0 y.2) _ (hYY0 z.2), hy', hz', add_zero]
end

