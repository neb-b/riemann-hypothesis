module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SpaceEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CmplEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ConeCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientSurjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MapAdjAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DefEx
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.defEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → Φ.noMu.Std l a ∧ Φ.noMu.IsRes ((residue Λ).comp a) c ∧ ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (P : PD Φ.ι Γ R), Φ.noMu.IsDef a c P := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS c hc
  haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  have hok : Φ.noMu.Ok ((residue Λ).comp a) :=
    ⟨hS.ok.mul, hS.ok.kill, hS.ok.dist, hS.ok.two, hS.ok.lc⟩
  have hS' : Φ.noMu.Std l a :=
    ⟨hok, hS.char, hS.cont, hS.phi, hS.closed, hS.phiv, fun _ _ hs => hs.elim⟩
  have hpair : ∀ {R : Type} [CommRing R] (b : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair b P → Φ.noMu.IsPair b P :=
    fun b P h => ⟨h.mult, h.kill, h.nrm, h.low, h.flag, fun _ _ hs => hs.elim⟩
  have hc' : Φ.noMu.IsRes ((residue Λ).comp a) c :=
    ⟨hpair _ c hc.pair, ⟨hc.res.diag, hc.res.char, hc.res.shape⟩, hc.cont⟩
  refine ⟨hS', hc', ?_⟩
  obtain ⟨X⟩ := spaceEx Φ.noMu l a hS'
  have hid : ∀ x : ResidueField Λ, res Λ (ResidueField Λ) x = x := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    exact (res Λ (ResidueField Λ)).commutes y
  have hmap : c.map ↑(res Λ (ResidueField Λ)) = c := by
    apply PD.ext
    · ext g i j
      simp [PD.map, mapRep, hid]
    · funext v
      ext i j
      simp [PD.map, hid]
  have hmax : maximalIdeal (ResidueField Λ) = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  have hlift : Φ.noMu.Lifts a c c := ⟨hc'.pair, by rw [hmax]; exact hc.cont, hmap⟩
  obtain ⟨x, hx⟩ := X.univ (ResidueField Λ) c c hc' hlift
  have hres : Φ.noMu.IsRes ((residue Λ).comp a) (X.P.map ↑x) := by rw [hx]; exact hc'
  obtain ⟨R, i1, i2, i3, f, hdef, -, -⟩ := cmplEx Φ.noMu l a hS' X x hres
  rw [hx] at hdef
  exact ⟨R, i1, i2, i3, X.P.map ↑f, hdef⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExAbove
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem sum_deg (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] {V : Type} [Fintype V]
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal) :
    ∑ v, locDeg (pl v) ≤ Module.finrank ℚ F := by
  classical
  have hl : l.Prime := Fact.out
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 F)
  rw [RingOfIntegers.rank] at hsum
  have hover : ∀ v, (pl v).asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) := fun v => by
    refine ⟨(pl v).isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ (pl v).isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hm v
  let e : V → (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) := fun v => ⟨(pl v).asIdeal, hover v⟩
  have he : Function.Injective e := fun a b h => hi (HeightOneSpectrum.ext (congrArg Subtype.val h))
  rw [← hsum]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩)))
  rw [Finset.sum_map]
  rfl

private theorem cc_ex {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (w : InfinitePlace F) : ∃ c : G F Ω, IsCCAt w c := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois F Ω := {}
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
  let cj : ℂ →ₐ[F] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  refine ⟨(cj.comp j).restrictNormal' Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
  · rw [show j.toRingHom.comp (algebraMap F Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
    exact w.mk_embedding

private theorem contAct {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup G] (ρ : Representation k G M)
    (h : IsOpen (ρ.ker : Set G)) : ContAction ρ := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (ρ.ker : Set G), h.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have hx' : ρ (g⁻¹ * x) = 1 := hx
  have : ρ x = ρ g := by rw [← mul_inv_cancel_left g x, map_mul, hx', mul_one]
  simp only [this]

private theorem ex_above (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] :
    ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hl : l.Prime := Fact.out
  haveI : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  obtain ⟨P, hP, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(l : ℤ)})
  have hm : ((l : ℕ) : 𝓞 F) ∈ P := by
    have : (l : ℤ) ∈ P.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP.isPrime, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.ne_zero (by exact_mod_cast hm)

theorem UpperTheory.V.Ws.X1.ecG :
    GC.Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GC.GLink l S K π → (∀ w ∈ S, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → ∀ (V : Type) (ι : V ≃ S) (A : V → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) (ι v).1) → ∀ (k W : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup W] [Module k W] [Module.Finite k W] (ρ : Representation k Γ W) (b : V → Submodule k W) (m e : ℕ), IsOpen (ρ.ker : Set Γ) → (∀ v, ∀ s ∈ Dec (F := F) (A v), ∀ X ∈ b v, ρ (π s) X ∈ b v) → (∀ f : W →ₗ[k] k, (∀ g X, f (ρ (π g) X) = (GC.cycF F Ω l k g : k) * f X) → f = 0) → (∀ v, Module.finrank k (b v) = m) → (∀ g : G F Ω, IsCC g → Module.finrank k (LinearMap.ker (ρ (π g) - 1)) ≤ e) → Module.Finite k (Fr.coneH2 (fun v => π.comp (Dec (F := F) (A v)).subtype) ρ b) ∧ Module.finrank k (Fr.coneH2 (fun v => π.comp (Dec (F := F) (A v)).subtype) ρ b) + Module.finrank k (Fr.coneH0 ρ b) + Module.finrank ℚ F * m ≤ Module.finrank k (Fr.H1C (fun v => π.comp (Dec (F := F) (A v)).subtype) ρ b) + Module.finrank ℚ F * e := by
  intro hP F Ω _ _ _ _ _ l _ hF S K Γ _ _ _ _ _ _ π hg honly V ι A hA k W _ _ _ _ _ _ ρ b m e hop hb hdual hm he
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  letI : Fintype V := Fintype.ofEquiv S ι.symm
  letI : TopologicalSpace W := ⊥
  haveI : DiscreteTopology W := ⟨rfl⟩
  letI : ∀ v, TopologicalSpace (W ⧸ b v) := fun _ => ⊥
  haveI : ∀ v, DiscreteTopology (W ⧸ b v) := fun _ => ⟨rfl⟩
  haveI : ∀ v, CompactSpace (Dec (F := F) (A v)) := fun v =>
    isCompact_iff_compactSpace.1 (isClosed_Dec (A v)).isCompact
  have hρ : ContAction ρ := contAct ρ hop
  choose c hc using fun w : InfinitePlace F => cc_ex (Ω := Ω) w
  have hA' : ∀ w : S, IsPlaceOver (A (ι.symm w)) w.1 := fun w => by simpa using hA (ι.symm w)
  have hD : Loc.H0dual (GC.cycF F Ω l k) (ρ.comp π) = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun f hf => hdual f hf
  let d : ∀ v, Dec (F := F) (A v) →* Γ := fun v => π.comp (Dec (F := F) (A v)).subtype
  have hdc : ∀ v, Continuous (d v) := fun v => hg.cont.comp continuous_subtype_val
  let τ : ∀ v, Representation k (Dec (F := F) (A v)) (W ⧸ b v) := fun v =>
    Representation.quotient (ρ.comp (d v)) (b v) fun g X hX => hb v g.1 g.2 X hX
  have hτq : ∀ v s m, (b v).mkQ (ρ (d v s) m) = τ v s ((b v).mkQ m) := fun _ _ _ => rfl
  have hτ : ∀ v, ContAction (τ v) := fun v => by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨m, rfl⟩ := (b v).mkQ_surjective m
    exact (continuous_of_discreteTopology (f := (b v).mkQ)).comp (hρ.comp ((hdc v).prodMk continuous_const))
  have hE := fun v => GC.locEuler hP.lf hP.lt hP.le F Ω l (ι v).1 (A v) (hA v) k (W ⧸ b v) (τ v) (hτ v)
  obtain ⟨f1, f2, -⟩ := GC.H2_galois_quotient_eq hP F Ω l hF S K Γ π hg k W ρ hρ _ hc _ hA'
  have hO := GC.H2_galois_quotient_surjective hP F Ω l hF S K Γ π hg k W ρ hρ _ hc _ hA' hD (fun w => W ⧸ b (ι.symm w))
    (fun w => τ (ι.symm w)) (fun w => (b (ι.symm w)).mkQ) (fun w => hτq (ι.symm w))
    fun w => (b (ι.symm w)).mkQ_surjective
  have hC := GC.coneCount l Γ V (fun v => Dec (F := F) (A v)) d hdc k W ρ hρ (fun v => W ⧸ b v) τ
    (fun v => (b v).mkQ) hτq (fun v => (b v).mkQ_surjective) f1 f2 fun v => (hE v).1
  have hbq : (fun v => LinearMap.ker (b v).mkQ) = b := funext fun v => Submodule.ker_mkQ _
  rw [hbq] at hC
  obtain ⟨-, g2, hC⟩ := hC
  refine ⟨g2, ?_⟩
  have hK := Submodule.finrank_mono (s := ⨅ v, LinearMap.ker (compatiblePairH2 ρ (τ v) (d v) (hdc v) (b v).mkQ
      continuous_of_discreteTopology (hτq v)))
    (t := ⨅ w : S, LinearMap.ker (compatiblePairH2 ρ (τ (ι.symm w)) (π.comp (Dec (F := F) (A (ι.symm w))).subtype)
      (hdc (ι.symm w)) (b (ι.symm w)).mkQ continuous_of_discreteTopology (hτq (ι.symm w))))
    (le_iInf fun w => iInf_le _ (ι.symm w))
  have s2 : ∑ w : S, Module.finrank k (H2 (τ (ι.symm w))) = ∑ v, Module.finrank k (H2 (τ v)) :=
    ι.symm.sum_comp fun v => Module.finrank k (H2 (τ v))
  have sR : ∑ w : InfinitePlace F, Module.finrank k (LinearMap.ker (ρ (π (c w)) - 1)) ≤ Module.finrank ℚ F * e := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun w : InfinitePlace F => Module.finrank k (LinearMap.ker (ρ (π (c w)) - 1))) e
      fun w _ => he _ (by obtain ⟨j, hj, -⟩ := hc w; exact ⟨j, hj⟩)
    refine this.trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank]
    omega
  obtain ⟨w0, hw0⟩ := ex_above l F
  obtain ⟨q, hq⟩ : ∃ q, q + m = Module.finrank k W :=
    ⟨_, by rw [← hm (ι.symm ⟨w0, hg.above _ hw0⟩)]; exact Submodule.finrank_quotient_add_finrank _⟩
  have hloc : ∀ v, Module.finrank k (H1 (τ v)) = Module.finrank k (H0 (τ v)) + Module.finrank k (H2 (τ v)) + locDeg (ι v).1 * q := fun v => by
    have a1 := (b v).finrank_quotient_add_finrank
    rw [hm v, ← hq] at a1
    rw [(hE v).2.2.1 (honly _ (ι v).2), Nat.add_right_cancel a1]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun v _ => hloc v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hdeg := Nat.mul_le_mul_right q (sum_deg l F (fun v => (ι v).1)
    (fun x y h => ι.injective (Subtype.ext h)) fun v => honly _ (ι v).2)
  rw [s2, ← hq, mul_add] at hO
  change Module.finrank k (Fr.coneH2 d ρ b) + _ + _ ≤ Module.finrank k (Fr.H1C d ρ b) + _
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ObWeak
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ex_mu {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A] (η : A)
    (hη : ∀ x ∈ maximalIdeal A, x * η = 0) :
    ∃ μ : ResidueField O →+ A, (∀ a : O, μ (residue O a) = a • η) ∧ ∀ (a : A) c, μ (res O A a * c) = a * μ c := by
  have k : ∀ a b : O, residue O a = residue O b → a • η = b • η := fun a b h => by
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    refine hη _ ?_
    rw [← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]
  choose s hs using residue_surjective (R := O)
  have k2 : ∀ a : O, s (residue O a) • η = a • η := fun a => k _ _ (hs _)
  refine ⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩
  · rw [← add_smul]
    exact k _ _ (by rw [map_add (f := _), hs, hs, hs])
  · obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
    have e : res O A a = residue O b := by
      have := (res_eq_zero_iff O A _).2 hb
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
    have e2 : a * η = b • η := by
      have := hη _ hb
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at this
    show s _ • η = a * (s c • η)
    rw [mul_smul_comm, e2, smul_smul]
    exact k _ _ (by rw [map_mul, hs, hs, e, mul_comm])

private theorem mmap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

private theorem smap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A - B).map f = A.map f - B.map f := by
  ext i j
  simp

private theorem amap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A : M4 R) : (adj A).map f = adj (A.map f) := by
  ext i j
  rw [Matrix.map_apply, adj_apply, adj_apply, map_zsmul, Matrix.map_apply]

theorem UpperTheory.V.Ws.X1.obWeak :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → Obs Λ R (Fr.coneH2 loc (adSp rb hb) fun v => bor (nb v)) fun A' _ _ _ q => Function.Surjective q ∧ maximalIdeal A' * RingHom.ker q = ⊥ ∧ WLift loc ν r n q := by
  intro O _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc R _ _ _ ν r n hν hw hr rb nb hb hrb hnb A _ _ _ p hp hs κ _ ε hK hind
  classical
  obtain ⟨D, hD⟩ := X1.slEx h2 loc hloc p hp hs ν r n hν hw hr
  obtain ⟨co, k1, k2, k4⟩ := X1.coefEx (RingHom.ker p) hs κ ε hK hind
  choose z z0 z1 z2 using fun u : κ =>
    X1.obCoc loc hloc p hp hs ν r n hν hw hr rb nb hb hrb hnb D (co u) (k1 u) (k2 u)
  have d1 : ∀ s t, (D.om s t).map p = 0 := fun s t => by
    rw [SL.om, smap, mmap, D.rt_map, D.rt_map, D.rt_map, map_mul, sub_self]
  have d2 : ∀ v s, (D.de v s).map p = 0 := fun v s => by
    have e1 : adj (n v) * n v = 1 := by
      have := hw.sp v
      rwa [IsGSp, one_smul] at this
    have e2 : n v * adj (n v) = 1 := mul_eq_one_comm.1 e1
    rw [SL.de, smap, mmap, mmap, amap, D.rt_map, D.nt_map, D.t_map, ← mul_assoc, ← mul_assoc, e2, one_mul,
      mul_assoc, e2, mul_one, sub_self]
  refine ⟨fun u => Submodule.Quotient.mk ⟨z u, z0 u⟩, ?_⟩
  intro c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1
  have hx : ∑ u, residue O (c u) • z u ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)) := by
    have h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) •
        (⟨z u, z0 u⟩ : Fr.continuousCocycles2 loc (adSp rb hb) (fun v => bor (nb v)))) :
        Fr.coneH2 loc (adSp rb hb) (fun v => bor (nb v))) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, ← Submodule.mkQ_apply, map_sum]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum] at h1
    exact h1
  obtain ⟨μ, m1, m2⟩ := ex_mu (O := O) η hη
  have pp : ∀ x, p'' (p' x) = p x := fun x => DFunLike.congr_fun hpp x
  have key : ∀ x, p x = 0 → p' x = μ (∑ u, residue O (c u) * co u x) := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := k4 x hx
    have : ∑ u, residue O (c u) * co u x = residue O (∑ u, a u * c u) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]
    rw [this, m1, Finset.sum_smul]
    conv_lhs => rw [hxa]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, e1, mul_smul]
  have keyM : ∀ (M : M4 A) (Y : κ → sp4 (ResidueField O)) (g : M4 (ResidueField O)),
      M.map p = 0 → (∀ u, (Y u).1 * g = M.map (co u)) →
      M.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ := fun M Y g h1 h3 => by
    ext a b
    have h4 : p (M a b) = 0 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply, key _ h4, Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Submodule.coe_smul, smul_mul_assoc, h3]
    rfl
  have m3 : ∀ d, p'' (μ d) = 0 := fun d => by
    obtain ⟨a, rfl⟩ := residue_surjective d
    rw [m1, map_smul, hη0, smul_zero]
  have hp'' : Function.Surjective p'' := fun y => by
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p' x, pp x⟩
  have hs' : maximalIdeal A' * RingHom.ker p'' = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨y, rfl⟩ := hp' y
    rw [RingHom.mem_ker, pp] at hy
    rw [Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]
  obtain ⟨D', f1, f2⟩ := hD A' p' p'' hpp
  refine ⟨hp'', hs', X1.obCor loc hloc p'' hp'' hs' ν r n hν hw hr rb nb hb hrb hnb D' μ μ.map_add m2 m3 _ hx
    (fun s t => ?_) (fun v s => ?_)⟩
  · rw [f1, keyM _ (fun u => (z u).1 (s, t)) _ (d1 s t) fun u => z1 u s t, Prod.fst_sum, Finset.sum_apply]
    rfl
  · rw [f2, keyM _ (fun u => (z u).2 v s) _ (d2 v s) fun u => z2 u v s, Prod.snd_sum, Finset.sum_apply,
      Finset.sum_apply]
    rfl
end

