module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartCut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsSmoothQuotientByWeightedEquations
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem quot_facts {O X R R' : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (W : WPres O X R) (h : W.HasOrigin) (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (hh : IsHomog O W.wt (RingHom.ker (p.comp W.π))) (x' : R' →ₐ[O] O) (hx : x'.comp p = W.origin h) :
    ∃ h' : (W.quot p hp hh).HasOrigin, (W.quot p hp hh).origin h' = x' ∧
      (W.quot p hp hh).part = fun j => (W.part j).map p.toLinearMap := by
  have hq : ∀ f : MvPowerSeries W.σ O, p (W.π f) = 0 → MvPowerSeries.constantCoeff f = 0 := by
    intro f hf
    have h1 := congrArg (fun g => g (W.π f)) hx
    simp only [AlgHom.comp_apply, hf, map_zero, WPres.origin_π] at h1
    exact h1.symm
  refine ⟨hq, ?_, ?_⟩
  · ext y
    obtain ⟨z, rfl⟩ := hp y
    obtain ⟨f, rfl⟩ := W.surj z
    have e1 := WPres.origin_π (W.quot p hp hh) hq f
    have e2 := congrArg (fun g => g (W.π f)) hx
    simp only [AlgHom.comp_apply, WPres.origin_π] at e2
    exact e1.trans e2.symm
  · funext j
    show Submodule.map (p.comp W.π).toLinearMap _ = Submodule.map p.toLinearMap (Submodule.map W.π.toLinearMap _)
    rw [← Submodule.map_comp]
    rfl

private theorem der_sq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
  intro g hg
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
  · rw [RingHom.mem_ker] at ha hb
    rw [hD a b, ha, hb, zero_smul, zero_smul, add_zero]
  · intro a b ha hb
    rw [map_add (f := _), ha, hb, add_zero]

private theorem indep {O A κ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [Fintype κ] (x : A →ₐ[O] O)
    (g : κ → A) (hd : ∀ k, ∃ δ ∈ PtDer x O, δ (g k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (g k') = 0) :
    LinearIndependent O (fun i => (satSq x).mkQ (g i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hs : (satSq x).mkQ (∑ i, c i • g i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [map_smul] using hc
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hs
  obtain ⟨a, ha0, ha⟩ := hs
  obtain ⟨δ, hδ, hk, hk'⟩ := hd k
  have hz := der_sq x δ hδ _ ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum] at hz
  simp only [map_smul, smul_eq_mul] at hz
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hk' j hj, mul_zero]) (by simp)] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h ha0
  · rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hk

private theorem der_desc {O A A' κ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
    (x : A →ₐ[O] O) (g : κ → A) (hg : ∀ k, x (g k) = 0) (p : A →ₐ[O] A') (hp : Function.Surjective p)
    (hk : RingHom.ker p = Ideal.span (Set.range g)) (x' : A' →ₐ[O] O) (hx : x'.comp p = x)
    (δ : A →ₗ[O] O) (hδ : δ ∈ PtDer x O) (h0 : ∀ k, δ (g k) = 0) :
    ∃ δ' ∈ PtDer x' O, ∀ y, δ' (p y) = δ y := by
  have hker : ∀ y, y ∈ Ideal.span (Set.range g) → x y = 0 ∧ δ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact ⟨hg k, h0 k⟩
    | zero => simp
    | add a b _ _ ha hb => simp [ha.1, ha.2, hb.1, hb.2]
    | smul a z _ hz =>
      refine ⟨?_, ?_⟩
      · simp [hz.1]
      · rw [smul_eq_mul, hδ a z, hz.1, hz.2, smul_zero, zero_smul, add_zero]
  have hle : LinearMap.ker p.toLinearMap ≤ LinearMap.ker δ := by
    intro y hy
    have hy' : y ∈ RingHom.ker p := hy
    rw [hk] at hy'
    exact (hker y hy').2
  let e := LinearMap.quotKerEquivOfSurjective p.toLinearMap hp
  let δ' : A' →ₗ[O] O := ((LinearMap.ker p.toLinearMap).liftQ δ hle).comp e.symm.toLinearMap
  have hδ' : ∀ y, δ' (p y) = δ y := by
    intro y
    have : e.symm (p y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [δ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  refine ⟨δ', ?_, hδ'⟩
  intro f g'
  obtain ⟨a, rfl⟩ := hp f
  obtain ⟨b, rfl⟩ := hp g'
  rw [← map_mul, hδ', hδ', hδ', hδ a b]
  have ha : x' (p a) = x a := by rw [← hx]; rfl
  have hb : x' (p b) = x b := by rw [← hx]; rfl
  rw [ha, hb]

theorem UpperTheory.exists_smooth_quotient_by_weighted_equations :
    ∀ (O X : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] (P : Type) [CommRing P] [Algebra O P] [IsCO O P] (W : WPres O X P) (h : W.HasOrigin) (n : X → ℕ), SmoothPt W.part (W.origin h) n → ∀ (κ : Type) [Fintype κ] (g : κ → P) (w : κ → X), (∀ k, g k ∈ W.part (w k) ∧ W.origin h (g k) = 0) → (∀ k, ∃ δ ∈ PtDer (W.origin h) O, δ (g k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (g k') = 0) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (_ : IsDomain R) (q : P →ₐ[O] R) (W' : WPres O X R) (h' : W'.HasOrigin) (n' : X → ℕ), Function.Surjective q ∧ (∀ s, ∃ s', W'.wt s = W.wt s') ∧ (∀ j, W'.part j = (W.part j).map q.toLinearMap) ∧ (W'.origin h').comp q = W.origin h ∧ (∀ k, q (g k) = 0) ∧ (∀ δ ∈ PtDer (W.origin h) O, (∀ k, δ (g k) = 0) → ∀ y, q y = 0 → δ y = 0) ∧ SmoothPt W'.gr (W'.originA h') n' ∧ ∀ j, n' j + Nat.card {k // w k = j} = n j := by
  intro O X _ _ _ _ _ _ _ _ _ P _ _ _ W h n hs κ _ g w hgw hd
  classical
  obtain ⟨τ, _, wt0, φ, hc, hn⟩ := hs
  set I : Ideal P := Ideal.span (Set.range g) with hI
  have hIx : ∀ a ∈ I, W.origin h a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (W.origin h) := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hgw k).2
    exact hle ha
  let p : P →ₐ[O] P ⧸ I := Ideal.Quotient.mkₐ O I
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective O I
  have hpker : RingHom.ker p = Ideal.span (Set.range g) := by
    rw [← hI]
    exact Ideal.Quotient.mkₐ_ker O I
  let x' : P ⧸ I →ₐ[O] O := Ideal.Quotient.liftₐ I (W.origin h) hIx
  have hx' : x'.comp p = W.origin h := by
    ext y
    rfl
  have hli := indep (W.origin h) g hd
  obtain ⟨τ', _, wt', φ', hc', hn'⟩ :=
    chart_cut O P X W.part (W.origin h) τ wt0 φ hc κ g w hgw hli (P ⧸ I) p x' hp hpker hx'
  have hgA : ∀ k, (⟨g k, W.part_le_A (hgw k).1⟩ : W.A) ∈ W.gr (w k) := fun k => (hgw k).1
  obtain ⟨hhom, -⟩ := homog_span O P X W κ (fun k => ⟨g k, W.part_le_A (hgw k).1⟩) w hgA
  have hh1 : IsHomog O W.wt (RingHom.ker (p.comp W.π)) := by
    have e : RingHom.ker (p.comp W.π) = Ideal.comap W.π (Ideal.span (Set.range fun k => g k)) := by
      ext f
      simp [p, Ideal.Quotient.eq_zero_iff_mem, hI]
    rw [e]
    exact hhom
  obtain ⟨h1, ho1, hpart1⟩ := quot_facts W h p hp hh1 x' hx'
  set W1 := W.quot p hp hh1 with hW1
  have hc1 : IsChart W1.part (W1.origin h1) wt' φ' := by
    rw [ho1, hpart1]
    exact hc'
  obtain ⟨hprime, hhom1, hkle, hdk, hdesc⟩ := chart_ker O X (P ⧸ I) W1 h1 τ' wt' φ' hc1
  set J : Ideal (P ⧸ I) := RingHom.ker φ' with hJ
  have hJx : ∀ a ∈ J, x' a = 0 := by
    intro a ha
    have := hkle ha
    rw [ho1] at this
    exact this
  let p2 : P ⧸ I →ₐ[O] (P ⧸ I) ⧸ J := Ideal.Quotient.mkₐ O J
  have hp2 : Function.Surjective p2 := Ideal.Quotient.mkₐ_surjective O J
  let x'' : (P ⧸ I) ⧸ J →ₐ[O] O := Ideal.Quotient.liftₐ J x' hJx
  let φ'' : (P ⧸ I) ⧸ J →ₐ[O] MvPowerSeries τ' (FractionRing O) :=
    Ideal.Quotient.liftₐ J φ' (fun a ha => ha)
  have hx'' : x''.comp p2 = W1.origin h1 := by
    rw [ho1]
    ext y
    rfl
  have hφ'' : φ''.comp p2 = φ' := by
    ext y
    rfl
  have hc2 := hdesc ((P ⧸ I) ⧸ J) p2 x'' φ'' hp2 hx'' hφ''
  have hh2 : IsHomog O W1.wt (RingHom.ker (p2.comp W1.π)) := by
    have e : RingHom.ker (p2.comp W1.π) = RingHom.ker (φ'.comp W1.π) := by
      ext f
      simp [p2, Ideal.Quotient.eq_zero_iff_mem, hJ]
    rw [e]
    exact hhom1
  obtain ⟨h2, ho2, hpart2⟩ := quot_facts W1 h1 p2 hp2 hh2 x'' hx''
  set W2 := W1.quot p2 hp2 hh2 with hW2
  have hc3 : IsChart W2.part (W2.origin h2) wt' φ'' := by
    rw [ho2, hpart2]
    exact hc2
  have hgr := chart_gr O X ((P ⧸ I) ⧸ J) W2 h2 τ' wt' φ'' hc3
  haveI : J.IsPrime := hprime
  let q : P →ₐ[O] (P ⧸ I) ⧸ J := p2.comp p
  have hq : Function.Surjective q := hp2.comp hp
  have hpartq : ∀ j, W2.part j = (W.part j).map q.toLinearMap := by
    intro j
    rw [hpart2, hpart1]
    show _ = Submodule.map (p2.toLinearMap.comp p.toLinearMap) _
    rw [Submodule.map_comp]
  refine ⟨(P ⧸ I) ⧸ J, inferInstance, inferInstance, co_quot O P _ q hq, inferInstance, q, W2, h2,
    fun j => Nat.card {i // wt' i = j}, hq, fun s => ⟨s, rfl⟩, hpartq, ?_, ?_, ?_,
    ⟨τ', inferInstance, wt', _, hgr, fun j => rfl⟩, ?_⟩
  · rw [ho2]
    ext y
    rfl
  · intro k
    show p2 (p (g k)) = 0
    have : p (g k) = 0 := by
      show Ideal.Quotient.mk I (g k) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.subset_span ⟨k, rfl⟩
    rw [this, map_zero]
  · intro δ hδ h0 y hy
    obtain ⟨δ', hδ'mem, hδ'⟩ := der_desc (W.origin h) g (fun k => (hgw k).2) p hp hpker x' hx' δ hδ h0
    rw [← hδ' y]
    have hJy : p y ∈ J := by
      have : p2 (p y) = 0 := hy
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    apply hdk δ' (by rw [ho1]; exact hδ'mem) (p y) hJy
  · intro j
    rw [← hn j]
    exact hn' j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.FgMapMk
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem fg_map_mk {O A S : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing S]
    [Algebra O S] (f : A →ₐ[O] S) (I : Ideal A) (hI : ∀ a, f a = 0 ↔ a ∈ I) (P : Submodule O A) (T : Submodule O S)
    (hT : T.FG) (hP : ∀ a ∈ P, f a ∈ T) : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).FG := by
  have hIf : ∀ a ∈ I, f a = 0 := fun a ha => (hI a).mpr ha
  let g : A ⧸ I →ₐ[O] S := Ideal.Quotient.liftₐ I f hIf
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hI a).mp hy
  haveI : IsNoetherian O T := isNoetherian_of_fg_of_noetherian T hT
  have hle : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).map g.toLinearMap ≤ T := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hP a ha
  exact Submodule.fg_of_fg_map_injective g.toLinearMap hg (isNoetherian_submodule.mp inferInstance _ hle)

theorem UpperTheory.V.GradeZeroInterpolatingElement.m2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → M2 M.gr M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hF
  obtain ⟨h1, -, h3⟩ := kerA D hD M
  have hs := spanMono D hD M hF 0
  have hfin := hF M.S M.ru M.pt
  have hT : (Subalgebra.toSubmodule (Algebra.adjoin c.O (mono M.ru.hom 0))).FG :=
    Module.Finite.iff_fg.1 hfin
  refine fg_map_mk (M.SS.val.comp M.toSS) _ (fun a => ?_) _ _ hT (fun a ha => ?_)
  · rw [← h1 a]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have h4 : (M.toSS a).1 ∈ M.sPart 0 := h3 0 a ha
    rw [hs] at h4
    exact Algebra.span_le_adjoin _ _ h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ ξ' : M.SS →ₐ[c.O] K), M.rep ξ = M.rep ξ' → ξ = ξ' := by
  intro Ω _ _ _ l _ c D hD M h0 K _ _ ξ ξ' hrep
  have hent : ∀ g i j, ξ (M.ent g i j) = ξ' (M.ent g i j) := by
    intro g i j
    have := congrArg (fun r => r g i j) hrep
    simpa [Model.rep, mapRep, Model.rS, RingHom.mapMatrix_apply] using this
  let Q : Subalgebra c.O M.S := (AlgHom.equalizer ξ ξ').map M.SS.val
  have hQent : ∀ g i j, M.ru.hom g i j ∈ Q := by
    intro g i j
    exact ⟨M.ent g i j, hent g i j, rfl⟩
  have hQmono : ∀ w, mono M.ru.hom w ⊆ (Q : Set M.S) := by
    intro w y hy
    obtain ⟨L, -, rfl⟩ := hy
    apply Subalgebra.list_prod_mem
    intro z hz
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact hQent _ _ _
  have hle : (⨆ j, M.sPart j) ≤ Subalgebra.toSubmodule Q := by
    refine iSup_le fun w => ?_
    rw [spanMono D hD M h0 w, Submodule.span_le]
    exact hQmono w
  apply AlgHom.ext
  intro x
  have hx : (x : M.S) ∈ ⨆ j, M.sPart j := x.2
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pts_wv {K : Type} [CommRing K] (t : Multiplicative (ℤ × ℤ) →* Kˣ) (w : ℤ × ℤ) :
    wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w = t (Multiplicative.ofAdd w) := by
  obtain ⟨a, b⟩ := w
  have h : Multiplicative.ofAdd ((a, b) : ℤ × ℤ) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ^ a * Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ^ b := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_zpow, toAdd_mul, Prod.ext_iff]
  rw [h, map_mul, map_zpow, map_zpow]
  rfl

private theorem pts_abs {O S K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S] [IsCO O S] [Field K] [IsAlgClosed K] [Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (W : WPres O (ℤ × ℤ) S) (hz : ∀ i, W.z i ∈ maximalIdeal S)
    (A B : Subalgebra O S) (hA : W.A = A) [Module.Finite O B] (hB : W.part 0 ≤ B.toSubmodule) (ξ : A →ₐ[O] K) :
    ∃ (t : Kˣ × Kˣ) (y : S →ₐ[O] K), ∀ w, ∀ x : A, (x : S) ∈ W.part w → y x = (wv t w : K) * ξ x := by
  subst hA
  have hB' : IsNoetherian O B.toSubmodule := by
    have : IsNoetherian O B := isNoetherian_of_isNoetherianRing_of_finite O B
    exact this
  have hP : IsNoetherian O (W.part 0) := isNoetherian_of_le hB
  have hG : (W.gr 0).FG := by
    apply Submodule.fg_of_fg_map_injective W.A.val.toLinearMap Subtype.val_injective
    have hle : Submodule.map W.A.val.toLinearMap (W.gr 0) ≤ W.part 0 := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    first
      | exact isNoetherian_submodule.mp hP _ hle
      | exact isNoetherian_submodule'.mp hP _ hle
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite O (ℤ × ℤ) S W hz K ξ (hG.map _)
  refine ⟨(t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))), Ξ, ?_⟩
  intro w x hx
  have hx' : x ∈ W.gr w := hx
  have h1 := act_of_mem W.gr t ξ hx'
  rw [← hΞ] at h1
  rw [pts_wv]
  exact h1

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptScale :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ∃ t r, D.EPt r ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
  intro Ω _ _ _ l _ c D hD M hF ξ
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨hinj, -, -, hcomp, -⟩ := dvrFacts l c.O
  haveI : Algebra.IsAlgebraic ℤ_[l] ℚ_[l] := IsLocalization.isAlgebraic ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) := Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.extendScalars hinj
  obtain ⟨-, -, WS, hWS, hz⟩ := sInternal D hD M
  have hpart : WS.part = M.sPart := funext hWS
  have hA : WS.A = M.SS := by
    simp only [WPres.A, Model.SS, hpart]
  haveI hfin : Module.Finite c.O (Algebra.adjoin c.O (mono M.ru.hom 0)) := hF M.S M.ru M.pt
  have hB : WS.part 0 ≤ (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule := by
    rw [hWS, spanMono D hD M hF 0, Submodule.span_le]
    exact Algebra.subset_adjoin
  obtain ⟨t, y, hy⟩ := pts_abs WS hz M.SS _ hA hB ξ
  refine ⟨t, mapRep (y : M.S →+* PadicAlgCl l) M.ru.hom, ⟨M.S, _, _, _, M.ru, y, M.pt, rfl⟩, ?_⟩
  intro g
  ext i j
  have h := hy (wt i j) (M.ent g i j) (by rw [hWS]; exact M.entry_mem g i j)
  have e : ((M.ent g i j : M.SS) : M.S) = M.ru.hom g i j := rfl
  rw [e] at h
  simpa [tconj, Model.rep, mapRep, Model.rS] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SmoothPtPartOfSmoothPtAssociatedGraded
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private lemma order_pow {O A K τ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [Algebra O K]
    (x : A →ₐ[O] O) (φ : A →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, MvPowerSeries.constantCoeff (φ f) = algebraMap O K (x f)) (n : ℕ) :
    ∀ g ∈ RingHom.ker x ^ n, (n : ℕ∞) ≤ (φ g).order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
    · rw [RingHom.mem_ker] at hb
      rw [map_mul]
      refine le_trans ?_ MvPowerSeries.le_order_mul
      push_cast
      refine add_le_add (ih a ha) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 ?_)
      rw [hc, hb, map_zero]
    · intro a b ha hb
      rw [map_add (f := _)]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

private lemma extend {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (A : Subalgebra O R) (q : Ideal R) (φ : A →ₐ[O] MvPowerSeries τ K)
    (ho : ∀ (n : ℕ) (y : A), (y : R) ∈ q ^ n → (n : ℕ∞) ≤ (φ y).order)
    (ha : ∀ (n : ℕ) (x : R), ∃ y : A, x - y ∈ q ^ n) :
    ∃ ψ : R →ₐ[O] MvPowerSeries τ K, ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y) := by
  classical
  choose a ha using ha
  let ψ : R → MvPowerSeries τ K := fun x m => MvPowerSeries.coeff m (φ (a (m.degree + 1) x))
  have spec : ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y) := by
    intro n x y hy m hm
    show MvPowerSeries.coeff m (φ (a (m.degree + 1) x)) = _
    have h1 : x - y ∈ q ^ (m.degree + 1) := Ideal.pow_le_pow_right hm hy
    have h2 : ((a (m.degree + 1) x - y : A) : R) ∈ q ^ (m.degree + 1) := by
      have := Ideal.sub_mem _ h1 (ha (m.degree + 1) x)
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have h3 : MvPowerSeries.coeff m (φ (a (m.degree + 1) x - y)) = 0 := by
      refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (ho _ _ h2))
      exact_mod_cast Nat.lt_succ_self _
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  have onA : ∀ y : A, ψ y = φ y := fun y => by
    ext m
    exact spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)
  have hadd : ∀ x x', ψ (x + x') = ψ x + ψ x' := fun x x' => by
    ext m
    have hm := Nat.lt_succ_self m.degree
    rw [map_add (f := _), spec _ x _ (ha _ x) m hm, spec _ x' _ (ha _ x') m hm, ← map_add (f := _), ← map_add (f := _)]
    refine spec _ _ _ ?_ m hm
    have := Ideal.add_mem _ (ha (m.degree + 1) x) (ha (m.degree + 1) x')
    rw [sub_add_sub_comm] at this
    exact this
  have hmul : ∀ x x', ψ (x * x') = ψ x * ψ x' := fun x x' => by
    ext m
    have hm := Nat.lt_succ_self m.degree
    have h1 : x * x' - ((a (m.degree + 1) x * a (m.degree + 1) x' : A) : R) ∈ q ^ (m.degree + 1) := by
      have := Ideal.add_mem _ (Ideal.mul_mem_right x' _ (ha (m.degree + 1) x))
        (Ideal.mul_mem_left _ (a (m.degree + 1) x : R) (ha (m.degree + 1) x'))
      convert this using 1
      push_cast
      ring
    rw [spec _ _ _ h1 m hm, map_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h2 : p.1.degree + p.2.degree = m.degree := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add (f := _)]
    rw [spec _ x _ (ha (m.degree + 1) x) p.1 (by omega), spec _ x' _ (ha (m.degree + 1) x') p.2 (by omega)]
  refine ⟨{ toFun := ψ
            map_one' := (onA 1).trans (map_one φ)
            map_mul' := hmul
            map_zero' := (onA 0).trans (map_zero φ)
            map_add' := hadd
            commutes' := fun c => (onA (algebraMap O A c)).trans (φ.commutes c) }, spec⟩

theorem UpperTheory.smoothPt_part_of_smoothPt_associatedGraded :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (n : X → ℕ), SmoothPt W.gr (W.originA h) n → SmoothPt W.part (W.origin h) n := by
  rintro O X R _ _ _ _ _ _ _ _ W h n ⟨τ, fτ, wt, φ, H, hn⟩
  obtain ⟨ψ, spec⟩ := extend W.A (RingHom.ker (W.origin h)) φ
    (fun k y hy => order_pow (W.originA h) φ H.const k y (by
      rw [← (ker_pow O R X W h k).1]
      exact hy))
    (fun k => (ker_pow O R X W h k).2)
  have onA : ∀ y : W.A, ψ y = φ y := fun y => by
    ext m
    exact spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)
  obtain ⟨h1, h2⟩ := ker_pow O R X W h 2
  have hx : ∀ (f : R) (y : W.A), f - y ∈ RingHom.ker (W.origin h) ^ 2 → W.origin h f = W.originA h y := by
    intro f y hy
    have := Ideal.pow_le_self (two_ne_zero) hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  refine ⟨τ, fτ, wt, ψ, ⟨fun j f hf => ?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩, hn⟩
  · have := H.graded j ⟨f, W.part_le_A hf⟩ hf
    rw [← onA] at this
    exact this
  · obtain ⟨y, hy⟩ := h2 f
    rw [hx f y hy, ← H.const, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact spec 2 f y hy 0 (by simp)
  · obtain ⟨f, hf, hf'⟩ := H.onto i
    rw [← onA] at hf hf'
    exact ⟨f, hf, hf'⟩
  · obtain ⟨y, hy⟩ := h2 f
    obtain ⟨c, hc, hcy⟩ := H.inj y ((hx f y hy).symm.trans hf) (fun i => by
      rw [← spec 2 f y hy _ (by rw [Finsupp.degree_single]; norm_num)]
      exact hl i)
    rw [← h1] at hcy
    have h3 : c • (y : R) ∈ RingHom.ker (W.origin h) ^ 2 := hcy
    refine ⟨c, hc, ?_⟩
    have h4 := Ideal.add_mem _ (Submodule.smul_of_tower_mem _ c hy) h3
    rwa [← smul_add, sub_add_cancel] at h4
end

