module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfTraceTranslationInvariantSemisimple
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

theorem UpperTheory.eq_one_of_trace_translation_invariant_semisimple :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ : Γ →* GL (Fin n) k), Formalism.MainNotions.N.IsSSRep ρ → ∀ g : Γ, (∀ h : Γ, (ρ (h * g) : Matrix (Fin n) (Fin n) k).trace = (ρ h : Matrix (Fin n) (Fin n) k).trace) → ρ g = 1 := by
  intro Γ k _ _ _ n ρ hss g htr
  classical
  let σ : Γ →* Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp ρ)
  have hσ : ∀ h, σ h = Matrix.toLin' (ρ h : Matrix (Fin n) (Fin n) k) := fun h => rfl
  let A : Subalgebra k (Module.End k (Fin n → k)) := Algebra.adjoin k (Set.range σ)
  have hspan : ∀ a ∈ A, a ∈ Submodule.span k (Set.range σ) := by
    intro a ha
    have h1 : a ∈ Subalgebra.toSubmodule A := ha
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq] at h1
    exact h1
  have hinv : ∀ W : Submodule k (Fin n → k), Formalism.MainNotions.N.IsInv ρ W →
      ∀ a ∈ A, ∀ v ∈ W, a v ∈ W := by
    intro W hW a ha v hv
    suffices H : ∀ b ∈ Submodule.span k (Set.range σ), b v ∈ W from H a (hspan a ha)
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨h, rfl⟩ := hb'
      rw [hσ, Matrix.toLin'_apply]
      exact hW h v hv
    | zero => simpa using W.zero_mem
    | add b c _ _ hb hc => simpa using W.add_mem hb hc
    | smul c b _ hb => simpa using W.smul_mem c hb
  have hssA : IsSemisimpleModule A (Fin n → k) := by
    refine { exists_isCompl := fun W => ?_ }
    have hW : Formalism.MainNotions.N.IsInv ρ (W.restrictScalars k) := by
      intro h v hv
      have hmem : σ h ∈ A := Algebra.subset_adjoin ⟨h, rfl⟩
      have := W.smul_mem (⟨σ h, hmem⟩ : A) hv
      exact this
    obtain ⟨W', hW'inv, hc⟩ := hss _ hW
    let W'' : Submodule A (Fin n → k) :=
      { carrier := W'
        add_mem' := W'.add_mem
        zero_mem' := W'.zero_mem
        smul_mem' := fun a v hv => hinv W' hW'inv a a.2 v hv }
    refine ⟨W'', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro v hv hv'
      exact (Submodule.disjoint_def.mp hc.disjoint) v hv hv'
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      have hv : v ∈ W.restrictScalars k ⊔ W' := by rw [hc.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      exact Submodule.add_mem_sup hy hz
  let φ : A →ₗ[A] (Fin n → (Fin n → k)) :=
    { toFun := fun a i => (a : Module.End k (Fin n → k)) (Pi.single i 1)
      map_add' := fun a b => by ext i j; simp
      map_smul' := fun a b => by ext i j; rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply (Pi.basisFun k (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact congrFun hab i
  have hssAA : IsSemisimpleModule A A := IsSemisimpleModule.of_injective φ hφ
  have hgA : σ g ∈ A := Algebra.subset_adjoin ⟨g, rfl⟩
  have hxA : σ g - 1 ∈ A := A.sub_mem hgA A.one_mem
  have htrace : ∀ a ∈ A, LinearMap.trace k (Fin n → k) (a * (σ g - 1)) = 0 := by
    intro a ha
    suffices H : ∀ b ∈ Submodule.span k (Set.range σ),
        LinearMap.trace k (Fin n → k) (b * (σ g - 1)) = 0 from H a (hspan a ha)
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨h, rfl⟩ := hb'
      rw [mul_sub, mul_one, ← map_mul, map_sub, hσ, hσ, Matrix.trace_toLin'_eq,
        Matrix.trace_toLin'_eq, htr, sub_self]
    | zero => simp
    | add b c _ _ hb hc => rw [add_mul, map_add (f := _), hb, hc, add_zero]
    | smul c b _ hb => rw [smul_mul_assoc, map_smul, hb, smul_zero]
  let x' : A := ⟨σ g - 1, hxA⟩
  obtain ⟨L', hL⟩ := exists_isCompl (Submodule.span A {x'})
  have h1 : (1 : A) ∈ Submodule.span A {x'} ⊔ L' := by rw [hL.sup_eq_top]; trivial
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp h1
  have he'eq : e' = 1 - e := by rw [← hee]; abel
  have key : ∀ l ∈ Submodule.span A {x'}, l * e = l := by
    intro l hl
    have h2 : l * e' ∈ L' := L'.smul_mem l he'
    have h5 : l * e' = l - l * e := by rw [he'eq, mul_sub, mul_one]
    have h3 : l * e' ∈ Submodule.span A {x'} := by
      rw [h5]
      exact Submodule.sub_mem _ hl (Submodule.smul_mem _ l he)
    have h4 := (Submodule.disjoint_def.mp hL.disjoint) _ h3 h2
    rw [h5, sub_eq_zero] at h4
    exact h4.symm
  have hidem : e * e = e := key e he
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp he
  have htr_e : LinearMap.trace k (Fin n → k) (e : Module.End k (Fin n → k)) = 0 := by
    rw [← hy]
    exact htrace _ y.2
  have hI : IsIdempotentElem (e : Module.End k (Fin n → k)) := congrArg Subtype.val hidem
  have he0 : (e : Module.End k (Fin n → k)) = 0 := by
    first
    | exact (LinearMap.IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e
    | exact (IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e
  have he0' : e = 0 := Subtype.ext he0
  have hx0 : x' = 0 := by
    rw [← key x' (Submodule.mem_span_singleton_self x'), he0', mul_zero]
  have hx1 : σ g - 1 = 0 := congrArg Subtype.val hx0
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one, ← hσ]
  exact sub_eq_zero.mp hx1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorInLocallyStableSubspace
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.exists_fixed_vector_in_locally_stable_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E n)), K ≤ locU n w → (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ) → ∀ W : Submodule ℂ (UA E n → ℂ), W ≤ σ → W ≠ ⊥ → (∀ x ∈ locU n w, ∀ φ ∈ W, RU E n x φ ∈ W) → ∃ φ ∈ W, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  intro E _ _ _ n π hπ w K hK hu W hWπ hW0 hW
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨τ, -, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n Ψ w
  let ρ : Representation ℂ (locU n w) Ψ.V := Ψ.rep.comp (locU n w).subtype
  let F : Representation.IntertwiningMap τ.ρ ρ :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V τ.V τ.V Ψ.rep (locU n w).subtype
    τ.ρ τ.ρ Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  have hfi : ∀ (i : Representation.IntertwiningMap τ.ρ ρ) g u, i.toLinearMap (τ.ρ g u) = ρ g (i.toLinearMap u) :=
    fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u
  let K' : Subgroup (locU n w) := K.comap (locU n w).subtype
  have hfix : ∃ v : τ.V, v ≠ 0 ∧ ∀ k ∈ K', τ.ρ k v = v := by
    by_contra hn
    have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ρ τ.ρ hirr
      (fun i : Representation.IntertwiningMap τ.ρ ρ => i.toLinearMap) hfi (K' : Set (locU n w)) ⊥
      (fun i v hv => by
        have hv' : v = 0 := by
          by_contra h
          exact hn ⟨v, h, hv⟩
        rw [hv', map_zero]
        exact Submodule.zero_mem _)
      (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) ⟨φ, hφ⟩
      (fun k hk => Subtype.ext (hφK k.1 hk)) (by rw [htop]; exact Submodule.mem_top)
    exact hφ0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 key))
  obtain ⟨v, hvW, hv0, hv⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed τ.ρ hirr ρ
    (by
      rw [eq_top_iff, ← htop]
      exact iSup_le fun i => le_iSup_of_le ⟨i.toLinearMap, hfi i⟩ le_rfl)
    (W.comap π.subtype) (fun g v hv => hW g.1 g.2 v.1 hv)
    (fun e => hW0 ((Submodule.eq_bot_iff W).2 fun x hx => by
      have h : (⟨x, hWπ hx⟩ : π) ∈ W.comap π.subtype := hx
      rw [e] at h
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h))) K' hfix
  exact ⟨v.1, hvW, fun e => hv0 (Subtype.ext e), fun k hk => congrArg Subtype.val (hv ⟨k, hK hk⟩ hk)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticOfInertia
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

theorem UpperTheory.exists_quadratic_of_inertia :
    UpperTheory.V.Af.Cr.QuadCM → UpperTheory.V.Af.Cr.ImagGen → UpperTheory.V.Af.Cr.IneRes → UpperTheory.V.Af.Cr.ExQuadR := by
  intro hQ hI hR F Ω _ _ _ _ _ _ l _ h2 S hS
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hT : {v | ¬ S v}.Finite := Filter.eventually_cofinite.1 hS
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      v ∉ (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 ℚ)) '' {v | ¬ S v} :=
    (hT.image _).eventually_cofinite_notMem
  obtain ⟨K₀, _, _, _, _, _, _, hK₀, hl, v₀, A, ⟨hv1, hv2⟩, hA, s, hs, hsn⟩ :=
    Cq.exQuad Ω l h2 _ (h1.and (hR ℚ F Ω))
  obtain ⟨d, y₀, hd, hy₀, hgen⟩ := hI K₀ hK₀
  obtain ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, y, hy, hgenK⟩ := hQ F Ω (d : F) (algebraMap K₀ Ω y₀)
    (by rw [← map_pow, hy₀, map_ratCast, map_ratCast]) (fun φ => by rw [map_ratCast]; exact_mod_cast hd)
  obtain ⟨w, hw, hwv⟩ := place_between (L := F) hA
  obtain ⟨t, rfl⟩ := hv2 A hA hs
  refine ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, fun j L hL x => ?_, w, A, ?_, hw, t, hs, ?_⟩
  · obtain ⟨a, b, rfl⟩ := hgenK x
    obtain ⟨z, hz⟩ := Cq.embPadic K₀ hK₀ l hl (j.comp (algebraMap K₀ Ω)) y₀
    rw [map_add (f := _), map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add (f := _), map_mul]
    refine add_mem (hL a) (mul_mem (hL b) ?_)
    rw [RingHom.comp_apply] at hz
    rw [← hz]
    exact L.1.algebraMap_mem z
  · by_contra h
    exact hv1 ⟨w, h, hwv⟩
  · rintro ⟨u, rfl⟩
    have hu : u (algebraMap K₀ Ω y₀) = algebraMap K₀ Ω y₀ := by rw [← hy]; exact u.commutes y
    refine hsn ⟨{ u.toRingEquiv with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
    obtain ⟨a, b, rfl⟩ := hgen x
    show u _ = _
    simp only [map_add (f := _), map_mul, map_ratCast, hu]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicUnitaryMemNhdsOneOfTrivialAtPlaces
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → ∀ U ∈ nhds (1 : finU (E := E) (n := n)), ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : finU (E := E) (n := n), (∀ u ∉ T, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u (n := n)) → (∀ u ∈ S, cLoc u (k : UA E n) = 1) → k ∈ U := by
  classical
  intro E _ _ _ n T hT U hU
  have hι : Topology.IsInducing (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [hι.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hV' : finGL E n ⁻¹' V ∈ nhds (1 : GL (Fin n) (Af E)) :=
    GlobalTheory.DefU.LocAdm.continuous_finGL.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hV)
  obtain ⟨S, hS⟩ := UpperTheory.V.Af.GlobalFixedVectors.exists_KAway_subset (M := 1) hV'
  refine ⟨S ∪ hT.toFinset, fun k hk hk1 => hVU ?_⟩
  have hall : ∀ u, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u (n := n) := fun u => by
    by_cases hu : u ∈ T
    · rw [hk1 u (Finset.mem_union_right _ (hT.mem_toFinset.2 hu))]; exact one_mem _
    · exact hk u hu
  have ent : ∀ (x : UA E n), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) → ∀ a b,
      Matrix.GeneralLinearGroup.map (pFin E) (x : GA E n) a b ∈ UpperTheory.V.Af.Ohat E := fun x hx a b =>
    UpperTheory.V.Af.GlobalFixedVectors.mem_Ohat.2 fun u => by
      obtain ⟨Q, hQ⟩ := hx u
      have e : (cLoc u x).val a b ∈ u.adicCompletionIntegers E := by
        rw [← hQ]; exact (Q.val a b).2
      exact e
  have h1 := ent _ hall
  have hmem : Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n) ∈
      UpperTheory.V.Af.GlobalFixedVectors.KAway n 1 S := by
    refine UpperTheory.V.Af.GlobalFixedVectors.mem_KAway.2 ⟨UpperTheory.V.Af.mem_KLev.2 ⟨h1, fun a b => ?_, fun a b => ?_⟩, fun w hw => ?_⟩
    · rw [← map_inv]
      exact ent (k : UA E n)⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hall u)) a b
    · refine ⟨_, sub_mem (h1 a b) ?_, by rw [Nat.cast_one, one_mul]⟩
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact hk1 w (Finset.mem_union_left _ hw)
  have hk2 : Matrix.GeneralLinearGroup.map (pInf E) ((k : UA E n) : GA E n) = 1 := k.2
  have e : finGL E n (Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n)) = ((k : UA E n) : GA E n) :=
    ga_ext (by rw [pInf_finGL, hk2]) (by rw [pFin_finGL])
  have := hS hmem
  rwa [Set.mem_preimage, e] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

theorem UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → w.asIdeal.inertiaDeg ℤ = 1 → IsSplitAt w := by
  intro E _ _ _ w hun hf
  classical
  set F := maximalRealSubfield E
  set P : Ideal (𝓞 E) := w.asIdeal
  set p : Ideal (𝓞 F) := P.under (𝓞 F)
  have hfin : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have he : P.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one P (𝓞 F)
  have hf' : P.inertiaDeg (𝓞 F) = 1 := by
    have h := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at h
    exact (Nat.eq_one_of_mul_eq_one_left h.symm)
  by_contra hns
  have hone : ∀ q : p.primesOver (𝓞 E), q.1 = P := by
    intro q
    by_contra hq
    apply hns
    have hq0 : q.1 ≠ ⊥ := by
      intro h0
      have hP0 : p = ⊥ := by
        have := q.2.2
        rw [Ideal.liesOver_iff, h0] at this
        rw [this]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      apply w.ne_bot
      exact Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) hP0
    refine ⟨⟨q.1, q.2.1, hq0⟩, ?_, ?_⟩
    · intro h
      exact hq (congrArg HeightOneSpectrum.asIdeal h)
    · ext1
      change Ideal.under (𝓞 F) q.1 = p
      exact (Ideal.liesOver_iff _ _).mp q.2.2 |>.symm
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  have huniq : (Finset.univ : Finset (p.primesOver (𝓞 E))) = {⟨P, hPmem⟩} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hone q)
  rw [huniq, Finset.sum_singleton, he, hf', hfin] at hsum
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

theorem UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Ine (F := Lp L) A ≤ (resP L Ω).range) → ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal := by
  intro L Ω _ _ _ _ _ _ h w
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let v : Plc (Lp L) := ⟨w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)), inferInstance, by
    exact Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)) w.asIdeal)⟩
  have hv : IsPlaceOver A v := by
    intro x
    have h1 := hA (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ w.asIdeal
    rw [← h1, IsScalarTower.algebraMap_apply (Lp L) L Ω]
    rfl
  have hle := h A v hv
  have hbot : Ideal.inertia Gal(L/(Lp L)) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs (Lp L) L Ω A w hA, eq_bot_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, rfl⟩ := hle hσ
    rw [Subgroup.mem_bot]
    ext x
    apply (algebraMap L Ω).injective
    rw [AlgEquiv.one_apply]
    show algebraMap L Ω ((AlgEquiv.restrictScalars (Lp L) τ).restrictNormal L x) = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact τ.commutes x
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← (UpperTheory.V.CF.ineCard).1 (Lp L) L w, hbot]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KernelSemisimpleCharpolyProduct
section
open Formalism.MainNotions.N


private theorem ker_transfer {Γ K : Type} [Group Γ] [Field K] {n m : ℕ} (ρ : Γ →* GL (Fin n) K)
    (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ) (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly) (s : Γ) (h : ρ s = 1) : σ s = 1 := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  have h1 := hP s
  rw [h] at h1
  simpa using h1
end

