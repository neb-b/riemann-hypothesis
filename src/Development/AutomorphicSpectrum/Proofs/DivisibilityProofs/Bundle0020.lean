module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT2
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimensionStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension | exact GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem mem_range_of_tmul_eq {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (x : Ω)
    (h : x ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] x) : x ∈ (algebraMap L Ω).range := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap L Ω).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  let m : Ω ⊗[L] Ω →ₗ[L] Ω := TensorProduct.lid L Ω ∘ₗ TensorProduct.map g LinearMap.id
  have e := congrArg m h
  simp only [m, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, hg1,
    one_smul, LinearEquiv.coe_coe] at e
  exact ⟨g x, by rw [Algebra.algebraMap_eq_smul_one]; exact e⟩

theorem factor_of_epi {O F Ω₀ Ω : Type} [CommRing O] [Field F] [Field Ω₀] [Field Ω]
    (β : O →+* F) (hβ : Epi (CommRingCat.ofHom β)) (a : O →+* Ω₀) (fn : Ω₀ →+* Ω) (cst : F →+* Ω)
    (h : fn.comp a = cst.comp β) : ∃ a' : F →+* Ω₀, a'.comp β = a := by
  let _ := fn.toAlgebra
  have e : CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[Ω₀] Ω).comp cst) =
      CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Ω →ₐ[Ω₀] Ω ⊗[Ω₀] Ω).toRingHom.comp cst) := by
    ext o
    have ho : cst (β o) = algebraMap Ω₀ Ω (a o) := by
      rw [RingHom.algebraMap_toAlgebra]; exact (RingHom.congr_fun h o).symm
    change cst (β o) ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst (β o)
    rw [ho, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have e2 := hβ.left_cancellation _ _ e
  have key : ∀ u : F, ∃ w : Ω₀, fn w = cst u := by
    intro u
    have hu := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e2) u
    change cst u ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst u at hu
    obtain ⟨w, hw⟩ := mem_range_of_tmul_eq (L := Ω₀) (cst u) hu
    exact ⟨w, by rw [← hw, RingHom.algebraMap_toAlgebra]⟩
  choose g hg using key
  have inj := fn.injective
  refine ⟨{ toFun := g
            map_one' := inj (by rw [hg, map_one, map_one])
            map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := inj (by rw [hg, map_zero, map_zero])
            map_add' := fun x y => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }, ?_⟩
  ext o
  apply inj
  change fn (g (β o)) = fn (a o)
  rw [hg]
  exact (RingHom.congr_fun h o).symm

theorem eq_genPt_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hf : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)
  have : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, rfl⟩ := this
  let _ := hf.toField
  have : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum _) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

theorem mem_of_dense_of_noGen {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  classical
  have hCi : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent y) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη : hCi.genericPoint = y := hy _ (hgen.specializes mem_irreducibleComponent)
  rw [hη] at hgen
  have hmax := irreducibleComponent_mem_irreducibleComponents y
  set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD
  have hDc : IsClosed D := by
    rw [hD, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hyD : y ∉ D := by
    rintro ⟨C, ⟨hC, hne⟩, hyC⟩
    have hle : irreducibleComponent y ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)
    exact hne (le_antisymm (hmax.2 hC.1 hle) hle)
  obtain ⟨u, huD, huU⟩ := hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩
  have huC : u ∈ irreducibleComponent y := by
    by_contra hne
    refine huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩,
      mem_irreducibleComponent⟩
    intro e
    exact hne (by
      have : u ∈ irreducibleComponent u := mem_irreducibleComponent
      rw [Set.mem_singleton_iff.1 e] at this
      exact this)
  exact (hgen.specializes huC).mem_open hU huU

theorem noetherianSpace_baseChange {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

theorem gen_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y),
    Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A hmono
  have hepi : Epi (CommRingCat.ofHom β) := by
    have h1 : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := hmono
    have h2 : Mono (CommRingCat.ofHom β).op := Scheme.Spec.mono_of_mono_map h1
    exact unop_epi_of_mono (CommRingCat.ofHom β).op
  let a : O →+* A.Ω₀ := (Spec.preimage (A.ξ₀ ≫ Y.s)).hom
  have ha : spMap a = A.ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : A.fn.comp a = A.cst.comp β := by
    have h1 : spMap (A.fn.comp a) = spMap (A.cst.comp β) := by
      rw [← A.cst_over]
      have hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
      calc spMap (A.fn.comp a) = spMap A.fn ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd, Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨a', ha'⟩ := factor_of_epi β hepi a A.fn A.cst hfa
  have hsq : A.ξ₀ ≫ Y.s = spMap a' ≫ spMap β := by
    rw [← ha, ← ha']
    simp only [spMap, ← Spec.map_comp]; rfl
  let z : Sp A.Ω₀ ⟶ pullback Y.s (spMap β) := pullback.lift A.ξ₀ (spMap a') hsq
  have hz : z ≫ pullback.fst _ _ = A.ξ₀ := pullback.lift_fst _ _ _
  let y0 : ↥(pullback Y.s (spMap β)) := z (IsLocalRing.closedPoint A.Ω₀)
  have hfst : pullback.fst Y.s (spMap β) y0 = genPt A.ξ₀ := by
    show (pullback.fst Y.s (spMap β)) (z _) = A.ξ₀ _
    rw [← hz]
    rfl
  have hmax : ∀ y', y' ⤳ y0 → y' = y0 := by
    intro y' hy
    have h1 : pullback.fst Y.s (spMap β) y' ⤳ genPt A.ξ₀ := hfst ▸ hy.map (pullback.fst Y.s (spMap β)).continuous
    have h2 := eq_genPt_of_specializes A.ξ₀ A.gen₀ _ h1
    exact (pullback.fst Y.s (spMap β)).injective (h2.trans hfst.symm)
  have := noetherianSpace_baseChange Y.proj β
  have := Y.jQ_open
  have hy0 : y0 ∈ Set.range Y.jQ :=
    mem_of_dense_of_noGen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hmax
  have hrange : Set.range z ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint A.Ω₀ := Subsingleton.elim (α := PrimeSpectrum A.Ω₀) _ _
    rw [this]
    exact hy0
  refine ⟨IsOpenImmersion.lift Y.jQ z hrange, ?_⟩
  show A.ξ₀ = IsOpenImmersion.lift Y.jQ z hrange ≫ Y.jQ ≫ pullback.fst _ _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hz]

end GlobalTheory.CompanionTheory.Ar.GenOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEq
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.TopLink

section Cyc

variable {K : Type} [DecidableEq K] {ι : K → Type}

theorem intNumL_perm (F : Type) [Field F] (V : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) := ⟨fun a b g => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cycList_perm (Z : Ideal (MRing ι O) → ℤ) {l l' : List (K → ℤ)} (h : l.Perm l') :
    cycList Z l = cycList Z l' := by
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm (IsLocalRing.ResidueField O) (specialIdeal W) h


omit [DecidableEq K] in
theorem divCycle_mul_finite {R : Type} [CommRing R] [IsNoetherianRing (MRing ι R)] (P : Ideal (MRing ι R))
    (f : MRing ι R) (n : Ideal (MRing ι R) → ℤ) :
    (Function.support fun W => divCycle P f W * n W).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dite_eq_right (fun h' => h h'.1), zero_mul]

theorem cycList_ratDiv [Fintype K] [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (f g : MRing ι O)
    (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  unfold cycList cycEval ratDiv
  simp only [sub_mul]
  exact finsum_sub_distrib (divCycle_mul_finite P f _) (divCycle_mul_finite P g _)

end Cyc

theorem link_monomial {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {σ : Type} {S : Finset Nat.Primes} {T : LocPair ι ℤ σ} (hT : T.IsVertOff P S)
    {A A' : σ → HermLine ι} (hA : ∀ i, IsSmoothHerm (A i)) (hA' : ∀ i, IsSmoothHerm (A' i))
    (hiso : T.IsIsometric P A A') (i : σ) (μ : σ ⊕ σ →₀ ℕ) (hμ : μ.toMultiset.card = D) :
    arList I P (((μ + Finsupp.single (Sum.inl i) 1).toMultiset.map (Sum.elim A A')).toList) -
      arList I P (((μ + Finsupp.single (Sum.inr i) 1).toMultiset.map (Sum.elim A A')).toList) =
    ∑ p ∈ S, Real.log (p : ℕ) *
      (cycList (ratDiv (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) (T.f i))
        (MvPolynomial.map (Int.castRingHom (ZP p)) (T.g i))) (classList (Sum.elim T.x T.x') μ ++ []) : ℝ) := by
  classical
  set m := μ.toMultiset.toList with hm
  have hlen : m.length = D := by rw [hm, Multiset.length_toList, hμ]
  subst hlen
  let L : Fin m.length → HermLine ι := fun j => Sum.elim A A' (m.get j)
  have hB : ∀ s, IsSmoothHerm (Sum.elim A A' s) := by
    rintro (s | s)
    · exact hA s
    · exact hA' s
  have hL : ∀ j, IsSmoothHerm (L j) := fun j => hB _
  have hofL : List.ofFn L = m.map (Sum.elim A A') := by
    conv_rhs => rw [← List.ofFn_get m]
    rw [List.map_ofFn]
    rfl
  have key : ∀ s, arList I P (((μ + Finsupp.single s 1).toMultiset.map (Sum.elim A A')).toList) =
      I P (m.length + 1) (Fin.snoc L (Sum.elim A A' s)) := by
    intro s
    apply arList_eq_of_perm hP hI
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; exact hB s
      · rw [Fin.snoc_castSucc]; exact hL j
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [show (List.ofFn fun j => L j) = m.map (Sum.elim A A') from hofL, ← Multiset.coe_eq_coe,
        Multiset.coe_toList, List.concat_eq_append, ← Multiset.coe_add, ← Multiset.map_coe, hm,
        Multiset.coe_toList, map_add, Finsupp.toMultiset_single, Multiset.map_add]
      simp
  have hdeg : (List.ofFn fun j => (L j).a).Perm (classList (Sum.elim T.x T.x') μ ++ []) := by
    have h1 : (List.ofFn fun j => (L j).a) = m.map (Sum.elim T.x T.x') := by
      conv_rhs => rw [← List.ofFn_get m]
      rw [List.map_ofFn]
      congr 1
      funext j
      change (Sum.elim A A' (m.get j)).a = Sum.elim T.x T.x' (m.get j)
      cases h : m.get j with
      | inl s => exact (hiso s).1
      | inr s => exact (hiso s).2.1
    rw [h1, List.append_nil, classList, ← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, hm,
      Multiset.coe_toList]
  rw [key, key]
  have step := _root_.GlobalTheory.CompanionTheory.Ar.Num.Link.change_line K ι P m.length hP I hI S (T.comp fun _ : Unit => i) (fun _ => hT i)
    (A i) (A' i) (hA i) (hA' i) (fun _ => hiso i) L hL
  refine step.trans (Finset.sum_congr rfl fun p _ => ?_)
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -⟩ := hT i
  have e1 := _root_.GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList K ι P m.length hP p bf (T.f i) hf hfP (List.ofFn fun j => (L j).a) (by simp)
  have e2 := _root_.GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList K ι P m.length hP p bg (T.g i) hg hgP (List.ofFn fun j => (L j).a) (by simp)
  rw [← cycList_perm _ hdeg, cycList_ratDiv, ← e1, ← e2]
  push_cast
  rfl

theorem arNum_eq_sum_log_val : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (σ : Type) [Fintype σ] (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → ∀ A A' : σ → HermLine ι, (∀ i, IsSmoothHerm (A i)) → (∀ i, IsSmoothHerm (A' i)) → T.IsIsometric P A A' → ∀ (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ), IsMixExpansion D V Gs → arNum I P (Sum.elim A A') V = ∑ p ∈ S, Real.log (p : ℕ) * (T.map (Int.castRingHom (ZP p))).val (extTo (ZP p) P) Gs := by
  intro K _ _ ι _ P D hP I hI σ _ S T hT A A' hA hA' hiso V Gs hV
  classical
  obtain ⟨rfl, hG⟩ := hV
  rw [arNum_sum']
  simp only [LocPair.val, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cycNum, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [(Gs i).as_sum, Finset.mul_sum, arNum_sum']
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hcard : μ.toMultiset.card = D := by
    have h := hG i (MvPolynomial.mem_support_iff.1 hμ)
    rw [Finsupp.card_toMultiset, ← h, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hpoly : (X (Sum.inl i) - X (Sum.inr i)) * monomial μ (AddMonoidAlgebra.coeff (Gs i) μ) =
      monomial (μ + Finsupp.single (Sum.inl i) 1) (AddMonoidAlgebra.coeff (Gs i) μ) +
        monomial (μ + Finsupp.single (Sum.inr i) 1) (-AddMonoidAlgebra.coeff (Gs i) μ) := by
    rw [monomial_add_single, monomial_add_single, map_neg]
    ring
  have hmono := link_monomial hP hI hT hA hA' hiso i μ hcard
  rw [hpoly, arNum_add', arNum_monomial', arNum_monomial', neg_mul, ← sub_eq_add_neg, ← mul_sub, hmono,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [LocPair.map]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.TopLink
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelGeometricGenericNumber
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GeoModel

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem intNumL_ofFn' {K : Type} [DecidableEq K] {ι : K → Type} (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem geoMono_mapDomain_some (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (μ : Ψ × Fin N →₀ ℕ) (hμ : μ.degree = dimFl Ψ N) :
    M.geoMono (μ.mapDomain some) = (intNumL ℚ (extTo ℚ M.P) (classList M.xdeg μ) : ℝ) / (M.δ : ℝ) := by
  have hcard : (Finsupp.toMultiset μ).card = dimFl Ψ N := by
    rw [Finsupp.card_toMultiset, ← hμ, Finsupp.degree_apply]
    rfl
  have hmap : Finsupp.toMultiset (μ.mapDomain some) = (Finsupp.toMultiset μ).map some :=
    (Finsupp.toMultiset_map μ some).symm
  have hdeg : (μ.mapDomain some).degree = dimFl Ψ N := by
    rw [← hμ]
    induction μ using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [Finsupp.mapDomain_add]
    | single a b => simp
  have hnone : (μ.mapDomain some) none = 0 := Finsupp.mapDomain_notin_range _ _ (by simp)
  have hlen : (Finsupp.toMultiset (μ.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [Multiset.length_toList, hmap, Multiset.card_map, hcard]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  set L := monoLines (M.line 1) (μ.mapDomain some) (dimFl Ψ N) with hLdef
  have hL : ∀ k : Fin (dimFl Ψ N), L k = M.line 1 ((Finsupp.toMultiset (μ.mapDomain some)).toList.get
      ⟨k, by rw [hlen]; exact k.2⟩) := by
    intro k
    simp only [hLdef, monoLines]
    rw [dite_eq_left (by rw [hlen]; exact k.2)]
  have hline : ∀ o, IsSmoothHerm (M.line 1 o) := by
    rintro (_ | r)
    · exact M.A_smooth
    · exact M.x_smooth 1 r
  have hsm : ∀ j, IsSmoothHerm (L j) := fun j => by rw [hL j]; exact hline _
  rw [_root_.GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_one_eq_intNum M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII _ _) L hsm, ← intNumL_ofFn']
  congr 2
  refine NumericalSegreProof.intNumL_perm ℚ _ ?_
  have hlist : List.ofFn (fun j => (L j).a) =
      (Finsupp.toMultiset (μ.mapDomain some)).toList.map (fun o => (M.line 1 o).a) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      rw [hL]
      rfl
  rw [hlist, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, hmap, Multiset.map_map]
  rw [classList, Multiset.coe_toList]
  refine Multiset.map_congr rfl fun r _ => ?_
  exact M.x_deg 1 r

theorem geoFun_toA_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K]
    (II : IntersectionSystem), IsIntersectionSystem II → ∀ (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N) →
    M.geoFun (toA F) = genNum ℚ (extTo ℚ M.P) M.xdeg F [] / (M.δ : ℝ) := by
  intro Ψ _ _ N M _ II hII F hF
  have h1 : toA F = ∑ μ ∈ F.support, F.coeff μ • basisMonomials (Option (Ψ × Fin N)) ℝ (μ.mapDomain some) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [toA, F.as_sum, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum, genNum, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : μ.degree = dimFl Ψ N := by
    exact (DFunLike.congr_fun Finsupp.degree_eq_weight_one μ).trans (hF (mem_support_iff.1 hμ))
  rw [map_smul, RootModel.geoFun, Module.Basis.constr_basis, geoMono_mapDomain_some M II hII μ hd,
    smul_eq_mul, List.append_nil, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.Num.GeoModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT2Statement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_T2 : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (K C' rd Lval : ℝ), 0 ≤ K → 0 ≤ C' → 1 ≤ rd → T.Proportional → FrobShape frob → I9 (Ψ := Ψ) (N := N) hh → T.Prop6 II frob → T.ThmBA II hh → T.PropF II C' rd Lval → T.LowerBoundAtBase II hh frob K rd Lval → T.T2 II (K + C' + 2) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs <;> assumption)
end

