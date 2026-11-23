module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteSpanKummerSelmerRepresentatives
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]
    {x : K} (hx : x ≠ 0) (n : ℕ) : divisor (x ^ n) = n • (divisor x : Divisor k K) := by
  induction n with
  | zero => simp [divisor_one]
  | succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

theorem UpperTheory.exists_finite_span_kummerSelmer_representatives :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], ∃ (n : ℕ) (v : Fin n → K), ∀ f ∈ SelAll k K q, ∃ g ∈ SelAll k K q, (∃ c : Fin n → k, (g : K) = ∑ i, c i • v i) ∧ ∃ u : Kˣ, f = g * u ^ q := by
  intro k K _ _ _ _ _ q _
  have hcl : algebraicClosure k K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_algebraicClosure_iff] at hz
    rw [IntermediateField.mem_bot]
    exact minpoly.mem_range_of_degree_eq_one k z
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz.isIntegral))
  obtain ⟨x, hxt, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hd : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K := Module.finrank_pos
  obtain ⟨γ, hγ⟩ := Divisor.exists_bound_deg_sub_finrank_L (k := k) (K := K)
  set n := γ.toNat + 1
  set E : Divisor k K := n • poleDivisor x with hE
  have hdegE : (n : ℤ) ≤ Divisor.deg E := by
    rw [hE, map_nsmul, Divisor.deg_poleDivisor hxt, nsmul_eq_mul]
    have h1 : (1 : ℤ) ≤ (Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K : ℤ) := by
      exact_mod_cast hd
    have h2 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    nlinarith
  set V := (q • E).L with hV
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun i => (b i : K), ?_⟩
  intro f hf
  have hf' : ∀ w : Place k K, (q : ℤ) ∣ w.ord (f : K) := hf
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  let D : Divisor k K := Finsupp.mapRange (fun z : ℤ => z / (q : ℤ)) (by simp) (divisor (f : K))
  have hD : divisor (f : K) = q • D := by
    ext w
    simp only [D, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel', divisor_apply]
    rw [divisor_apply]
    exact hf' w
  have hdegD : Divisor.deg D = 0 := by
    have h0 := Divisor.deg_divisor (k := k) (f : K)
    rw [hD, map_nsmul, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hq
    · exact h
  have hri := hγ (D + E)
  rw [map_add (f := _), hdegD, zero_add] at hri
  have hn : γ < (n : ℤ) := by
    dsimp [n]
    by_cases h : 0 ≤ γ
    · rw [Int.toNat_of_nonneg h]
      omega
    · have : (0 : ℤ) ≤ (γ.toNat : ℤ) := by positivity
      omega
  have hpos : 0 < Module.finrank k (D + E).L := by omega
  obtain ⟨⟨h, hmem⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hh : h ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hle := (Divisor.mem_L_iff_le hh).mp hmem
  let u : Kˣ := Units.mk0 h hh
  have hval : ((f * u ^ q : Kˣ) : K) = (f : K) * h ^ q := by simp [u]
  have hgne : ((f * u ^ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hgdiv : divisor ((f * u ^ q : Kˣ) : K) = q • (D + divisor h) := by
    rw [hval, divisor_mul f.ne_zero (pow_ne_zero _ hh), UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' hh, hD, smul_add]
  have hgV : ((f * u ^ q : Kˣ) : K) ∈ V := by
    rw [hV, Divisor.mem_L_iff_le hgne, hgdiv, ← smul_add]
    have h3 : D + divisor h + E = divisor h + (D + E) := by abel
    rw [h3]
    exact nsmul_nonneg hle q
  refine ⟨f * u ^ q, ?_, ?_, u⁻¹, by group⟩
  · intro w
    rw [← divisor_apply, hgdiv, Finsupp.smul_apply, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · refine ⟨fun i => b.repr ⟨_, hgV⟩ i, ?_⟩
    have hs := b.sum_repr ⟨_, hgV⟩
    have hs' := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs'
    exact hs'.symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSubalgebraEqRangeGermToFunctionField
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKernelPowClassesOfPrimitiveRoot
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma mem_range_of_fixed {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (q : ℕ) (hq : (q : K) ≠ 0) (σ₀ : K' →ₐ[K] AlgebraicClosure K) (c : K') (d : K) (hd : d ≠ 0)
    (hc : c ^ q = algebraMap K K' d)
    (hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c) : c ∈ (algebraMap K K').range := by
  have hsep : (minpoly K c).Separable := by
    refine (Polynomial.separable_X_pow_sub_C d hq hd).of_dvd (minpoly.dvd K c ?_)
    simp [hc]
  have hsplit : ((minpoly K c).map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hroot : (minpoly K c).rootSet (AlgebraicClosure K) = {σ₀ c} := by
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact hfix σ
    · rintro rfl
      exact ⟨σ₀, rfl⟩
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  rw [← minpoly.natDegree_eq_one_iff, ← hcard, Fintype.card_eq_one_iff]
  refine ⟨⟨σ₀ c, by rw [hroot]; rfl⟩, fun y => Subtype.ext ?_⟩
  have hy : (y : AlgebraicClosure K) ∈ ({σ₀ c} : Set (AlgebraicClosure K)) := hroot ▸ y.2
  exact hy

theorem UpperTheory.finite_kernel_powClasses_of_primitive_root :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] (q : ℕ) [NeZero q], (∃ ζ : K, IsPrimitiveRoot ζ q) → FinCls q {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
  intro K K' _ _ _ _ q _ ⟨ζ, hζ⟩
  classical
  haveI := hζ.neZero'
  have hq : ((q : ℕ) : K) ≠ 0 := NeZero.ne _
  have hq0 : q ≠ 0 := NeZero.ne q
  let σ₀ : K' →ₐ[K] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let S : Set Kˣ := {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}
  let bb : Kˣ → K' := fun a => if h : ∃ b : K', algebraMap K K' (a : K) = b ^ q then h.choose else 1
  have hbb : ∀ a ∈ S, algebraMap K K' (a : K) = bb a ^ q := by
    intro a ha
    have ha' : ∃ b : K', algebraMap K K' (a : K) = b ^ q := ha
    simp only [bb, dif_pos ha']
    exact ha'.choose_spec
  have hbb0 : ∀ a ∈ S, bb a ≠ 0 := by
    intro a ha h0
    have h := hbb a ha
    rw [h0, zero_pow hq0] at h
    exact a.ne_zero ((algebraMap K K').injective (by rw [h, map_zero]))
  let sig : Kˣ → (K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun a σ => σ (bb a) / σ₀ (bb a)
  have hsig : ∀ a ∈ S, ∀ σ, sig a σ ∈ Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) := by
    intro a ha σ
    rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hq0)]
    have h1 : σ (bb a) ^ q = σ₀ (bb a) ^ q := by
      rw [← map_pow, ← map_pow, ← hbb a ha, AlgHom.commutes, AlgHom.commutes]
    have h2 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr (hbb0 a ha)
    simp only [sig, div_pow, h1, div_self (pow_ne_zero _ h2)]
  have hfin : (sig '' S).Finite := by
    refine (Set.Finite.pi (t := fun _ => (Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) : Set _))
      (fun _ => Finset.finite_toSet _)).subset ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Set.mem_univ_pi.mpr (fun σ => hsig a ha σ)
  let rep : ((K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) → Kˣ :=
    fun f => if h : ∃ a ∈ S, sig a = f then h.choose else 1
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro a ha
  have hex : ∃ a' ∈ S, sig a' = sig a := ⟨a, ha, rfl⟩
  have htS : rep (sig a) ∈ S ∧ sig (rep (sig a)) = sig a := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  refine ⟨rep (sig a), Finset.mem_image.mpr ⟨sig a, hfin.mem_toFinset.mpr ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  set t := rep (sig a) with ht
  have hat := hbb0 a ha
  have htt := hbb0 t htS.1
  let c : K' := bb a / bb t
  have hc : c ^ q = algebraMap K K' ((a : K) / (t : K)) := by
    rw [map_div₀, hbb a ha, hbb t htS.1, div_pow]
  have hd : (a : K) / (t : K) ≠ 0 := div_ne_zero a.ne_zero t.ne_zero
  have hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c := by
    intro σ
    have e := congrFun htS.2 σ
    simp only [sig] at e
    have h1 : σ (bb t) ≠ 0 := (map_ne_zero σ).mpr htt
    have h2 : σ₀ (bb t) ≠ 0 := (map_ne_zero σ₀).mpr htt
    have h3 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr hat
    simp only [c, map_div₀]
    rw [div_eq_div_iff h1 h2]
    rw [div_eq_div_iff h2 h3] at e
    linear_combination -e
  obtain ⟨e, he⟩ := mem_range_of_fixed q hq σ₀ c _ hd hc hfix
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero] at he
    exact div_ne_zero hat htt he.symm
  refine ⟨Units.mk0 e he0, ?_⟩
  ext
  apply (algebraMap K K').injective
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, he, hc, map_div₀]
  have : algebraMap K K' (t : K) ≠ 0 := (map_ne_zero _).mpr t.ne_zero
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FinitePicTorsionOfFiniteKummerSelmer
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem finite_bad_places (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] :
    {v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring}.Finite := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine (Set.Finite.biUnion s.finite_toSet (fun g _ =>
    Place.finite_ord_ne_zero (k := k) (algebraMap B (FractionRing B) g))).subset ?_
  intro v hv
  by_contra hcon
  apply hv
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hmem : ∀ g ∈ s, algebraMap B (FractionRing B) g ∈ v.ring := by
    intro g hg
    by_cases g0 : algebraMap B (FractionRing B) g = 0
    · rw [g0]; exact zero_mem _
    · have h0 : v.ord (algebraMap B (FractionRing B) g) = 0 := by
        by_contra hne
        exact hcon g hg hne
      exact (v.ord_nonneg_iff g0).1 h0.ge
  intro b
  have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hmem x hx
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply k B (FractionRing B)]
    exact v.algebraMap_mem r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem dvd_ord_of_mem_sel (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [IsFunctionField k (FractionRing B)] (q : ℕ) (v : Place k (FractionRing B))
    (hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring) (f : (FractionRing B)ˣ)
    (hf : f ∈ LateralTheory.E.LeafPicCut.sel B q) : (q : ℤ) ∣ v.ord (f : FractionRing B) := by
  have hk : ∀ c : k, algebraMap k (FractionRing B) c ∈ (algebraMap B (FractionRing B)).range :=
    fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B (FractionRing B) c).symm⟩
  obtain ⟨I, hI⟩ := hf
  have hvP := Place.ofHeightOneSpectrum_center B hk v hv
  have hval := Place.valuation_ofHeightOneSpectrum B hk (Place.center B v hv)
  rw [hvP] at hval
  have h1 := v.valuation_eq_exp_neg_ord f.ne_zero
  rw [hval, GlobalTheory.Idele.valuation_eq_exp_neg_count _ f.ne_zero, WithZero.exp_inj, neg_inj] at h1
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) (f : FractionRing B) =
      ((I : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) ^ q := by
    have := congrArg (fun J : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ =>
      (J : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) hI
    simpa using this.symm
  rw [hspan, FractionalIdeal.count_pow] at h1
  exact ⟨_, h1.symm⟩

theorem UpperTheory.finite_pic_torsion_of_finite_kummerSelmer :
    LateralTheory.E.LeafPicCut.LeafSelPic → ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] (q : ℕ) [NeZero q], FinCls q (SelAll k (FractionRing B) q) → Finite {c : CommRing.Pic B // c ^ q = 1} := by
  intro hS k B _ _ _ _ _ _ q _ hT
  have hfin : Finite (LateralTheory.E.LeafPicCut.selQ B q) := by
    have : Finite {v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} := (finite_bad_places k B).to_subtype
    let φ : LateralTheory.E.LeafPicCut.sel B q →
        ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) :=
      fun f v => ((v.1.ord ((f.1 : (FractionRing B)ˣ) : FractionRing B) : ℤ) : ZMod q)
    let r := Function.invFun φ
    have hall : ∀ f : LateralTheory.E.LeafPicCut.sel B q,
        (f.1 / (r (φ f)).1 : (FractionRing B)ˣ) ∈ SelAll k (FractionRing B) q := by
      intro f v
      have hdiv : v.ord (((f.1 / (r (φ f)).1 : (FractionRing B)ˣ)) : FractionRing B) =
          v.ord (f.1 : FractionRing B) - v.ord ((r (φ f)).1 : FractionRing B) := by
        rw [Units.val_div_eq_div_val, v.ord_div f.1.ne_zero (r (φ f)).1.ne_zero]
      rw [hdiv]
      by_cases hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring
      · exact dvd_sub (dvd_ord_of_mem_sel k B q v hv _ f.2) (dvd_ord_of_mem_sel k B q v hv _ (r (φ f)).2)
      · have h := congrFun (Function.invFun_eq (f := φ) ⟨f, rfl⟩) ⟨v, hv⟩
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨T, hT⟩ := hT
    choose t ht u hu using fun f => hT _ (hall f)
    refine Finite.of_injective (β := ({v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) × T)
      (fun x => (φ x.out, ⟨t x.out, ht x.out⟩)) ?_
    intro x y hxy
    have h1 : φ x.out = φ y.out := congrArg Prod.fst hxy
    have h2 : t x.out = t y.out := congrArg (fun p => (p.2 : T).1) hxy
    have hx := hu x.out
    have hy := hu y.out
    rw [div_eq_iff_eq_mul'] at hx hy
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨(u x.out)⁻¹ * u y.out, ?_⟩
    simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, hy, h1, h2, mul_pow, inv_pow]
    group
  have key : Finite {c : ClassGroup B // c ^ q = 1} := hS B q hfin
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HypercohomologyPostClEqClComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.hypercohomology_post_cl_eq_cl_comp :
    ∀ {M F G : Shv ℤ} (f : M ⟶ F) (g : F ⟶ G), HK.post ℤ (sgl M) g 0 (cl f) = cl (f ≫ g) := by
  intro M F G f g
  have hg : resAug F ≫ resMap ℤ g = (CochainComplex.singleFunctor (Shv ℤ) 0).map g ≫ resAug G :=
    ((_root_.GlobalTheory.EtC.ResBasic.res_basic ℤ F).2.2.2.2.2.2.2 G g).1
  have key : ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) ≫ resMap ℤ g =
      (CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G := by
    rw [Category.assoc, hg, Functor.map_comp, Category.assoc]
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))
    (Cocycle.ofHom (resMap ℤ g)) (add_zero 0)) = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G))
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  rw [← key]
  simp [zcomp, Cochain.ofHom_comp]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldFractionRingOfDedekindFiniteType
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType :
    ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → IsFunctionField k (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B (FractionRing B) hdim
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def invFn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Ob b A ⥤ Ob a A where
  obj y := ⟨(Equiv.ofBijective _ h1).symm y.pt⟩
  map {x y} f := ⟨(Equiv.ofBijective _ h2).symm f.1, h1.1 (by
    have e1 : φ.d.app A ((Equiv.ofBijective _ h1).symm x.pt) = x.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e2 : φ.d.app A ((Equiv.ofBijective _ h1).symm y.pt) = y.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm f.1) = f.1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.d.app A _ = φ.d.app A _
    rw [φ.eq, e1, e2, e3]
    exact f.2)⟩
  map_id x := Subtype.ext (h2.1 (by
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm 1) = 1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A 1
    rw [map_one (φ.g.app A).hom]
    exact e3))
  map_comp {x y z} f g := Subtype.ext (h2.1 (by
    have e : ∀ u : b.G.obj A, φ.g.app A ((Equiv.ofBijective _ h2).symm u) = u := fun u =>
      (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A (_ * _)
    rw [map_mul (φ.g.app A).hom, e, e, e]
    rfl))

private theorem fn_inv {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    φ.fn A ⋙ invFn φ A h1 h2 = 𝟭 _ := by
  have ho : ∀ x : Ob a A, (φ.fn A ⋙ invFn φ A h1 h2).obj x = (𝟭 _ : Ob a A ⥤ Ob a A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).symm_apply_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).symm_apply_apply f.1

private theorem inv_fn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    invFn φ A h1 h2 ⋙ φ.fn A = 𝟭 _ := by
  have ho : ∀ x : Ob b A, (invFn φ A h1 h2 ⋙ φ.fn A).obj x = (𝟭 _ : Ob b A ⥤ Ob b A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).apply_symm_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).apply_symm_apply f.1

private theorem comp_bij {C D : Type} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (G : D ⥤ C)
    (h : F ⋙ G = 𝟭 _) (h' : G ⋙ F = 𝟭 _) (k : ℕ) :
    Function.Bijective (fun s : ComposableArrows C k => s ⋙ F) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun t => t ⋙ G, fun s => ?_, fun t => ?_⟩
  · show (s ⋙ F) ⋙ G = s
    rw [Functor.assoc, h, Functor.comp_id]
  · show (t ⋙ G) ⋙ F = t
    rw [Functor.assoc, h', Functor.comp_id]

theorem UpperTheory.isIso_stackProductMap_of_bijective :
    ∀ (E : Spc) {a b : Act} (φ : Act.Hom a b), (∀ A, Function.Bijective (fun x : a.D.obj A => φ.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) → IsIso (Sp.map E φ) := by
  intro E a b φ h1 h2
  apply isIso_of_bijective_on_simplices
  intro k T
  have hb := (Function.bijective_id (α := Sx E k T)).prodMap
    (comp_bij (C := Ob a (Scheme.Γ.obj (op T))) (D := Ob b (Scheme.Γ.obj (op T)))
      (φ.fn _) (invFn φ _ (h1 _) (h2 _)) (fn_inv φ _ (h1 _) (h2 _)) (inv_fn φ _ (h1 _) (h2 _)) k)
  exact hb
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSubsingletonCoh
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology :
    ∀ (F : Shv ℤ) (P : PSh) (n : ℤ), Subsingleton (H ℤ (disc.obj P) F n) → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n) := by
  intro F P n hs
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf ℤ
  haveI : (res ℤ F).IsKInjective := (_root_.GlobalTheory.EtC.ResBasic.res_basic ℤ F).1
  haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
  have hb := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso ℤ (e P).hom (res ℤ F) n
  exact hb.2.subsingleton
end

