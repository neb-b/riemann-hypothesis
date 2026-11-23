module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicIdempotentCentralizerHermitian
section
open Matrix Polynomial

namespace GlobalTheory.IsoIdem

theorem eq_zero_of_pow_eq_zero {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) (k : ℕ)
    (hk : y ^ k = 0) : y = 0 := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CommSep.eq_aeval_of_commute_of_separable A hs y hy
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact eq_zero_of_zero_eq_one hk.symm _
  have hsq : Squarefree (minpoly E A) :=
    Squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly A) hs.squarefree
  have h1 : minpoly E A ∣ q ^ (k + 1) := minpoly.dvd E A (by rw [map_pow]; exact hk)
  have h2 : minpoly E A ∣ q := (hsq.dvd_pow_iff_dvd (by omega)).1 h1
  exact minpoly.dvd_iff.1 h2

theorem exists_pow_mul_eq {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (z : Matrix (Fin r) (Fin r) E) (hz : z * A = A * z) :
    ∃ n : ℕ, ∃ w : Matrix (Fin r) (Fin r) E, w * A = A * w ∧ z ^ (n + 1) * w = z ^ n := by
  let S := Subalgebra.centralizer E ({A} : Set (Matrix (Fin r) (Fin r) E))
  have hmem : ∀ a : Matrix (Fin r) (Fin r) E, a ∈ S ↔ a * A = A * a := by
    intro a; rw [Subalgebra.mem_centralizer_iff]; simp [eq_comm]
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun a b => Subtype.ext (GlobalTheory.CommSep.commute_of_commute_separable E r A hs a b
      ((hmem a).1 a.2) ((hmem b).1 b.2)) }
  haveI : IsArtinianRing S := IsArtinianRing.of_finite E S
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := S) (M := S) ⟨z, (hmem z).2 hz⟩ 1
  refine ⟨n, w, (hmem w).1 w.2, ?_⟩
  have := congrArg Subtype.val hw
  simpa using this

theorem star_mul_comm {E : Type} [Field E] [StarRing E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hA : A.IsHermitian) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) :
    star y * A = A * star y := by
  have hA' : star A = A := hA
  have := congrArg star hy
  rw [star_mul, star_mul, hA'] at this
  exact this.symm

theorem pow_add_mul_pow {R : Type} [Ring R] (z w : R) (m : ℕ) (h : z ^ (m + 1) * w = z ^ m) :
    ∀ j : ℕ, z ^ (m + j) * w ^ j = z ^ m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc z ^ (m + (j + 1)) * w ^ (j + 1) = z ^ j * (z ^ (m + 1) * w) * w ^ j := by
          rw [pow_succ' w j, show m + (j + 1) = j + (m + 1) by omega, pow_add]
          simp only [mul_assoc]
      _ = z ^ (m + j) * w ^ j := by rw [h, ← pow_add, show j + m = m + j by omega]
      _ = z ^ m := ih

theorem isoIdem : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E),
    A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧
      f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y →
        y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  intro E _ _ r A hA hs
  have comm : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → a * b = b * a :=
    GlobalTheory.CommSep.commute_of_commute_separable E r A hs
  have cstar := star_mul_comm A hA
  have cmul : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a * b) * A = A * (a * b) := by
    intro a b ha hb; rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have cadd : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a + b) * A = A * (a + b) := by
    intro a b ha hb; rw [add_mul, mul_add, ha, hb]
  have csub : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a - b) * A = A * (a - b) := by
    intro a b ha hb; rw [sub_mul, mul_sub, ha, hb]
  have cone : (1 : Matrix (Fin r) (Fin r) E) * A = A * 1 := by simp
  have cpow : ∀ a : Matrix (Fin r) (Fin r) E, a * A = A * a → ∀ k : ℕ, a ^ k * A = A * a ^ k := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact cmul _ _ ih ha
  let S : Set (Matrix (Fin r) (Fin r) E) := {f | f * A = A * f ∧ f * f = f ∧ f * star f = 0}
  obtain ⟨f, ⟨hfC, hff, hfs⟩, hmax⟩ :=
    (measure fun f : Matrix (Fin r) (Fin r) E => r - f.rank).wf.has_min S ⟨0, by simp [S]⟩
  refine ⟨f, hfC, hff, hfs, ?_⟩
  intro y hy hiso
  by_contra hz
  set e := 1 - f - star f with he
  set z := y * e with hzdef
  have hfsC := cstar f hfC
  have heC : e * A = A * e := csub _ _ (csub _ _ cone hfC) hfsC
  have hzC : z * A = A * z := cmul _ _ hy heC
  have hsf : star f * f = 0 := by rw [← comm f (star f) hfC hfsC]; exact hfs
  have hsfsf : star f * star f = star f := by rw [← star_mul, hff]
  have hfe : f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hff, hfs]; abel
  have hsfe : star f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hsf, hsfsf]; abel
  have hef : e * star f = 0 := by rw [← comm _ _ hfsC heC]; exact hsfe
  have hee : e * e = e := by
    calc e * e = (1 - f - star f) * e := by rw [← he]
      _ = e := by rw [sub_mul, sub_mul, one_mul, hfe, hsfe, sub_zero, sub_zero]
  have hestar : star e = e := by
    rw [he, star_sub, star_sub, star_one, star_star, sub_right_comm]
  have hze : z * e = z := by rw [hzdef, mul_assoc, hee]
  obtain ⟨n, w, hwC, hw⟩ := exists_pow_mul_eq A hs z hzC
  have hw' : z ^ (n + 1 + 1) * w = z ^ (n + 1) := by
    rw [pow_succ' z (n + 1), mul_assoc, hw, ← pow_succ']
  have key := pow_add_mul_pow z w (n + 1) hw' (n + 1)
  have hzw : Commute z w := comm _ _ hzC hwC
  set g := z ^ (n + 1) * w ^ (n + 1) with hg
  have hgC : g * A = A * g := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgz : g * z ^ (n + 1) = z ^ (n + 1) := by
    rw [hg, mul_assoc, ((hzw.pow_pow (n + 1) (n + 1)).symm).eq, ← mul_assoc, ← pow_add, key]
  have hgg : g * g = g := by
    conv_lhs => rw [hg]
    rw [← mul_assoc, hgz]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hgz
    exact hz (eq_zero_of_pow_eq_zero A hs z hzC _ hgz.symm)
  set a := z ^ n * w ^ (n + 1) with ha
  have haC : a * A = A * a := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgza : g = z * a := by rw [hg, ha, pow_succ', mul_assoc]
  have hgs : g * star g = 0 := by
    have hb : (a * star a) * A = A * (a * star a) := cmul _ _ haC (cstar _ haC)
    rw [hgza, star_mul, mul_assoc, ← mul_assoc a, comm _ _ hb (cstar _ hzC), ← mul_assoc]
    rw [show z * star z = 0 from hiso, zero_mul]
  have hge : g * e = g := by
    rw [hgza, mul_assoc, comm a e haC heC, ← mul_assoc, hze]
  have hfz : f * z = 0 := by
    rw [hzdef, ← mul_assoc, comm f y hfC hy, mul_assoc, hfe, mul_zero]
  have hfg : f * g = 0 := by rw [hgza, ← mul_assoc, hfz, zero_mul]
  have hgf : g * f = 0 := by rw [comm g f hgC hfC]; exact hfg
  have hfsg : f * star g = 0 := by
    rw [← hge, star_mul, hestar, ← mul_assoc, hfe, zero_mul]
  have hgsf : g * star f = 0 := by rw [← hge, mul_assoc, hef, mul_zero]
  have hf'S : f + g ∈ S := by
    refine ⟨cadd _ _ hfC hgC, ?_, ?_⟩
    · rw [add_mul, mul_add, mul_add, hff, hfg, hgf, hgg]; abel
    · rw [star_add, add_mul, mul_add, mul_add, hfs, hfsg, hgsf, hgs]; abel
  have hrank : f.rank < (f + g).rank := by
    unfold Matrix.rank
    apply Submodule.finrank_lt_finrank_of_lt
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · have h1 : (f + g) * f = f := by rw [add_mul, hff, hgf, add_zero]
      calc LinearMap.range f.mulVecLin = LinearMap.range ((f + g) * f).mulVecLin := by rw [h1]
        _ ≤ _ := by rw [Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · obtain ⟨v, hv⟩ : ∃ v : Fin r → E, g *ᵥ v ≠ 0 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        apply hg0
        ext i j
        have := congrFun (hall (Pi.single j 1)) i
        simpa [Matrix.mulVec_single] using this
      refine ⟨g *ᵥ v, ⟨g *ᵥ v, ?_⟩, ?_⟩
      · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hfg, hgg, zero_add]
      · rintro ⟨u, hu⟩
        rw [Matrix.mulVecLin_apply] at hu
        apply hv
        have hgv : g *ᵥ v = g *ᵥ (g *ᵥ v) := by rw [Matrix.mulVec_mulVec, hgg]
        rw [hgv, ← hu, Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]
  have hle : (f + g).rank ≤ r := by
    simpa using Matrix.rank_le_card_width (f + g)
  exact hmax (f + g) hf'S (show r - (f + g).rank < r - f.rank by omega)

end GlobalTheory.IsoIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPosPowGaloisFixingFinset
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.PowFix

theorem exists_pos_pow_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (x : Ω) (hx : IsIntegral E x) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  classical
  have hfin : ((minpoly E x).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  haveI := hfin.to_subtype
  let f : ℕ → (minpoly E x).rootSet Ω := fun n => ⟨(σ ^ n) x, by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    rw [show ((σ ^ n) x) = ((σ ^ n : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) x from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val h
  have key : ∀ a b : ℕ, a < b → (σ ^ a) x = (σ ^ b) x → ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
    intro a b hlt he
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e, AlgEquiv.mul_apply] at he
    exact ((σ ^ a).injective he).symm
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt h'
  · exact key b a hlt h'.symm

theorem pow_apply_eq_of_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (τ : Ω ≃ₐ[E] Ω) (x : Ω) (h : τ x = x) (j : ℕ) : (τ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem exists_pos_pow_fix : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  intro E Ω _ _ _ _ _ σ s
  classical
  have hint : ∀ x : Ω, IsIntegral E x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral
  choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)
  refine ⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
  rw [hc, pow_mul]
  exact pow_apply_eq_of_apply_eq _ x (hk x) c

end GlobalTheory.PowFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinset
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  intro E Ω _ _ _ _ _ s
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E (s : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E K
  refine ⟨(α : Ω), fun σ => ?_⟩
  have key : IntermediateField.adjoin E {(α : Ω)} = K := by
    have h1 := congrArg (IntermediateField.map K.val) hα
    rw [IntermediateField.adjoin_map] at h1
    have hm : IntermediateField.map K.val ⊤ = K := by
      ext y; constructor
      · rintro ⟨z, -, rfl⟩; exact z.2
      · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hm] at h1
    simpa [Set.image_singleton] using h1

  have gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y := by
    intro T hT y hy
    have := IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl
      (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val)
      (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])
    exact congrArg (fun φ => φ ⟨y, hy⟩) this
  constructor
  · intro h x hx
    have hxK : x ∈ IntermediateField.adjoin E {(α : Ω)} := by
      rw [key]; exact IntermediateField.subset_adjoin E _ hx
    exact gen {(α : Ω)} (by simpa using h) x hxK
  · intro h
    exact gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_primitiveRoot_coeffRing_of_good {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    (h : Good K 1 LL) : ∃ ζ : ↥(OL LL), IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hdeg : (Polynomial.cyclotomic l (Om l)).degree ≠ 0 :=
    (Polynomial.degree_cyclotomic_pos l (Om l) hl).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  have hζ : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) ?_
    apply IntermediateField.subset_adjoin
    change z ^ (l ^ 1) = 1
    rw [pow_one]
    exact hζ.pow_eq_one
  have hLL : z ∈ LL.1 := h.2.2.2 (Ks K 1).val ⟨z, hmem⟩
  have hζ' : IsPrimitiveRoot (⟨z, hLL⟩ : ↥LL.1) l :=
    IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ Subtype.val_injective
  have hint : IsIntegral ℤ_[l] (⟨z, hLL⟩ : ↥LL.1) :=
    IsIntegral.of_pow hl (by rw [hζ'.pow_eq_one]; exact isIntegral_one)
  exact ⟨⟨⟨z, hLL⟩, hint⟩,
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζ' Subtype.val_injective⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegree
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

open NumberField IsDedekindDomain Polynomial in
private theorem dvd_of_primitiveRoot_pow_pow_eq_self {Ω : Type} [Field Ω] {q k m : ℕ} (hq : 1 < q)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (q ^ k - 1)) (hpos : 0 < q ^ k - 1) (hm : ζ ^ q ^ m = ζ) :
    k ∣ m := by
  have hz : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have h1 : q ^ k - 1 ∣ q ^ m - 1 := by
    apply hζ.dvd_of_pow_eq_one
    have h0 : ζ ^ (q ^ m - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), one_mul]
      exact hm
    exact mul_right_cancel₀ hz h0
  have h2 := Nat.pow_sub_one_gcd_pow_sub_one q k m
  rw [Nat.gcd_eq_left h1] at h2
  have h3 : q ^ k = q ^ Nat.gcd k m := by
    have := Nat.one_le_pow (Nat.gcd k m) q (by omega)
    have := Nat.one_le_pow k q (by omega)
    omega
  have h4 := Nat.pow_right_injective hq h3
  rw [h4]
  exact Nat.gcd_dvd_right k m


open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.exists_fixed_dvd_deg : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (k : ℕ), 0 < k →
    ∃ ζ : Ω, ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ζ = ζ → (k : ℤ) ∣ _root_.GlobalTheory.WeilDeligne.deg σ := by
  intro E Ω _ _ _ _ _ A w h k hk
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq1 : 1 < _root_.Formalism.ConjugateSelfDual.normV w := _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  have hpos : 0 < _root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hk.ne' hq1)
  haveI : NeZero ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hpos.ne')⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1)
  have hvN : ¬ A.valuation ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) < 1 := by
    have hmem : ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
      intro hN
      have h1 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ∈ w.asIdeal := by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using Ideal.absNorm_mem w.asIdeal
      have h2 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k ∈ w.asIdeal := Ideal.pow_mem_of_mem _ h1 _ hk
      have h3 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k - ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) = 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
        ring
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h3 ▸ sub_mem h2 hN))
    simpa using _root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hmem h 1
  have hζv : A.valuation ζ ≤ 1 := le_of_eq (_root_.ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hpos.ne' hζ.pow_eq_one)
  have hroot : ∀ m : ℕ, (ζ ^ _root_.Formalism.ConjugateSelfDual.normV w ^ m) ^ (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1) = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ, fun σ hσ => ?_⟩
  rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hd
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := m) (b := 0)
      (by rw [hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN hζ.pow_eq_one (hroot m) hv
    rw [hm]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq.symm)
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hd.le)
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := 0) (b := m)
      (by rw [← hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN (hroot m) hζ.pow_eq_one hv
    rw [← neg_neg (_root_.GlobalTheory.WeilDeligne.deg σ), hm, dvd_neg]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveValuationIsIntegralIffNonneg
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_surjective_valuation_isIntegral_iff (K : UQ) (L : Type) [Field L] [Algebra K.E L]
    [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L] :
    ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧
      ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  haveI hdvr := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure K.O K.E L
  haveI hfr := integralClosure.isFractionRing_of_finite_extension (A := K.O) K.E L
  set R := integralClosure K.O L
  let P := IsDiscreteValuationRing.maximalIdeal R
  let u : Lˣ →* Multiplicative ℤ := WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (P.valuation L).toMonoidWithZeroHom.toMonoidHom)
  have hu : ∀ x : Lˣ, ((u x : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = P.valuation L x := by
    intro x
    simp [u, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  have key : ∀ x : L, x ≠ 0 → (IsIntegral K.O x ↔ P.valuation L x ≤ 1) := by
    intro x hx
    rw [← mem_integralClosure_iff]
    constructor
    · intro h
      have : x = algebraMap R L ⟨x, h⟩ := rfl
      rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    · intro h
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [← hr]; exact r.2
      · by_cases hrm : r ∈ IsLocalRing.maximalIdeal R
        · exfalso
          have h1 : P.valuation L (algebraMap R L r) < 1 :=
            (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem P r).2 hrm
          rw [hr] at h1
          have h2 : P.valuation L x * P.valuation L x⁻¹ = 1 := by
            rw [← map_mul, mul_inv_cancel₀ hx, map_one]
          have h3 : P.valuation L x * P.valuation L x⁻¹ < 1 :=
            lt_of_le_of_lt (mul_le_of_le_one_left' h) h1
          exact (ne_of_lt h3) h2
        · have hru : IsUnit r := by
            by_contra hh; exact hrm ((IsLocalRing.mem_maximalIdeal r).2 hh)
          obtain ⟨s, hs⟩ := hru
          have : x = algebraMap R L (s⁻¹ : Rˣ) := by
            have e1 : algebraMap R L (s : R) * algebraMap R L ((s⁻¹ : Rˣ) : R) = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            rw [hs, hr] at e1
            exact (inv_mul_eq_one₀ hx).1 e1
          rw [this]; exact ((s⁻¹ : Rˣ) : R).2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R L π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R L) _ h)
  let πL : Lˣ := Units.mk0 _ hπ0
  have huπ : u πL = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hu]
    change P.valuation L (algebraMap R L π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton P hπ.ne_zero hπ.maximalIdeal_eq]
    rfl
  refine ⟨u⁻¹, ?_, ?_⟩
  · intro n
    refine ⟨πL ^ (Multiplicative.toAdd n), ?_⟩
    rw [map_zpow, MonoidHom.inv_apply, huπ, ← ofAdd_neg, neg_neg, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    rfl
  · intro x
    rw [key _ x.ne_zero, ← hu, MonoidHom.inv_apply, toAdd_inv, neg_nonneg, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRatStatement
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGaloisInertia_lifts_absoluteInertia_rat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  first | exact @GlobalTheory.InertiaLift.main | exact GlobalTheory.InertiaLift.main | (intros; apply GlobalTheory.InertiaLift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtensionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L], {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  first | exact @GlobalTheory.InertiaAlmostAll.finite_ramified | exact GlobalTheory.InertiaAlmostAll.finite_ramified | (intros; apply GlobalTheory.InertiaAlmostAll.finite_ramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentDecompositionOfIntegralityStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_decomposition_of_integrality : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] [IsUltrametricDist F] (A : Et F E), (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) → ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧ (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧ ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  first | exact @GlobalTheory.JR.Et.Idem.main | exact GlobalTheory.JR.Et.Idem.main | (intros; apply GlobalTheory.JR.Et.Idem.main <;> assumption)
end

