module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOC
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FiniteAlgIdem

open Polynomial

theorem isCoprime_multiset_prod_left {R : Type} [CommRing R] (s : Multiset R) (y : R)
    (h : ∀ x ∈ s, IsCoprime x y) : IsCoprime s.prod y := by
  induction s using Multiset.induction_on with
  | empty => exact isCoprime_one_left
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a s)).mul_left
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem monic_eq_prod_X_sub_C {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) (f : O[X]) (hf : f.Monic) :
    ∃ r : Multiset O, f = (r.map fun x => X - C x).prod := by
  classical
  have hinj : Function.Injective (algebraMap O L) := hv.hom_inj
  have hs : (f.map (algebraMap O L)).Splits := IsAlgClosed.splits _
  have hm : (f.map (algebraMap O L)).Monic := hf.map _
  have hroot : ∀ x ∈ (f.map (algebraMap O L)).roots, ∃ y, algebraMap O L y = x := by
    intro x hx
    have hint : IsIntegral O x := ⟨f, hf, by
      rw [← Polynomial.eval_map]
      exact (Polynomial.mem_roots hm.ne_zero).1 hx⟩
    exact hv.exists_of_le_one ((Valuation.mem_integer_iff _ _).1 (hv.mem_of_integral hint))
  refine ⟨(f.map (algebraMap O L)).roots.map (Function.invFun (algebraMap O L)), ?_⟩
  apply Polynomial.map_injective _ hinj
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm]
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp [Function.invFun_eq (hroot x hx)]

theorem exists_prod_sub_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) {A : Type} [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (a : A) :
    ∃ r : Multiset O, (r.map fun x => a - algebraMap O A x).prod = 0 := by
  obtain ⟨f, hf, hfa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
  obtain ⟨r, hr⟩ := monic_eq_prod_X_sub_C hv f hf
  refine ⟨r, ?_⟩
  have h : aeval a f = 0 := hfa
  rw [hr, map_multiset_prod, Multiset.map_map] at h
  simpa [Function.comp_def] using h

theorem exists_mem_eq {O : Type} [CommRing O] {A K : Type} [CommRing A] [Algebra O A]
    [CommRing K] [IsDomain K] [Algebra O K] (c : A →ₐ[O] K) {a : A} {r : Multiset O}
    (hr : (r.map fun x => a - algebraMap O A x).prod = 0) :
    ∃ x ∈ r, c a = algebraMap O K x := by
  have h := congrArg c hr
  rw [map_multiset_prod, Multiset.map_map, map_zero, Multiset.prod_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 h
  refine ⟨x, hx, ?_⟩
  simp only [Function.comp_apply, map_sub, AlgHom.commutes] at hx0
  exact sub_eq_zero.1 hx0


open Classical in
theorem exists_idempotent {O : Type} [CommRing O] [IsLocalRing O] {A : Type} [CommRing A]
    [Algebra O A] {a : A} {r : Multiset O} (hr : (r.map fun x => a - algebraMap O A x).prod = 0)
    (ρ : IsLocalRing.ResidueField O) :
    ∃ e : A, IsIdempotentElem e ∧ ∀ c : A →ₐ[O] IsLocalRing.ResidueField O,
      c e = if c a = ρ then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : O[X],
      g = ((r.filter fun x => IsLocalRing.residue O x = ρ).map fun x => X - C x).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : O[X],
      h = ((r.filter fun x => ¬ IsLocalRing.residue O x = ρ).map fun x => X - C x).prod :=
    ⟨_, rfl⟩
  have hgh : g * h = (r.map fun x => X - C x).prod := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add (f := _), Multiset.filter_add_not]
  have hcop : IsCoprime g h := by
    rw [hg]
    apply isCoprime_multiset_prod_left
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hp
    rw [hh]
    apply IsCoprime.symm
    apply isCoprime_multiset_prod_left
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hq
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    rw [map_sub, (Multiset.mem_filter.1 hx).2, sub_ne_zero]
    exact (Multiset.mem_filter.1 hy).2
  obtain ⟨u, w, huw⟩ := hcop
  have hF : aeval a (g * h) = 0 := by
    rw [hgh, map_multiset_prod, Multiset.map_map]
    simpa [Function.comp_def] using hr
  refine ⟨aeval a (w * h), ?_, ?_⟩
  · have key : w * h * (w * h) = w * h - u * w * (g * h) := by
      linear_combination (w * h) * huw
    show aeval a (w * h) * aeval a (w * h) = aeval a (w * h)
    rw [← map_mul, key, map_sub, map_mul (aeval a) (u * w), hF, mul_zero, sub_zero]
  · intro c
    rw [← Polynomial.aeval_algHom_apply]
    obtain ⟨x, hx, hcx⟩ := exists_mem_eq c hr
    rw [IsLocalRing.ResidueField.algebraMap_eq] at hcx
    have h1 := congrArg (aeval (c a)) huw
    rw [map_add (f := _), map_mul, map_mul, map_one] at h1
    by_cases hρ : IsLocalRing.residue O x = ρ
    · have hg0 : aeval (c a) g = 0 := by
        rw [hg, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_pos (hcx.trans hρ), map_mul]
      rw [hg0, mul_zero, zero_add] at h1
      exact h1
    · have hh0 : aeval (c a) h = 0 := by
        rw [hh, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_neg (show ¬ c a = ρ by rwa [hcx]), map_mul, hh0, mul_zero]

end GlobalTheory.FiniteAlgIdem

namespace GlobalTheory.FiniteAlgIdem

theorem idempotent_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) {A : Type}
    [CommRing A] [Algebra O A] [Algebra.IsIntegral O A] {s : A} (hs : IsIdempotentElem s)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c s = 0) : s = 0 := by
  by_contra hne
  have hI : Ideal.span {1 - s} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    apply hne
    have h0 : (1 - s) * s = 0 := by rw [sub_mul, one_mul, hs.eq, sub_self]
    exact hu.mul_right_eq_zero.1 h0
  obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal _ hI
  let ψ : O →ₐ[O] A ⧸ M := Algebra.ofId O (A ⧸ M)
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨r, hr⟩ := exists_prod_sub_eq_zero hv b
    obtain ⟨x, -, hbx⟩ := exists_mem_eq (Ideal.Quotient.mkₐ O M) hr
    exact ⟨x, by rw [Algebra.ofId_apply, ← hbx]; rfl⟩
  have hker : ∀ y ∈ RingHom.ker ψ, (Algebra.ofId O (IsLocalRing.ResidueField O)) y = 0 := by
    intro y hy
    have hne : RingHom.ker ψ ≠ ⊤ := by
      rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
      exact one_ne_zero
    rw [Algebra.ofId_apply, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact IsLocalRing.le_maximalIdeal hne hy
  let c : A →ₐ[O] IsLocalRing.ResidueField O :=
    (Ideal.Quotient.liftₐ (RingHom.ker ψ) (Algebra.ofId O _) hker).comp
      ((Ideal.quotientKerAlgEquivOfSurjective hψ).symm.toAlgHom.comp (Ideal.Quotient.mkₐ O M))
  have hm : Ideal.Quotient.mkₐ O M (1 - s) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM (Ideal.mem_span_singleton_self _)
  have h1 : c (1 - s) = 0 := by
    simp only [c, AlgHom.comp_apply, hm, map_zero]
  rw [map_sub, map_one, h c, sub_zero] at h1
  exact one_ne_zero h1

theorem finite_and_idempotents {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] :
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
        (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
        ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  classical
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := A)
  choose r hr using fun a : A => exists_prod_sub_eq_zero hv a
  choose E hEi hEc using fun (a : A) (ρ : IsLocalRing.ResidueField O) =>
    exists_idempotent (hr a) ρ
  have hsep : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      (∀ j ∈ S, c' j = c j) → c' = c := by
    intro c c' hcc
    apply AlgHom.toLinearMap_injective
    exact LinearMap.ext_on hS fun x hx => hcc x hx
  let e : (A →ₐ[O] IsLocalRing.ResidueField O) → A := fun c => ∏ j ∈ S, E j (c j)
  have hec : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      c' (e c) = if c = c' then 1 else 0 := by
    intro c c'
    simp only [e, map_prod, hEc]
    by_cases hcc : c = c'
    · subst hcc
      rw [if_pos rfl, Finset.prod_boole, if_pos (fun j _ => rfl)]
    · rw [if_neg hcc, Finset.prod_boole, if_neg (fun hh => hcc (hsep c c' hh).symm)]
  have hei : ∀ c, IsIdempotentElem (e c) := fun c =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ ha hb => ha.mul hb)
      IsIdempotentElem.one (fun j _ => hEi _ _)
  have hort : ∀ c c', c ≠ c' → e c * e c' = 0 := by
    intro c c' hne
    apply idempotent_eq_zero hv ((hei c).mul (hei c'))
    intro c''
    rw [map_mul, hec, hec]
    split_ifs with h1 h2 <;> simp_all
  have hfin : Finite (A →ₐ[O] IsLocalRing.ResidueField O) := by
    let T : S → Finset (IsLocalRing.ResidueField O) := fun j =>
      ((r j).map (algebraMap O (IsLocalRing.ResidueField O))).toFinset
    let F : (A →ₐ[O] IsLocalRing.ResidueField O) → (∀ j : S, T j) := fun c j =>
      ⟨c j, by
        obtain ⟨x, hx, hcx⟩ := exists_mem_eq c (hr j)
        simp only [T, Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨x, hx, hcx.symm⟩⟩
    refine Finite.of_injective F ?_
    intro c c' hcc
    exact hsep c' c fun j hj => congrArg Subtype.val (congrFun hcc ⟨j, hj⟩)
  refine ⟨hfin, e, hei, hort, ?_, ?_⟩
  · haveI := hfin
    letI := Fintype.ofFinite (A →ₐ[O] IsLocalRing.ResidueField O)
    rw [finsum_eq_sum_of_fintype]
    have horth : OrthogonalIdempotents e := ⟨hei, fun c c' h => hort c c' h⟩
    have hsum := horth.isIdempotentElem_sum (s := Finset.univ)
    have h0 := idempotent_eq_zero hv hsum.one_sub (fun c'' => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_one, map_sum]
      simp [hec])
    exact (sub_eq_zero.1 h0).symm
  · intro c c'
    rw [hec]
    split_ifs with h <;> simp [h]

end GlobalTheory.FiniteAlgIdem

theorem GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A],
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
    ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
    (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
    ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _
  exact GlobalTheory.FiniteAlgIdem.finite_and_idempotents hv A
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductions
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isMonHom_of_fst_mul_snd {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by
  have hm : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ g = (x ≫ g) * (y ≫ g) := fun T x y => by
    have := congrArg (lift x y ≫ ·) h
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using this
  refine ⟨?_, ?_⟩
  · have h1 := hm (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S) ⟶ A) ≫ g = 1 := left_eq_mul.1 h1
    simpa [Hom.one_def] using h2
  · have e : (fst A A * snd A A) = μ[A] := by simp [Hom.mul_def]
    rw [e] at h
    rw [h, Hom.mul_def]
    congr 1

theorem mul_comp_of_isGrpPullback {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by
  let x' : T ⟶ Y := Over.homMk (ha.1.lift x.left T.hom (Over.w x)) (ha.1.lift_snd _ _ _)
  let y' : T ⟶ Y := Over.homMk (ha.1.lift y.left T.hom (Over.w y)) (ha.1.lift_snd _ _ _)
  have hx : x.left = x'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have hy : y.left = y'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have h1 := ha.2 T x' y' x y hx hy
  have h2 := hb.2 T (x' ≫ f) (y' ≫ f) (x ≫ g) (y ≫ g)
    (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hg])
    (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hg])
  ext
  rw [h2, Over.comp_left, h1, ← MonObj.mul_comp, Over.comp_left, Category.assoc, Category.assoc, hg]

theorem grpHom_algebraise : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  intro H R _ _ I hI A B _ _ hA hB Y Z _ _ β δ a b ha hβ hb hδ f hf hc
  obtain ⟨g, hg, hu⟩ := H R I hI A B hA inferInstance inferInstance inferInstance Y β a
    (fun e => (ha e).1) hβ (fun e => (f e).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← Category.assoc, hc, Category.assoc, hδ])
  refine ⟨g, isMonHom_of_fst_mul_snd g ?_, hg, hu⟩
  haveI : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  refine H.hom_ext hI fun e => ?_
  haveI := hf e
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (pullback.snd (A ⊗ A).hom (thick R I e))
  let P : Over.mk (T.hom ≫ thick R I e) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst (A ⊗ A).hom (thick R I e)) pullback.condition
  have key := mul_comp_of_isGrpPullback (ha e) (hb e) (f e) g (hg e) T (P ≫ fst A A) (P ≫ snd A A)
  have key' : P ≫ (fst A A * snd A A) ≫ g = P ≫ ((fst A A ≫ g) * (snd A A ≫ g)) := by
    rw [← Category.assoc, MonObj.comp_mul, key, MonObj.comp_mul, Category.assoc, Category.assoc]
  exact congrArg (·.left) key'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def HaarChart (X : Data E r) (c : ℝ≥0∞) : Prop :=
  ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ g, φ (frameOf X g) ∂haarR X = c * ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X)

def trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
    (y : Frame X.Ψ r) : Frame X'.Ψ r :=
  fun τ' => (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') : Matrix (Fin r) (Fin r) ℂ)

end

end GlobalTheory.FlagQuotHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtDeformedProductDerivativeTerm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum

theorem hasDerivAt_inv_pow_affine (c a b : ℂ) (n : ℕ) (u : ℂ) (hu : a + u * b ≠ 0) :
    HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (-(n : ℂ) * b * (a + u * b)⁻¹ ^ (n + 1))) u := by
  have h1 : HasDerivAt (fun t : ℂ => a + t * b) b u := by
    simpa using ((hasDerivAt_id u).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (n * (a + u * b)⁻¹ ^ (n - 1) * (-b / (a + u * b) ^ 2))) u :=
    ((h1.inv hu).pow n).const_mul c
  refine h2.congr_deriv ?_
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring

theorem defCoord_ne_zero {E : Type} [Field E] [NumberField E] {I : Type} (φ : I → E →+* ℂ) (z : I → ℂ)
    (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have hφ : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx
  have hpos : 0 < ‖φ i x‖ := norm_pos_iff.mpr hφ
  have hz1 : ‖z i‖ < 1 := hz i
  unfold defCoord at h
  have heq : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have hn : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [heq]
    rw [norm_neg, norm_mul, Complex.norm_conj]
  have hlt := mul_lt_of_lt_one_left hpos hz1
  linarith

theorem hasFDerivAt_dTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ)
    (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x)
      (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  intro E _ _ I _ _ φ k m x hx z hz
  set C : I → ℂ := fun i => ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) *
    (starRingEnd ℂ (φ i x)) ^ m i with hC
  have hd : ∀ i, HasFDerivAt (fun w : I → ℂ => C i * (defCoord φ w x i)⁻¹ ^ (k + m i))
      ((C i * (-((k + m i : ℕ) : ℂ) * starRingEnd ℂ (φ i x) * (defCoord φ z x i)⁻¹ ^ (k + m i + 1))) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) z := by
    intro i
    have h1 := hasDerivAt_inv_pow_affine (C i) (φ i x) (starRingEnd ℂ (φ i x)) (k + m i) (z i)
      (defCoord_ne_zero φ z hz x hx i)
    have h2 := h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : I => ℂ) i z)
    exact h2
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hfun : (fun w : I → ℂ => dTerm φ k m w x) =
      (fun w => ∏ i ∈ Finset.univ, C i * (defCoord φ w x i)⁻¹ ^ (k + m i)) := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  symm
  unfold dTerm
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [hC, hij]
  · simp only [hC, Pi.add_apply, Pi.single_eq_same, Finset.prod_range_succ]
    push_cast
    ring

end GlobalTheory.DeformedSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValue
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_unique' {F : Type} [Field F] [NumberField F] {k : ℕ}
    {L : _root_.GlobalTheory.HilbFam.Lat F} {b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ} {G G' : ℂ}
    (h : _root_.GlobalTheory.HilbFam.IsGVal k L b a G)
    (h' : _root_.GlobalTheory.HilbFam.IsGVal k L b a G') : G = G' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨h₁', h₂'⟩ := h'
  by_cases hk : k = 2
  · subst hk
    obtain ⟨H, hH, hsum, rfl⟩ := h₂ rfl
    obtain ⟨H', hH', hsum', rfl⟩ := h₂' rfl
    have hU : IsOpen {σ : ℂ | -1 / 2 < σ.re} := isOpen_lt continuous_const Complex.continuous_re
    have hC : IsPreconnected {σ : ℂ | -1 / 2 < σ.re} := (convex_halfSpace_re_gt _).isPreconnected
    have hone : (1 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num
    have hzero : (0 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.zero_re]; norm_num
    have hev : H =ᶠ[nhds 1] H' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact (hsum σ hσ).unique (hsum' σ hσ)
    exact (hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hH'.analyticOnNhd hU) hC
      hone hev hzero
  · exact (h₁ hk).unique (h₁' hk)


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (G : ℂ),
    _root_.GlobalTheory.HilbFam.IsGVal k L b a G → _root_.GlobalTheory.HilbFam.gval k L b a = G := by
  intro F _ _ _ k L b a G hG
  have h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := ⟨G, hG⟩
  rw [_root_.GlobalTheory.HilbFam.gval, dite_eq_left h]
  exact isGVal_unique' h.choose_spec hG

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  first | (exact @GlobalTheory.EtC.DiscSupp.bijective_disc) | (exact GlobalTheory.EtC.DiscSupp.bijective_disc) | (intros; apply GlobalTheory.EtC.DiscSupp.bijective_disc  <;> assumption)
end

