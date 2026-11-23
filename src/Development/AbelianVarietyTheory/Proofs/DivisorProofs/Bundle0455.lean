module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
section
open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DenClear

variable {E : Type} [Field E] [NumberField E]

theorem exists_natMul_isIntegral (c : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this

theorem intSmul_eq {r : ℕ} (a : 𝓞 E) (w : Fin r → E) : a • w = (a : E) • w := by
  rw [← algebraMap_smul E a w]

theorem exists_natSmul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))) : ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : ((n * m : ℕ) : E) • (x + y) = m • ((n : E) • x) + n • ((m : E) • y) := by
      simp only [Nat.cast_mul, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem hnx m) (Λ.nsmul_mem hmy n)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hc⟩ := exists_natMul_isIntegral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, (a : E) = (m : E) * c := ⟨⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩, rfl⟩
    have e : ((m * n : ℕ) : E) • (c • x) = a • ((n : E) • x) := by
      rw [intSmul_eq, ha, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact Λ.smul_mem _ hnx

variable [IsCMField E]

theorem exists_natSmul_mem_lieLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 →
    (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) → ∃ N : ℕ, 0 < N ∧ (N : E) • X ∈ lieLat G Λ := by
  intro E _ _ _ r G Λ hfg hspan X htr hskew
  obtain ⟨S, hS⟩ := hfg
  have hv : ∀ s : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • (X *ᵥ s) ∈ Λ := fun s =>
    exists_natSmul_mem Λ _ (by rw [hspan]; trivial)
  choose n hn hnX using hv
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_, ?_, ?_⟩
  · rw [trace_smul, htr, smul_zero]
  · intro x y
    have h := hskew x y
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at h ⊢
    have e1 : ∀ a b, (↑(∏ s ∈ S, n s) * (X *ᵥ x) a) * G a b * (IsCMField.complexConj E) (y b) =
        (↑(∏ s ∈ S, n s) : E) * ((X *ᵥ x) a * G a b * (IsCMField.complexConj E) (y b)) := fun a b => by ring
    have e2 : ∀ a b, x a * G a b * ((↑(∏ s ∈ S, n s) : E) * (IsCMField.complexConj E) ((X *ᵥ y) b)) =
        (↑(∏ s ∈ S, n s) : E) * (x a * G a b * (IsCMField.complexConj E) ((X *ᵥ y) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h, mul_zero]
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [smul_mulVec]
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hs
      rw [hk, Nat.cast_mul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
      exact Λ.nsmul_mem (hnX s) k
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [intSmul_eq, mulVec_smul, ← intSmul_eq]
      exact Λ.smul_mem a hx

end GlobalTheory.DenClear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwise
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ContLevel

theorem chains_map_f (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (k : ℕ) :
    ((chains R).map φ).f (-(k : ℤ)) = (chainsXIso R E k).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv :=
  HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := k) rfl

end GlobalTheory.EtC.ContLevel


open GlobalTheory.EtC.ContLevel in
theorem GlobalTheory.EtC.contCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  intro R _ F I _ _ G c hG
  obtain ⟨-, hneg, -, -, -, hpos⟩ := _root_.GlobalTheory.EtC.res_basic R F
  obtain ⟨cl, hsurj, hiff, hzero, hpull⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  refine fun n => GlobalTheory.EtC.cont_cx_of_degreewise R I (G ⋙ chains R) ((chains R).mapCone c) (res R F)
     (fun i p hp => hpos (G.obj i) p hp) (fun p hp => hpos c.pt p hp) hneg ?_ n
  intro p s
  by_cases hp : 0 < p
  · constructor
    · intro t _
      obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
      refine ⟨i, 0, 0, zero_comp, ?_⟩
      have : t = 0 := (hpos c.pt p hp).eq_of_src _ _
      simp [this]
    · intro i u _ _
      refine ⟨i, 𝟙 i, 0, ?_⟩
      have : u = 0 := (hpos (G.obj i) p hp).eq_of_src _ _
      simp [this]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    have hk := hG (op (SimplexCategory.mk k)) s
    constructor
    · intro t ht
      let t' := (chainsXIso R c.pt k).inv ≫ t
      have ht' : t' ≫ (res R F).d s (s + 1) = 0 := by simp [t', ht]
      obtain ⟨i, y, hy⟩ := hk.1 (cl _ s t' ht')
      obtain ⟨u', hu', rfl⟩ := hsurj _ s y
      obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
      change pull R (disc.map ((c.π.app i).app (op (SimplexCategory.mk k)))) F s _ = _ at hy
      rw [hp2, hiff] at hy
      obtain ⟨y', hy'⟩ := hy
      refine ⟨i, (chainsXIso R (G.obj i) k).hom ≫ u', (chainsXIso R c.pt k).hom ≫ y', by simp [hu'], ?_⟩
      change ((chains R).map (c.π.app i)).f _ ≫ _ = _
      rw [chains_map_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hy']
      simp [t', Preadditive.comp_add]
    · rintro i u hu ⟨y, hy⟩
      let u' := (chainsXIso R (G.obj i) k).inv ≫ u
      have hu' : u' ≫ (res R F).d s (s + 1) = 0 := by simp [u', hu]
      have hdie : pull R ((((evaluation _ PSh).obj (op (SimplexCategory.mk k)) ⋙ disc).mapCone c).π.app i) F s
          (cl _ s u' hu') = 0 := by
        change pull R (disc.map ((c.π.app i).app _)) F s _ = 0
        obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
        rw [hp2, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) s, hiff]
        refine ⟨(chainsXIso R c.pt k).inv ≫ y, ?_⟩
        change ((chains R).map (c.π.app i)).f _ ≫ u = _ at hy
        rw [chains_map_f] at hy
        rw [zero_add, Category.assoc, ← hy]
        simp [u']
      obtain ⟨k', f, hf⟩ := hk.2 i _ hdie
      change pull R (disc.map ((G.map f).app (op (SimplexCategory.mk k)))) F s _ = 0 at hf
      obtain ⟨h3, hp3⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((G.map f).app (op (SimplexCategory.mk k))) s u' hu'
      rw [hp3, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) s, hiff] at hf
      obtain ⟨y'', hy''⟩ := hf
      refine ⟨k', f, (chainsXIso R (G.obj k') k).hom ≫ y'', ?_⟩
      change ((chains R).map (G.map f)).f _ ≫ u = _
      rw [chains_map_f, zero_add] at *
      simp only [Category.assoc]
      exact congrArg ((chainsXIso R (G.obj k') k).hom ≫ ·) hy''

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditive
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace KumNat
open ClsSpec

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) {s : ℤ} (hs : s < 0) :
    Subsingleton (Sec ((res R F).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p s h U x) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 α β p s h U x).2.1

variable {q : ℕ}

theorem kum_unique [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ γ' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h₁' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ' 1 0 (by simp) U x = 0)
    (h₂' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ' 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    change U ⟶ X at x
    refine sep (ClsSpec.loc_mono (root_loc (unit_res x hX) (umap x u)) fun V g ⟨v, hv⟩ => ?_)
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 0 1 _ V U g x]
    have hv' : v ^ q = umap (g ≫ x) u := by rw [hv, umap_comp]
    exact (h₂ V (g ≫ x) v hv').trans (h₂' V (g ≫ x) v hv').symm
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact (h₁ U x).trans (h₁' U x).symm
  | p + 2 =>
    haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
    exact Subsingleton.elim _ _

theorem eq_zero_of_kumT [NeZero q] (ht : kumT q = 0) {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = 0 :=
  kum_unique hX u h₁ h₂ (fun U x => ev_zero (E := sch.obj X) _ _ _ _ _)
    (fun U x v _ => (ev_zero (E := sch.obj X) _ _ _ _ _).trans (by rw [ht]; exact (smap_zero _).symm))

theorem kum_pull [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) (hX : IsUnit (q : Γ(X, ⊤))) :
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u) := by
  obtain ⟨γ, hγ, h₁, h₂⟩ := kum_spec q hX u
  obtain ⟨γ', hγ', h₁', h₂'⟩ := kum_spec q (unit_res f hX) (umap f u)
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine Cocycle.ext (kum_unique (unit_res f hX) (umap f u) (fun U y => ?_) (fun U y v hv => ?_) h₁' h₂')
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 1 0 _ U y = 0
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 _ U y]
    exact h₁ U (y ≫ f)
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 0 1 _ U y = _
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 _ U y]
    exact h₂ U (y ≫ f) v (by rw [hv, umap_comp])

theorem kum_mul [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u₁ u₂ : (Γ(X, ⊤))ˣ) :
    kum q (u₁ * u₂) = kum q u₁ + kum q u₂ := by
  obtain ⟨γ₁, e₁, a₁, b₁⟩ := kum_spec q hX u₁
  obtain ⟨γ₂, e₂, a₂, b₂⟩ := kum_spec q hX u₂
  obtain ⟨γ₃, e₃, a₃, b₃⟩ := kum_spec q hX (u₁ * u₂)
  rw [← e₁, ← e₂, ← e₃, eq_comm, ← CohomologyClass.mk_add, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨e, he, hw⟩ := exists_two_family ht (E := sch.obj X) (p := 0) (fun U (x : U ⟶ X) => unit_res x hX)
      (fun U (x : U ⟶ X) => umap x u₁) (fun U (x : U ⟶ X) => umap x u₂)
      (fun V U g (x : U ⟶ X) => umap_comp g x u₁) (fun V U g (x : U ⟶ X) => umap_comp g x u₂)
    obtain ⟨β, c₁, c₂⟩ := exists_single (I := res _ (tw q 1)) (n := 0) 0 0 (by simp) e he
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    rw [Cocycle.coe_sub, Cocycle.coe_add, ev_sub', ev_add]
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      have hxU := unit_res (show U ⟶ X from x) hX
      refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hxU (umap (show U ⟶ X from x) u₁))
        (root_loc hxU (umap (show U ⟶ X from x) u₂))) ?_)
      rintro V g ⟨⟨v, hv⟩, w, hw'⟩
      have hv' : v ^ q = umap (show V ⟶ X from x.res g) u₁ := by rw [hv]; exact (umap_comp g _ u₁).symm
      have hw'' : w ^ q = umap (show V ⟶ X from x.res g) u₂ := by rw [hw']; exact (umap_comp g _ u₂).symm
      have hvw : (v * w) ^ q = umap (show V ⟶ X from x.res g) (u₁ * u₂) := by rw [mul_pow, hv', hw'', map_mul]
      rw [res_map, he V U g x, res_sub, res_add, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₁.1 0 1 _ V U g x,
        (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₂.1 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₃.1 0 1 _ V U g x]
      rw [hw V (x.res g) v w hv' hw'', b₁ V (x.res g) v hv', b₂ V (x.res g) w hw'', b₃ V (x.res g) _ hvw, smap_sub,
        smap_add]
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a₁ U x, a₂ U x, a₃ U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · refine ⟨0, ?_⟩
    rw [δ_zero, Cocycle.coe_sub, Cocycle.coe_add, eq_zero_of_kumT ht hX u₁ a₁ b₁, eq_zero_of_kumT ht hX u₂ a₂ b₂,
      eq_zero_of_kumT ht hX _ a₃ b₃]
    simp

theorem kum_pow_self [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) : kum q (u ^ q) = 0 := by
  obtain ⟨γ, e, a, b⟩ := kum_spec q hX (u ^ q)
  rw [← e, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨β, c₁, c₂⟩ := exists_single (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) 0 0 (by simp)
      (fun U (x : U ⟶ X) => kumT q U (umap x u))
      (fun V U g (x : U ⟶ X) => (ht.1 V U g _ (unit_res x hX)).trans (congrArg (kumT q V) (umap_comp g x u).symm))
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      change U ⟶ X at x
      exact (b U x _ (by rw [← map_pow])).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · exact ⟨0, by rw [δ_zero, eq_zero_of_kumT ht hX _ a b]⟩

end KumNat


open KumNat in
theorem kum_cocycle_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u → ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧ ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 := by
  intro q _
  exact ⟨fun X u hX => kum_spec q hX u, fun f u hX => kum_pull f u hX, fun u v hX => ⟨kum_mul hX u v, kum_pow_self hX u⟩⟩

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LerayInj

theorem peel (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hH : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (N : ℤ) (hN : (n : ℤ) + 1 = N)
    (c : Cochain ((chains R).obj E) (res R F) N)
    (hc : ∀ (p q : ℤ) (hpq : p + N = q), p ≠ -N → c.v p q hpq = 0)
    (β₀ : Cochain ((chains R).obj E) (res R F) n) (h₀ : δ n N β₀ = c) :
    ∀ k : ℕ, k ≤ n → ∃ β : Cochain ((chains R).obj E) (res R F) n, δ n N β = c ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(k : ℤ) < p → β.v p q hpq = 0 := by
  obtain ⟨cl, -, hcl, hcl0, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  obtain ⟨-, -, -, -, -, hpos⟩ := _root_.GlobalTheory.EtC.res_basic R F
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨β₀, h₀, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨β, hβ, hv⟩ := ih (by omega)
    have hqk : (((n - k : ℕ) : ℤ)) = (n : ℤ) - k := by omega
    let t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X ((n - k : ℕ) : ℤ) :=
      (chainsXIso R E k).inv ≫ β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) (by omega)
    have ht : t ≫ (res R F).d ((n - k : ℕ) : ℤ) (((n - k : ℕ) : ℤ) + 1) = 0 := by
      have e := Cochain.congr_v hβ (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega)
      rw [δ_v n N hN β (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega) ((n - k : ℕ) : ℤ) (-(k : ℤ) + 1)
        (by omega) rfl, hc _ _ _ (by omega), hv (-(k : ℤ) + 1) (((n - k : ℕ) : ℤ) + 1) (by omega) (by omega),
        comp_zero, smul_zero, add_zero] at e
      simp only [t, Category.assoc, e, comp_zero]
    have h0 : cl _ _ t ht = cl _ _ 0 zero_comp :=
      (hH k (n - k) (by omega) (by omega) _).trans (hcl0 _ _).symm
    obtain ⟨y, hy⟩ := ((hcl _ _ _ _ _ _).1 h0)
    rw [zero_add] at hy
    let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
      Cochain.single (p := -(k : ℤ)) (q := ((n - k : ℕ) : ℤ) - 1) ((chainsXIso R E k).hom ≫ y) ((n : ℤ) - 1)
    refine ⟨β - δ ((n : ℤ) - 1) n γ, ?_, ?_⟩
    · rw [δ_sub, δ_δ, sub_zero, hβ]
    · intro p q hpq hp
      rw [Cochain.sub_v, Cochain.δ_single _ ((n : ℤ) - 1) n (by omega) (-(k : ℤ) - 1) ((n - k : ℕ) : ℤ) (by omega) (by omega),
        Cochain.add_v, Cochain.units_smul_v]
      by_cases hpk : p = -(k : ℤ)
      · subst hpk
        obtain rfl : q = ((n - k : ℕ) : ℤ) := by omega
        rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero]
        have hb : β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) hpq = (chainsXIso R E k).hom ≫ t := by
          simp only [t, Iso.hom_inv_id_assoc]
        rw [hb, hy, Category.assoc, sub_self]
      · rw [hv p q hpq (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpk,
          Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero, sub_zero]

end GlobalTheory.EtC.LerayInj

namespace GlobalTheory.EtC

theorem leray_inj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) →
    (∀ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls (R := R) (E := E) (n := 0) s 0 → s = 0) ∧
    ∀ s : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F, IsCls (R := R) (E := E) (n := n + 1) s 0 →
      ∃ t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd (R := R) (E := E) (n := n) t = s := by
  intro R _ F E n hH
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := _root_.GlobalTheory.EtC.res_basic R F
  constructor
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β, hβ⟩ := hz0
    have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) 0 (by simp)
    have h1 : β.v (-((0 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    have h2 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 := (hpos E 1 (by norm_num)).eq_of_tgt _ _
    rw [δ_v m _ hm β _ 0 _ (-1) 1 (by omega) (by omega), h1, h2, zero_comp, zero_comp, smul_zero,
      add_zero] at e
    have e' : (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).hom ≫ s ≫ resι R F := by
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)) = z.1 from rfl, hz, Cochain.single_v]
    rw [e'] at e
    have e2 : s ≫ resι R F = 0 ≫ resι R F := by
      rw [zero_comp]
      exact (cancel_epi (chainsXIso R E 0).hom).1 (by rw [← e, comp_zero])
    exact (cancel_mono (resι R F)).1 e2
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β₀, hβ₀⟩ := hz0
    obtain rfl : m = (n : ℤ) := by push_cast at hm; omega
    have hzv : ∀ (p q : ℤ) (hpq : p + ((n + 1 : ℕ) : ℤ) = q),
        (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)).v p q hpq =
          (Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
            ((chainsXIso R E (n + 1)).hom ≫ s ≫ resι R F) ((n + 1 : ℕ) : ℤ)).v p q hpq := by
      intro p q hpq
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)) = z.1 from rfl, hz]
    obtain ⟨β, hβ, hv⟩ := LerayInj.peel R F E n hH ((n + 1 : ℕ) : ℤ) (by push_cast; rfl) z
      (fun p q hpq hp => by rw [hzv, Cochain.single_v_eq_zero _ _ _ _ _ hp]) β₀ hβ₀ n le_rfl

    let b := β.v (-(n : ℤ)) 0 (by omega)
    have hb : b ≫ (res R F).d 0 1 = 0 := by
      have e := Cochain.congr_v hβ (-(n : ℤ)) 1 (by push_cast; omega)
      rw [δ_v (n : ℤ) _ (by push_cast; rfl) β (-(n : ℤ)) 1 _ 0 (-(n : ℤ) + 1) (by omega) rfl,
        hv (-(n : ℤ) + 1) 1 (by omega) (by omega), comp_zero, smul_zero, add_zero, hzv,
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
      exact e
    haveI : Mono (ShortComplex.mk _ _ w).f := hmono
    let t' : ((chains R).obj E).X (-(n : ℤ)) ⟶ F := hex.lift b hb
    have ht' : t' ≫ resι R F = b := hex.lift_f b hb

    have e := Cochain.congr_v hβ (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    have h1 : β.v (-((n + 1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    rw [δ_v (n : ℤ) _ (by push_cast; rfl) β _ 0 _ (-1) (-(n : ℤ)) (by omega) (by push_cast; omega), h1,
      zero_comp, zero_add, hzv, Cochain.single_v] at e
    rw [show β.v (-(n : ℤ)) 0 (by omega) = b from rfl, ← ht'] at e
    have hD : ((chainsN R).obj E).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i) :=
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
    let D : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋n⦌)) :=
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
    have hd : ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
        (chainsXIso R E (n + 1)).hom ≫ D ≫ (chainsXIso R E n).inv :=
      (HomologicalComplex.extend_d_eq _ _ rfl rfl).trans
        (congrArg (fun D' => (chainsXIso R E (n + 1)).hom ≫ D' ≫ (chainsXIso R E n).inv) hD)
    rw [hd] at e
    have hs : s = (((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E n).inv ≫ t') := by
      apply (cancel_epi (chainsXIso R E (n + 1)).hom).1
      apply (cancel_mono (resι R F)).1
      rw [Category.assoc, ← e]
      simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    refine ⟨(((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E n).inv ≫ t'), ?_⟩
    rw [hs]
    simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
      smul_smul, Category.assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCoverStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayerVietoris_equivalence_of_cover : GlobalTheory.EtC.A4 := by
  first | (exact @GlobalTheory.MayerVietorisEqv.a4) | (exact GlobalTheory.MayerVietorisEqv.a4) | (intros; apply GlobalTheory.MayerVietorisEqv.a4  <;> assumption)
end

