module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0061
public import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0062

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.DerivUnit
section
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfPrim
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem derivUnit {C : Type} [CommRing C] [Nontrivial C] (q : ℕ) (z : C) (hq : IsUnit (q : C))
    (hz : (cyclotomic q C).eval z = 0) : IsUnit ((derivative (cyclotomic q C)).eval z) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q C
  have hzq : z ^ q = 1 := by
    have := congrArg (eval z) hg
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hz, zero_mul] at this
    exact sub_eq_zero.mp this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hzq hq0
  have hd := congrArg (fun p => (derivative p).eval z) hg
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_add, eval_mul,
    eval_C, eval_pow, eval_X, hz, zero_mul, add_zero] at hd
  have hu : IsUnit ((q : C) * z ^ (q - 1)) := hq.mul (hzu.pow _)
  have hu' : IsUnit ((derivative (cyclotomic q C)).eval z * g.eval z) := by
    rw [← hd]; simpa using hu
  exact isUnit_of_mul_isUnit_left hu'

theorem evalHom {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (p : B[X]) (x : B) :
    f (p.eval x) = (p.map f).eval (f x) := by
  rw [Polynomial.eval_map, eval₂_at_apply]

theorem primLift : LeafPrimLift := by
  intro q B C _ _ _ _ f hf ζ
  have hloc : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨z, hqC, hz⟩ := ζ
  have hz' : (cyclotomic q C).eval z = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic] at hz; exact hz
  have hqB : IsUnit (q : B) := by
    have : IsUnit (f (q : B)) := by simpa using hqC
    exact (isUnit_map_iff f _).mp this
  obtain ⟨a0, rfl⟩ := hf z
  have hker : (cyclotomic q B).eval a0 ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map f
    rw [evalHom, map_cyclotomic, hz'] at this
    exact not_isUnit_zero this
  have hder : IsUnit ((derivative (cyclotomic q B)).eval a0) := by
    apply (isUnit_map_iff f _).mp
    rw [evalHom, ← derivative_map, map_cyclotomic]
    exact derivUnit q (f a0) hqC hz'
  have : IsLocalRing C := IsLocalRing.of_surjective' f hf
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0 hker hder
  have hfa : (cyclotomic q C).eval (f a) = 0 := by
    rw [← map_cyclotomic q f, ← evalHom, ha.eq_zero, map_zero]
  refine ⟨⟨a, hqB, ?_⟩, ?_⟩
  · rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic]; exact ha.eq_zero
  · apply Subtype.ext
    change f a = f a0
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hfa hz' ?_ (derivUnit q (f a) hqC hfa)
    rw [← map_sub, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp ham

end LateralTheory.E.LeafClosedSH0PfPrim
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmbedNonDegOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf
  LateralTheory.E.GeometricData

namespace LateralTheory.E.EmbedNonDeg₂

theorem germ_res {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem rA_res {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {W X : Z.Opens}
    (h : W ≤ X) (a : A) : Z.presheaf.map (homOfLE h).op (rA p X a) = rA p W a := by
  have e := Scheme.Hom.appLE_map p (U := ⊤) (V := X) le_top (homOfLE h).op
  simp only [rA, RingHom.comp_apply]
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) e

theorem int_adjoin {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : Polynomial A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (t : K)
    (hc : ∀ a, φ (f (Polynomial.C a)) = algebraMap A K a) (hX : φ (f Polynomial.X) = t) (x : S) :
    IsIntegral (Algebra.adjoin A {t}) (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  let ψ : Polynomial A →+* Algebra.adjoin A {t} :=
    (Polynomial.aeval (⟨t, Algebra.self_mem_adjoin_singleton A t⟩ : Algebra.adjoin A {t})).toRingHom
  have key : (algebraMap (Algebra.adjoin A {t}) K).comp ψ = φ.comp f := by
    apply Polynomial.ringHom_ext
    · intro a; simp [ψ, hc]
    · simp [ψ, hX]
  refine ⟨P.map ψ, hm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, key, ← Polynomial.hom_eval₂, hP, map_zero]

theorem int_A {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (hc : ∀ a, φ (f a) = algebraMap A K a) (x : S) :
    IsIntegral A (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  refine ⟨P, hm, ?_⟩
  have : algebraMap A K = φ.comp f := RingHom.ext fun a => (hc a).symm
  rw [this, ← Polynomial.hom_eval₂, hP, map_zero]

theorem range_loc {A K : Type} [CommRing A] [Field K] [Algebra A K] {Z : Scheme.{0}} {U W : Z.Opens}
    (hU : IsAffineOpen U) (s : Γ(Z, U)) (hW : Z.basicOpen s = W) (hle : W ≤ U)
    (φU : Γ(Z, U) →+* K) (φW : Γ(Z, W) →+* K)
    (hres : ∀ x, φW (Z.presheaf.map (homOfLE hle).op x) = φU x) (B : Subalgebra A K)
    (hB : ∀ k, k ∈ B ↔ ∃ x, φU x = k) (hs : φU s ≠ 0) (hinv : (φU s)⁻¹ ∈ φW.range) :
    φW.range = (AdjoinInv B (φU s)).toSubring := by
  subst hW
  have := hU.isLocalization_basicOpen s
  ext k; constructor
  · intro hk0
    obtain ⟨z, rfl⟩ := hk0
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e1⟩ := IsLocalization.surj (Submonoid.powers s) z
    have e2 := congrArg φW e1
    rw [map_mul] at e2
    change φW z * φW (Z.presheaf.map (homOfLE hle).op (s ^ n)) = φW (Z.presheaf.map (homOfLE hle).op x) at e2
    rw [hres, hres, map_pow] at e2
    have e3 : φW z = φU x * ((φU s)⁻¹) ^ n := by
      rw [← e2, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs), mul_one]
    change φW z ∈ AdjoinInv B (φU s)
    rw [e3]
    refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ ?_ _)
    · exact Algebra.subset_adjoin (Or.inl ((hB _).mpr ⟨x, rfl⟩))
    · exact Algebra.subset_adjoin (Or.inr rfl)
  · intro hk
    have hBW : ∀ k ∈ B, k ∈ φW.rangeS := by
      intro k hk; obtain ⟨x, rfl⟩ := (hB k).mp hk
      exact ⟨_, hres x⟩
    let R : Subalgebra A K :=
      { toSubsemiring := φW.rangeS, algebraMap_mem' := fun a => hBW _ (B.algebraMap_mem a) }
    have hle' : AdjoinInv B (φU s) ≤ R := by
      rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro k (hk | hk)
      · exact hBW k hk
      · rw [Set.mem_singleton_iff.mp hk]; obtain ⟨y, hy⟩ := hinv; exact ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hle' hk
    exact ⟨y, hy⟩

theorem EmbedNonDeg_of : EmbedNonDeg := by
  intro A _ _ Z p hI hTop hN
  obtain ⟨U, V, s, s', hU, hV, hUV, hsU, hsV, ⟨z, hz⟩, hss, hiU, hiV⟩ := hN
  have hzU : z ∈ U := (inf_le_left : U ⊓ V ≤ U) hz
  have hzV : z ∈ V := (inf_le_right : U ⊓ V ≤ V) hz
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : Nonempty (U ⊓ V : Z.Opens) := ⟨⟨z, hz⟩⟩
  have : Nonempty (U ⊔ V : Z.Opens) := ⟨⟨z, (le_sup_left : U ≤ U ⊔ V) hzU⟩⟩
  let φU : Γ(Z, U) →+* Z.functionField := (Z.germToFunctionField U).hom
  let φV : Γ(Z, V) →+* Z.functionField := (Z.germToFunctionField V).hom
  let φW : Γ(Z, U ⊓ V) →+* Z.functionField := (Z.germToFunctionField (U ⊓ V)).hom
  let φT : Γ(Z, U ⊔ V) →+* Z.functionField := (Z.germToFunctionField (U ⊔ V)).hom
  let _ : Algebra A Z.functionField := (φU.comp (rA p U)).toAlgebra
  have hcU : ∀ a, φU (rA p U a) = algebraMap A Z.functionField a := fun a => rfl
  have rL : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x) = φU x :=
    fun x => germ_res U (U ⊓ V) inf_le_left x
  have rR : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x) = φV x :=
    fun x => germ_res V (U ⊓ V) inf_le_right x
  have hcV : ∀ a, φV (rA p V a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rL, ← rR, rA_res, rA_res]
  have hmul : φU s * φV s' = 1 := by
    have h := congrArg φW hss
    rw [map_mul, map_one, rL, rR] at h
    exact h
  have ht : φU s ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hs0' : φV s' ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hs'inv : φV s' = (φU s)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φU.rangeS, algebraMap_mem' := fun a => ⟨rA p U a, hcU a⟩ }
  let C : Subalgebra A Z.functionField :=
    { toSubsemiring := φV.rangeS, algebraMap_mem' := fun a => ⟨rA p V a, hcV a⟩ }
  have hWB : φW.range = (AdjoinInv B (φU s)).toSubring :=
    range_loc hU s hsU inf_le_left φU φW rL B (fun _ => Iff.rfl) ht ⟨_, (rR s').trans hs'inv⟩
  have hWC : φW.range = (AdjoinInv C (φV s')).toSubring :=
    range_loc hV s' hsV inf_le_right φV φW rR C (fun _ => Iff.rfl) hs0'
      ⟨_, (rL s).trans (by rw [hs'inv, inv_inv])⟩
  have hglue : AdjoinInv B (φU s) = Algebra.adjoin A ((C : Set Z.functionField) ∪ {φU s}) := by
    have h2 := Subalgebra.toSubring_injective (hWB.symm.trans hWC)
    rw [h2, AdjoinInv, hs'inv, inv_inv]
  have hTop' : (rA p (U ⊔ V)).IsIntegral := by rw [hUV]; exact hTop
  have hcT : ∀ a, φT (rA p (U ⊔ V) a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rA_res p (le_sup_left : U ≤ U ⊔ V) a]
    exact (germ_res (U ⊔ V) U le_sup_left _).symm
  have hBC : ∀ x ∈ B, x ∈ C → IsIntegral A x := by
    intro x hxB hxC
    obtain ⟨u, hu⟩ := hxB
    obtain ⟨v, hv⟩ := hxC
    have heq : Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op u =
        Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op v :=
      Z.germToFunctionField_injective (U ⊓ V) (((rL u).trans (hu.trans hv.symm)).trans (rR v).symm)
    let g := (Z.sheaf.objSupIsoProdEqLocus U V).inv ⟨(u, v), heq⟩
    have hg : Z.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op g = u :=
      Z.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have hx : x = φT g := by
      rw [← hu, ← hg]; exact germ_res (U ⊔ V) U le_sup_left g
    rw [hx]
    exact int_A (rA p (U ⊔ V)) hTop' φT hcT g
  have intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {φU s}) b := by
    intro b hb
    obtain ⟨x, rfl⟩ := hb
    exact int_adjoin (Polynomial.eval₂RingHom (rA p U) s) hiU φU (φU s)
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcU a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]) x
  have intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {(φU s)⁻¹}) c := by
    intro c hc
    obtain ⟨x, rfl⟩ := hc
    exact int_adjoin (Polynomial.eval₂RingHom (rA p V) s') hiV φV (φU s)⁻¹
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcV a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact hs'inv) x
  refine ⟨Z.functionField, inferInstance, inferInstance, B, C, φU s,
    ⟨ht, ⟨s, rfl⟩, ⟨s', hs'inv⟩, intB, intC, hglue⟩, hBC, ?_⟩
  exact ⟨U, V, φU, φV, φW, hU, hV, hsU ▸ hU.basicOpen s, hUV,
    Z.germToFunctionField_injective U, Z.germToFunctionField_injective V,
    Z.germToFunctionField_injective (U ⊓ V), SetLike.ext fun _ => Iff.rfl, SetLike.ext fun _ => Iff.rfl, hWB,
    rL, rR, fun a => rfl, hcV⟩

end LateralTheory.E.EmbedNonDeg₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmptySec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0PfEmpty
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem emptySec : LeafEmptySec := by
  intro R _ F X hX
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := by
    exact Scheme.bot_mem_grothendieckTopology X
  have hT := Sheaf.isTerminalOfBotCover F X hb
  have hZ : IsZero (F.obj.obj (op X)) := hT.isZero
  exact (ModuleCat.isZero_iff_subsingleton.mp hZ)

end LateralTheory.E.LeafClosedSH0PfEmpty
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GeometricDataOfLines
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

theorem rA_top {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    rA p ⊤ = p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  have h : p.appLE ⊤ ⊤ le_top = p.appTop := p.appLE_eq_app (U := ⊤)
  rw [rA, h]

theorem topInt : TopInt := by
  intro A _ _ Z p hIL
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have : UniversallyClosed u := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hu).1
  have : UniversallyClosed l := hl.1.toUniversallyClosed
  have h1 := isIntegral_appTop_of_universallyClosed (u ≫ l)
  rw [rA_top]
  refine RingHom.IsIntegral.trans _ _ ?_ h1
  exact RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective

theorem germ_res_eq {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem embedAffine : EmbedAffine := by
  intro A _ _ Z p hI hTop hAff
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨z, trivial⟩⟩
  have : Nonempty (⊤ ⊓ ⊤ : Z.Opens) := ⟨⟨z, trivial, trivial⟩⟩
  let φ : Γ(Z, ⊤) →+* Z.functionField := (Z.germToFunctionField ⊤).hom
  let _ : Algebra A Z.functionField := (φ.comp (rA p ⊤)).toAlgebra
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φ.rangeS, algebraMap_mem' := fun a => ⟨rA p ⊤ a, rfl⟩ }
  have hBint : ∀ x ∈ B, IsIntegral A x := by
    rintro x ⟨g, rfl⟩
    obtain ⟨P, hP, hP0⟩ := hTop g
    refine ⟨P, hP, ?_⟩
    have : Polynomial.eval₂ (algebraMap A Z.functionField) (φ g) P = φ (Polynomial.eval₂ (rA p ⊤) g P) := by
      rw [Polynomial.hom_eval₂]; rfl
    rw [this, hP0, map_zero]
  have hDov : AdjoinInv B 1 = B := by
    apply le_antisymm
    · rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro x (hx | hx)
      · exact hx
      · rw [Set.mem_singleton_iff.mp hx, inv_one]; exact B.one_mem
    · intro x hx
      exact Algebra.subset_adjoin (Or.inl hx)
  refine ⟨Z.functionField, inferInstance, inferInstance, B, B, 1, ?_, fun x hx _ => hBint x hx, ?_⟩
  · refine ⟨one_ne_zero, B.one_mem, by rw [inv_one]; exact B.one_mem, ?_, ?_, ?_⟩
    · intro b hb; exact (hBint b hb).tower_top
    · intro b hb; exact (hBint b hb).tower_top
    · rw [hDov]
      apply le_antisymm
      · intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
      · rw [Algebra.adjoin_le_iff]
        rintro x (hx | hx)
        · exact hx
        · rw [Set.mem_singleton_iff.mp hx]; exact B.one_mem
  · refine ⟨⊤, ⊤, φ, φ, (Z.germToFunctionField (⊤ ⊓ ⊤)).hom, hAff, hAff, by simpa using hAff, sup_idem _,
      Z.germToFunctionField_injective _, Z.germToFunctionField_injective _, Z.germToFunctionField_injective _,
      rfl, rfl, ?_, ?_, ?_, fun a => rfl, fun a => rfl⟩
    · rw [hDov]
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, germ_res_eq (⊤ ⊓ ⊤) ⊤ (le_inf le_rfl le_rfl) s⟩
      · rintro ⟨s, rfl⟩
        exact ⟨Z.presheaf.map (homOfLE inf_le_left).op s, germ_res_eq _ _ _ s⟩
    · intro s; exact germ_res_eq _ _ _ s
    · intro s; exact germ_res_eq _ _ _ s

end LateralTheory.E.GeometricData
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GluingExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluingExistence

theorem mul_pow_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (x : L) (hx : x ∈ Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    ∃ n : ℕ, x * v ^ n ∈ C := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hv0]; exact C.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using C.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * v ^ (n + m) = (x * v ^ n) * v ^ m + (y * v ^ m) * v ^ n := by ring
    rw [this]; exact C.add_mem (C.mul_mem hn (C.pow_mem hv _)) (C.mul_mem hm (C.pow_mem hv _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * v ^ (n + m) = (x * v ^ n) * (y * v ^ m) := by ring
    rw [this]; exact C.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C E : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (hCE : C ≤ E) (hE : E = Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
    IsLocalization.Away (⟨v, hv⟩ : C) E := by
  letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
  have hvi : v⁻¹ ∈ E := hE ▸ Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨v⁻¹, hvi⟩ ^ n, Subtype.ext ?_⟩
    show (v ^ n) * (v⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ hv0, one_pow]
  · rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := mul_pow_mem C v hv hv0 z (hE ▸ hz)
    exact ⟨(⟨z * v ^ n, hn⟩, ⟨⟨v, hv⟩ ^ n, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y h
    refine ⟨1, ?_⟩
    have : (x : L) = y := congrArg (fun w : E => (w : L)) h
    simp [Subtype.ext this]

theorem LeafGlueExists_of : LeafGlueExists := by
  intro Ω L _ _ _ A B u h
  obtain ⟨hu, huA, huB, -, -, -, -, -, -, -, -, hadj, -⟩ := h
  set D := Dr Ω A u
  have hAD : A ≤ D := le_Dr_A A u
  have hBD : B ≤ D := le_Dr_B A B u hadj
  letI iAD : Algebra A D := (Subalgebra.inclusion hAD).toRingHom.toAlgebra
  letI iBD : Algebra B D := (Subalgebra.inclusion hBD).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨u, huA⟩ : A) D := away A D u huA hu hAD rfl
  haveI : IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D :=
    away B D u⁻¹ huB (inv_ne_zero hu) hBD (by rw [inv_inv]; exact hadj)
  let fA : Sp D ⟶ Sp A := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom)
  let fB : Sp D ⟶ Sp B := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom)
  haveI hfA : IsOpenImmersion fA := IsOpenImmersion.of_isLocalization (S := D) (⟨u, huA⟩ : A)
  haveI hfB : IsOpenImmersion fB := IsOpenImmersion.of_isLocalization (S := D) (⟨u⁻¹, huB⟩ : B)
  haveI : ∀ {i j : WalkingSpan} (f : i ⟶ j), IsOpenImmersion ((span fA fB).map f) := by
    intro i j f
    rcases f with _ | j
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · rcases j with _ | _
      · exact hfA
      · exact hfB
  have hc : fA ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
      fB ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    simp only [fA, fB, ← Spec.map_comp]; rfl
  refine ⟨{
    C0 := pushout fA fB
    c0 := pushout.desc _ _ hc
    iA := pushout.inl fA fB
    iB := pushout.inr fA fB
    hiA := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hiB := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hcA := pushout.inl_desc _ _ _
    hcB := pushout.inr_desc _ _ _
    agree := pushout.condition
    cover := ?_
    inter := ?_ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span fA fB) x
    rcases i with _ | j
    · left; refine ⟨fA xi, ?_⟩
      rw [← colimit.w (span fA fB) (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
    · rcases j with _ | _
      · left; exact ⟨xi, rfl⟩
      · right; exact ⟨xi, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hab : colimit.ι (span fA fB) (some WalkingPair.left) a =
          colimit.ι (span fA fB) (some WalkingPair.right) b := hb.symm
      obtain ⟨k, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span fA fB)).mp hab
      rcases k with _ | k
      · refine ⟨y, ?_⟩
        rw [← hy1, Subsingleton.elim fi (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
      · rcases k with _ | _
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.left) (some WalkingPair.right) from fj)
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.right) (some WalkingPair.left) from fi)
    · rintro ⟨y, rfl⟩
      refine ⟨⟨fA y, rfl⟩, ⟨fB y, ?_⟩⟩
      show (fB ≫ pushout.inr fA fB).base y = (fA ≫ pushout.inl fA fB).base y
      rw [pushout.condition]

end LateralTheory.E.GluingExistence
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafObjFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafObjFPPf

def Desc (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
    FP q ∧ IsPullback v f q (toR R)

def LeafObjAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), IsAffine X → FP f → Desc k f

def LeafObjGlue : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
    Desc k (U.ι ≫ f) → Desc k (V.ι ≫ f) → Desc k ((U ⊓ V).ι ≫ f) → Desc k f

def LeafQCQSInduct : Prop := ∀ (S : Scheme.{0}) [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop),
    (∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f) →
    (∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f) →
    ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → P f

theorem objectDescent_of_affineDescent (hA : LeafObjAff) (hG : LeafObjGlue) (hI : LeafQCQSInduct) : LeafObjFP := by
  intro k _ Ω _ _ X f hf
  exact hI (Sp Ω) (fun g => Desc k g) (fun g hX hg => hA k Ω g hX hg)
    (fun g hg U V hUV h1 h2 h3 => hG k Ω g hg U V hUV h1 h2 h3) f hf

end LateralTheory.E.LeafObjFPPf

end
end

