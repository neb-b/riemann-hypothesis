module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem eq_refl_of_isometry_congMod : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) →
    ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  intro X _ _ _ β hpos e he N hN hc
  choose u hu using hc
  have hQ0 : ∀ x, 0 ≤ β x x := fun x => by
    by_cases h : x = 0
    · simp [h]
    · exact (hpos x h).le
  have hdec : ∀ x, x ≠ 0 → β (u x) (u x) < β x x := by
    intro x hx
    have h1 : 0 ≤ β (e x + x) (e x + x) := hQ0 _
    have h2 : β (e x - x) (e x - x) = (N : ℤ) * ((N : ℤ) * β (u x) (u x)) := by
      rw [show e x - x = N • u x by rw [hu x]; abel]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, he x x] at h1 h2
    have hc := hpos x hx
    have hd := hQ0 (u x)
    have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul hN' hN' (by norm_num) (by omega)) hd]
  have hnil : ∀ n : ℕ, ∀ x, (β x x).toNat = n → ∃ k, u^[k] x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn
      by_cases hx : x = 0
      · exact ⟨0, by simpa using hx⟩
      · have hlt := hdec x hx
        have hd := hQ0 (u x)
        obtain ⟨k, hk⟩ := ih (β (u x) (u x)).toNat (by omega) (u x) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
  ext y
  by_contra hne
  have huy : u y ≠ 0 := fun h => hne (by rw [hu y, h]; simp)
  classical
  have hex : ∃ k, u^[k] y = 0 := hnil _ y rfl
  have hk : u^[Nat.find hex] y = 0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, u^[j] y ≠ 0 := fun j hj => Nat.find_min hex hj
  have hy0 : y ≠ 0 := fun h => hne (by simp [h])
  have hk2 : 2 ≤ Nat.find hex := by
    by_contra h
    interval_cases h' : Nat.find hex
    · exact hy0 (by simpa using hk)
    · exact huy (by simpa using hk)
  have hux : u (u^[Nat.find hex - 2] y) ≠ 0 := by
    rw [← Function.iterate_succ_apply' u]
    exact hmin _ (by omega)
  have huux : u (u (u^[Nat.find hex - 2] y)) = 0 := by
    rw [← Function.iterate_succ_apply' u, ← Function.iterate_succ_apply' u]
    rw [show (Nat.find hex - 2).succ.succ = Nat.find hex by omega]
    exact hk
  set x := u^[Nat.find hex - 2] y
  have key := he x (u x)
  rw [hu x, hu (u x), huux] at key
  simp only [smul_zero, add_zero, map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at key
  have hp := hpos (u x) hux
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hN0 hp]

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFiltrationSectionCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.Orders

section Alg
open MvPolynomial

variable {R : Type} [CommRing R]

end Alg

section Val

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def vh (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR x U f = vh x U h f := by
  rw [valR, dite_eq_left h]; rfl

theorem vh_congr {x y : Sp A ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) :
    vh x U h = vh y U h' := by subst e; rfl

theorem vh_spMap {B : Type} [CommRing B] (ψ : A →+* B) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) : vh (spMap ψ ≫ x) U h' f = ψ (vh x U h f) := by
  have h1 : (spMap ψ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have h3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f)) h2
  simp only [vh, h1, RingHom.comp_apply, CommRingCat.hom_comp]
  exact h3

theorem vh_res (x : Sp A ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    vh x V h' (resG X hVU f) = vh x U h f := by
  have h1 : X.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h' = x.appLE U ⊤ h := Scheme.Hom.map_appLE _ _ _
  simp only [vh, ← h1, RingHom.comp_apply, CommRingCat.hom_comp]

theorem vh_const {R : Type} [CommRing R] (ψ : R →+* A) (p : X ⟶ Sp R) (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) : vh x U h (Geo.Tor.constFn p U a) = ψ a := by
  have h1 : p.appLE ⊤ U le_top ≫ x.appLE U ⊤ h = (spMap ψ).appTop := by
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
    rw [← hx, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have h3 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h2
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  simp only [vh, Geo.Tor.constFn, RingHom.comp_apply]
  erw [h4, h3]
  simp

theorem eq_of_vh {x y : Sp A ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : vh x U h = vh y U h') : x = y := by
  have e' : x.appLE U ⊤ h = y.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A)).hom]
    exact CommRingCat.hom_ext e
  have hT : IsAffineOpen (⊤ : (Sp A).Opens) := isAffineOpen_top _
  have a1 := IsAffineOpen.SpecMap_appLE_fromSpec x hU hT h
  have a2 := IsAffineOpen.SpecMap_appLE_fromSpec y hU hT h'
  rw [e', a2] at a1
  haveI : IsIso hT.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  exact ((cancel_epi _).1 a1).symm

theorem vh_ne_zero [Nontrivial A] (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U))
    (hf : ⊤ ≤ x ⁻¹ᵁ X.basicOpen f) : vh x U h f ≠ 0 := by
  intro h0
  have h1 : (x.appLE U ⊤ h).hom f = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]; exact h0
  have h2 := Scheme.basicOpen_appLE x ⊤ U h f
  erw [h1] at h2
  rw [Scheme.basicOpen_zero, top_inf_eq] at h2
  obtain ⟨p⟩ : Nonempty (Sp A) := inferInstanceAs (Nonempty (PrimeSpectrum A))
  have := hf (show p ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← h2] at this
  exact this

theorem top_le_of_nil {B : Type} [CommRing B] (ψ : A →+* B) (hs : Function.Surjective ψ)
    (hn : ∀ z, ψ z = 0 → IsNilpotent z) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) :
    ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have : p ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [range_comap_of_surjective _ ψ hs]
    refine (PrimeSpectrum.mem_zeroLocus _ _).2 ?_
    intro z hz
    obtain ⟨n, hn⟩ := hn z hz
    exact (show PrimeSpectrum A from p).isPrime.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
  obtain ⟨q, rfl⟩ := this
  exact h (show (show Sp B from q) ∈ (⊤ : (Sp B).Opens) from trivial)

end Val

section Grp

variable {R : Type} [CommRing R]

theorem epsScale_zero : epsScale R 0 = toUnit _ ≫ TanComb.zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (epsScaleR (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

variable {G : Over (Sp R)} [GrpObj G]

theorem epsScale_zero_comp {y : epsR R ⟶ G} (hy : IsTangent y) : epsScale R 0 ≫ y = 1 := by
  rw [epsScale_zero, Category.assoc, (TanComb.isTangent_iff y).1 hy, MonObj.comp_one]

def orig (G : Over (Sp R)) [GrpObj G] : Sp R ⟶ G.left := eSec G

theorem top_le_tangent {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) :
    ⊤ ≤ (show Sp (DualNumber R) ⟶ G.left from y.left) ⁻¹ᵁ U := by
  refine top_le_of_nil (TrivSqZeroExt.fstHom R R R).toRingHom (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) ?_ _ U ?_
  · intro z hz
    have hz' : z.fst = 0 := hz
    refine ⟨2, ?_⟩
    ext <;> simp [sq, hz']
  · have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (show Sp (DualNumber R) ⟶ G.left from y.left) = orig G := hy
    rw [this]; exact he

theorem fst_vh_tangent {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : (vh (A := DualNumber R) y.left U (top_le_tangent hy he) f).fst = vh (orig G) U he f := by
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (show Sp (DualNumber R) ⟶ G.left from y.left) = orig G := hy
  rw [← vh_congr this U (by rw [this]; exact he) he, vh_spMap _ _ _ (top_le_tangent hy he)]
  rfl

theorem isTangent_one : IsTangent (1 : epsR R ⟶ G) := by
  rw [TanComb.isTangent_iff, MonObj.comp_one]

end Grp

section Sec

theorem vh_sec_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {H : LB X} (s : H.Sec) (x : Sp K ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ x ⁻¹ᵁ H.U l) (hs : ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s) : vh x (H.U l) hl (s.f l) ≠ 0 := by
  haveI : Unique (Sp K) := inferInstanceAs (Unique (PrimeSpectrum K))
  have h1 : x default ∈ Out.nonzeroLocus s := hs (show (default : Sp K) ∈ (⊤ : (Sp K).Opens) from trivial)
  rw [Out.nonzeroLocus, TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨k, hk⟩ := h1
  have hk' : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f k) := by
    intro p _
    rw [Subsingleton.elim p default]; exact hk
  have hkU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
  have hkl : ⊤ ≤ x ⁻¹ᵁ (H.U k ⊓ H.U l) := fun p hp => ⟨hkU hp, hl hp⟩
  have h2 := vh_ne_zero x _ hkU _ hk'
  have h3 := congrArg (vh x _ hkl) (s.compat k l)
  rw [map_mul] at h3
  erw [vh_res x _ hkU hkl, vh_res x _ hl hkl] at h3
  intro h0
  rw [h0, mul_zero] at h3
  exact h2 h3

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]

theorem exists_sep {H : LB G.left} {J : Type} (s : J → H.Sec) (hs : GlobalTheory.ZH.ImmBy G.hom H s Set.univ)
    {y : epsR K ⟶ G} (hy : IsTangent y) (hy1 : y ≠ 1) (l : H.ι) (hl : ⊤ ≤ orig G ⁻¹ᵁ H.U l) :
    ∃ s₀ s₁ : H.Sec, vh (orig G) _ hl (s₀.f l) ≠ 0 ∧ vh (orig G) _ hl (s₁.f l) = 0 ∧
      (vh (A := DualNumber K) y.left _ (top_le_tangent hy hl) (s₁.f l)).snd ≠ 0 := by
  haveI : Unique (Sp K) := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨hc, hs⟩ := hs
  have h1 : orig G default ∈ ⨆ i ∈ (Set.univ : Set J), Out.nonzeroLocus (s i) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨i, -, hi⟩ := h1
  obtain ⟨haff, r, hr, hgen⟩ := hs i trivial
  have hV : ⊤ ≤ orig G ⁻¹ᵁ Out.nonzeroLocus (s i) := by
    intro p _
    rw [Subsingleton.elim p default]; exact hi
  have h0 := vh_sec_ne_zero (s i) (orig G) l hl hV
  have hj : ∃ j, (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j)).snd ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hy1
    apply Over.OverMorphism.ext
    refine eq_of_vh (A := DualNumber K) haff (top_le_tangent hy hV) (top_le_tangent isTangent_one hV) ?_
    refine RingHom.eq_of_eqOn_set_dense hgen ?_
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact (vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y) _ _ a).trans
        (vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w (1 : epsR K ⟶ G)) _ _ a).symm
    · apply TrivSqZeroExt.ext
      · exact (fst_vh_tangent hy hV _).trans (fst_vh_tangent isTangent_one hV _).symm
      · refine (hn j).trans ?_
        have := vh_spMap (algebraMap K (DualNumber K)) (orig G) _ hV (top_le_tangent isTangent_one hV) (r j)
        erw [this]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨j, hj⟩ := hj
  have key : vh (A := DualNumber K) y.left _ (top_le_tangent hy hl)
      ((secComb G.hom ![1, -vh (orig G) _ hV (r j)] ![s j, s i]).f l) =
      (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j) - algebraMap K _ (vh (orig G) _ hV (r j))) *
        vh (A := DualNumber K) y.left _ (top_le_tangent hy hl) ((s i).f l) := by
    have hW : ⊤ ≤ (show Sp (DualNumber K) ⟶ G.left from y.left) ⁻¹ᵁ (Out.nonzeroLocus (s i) ⊓ H.U l) :=
      fun p hp => ⟨top_le_tangent hy hV hp, top_le_tangent hy hl hp⟩
    have h3 := congrArg (vh _ _ hW) (hr j l)
    rw [map_mul, vh_res _ _ (top_le_tangent hy hl) hW, vh_res _ _ (top_le_tangent hy hl) hW,
      vh_res _ _ (top_le_tangent hy hV) hW] at h3
    simp only [secComb, Fin.sum_univ_two, map_add (f := _), map_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y),
      vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y)]
    erw [h3]
    simp only [map_one, map_neg]
    ring
  have hf : (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j) -
      algebraMap K _ (vh (orig G) _ hV (r j))).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, fst_vh_tangent hy hV]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨s i, secComb G.hom ![1, -vh (orig G) _ hV (r j)] ![s j, s i], h0, ?_, ?_⟩
  · rw [← fst_vh_tangent hy hl, key, TrivSqZeroExt.fst_mul, hf, zero_mul]
  · rw [key, TrivSqZeroExt.snd_mul, hf, fst_vh_tangent hy hl, zero_smul, zero_add, TrivSqZeroExt.snd_sub]
    simpa [TrivSqZeroExt.algebraMap_eq_inl, h0] using hj

theorem tanComb_ne_one {m : ℕ} {v : Fin m → (epsR K ⟶ G)} (hv : IsLieBasis v) {x : Fin m → K} (hx : x ≠ 0) :
    tanComb x v ≠ 1 := by
  intro h
  have h0 : tanComb 0 v = 1 := by
    apply List.prod_eq_one
    intro w hw
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hw
    exact epsScale_zero_comp (hv.1 a)
  obtain ⟨c, -, hc⟩ := hv.2 1 isTangent_one
  exact hx ((hc x (h ▸ isLieComb_tanComb x v)).trans (hc 0 (h0 ▸ isLieComb_tanComb 0 v)).symm)

end Sec

end GlobalTheory.SecJet.Orders

namespace GlobalTheory.SecJet


end GlobalTheory.SecJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VanishEmbedded

open GlobalTheory.HSCore.VanishNumberField

theorem subsingleton_coh_canon_tens : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hNum hNad F _ ⟨σ⟩ X p D hsm hp hgc K N hnef hbig q hq
  letI := σ.toAlgebra
  let X' := pullback p (spMap (algebraMap F ℂ))
  let π : X' ⟶ X := pullback.fst _ _
  let p' : X' ⟶ Sp ℂ := pullback.snd _ _
  have H : IsPullback π p' p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hI, -, hsm', hp', -⟩ := GlobalTheory.BaseChangeVariety.baseChange_props F ℂ X X' p p' π D H hp hgc
  haveI : Nonempty X := ⟨π (Classical.arbitrary X')⟩
  letI := algebraΓOfHom p
  letI := algebraΓOfHom p'
  obtain ⟨hprop, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hL := LB.isLB_pull hnef.isLB π
  have hnef' : IsNef ℂ (N.pull π) := GlobalTheory.NefFieldExt.isNef_baseChange hNum F ℂ X X' p p' π H hp N hnef
  have hbig' : IsBig ℂ (N.pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hbig.3
    have hD : topologicalKrullDim X = D := topologicalKrullDim_eq_of_smooth p D hsm
    obtain rfl : D₀ = D := by exact_mod_cast hD₀.symm.trans hD
    refine (isBig_iff (f := p') (fun _ => rfl) hp'
      (topologicalKrullDim_eq_of_smooth _ D₀ hsm')).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hbig.1, cls_pull (isLB_lbPow hbig.1 m), cls_lbPow hbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull H (isLB_lbPow hbig.1 m) 0).symm
  have hKV := GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs hNad X' p' D hp' hI (K.baseChange H) (N.pull π) hnef' hbig' q hq
  have hM : (tens K.bundle N).IsLB := isLB_tens K.isLB hnef.isLB
  have hK' := LB.isLB_pull K.isLB π
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X') (LB.isLB_pull hM π) (isLB_tens hK' hL)
    (by rw [cls_pull hM π, cls_tens K.isLB hnef.isLB, cls_tens hK' hL, cls_pull K.isLB π, cls_pull hnef.isLB π, map_add (f := _)])
  exact subsingleton_coh_of_pull (f := p) (f' := p') H hM q
    ((cohOn.mapIso Γ(X', ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 hKV)

end GlobalTheory.VanishEmbedded
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExists
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem conj_embK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

theorem ksExist : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type)
    [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q →
    GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ hx
  have P := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G x'
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G y.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := _root_.GlobalTheory.PolExists.polForm_exists P Xo hπ
  have hadj := _root_.GlobalTheory.PolAdjoint.polForm_adjoint P Xo hπ a ha hpol
  have hK := _root_.GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have hL := (P.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := _root_.GlobalTheory.LieBasis.lifts_basis_mod_fil P y hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → K,
      ∃ w, IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ =>
    _root_.GlobalTheory.KSExist.ksRow_exists_lieComb hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => _root_.GlobalTheory.KSExist.isKSValue_act hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, conj_embK]) a₀
  choose cf w hw using hrow
  refine ⟨fun k => cf k.1 k.2.1 k.2.2, A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub,
    hb, hπ, hπ', rfl, hpol, hu, fun σ k => hbl ⟨σ, k⟩, fun τ a₀ => ⟨w τ a₀, (hw τ a₀).1, (hw τ a₀).2⟩⟩

end GlobalTheory.KSExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegre
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem levCover_model : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  have h1 := _root_.GlobalTheory.LevModel.over_comp D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  choose π δ hGm hIso hOv using h1
  have h2 := fun k₂ => _root_.GlobalTheory.LevModel.conj_arithGroup_le D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  obtain ⟨N, hN, hsum⟩ := _root_.GlobalTheory.LevModel.cover_degree_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ π δ
    (fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2, hOv k₂⟩)
  have h4 := fun k₂ => _root_.GlobalTheory.LevRead.reading_pull D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  choose t ht hread using h4
  refine ⟨π, δ, N, hN, fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2⟩, hsum, t, ht, ?_⟩
  intro a n hD f hf g hg hP k₂ x x' hx hm hn
  exact hread k₂ a n hD f hf g hg hP x x' hx hm hn

end GlobalTheory.LevModel
end

