module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem exists_chart_lbPow (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (z : Fin g → ℂ) :
    ∃ k : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := by
  obtain ⟨i, hi⟩ := SymmetricSemicharacter.exists_chart u SymmetricSemicharacter.valueRules hL z
  refine ⟨fun _ => i, ?_⟩
  rwa [Cartier.lbPow_U]

theorem fr_pow_ne_zero (u : HolUnif A L g) (n : ℕ) {z : Fin g → ℂ} {k : (lbPow L n).ι}
    (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k) : u.fr (k PUnit.unit) z ^ n ≠ 0 :=
  pow_ne_zero n (u.fr_ne _ z (Cartier.lbPow_U L n k ▸ hk))

theorem le_preimage_nonzeroLocus_iff (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s : (lbPow L n).Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (z : Fin g → ℂ) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus s ↔ θ z ≠ 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem _ _).1 h)
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hs k z (top_le_preimage_of_valAt'_ne_zero _ h1)] at h1
    exact left_ne_zero_of_mul h1
  · intro h
    obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
    refine top_le_preimage_mono _ (le_iSup (fun k => A.left.basicOpen (s.f k)) k) ?_
    rw [top_le_preimage_basicOpen_iff, hs k z hk]
    exact mul_ne_zero h (fr_pow_ne_zero u n hk)

theorem valAt'_eq_div_of_mul (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s s' : (lbPow L n).Sec}
    {θ θ' : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ') (r : Γ(A.left, Out.nonzeroLocus s))
    (hr : ∀ k, resG _ (inf_le_right : Out.nonzeroLocus s ⊓ (lbPow L n).U k ≤ _) (s'.f k) =
      resG _ inf_le_left r * resG _ inf_le_right (s.f k)) {z : Fin g → ℂ} (hz : θ z ≠ 0) :
    valAt' (u.ex z).left _ r = θ' z / θ z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
  have hW := (top_le_preimage_inf _ _ _).2 ⟨(le_preimage_nonzeroLocus_iff u hL hs z).2 hz, hk⟩
  have h := congrArg (valAt' (u.ex z).left _) (hr k)
  rw [valAt'_mul, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, hs k z hk, hs' k z hk,
    ← _root_.mul_assoc] at h
  rw [mul_right_cancel₀ (fr_pow_ne_zero u n hk) h, mul_div_cancel_right₀ _ hz]

theorem exists_regular_quotients (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {κ : Type*} {s : κ → (lbPow L n).Sec}
    {θ : κ → (Fin g → ℂ) → ℂ} (hs : ∀ j, u.IsFnPow n (s j) (θ j)) (i : κ) {z₀ : Fin g → ℂ} (h0 : θ i z₀ ≠ 0) :
    ∃ (U : A.left.Opens) (ρ : κ → Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → θ i z ≠ 0 ∧ ∀ j, valAt' (u.ex z).left U (ρ j) = θ j z / θ i z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z₀
  have hle := A.left.basicOpen_le ((s i).f k)
  obtain ⟨v, hv⟩ : IsUnit (resG A.left hle ((s i).f k)) := RingedSpace.isUnit_res_basicOpen _ _
  refine ⟨A.left.basicOpen ((s i).f k), fun j => resG A.left hle ((s j).f k) * (v⁻¹).val, ?_, fun z hz => ?_⟩
  · rw [top_le_preimage_basicOpen_iff, hs i k z₀ hk]
    exact mul_ne_zero h0 (fr_pow_ne_zero u n hk)
  · have hk' := top_le_preimage_mono _ hle hz
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hz
    rw [hs i k z hk'] at h1
    refine ⟨left_ne_zero_of_mul h1, fun j => ?_⟩
    rw [valAt'_mul, valAt'_units_inv _ hz, hv, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, hs i k z hk', hs j k z hk',
      ← div_eq_mul_inv, mul_div_mul_right _ _ (right_ne_zero_of_mul h1)]

theorem isMonHom_of_lift {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') [Smooth A.hom] (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A')
    (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) : IsMonHom f := by
  have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom inferInstance
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  have h0' : u'.ex 0 = η[A'] := by
    rw [(u'.ker 0).2 u'.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [← h0, ← hf, map_zero, h0']
  · have hft : LocallyOfFiniteType (A ⊗ A).hom := by
      change LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    refine TorusEnd.hom_ext_of_points (existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) A' (A ⊗ A)
      (isReduced_tensorObj_complex A A hr hr inferInstance inferInstance) hft) fun y => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (y ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (y ≫ snd A A)
    have hy : y = lift (u.ex z) (u.ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← u.ex_add, ← hf, map_add (f := _), u'.ex_add, Hom.mul_def, ← Category.assoc,
      lift_map, ← hf, ← hf]

theorem exists_isMonHom_of_complementary (hamp : Out.AmpleSt) (P P' : Out.PolAV (Sp ℂ)) {g g' : ℕ}
    (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g') {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (hsec : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ)
    (hfn : ∀ (k : ℕ) s, ∃ θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (d : ℕ)
    (hd : ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' 4 θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  have hsm := P.isAb.smooth
  have hr : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ P.A) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A) := fun y => u'.ex (F (Function.surjInv u.ex_onto y))
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (F z) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (F z) ⟨_, hF _ h1⟩
    rwa [← map_add, add_sub_cancel] at this
  obtain ⟨m, s, hcov, hD⟩ := veryAmple_lbPow hamp ℂ P' 4 le_rfl
  choose θ hθ hθs using fun j => hfn 4 (s j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P'.A P.A hr inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (F z₀)).left _ hcov
    obtain ⟨haff, r, hr, hgen⟩ := hD i
    have hmem := le_preimage_nonzeroLocus_iff u' P'.isLB (hθs i)
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose t ht using fun j => hsec d _ (hG _ (hθ j))
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u P.isLB ht i (mul_ne_zero ((hmem _).1 hi) hG0)
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P'.isLB (hθs i) (hθs j) (r j) (hr j) h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, u'.ex (F z) = u.ex z ≫ f := fun z => by rw [hf, hΦ]
  exact ⟨f, isMonHom_of_lift u u' F f hfe, hfe⟩

end GlobalTheory.LatticeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.CoordChart

private theorem isIso_restrict_lemma {X Z Y : Scheme.{0}} (x : X ⟶ Z) [Mono x] (j : Y ⟶ X)
    [IsOpenImmersion (j ≫ x)] : IsIso (x ∣_ (j ≫ x).opensRange) := by
  set V := (j ≫ x).opensRange with hV
  let s : V.toScheme ⟶ X := (j ≫ x).isoOpensRange.inv ≫ j
  have hs : s ≫ x = V.ι := by
    rw [← cancel_epi (j ≫ x).isoOpensRange.hom]
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.Hom.isoOpensRange_hom_ι (j ≫ x)).symm
  have hr : Set.range s ⊆ Set.range (x ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show x (s y) ∈ V
    have e : x (s y) = V.ι y := by rw [← Scheme.Hom.comp_apply, hs]
    rw [e]
    have hm : V.ι y ∈ Set.range V.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hm
  let s' := IsOpenImmersion.lift (x ⁻¹ᵁ V).ι s hr
  have h1 : s' ≫ (x ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono ((x ⁻¹ᵁ V).ι ≫ x), Category.assoc, reassoc_of% h1, hs, morphismRestrict_ι,
      Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% h1, hs, Category.id_comp]

theorem isOpenImmersion_of_mono_of_local {X Z : Scheme.{0}} (x : X ⟶ Z) [Mono x]
    (h : ∀ p : X, ∃ (Y : Scheme.{0}) (j : Y ⟶ X), IsOpenImmersion (j ≫ x) ∧
      x p ∈ Set.range (j ≫ x)) : IsOpenImmersion x := by
  choose Y j hj hp using h
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion)
    (fun p => (j p ≫ x).opensRange) ?_ (fun p => ?_)
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨p, by rw [Scheme.Hom.mem_opensRange]; exact hp p⟩
  · have := isIso_restrict_lemma x (j p)
    infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using e

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, y = spMap f := by
  refine ⟨(Spec.preimage y).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mono_of_ring_points {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z)
    (h : ∀ (B : Type) [CommRing B] (f g : A →+* B), spMap f ≫ x = spMap g ≫ x → f = g) : Mono x := by
  refine ⟨fun {W} a b hab => ?_⟩
  have key : ∀ (B : Type) [CommRing B] (t : Sp B ⟶ W), t ≫ a = t ≫ b := by
    intro B _ t
    obtain ⟨f, hf⟩ := exists_spMap (t ≫ a)
    obtain ⟨g, hg⟩ := exists_spMap (t ≫ b)
    have hfg : f = g := h _ f g (by rw [← hf, ← hg, Category.assoc, Category.assoc, hab])
    rw [hf, hg, hfg]
  exact W.affineOpenCover.openCover.hom_ext a b
    (fun k => key (W.affineOpenCover.X k) (W.affineOpenCover.openCover.f k))

theorem exists_chart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  intro R σ _ I Z s M th i hP
  obtain ⟨hM, hpts, hrep⟩ := hP
  set J := I ⊔ Ideal.span {MvPolynomial.X i - 1} with hJ
  set q := Ideal.Quotient.mk J with hq

  have hq1 : q (MvPolynomial.X i) = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

  have hev : ∀ F, MvPolynomial.eval₂ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) F = q F := by
    intro F
    have e : MvPolynomial.eval₂Hom (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) = q :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun a => by simp)
    exact RingHom.congr_fun e F
  obtain ⟨x, ⟨hxs, hxc⟩, -⟩ := hrep _ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a))
    (by rw [Ideal.eq_top_iff_one, ← hq1]; exact Ideal.subset_span ⟨i, rfl⟩)
    (fun F hF => by rw [hev, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_sup_left hF)

  have hmono : Mono x := by
    apply mono_of_ring_points
    intro B _ f g hfg
    have hcf := GlobalTheory.ZM.Coord.baseChange hxc f
    have hcg := GlobalTheory.ZM.Coord.baseChange hxc g
    rw [hfg] at hcf
    obtain ⟨u, hu⟩ := GlobalTheory.ZM.Coord.unique hM hcg hcf
    have hu1 : (u : B) = 1 := by
      have e := hu i
      simp only [hq1, map_one] at e
      simpa using e.symm
    have hv : ∀ a, f (q (MvPolynomial.X a)) = g (q (MvPolynomial.X a)) := fun a => by
      rw [hu a, hu1, _root_.one_mul]
    have hb : f.comp (q.comp MvPolynomial.C) = g.comp (q.comp MvPolynomial.C) := by
      apply spMap_inj
      rw [← spMap_comp (q.comp MvPolynomial.C) f, ← spMap_comp (q.comp MvPolynomial.C) g, ← hxs,
        reassoc_of% hfg]
    have hc : f.comp q = g.comp q :=
      MvPolynomial.ringHom_ext (fun r => by simpa using RingHom.congr_fun hb r) (fun a => by simpa using hv a)
    exact Ideal.Quotient.ringHom_ext hc

  have hsub : Set.range x ⊆ (Out.nonzeroLocus (th i) : Set Z) := by
    rintro _ ⟨p, rfl⟩
    refine (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hxc).2 ?_
    show q (MvPolynomial.X i) ∉ p.asIdeal
    rw [hq1]
    exact fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

  have hloc : ∀ z ∈ (Out.nonzeroLocus (th i) : Set Z), ∃ (B : Type) (_ : CommRing B)
      (ψ : (MvPolynomial σ R ⧸ J) →+* B), IsOpenImmersion (spMap ψ ≫ x) ∧ z ∈ Set.range (spMap ψ ≫ x) := by
    intro z hz
    obtain ⟨R', _, x', v', hx'o, ⟨p, rfl⟩, hx'c⟩ := (_root_.GlobalTheory.ZM.LocalCoord.secCoord_local Z M σ th hM).2.2 z
    have hp : v' i ∉ p.asIdeal := (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hx'c).1 hz
    have hunit : IsUnit (algebraMap R' (Localization.Away (v' i)) (v' i)) :=
      IsLocalization.Away.algebraMap_isUnit (v' i)
    have hc1 := GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange hx'c (algebraMap R' (Localization.Away (v' i))))
      hunit.unit⁻¹
    set w : σ → Localization.Away (v' i) :=
      fun a => ((hunit.unit⁻¹ : (Localization.Away (v' i))ˣ) : Localization.Away (v' i)) *
        algebraMap R' (Localization.Away (v' i)) (v' a) with hw
    have hwi : w i = 1 := by simp [w]
    obtain ⟨β', hβ'⟩ := exists_spMap ((spMap (algebraMap R' (Localization.Away (v' i))) ≫ x') ≫ s)
    obtain ⟨hspan, hI⟩ := hpts _ β' _ w hβ' hc1
    have hker : J ≤ RingHom.ker (MvPolynomial.eval₂Hom β' w) := by
      refine sup_le (fun F hF => hI F hF) (Ideal.span_le.2 ?_)
      rintro _ rfl
      simp [hwi]
    let ψ : (MvPolynomial σ R ⧸ J) →+* Localization.Away (v' i) :=
      Ideal.Quotient.lift J (MvPolynomial.eval₂Hom β' w) (fun F hF => hker hF)
    have hψC : ∀ r, ψ (q (MvPolynomial.C r)) = β' r := fun r =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    have hψX : ∀ a, ψ (q (MvPolynomial.X a)) = w a := fun a =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    obtain ⟨y, -, hyu⟩ := hrep _ β' w hspan hI
    have e2 : spMap (algebraMap R' (Localization.Away (v' i))) ≫ x' = y := hyu _ ⟨hβ', hc1⟩
    have e1 : spMap ψ ≫ x = y := by
      refine hyu _ ⟨?_, ?_⟩
      · rw [Category.assoc, hxs, spMap_comp]
        congr 1
        exact RingHom.ext hψC
      · have e := GlobalTheory.ZM.Coord.baseChange hxc ψ
        convert e using 2 with a
        exact (hψX a).symm
    have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (v' i)) (v' i)
    have hpm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i)))) := by
      rw [hrange]
      exact hp
    obtain ⟨p', hp'⟩ := hpm
    refine ⟨Localization.Away (v' i), inferInstance, ψ, ?_, p', ?_⟩
    · rw [e1, ← e2]
      infer_instance
    · rw [e1, ← e2]
      show x' (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i))) p') = x' p
      rw [hp']
  have := hmono
  refine ⟨x, ?_, ?_, hxs, hxc⟩
  · apply isOpenImmersion_of_mono_of_local x
    intro p
    obtain ⟨B, _, ψ, h1, h2⟩ := hloc (x p) (hsub ⟨p, rfl⟩)
    exact ⟨Sp B, spMap ψ, h1, h2⟩
  · refine Set.Subset.antisymm hsub (fun z hz => ?_)
    obtain ⟨B, _, ψ, -, ⟨b, hb⟩⟩ := hloc z hz
    exact ⟨(spMap ψ) b, hb⟩

end GlobalTheory.ZM.CoordChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateIsoFieldExt

theorem exists_unit_of_pow_eq_one {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [CharZero K]
    (i : K →+* Ω) (n : ℕ) (hn : 0 < n) (z : Ωˣ) (hz : z ^ n = 1) :
    ∃ u : Kˣ, Units.map i.toMonoidHom u = z := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h2 : IsPrimitiveRoot (i ξ) n := hξ.map_of_injective i.injective
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one hz'
  refine ⟨(hξ.isUnit hn.ne').unit ^ j, Units.ext ?_⟩
  simpa using hj

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
  {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) {Q Q' : Type} [Group Q] [Group Q'] (f : Q →* Q')
  {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
  {e : ℕ → Q → Q → Kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}

theorem units_map_injective : Function.Injective (Units.map i.toMonoidHom) :=
  Units.map_injective i.injective

theorem up (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y))
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I : TateIso D K Q act e) :
    ∃ I' : TateIso D Ω Q' act' e', ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (units_map_injective i)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin, hact]
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by rw [← map_zpow, he]; exact I.isom n hn a b },
    fun n _ => ⟨rfl, fun _ => rfl⟩⟩
  · obtain ⟨y, hy, rfl⟩ := honto n hn z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

theorem down [IsAlgClosed K] [CharZero K] (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y)) (hone : ∀ c, act c 1 = 1)
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I' : TateIso D Ω Q' act' e') :
    ∃ I : TateIso D K Q act e, ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  have h1 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map i.toMonoidHom u = I'.ζ n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one i n hn _ (I'.ζ_prim n hn).pow_eq_one
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hn⟩
  have h2 : ∀ n v, ∃ y : Q, (0 < n → f y = I'.ev n v) ∧ (¬ 0 < n → y = 1) := fun n v => by
    by_cases hn : 0 < n
    · obtain ⟨y, -, hy⟩ := honto n hn _ ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun _ => hy, fun h => absurd hn h⟩
    · exact ⟨1, fun h => absurd h hn, fun _ => rfl⟩
  choose ζ hζ using h1
  choose ev hev hev0 using h2
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => units_map_injective i ?_
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← hev n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ?_
            tower := fun n m hn hm a => hinj ?_
            isom := fun n hn a b => ?_ },
    fun n hn => ⟨by rw [← hζ n hn]; rfl, fun v => (hev n v hn).symm⟩⟩
  · refine IsPrimitiveRoot.of_map_of_injective ?_ (units_map_injective i)
    rw [hζ n hn]; exact I'.ζ_prim n hn
  · rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm]
  · by_cases hn : 0 < n
    · apply hinj
      rw [map_mul, hev _ _ hn, hev _ _ hn, hev _ _ hn, I'.add]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hev0 _ _ hn, _root_.mul_one]
  · by_cases hn : 0 < n
    · apply hinj
      rw [hact, hev _ _ hn, hev _ _ hn, I'.lin]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hone]
  · rw [← map_eq_one_iff f hinj, map_pow, I'.onto n hn]
    refine exists_congr fun a => ?_
    rw [← hev n a hn, hinj.eq_iff]
  · rw [map_pow, hev _ _ (Nat.mul_pos hn hm), hev _ _ hn, I'.tower n m hn hm]
  · rw [← he, map_zpow, hζ n hn, hev _ _ hn, hev _ _ hn]
    exact I'.isom n hn a b

end Abstract

noncomputable def precomp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (A : Over S) [GrpObj A] :
    (T ⟶ A) →* (T' ⟶ A) where
  toFun y := g ≫ y
  map_one' := MonObj.comp_one g
  map_mul' a b := MonObj.comp_mul g a b

theorem tateIso_fieldExt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S), (∀ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v) ∧ ∀ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), (∀ c, IsMonHom (act c)) → ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v := by
  intro hL E _ _ _ H D S P act K Ω _ _ _ _ _ i x
  obtain ⟨hinj, honto⟩ := _root_.GlobalTheory.torsion_points_field_extension hL S P K Ω i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have honto' : ∀ n, 0 < n → ∀ z : Over.mk (spMap i ≫ x) ⟶ P.A, z ^ n = 1 →
      ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ precomp g P.A y = z :=
    fun n hn z hz => honto n z (Nat.cast_ne_zero.mpr hn.ne') hz
  refine ⟨fun I => up D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun n y y' c => _root_.GlobalTheory.weilIs_fieldExt_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I,
    fun I' hm => down D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun c => ?_) (fun n y y' c => _root_.GlobalTheory.weilIs_fieldExt_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I'⟩
  haveI := hm c
  exact MonObj.one_comp (act c)

end GlobalTheory.TateIsoFieldExt
end

