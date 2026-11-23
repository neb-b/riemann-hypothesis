module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactDetBandSiegelSet
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

open scoped Pointwise

namespace GlobalTheory.SiegelBand

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

theorem le_pow_mul_of_adjacent {a : ℕ} (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {Q : ℝ} (hQ : 1 ≤ Q)
    (hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i) (i j : Fin a) :
    ρ i ≤ Q ^ a * ρ j := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have key : ∀ m : ℕ, ∀ i j : Fin a, (j : ℕ) = i + m → ρ i ≤ Q ^ m * ρ j ∧ ρ j ≤ Q ^ m * ρ i := by
    intro m
    induction m with
    | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      subst this
      simp
    | succ m ih =>
      intro i j h
      let j' : Fin a := ⟨i + m, by omega⟩
      obtain ⟨h1, h2⟩ := ih i j' rfl
      obtain ⟨h3, h4⟩ := hadj j' j (by simp [j']; omega)
      have hpm : 0 ≤ Q ^ m := pow_nonneg hQ0 m
      constructor
      · calc ρ i ≤ Q ^ m * ρ j' := h1
          _ ≤ Q ^ m * (Q * ρ j) := mul_le_mul_of_nonneg_left h3 hpm
          _ = Q ^ (m + 1) * ρ j := by ring
      · calc ρ j ≤ Q * ρ j' := h4
          _ ≤ Q * (Q ^ m * ρ i) := mul_le_mul_of_nonneg_left h2 hQ0
          _ = Q ^ (m + 1) * ρ i := by ring
  rcases le_total (i : ℕ) j with hij | hij
  · have h := (key ((j : ℕ) - i) i j (by omega)).1
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)
  · have h := (key ((i : ℕ) - j) j i (by omega)).2
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)

theorem absDetA_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    absDetA g = (ideleModule E (AdelicGLn.det E a g) : ℝ) := by
  unfold absDetA
  rw [Reduction.adeleAbs_units (K := E)]
  rfl

theorem posIdele_congr {E : Type} [Field E] [NumberField E] {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    Reduction.posIdele (K := E) x hx = Reduction.posIdele (K := E) y hy := by
  subst h; rfl

theorem exists_isCompact_band_siegel : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  intro E _ _ a ω hω t R ht
  classical
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hfc : Continuous fun b : GA E a => (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := Reduction.exists_pos_bounds hω hfc
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  set Q : ℝ := max 1 (max R t⁻¹) with hQdef
  have hQ : 1 ≤ Q := le_max_left _ _
  set Qa : ℝ := (Q ^ a) ^ a with hQadef
  have hQa : 0 < Qa := pow_pos (pow_pos (zero_lt_one.trans_le hQ) _) _
  set lo : ℝ := min 1 (X₁ / Qa) with hlodef
  set hi : ℝ := max 1 (Qa * X₂) with hhidef
  have hlo : 0 < lo := lt_min one_pos (div_pos hX₁ hQa)
  let g : {r : ℝ // 0 < r} → IdeleGroup E := fun r => Reduction.posIdele (K := E) r.1 r.2
  have hg : Continuous g := Reduction.continuous_posIdele_subtype
  let h : (Fin a → ℝ) → (Fin a → IdeleGroup E) := fun ρ i => g ⟨max (ρ i) lo, hlo.trans_le (le_max_right _ _)⟩
  have hh : Continuous h := continuous_pi fun i => hg.comp
      (((continuous_apply i).max continuous_const).subtype_mk fun ρ => hlo.trans_le (le_max_right _ _))
  let F : (Fin a → ℝ) → GA E a := fun ρ => Reduction.diagUnits a (h ρ)
  have hF : Continuous F := (Reduction.continuous_diagUnits (K := E) a).comp hh
  have hT : IsCompact (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) := (isCompact_univ_pi fun _ => isCompact_Icc).image hF
  have hband : band E a = {g | 1 ≤ (ideleModule E (AdelicGLn.det E a g) : ℝ)} ∩
      {g | (ideleModule E (AdelicGLn.det E a g) : ℝ) ≤ 2} := by
    ext g; simp [band, absDetA_eq]
  have hclosed : IsClosed (band E a) := by
    rw [hband]; exact (isClosed_le continuous_const hfc).inter (isClosed_le hfc continuous_const)
  refine ⟨ω * (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) * (Reduction.maxCompact (K := E) (n := a) : Set (GA E a)) ∩ band E a,
    ((hω.mul hT).mul Reduction.isCompact_maxCompact).inter_right hclosed, Set.inter_subset_right, ?_⟩
  intro b hb ρ hρ hlow hup k hk hmem
  refine ⟨?_, hmem⟩
  set P : ℝ := ∏ i, ρ i with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => hρ i
  have hdet := Reduction.det_mul_mul b (Reduction.diagUnits a fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) k
  rw [Reduction.ideleModule_det_diagUnits_posIdele ρ hρ,
    Reduction.mem_normOneGL.1 (Reduction.maxCompact_le_normOneGL hk), mul_one] at hdet
  have hm := hmem
  simp only [band, Set.mem_setOf_eq, absDetA_eq] at hm
  rw [hdet] at hm
  obtain ⟨h1, h2⟩ := hm
  have hbb := hB b hb
  have hPd1 : P ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc P ^ d * B₁ ≤ P ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hbb.1 (pow_nonneg hP.le _)
      _ = _ := mul_comm _ _
      _ ≤ 2 := h2
  have hPd2 : B₂⁻¹ ≤ P ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ B₂ * P ^ d := mul_le_mul_of_nonneg_right hbb.2 (pow_nonneg hP.le _)
  have hPlow : X₁ ≤ P := by
    rcases le_or_gt 1 P with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hPd2.trans (pow_le_of_le_one hP.le h.le hd0.ne'))
  have hPup : P ≤ X₂ := by
    rcases le_or_gt P 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hPd1.trans (le_max_right _ _))
  have hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i := by
    intro i j hij
    constructor
    · exact (hup i j hij).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (hρ j).le)
    · calc ρ j = t⁻¹ * (t * ρ j) := by field_simp
        _ ≤ t⁻¹ * ρ i := mul_le_mul_of_nonneg_left (hlow i j hij) (inv_nonneg.2 ht.le)
        _ ≤ Q * ρ i := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) (hρ i).le
  have hratio := le_pow_mul_of_adjacent ρ hρ hQ hadj
  have hbox : ∀ i, ρ i ∈ Set.Icc lo hi := by
    intro i
    have ha0 : a ≠ 0 := by have := i.2; omega
    have hup' : ρ i ^ a ≤ Qa * P := by
      calc ρ i ^ a = ∏ _j : Fin a, ρ i := by simp
        _ ≤ ∏ j : Fin a, (Q ^ a * ρ j) :=
          Finset.prod_le_prod₀ (fun _ _ => (hρ i).le) fun j _ => hratio i j
        _ = Qa * P := by rw [Finset.prod_mul_distrib]; simp [hQadef, hPdef]
    have hlow' : P ≤ Qa * ρ i ^ a := by
      calc P = ∏ j : Fin a, ρ j := rfl
        _ ≤ ∏ _j : Fin a, (Q ^ a * ρ i) :=
          Finset.prod_le_prod₀ (fun j _ => (hρ j).le) fun j _ => hratio j i
        _ = Qa * ρ i ^ a := by rw [Finset.prod_mul_distrib]; simp [hQadef]
    constructor
    · rcases le_or_gt 1 (ρ i) with h | h
      · exact (min_le_left _ _).trans h
      · refine (min_le_right _ _).trans ?_
        refine (pow_le_of_le_one (hρ i).le h.le ha0).trans' ?_
        rw [div_le_iff₀ hQa, mul_comm]
        exact hPlow.trans hlow'
    · rcases le_or_gt (ρ i) 1 with h | h
      · exact h.trans (le_max_left _ _)
      · exact (le_self_pow₀ h.le ha0).trans (hup'.trans
          ((mul_le_mul_of_nonneg_left hPup hQa.le).trans (le_max_right _ _)))
  have hFρ : F ρ = Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) := by
    show Reduction.diagUnits a (h ρ) = _
    congr 1
    funext i
    exact posIdele_congr _ _ (max_eq_left (hbox i).1)
  rw [← hFρ]
  exact Set.mul_mem_mul (Set.mul_mem_mul hb ⟨ρ, fun i _ => hbox i, rfl⟩) hk

end GlobalTheory.SiegelBand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassAgreeingNearZeros
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.KummerStep

noncomputable abbrev gU (A : Type) [CommRing A] : Aˣ →* (Γ(Spec (CommRingCat.of A), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isUnit_natCast_of {k R : Type} [Field k] [CommRing R] (φ : k →+* R) {q : ℕ} (hq : IsUnit (q : k)) :
    IsUnit (q : R) := by
  simpa using hq.map φ

theorem kum_spMap (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hq : IsUnit (q : A))
    (u : Aˣ) : pull _ (spMap φ) _ _ (kum q (gU A u)) = kum q (gU B (Units.map φ.toMonoidHom u)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [(GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.2.2 (Spec.map (CommRingCat.ofHom φ)) (gU A u) hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← h]; simp
  simp only [gU, Units.coe_map, MonoidHom.coe_coe]
  rw [h2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  simp

theorem kum_pow_eq (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (u v : Aˣ) :
    kum q (gU A (u * v ^ q)) = kum q (gU A u) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [map_mul, map_pow, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A u) _ hq').1, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A v) (gU A v) hq').2, add_zero]

theorem kum_pow (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (v : Aˣ) :
    kum q (gU A (v ^ q)) = 0 := by
  have := kum_pow_eq q hq 1 v
  rw [one_mul] at this
  rw [this, map_one]
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have h := ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hq').1
  rw [one_mul] at h
  simpa using h

theorem of_steps (L1 : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c) (L2 : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q) : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  intro q _ k B _ _ _ _ _ _ hq f hf A' _ _ hA' w
  obtain ⟨A₂, _, _, _, _, hA₂, c, hc⟩ := L1 q k B hq f hf A' hA' w
  set c₀ : (Localization.Away (algebraMap B A₂ f))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (algebraMap B A₂ f)))).hom.hom.toMonoidHom c with hc₀
  have hcc : gU _ c₀ = c := by
    ext; simp [c₀, gU]
  obtain ⟨g, hfg, u, ⟨A₃, _, _, _, _, hA₃, hg, v, hv⟩, C, _, _, hC, v', hv'⟩ := L2 q k B hq f hf A₂ hA₂ c₀
  letI : Algebra A' A₃ := ((algebraMap A₂ A₃).comp (algebraMap A' A₂)).toAlgebra
  haveI : IsScalarTower B A' A₃ := IsScalarTower.of_algebraMap_eq (fun b => by
    show algebraMap B A₃ b = algebraMap A₂ A₃ (algebraMap A' A₂ (algebraMap B A' b))
    rw [← IsScalarTower.algebraMap_apply B A' A₂, ← IsScalarTower.algebraMap_apply B A₂ A₃])
  have hkB : ∀ (R : Type) [CommRing R] [Algebra B R], IsUnit (q : R) := fun R _ _ =>
    isUnit_natCast_of ((algebraMap B R).comp (algebraMap k B)) hq
  refine ⟨g, hfg, A₃, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA₃, hg, hC, kum q (gU _ u), ?_, ?_⟩
  · rw [kum_spMap q _ (hkB _)]
    have : Units.map (Localization.awayMap (algebraMap B C) (f * g)).toMonoidHom u = v' ^ q := by
      ext; simpa using hv'
    rw [this]
    exact kum_pow q (hkB _) v'
  · intro φ ψ hφ hψ
    have hu₁ : IsUnit (((algebraMap A₂ (Localization.Away (algebraMap B A₂ f))).comp (algebraMap A' A₂))
        (algebraMap B A' f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hu₂ : IsUnit (((algebraMap A₃ (Localization.Away (algebraMap B A₃ f))).comp (algebraMap A₂ A₃))
        (algebraMap B A₂ f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A₂ A₃]
      exact IsLocalization.Away.algebraMap_isUnit _
    set φ₁ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f) :=
      IsLocalization.Away.lift (algebraMap B A' f) hu₁
    set φ₂ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f) :=
      IsLocalization.Away.lift (algebraMap B A₂ f) hu₂
    have hφ₁ : φ₁.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A' f)) (algebraMap B A' f) hu₁
    have hφ₂ : φ₂.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) hu₂
    have hφe : φ = φ₂.comp φ₁ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) ?_
      rw [hφ, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, hφ₂, RingHom.comp_assoc]
      rfl
    have key := hv φ₂ ψ hφ₂ hψ
    have hkey : Units.map φ₂.toMonoidHom c₀ = Units.map ψ.toMonoidHom u * v ^ q := by
      ext; simpa using key
    rw [hφe, spMap_comp', pull_comp, hc φ₁ hφ₁, ← hcc, kum_spMap q φ₂ (hkB _), hkey, kum_pow_eq q (hkB _),
      kum_spMap q ψ (hkB _)]

theorem exists_class_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a :=
  of_steps GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow

end GlobalTheory.EtC.KummerStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadLB

open GlobalTheory.CechPic in
theorem exists_spread : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by

  intro S Y U YU _ f _ _ j _ e fU hpb L hL x N hN hag
  obtain ⟨W₁, hx₁, N₁, hN₁, hq⟩ := _root_.GlobalTheory.StalkLB.exists_lb_nhd f x N hN
  have hr1 : Set.range (pullback.fst f (S.fromSpecStalk x)) ⊆ Set.range (f ⁻¹ᵁ W₁).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f (pullback.fst f (S.fromSpecStalk x) y) ∈ W₁
    have hsp : f (pullback.fst f (S.fromSpecStalk x) y) ⤳ x := by
      have : f (pullback.fst f (S.fromSpecStalk x) y) ∈ Set.range (S.fromSpecStalk x) :=
        ⟨pullback.snd f (S.fromSpecStalk x) y, by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hsp.mem_open W₁.isOpen hx₁
  let q₁ := IsOpenImmersion.lift (f ⁻¹ᵁ W₁).ι (pullback.fst f (S.fromSpecStalk x)) hr1
  have hq₁ : q₁ ≫ (f ⁻¹ᵁ W₁).ι = pullback.fst f (S.fromSpecStalk x) := IsOpenImmersion.lift_fac _ _ _
  have iso1 := hq q₁ hq₁
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip inferInstance
  haveI : QuasiCompact e := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  haveI : QuasiCompact (f ⁻¹ᵁ W₁).ι := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict f W₁) inferInstance
  let h : pullback (f ⁻¹ᵁ W₁).ι e ⟶ S := pullback.fst (f ⁻¹ᵁ W₁).ι e ≫ (f ⁻¹ᵁ W₁).ι ≫ f

  obtain ⟨W₂, hx₂, iso2⟩ := _root_.GlobalTheory.StalkLBIso.exists_lbIso_nhd h x (N₁.pull (pullback.fst (f ⁻¹ᵁ W₁).ι e))
    (L.pull (pullback.snd (f ⁻¹ᵁ W₁).ι e)) (pull_isLB hN₁ _) (pull_isLB hL _) (by
      set r := pullback.fst h (S.fromSpecStalk x)
      have hs : (r ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e ≫ (f ⁻¹ᵁ W₁).ι) ≫ f = pullback.snd h (S.fromSpecStalk x) ≫ S.fromSpecStalk x := by
        rw [← pullback.condition]; simp only [h, Category.assoc]; rfl
      let s := pullback.lift _ _ hs
      have hs1 : s ≫ q₁ = r ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e := by
        rw [← cancel_mono (f ⁻¹ᵁ W₁).ι, Category.assoc, hq₁]; simp only [s, pullback.lift_fst, Category.assoc]
      have hs2 : s ≫ pullback.fst f (S.fromSpecStalk x) = (r ≫ pullback.snd (f ⁻¹ᵁ W₁).ι e) ≫ e := by
        simp only [s, pullback.lift_fst, Category.assoc, pullback.condition]
      have i3 := (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 (hag _ s _ hs2)
      have i1 := (cls_eq_iff (pull_isLB hN₁ _) hN).2 iso1
      refine (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) r) (pull_isLB (pull_isLB hL _) r)).1 ?_
      rw [cls_pull (pull_isLB hN₁ _), cls_pull hN₁, cls_pull (pull_isLB hL _), cls_pull hL, ← pull_comp, ← pull_comp, ← hs1,
        pull_comp, ← cls_pull hN₁ _ (pull_isLB hN₁ _), i1, ← cls_pull hN _ (pull_isLB hN _), i3, cls_pull hL])
  refine ⟨W₁ ⊓ W₂, ⟨hx₁, hx₂⟩, ?_⟩
  have hle : f ⁻¹ᵁ (W₁ ⊓ W₂) ≤ f ⁻¹ᵁ W₁ := fun y hy => hy.1
  refine ⟨N₁.pull (Y.homOfLE hle), pull_isLB hN₁ _, fun T a b hab => ?_⟩
  have hc : (a ≫ Y.homOfLE hle) ≫ (f ⁻¹ᵁ W₁).ι = b ≫ e := by rw [Category.assoc, Scheme.homOfLE_ι, hab]
  let c := pullback.lift _ _ hc
  have hcr : Set.range c ⊆ Set.range (h ⁻¹ᵁ W₂).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (c t) ∈ W₂
    have : c ≫ h = a ≫ (f ⁻¹ᵁ (W₁ ⊓ W₂)).ι ≫ f := by
      simp only [h, c, pullback.lift_fst_assoc, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
    exact ((a t).2 : _).2
  let d := IsOpenImmersion.lift (h ⁻¹ᵁ W₂).ι c hcr
  have hd : d ≫ (h ⁻¹ᵁ W₂).ι = c := IsOpenImmersion.lift_fac _ _ _
  have i2 := (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) _) (pull_isLB (pull_isLB hL _) _)).2 iso2
  refine (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) a) (pull_isLB hL b)).1 ?_
  have e1 : a ≫ Y.homOfLE hle = d ≫ (h ⁻¹ᵁ W₂).ι ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e := by
    rw [← Category.assoc, hd]; simp only [c, pullback.lift_fst]
  have e2 : b = d ≫ (h ⁻¹ᵁ W₂).ι ≫ pullback.snd (f ⁻¹ᵁ W₁).ι e := by
    rw [← Category.assoc, hd]; simp only [c, pullback.lift_snd]
  rw [cls_pull (pull_isLB hN₁ _), cls_pull hN₁, ← pull_comp, e1, cls_pull hL, e2, pull_comp, pull_comp, pull_comp d,
    pull_comp (h ⁻¹ᵁ W₂).ι, ← cls_pull hN₁ _ (pull_isLB hN₁ _), ← cls_pull (pull_isLB hN₁ _) _ (pull_isLB (pull_isLB hN₁ _) _), i2,
    cls_pull (pull_isLB hL _), cls_pull hL]

end GlobalTheory.SpreadLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZeroSectionValueInPowerFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUnivVals

open TopologicalSpace Opposite

theorem comp_base_pt {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem glue_fn {X : Scheme.{0}} {J : Type} (W : J → X.Opens) (hc : (⊤ : X.Opens) ≤ iSup W) (a : ∀ i, Γ(X, W i))
    (h : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 X) x (W i) (a i) = gs (𝟙 X) x (W j) (a j)) :
    ∃ α : Γ(X, ⊤), ∀ i x, x ∈ W i → gs (𝟙 X) x ⊤ α = gs (𝟙 X) x (W i) (a i) := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hc a
    (fun i j => fn_ext (V := W i ⊓ W j) fun y hy =>
      (gs_res (𝟙 X) y inf_le_left hy _).trans ((h i j y hy.1 hy.2).trans (gs_res (𝟙 X) y inf_le_right hy _).symm))
  refine ⟨s, fun i x hx => ?_⟩
  exact (gs_res (𝟙 X) x (le_top : W i ≤ ⊤) hx s).symm.trans (congrArg (gs (𝟙 X) x (W i)) (hs i))

theorem vals (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))) (hL : L.IsLB) (hA : eA.IsGen) :
    ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  set S : Scheme.{0} := (𝟙_ (Over (Sp Rg))).left with hS
  set e : S ⟶ (topS Rg ⊗ A).left := eSec A ≫ θ A with he_def
  have he : e ≫ (snd (topS Rg) A).left = eSec A := by
    rw [he_def, Category.assoc, θ_snd, Category.comp_id]
  have memN : ∀ (z : S) (q : Fin 1 → L.ι), e z ∈ (LPow A L (k : ℤ) (topS Rg)).U q ↔ eSec A z ∈ L.U (q 0) := by
    intro z q
    constructor
    · intro h
      have h0 := Set.mem_iInter.1 h 0
      rw [Set.mem_preimage, ← comp_base_pt, he] at h0
      exact h0
    · intro h
      refine Set.mem_iInter.2 fun t => ?_
      rw [Subsingleton.elim t 0, Set.mem_preimage, ← comp_base_pt, he]
      exact h
  let W : L.ι → S.Opens := fun i => e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => i)
  have memW : ∀ (z : S) (i : L.ι), z ∈ W i ↔ eSec A z ∈ L.U i := by
    intro z i
    constructor
    · intro h; exact mem_pull.1 h.2
    · intro h; exact ⟨(memN z _).2 h, mem_pull.2 h⟩
  let a : ∀ i, Γ(S, W i) := fun i =>
    (S.presheaf.map (homOfLE (inf_le_left : W i ≤ e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i))).op).hom ((e.app _).hom (s.f (fun _ => i))) *
      ((res (inf_le_right : W i ≤ (L.pull (eSec A)).U (fun _ => i)) (eA.s (fun _ => i)))⁻¹ ^ k).val
  have ga : ∀ i x, x ∈ W i → gs (𝟙 S) x (W i) (a i) =
      gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i)) (s.f (fun _ => i)) * ((gm (𝟙 S) x _ (eA.s (fun _ => i)))⁻¹ ^ k).val := by
    intro i x hx
    rw [gs_mul (𝟙 S) x _ hx, gs_res (𝟙 S) x _ hx, gs_pull (𝟙 S) e x _ hx.1, Category.id_comp, gs_unit (𝟙 S) x _ hx,
      map_pow, map_inv, gm_res (𝟙 S) x _ hx]

  have compat : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 S) x (W i) (a i) = gs (𝟙 S) x (W j) (a j) := by
    intro i j x hx hy
    have hxi := (memW x i).1 hx
    have hxj := (memW x j).1 hy
    have hx' : e x ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j) := ⟨hx.1, hy.1⟩
    have mem : (snd (topS Rg) A).left (e x) ∈ L.U i ⊓ L.U j := by
      rw [← comp_base_pt, he]; exact ⟨hxi, hxj⟩
    have hg : gm e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) ((LPow A L (k : ℤ) (topS Rg)).g (fun _ => i) (fun _ => j)) =
        (gm (eSec A) x _ (L.g i j)) ^ k := by
      show gm e x _ (∏ _t : Fin 1, (res _ (pullU (snd (topS Rg) A).left _ (L.g i j))) ^ (k : ℤ)) = _
      rw [Fintype.prod_unique, map_zpow]
      erw [gm_res e x _ hx']
      rw [gm_pull e _ x _ mem, he, zpow_natCast]
    have hs := congrArg (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j))) (s.compat (fun _ => i) (fun _ => j))
    rw [gs_res e x _ hx', gs_mul e x _ hx', gs_res e x _ hx', gs_unit e x _ hx', hg] at hs
    have hp : x ∈ (L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j) := ⟨hx.2, hy.2⟩
    have mem' : (eSec A) ((𝟙 S : S ⟶ S) x) ∈ L.U i ⊓ L.U j := ⟨hxi, hxj⟩
    have hg' : gm (𝟙 S) x _ ((L.pull (eSec A)).g (fun _ => i) (fun _ => j)) = gm (eSec A) x _ (L.g i j) := by
      show gm (𝟙 S) x _ (∏ _t : PUnit, (res _ (pullU (eSec A) _ (L.g i j))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      erw [gm_res (𝟙 S) x _ hp]
      rw [gm_pull (𝟙 S) (eSec A) x _ mem', Category.id_comp]
    have hA' := congrArg (gm (𝟙 S) x ((L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j)))
      (hA (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ x _ hp, gm_res _ x _ hp, hg'] at hA'
    rw [ga i x hx, ga j x hy, hs, hA']
    set u := gm (eSec A) x _ (L.g i j)
    set B := gm (𝟙 S) x _ (eA.s (fun _ => j))
    have hinv : (u * B)⁻¹ ^ k = (u ^ k)⁻¹ * B⁻¹ ^ k := by rw [mul_inv, mul_pow, inv_pow]
    have hU : (u ^ k).val * ((u ^ k)⁻¹).val = 1 := Units.mul_inv _
    rw [hinv, Units.val_mul]
    linear_combination (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) (s.f (fun _ => j)) * (B⁻¹ ^ k).val) * hU
  obtain ⟨α, hα⟩ := glue_fn W (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (eSec A x)
      exact Opens.mem_iSup.2 ⟨i, (memW x i).2 hi⟩) a compat
  refine ⟨α, fun z q hz => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, q = fun _ => i := ⟨q 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
  have hzW : z ∈ W i := (memW z i).2 ((memN z _).1 hz)
  rw [hα i z hzW, ga i z hzW]
  show _ = _ * ((gm (𝟙 S) z _ (eA.s fun _ => i)) ^ k).val
  rw [_root_.mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.HomFixUnivVals
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareOfSymmetricTensorRelationsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations : ∀ (K : Type) [Field K] (V W : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (β : V →ₗ[K] V →ₗ[K] W), Module.finrank K W ≤ (Module.finrank K V).choose 2 → (∀ t : V ⊗[K] V, TensorProduct.lift β t = 0 → TensorProduct.comm K V V t = t) → (∃ e : ⋀[K]^2 V ≃ₗ[K] W, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = β a b) ∧ Function.Surjective (TensorProduct.lift β) ∧ ∀ t : V ⊗[K] V, TensorProduct.comm K V V t = t → TensorProduct.lift β t = 0 := by
  first | exact @GlobalTheory.exteriorSq_of_symm_relations | exact GlobalTheory.exteriorSq_of_symm_relations | (intros; apply GlobalTheory.exteriorSq_of_symm_relations <;> assumption)
end

