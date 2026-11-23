module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTranspose
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_semisimple_rep_tpow {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]
    (ρ : G →* Matrix ι ι ℂ) (h : SS (Set.range ρ)) (n : ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (r : Representation ℂ G V)
      (b : Module.Basis (Fin n → ι) ℂ V),
      r.IsSemisimpleRepresentation ∧ ∀ g, LinearMap.toMatrix b b (r g) = tpow n (ρ g) := by
  induction n with
  | zero =>
    have hm : ∀ g : G, LinearMap.toMatrix (Pi.basisFun ℂ (Fin 0 → ι)) (Pi.basisFun ℂ (Fin 0 → ι))
        (Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g) = 1 := by
      intro g
      have : Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g = LinearMap.id := by
        ext v; simp
      rw [this, LinearMap.toMatrix_id]
    refine ⟨(Fin 0 → ι) → ℂ, inferInstance, inferInstance, Representation.trivial ℂ G _,
      Pi.basisFun ℂ _, ?_, ?_⟩
    · rw [← _root_.GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation (Fin 0 → ι) G _ _ (Pi.basisFun ℂ _)]
      intro W _
      obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
      refine ⟨W', ?_, hW'⟩
      rintro _ ⟨g, rfl⟩ v hv
      simpa only [hm, Matrix.one_mulVec] using hv
    · intro g
      rw [hm]
      ext a b
      have : a = b := Subsingleton.elim _ _
      subst this
      simp [tpow]
  | succ n ih =>
    obtain ⟨V, _, _, r, b, hr, hb⟩ := ih
    let r₁ : Representation ℂ G (ι → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom.toMonoidHom.comp ρ
    have h₁ : ∀ g, LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (r₁ g) = ρ g := by
      intro g
      change LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (Matrix.toLin' (ρ g)) = ρ g
      rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    have hs₁ : r₁.IsSemisimpleRepresentation := by
      rw [← _root_.GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation ι G _ _ (Pi.basisFun ℂ _)]
      simpa only [h₁] using h
    haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b
    let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) := Fin.consEquiv fun _ => ι
    refine ⟨(ι → ℂ) ⊗[ℂ] V, inferInstance, inferInstance, r₁.tprod r,
      ((Pi.basisFun ℂ ι).tensorProduct b).reindex e,
      _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod G _ r₁ V r hs₁ hr, ?_⟩
    intro g
    have ht : LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct b) ((Pi.basisFun ℂ ι).tensorProduct b)
        ((r₁.tprod r) g) = ρ g ⊗ₖ tpow n (ρ g) := by
      rw [Representation.tprod_apply, TensorProduct.toMatrix_map, h₁, hb]
    ext a c
    have := congrFun (congrFun ht (e.symm a)) (e.symm c)
    rw [LinearMap.toMatrix_apply] at this ⊢
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, this]
    simp [e, tpow, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]

theorem ss_tpow_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)),
    IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  intro ι _ _ Γ hΓ hs n
  obtain ⟨G, _, ρ, rfl⟩ := _root_.GlobalTheory.ClassFin.IsPre.exists_group_range ι Γ hΓ
  obtain ⟨V, _, _, r, b, hr, hb⟩ := exists_semisimple_rep_tpow ρ hs n
  have h := _root_.GlobalTheory.ClassFin.ss_transpose _ _ ((_root_.GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation _ G V r b).2 hr)
  simp only [hb] at h
  rw [← Set.range_comp] at h ⊢
  exact h

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletion
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_eq_top_of_isSquare_image {F L : Type} [Field F] [Field L] [CharZero L]
    (φ : F →+* L) (δ : F) (hδ : δ ≠ 0) (h : IsSquare (φ δ)) (x : Fˣ) : x ∈ normSub φ δ := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hδ ((map_eq_zero φ).1 (by simpa using hr))
  refine ⟨(φ x + 1) / 2, (φ x - 1) / (2 * r), ?_⟩
  rw [hr]
  field_simp
  ring

theorem exists_not_mem_not_isSquare_completion :
    ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ u S₀ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, locNorm F u S₀ ≤ locNorm F u S := by
    intro S x hx
    rw [locNorm, Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, hx.2⟩
    have h1 := hx.1
    simp only [Subgroup.mem_iInf] at h1 ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact h1 v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact normSub_eq_top_of_isSquare_image _ u hu (hcon v hv) x
  have hidx := (_root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F u S₀ hu).1
  haveI : (locNorm F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ locNorm F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ locNorm F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hX := hS₁ S hS
  refine _root_.GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top F (Units.mk0 u hu) S hadm (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x ∈ locNorm F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfSUnitLocalSquareFiniteRealPlaces
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_normSub_of_isSquare {F L : Type} [Field F] [CharZero F] [Field L] (φ : F →+* L)
    (δ : Fˣ) (h : IsSquare (φ (δ : F))) (x : Fˣ) : x ∈ normSub φ (δ : F) := by
  obtain ⟨c, hc⟩ := h
  have hδ : φ (δ : F) ≠ 0 := (map_ne_zero φ).mpr δ.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hc
    exact hδ hc
  have h2 : (2 : L) ≠ 0 := by
    have : φ 2 ≠ 0 := (map_ne_zero φ).mpr two_ne_zero
    rwa [map_ofNat] at this
  rw [mem_normSub]
  refine ⟨(φ (x : F) + 1) / 2, (φ (x : F) - 1) / (2 * c), ?_⟩
  rw [hc]
  field_simp
  ring

theorem isSquare_of_mem_locSq : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ locSq F S → IsSquare (y : F) := by
  intro F _ _ _ S T hS hT y hy hloc
  by_contra hns
  apply _root_.GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top F y (S ∪ T) (hS.mono Finset.subset_union_left) hy hns
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  intro x hx
  rw [finSq, Subgroup.mem_iInf] at hx
  rw [locSq, Subgroup.mem_inf, finSq, Subgroup.mem_iInf, Subgroup.mem_iInf] at hloc
  obtain ⟨hlocS, hlocR⟩ := hloc
  rw [locNorm, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_iInf]
  refine ⟨fun v => ?_, fun σ => ?_⟩
  · rw [Subgroup.mem_iInf]
    intro hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact mem_normSub_of_isSquare _ y
        ((mem_sqSub _ _).mp (Subgroup.mem_iInf.mp (hlocS v) hvS)) x
    · exact sqSub_le_normSub _ _ (Subgroup.mem_iInf.mp (hx v) hvT)
  · exact mem_normSub_of_isSquare _ y ((mem_sqSub _ _).mp (hlocR σ)) x

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndex
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_kNorm_iff_map_mem_id (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F)
    (x : Fˣ) :
    x ∈ kNorm p φ δ ↔ Units.map (φ : F →* L) x ∈ kNorm p (RingHom.id L) (φ δ) := by
  rw [mem_kNorm, mem_kNorm]
  exact Iff.rfl

theorem pow_tNon_le_index_finNorm :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ : F)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
      (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  intro p F _ _ _ ζ δ S hp hζ
  classical
  have hpow := (_root_.GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map p hp.pos).1
  have hPN : finPow p F S ≤ finNorm p F δ S := by
    unfold finPow finNorm
    exact iInf_mono fun v => iInf_mono fun _ => hpow _ _ _ _
  have h0 : (finNorm p F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (_root_.GlobalTheory.CNorm.index_finPow_le p F S hp.pos).1 (Subgroup.index_dvd_of_le hPN)
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ} with hA
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  letI : Fintype A := hAf.fintype
  let K : A → Subgroup Fˣ := fun v => kNorm p (algebraMap F (v.1.adicCompletion F)) δ
  have hle : finNorm p F δ S ≤ ⨅ i, K i := le_iInf fun v => iInf₂_le v.1 v.2.1
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card A = tNon p F δ S := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (_root_.GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime p Fˣ A K hp ?_ ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  · intro v x
    exact hpow _ _ _ _ ⟨algebraMap F _ (x : F), by simp⟩
  · intro v
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.CNorm.exists_local_nonnorm p F ζ δ v.1 hp hζ v.2.2
    obtain ⟨x, hx0, hxv⟩ := _root_.GlobalTheory.CNorm.exists_approx_mod_powers p F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1
        (c : v.1.adicCompletion F)) hp.pos (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simp
        · simp [Function.update_of_ne hw])
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      obtain ⟨r, hr⟩ := hxv v.1 v.2.1
      rw [Function.update_self] at hr
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero, mul_zero] at hr
        exact hx0 (by simpa using hr)
      have hm' := (mem_kNorm_iff_map_mem_id p _ δ _).1 hm
      have hrm : (Units.mk0 r hr0) ^ p ∈ kNorm p (RingHom.id (v.1.adicCompletion F))
          (algebraMap F (v.1.adicCompletion F) δ) := hpow _ _ _ _ ⟨r, by simp⟩
      apply hc
      have hq := Subgroup.div_mem _ hm' hrm
      convert hq using 1
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      simpa using hr.symm
    · intro w hj
      have hw : w.1 ≠ v.1 := fun h => hj (Subtype.ext h)
      obtain ⟨r, hr⟩ := hxv w.1 w.2.1
      rw [Function.update_of_ne hw, one_mul] at hr
      exact hpow _ _ _ _ ⟨r, hr.symm⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroup
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] [DecidableEq ι] in
theorem ptsGroup_map_ev {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι A) :
    φ (ev f g) = ev f (g.map φ) := by
  unfold ev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem ptsGroup_generic_map {R : Type} [CommRing R] [Algebra ℚ R] (g : Matrix ι ι R) :
    (Matrix.mvPolynomialX ι ι ℚ).map (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) = g := by
  ext i j
  simp [Matrix.mvPolynomialX]

theorem ptsGroup_ev_adjugate {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι R) : ev (ev f (Matrix.mvPolynomialX ι ι ℚ).adjugate) g = ev f g.adjugate := by
  have h := ptsGroup_map_ev (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) f
    (Matrix.mvPolynomialX ι ι ℚ).adjugate
  have h2 := AlgHom.map_adjugate (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2))
    (Matrix.mvPolynomialX ι ι ℚ)
  simp only [AlgHom.mapMatrix_apply] at h2
  rw [h2, ptsGroup_generic_map] at h
  exact h

theorem ptsGroup_ev_det {R : Type} [CommRing R] [Algebra ℚ R]
    (g : Matrix ι ι R) : ev ((Matrix.mvPolynomialX ι ι ℚ).det - 1) g = g.det - 1 := by
  have h2 := AlgHom.map_det (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2))
    (Matrix.mvPolynomialX ι ι ℚ)
  simp only [AlgHom.mapMatrix_apply] at h2
  rw [ptsGroup_generic_map] at h2
  unfold ev
  rw [map_sub, map_one, h2]

theorem ptsGroup_ev_one (R : Type) [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ) :
    ev f (1 : Matrix ι ι R) = algebraMap ℚ R (ev f (1 : Matrix ι ι ℚ)) := by
  have h := ptsGroup_map_ev (Algebra.ofId ℚ R) f (1 : Matrix ι ι ℚ)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h.symm

theorem ptsGroup_ev_mul {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ)
    (x y : Matrix ι ι R) :
    MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2))
      (ev f ((Matrix.of fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ)) *
        (Matrix.of fun i j => (MvPolynomial.X (Sum.inr (i, j)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ)))) =
      ev f (x * y) := by
  rw [ptsGroup_map_ev]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem pts_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∀ (R : Type) [CommRing R] [Algebra ℚ R], (1 : Matrix ι ι R) ∈ pts Γ R ∧ (∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, x * y ∈ pts Γ R) ∧ (∀ x ∈ pts Γ R, x.adjugate ∈ pts Γ R) ∧ ∀ x ∈ pts Γ R, x.det = 1 := by
  intro ι _ _ Γ hΓ R _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    have h1 := hf 1 hΓ.one_mem
    rw [ptsGroup_ev_one] at h1 ⊢
    rw [(map_eq_zero_iff _ (algebraMap ℚ ℂ).injective).1 h1, map_zero]
  · intro x hx y hy f hf
    rw [← ptsGroup_ev_mul]
    refine _root_.GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts ι Γ hΓ.aut_mem _ ?_ R x hx y hy
    intro g hg h hh
    rw [ptsGroup_ev_mul]
    exact hf _ (hΓ.mul_mem g hg h hh)
  · intro x hx f hf
    rw [← ptsGroup_ev_adjugate]
    refine hx _ ?_
    intro g hg
    rw [ptsGroup_ev_adjugate]
    exact hf _ (hΓ.adj_mem g hg)
  · intro x hx
    rw [← sub_eq_zero, ← ptsGroup_ev_det]
    refine hx _ ?_
    intro g hg
    rw [ptsGroup_ev_det, hΓ.det_eq g hg, sub_self]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ZlatticeTsumDilateSubIntegralLeRapidStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) / ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  exact @GlobalTheory.latticeSum_dilate_sub_integral_le
end

