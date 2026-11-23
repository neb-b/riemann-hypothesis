module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalSectionFamilyUnitAtPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.SemiLoc

variable {X : Scheme.{0}}

theorem exists_pow_mul_eq_zero_of_germ {V : X.Opens} (hV : IsAffineOpen V) (h s : Γ(X, V))
    (H : ∀ z (hz : z ∈ V), z ∈ X.basicOpen h → (X.presheaf.germ V z hz).hom s = 0) :
    ∃ m : ℕ, h ^ m * s = 0 := by
  apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hV
  apply TopCat.Presheaf.section_ext X.sheaf
  intro z hz
  simp only [TopCat.Presheaf.restrictOpen, map_zero]
  erw [TopCat.Presheaf.germ_res_apply]
  exact H z (X.basicOpen_le h hz) hz

theorem exists_germ_eq_pow_mul {V O : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hO : X.basicOpen h ≤ O) (r : Γ(X, O)) :
    ∃ (n : ℕ) (y : Γ(X, V)), ∀ z (hz : z ∈ X.basicOpen h),
      (X.presheaf.germ V z (X.basicOpen_le h hz)).hom y =
        (X.presheaf.germ V z (X.basicOpen_le h hz)).hom h ^ n *
          (X.presheaf.germ O z (hO hz)).hom r := by
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV h
    ((X.presheaf.map (homOfLE hO).op).hom r)
  refine ⟨n, y, fun z hz => ?_⟩
  have := congrArg (X.presheaf.germ (X.basicOpen h) z hz).hom hy
  simp only [TopCat.Presheaf.restrictOpen, map_mul, map_pow] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem germ_cocycle {L : LB X} (hL : L.IsLB) (a b c : L.ι) (z : X) (ha : z ∈ L.U a)
    (hb : z ∈ L.U b) (hc : z ∈ L.U c) :
    (X.presheaf.germ (L.U a ⊓ L.U b) z ⟨ha, hb⟩).hom (L.g a b).val *
      (X.presheaf.germ (L.U b ⊓ L.U c) z ⟨hb, hc⟩).hom (L.g b c).val =
    (X.presheaf.germ (L.U a ⊓ L.U c) z ⟨ha, hc⟩).hom (L.g a c).val := by
  have := congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ =>
    (X.presheaf.germ (L.U a ⊓ L.U b ⊓ L.U c) z ⟨⟨ha, hb⟩, hc⟩).hom u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul, res, Units.coe_map] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

end GlobalTheory.Pinch.SemiLoc

namespace GlobalTheory.Pinch.SemiLoc

theorem exists_secFam_isUnit_germ : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ (J : Type) [Fintype J] (f : J → Γ(X, W)) (k : J → L.ι) (hk : ∀ j, X.basicOpen (f j) ≤ L.U (k j)) (x : X), x ∈ W → ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧ ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
  intro X L hL W hW J _ f k hk x hxW
  classical
  obtain ⟨k0, hk0⟩ : ∃ k0, x ∈ L.U k0 := by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨h, hhU, hxh⟩ := hW.exists_basicOpen_le (V := L.U k0) ⟨x, hk0⟩ hxW
  have hDW : ∀ j, X.basicOpen (f j) ≤ W := fun j => X.basicOpen_le (f j)
  let hj : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom h
  have hbj : ∀ j, X.basicOpen (hj j) = X.basicOpen (f j) ⊓ X.basicOpen h :=
    fun j => X.basicOpen_res h _
  have hgj : ∀ j z (hz : z ∈ X.basicOpen (f j)),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (hj j) =
        (X.presheaf.germ W z (hDW j hz)).hom h :=
    fun j z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hO : ∀ j, X.basicOpen (hj j) ≤ L.U (k j) ⊓ L.U k0 := fun j => by
    rw [hbj]; exact inf_le_inf (hk j) hhU
  choose n y hy using fun j =>
    exists_germ_eq_pow_mul (hW.basicOpen (f j)) (hj j) (hO j) (L.g (k j) k0).val
  let N := Finset.univ.sup n
  let e : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => hj j ^ (N - n j) * y j
  have he : ∀ j z (hz : z ∈ X.basicOpen (f j)) (hzh : z ∈ X.basicOpen h),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) =
        (X.presheaf.germ W z (hDW j hz)).hom h ^ N *
          (X.presheaf.germ (L.U (k j) ⊓ L.U k0) z ⟨hk j hz, hhU hzh⟩).hom (L.g (k j) k0).val := by
    intro j z hz hzh
    have hz' : z ∈ X.basicOpen (hj j) := by rw [hbj]; exact ⟨hz, hzh⟩
    have h1 := hy j z hz'
    simp only [e, map_mul, map_pow]
    rw [h1]; simp only [hgj]; rw [← _root_.mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ j))]
  have hdef : ∀ j j', ∃ m : ℕ, ∀ z (hz : z ∈ X.basicOpen (f j)) (hz' : z ∈ X.basicOpen (f j')),
      (X.presheaf.germ W z (hDW j hz)).hom h ^ m *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
    intro j j'
    obtain ⟨V, hVdef⟩ : ∃ V, V = X.basicOpen (f j * f j') := ⟨_, rfl⟩
    have hVeq : V = X.basicOpen (f j) ⊓ X.basicOpen (f j') := hVdef.trans (X.basicOpen_mul _ _)
    have hVa : IsAffineOpen V := hVdef ▸ hW.basicOpen (f j * f j')
    have hV1 : V ≤ X.basicOpen (f j) := hVeq ▸ inf_le_left
    have hV2 : V ≤ X.basicOpen (f j') := hVeq ▸ inf_le_right
    have hVg : V ≤ L.U (k j) ⊓ L.U (k j') := le_inf (hV1.trans (hk j)) (hV2.trans (hk j'))
    have hVW : V ≤ W := hV1.trans (hDW j)
    let d : Γ(X, V) := (X.presheaf.map (homOfLE hV1).op).hom (e j) -
      (X.presheaf.map (homOfLE hVg).op).hom (L.g (k j) (k j')).val *
        (X.presheaf.map (homOfLE hV2).op).hom (e j')
    let hV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom h
    have hbV : X.basicOpen hV = V ⊓ X.basicOpen h := X.basicOpen_res h _
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_germ hVa hV d (by
      intro z hz hzb
      rw [hbV] at hzb
      simp only [d, map_sub, map_mul]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply]
      rw [he j z (hV1 hz) hzb.2, he j' z (hV2 hz) hzb.2,
        ← germ_cocycle hL (k j) (k j') k0 z (hk j (hV1 hz)) (hk j' (hV2 hz)) (hhU hzb.2)]
      ring)
    refine ⟨m, fun z hz hz' => ?_⟩
    have hzV : z ∈ V := by rw [hVeq]; exact ⟨hz, hz'⟩
    have := congrArg (X.presheaf.germ V z hzV).hom hm
    simp only [d, hV, map_mul, map_pow, map_sub, map_zero] at this
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
    exact this
  choose m hm using hdef
  let M := Finset.univ.sup (fun p : J × J => m p.1 p.2)
  refine ⟨fun j => hj j ^ M * e j, ?_, ?_⟩
  · intro j j' z hz hz'
    have hle : m j j' ≤ M := Finset.le_sup (f := fun p : J × J => m p.1 p.2) (Finset.mem_univ (j, j'))
    have h0 := hm j j' z hz hz'
    simp only [map_mul, map_pow]
    simp only [hgj]
    have h2 : (X.presheaf.germ W z (hDW j hz)).hom h ^ M *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
      rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc, h0, mul_zero]
    linear_combination h2
  · intro j hx
    have hu : IsUnit ((X.presheaf.germ W x (hDW j hx)).hom h) := (X.mem_basicOpen h x _).1 hxh
    simp only [map_mul, map_pow]
    simp only [hgj]; rw [he j x hx hxh]
    exact (hu.pow _).mul ((hu.pow _).mul ((L.g (k j) k0).isUnit.map _))

end GlobalTheory.Pinch.SemiLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldTopFormPairingRegularAtPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open IsLocalRing

theorem isUnit_det_of_span_eq_top (k A : Type) [CommRing k] [CommRing A] [Algebra k A] {N : ℕ} (g : Fin N → A)
    (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (hδ : Submodule.span A (Set.range δ) = ⊤) :
    IsUnit (Matrix.of fun i j => δ j (g i)).det := by
  classical
  have h : ∀ i, ∃ a : Fin N → A, ∑ j, a j • δ j = KaehlerDifferential.linearMapEquivDerivation k A (bΩ.coord i) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hδ ▸ Submodule.mem_top)
  choose a ha using h
  have hm : (Matrix.of fun i j => δ j (g i)) * (Matrix.of fun j i => a i j) = 1 := by
    ext l i
    have h1 := congrArg (fun d : Derivation k A A => d (g l)) (ha i)
    simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hg] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 : (∑ j, a i j • δ j) (g l) = ∑ j, a i j * δ j (g l) := by
      have := map_sum (FunLike.coeAddMonoidHom (Derivation k A A) A A) (fun j => a i j • δ j) Finset.univ
      have h3 := congrFun this (g l)
      rw [Finset.sum_apply] at h3
      exact h3
    rw [h2] at h1
    simp only [Matrix.of_apply, mul_comm (δ _ _)]
    rw [h1]
    simp [Finsupp.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem det_mem_maximalIdeal (k A : Type) [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A] {N : ℕ}
    (g : Fin N → A) (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (t : A) (ht : t ∈ maximalIdeal A)
    (hd : KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]))
    (hδ : ∀ j, δ j t ∈ Ideal.span {t}) : (Matrix.of fun i j => δ j (g i)).det ∈ maximalIdeal A := by
  classical
  set c : Fin N → A := fun i => bΩ.repr (KaehlerDifferential.D k A t) i with hc
  have hsum : KaehlerDifferential.D k A t = ∑ i, c i • bΩ i := (bΩ.sum_repr _).symm
  have hne : (fun i => residue A (c i)) ≠ 0 := by
    intro h0
    apply hd
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (residue_eq_zero_iff _).1 (congrFun h0 i)
  rw [← residue_eq_zero_iff, RingHom.map_det]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne, ?_⟩
  funext j
  have h1 : δ j t = ∑ i, c i * δ j (g i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (δ j).liftKaehlerDifferential_comp_D t, hsum, map_sum]
    simp [hg]
  have h2 : residue A (δ j t) = 0 :=
    (residue_eq_zero_iff _).2 ((Ideal.span_singleton_le_iff_mem _).2 ht (hδ j))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum] at h2
  simpa [Matrix.vecMul, dotProduct] using h2

theorem derivation_mem_span_of_prod {k A : Type} [CommRing k] [CommRing A] [IsRegularLocalRing A] [Algebra k A] {n : ℕ}
    (f : Fin n → A) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp A n f) (J : Finset (Fin n)) {j : Fin n} (hj : j ∈ J)
    (δ : Derivation k A A) (hδ : δ (∏ i ∈ J, f i) ∈ Ideal.span {∏ i ∈ J, f i}) : δ (f j) ∈ Ideal.span {f j} := by
  classical
  have hD : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params f hf.1 hf.2
  rw [Ideal.mem_span_singleton] at hδ ⊢
  rw [← Finset.mul_prod_erase J f hj, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hδ
  have h1 : f j ∣ (∏ i ∈ J.erase j, f i) * δ (f j) :=
    (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans hδ)
  refine ((hp j).dvd_or_dvd h1).resolve_left fun h2 => ?_
  obtain ⟨i, hi, h3⟩ := (hp j).exists_mem_finset_dvd h2
  exact (ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).2 j i (Finset.ne_of_mem_erase hi).symm
    ((hp j).associated_of_dvd (hp i) h3)

theorem D_notMem_smul_top {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (ResidueField A)] {t : A} (ht : t ∈ maximalIdeal A) (ht2 : t ∉ maximalIdeal A ^ 2) :
    KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]) := by
  intro hm
  have h := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := k) (fun _ : Unit => t) (fun _ => ht)
    (linearIndependent_unique_iff.2 (by
      intro h0
      exact ht2 ((Ideal.toCotangent_eq_zero _ _).1 h0)))
  refine h.ne_zero () ?_
  generalize KaehlerDifferential.D k A t = w at hm
  refine Submodule.smul_induction_on hm (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff _).2 hr, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

theorem derivation_mem_map {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (I : Ideal R) (d : R → R) (hd : ∀ r ∈ I, d r ∈ I) (δ : Derivation k A A) (hδ : ∀ r, δ (φ r) = φ (d r))
    {a : A} (ha : a ∈ I.map φ) : δ a ∈ I.map φ := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hδ]
    exact Ideal.mem_map_of_mem _ (hd r hr)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

theorem exists_boundary_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∉ (j₀ TF.Y Z).opensRange → ∃ t ∈ IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x), KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) t ∉ (IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x)) • (⊤ : Submodule ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) ∧ ∀ j, δ j t ∈ Ideal.span {t} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx b δ hδ hn
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨hreg, n, f, J, hf, ⟨j, hj⟩, hI⟩ := _root_.GlobalTheory.LogKSDiv.boundary_germ_snc E H Dw l Xo c TF Z x U hx hn
  have hm : f j ∈ maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x) := hf.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  refine ⟨f j, hm, ?_, fun i => ?_⟩
  · obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.1 (X₀ TF.Y Z).isBasis_affineOpens (show x ∈ (⊤ : (X₀ TF.Y Z).Opens) from trivial)
    haveI := GlobalTheory.AdaptedFrame.formallySmooth_residueField (s₀ TF.Y Z) (n := Dw.dim) hV x hxV (by
      ext t
      change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) ⊤ t) =
        ((X₀ TF.Y Z).presheaf.germ V x hxV).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) V t)
      rw [← GlobalTheory.TopForm.resG_comp_algX (s₀ TF.Y Z) (le_top : V ≤ ⊤), RingHom.comp_apply, germ_resG])
    exact D_notMem_smul_top hm ((ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).1 j)
  · refine derivation_mem_span_of_prod f hf J hj (δ i) ?_
    rw [← hI]
    refine derivation_mem_map _ _ (b i).1 (b i).2.2 (δ i) (hδ i) ?_
    rw [hI]
    exact Ideal.subset_span rfl

theorem local_topPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → (barComp TF.Y Z).ι x ∈ U.1 → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((b j).1 r)) → ∀ (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hxU ρ hρ b D hD U' ω hω hx
  have h1 := chartRestr_eq_germ E H Dw l Xo c TF Z x U hU hxU ρ hρ
  obtain ⟨δ, hδK, hδR⟩ := GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension E H Dw l Xo c TF Z x U hU hxU ρ h1 (fun j => (b j).1) D hD
  obtain ⟨g, bΩ, u, hg, hu, hform⟩ := frame_eq_unit_smul_dForm E H Dw l Xo c TF Z x U' ω hω hx
  letI := (stalkAlg TF Z x).toAlgebra
  have key : topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω) =
      algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField
        (u * (Matrix.of fun i j => δ j (g i)).det) := by
    rw [hform, LinearMap.map_smul, topPair_dForm, smul_eq_mul, map_mul, RingHom.map_det]
    congr 2
    ext i j
    exact hδK j (g i)
  refine ⟨⟨_, key.symm⟩, fun hU' => ?_, fun hr => ?_⟩
  · by_contra hn
    obtain ⟨t, htm, htd, htδ⟩ := exists_boundary_param E H Dw l Xo c TF Z x U hxU b δ hδR hn
    have hz := det_mem_maximalIdeal c.F _ g bΩ hg δ t htm htd htδ
    refine (zeroAt_iff.1 ⟨_, Ideal.mul_mem_left _ u hz, key.symm⟩).2 hU'
  · have hs := GlobalTheory.T.span_logDer_germs' E H Dw l Xo c TF Z x U hU hxU b δ hδR hr
    exact ⟨_, hu.mul (isUnit_det_of_span_eq_top c.F _ g bΩ hg δ hs), key.symm⟩

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem elementary_binom_bound : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  intro c k h d hk hh hcd
  have hhk : 0 < h ^ k := pow_pos hh k
  set a : ℚ := (c : ℚ) * ((k : ℚ) / h) ^ k with ha
  have had : a < d := by
    rw [ha, div_pow, ← mul_div_assoc, div_lt_iff₀ hhk]; linarith
  refine ⟨(a + d) / 2, by linarith, ?_⟩
  intro l₀
  have hlim : Tendsto (fun l : ℕ => (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) atTop
      (nhds ((c : ℚ) * ((k : ℚ) / h + 0) ^ k)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (k : ℚ))).pow k).const_mul _
  rw [add_zero] at hlim
  have hev1 : ∀ᶠ l : ℕ in atTop, (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k < (a + d) / 2 :=
    hlim.eventually (gt_mem_nhds (by rw [← ha]; linarith))
  have hev2 : ∀ᶠ l : ℕ in atTop, h < (l : ℚ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop h)
  obtain ⟨l, hl1, hl2, hl0⟩ := (hev1.and (hev2.and (eventually_ge_atTop l₀))).exists
  have hlpos : (0 : ℚ) < l := lt_trans hh hl2
  set x : ℚ := (k : ℚ) * l / h with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨l, ⌊x⌋₊ + 1, hl0, by omega, ?_, hl2, ?_⟩
  · have := Nat.lt_floor_add_one x
    push_cast
    rw [hx, div_lt_iff₀ hh] at this
    linarith
  · have hfl : ((⌊x⌋₊ : ℕ) : ℚ) ≤ x := Nat.floor_le hx0
    have hcast : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) = (⌊x⌋₊ : ℚ) + k := by
      have : ⌊x⌋₊ + 1 + k - 1 = ⌊x⌋₊ + k := by omega
      rw [this]; push_cast; ring
    have hch : (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ) ≤ (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial :=
      Nat.choose_le_pow_div k _
    have hfact : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hbase : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ≤ (l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) := by
      rw [hcast, mul_add, hx]
      have e1 : (l : ℚ) * ((k : ℚ) / h) = (k : ℚ) * l / h := by ring
      have e2 : (l : ℚ) * ((k : ℚ) / l) = k := by field_simp
      rw [e1, e2]; linarith [hfl]
    have hpow : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k ≤ ((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have hlk : (0 : ℚ) < (l : ℚ) ^ k := pow_pos hlpos k
    push_cast
    calc (c : ℚ) * (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ)
        ≤ (c : ℚ) * ((((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ ≤ (c : ℚ) * (((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k / k.factorial) := by
          gcongr
      _ = ((c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) * (l : ℚ) ^ k / k.factorial := by
          rw [mul_pow]; ring
      _ < (a + d) / 2 * (l : ℚ) ^ k / k.factorial := by
          apply div_lt_div_of_pos_right _ hfact
          exact mul_lt_mul_of_pos_right hl1 hlk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PreUTheta

theorem exists_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  intro R _ _ _ D A G _ _ U τ g hE hnz hmul
  obtain ⟨z₀, hz₀, hn₀⟩ := hnz (closedPoint R)
  have hx : D.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.P.A).left z₀) = closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.P.A))).trans hz₀
  obtain ⟨y', hy'⟩ := GlobalTheory.ThetaUnit.exists_thick_pt le_rfl 0 D.P.A _ hx
  obtain ⟨y, rfl⟩ := (U.gt 0).q_surj.surj y'
  have hpG : (U.gt 0).pG.left y = (snd (𝟙_ (Over (Sp R))) D.P.A).left z₀ := hy'
  let rG : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ G).left :=
    (lift (toUnit _) (fstG (maximalIdeal R) 0 G)).left
  let rB : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ D.P.A).left :=
    (lift (toUnit _) (U.gt 0).pG).left
  have h₁ : rG ≫ (snd _ G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have h₂ : rB ≫ (snd _ D.P.A).left = (U.gt 0).pG.left := by
    rw [← Over.comp_left, lift_snd]
  have h₃ : rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hinj : ∀ a b : (𝟙_ (Over (Sp R)) ⊗ D.P.A).left,
      (snd (𝟙_ (Over (Sp R))) D.P.A).left a = (snd (𝟙_ (Over (Sp R))) D.P.A).left b → a = b := by
    intro a b hab
    have e := GlobalTheory.PsiExpansion.snd_lift_unit D.P.A
    have key : ∀ c, (lift (toUnit D.P.A) (𝟙 D.P.A)).left ((snd (𝟙_ (Over (Sp R))) D.P.A).left c) = c :=
      fun c => by rw [← Scheme.Hom.comp_apply, e]; rfl
    rw [← key a, ← key b, hab]
  have hrB : rB y = z₀ := hinj _ _ ((congrArg (fun q => q y) h₂).trans hpG)
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.P.isLB y
  obtain ⟨JG, hJG⟩ := GlobalTheory.ConstFam.exists_good' U.P.L.isLB y
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨H₁, H₂⟩ := hs _ (𝟙 _) rG rB (by rw [Category.id_comp]; exact h₁) (by rw [Category.id_comp]; exact h₂) h₃
    y JG J hJG hJ
  have hu : IsUnit (sval (g 0) rB y J) :=
    (GlobalTheory.Ex.OneGen.isUnit_sval_iff (g 0) rB y hJ).2 (by rw [hrB]; exact hn₀)
  have hc' : rB ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ spMap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
    Over.w (lift (toUnit _) (U.gt 0).pG)
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, h, hh⟩ := hmul α hα
    rw [GlobalTheory.IndivisibleSection.sval_of_secIsMul hh _ y hJ, hc', cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha), GlobalTheory.GermDiv.cst_zero, zero_mul, zero_mul])
    (fun h => absurd (H₁ 0 h) hu.ne_zero)] at H₂
  have hτ : IsUnit (sval τ rG y JG) :=
    isUnit_of_mul_isUnit_right (H₂ ▸ hu.mul (Units.isUnit _))
  obtain ⟨σ, hσ⟩ := GlobalTheory.PsiExpansion.exists_sameG U.P.L.isLB τ
  rw [hσ _ rG y JG hJG, h₁] at hτ
  have hm := (GlobalTheory.Ex.OneGen.isUnit_sval_iff σ _ y hJG).1 hτ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfH0 σ, _, GlobalTheory.ThetaClosed.nonzeroLocus_firstPower_section_subset σ hm, ?_⟩
  have hc : (fstG (maximalIdeal R) 0 G).left ≫ G.hom = (U.gt 0).pG.left ≫ D.P.A.hom :=
    (Over.w (fstG (maximalIdeal R) 0 G)).trans (Over.w (U.gt 0).pG).symm
  exact (congrArg (fun q => q y) hc).trans ((congrArg D.P.A.hom hpG).trans hx)

end GlobalTheory.PreUTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | exact GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | (intros; apply GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample <;> assumption)
end

