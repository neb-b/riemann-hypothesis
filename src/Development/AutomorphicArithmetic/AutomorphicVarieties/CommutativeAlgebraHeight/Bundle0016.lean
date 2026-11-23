module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FLimit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DQuotDet
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_quotDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], D.IsCont (maximalIdeal A) → ∀ Z : Set (MonoidAlgebra A G), (∀ z ∈ Z, D.Kills z) → ∃ DE : Det n A (D.CHQuot Z), DE.IsCH ∧ DE.pull (D.toQuot Z) = D.toDet := by
  intro n A G _ _ _ _ D _ _ _ _ hc Z hZ
  set f := D.toQuot Z
  have hsurj : Function.Surjective f := RingCon.mkₐ_surjective _
  have hmem : ∀ x, x ∈ D.chBar Z → f x = 0 := by
    intro x hx
    have hr : (D.chBar Z).ringCon x 0 := (TwoSidedIdeal.rel_iff _ _ _).2 (by rwa [sub_zero])
    rw [← map_zero f]
    exact (RingCon.eq _).2 hr
  have hker : ∀ x, f x = 0 → x ∈ D.chBar Z := by
    intro x hx
    rw [← map_zero f] at hx
    have hr := (RingCon.eq _).1 hx
    simpa using (TwoSidedIdeal.rel_iff _ _ _).1 hr
  have hle : TwoSidedIdeal.span (D.CH ∪ Z) ≤ D.chBar Z := by
    unfold GDet.chBar closureIdeal
    refine le_iInf fun N => le_iInf fun H => fun y hy => ?_
    exact TwoSidedIdeal.mem_span_iff.1 hy _ fun z hz =>
      TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) (Or.inl (Or.inl hz))
  have hsub : D.CH ∪ Z ⊆ D.chBar Z := fun x hx =>
    hle (TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hx)
  have hCHk : ∀ z ∈ D.CH, D.Kills z := by
    intro z hz
    have hz' : z ∈ D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hz
    exact (d_toDet D z).2.2.2.1 ((d_ker _ z).1.1 (d_ch_ker _ hz'))
  have hK : ∀ x, f x = 0 → x ∈ D.toDet.ker := fun x hx =>
    (d_ker _ x).1.2 ((d_toDet D x).2.2.2.2
      (d_closed D (maximalIdeal A) hc (D.CH ∪ Z)
        (by
          rintro z (hz | hz)
          exacts [hCHk z hz, hZ z hz]) x (hker x hx)))
  obtain ⟨DE, hDE, -⟩ := d_factor D.toDet f hsurj hK
  refine ⟨DE, ?_, hDE⟩
  show DE.CH = ⊥
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := ((d_pull DE f).2.2.2 hsurj).2 y hy
    rw [hDE, d_toDet_CH] at hx
    rw [hmem x ((TwoSidedIdeal.mem_span_iff.1 hx) _ fun z hz => hsub (Or.inl hz))]
    exact TwoSidedIdeal.zero_mem _
  · intro hy
    rw [TwoSidedIdeal.mem_bot] at hy
    rw [hy]
    exact TwoSidedIdeal.zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) (N : ℕ) (x : B.B), ∃ y ∈ Algebra.adjoin O ({a | ∃ (i : ℕ) (g : F.G₀), 1 ≤ i ∧ i ≤ n ∧ a = B.u.D.lam i (MonoidAlgebra.single g 1)} ∪ {a | ∃ v i g, a = ((B.u.ψ v i g : B.Bˣ) : B.B)}), x - y ∈ maximalIdeal B.B ^ N := by
  intro l _ F O _ _ _ _ _ _ _ n r B N x
  refine u_gen O B.B _ ?_ N x
  intro R' _ _ _ f f' h
  obtain ⟨p, hp⟩ := pair_map r B.u f
  refine (B.univ R' p).unique hp ⟨?_, fun v i => ?_⟩
  · rw [← hp.1]
    refine d_gext _ _ fun g i h1 h2 => ?_
    have e : ∀ φ : B.B →+* R', (B.u.D.map φ).lam i (MonoidAlgebra.single g 1) =
        φ (B.u.D.lam i (MonoidAlgebra.single g 1)) := fun φ => by
      have := ((d_gmap B.u.D).2.2.1 φ (MonoidAlgebra.single g 1)).2 i
      rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
    rw [e, e]
    exact (h _ (Or.inl ⟨i, g, h1, h2, rfl⟩)).symm
  · rw [← hp.2 v i]
    ext g
    exact (h _ (Or.inr ⟨v, i, g, rfl⟩)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsSemisimpleRepOfDetLawOfIsAlgClosed
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem det_bd {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (Matrix.blockDiagonal' d).det = ∏ k, (d k).det := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (Matrix.blockDiagonal' d).toSquareBlock Sigma.fst k =
      (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [Matrix.toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, Matrix.det_submatrix_equiv_self]

private theorem pull_pull {n : ℕ} {A E E' E'' : Type} [CommRing A] [Ring E] [Algebra A E] [Ring E'] [Algebra A E']
    [Ring E''] [Algebra A E''] (D : Det n A E) (f : E' →ₐ[A] E) (g : E'' →ₐ[A] E') :
    (D.pull f).pull g = D.pull (f.comp g) := by
  refine Det.ext' fun S _ _ x => ?_
  change D.D S (Algebra.TensorProduct.map (AlgHom.id S S) f (Algebra.TensorProduct.map (AlgHom.id S S) g x)) =
    D.D S (Algebra.TensorProduct.map (AlgHom.id S S) (f.comp g) x)
  congr 1
  induction x with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem pull_id {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) :
    D.pull (AlgHom.id A E) = D := by
  refine Det.ext' fun S _ _ x => ?_
  change D.D S (Algebra.TensorProduct.map (AlgHom.id S S) (AlgHom.id A E) x) = D.D S x
  simp

private theorem ofRep_comp {n : ℕ} {A E E' ι : Type} [CommRing A] [Ring E] [Algebra A E] [Ring E'] [Algebra A E']
    [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (g : E' →ₐ[A] E) :
    Det.ofRep h (r.comp g) = (Det.ofRep h r).pull g := by
  refine Det.ext' fun S _ _ x => ?_
  change (Det.repS (r.comp g) S x).det = (Det.repS r S (Algebra.TensorProduct.map (AlgHom.id S S) g x)).det
  congr 1
  induction x with
  | tmul s y => simp [Det.repS_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem ofRep_fin {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E]
    [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) :
    ∃ r' : E →ₐ[A] Matrix (Fin n) (Fin n) A, Det.ofRep (Fintype.card_fin n) r' = Det.ofRep h r := by
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq h
  refine ⟨(Matrix.reindexAlgEquiv A A e).toAlgHom.comp r, Det.ext' fun S _ _ x => ?_⟩
  change (Det.repS ((Matrix.reindexAlgEquiv A A e).toAlgHom.comp r) S x).det = (Det.repS r S x).det
  rw [← Matrix.det_submatrix_equiv_self e.symm (Det.repS r S x)]
  congr 1
  induction x with
  | tmul s y => ext a b; simp [Det.repS_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; rfl

private def bdRep {k ι κ : Type} [CommRing k] [Fintype κ] [DecidableEq κ] (m : ι → Type) [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (p : κ → ι) :
    (∀ i, Matrix (m i) (m i) k) →ₐ[k] Matrix (Σ j, m (p j)) (Σ j, m (p j)) k where
  toFun x := Matrix.blockDiagonal' fun j => x (p j)
  map_one' := Matrix.blockDiagonal'_one
  map_mul' x y := Matrix.blockDiagonal'_mul (fun j => x (p j)) (fun j => y (p j))
  map_zero' := Matrix.blockDiagonal'_zero
  map_add' x y := Matrix.blockDiagonal'_add (fun j => x (p j)) (fun j => y (p j))
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [← Matrix.blockDiagonal'_one, ← Matrix.blockDiagonal'_smul]
    rfl

private theorem bdRep_repS {k ι κ : Type} [CommRing k] [Fintype κ] [DecidableEq κ] (m : ι → Type)
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (p : κ → ι) (S : Type) [CommRing S] [Algebra k S]
    (y : S ⊗[k] (∀ i, Matrix (m i) (m i) k)) :
    Det.repS (bdRep m p) S y = Matrix.blockDiagonal' fun j => Det.repS (AlgHom.id k _) S
      (Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom k (fun i => Matrix (m i) (m i) k) (p j)) y) := by
  induction y with
  | tmul s x =>
    ext ⟨a, a'⟩ ⟨b, b'⟩
    by_cases hab : a = b
    · subst hab
      simp [Det.repS_tmul, bdRep]
    · simp [Det.repS_tmul, bdRep, Matrix.blockDiagonal'_apply_ne _ _ _ hab]
  | add a b ha hb =>
    simp only [map_add (f := _), ha, hb]
    rw [← Matrix.blockDiagonal'_add]
    rfl

private theorem pi_case {n N : ℕ} {k : Type} [Field k] (d : Fin N → ℕ)
    (D : Det n k (∀ i, Matrix (Fin (d i + 1)) (Fin (d i + 1)) k)) :
    ∃ r : (∀ i, Matrix (Fin (d i + 1)) (Fin (d i + 1)) k) →ₐ[k] Matrix (Fin n) (Fin n) k,
      Det.ofRep (Fintype.card_fin n) r = D := by
  obtain ⟨m, Ds, hm, hD⟩ := d_prod (fun i => Matrix (Fin (d i + 1)) (Fin (d i + 1)) k) D
  choose μ hμ hDs using fun i => d_matrix (Ds i)
  have hc : Fintype.card (Σ j : (Σ i, Fin (μ i)), Fin (d j.1 + 1)) = n := by
    rw [← hm, Fintype.card_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hμ i]
  obtain ⟨r, hr⟩ := ofRep_fin hc (bdRep (k := k) (fun i => Fin (d i + 1)) (fun j : (Σ i, Fin (μ i)) => j.1))
  refine ⟨r, hr.trans (Det.ext' fun S _ _ y => ?_)⟩
  rw [hD]
  change (Det.repS (bdRep (k := k) (fun i => Fin (d i + 1)) (fun j : (Σ i, Fin (μ i)) => j.1)) S y).det = _
  rw [bdRep_repS, det_bd, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine Eq.trans ?_ (hDs i S _).symm
  exact Fin.prod_const (M := S) (μ i) (Det.repS (AlgHom.id k _) S (Algebra.TensorProduct.map (AlgHom.id S S)
    (Pi.evalAlgHom k (fun i => Matrix (Fin (d i + 1)) (Fin (d i + 1)) k) i) y)).det

theorem UpperTheory.V.CA.exists_semisimple_rep_of_detLaw_of_isAlgClosed :
    ∀ {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] (D : Det n k E), ∃ r : E →ₐ[k] Matrix (Fin n) (Fin n) k, IsSemisimpleRing r.range ∧ Det.ofRep (Fintype.card_fin n) r = D := by
  intro n k E _ _ _ _ D
  let f : E →ₐ[k] D.ker.ringCon.Quotient := RingCon.mkₐ k D.ker.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ D.ker := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨D', hD', -⟩ := d_factor D f hf fun x => (hk x).1
  have hker : D'.ker = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨x, rfl⟩ := hf y
    have := (d_pull D' f).2.1 x hy
    rw [hD'] at this
    exact (TwoSidedIdeal.mem_bot _).2 ((hk x).2 this)
  obtain ⟨hfin, hss⟩ := d_faithful_ss D' hker
  obtain ⟨N, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k D.ker.ringCon.Quotient
  obtain ⟨d', rfl⟩ : ∃ d' : Fin N → ℕ, d = fun i => d' i + 1 :=
    ⟨fun i => d i - 1, funext fun i => by have := (hd i).out; dsimp only; omega⟩
  obtain ⟨r, hr⟩ := pi_case d' (D'.pull e.symm.toAlgHom)
  refine ⟨(r.comp e.toAlgHom).comp f, ?_, ?_⟩
  · have hrange : ((r.comp e.toAlgHom).comp f).range = (r.comp e.toAlgHom).range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [hrange]
    exact RingHom.isSemisimpleRing_of_surjective (r.comp e.toAlgHom).rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  · rw [ofRep_comp, ofRep_comp, hr, pull_pull D']
    have : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k _ := by
      ext x; simp
    rw [this, pull_id, hD']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.finE :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → ∀ Z : Set (MonoidAlgebra B G), (∃ s : Finset G, s.card ≤ finBound n h ∧ Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) = ⊤) ∧ Module.Finite B (D.CHQuot Z) ∧ ∀ N : ℕ, ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, D.toQuot Z (MonoidAlgebra.single u 1) - 1 ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z)) := by
  classical
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hm hmf Z
  obtain ⟨s, hs, hy, hU⟩ := f_limit (D.CH ∪ Z) (finBound n h) (fun U => by
    obtain ⟨s, hs, hy⟩ := f_level D χ hc hm hmf 1 U
    refine ⟨s, hs, fun y => ?_⟩
    obtain ⟨z, hz, hyz⟩ := hy y
    refine ⟨z, hz, ?_⟩
    apply TwoSidedIdeal.span_mono ?_ hyz
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx)
  have key : ∀ a b : MonoidAlgebra B G, a - b ∈ closureIdeal (maximalIdeal B) (D.CH ∪ Z) →
      D.toQuot Z a = D.toQuot Z b := by
    intro a b hab
    show RingCon.mkₐ B (D.chBar Z).ringCon a = RingCon.mkₐ B (D.chBar Z).ringCon b
    exact Quot.sound ((TwoSidedIdeal.rel_iff _ _ _).2 hab)
  have hspan : Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ : ∃ y, D.toQuot Z y = q := ⟨Quot.out q, Quot.out_eq q⟩
    obtain ⟨z, hz, hyz⟩ := hy y
    have himg : (fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G) =
        (D.toQuot Z).toLinearMap '' ((fun g => MonoidAlgebra.single g 1) '' (s : Set G)) := by
      rw [Set.image_image]
      rfl
    rw [himg, Submodule.span_image]
    exact ⟨z, hz, (key y z hyz).symm⟩
  refine ⟨⟨s, hs, hspan⟩, ⟨⟨s.image (fun g => D.toQuot Z (MonoidAlgebra.single g 1)), by
    rw [Finset.coe_image]
    exact hspan⟩⟩, ?_⟩
  intro N
  obtain ⟨U, hU'⟩ := hU N
  refine ⟨U, fun u hu => ?_⟩
  obtain ⟨z, hz, hz'⟩ := hU' u hu
  have heq : D.toQuot Z (MonoidAlgebra.single u 1) - 1 = D.toQuot Z z := by
    rw [← map_one (D.toQuot Z), ← map_sub]
    exact key _ _ hz'
  rw [heq]
  have hle : (maximalIdeal B ^ N) • (⊤ : Submodule B (MonoidAlgebra B G)) ≤
      ((maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z))).comap (D.toQuot Z).toLinearMap := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap]
    show D.toQuot Z (r • m) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  exact hle hz
end

