module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0013
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaSmith
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section lattice

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem exists_smith_basis (hv : v.Integers R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Submodule R (ι → R)) (hL : L.FG) :
    ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧
      L = Submodule.span R (Set.range fun j => ε j • Λ j) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A : Matrix (Fin (Fintype.card ι)) (Fin m) R := Matrix.of fun i k => g k (e.symm i)
  obtain ⟨P, Q, a, hP, hQ, hD⟩ :=
    ReciprocityTheory.PGsh.Up.Smith.smith_mat (v := v) hv (Fintype.card ι) m A
  have hPv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hQv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hAQ : A * Q = P⁻¹ * (P * A * Q) := by
    simp only [← Matrix.mul_assoc, hPv, Matrix.one_mul]
  have hA : A = P⁻¹ * (P * A * Q) * Q⁻¹ := by
    rw [← hAQ, Matrix.mul_assoc, hQv, Matrix.mul_one]
  let Λ : Matrix ι ι R := Matrix.of fun j i => P⁻¹ (e i) (e j)
  let ε : ι → R := fun j => if (e j : ℕ) < m then a (e j) else 0
  have hΛ : Λ = ((P⁻¹).submatrix e e)ᵀ := by
    ext j i; rfl
  have hdet : IsUnit Λ.det := by
    rw [hΛ, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 hP
  refine ⟨Λ, ε, hdet, le_antisymm ?_ ?_⟩
  · rw [← hg, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hgl : g l = ∑ k : Fin m, ∑ j : Fin (Fintype.card ι),
        (Q⁻¹ k l * (P * A * Q) j k) • Λ (e.symm j) := by
      ext i
      have h1 : A (e i) l = (P⁻¹ * (P * A * Q) * Q⁻¹) (e i) l := by rw [← hA]
      have h2 : A (e i) l = g l i := by simp [A]
      rw [← h2, h1, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply (M := P⁻¹)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Λ, Matrix.of_apply, Equiv.apply_symm_apply]
      ring
    rw [SetLike.mem_coe, hgl]
    refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => ?_
    rw [hD j k]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : ((e (e.symm j)) : ℕ) < m := by
        rw [Equiv.apply_symm_apply, ← hkj]; exact k.2
      have hε : ε (e.symm j) = a j := by
        simp only [ε, if_pos hj, Equiv.apply_symm_apply]
      rw [if_pos hkj, mul_smul, ← hε]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm j, rfl⟩)
    · rw [if_neg hkj, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ε j • Λ j ∈ L
    by_cases hj : (e j : ℕ) < m
    · have hsum : ε j • Λ j = ∑ l : Fin m, Q l ⟨e j, hj⟩ • g l := by
        ext i
        have h1 : (A * Q) (e i) ⟨e j, hj⟩ = (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ := by rw [← hAQ]
        have h2 : (A * Q) (e i) ⟨e j, hj⟩ = ∑ l, Q l ⟨e j, hj⟩ * g l i := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [A, mul_comm]
        have h3 : (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ = a (e j) * P⁻¹ (e i) (e j) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
          · rw [hD]; simp [mul_comm]
          · intro b _ hb
            rw [hD, if_neg, mul_zero]
            intro h
            exact hb (Fin.ext h.symm)
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← h2, h1, h3]
        simp only [ε, if_pos hj, Λ, Matrix.of_apply]
      rw [hsum, ← hg]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · have : ε j = 0 := if_neg hj
      rw [this, zero_smul]
      exact Submodule.zero_mem _

noncomputable def rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (h : IsUnit Λ.det) :
    (ι → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear Λ) (Matrix.vecMulLinear Λ⁻¹)
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h])
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ h])

theorem rowEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (x : ι → R) : rowEquiv Λ h x = ∑ j, x j • Λ j := by
  show x ᵥ* Λ = _
  rw [Matrix.vecMul_eq_sum]

theorem map_rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) :
    (Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)).map
        (rowEquiv Λ h : (ι → R) →ₗ[R] (ι → R)) =
      Submodule.span R (Set.range fun j => ε j • Λ j) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    show rowEquiv Λ h x ∈ _
    rw [rowEquiv_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hx j (Set.mem_univ j))
    rw [← hr, mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j (ε j), ?_, ?_⟩
    · intro k _
      by_cases hk : k = j
      · subst hk
        simpa using Ideal.mem_span_singleton_self (ε k)
      · simp [Pi.single_eq_of_ne hk]
    · show rowEquiv Λ h _ = _
      rw [rowEquiv_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ _) hj

theorem dvd_of_smul_row_mem {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) (c : R) (j : ι)
    (hc : c • Λ j ∈ Submodule.span R (Set.range fun j => ε j • Λ j)) : ε j ∣ c := by
  rw [← map_rowEquiv Λ h ε] at hc
  obtain ⟨x, hx, hxe⟩ := hc
  have hx' : x = Pi.single j c := by
    apply (rowEquiv Λ h).injective
    have : rowEquiv Λ h x = c • Λ j := hxe
    rw [this, rowEquiv_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ _) hj
  have := hx j (Set.mem_univ j)
  rw [hx', Pi.single_eq_same] at this
  exact Ideal.mem_span_singleton.1 this

theorem hasLen_quot_rows {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) {M : Type} [AddCommGroup M] [Module R M]
    (E : M ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j))) :
    HasLen v R M (∏ j, v (algebraMap R C (ε j))) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T : Submodule R (ι → R) := Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)
  have E1 : ((ι → R) ⧸ T) ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j)) :=
    Submodule.Quotient.equiv T _ (rowEquiv Λ h) (map_rowEquiv Λ h ε)
  have E2 : ((ι → R) ⧸ T) ≃ₗ[R] ((j : ι) → R ⧸ Ideal.span {ε j}) :=
    Submodule.quotientPi fun j => (Ideal.span {ε j} : Submodule R R)
  have E3 := LinearEquiv.piCongrLeft R (fun j : ι => R ⧸ Ideal.span {ε j}) e.symm
  refine ⟨Fintype.card ι, fun i => ε (e.symm i), ⟨((E.trans E1.symm).trans E2).trans E3.symm⟩, ?_⟩
  exact Equiv.prod_comp e.symm fun j => v (algebraMap R C (ε j))

end lattice

theorem smith_of (hfg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG)
    (hquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  have hp1 : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨-, -, cp, hcp, -, -⟩ := cpaf p C v R hv hp (ι → ZMod p) AA 0
  have hcoord : ∀ i, (Pi.single i cp : ι → R) ∈ afLat p AA.carrier := by
    intro i
    obtain ⟨g, hg, c, hc, -, h⟩ :=
      cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    have hvc : v (algebraMap R C cp) = v (algebraMap R C c) :=
      (pow_left_inj₀ zero_le zero_le hp1).1 (hcp.trans hc.symm)
    obtain ⟨u, hu⟩ : c ∣ cp := hv.dvd_of_le hvc.le
    have hmem : (Pi.single i c : ι → R) ∈ afLat p AA.carrier := by
      refine ⟨g, (Submodule.mem_inf.1 hg).1, fun x => ?_⟩
      have hs : ∑ k, (Pi.single i c : ι → R) k * ((x k).val : R) = c * ((x i).val : R) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hi; exact absurd (Finset.mem_univ _) hi
      rw [hs, map_mul, map_natCast]
      exact (h x).1
    have : (Pi.single i cp : ι → R) = u • (Pi.single i c : ι → R) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [hu, mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  have hscale : ∀ l : ι → R, cp • l ∈ afLat p AA.carrier := by
    intro l
    have : cp • l = ∑ i, l i • (Pi.single i cp : ι → R) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcoord i)
  obtain ⟨Λ, ε, hdet, hL⟩ := exists_smith_basis hv _ (hfg p C v R hv hp ι AA)
  refine ⟨Λ, ε, hdet, hL, fun j => ?_, ?_⟩
  · have hd : ε j ∣ cp := dvd_of_smul_row_mem Λ hdet ε cp j (hL ▸ hscale (Λ j))
    obtain ⟨t, ht⟩ := hd
    have hle : v (algebraMap R C cp) ≤ v (algebraMap R C (ε j)) := by
      rw [ht, map_mul, map_mul]
      exact mul_le_of_le_one_right' (hv.map_le_one t)
    rw [← hcp]
    exact pow_le_pow_left₀ zero_le hle _
  · obtain ⟨E⟩ := hquot p C v R hv hp ι AA
    exact hasLen_quot_rows Λ hdet ε (E.trans (Submodule.quotEquivOfEq _ _ hL))

end PositivityTheory.HtPt.Ra
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RgProd
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Rg

open scoped TensorProduct

section
variable {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']

theorem lift_mul' {X : Over (Spec (CommRingCat.of R))} (a b : X ⟶ G) (a' b' : X ⟶ G') :
    lift (a * b) (a' * b') = lift a a' * lift b b' := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [MonObj.mul_comp]
  · simp [MonObj.mul_comp]

theorem pow_eq_one_iff' {X : Over (Spec (CommRingCat.of R))} (z : X ⟶ G ⊗ G') (p : ℕ) :
    z ^ p = 1 ↔ (z ≫ fst G G') ^ p = 1 ∧ (z ≫ snd G G') ^ p = 1 := by
  have key : z ^ p = lift ((z ≫ fst G G') ^ p) ((z ≫ snd G G') ^ p) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.pow_comp]
  have one : (1 : X ⟶ G ⊗ G') = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]
  rw [key, one]
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· ≫ fst G G') h, by simpa using congrArg (· ≫ snd G G') h⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem lift_right {A B S : Type} [CommRing A] [CommRing B] [CommRing S] [Algebra R A] [Algebra R B]
    [Algebra R S] (f : A →ₐ[R] S) (g : B →ₐ[R] S) (h : ∀ x y, Commute (f x) (g y)) :
    (Algebra.TensorProduct.lift f g h).comp Algebra.TensorProduct.includeRight = g :=
  Algebra.TensorProduct.lift_comp_includeRight f g h

variable {p : ℕ}

def prodPt (T : TorsRep G p) (T' : TorsRep G' p) : sp (R₀ := R) (T.A ⊗[R] T'.A) ⟶ G ⊗ G' :=
  lift (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] T.A ⊗[R] T'.A) ≫ T.y)
    (spMap (Algebra.TensorProduct.includeRight : T'.A →ₐ[R] T.A ⊗[R] T'.A) ≫ T'.y)

theorem prodPt_iff (T : TorsRep G p) (T' : TorsRep G' p) {S : Type} [CommRing S] [Algebra R S]
    (φ : T.A ⊗[R] T'.A →ₐ[R] S) (z : sp (R₀ := R) S ⟶ G ⊗ G') :
    spMap φ ≫ prodPt T T' = z ↔
      spMap (φ.comp Algebra.TensorProduct.includeLeft) ≫ T.y = z ≫ fst G G' ∧
      spMap (φ.comp Algebra.TensorProduct.includeRight) ≫ T'.y = z ≫ snd G G' := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [prodPt, Category.assoc, lift_fst, ← Category.assoc, Chart.spMap_comp]
    · rw [prodPt, Category.assoc, lift_snd, ← Category.assoc, Chart.spMap_comp]
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [prodPt, Category.assoc, lift_fst, ← Category.assoc, Chart.spMap_comp, h1]
    · rw [prodPt, Category.assoc, lift_snd, ← Category.assoc, Chart.spMap_comp, h2]

def prodRep (T : TorsRep G p) (T' : TorsRep G' p) : TorsRep (G ⊗ G') p where
  A := T.A ⊗[R] T'.A
  free := by
    have := T.free
    have := T'.free
    infer_instance
  fin := by
    have := T.fin
    have := T'.fin
    infer_instance
  y := prodPt T T'
  y_p := by
    rw [pow_eq_one_iff', prodPt, lift_fst, lift_snd, ← MonObj.comp_pow, ← MonObj.comp_pow, T.y_p, T'.y_p]
    exact ⟨MonObj.comp_one _, MonObj.comp_one _⟩
  univ := by
    intro S _ _ z hz
    rw [pow_eq_one_iff'] at hz
    obtain ⟨φ, hφ, uφ⟩ := T.univ S _ hz.1
    obtain ⟨ψ, hψ, uψ⟩ := T'.univ S _ hz.2
    refine ⟨Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _, ?_, ?_⟩
    · show _ ≫ _ = _
      rw [prodPt_iff, Algebra.TensorProduct.lift_comp_includeLeft, lift_right]
      exact ⟨hφ, hψ⟩
    · intro χ hχ
      obtain ⟨h, h'⟩ := (prodPt_iff T T' χ z).1 hχ
      apply Algebra.TensorProduct.ext
      · rw [Algebra.TensorProduct.lift_comp_includeLeft]
        exact uφ _ h
      · exact (uψ _ h').trans (Algebra.TensorProduct.lift_comp_includeRight _ _ _).symm

theorem isTorsPts_prod {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {pt : N → (sp (R₀ := R) R ⟶ G)} {pt' : N' → (sp (R₀ := R) R ⟶ G')}
    (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') :
    IsTorsPts (G ⊗ G') p (fun z : N × N' => lift (pt z.1) (pt' z.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, a'⟩ ⟨b, b'⟩ e
    have e1 := congrArg (· ≫ fst G G') e
    have e2 := congrArg (· ≫ snd G G') e
    simp only [lift_fst, lift_snd] at e1 e2
    exact Prod.ext (h.inj e1) (h'.inj e2)
  · rintro ⟨a, a'⟩ ⟨b, b'⟩
    simp only [Prod.fst_add, Prod.snd_add, h.add, h'.add]
    exact lift_mul' _ _ _ _
  · intro z
    rw [pow_eq_one_iff', h.range, h'.range]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨(a, b), ?_⟩
      apply CartesianMonoidalCategory.hom_ext <;> simp [ha, hb]
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨⟨a, by simp⟩, ⟨b, by simp⟩⟩

theorem exists_ev (T : TorsRep G p) {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h : IsTorsPts G p pt) : ∃ e : N → (T.A →ₐ[R] R), (∀ x, spMap (e x) ≫ T.y = pt x) ∧
      ∀ x φ, spMap φ ≫ T.y = pt x → φ = e x := by
  choose e he ue using fun x => T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)
  exact ⟨e, he, ue⟩

theorem mem_torsFun_iff {C : Type} [Field C] [Algebra R C] (T : TorsRep G p) {N : Type}
    {pt : N → (sp (R₀ := R) R ⟶ G)} {e : N → (T.A →ₐ[R] R)} (he : ∀ x, spMap (e x) ≫ T.y = pt x)
    (ue : ∀ x φ, spMap φ ≫ T.y = pt x → φ = e x) (f : N → C) :
    f ∈ torsFun C T pt ↔ ∃ a : T.A, f = fun x => algebraMap R C (e x a) := by
  show (∃ a : T.A, ∀ x φ, spMap φ ≫ T.y = pt x → f x = algebraMap R C (φ a)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x (e x) (he x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x φ hφ => ?_⟩
    rw [ue x φ hφ]

theorem torsFun_prod (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) (T' : TorsRep G' p)
    {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {pt : N → (sp (R₀ := R) R ⟶ G)} {pt' : N' → (sp (R₀ := R) R ⟶ G')}
    (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') :
    torsFun C (prodRep T T') (fun z : N × N' => lift (pt z.1) (pt' z.2)) =
      tens (torsFun C T pt) (torsFun C T' pt') := by
  obtain ⟨e, he, ue⟩ := exists_ev T h
  obtain ⟨e', he', ue'⟩ := exists_ev T' h'
  let E : N × N' → (T.A ⊗[R] T'.A →ₐ[R] R) := fun z =>
    Algebra.TensorProduct.lift (e z.1) (e' z.2) (fun _ _ => Commute.all _ _)
  have hE : ∀ z, spMap (E z) ≫ (prodRep T T').y = lift (pt z.1) (pt' z.2) := by
    intro z
    show spMap (E z) ≫ prodPt T T' = _
    rw [prodPt_iff]
    refine ⟨?_, ?_⟩
    · simp only [E]
      rw [Algebra.TensorProduct.lift_comp_includeLeft, he, lift_fst]
    · simp only [E]
      rw [lift_right, he', lift_snd]
  have uE : ∀ z (φ : T.A ⊗[R] T'.A →ₐ[R] R), spMap φ ≫ (prodRep T T').y = lift (pt z.1) (pt' z.2) →
      φ = E z := by
    intro z φ hφ
    obtain ⟨h1, h2⟩ := (prodPt_iff T T' φ _).1 hφ
    rw [lift_fst] at h1
    rw [lift_snd] at h2
    apply Algebra.TensorProduct.ext
    · simp only [E]
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
      exact ue _ _ h1
    · exact (ue' _ _ h2).trans (lift_right (e z.1) (e' z.2) (fun _ _ => Commute.all _ _)).symm
  have hS := mem_torsFun_iff (C := C) T he ue
  have hS' := mem_torsFun_iff (C := C) T' he' ue'
  have hP := mem_torsFun_iff (C := C) (prodRep T T') hE uE
  have hten : ∀ (z : N × N') (a : T.A) (b : T'.A),
      algebraMap R C (E z (a ⊗ₜ[R] b)) = algebraMap R C (e z.1 a) * algebraMap R C (e' z.2 b) := by
    intro z a b
    simp [E]
  have aux : ∀ t : T.A ⊗[R] T'.A,
      (fun z : N × N' => algebraMap R C (E z t)) ∈ tens (torsFun C T pt) (torsFun C T' pt') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      have h0 : (fun z : N × N' => algebraMap R C (E z 0)) = 0 := by
        funext z
        simp
      rw [h0]
      exact zero_mem _
    | tmul a b =>
      apply Submodule.subset_span
      refine ⟨fun x => algebraMap R C (e x a), (hS _).2 ⟨a, rfl⟩,
        fun x => algebraMap R C (e' x b), (hS' _).2 ⟨b, rfl⟩, ?_⟩
      funext z
      exact hten z a b
    | add s t hs ht =>
      have h2 : (fun z : N × N' => algebraMap R C (E z (s + t))) =
          (fun z => algebraMap R C (E z s)) + (fun z => algebraMap R C (E z t)) := by
        funext z
        simp
      rw [h2]
      exact add_mem hs ht
  apply le_antisymm
  · intro f hf
    obtain ⟨t, rfl⟩ := (hP f).1 hf
    exact aux t
  · unfold tens
    rw [Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    obtain ⟨a, rfl⟩ := (hS g).1 hg
    obtain ⟨b, rfl⟩ := (hS' k).1 hk
    exact (hP _).2 ⟨(a ⊗ₜ[R] b : T.A ⊗[R] T'.A), funext fun z => (hten z a b).symm⟩

end

end PositivityTheory.HtPt.Rg
end
end

