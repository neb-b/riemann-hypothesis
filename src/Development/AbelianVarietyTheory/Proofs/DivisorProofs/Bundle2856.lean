module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIffDegEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_field_over_trait : ∀ (R : Type) [CommRing R] [IsDomain R] (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F) (_ : Algebra (FractionRing W) F) (_ : Kb R →ₐ[FractionRing R] F), ∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r)) := by
  intro R _ _ W _ _ φ hφ
  let g : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := (IsFractionRing.lift (K := FractionRing R) hg).toAlgebra
  refine ⟨Kb W, inferInstance, inferInstance, inferInstance, inferInstance, IsAlgClosed.lift, fun r => ?_⟩
  exact IsFractionRing.lift_algebraMap hg r

theorem exists_map_exp_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  intro R _ _ _ hR D C j
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  have h1 : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  obtain ⟨wA, hwA⟩ := C.α_lb
  have hL : C.P.L.L.IsLB := by first | exact C.P.L.isLB | exact C.P.L.hL | exact C.P.L.lb
  have hL' : C.A.L.IsLB := C.A.isLB
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  · obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
    obtain ⟨K₀, _, _, _, _, em₀, hK₀⟩ := exists_field_over_trait R W₀ T₀.φ T₀.inj
    obtain ⟨lab, E, hlab, hE, -⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W₀ T₀ K₀ em₀ hK₀
    obtain ⟨Eb, hEb⟩ := GlobalTheory.Mum.Desc.eqv_down R hR D C.A (C.n ^ j) hodd (C.lab j) K₀ em₀ lab E hlab hE
    have hgal := GlobalTheory.Mum.labExt_of_trait R hR D C j W₀ ⟨T₀⟩
    obtain ⟨Φ₀, E₀, hE₀, hΦ₀⟩ := GlobalTheory.Mum.exists_eqv_rational R hR D C.A (C.n ^ j) hodd (C.lab j) Eb hEb hgal
    choose Φ hΦ using fun F₀ => _root_.GlobalTheory.Mum.exists_secK_of_iso_pull C.P.L.L C.A.L C.α wA hL hL' hwA (C.n ^ j) (Φ₀ F₀)
    refine ⟨Φ, fun W _ _ _ T => ?_⟩
    obtain ⟨K, _, _, _, _, em, hK⟩ := exists_field_over_trait R W T.φ T.inj
    obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure R hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W T K em hK
    exact GlobalTheory.T.traitExpansion_descends_from_algClosed_field R hR D C (C.n ^ j) W T K hK Φ c hc (fun F₀ => _root_.GlobalTheory.Mum.Trait.exists_expBy_one R hR D C (C.n ^ j) h1 W T F₀) hcv
  · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicRatCharPolyAbelianVariety
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.charPolyRat : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ) := by
  intro K _ A f
  obtain ⟨F, hF, hev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f.asHom]
  set N := 2 * A.dim with hN
  have hsupp : ∀ d ∈ F.support, d 0 + d 1 = N := by
    intro d hd
    by_contra h
    refine (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  let P : Polynomial ℚ := ∑ d ∈ F.support,
    Polynomial.C (AddMonoidAlgebra.coeff F d * (-1) ^ d 1) * Polynomial.X ^ d 0
  have hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F := by
    intro q
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Fin.prod_univ_two]
    ring
  have hcoef : P.coeff N = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp
    · intro d hd hne
      rw [ite_eq_right]
      intro h0
      apply hne
      have := hsupp d hd
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hdeg : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)
  have h10 : MvPolynomial.eval ![1, 0] F = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp [Fin.prod_univ_two]
    · intro d hd hne
      have := hsupp d hd
      have h1 : d 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i <;> simp <;> omega
      simp [Fin.prod_univ_two, h1]
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hone : MvPolynomial.eval ![1, 0] F = 1 := by
    have h := hev ![1, 0]
    have e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    have h2 := (GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2
    simp only [one_smul, Int.natAbs_one, one_pow] at h2
    simp [Fin.sum_univ_two, h2]
  have hnat : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg
    rw [hcoef, ← h10, hone]
    exact one_ne_zero
  refine ⟨P, ?_, hnat, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]
  · intro n
    rw [hPeval]
    have h := hev ![n, -1]
    have e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    congr 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul]
    rw [← zsmul_one (R := End A) n, End.sub_asHom, End.smul_asHom, End.one_asHom, sub_eq_add_neg]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_psi_val_eq_monomial_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ)
    (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ),
    (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1),
      ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
        Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  intro R _ _ _ Q m t gam hM χ n hn
  obtain ⟨u, n', hn', hc⟩ := hM χ
  obtain rfl : n = n' := funext fun i => by have := (hn' i).symm.trans (hn i); omega
  obtain ⟨j, hj, h, e⟩ := hc
  have hL := Q.P.isLB
  obtain ⟨e₀, he₀⟩ := exists_gen_of_local (V := R) Q.P.L hL (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun k => by cases k; exact hj hy
  have hx : Q.xK χ = jK R ≫ (Q.c χ).left := by simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let w : Γ(Spec (CommRingCat.of R), ⊤)ˣ :=
    Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u * (res le (e₀.s j))⁻¹
  let v : LB.Gen (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top w⟩
  have hv : v.IsGen := fun i i' => by
    obtain rfl : i = i' := funext fun k => k.elim
    have e' : (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
      dsimp only [LB.LinComb]
      erw [Fintype.prod_empty]
      rfl
    rw [e', _root_.one_mul]
  have hf : FormEq (Sum.elim (fun _ : PUnit => (Q.c χ).left) (PEmpty.elim : PEmpty.{1} → _))
      (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (PEmpty.elim : PEmpty.{1} → ℤ))
      (fun _ : PUnit => (Q.c χ).left) (fun _ => -1) := fun U _ g => by
    rw [Fintype.prod_sum_type]
    simp
  obtain ⟨ψ₀, hψ₀, vψ₀⟩ := exists_gen hL hf (LB.mulGen Q.P.L _ _ _ _ e₀ v)
    (mulGen_isGen _ _ _ _ _ _ _ he₀ hv)
  refine ⟨ψ₀, hψ₀, fun Z r z J hJ => ?_⟩
  rw [vψ₀ _ _ z J hJ, val_mul hJ]
  have m₁ : r z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j := h trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j := le trivial
  have e₁ : val (Q.psi χ) r z J = _ := gen_trans (Q.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e₀ (r ≫ jK R) z J = _ := gen_trans he₀ (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := Q.P.L) (K := PUnit) (fun _ => Q.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ Q.xK χ)) j =
      trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j := by
    have hq : r ≫ Q.xK χ = (r ≫ jK R) ≫ (Q.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j) ((Q.psi χ).s j)).val =
      cst (r ≫ jK R) z (u * ∏ i, t i ^ n i) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z h trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) e.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : val v (r ≫ jK R) z J = gm (r ≫ jK R) z ⊤ w := gm_res _ z _ (hJ.mem PEmpty.elim _) _
  have e₆ : (gm (r ≫ jK R) z ⊤ (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)).val = cst (r ≫ jK R) z u := by
    rw [← gs_unit _ z ⊤ trivial, Units.coe_map, cst, ← hto]; rfl
  have e₇ : ∀ a b : R, cst (r ≫ jK R) z (a * b) = cst (r ≫ jK R) z a * cst (r ≫ jK R) z b := fun a b => by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  have e₈ : gm (r ≫ jK R) z ⊤ (res le (e₀.s j)) =
      gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j) := gm_res _ z le trivial _
  have hg := Units.mul_inv (gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j))
  rw [e₁, e₂, e₅, Units.val_mul, Units.val_mul, e₄]
  erw [e₃]
  rw [map_mul, map_inv, e₈]
  simp only [Units.val_mul]
  rw [e₆, e₇]
  linear_combination (-((trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j).val * cst (r ≫ jK R) z u * cst (r ≫ jK R) z (∏ i, t i ^ n i))) * hg

end GlobalTheory.UnitPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseDeg
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.InvDegInverse

variable {K : Type} [Field K]

def invKer {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | ptMap f x = 1 ∧ ∃ k : ℕ, (k : K) ≠ 0 ∧ x ^ k = 1}
  one_mem' := ⟨map_one _, 1, by simp, one_pow _⟩
  mul_mem' := by
    rintro x y ⟨hx, a, ha, hxa⟩ ⟨hy, b, hb, hyb⟩
    refine ⟨by rw [map_mul, hx, hy, _root_.one_mul], a * b, by push_cast; exact mul_ne_zero ha hb, ?_⟩
    rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, a, ha, hxa⟩
    exact ⟨by rw [map_inv, hx, inv_one], a, ha, by rw [inv_pow, hxa, inv_one]⟩

theorem finite_invKer {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) : Finite (invKer f) := by
  have : Finite (ptMap f).ker := (GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A B f).1 hf.1
  exact Finite.of_injective (fun x : invKer f => (⟨x.1, x.2.1⟩ : (ptMap f).ker))
    (fun x y h => Subtype.ext (congrArg (fun z : (ptMap f).ker => (z : A.Pt)) h))

theorem card_invKer_ne_zero {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    ((Nat.card (invKer f) : ℕ) : K) ≠ 0 := by
  haveI := finite_invKer f hf
  intro h0
  have hpos : 0 < Nat.card (invKer f) := Nat.card_pos
  have hpd : ringChar K ∣ Nat.card (invKer f) := (ringChar.spec K _).1 h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hpp | hp0
  · haveI := Fact.mk hpp
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hpd
    obtain ⟨_, k, hk, hyk⟩ := y.2
    have : ringChar K ∣ k := by
      rw [← hy, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hyk
    exact hk ((ringChar.spec K k).2 this)
  · rw [hp0, zero_dvd_iff] at hpd
    omega

theorem galPts_mem_invKer {A B : AbVar K} (f : A ⟶ B) (σ : Gal K) (x : A.Pt) (hx : x ∈ invKer f) :
    galPts A.X σ x ∈ invKer f := by
  obtain ⟨h1, k, hk, hxk⟩ := hx
  refine ⟨?_, k, hk, by rw [← map_pow, hxk, map_one]⟩
  have e : ptMap f (galPts A.X σ x) = galPts B.X σ (ptMap f x) :=
    show (specAut σ ≫ x) ≫ f.hom = specAut σ ≫ (x ≫ f.hom) from Category.assoc _ _ _
  rw [e, h1, map_one]

end GlobalTheory.AV.AbVar.InvDegInverse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNeg
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Heat.ShiftGauge

theorem toUnit_left {R : Type} [CommRing R] (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem exists_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  intro R _ _ Q O _ _ _ oa Y mu x hx ψ₀ hψ₀
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hq : IsMonHom Y.q := Y.q_linear.isMonHom
  set Tx : Y.H ⟶ Y.H := 𝟙 Y.H * (toUnit Y.H ≫ x) with hTx

  have hTq : Tx ≫ Y.q = Y.q * (toUnit Y.H ≫ x ≫ Y.q) := by
    rw [hTx, MonObj.mul_comp, Category.id_comp, Category.assoc]
  have hcq : cP Q Y.H mu * (Tx ≫ Y.q) = Y.q := by
    rw [hTq, cP, _root_.mul_comm, _root_.mul_assoc, ← MonObj.comp_mul (toUnit Y.H) (x ≫ Y.q) (Q.c mu), hx,
      MonObj.comp_one, _root_.mul_one]
  have e₁ : (cP Q Y.H mu).left = Y.H.hom ≫ (Q.c mu).left := by rw [cP, Over.comp_left, toUnit_left]
  have e₂ : (1 : Y.H ⟶ Q.P.A).left = Y.H.hom ≫ eSec Q.P.A := by rw [Hom.one_def, Over.comp_left, toUnit_left]; rfl
  let s := (Y.Φ Y.H Tx).s mu
  let w := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ ψ₀ Y.H.hom)
    (LB.pullGen Q.P.L _ _ Q.rig Y.H.hom)) s
  have hw : w.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hψ₀ _)
    (pullGen_isGen _ _ _ _ Q.rig_gen _)) ((Y.Φ Y.H Tx).isGen mu)
  have hF : FormEq (Sum.elim (Sum.elim (fun _ : PUnit => Y.H.hom ≫ (Q.c mu).left)
      (fun _ : PUnit => Y.H.hom ≫ eSec Q.P.A)) (DegPre.gtφT Q Y.H (Y.Φ Y.H Tx).b mu))
      (fun k => - Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => (1 : ℤ))) DegPre.gtε k)
      (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] := by
    intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.prod_unique, Fin.prod_univ_two]
    rw [GlobalTheory.TorusModel.prod_pt, Ray.Φ_b, hcq, e₁, e₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  obtain ⟨e, he, hve⟩ := exists_gen hL hF (LB.invGen Q.P.L _ _ w) (invGen_isGen _ _ _ _ hw)
  have hval : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      val e y.left z J = (val ψ₀ T.hom z J * val Q.rig T.hom z J *
        val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J)⁻¹ := by
    intro T y z J hJ
    have hy : y ≫ Tx = y * (toUnit T ≫ x) := by
      rw [hTx, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit Y.H) (toUnit T)]
    have hp := ((GlobalTheory.TorusModel.isPull_iff y (Y.Φ Y.H Tx) (Y.Φ T (y ≫ Tx))).1 (Y.rep.1 T Y.H y Tx)).2 mu z J hJ
    rw [hve _ _ z J hJ, val_inv, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Over.w y, ← hy]
    rw [show val ((Y.Φ T (y ≫ Tx)).s mu) (𝟙 _) z J = _ from hp]
  refine ⟨e, he, ?_, fun T y z J hJ => ?_⟩
  · intro j V hV S _ φ x₁ x₁' c a a' ha ha' hV₁ hV₂ hqq hc
    subst ha ha'
    have hV' : Y.q.left ⁻¹ᵁ V ≤
        (LB.LinComb Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1]).U j := hV
    have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) → ∀ z,
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (valR b (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))) =
          gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
            (e.s j).val := by
      intro b hb z
      rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hV']
      refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z _ (hb trivial) _).trans ?_)
      rw [Category.id_comp]
      exact gs_res b z hV (hb trivial) _
    have hq' : x₁'.left ≫ Y.q.left = x₁.left ≫ Y.q.left := congrArg CommaMorphism.left hqq
    have hu : ∀ u : Over.mk (spMap φ) ⟶ Y.H, u ≫ Tx ≫ Y.q = (u ≫ Y.q) * (toUnit _ ≫ x ≫ Y.q) := fun u => by
      rw [hTq, MonObj.comp_mul, ← Category.assoc u (toUnit Y.H), toUnit_unique (u ≫ toUnit Y.H) (toUnit _)]
    have hT₀ : x₁' ≫ Tx ≫ Y.q = x₁ ≫ Tx ≫ Y.q := by rw [hu, hu, hqq]
    have hT : x₁'.left ≫ Tx.left ≫ Y.q.left = x₁.left ≫ Tx.left ≫ Y.q.left := congrArg CommaMorphism.left hT₀
    have hk : ∀ k, x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k =
        x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k :=
      Fin.forall_fin_two.2 ⟨hq', hT⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left => exists_chart hL (χ z)
    have hJ : Good Q.P.L z I := hI
    have hgv : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
        gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
          (e.s j).val = (trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] b z j
            (fun k => I (b ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) *
            val e b z I).val := fun b hb =>
      (gs_unit b z _ (hV (hb trivial)) _).trans (congrArg Units.val (gen_trans he b z (hV (hb trivial)) (hJ.mem _ b)))
    have htr : trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁'.left z j
          (fun k => I (x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) =
        trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁.left z j
          (fun k => I (x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) := by
      unfold trF
      exact Finset.prod_congr rfl fun k _ => congrArg (fun ψ => gm ψ z (Q.P.L.U (j k) ⊓ Q.P.L.U (I ψ)) (Q.P.L.g (j k) (I ψ)) ^ (![1, -1] : Fin 2 → ℤ) k) (hk k)
    have ve : val e x₁'.left z I = gm (𝟙 (Over.mk (spMap φ)).left) z ⊤ (unitOn (c (-mu))) * val e x₁.left z I := by
      have hb : (Y.Φ _ x₁').b = (Y.Φ _ x₁).b := by rw [Ray.Φ_b, Ray.Φ_b, hqq]
      have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ (toUnit _ ≫ x))).2 mu z I hJ
      have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' (toUnit _ ≫ x))).2 mu z I hJ
      rw [hb] at h2
      have h3 := hc mu z I hJ
      have h4 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁) hJ mu (-mu)
      have h5 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁') hJ mu (-mu)
      rw [add_neg_cancel, GlobalTheory.TorusModel.cv_zero _ hJ] at h4 h5
      rw [hb] at h5
      have h6 := hc (-mu) z I hJ
      rw [hval _ x₁ z I hJ, hval _ x₁' z I hJ]
      apply Additive.ofMul.injective
      have g1 := congrArg Additive.ofMul h1
      have g2 := congrArg Additive.ofMul h2
      have g3 := congrArg Additive.ofMul h3
      have g4 := congrArg Additive.ofMul h4
      have g5 := congrArg Additive.ofMul h5
      have g6 := congrArg Additive.ofMul h6
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at g1 g2 g3 g4 g5 g6 ⊢
      linear_combination (norm := abel) g1 - g2 - g4 + g5 + g6
    show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
    rw [germ _ hV₂ z, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, hgv _ hV₂, hgv _ hV₁, htr, ve,
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c (-mu) : S) = (unitOn (c (-mu))).val from rfl,
      gs_unit (𝟙 _) z ⊤ trivial, ← Units.val_mul]
    exact congrArg Units.val (_root_.mul_left_comm _ _ _)
  · rw [hval T y z J hJ]
    simp only [_root_.mul_assoc, inv_mul_cancel]

end GlobalTheory.Heat.ShiftGauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockIpSelfRePos
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem fockIp_self_re_pos {ι : Type} {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    0 < (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp p p).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun k hk => ?_) (MvPolynomial.support_nonempty.2 hp)
  rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hk)) ?_
  exact Nat.cast_pos.2 (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

theorem fockSum_ne_zero : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ), a ≤ d → fockSum D a d n ≠ 0 := by
  intro D a d n had h0
  have hpos : 0 < (fockSum D a d n).re := by
    unfold fockSum
    rw [Complex.re_sum]
    haveI : Nonempty (GlobalTheory.NormSum.Tup D a d n) := ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩⟩
    exact Finset.sum_pos (fun T _ => fockIp_self_re_pos (GlobalTheory.NormAdelic.minorPol_ne_zero T)) (by
      classical exact ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩, by simp⟩)
  rw [h0] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.NormRatio
end
end

