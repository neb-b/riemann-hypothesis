module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h a, gs_eq f z _ h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).symm

theorem formEq_famφB_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {Y : Scheme.{0}} (h : Y ⟶ D.P.A.left) :
    FormEq (fun i => h ≫ D.famφB 0 i) (DegPre.famε 1) (fun _ : Fin 1 => h) (fun _ => (1 : ℤ)) := by
  intro U _ hh
  have e0 : D.famφB 0 0 = 𝟙 _ := rfl
  have e1 : D.famφB 0 1 = 𝟙 _ := by
    show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
    rw [ThetaOne.c_zero, MonObj.comp_one]
    show ((𝟙 D.P.A) * 1).left = _
    rw [_root_.mul_one]; rfl
  have e2 : D.famφB 0 2 = D.famφB 0 3 := by
    show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
    rw [ThetaOne.c_zero, MonObj.comp_one]
    rfl
  simp only [Fin.prod_univ_four, Fin.prod_univ_one, e0, e1, e2]
  simp [DegPre.famε]

theorem exists_unitAt_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  intro V _ _ _ D θ hθ N hN hNV C b hb a
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  let r : Sp k ⟶ Sp V := Spec.map (CommRingCat.ofHom f)
  have hNk : (N : k) ≠ 0 := by
    have := (hNV.map f).ne_zero
    rwa [map_natCast] at this
  let θ' := ThetaOne.pullTo D f θ
  have hbasis := hθ k f θ' (ThetaOne.isPullSecLC_pullTo D f θ)
  obtain ⟨j₀, hj₀⟩ := ThetaOne.exists_ne_zero D f θ' hbasis
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB (formEq_famφB_zero D (snd (Over.mk r) D.P.A).left) θ'
  have hne : SecM.ofSec D.P.A (L := D.P.L) (a := 1) (T := Over.mk r) th ≠ 0 := by
    intro h0
    apply hj₀
    have hz : ∀ j, th.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j₀
    rw [← hth _ (𝟙 _) y J hJ]
    show gs _ y _ (th.f _) = gs _ y _ 0
    erw [hz]
    have gz : ∀ {Y : Scheme.{0}} (y : Y) (U : Y.Opens), gs (𝟙 Y) y U 0 = 0 := fun y U => by
      unfold gs; split_ifs <;> simp only [map_zero]
    exact (gz _ _).trans (gz _ _).symm
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P r hN hNk th hne
    (toUnit (Over.mk r) ≫ a)
  obtain ⟨c, hc⟩ := hb k r y hy
  refine ⟨c, ?_⟩
  have hmul : (toUnit (Over.mk r) ≫ a) * y = toUnit (Over.mk r) ≫ (a * b c) := by rw [hc, MonObj.comp_mul]
  rw [hmul] at hu
  let g := a * b c
  let q : Sp k := closedPoint k
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h1 := hu q J hJ
  have hρ : (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left ≫ (snd (Over.mk r) D.P.A).left = r ≫ g.left := by
    rw [← Over.comp_left, ptSecT, lift_snd, Over.comp_left]
    congr 1
  have hθ'e : θ' = H1.SectionArithmetic.pullSec θ (snd (Over.mk r) D.P.A).left :=
    SecOps.sec_ext fun j => ThetaOne.isPullSecLC_pullTo D f θ j
  have h2 : IsUnit (sval θ (r ≫ g.left) q J) := by
    have e := hth _ (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left q J hJ
    rw [← hρ, ← H1.SectionArithmetic.sval_pullSec θ _ _ q hJ, ← hθ'e, ← e]
    exact h1
  have hrq : r q = closedPoint V := by
    show (Spec.map (CommRingCat.ofHom f)).base (closedPoint k) = _
    rw [Spec.map_base]
    exact IsLocalRing.comap_closedPoint f
  refine ⟨fun σ => J (r ≫ σ), fun σ => ?_, ?_⟩
  · have := hJ (r ≫ σ)
    rwa [Scheme.Hom.comp_apply, hrq] at this
  · rw [sval_of θ (r ≫ g.left) q J (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) (fun i => by rw [Category.assoc])] at h2
    have hm : g.left (r q) ∈ (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U
        (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) :=
      show g.left (r q) ∈ LB.wchart D.P.L (D.famφB 0) (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) from Set.mem_iInter.2 fun i => by
        have := hJ (r ≫ g.left ≫ D.famφB 0 i)
        simpa [Scheme.Hom.comp_apply] using this
    have h2' : IsUnit ((r.stalkMap q).hom (gs g.left (r q) _ (θ.f (fun i => J (r ≫ g.left ≫ D.famφB 0 i))))) := by
      rw [← gs_comp_stalkMap r g.left q _ hm]; exact h2
    have h3 := isUnit_of_map_unit (r.stalkMap q).hom _ h2'
    rw [hrq] at h3
    exact h3

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.GraphPlace

section Gen

variable {K L F W : Type} [Field K] [Field L] [Field F] [Field W] [Algebra K L] [Algebra K F] [Algebra L W]
  [Algebra K W] [IsScalarTower K L W]


omit [Algebra K W] [IsScalarTower K L W] in
theorem indep_of_lift {ι : Type} (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) {x : ι → F}
    (hx : AlgebraicIndependent K x) : AlgebraicIndependent L fun i => ψ (1 ⊗ₜ x i) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) (MvPolynomial.aeval (R := K) x).toLinearMap
      (algebraicIndependent_iff_injective_aeval.1 hx)
  have e : (MvPolynomial.aeval (R := L) fun i => ψ (1 ⊗ₜ x i)) =
      (ψ.comp (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x))).comp
        (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.toAlgHom := by
    ext i
    simp
  rw [e]
  exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.injective

theorem trdeg_of_lift (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) (M : IntermediateField L W)
    (h1 : ∀ f, ψ (1 ⊗ₜ f) ∈ M) (h2 : M ≤ IntermediateField.adjoin L (Set.range fun f => ψ (1 ⊗ₜ f))) :
    Algebra.trdeg L M = Algebra.trdeg K F := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K F
  have hy := indep_of_lift ψ hψ hx.1
  rw [← hx.cardinalMk_eq_trdeg]
  apply le_antisymm
  · let E := IntermediateField.adjoin L (Set.range fun i => ψ (1 ⊗ₜ x i))
    let A := (algebraicClosure E W).restrictScalars L
    have hA : M ≤ A := by
      refine h2.trans (IntermediateField.adjoin_le_iff.2 ?_)
      rintro _ ⟨f, rfl⟩
      show ψ (1 ⊗ₜ f) ∈ algebraicClosure E W
      rw [mem_algebraicClosure_iff]
      let φ : F →ₐ[K] W := (ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight
      have hf : IsAlgebraic (Algebra.adjoin K (Set.range x)) f := hx.isAlgebraic.isAlgebraic f
      have hm : ∀ a ∈ Algebra.adjoin K (Set.range x), φ a ∈ E := by
        intro a ha
        have : Algebra.adjoin K (Set.range x) ≤ ((E.restrictScalars K).toSubalgebra).comap φ := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨i, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        exact this ha
      let g : Algebra.adjoin K (Set.range x) →+* E :=
        (φ.toRingHom.comp (Algebra.adjoin K (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
      have hg : Function.Injective g := fun a b h =>
        Subtype.ext (φ.toRingHom.injective (congrArg Subtype.val h))
      exact hf.ringHom_of_comp_eq g φ.toRingHom hg rfl
    have hE : Algebra.trdeg L E ≤ Cardinal.mk ι := by
      have : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E := by
        rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
        have htop : IntermediateField.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤ := by
          apply IntermediateField.lift_injective
          rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
          rfl
        rw [htop]
        infer_instance
      exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk L _ (alg := this)).trans Cardinal.mk_range_le
    calc Algebra.trdeg L M ≤ Algebra.trdeg L A :=
          trdeg_le_of_injective (IntermediateField.inclusion hA) (IntermediateField.inclusion_injective hA)
      _ = Algebra.trdeg L (algebraicClosure E W) := rfl
      _ = Algebra.trdeg L E := by
          haveI : FaithfulSMul E (algebraicClosure E W) :=
            (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E (algebraicClosure E W)).injective
          rw [← trdeg_add_eq L E (A := algebraicClosure E W), trdeg_eq_zero (R := E) (A := algebraicClosure E W), add_zero]
      _ ≤ _ := hE
  · have : AlgebraicIndependent L fun i => (⟨ψ (1 ⊗ₜ x i), h1 _⟩ : M) :=
      AlgebraicIndependent.of_comp M.val hy
    exact this.cardinalMk_le_trdeg

end Gen

theorem exists_trBasis {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
    [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
    [IsFractionRing (K ⊗[ℂ] κ') L] {n k' : ℕ} {x : Fin n → K} {τ' : Fin k' → κ'}
    (hx : TrBasis (algebraMap ℂ K) x) (hτ : TrBasis (algebraMap ℂ κ') τ') :
    ∃ w : Fin (k' + n) → L, TrBasis (algebraMap ℂ L) w := by
  have e1 : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e2 : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e3 : (algebraMap ℂ L).toAlgebra = (inferInstance : Algebra ℂ L) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at *
  rw [e1] at hx
  rw [e2] at hτ
  rw [e3]
  letI : Algebra K L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap K (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower K (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L,
      IsScalarTower.algebraMap_apply ℂ K (K ⊗[ℂ] κ')]
    rfl
  have h1 : Algebra.trdeg K L = Algebra.trdeg ℂ κ' := by
    let ψ := IsScalarTower.toAlgHom K (K ⊗[ℂ] κ') L
    rw [← trdeg_of_lift ψ (IsFractionRing.injective _ _) ⊤ (fun _ => trivial) ?_]
    · exact (IntermediateField.topEquiv (F := K) (E := L)).trdeg_eq.symm
    · intro z _
      have hm : ∀ a, ψ a ∈ IntermediateField.adjoin K (Set.range fun f => ψ (1 ⊗ₜ f)) := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem _
        | add a b ha hb => rw [map_add]; exact add_mem ha hb
        | tmul l f =>
          have : l ⊗ₜ[ℂ] f = l • ((1 : K) ⊗ₜ[ℂ] f) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul]
          exact IntermediateField.smul_mem _
            (IntermediateField.subset_adjoin K _ (Set.mem_range_self f))
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') z
      exact div_mem (hm a) (hm b)
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K L).injective
  have h2 := trdeg_add_eq ℂ K (A := L)
  rw [h1, ← hx.cardinalMk_eq_trdeg, ← hτ.cardinalMk_eq_trdeg] at h2
  obtain ⟨ι, w, hw⟩ := exists_isTranscendenceBasis' ℂ L
  have h3 : Cardinal.mk (Fin (k' + n)) = Cardinal.mk ι := by
    rw [hw.cardinalMk_eq_trdeg, ← h2]
    simp [add_comm]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  exact ⟨w ∘ e, hw.comp_equiv e⟩

theorem exists_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  IsLocModel (algebraMap ℂ K) R → Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ g : K, algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    (fun ω => @dite ℤ (∃ a, V.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hπ hR hinj hfr M hk _
  obtain ⟨Q, hQ, z, hm, hdim, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.localRing_graph_generic_point_of_injective (L := L) n k k' x τ' R π ρ hx hτ hz hc hπ hinj hfr hR hO hk
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w, hw⟩ := exists_trBasis (L := L) hx hτ
  obtain ⟨V, hV, hunit, -, hpow, hfo⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ r (k' + n) z (fun _ => 1)
    hm (by rw [hdim]; push_cast; rfl) rfl (fun _ => le_rfl) ⟨w, hw⟩
  have hne : ∀ q : Q, IsUnit q → (q : L) ≠ 0 := fun q hq => (hq.map Q.subtype).ne_zero
  refine ⟨V, fun g => ?_, fun b h => ?_, fun g h => ?_, fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · by_cases h : g = 0
    · subst h
      rw [TensorProduct.zero_tmul, map_zero]
      exact zero_mem _
    · obtain ⟨q, -, e⟩ := hg g h
      exact e ▸ hV _ q.2
  · obtain ⟨q, hq, e⟩ := hb b h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hg g h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hu l a b h
    exact e ▸ ⟨hne q hq, hunit q hq⟩
  · obtain ⟨q, e, hq⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    exact hpow M q h0 hq
  · have h := hfo y hy
    have hs : V.formOrd ((q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L))) =
        V.formOrd (dForm (algebraMap ℂ L) (fun i => (y i : L))) := by
      by_cases h0 : dForm (algebraMap ℂ L) (fun i => (y i : L)) = 0
      · rw [h0, smul_zero]
      · rw [V.formOrd_smul hw h0 (hne q hq), hunit q hq, zero_add]
    rw [hform]
    change V.formOrd ((q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L))) + 1 ≤ _
    rw [hs]
    simpa using h

end GlobalTheory.FieldPair.GraphPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.TraitLift

theorem exists_point_finite_ext {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (K : Type) [Field K] (y : Sp K ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap K L) ≫ y := by
  let P := pullback f y
  haveI : Nonempty (Sp K) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp K))
  obtain ⟨R, e, he, ⟨q, -⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := P) (x := p) (U := ⊤) trivial
  let g' : Spec R ⟶ Sp K := e ≫ pullback.snd f y
  haveI : LocallyOfFiniteType g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
    infer_instance
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  letI : Algebra K (R ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  haveI hft : Algebra.FiniteType K (R ⧸ I) :=
    RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨R ⧸ I, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing _ _,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ e ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_lift_of_proper {X Y : Scheme.{0}} (f : X ⟶ Y) [IsProper f] [Surjective f]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (hV : IsCN V) (y : Sp V ⟶ Y) :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ X),
      IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ f = spMap j ≫ y := by
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  obtain ⟨L, _, _, _, x, hx⟩ :=
    exists_point_finite_ext f (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ y)
  obtain ⟨V', _, _, _, hc, _, _, _, hcomp, -, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hv : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x ≫ f = spMap (algebraMap V' L) ≫ spMap (algebraMap V V') ≫ y := by
    rw [hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hcomp]
  let S : ValuativeCommSq f := { R := V', K := L, i₁ := x, i₂ := spMap (algebraMap V V') ≫ y, commSq := ⟨hsq⟩ }
  obtain ⟨l, -, hl⟩ := (hv S).some.default
  exact ⟨V', inferInstance, inferInstance, inferInstance, algebraMap V V', l,
    ⟨inferInstance, inferInstance, hc, charZero_of_injective_ringHom hinj⟩, hinj, hloc, hl⟩

theorem surjective_of_isHom_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {f : Y.Z ⟶ M.Z}
    (hf : M.IsHom Y (AlgHom.id o Ω) f) [IsProper f] : Surjective f := by
  have h : Y.pt ≫ f = M.pt := by
    rw [hf]
    exact (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  haveI : IsDominant (Y.pt ≫ f) := h ▸ inferInstance
  haveI : IsDominant f := IsDominant.of_comp Y.pt f
  infer_instance

theorem exists_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  intro g n F W Z i X₁ z₁ Y πY h V _ _ _ _ ev _ hV
  obtain ⟨U₀, EE, -, -, -, hf, hp⟩ := h
  haveI := surjective_of_isHom_id hf
  obtain ⟨V', _, _, _, j, ξ, h1, h2, h3, h4⟩ := exists_lift_of_proper πY V hV (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, j, ξ, h1, h2, h3, ?_⟩
  rw [h4, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep.TraitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat


open GlobalTheory.NonlocalTrait in
theorem exists_trait_torusPart : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  intro Y _ _ G _ _ hG w w' hsp hne
  let s' : Sp (Y.presheaf.stalk w') ⟶ Y := Y.fromSpecStalk w'
  let g : Y.presheaf.stalk w' →+* Y.presheaf.stalk w := (Y.presheaf.stalkSpecializes hsp).hom
  have hgs : spMap g ≫ s' = Y.fromSpecStalk w := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hg : ¬ IsLocalHom g := by
    intro hl
    apply hne
    have h1 : (spMap g) (closedPoint (Y.presheaf.stalk w)) = closedPoint (Y.presheaf.stalk w') :=
      Spec_closedPoint
    calc w = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := Scheme.fromSpecStalk_closedPoint.symm
      _ = (spMap g ≫ s') (closedPoint (Y.presheaf.stalk w)) := by rw [hgs]
      _ = s' ((spMap g) (closedPoint (Y.presheaf.stalk w))) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  let GR := (Over.pullback s').obj G
  have hGR : IsSemiAbelian GR := IsSemiAbelian.pullback _ G hG
  obtain ⟨V, _, _, hV, ψ, Ω, _, α, β, hψ, hβ, e, ⟨E⟩⟩ :=
    GlobalTheory.exists_trait_nonlocal_torusExtension (Y.presheaf.stalk w') GR hGR (Y.presheaf.stalk w) g hg
  let alg := algebraMap V (FractionRing V)
  let ξ : Sp V ⟶ Y := spMap ψ ≫ s'
  let G₁ := (Over.pullback ξ).obj G
  have h₁ : IsGrpPullback G₁ G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback _ G hG
  let GK := (Over.pullback (spMap (alg.comp ψ))).obj GR
  have hK : IsGrpPullback GK G (spMap alg ≫ ξ) _ :=
    ((isGrpPullback_pullback GR (spMap (alg.comp ψ))).comp (isGrpPullback_pullback G s')).congr
      (by rw [spMap_comp', Category.assoc]) rfl
  let ψ' : GK.left ⟶ G₁.left := h₁.1.lift _ (GK.hom ≫ spMap alg) (by rw [hK.1.w, Category.assoc])
  have hψ' : IsGrpPullback GK G₁ (spMap alg) ψ' :=
    h₁.cancel (hK.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _)
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  obtain ⟨j, hj, ej⟩ := GlobalTheory.TorusPart.extend_torus_hom_dvr V G₁ hG₁ GK ψ' hψ' ⟨E⟩ (FractionRing V) (RingHom.id _) GK ψ'
    hψ' E.X E.i E.i_hom
  haveI : IsLocalHom ψ := hψ
  have hαl : IsLocalHom α := ⟨fun x hx => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx⟩
  have hβl : IsLocalHom β := ⟨fun x hx => by
    by_contra hn
    rw [hβ x ((mem_maximalIdeal x).2 hn)] at hx
    exact not_isUnit_zero hx⟩
  have key : spMap α ≫ spMap alg ≫ ξ = spMap β ≫ Y.fromSpecStalk w := by
    calc spMap α ≫ spMap alg ≫ ξ = spMap ((α.comp alg).comp ψ) ≫ s' := by
          simp only [ξ, spMap_comp', Category.assoc]
      _ = spMap (β.comp g) ≫ s' := by rw [e]
      _ = spMap β ≫ Y.fromSpecStalk w := by rw [spMap_comp', Category.assoc, hgs]
  refine ⟨V, inferInstance, inferInstance, hV, ξ, G₁, inferInstance, inferInstance, pullback.fst G.hom ξ, E.X,
    inferInstance, inferInstance, inferInstance, j, GK, inferInstance, ψ', hψ', ?_, ?_, h₁, hj, ?_⟩
  · have h1 : (spMap ψ) (closedPoint V) = closedPoint (Y.presheaf.stalk w') := Spec_closedPoint
    calc ξ (closedPoint V) = s' ((spMap ψ) (closedPoint V)) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  · have h1 : (spMap α) (closedPoint Ω) = closedPoint (FractionRing V) := Spec_closedPoint
    have h2 : (spMap β) (closedPoint Ω) = closedPoint (Y.presheaf.stalk w) := Spec_closedPoint
    calc (spMap alg ≫ ξ) (closedPoint (FractionRing V)) = (spMap alg ≫ ξ) ((spMap α) (closedPoint Ω)) := by rw [h1]
      _ = (spMap α ≫ spMap alg ≫ ξ) (closedPoint Ω) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap β ≫ Y.fromSpecStalk w) (closedPoint Ω) := by rw [key]
      _ = Y.fromSpecStalk w ((spMap β) (closedPoint Ω)) := Scheme.Hom.comp_apply _ _ _
      _ = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := by rw [h2]
      _ = w := Scheme.fromSpecStalk_closedPoint
  · have : GlobalTheory.TorusPart.pullTorus hψ' j = E.i := ej
    rw [this]
    exact isTorPart_torusExtension E

end GlobalTheory.Poinc.FibLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfHeightOnePrimitiveEqZeroOfZeroDifferentialStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → ∀ b : H, cobOne K H b = 0 → dUnit (R := K) b = 0 → b = 0 := by
  first | exact @GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero | exact GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero | (intros; apply GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero <;> assumption)
end

