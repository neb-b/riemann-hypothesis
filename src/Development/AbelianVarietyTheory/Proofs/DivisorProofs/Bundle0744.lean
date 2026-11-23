module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtNegPrimeKernelDatumOfIntegersLattice
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_ker_point_sqrtNegNat {p : ℕ} (hp : 1 < p) (L : PeriodPair)
    (hL : MulStable L (sqrtNegNat p)) :
    ∃ t : ℂ, t ∉ L.lattice ∧ sqrtNegNat p * t ∈ L.lattice := by
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    rw [sqrtNegNat, map_mul, Complex.normSq_I, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg p), mul_one]
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have h0 : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    linarith
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hL
  have hc := kerRepsCard L _ S h0 hL hS
  rw [hn] at hc
  have hpos : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by
      push_cast at hc
      linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ := hpos
  have := hS.1 t ht
  exact ⟨t, by tauto, by tauto⟩

theorem g₂_mem_adjoin_j_of_eq (L : PeriodPair) (h0 : L.g₂ ≠ 0) (h : L.g₃ = L.g₂) :
    L.g₂ ∈ ℚ⟮(latticeCurve L).j⟯ := by
  have hΔ := latticeCurve_Δ_ne_zero L
  rw [latticeCurve_Δ, h] at hΔ
  have h27 : L.g₂ - 27 ≠ 0 := fun e => hΔ (by linear_combination L.g₂ ^ 2 * e)
  have hj : (latticeCurve L).j = 1728 * L.g₂ / (L.g₂ - 27) := by
    rw [latticeCurve_j_eq, h, div_eq_div_iff hΔ h27]
    ring
  have hj' : (latticeCurve L).j - 1728 = 1728 * 27 / (L.g₂ - 27) := by
    rw [hj]
    field_simp
    ring
  have e : L.g₂ = 27 * (latticeCurve L).j / ((latticeCurve L).j - 1728) := by
    rw [hj', hj]
    field_simp
  have hm := IntermediateField.mem_adjoin_simple_self ℚ (latticeCurve L).j
  rw [e]
  exact div_mem (mul_mem (ofNat_mem _ 27) hm) (sub_mem hm (ofNat_mem _ 1728))

theorem exists_datum_of_isIntegersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 →
    3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ),
      Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  intro p L₀ hp _ h3 hL₀
  obtain ⟨h2, h3', hmul⟩ := _root_.GlobalTheory.CMModel.integersLattice_invariants_ne_zero p L₀ hp h3 hL₀
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L₀.g₃ / L₀.g₂) two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact div_ne_zero h3' h2 (by rw [← hc]; simp)
  obtain ⟨L, hlat, hg2, hg3, -, hj⟩ := _root_.GlobalTheory.CMModel.exists_scaled_periodPair L₀ c hc0
  have hmul' : MulStable L (sqrtNegNat p) := by
    intro ω hω
    have h1 : c⁻¹ * ω ∈ L₀.lattice := (hlat _).mp (by rwa [mul_inv_cancel_left₀ hc0])
    have h2 := (hlat _).mpr (hmul _ h1)
    rwa [mul_left_comm, mul_inv_cancel_left₀ hc0] at h2
  have hne : L.g₂ ≠ 0 := by
    rw [hg2]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc0)) h2
  have heq : L.g₃ = L.g₂ := by
    have : L₀.g₃ = c ^ 2 * L₀.g₂ := by rw [hc, div_mul_cancel₀ _ h2]
    rw [hg2, hg3, this]
    field_simp
  have hmem := g₂_mem_adjoin_j_of_eq L hne heq
  rw [hj] at hmem
  obtain ⟨t, ht, ht'⟩ := exists_ker_point_sqrtNegNat hp.one_lt L hmul'
  exact ⟨L, t, ⟨hmul', hmem, heq ▸ hmem, ht, ht'⟩, hj⟩

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternion
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem nrm_smul_eq_sq_mul {R : Type*} [CommRing R] {a b : R} (t : R) (x : ℍ[R, a, b]) :
    nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_sum_orthIdem_smul {R : Type*} [CommRing R] {a b : R} {ι : Type} [Fintype ι] (η : ι → R)
    (y : ι → ℍ[R, a, b]) (h1 : ∀ i, η i * η i = η i) (h2 : ∀ i j, i ≠ j → η i * η j = 0)
    (h3 : ∑ i, η i = 1) : nrm (∑ i, η i • y i) = ∑ i, η i * nrm (y i) := by
  classical
  have key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i) := by
    intro i
    have hs : η i • (∑ j, η j • y j) = η i • y i := by
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, h1]
      · intro j _ hj
        rw [smul_smul, h2 i j (Ne.symm hj), zero_smul]
      · simp
    have := congrArg nrm hs
    rwa [nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1] at this
  calc nrm (∑ i, η i • y i) = ∑ i, η i * nrm (∑ j, η j • y j) := by
        rw [← Finset.sum_mul, h3, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => key i

def quatStdBasis {R : Type*} [CommRing R] (a b : R) : Fin 4 → ℍ[R, a, b] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem nrm_intertwiner_comb {R : Type*} [CommRing R] {a b c : R} (p q : ℍ[R, a, b]) (hp : p.re = 0) (hq : q.re = 0)
    (hpp : p * p = algebraMap R ℍ[R, a, b] c) (hqq : q * q = algebraMap R ℍ[R, a, b] c) :
    ∑ i, (![a * b, -b, -a, 1] : Fin 4 → R) i * nrm (p * quatStdBasis a b i + quatStdBasis a b i * q)
      = -8 * a * b * c := by
  have h1 := congrArg QuaternionAlgebra.re hpp
  have h2 := congrArg QuaternionAlgebra.re hqq
  simp [QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2
  simp [Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]
  linear_combination (-4 * a * b) * h1 + (-4 * a * b) * h2

theorem exists_unit_intertwiner : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  intro F _ _ a b ha hb c hc p q hp hq hpp hqq
  have hcomb := nrm_intertwiner_comb p q hp hq hpp hqq
  have hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c) := by
    have h : IsUnit (-8 * a * b * c) := by
      refine Ne.isUnit ?_
      have : (-8 : F) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc
    have h' := h.map (algebraMap F (AF F))
    rwa [map_mul, map_mul, map_mul, map_neg, map_ofNat] at h'
  rw [← hcomb] at hu
  obtain ⟨η, h1, h2, h3, h4⟩ := _root_.GlobalTheory.QSA.exists_idem_pick_unit F (Fin 4) _ _ hu
  refine ⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩
  · rw [nrm_sum_orthIdem_smul η _ h1 h2 h3]; exact h4
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc,
      Algebra.commutes]

end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCase
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNorm.FieldCase

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [Field K] [Algebra F K]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR K e) = inclR K (σ e) := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (x : K ⊗[F] E) :
    sigR K σ (sigR K σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) K) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective

theorem hR_eq_hf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → K ⊗[F] E) :
    hR K σ J x y = GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose y x := by
  simp only [hR, Formalism.UG.hform, GlobalTheory.UTrans.hf, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Alg

theorem exists_unitNorm_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hJ hunit hiso a b ha hb
  have hinj := inclR_injective (F := F) (E := E) K
  haveI : Nontrivial (K ⊗[F] E) := hinj.nontrivial
  haveI : CharZero (K ⊗[F] E) := charZero_of_injective_algebraMap (algebraMap F (K ⊗[F] E)).injective
  have hfield : IsField (K ⊗[F] E) :=
    ⟨exists_pair_ne _, mul_comm, fun {x} hx => (hunit x hx).exists_right_inv⟩
  letI : Field (K ⊗[F] E) := hfield.toField
  have hG : GlobalTheory.UTrans.IsHerm (sigR K σ) (JR K J).transpose :=
    { invol := sigR_sigR K σ (GlobalTheory.HermLineZeros.conj_invol hcm)
      ne_id := by
        obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
        exact ⟨inclR K d, fun h => hd (hinj (by rw [← sigR_inclR]; exact h))⟩
      herm := fun p q => by
        simp only [Matrix.transpose_apply, JR, Matrix.map_apply, sigR_inclR]
        rw [hJ.1 p q]
      det_ne := by
        rw [Matrix.det_transpose, JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        intro h
        exact hJ.2 (hinj (by rw [h, map_zero])) }
  have hsymm : ∀ x y, sigR K σ (hR K σ J x y) = hR K σ J y x := by
    intro x y
    rw [hR_eq_hf, hR_eq_hf, GlobalTheory.UTrans.IsoBasis.hf_symm hG]
  obtain ⟨u, hu0, huu⟩ := hiso
  have hz : ∃ z, z ≠ 0 ∧ GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose z z = 0 := ⟨u, hu0, by rw [← hR_eq_hf]; exact huu⟩
  obtain ⟨e, he, hne⟩ := GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid hG hz
    ![GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose a, GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose b] (by
      intro i
      fin_cases i
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG ha
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG hb)
  have hee : hR K σ J e e = 0 := by rw [hR_eq_hf]; exact he
  have h1 : hR K σ J a e ≠ 0 := by
    rw [hR_eq_hf]; exact hne 0
  have h2 : hR K σ J e b ≠ 0 := by
    intro h
    apply hne 1
    change GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose e b = 0
    rw [← hR_eq_hf, ← hsymm, h, map_zero]
  refine ⟨e, ⟨hR K σ J a e, isUnit_iff_ne_zero.2 h1, ?_⟩, ⟨hR K σ J e b, isUnit_iff_ne_zero.2 h2, ?_⟩⟩
  · rw [hsymm, gram2R, hee]; ring
  · rw [hsymm, gram2R, hee]; ring

end GlobalTheory.PlaneNorm.FieldCase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.EndLoc.HomGlue

theorem Pt.comp_f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z W : Scheme.{0}} {x x' : Pt A B L M Z} (e : x = x') (p : W ⟶ pullback A.hom x.t)
    (q : W ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst e
  obtain rfl : p = q := pullback.hom_ext h1 h2
  rfl

theorem Pt.ext_cover : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (y y' : HomGlue.Pt A B L M Z),
    (∀ i, y.map hL hM (𝒰.f i) = y'.map hL hM (𝒰.f i)) → y = y' := by
  intro S A B _ _ L M hL hM Z 𝒰 y y' h
  have ht : y.t = y'.t := 𝒰.hom_ext _ _ fun i => congrArg Pt.t (h i)
  obtain ⟨t, f, w⟩ := y
  obtain ⟨t', f', w'⟩ := y'
  dsimp only at ht
  subst ht
  suffices hf : f = f' by subst hf; rfl
  refine (Scheme.Pullback.openCoverOfRight 𝒰 A.hom t).hom_ext _ _ fun (i : 𝒰.I₀) => ?_
  have := Pt.comp_f_eq (h i) (𝟙 _) (𝟙 _) rfl rfl
  change 𝟙 _ ≫ pmap A t (𝒰.f i) ≫ f = 𝟙 _ ≫ pmap A t (𝒰.f i) ≫ f' at this
  rw [Category.id_comp, Category.id_comp] at this
  have e : (Scheme.Pullback.openCoverOfRight 𝒰 A.hom t).f i = pmap A t (𝒰.f i) := by
    rw [Scheme.Pullback.openCoverOfRight_f]
    apply pullback.hom_ext
    · erw [pullback.lift_fst]
    · erw [pullback.lift_snd]
  rw [e]
  exact this

end GlobalTheory.EndLoc.HomGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareOfSymmetricTensorRelations
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exteriorSq_of_symm_relations (K : Type) [Field K] (V W : Type) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (β : V →ₗ[K] V →ₗ[K] W)
    (hW : Module.finrank K W ≤ (Module.finrank K V).choose 2)
    (hrel : ∀ t : V ⊗[K] V, TensorProduct.lift β t = 0 → TensorProduct.comm K V V t = t) :
    (∃ e : ⋀[K]^2 V ≃ₗ[K] W, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = β a b) ∧
      Function.Surjective (TensorProduct.lift β) ∧
      ∀ t : V ⊗[K] V, TensorProduct.comm K V V t = t → TensorProduct.lift β t = 0 := by
  classical
  set n := Module.finrank K V with hn
  have h0 : ∀ a b x : V, Function.update ![a, b] 0 x = ![x, b] := by
    intro a b x; ext i; fin_cases i <;> rfl
  have h1 : ∀ a b x : V, Function.update ![a, b] 1 x = ![a, x] := by
    intro a b x; ext i; fin_cases i <;> rfl
  let wb : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V :=
    LinearMap.mk₂ K (fun a b => exteriorPower.ιMulti K 2 ![a, b])
      (by intro a₁ a₂ b
          rw [← h0 a₁ b (a₁ + a₂), AlternatingMap.map_update_add]; simp only [h0])
      (by intro c a b
          rw [← h0 a b (c • a), AlternatingMap.map_update_smul]; simp only [h0])
      (by intro a b₁ b₂
          rw [← h1 a b₁ (b₁ + b₂), AlternatingMap.map_update_add]; simp only [h1])
      (by intro c a b
          rw [← h1 a b (c • b), AlternatingMap.map_update_smul]; simp only [h1])
  let π : V ⊗[K] V →ₗ[K] ⋀[K]^2 V := TensorProduct.lift wb
  have hπt : ∀ a b, π (a ⊗ₜ b) = exteriorPower.ιMulti K 2 ![a, b] := by
    intro a b; simp [π, wb]
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span K 2 V, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    refine ⟨m 0 ⊗ₜ m 1, ?_⟩
    rw [hπt]; congr 1; ext i; fin_cases i <;> rfl
  have hswap : ∀ x y : V, exteriorPower.ιMulti K 2 ![x, y] = -exteriorPower.ιMulti K 2 ![y, x] := by
    intro x y
    rw [← (exteriorPower.ιMulti K 2).map_swap ![y, x] (show (0 : Fin 2) ≠ 1 by decide)]
    congr 1; ext i; fin_cases i <;> rfl
  have hdiag : ∀ x : V, exteriorPower.ιMulti K 2 ![x, x] = 0 := by
    intro x
    exact (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)
  let b := Module.finBasis K V
  let bt := b.tensorProduct b
  let r : V ⊗[K] V →ₗ[K] ⋀[K]^2 V :=
    bt.constr K (fun p => if p.1 < p.2 then exteriorPower.ιMulti K 2 ![b p.1, b p.2] else 0)
  have hrb : ∀ i j, r (b i ⊗ₜ b j) = if i < j then exteriorPower.ιMulti K 2 ![b i, b j] else 0 := by
    intro i j
    rw [← Module.Basis.tensorProduct_apply, Module.Basis.constr_basis]
  have hr : r ∘ₗ (LinearMap.id - (TensorProduct.comm K V V).toLinearMap) = π := by
    apply bt.ext; rintro ⟨i, j⟩
    simp only [bt, Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, map_sub, hrb, hπt]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h; simp [hdiag]
    · simp [h, lt_asymm h, hswap (b i) (b j)]
  have hS : ∀ t, TensorProduct.comm K V V t = t → π t = 0 := by
    intro t ht
    rw [← hr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ht,
      sub_self, map_zero]
  set L := TensorProduct.lift β with hLdef
  have hle : LinearMap.ker L ≤ LinearMap.ker π := fun t ht => hS t (hrel t ht)
  have hVV : Module.finrank K (V ⊗[K] V) = n * n := Module.finrank_tensorProduct
  have hext : Module.finrank K (⋀[K]^2 V) = n.choose 2 := by rw [exteriorPower.finrank_eq]
  have hπk := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hext, hVV] at hπk
  have hLk := LinearMap.finrank_range_add_finrank_ker L
  rw [hVV] at hLk
  have hLr : Module.finrank K (LinearMap.range L) ≤ Module.finrank K W := Submodule.finrank_le _
  have hNeq : LinearMap.ker L = LinearMap.ker π :=
    Submodule.eq_of_le_of_finrank_le hle (by
      generalize n * n = m at hπk hLk
      generalize n.choose 2 = k at hπk hW
      omega)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [hNeq] at hLk
    generalize n * n = m at hπk hLk
    generalize n.choose 2 = k at hπk hW
    omega
  refine ⟨?_, hL, fun t ht => ?_⟩
  · refine ⟨(π.quotKerEquivOfSurjective hπ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hNeq.symm).trans (L.quotKerEquivOfSurjective hL)), ?_⟩
    intro a c
    rw [← hπt, ← LinearMap.quotKerEquivOfSurjective_apply_mk π hπ, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, hLdef, TensorProduct.lift.tmul]
  · have : t ∈ LinearMap.ker L := hNeq ▸ hS t ht
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesMod
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.SemilocalClasses

theorem card_finset_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
    (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ x : A, π (n • x) = 0) (s : Finset Q) : s.card ≤ n ^ Module.finrank ℚ V := by
  classical
  obtain ⟨σ, hσ⟩ := hπ.hasRightInverse
  let F : Submodule ℤ A := Submodule.span ℤ (↑(s.image σ) : Set A)
  haveI : Module.Finite ℤ F := Module.Finite.span_of_finite ℤ (Finset.finite_toSet _)
  let g : F →ₗ[ℤ] V := f.toIntLinearMap ∘ₗ F.subtype
  have hg : Function.Injective g := hf.comp F.subtype_injective
  haveI : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
  haveI : Module.IsTorsionFree ℤ F := Function.Injective.moduleIsTorsionFree g hg (by simp)
  haveI : Module.Free ℤ F := Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank ℤ F ≤ Module.finrank ℚ V := by
    let b := Module.finBasis ℤ F
    have h1 : LinearIndependent ℤ (g ∘ b) := b.linearIndependent.map' g (LinearMap.ker_eq_bot.2 hg)
    have h2 : LinearIndependent ℚ (g ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
    simpa using h2.fintype_card_le_finrank
  let p : F →+ Q := π.comp F.subtype.toAddMonoidHom
  have hle : (nsmulAddMonoidHom (α := F) n).range ≤ p.ker := by
    rintro _ ⟨x, rfl⟩
    simpa [p] using h0 x
  have hidx : (nsmulAddMonoidHom (α := F) n).range.index = n ^ Module.finrank ℤ F :=
    AddSubgroup.index_range_nsmul F n
  have hpos : 0 < n ^ Module.finrank ℤ F := pow_pos hn _
  have hdvd : p.ker.index ∣ n ^ Module.finrank ℤ F := hidx ▸ AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_ker] at hdvd
  have hne : Nat.card p.range ≠ 0 := fun h => by
    rw [h] at hdvd; exact hpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  haveI : Finite p.range := Nat.finite_of_card_ne_zero hne
  have hsub : (↑s : Set Q) ⊆ (p.range : Set Q) := fun q hq =>
    ⟨⟨σ q, Submodule.subset_span (by simpa using ⟨q, hq, rfl⟩)⟩, hσ q⟩
  calc s.card = Nat.card (↑s : Set Q) := by simp
    _ ≤ Nat.card p.range := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ n ^ Module.finrank ℤ F := Nat.le_of_dvd hpos hdvd
    _ ≤ n ^ Module.finrank ℚ V := Nat.pow_le_pow_right hn hr

theorem finite_card_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
    (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ x : A, π (n • x) = 0) : Finite Q ∧ Nat.card Q ≤ n ^ Module.finrank ℚ V := by
  have h := card_finset_le f hf π hπ n hn h0
  have hfin : Finite Q := by
    by_contra hinf
    haveI : Infinite Q := not_finite_iff_infinite.1 hinf
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Q (n ^ Module.finrank ℚ V + 1)
    have := h s
    omega
  refine ⟨hfin, ?_⟩
  haveI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card]
  exact h Finset.univ

theorem finite_card_classes : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ∧ Nat.card (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ≤ (cA * c) ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ a b S L L' cA c _ _ hA hc
  haveI : Module.Finite ℚ (HomE E a b) := Module.Finite.trans E (HomE E a b)
  have hd : Module.finrank ℚ (HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E (HomE E a b), Module.finrank_linearMap]
    simp [mul_assoc]
  rw [← hd]
  refine finite_card_le (divLat cA (homAt S L L')).subtype.toAddMonoidHom (Submodule.subtype_injective _)
    ((mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype).mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective _) (cA * c) (Nat.mul_pos hA hc) fun x => ?_
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(cA : 𝓞 E) • (x : HomE E a b), x.2, ?_⟩
  show (c : 𝓞 E) • (cA : 𝓞 E) • (x : HomE E a b) = (cA * c) • (x : HomE E a b)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, mul_nsmul]

end GlobalTheory.SemilocalClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteFormsStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  first | exact @GlobalTheory.HCF.ModGrowth.modGrowth_span | exact GlobalTheory.HCF.ModGrowth.modGrowth_span | (intros; apply GlobalTheory.HCF.ModGrowth.modGrowth_span <;> assumption)
end

