module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjKernelMul
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel


open GlobalTheory.ConjPoint PeriodPair in
theorem exists_conj_kernel_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  intro p F L t hp h4 h3 hD σ hσ
  have h₂ : L.g₂ = σ L.g₂ := (hσ _ hD.g₂_mem).symm
  have h₃ : L.g₃ = σ L.g₃ := (hσ _ hD.g₃_mem).symm
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  obtain ⟨t', ht'⟩ := latticePoint_surjective L (s (latticePoint L t))
  have hct : IsConj L L σ t t' := (hc _ _).2 ht'.symm
  have ht'n : t' ∉ L.lattice := by
    rcases hct with h | h
    · exact (hD.notMem h.1).elim
    · exact h.2.1

  have hsq : (σ (sqrtNegNat p)) ^ 2 = (sqrtNegNat p) ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  have hm := IsConj.mul h₂ h₃ hD.mul hct
  have hker : σ (sqrtNegNat p) * t' ∈ L.lattice := by
    rcases hm with h | h
    · exact h.2
    · exact (h.1 hD.ker).elim
  have hker' : sqrtNegNat p * t' ∈ L.lattice := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e
    · rwa [e] at hker
    · rw [e, neg_mul] at hker
      simpa using neg_mem hker
  obtain ⟨-, hz, -⟩ := _root_.GlobalTheory.CMModel.ker_sqrtNegNat_cyclic p F L t hp h4 h3 hD
  obtain ⟨c, hcp, hcl⟩ := hz t' hker'
  refine ⟨c, fun hdvd => ?_, fun k => ?_⟩
  · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hcp
    subst hc0
    exact ht'n (by simpa using hcl)
  · have hk := IsConj.mul h₂ h₃ (α := (k : ℂ))
      (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl k) hct
    rw [map_natCast] at hk
    have h0 : IsConj L L σ 0 ((k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t') := by
      left
      refine ⟨zero_mem _, ?_⟩
      have : (k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t' = -((k : ℂ) * (t' - (c : ℂ) * t)) := by ring
      rw [this, ← nsmul_eq_mul]
      exact neg_mem (nsmul_mem hcl k)
    have := IsConj.add h₂ h₃ hk h0
    simpa using this

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEqui
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeGal

theorem continuous_galHom_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  first
  | exact @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | (apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix ..)

theorem exists_topAbelianization_mulEquiv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  have hc : (commutator G).map (φ : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]
    exact (hφ.homeomorph φ).image_closure _
  let ψ := QuotientGroup.congr _ _ φ hmap
  have h1 : Continuous ψ :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hφ.continuous)
  have hs : Continuous φ.symm :=
    (φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous
  have h2 : Continuous ψ.symm :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hs)
  exact ⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩

theorem exists_abMap_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K,
      Continuous φ ∧ Function.Bijective φ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  intro K _ _ Ω _ _ e
  haveI hint : Algebra.IsIntegral K Ω :=
    ⟨fun x => (isIntegral_algEquiv e).1 (Algebra.IsIntegral.isIntegral (e x))⟩
  let φ : (Ω ≃ₐ[K] Ω) ≃* Field.absoluteGaloisGroup K := AlgEquiv.autCongr e
  have h1 : Continuous φ.toMonoidHom :=
    continuous_galHom_of_fix φ.toMonoidHom fun y => ⟨e.symm y, fun σ hσ => by
      show e (σ (e.symm y)) = y
      rw [hσ, AlgEquiv.apply_symm_apply]⟩
  have h2 : Continuous φ.symm.toMonoidHom :=
    continuous_galHom_of_fix φ.symm.toMonoidHom fun y => ⟨e y, fun τ hτ => by
      show e.symm (τ (e y)) = y
      rw [hτ, AlgEquiv.symm_apply_apply]⟩
  have hφ : IsHomeomorph φ := (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph
  obtain ⟨ψ, hψ, hψg⟩ := exists_topAbelianization_mulEquiv φ hφ
  refine ⟨ψ.toMonoidHom, hψ.continuous, ψ.bijective, fun σ => ?_⟩
  exact hψg σ

end GlobalTheory.HeckeGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetDecoSetLatticeReps
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory

namespace DecoLatticeClasses

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def unitEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin γ.conjTranspose) (Matrix.mulVecLin γ)
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])

theorem unitEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    unitEquiv γ h ∈ UF E n := by
  intro x y
  change star (γ.conjTranspose.mulVec x) ⬝ᵥ (γ.conjTranspose.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mem_one_iff [NumberField E] (a : E) :
    a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end DecoLatticeClasses


open DecoLatticeClasses in
theorem exists_finset_decoSet_lattice_reps :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    ∃ Rs : Finset (Submodule (𝓞 E) (Sp E n)),
      (Rs.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
        ∃ g : UF E n,
          (((g, (1 : GLG (E := E) (n := n) (SG := SG))) • d :
            DecoSet (E := E) (n := n) (ST := ST) (SG := SG))).1.N ∈ Rs := by
  intro E _ _ _ _ hs n
  obtain ⟨R, hR, H⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr E n
  refine ⟨R, hR, fun ST SG d => ?_⟩
  have hu : Formalism.HermitianLatticesTheory.dual (hStd E n) d.1.N = d.1.N := d.2.uni
  have hspan : Submodule.span E (d.1.N : Set (Sp E n)) = ⊤ := by
    let W := Submodule.span E (d.1.N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    -- Self-duality puts the whole line through the orthogonal vector in the lattice.
    have hsmul (a : E) : a • e x ∈ d.1.N := by
      rw [← hu, mem_dual]
      intro y hy
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      rw [map_smul, hStd_isSymm.isRefl (e x) y hxy, smul_zero]
      exact Submodule.zero_mem _
    let i : E →ₗ[𝓞 E] d.1.N :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict d.1.N hsmul
    let : Module.Finite (𝓞 E) d.1.N := Module.Finite.iff_fg.mpr d.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H d.1.N d.2.lat.fg hspan (fun y => by
    conv_lhs => rw [← hu, mem_dual]
    simp only [mem_one_iff, hStd_apply, hs])
  have hγ' : γ * γ.conjTranspose = 1 := by
    rw [← hγ]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hs]
  refine ⟨⟨unitEquiv γ hγ', unitEquiv_mem γ hγ'⟩, ?_⟩
  have e : Formalism.HermitianLatticesTheory.gmap (unitEquiv γ hγ') d.1.N = L₀ := by
    ext x
    rw [mem_gmap, hm]
    rfl
  rw [← e] at hL₀
  exact hL₀

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem f_eq_of_pt_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z Y : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (p : Y ⟶ pullback A.hom x.t)
    (q : Y ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst h
  rw [pullback.hom_ext h1 h2]

theorem exists_glue_data : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), ∀ i, 𝒰.f i ≫ t = (x i).t ∧ ∀ e : pullback A.hom (x i).t ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ → e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝒰.f i → e ≫ f = (x i).f := by
  intro S A B _ _ L M hL hM Z 𝒰 x hx
  have hxt : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).t = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (x j).t :=
    fun i j => congrArg Pt.t (hx i j _ _ _ pullback.condition)
  obtain ⟨t, ht⟩ : ∃ t : Z ⟶ S, ∀ i, 𝒰.f i ≫ t = (x i).t :=
    ⟨_, fun i => 𝒰.ι_glueMorphisms _ hxt i⟩
  have c1 : ∀ i, pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.snd A.hom t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i := fun i => pullback.condition
  have hw : ∀ i, (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ (x i).t := by
    intro i
    rw [Category.assoc, pullback.condition, ← Category.assoc, c1, Category.assoc, ht]
  have hu1 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.fst A.hom (x i).t = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t :=
    fun i => pullback.lift_fst _ _ _
  have hu2 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.snd A.hom (x i).t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) := fun i => pullback.lift_snd _ _ _
  have hc : ∀ i j, pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw i) ≫ (x i).f) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw j) ≫ (x j).f) := by
    intro i j
    have c3 : pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f j) := pullback.condition
    have hbc : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ 𝒰.f i = (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← c1, ← c1, ← Category.assoc, ← Category.assoc, c3]
    have H := hx i j _ _ _ hbc
    have e1 : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw i)),
        hu2, Category.assoc]
    have e2 : (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw j)),
        hu2, Category.assoc]
    obtain ⟨p, hp1, hp2⟩ : ∃ p : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t),
        p ≫ pullback.fst _ _ = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _ ∧ p ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨q, hq1, hq2⟩ : ∃ q : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t),
        q ≫ pullback.fst _ _ = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _ := by
      rw [hp1, hq1, hu1, hu1, ← Category.assoc, ← Category.assoc, c3]
    have h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _ := by rw [hp2, hq2]
    have K : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).f = q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).f :=
      f_eq_of_pt_eq H p q h1 h2
    have p1 : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hp1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hp2, Category.id_comp, Category.assoc, hu2]
    have p2 : q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hq1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hq2, Category.id_comp, Category.assoc, hu2]
    rw [← Category.assoc, ← Category.assoc, ← p1, ← p2]
    exact (Category.assoc _ _ _).trans (K.trans (Category.assoc _ _ _).symm)
  let 𝒱 := 𝒰.pullback₁ (pullback.snd A.hom t)
  refine ⟨t, Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc, fun i => ⟨ht i, fun e he1 he2 => ?_⟩⟩
  have hι : pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc = pullback.lift _ _ (hw i) ≫ (x i).f :=
    Scheme.Cover.ι_glueMorphisms 𝒱 _ hc i
  have hv : e ≫ pullback.snd A.hom t = pullback.snd A.hom (x i).t ≫ 𝒰.f i := he2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : pullback A.hom (x i).t ⟶ pullback (pullback.snd A.hom t) (𝒰.f i),
      v ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = e ∧ v ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i) = pullback.snd A.hom (x i).t :=
    ⟨pullback.lift e _ hv, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hvu : v ≫ pullback.lift _ _ (hw i) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hv1, he1, Category.id_comp]
    · rw [Category.assoc, hu2, hv2, Category.id_comp]
  rw [← hv1, Category.assoc, hι, ← Category.assoc, hvu, Category.id_comp]

end GlobalTheory.EndLoc.HomGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOne
section
noncomputable section

open Formalism.L2.DIV NumberField

namespace GlobalTheory.GoodFamilyOfChars

theorem nOf_eq_nS {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (P0 : Subgroup G)
    [Fintype P0] (ψ0 : P0 →* Kˣ) (s : T.S) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf (T.tau s) ⟨P0, ψ0⟩ = Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨P0, ψ0⟩ s := by
  classical
  have e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]
    congr 1
    have hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have : x ∉ P0 := fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
      simp [this]), Finset.sum_map]
    simp only [Function.Embedding.subtype_apply]
    refine Finset.sum_congr (by convert rfl) fun h _ => ?_
    simp [h.2, Representation.asAlgebraHom_of, map_inv]
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS
  rw [e]

variable {K : Type} [Field K] {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module K W]

theorem asAlg_mem (τ : Representation K G W) (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U)
    (a : MonoidAlgebra K G) : ∀ w ∈ U, τ.asAlgebraHom a w ∈ U := by
  induction a using MonoidAlgebra.induction_on with
  | of g => intro w hw; simpa [Representation.asAlgebraHom_of] using hU g w hw
  | add a b ha hb => intro w hw; simpa using U.add_mem (ha w hw) (hb w hw)
  | smul r a ha => intro w hw; simpa using U.smul_mem r (ha w hw)

theorem asAlg_comm (τ : Representation K G W) (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f)
    (a : MonoidAlgebra K G) : f * τ.asAlgebraHom a = τ.asAlgebraHom a * f := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g
  | add a b ha hb => simp [map_add (f := _), mul_add, add_mul, ha, hb]
  | smul r a ha => simp [map_smul, ha]

theorem irr_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hs ((φ w)⁻¹ • φ.smulRight v)
  have := asAlg_mem τ U hU a w hw
  rw [ha] at this
  simpa [hφ] using this

theorem scalar_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  have hc : f ∈ Set.center (Module.End K W) := by
    rw [Semigroup.mem_center_iff]
    intro e
    obtain ⟨a, rfl⟩ := hs e
    exact (asAlg_comm τ f hf a).symm
  obtain ⟨α, hα, rfl⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, by ext x; simp⟩

theorem exists_goodFamily : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  intro K _ _ G _ _ X hX P0 _ ψ0 h1
  obtain ⟨T, hT, hM, -⟩ := GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1
  have hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g) := fun s => rfl
  have hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X := fun s => (hT _).2 ⟨s, (hch s)⟩
  refine ⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau,
    ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU,
     fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩,
    fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs⟩ := (hT χ).1 h
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hmem s
  · rw [nOf_eq_nS]
    exact hM s

end GlobalTheory.GoodFamilyOfChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHtNumsOfKerSideLastSide
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem exists_htNums_of_kerSide_lastSide :
    ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [DecidableEq Pl] [Fintype Emb] (R : RecNums J Pl) (C CT A : ℝ)
      (P : (J → Emb → ℝ) → Prop), 0 ≤ C → 0 ≤ CT → 2 * (16 + CT) ≤ R.Ch → 6 * C + 1 + 2 * C * C ≤ R.Ch →
      4 * C * (CT + C) ≤ R.Ch → KerSide R Emb C P → LastSide R CT A →
      ∃ hn : HtNums R Emb, hn.hPn = A ∧ P hn.sz := by
  intro J Pl Emb _ _ _ _ R C CT A P hC hCT h1 h2 h3 hK hL
  obtain ⟨g0, MainNotions, logOm, logth0, logh, logh', vv, logg, a1, a2, a3, a4, a5, a6, a7, a8, a9, hP⟩ := hK
  obtain ⟨bT, nτ, lam1, D0, D1, logc, logxi, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hL
  refine ⟨{ hPn := A, g0 := g0, MainNotions := MainNotions, logOmτ := logOm, logth0 := logth0, logh := logh, logh' := logh', vv := vv,
            logg := logg, C2 := C, Cth := C, C4 := C, c5 := C, c6 := C, CT := CT, C8 := C, Ce := C, ev := 0, bT := bT,
            nτ := nτ, lam1 := lam1, D0 := D0, D1 := D1, logc := logc, logxi := logxi, Cev := 0,
            i1 := a1, i2 := a2, i3 := a3, i4 := a4, i5 := a5, i6 := a6, i7 := a7, i8 := a8, i9 := a9,
            i10 := ⟨hC, hC, hC, hC, hC, hC, hC⟩,
            t1 := by simpa using b1, t2 := b2, t3 := b3, t4 := b4, t5 := b5, t6 := b6, t7 := b7, t8 := b8, t9 := b9,
            t10 := ⟨b10, b11, hCT⟩, t11 := ⟨by simp, le_rfl⟩,
            k1 := by linarith, k2 := by linarith, k3 := by linarith }, rfl, hP⟩

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAtStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F), (∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) → D ≠ 0 → ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ) → ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ), (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧ (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  first | exact @GlobalTheory.CMModel.exists_integral_of_modelAt | exact GlobalTheory.CMModel.exists_integral_of_modelAt | (intros; apply GlobalTheory.CMModel.exists_integral_of_modelAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFrameOfPosDef
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem exists_inv_frame_of_posDef {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ X : Matrix n n ℂ, IsUnit X.det ∧ (X⁻¹).conjTranspose * X⁻¹ = A := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBdet : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBdet, hB, Matrix.star_eq_conjTranspose]

theorem exists_isFrames (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs)
    (h : ∀ v : InfinitePlace K, ((Df.HV Bs.μ0).map v.embedding).PosDef) : ∃ X0, IsFrames Df X0 := by
  choose X hX using fun v => exists_inv_frame_of_posDef _ (h v)
  exact ⟨X, hX⟩

end GlobalTheory.ColRows
end

