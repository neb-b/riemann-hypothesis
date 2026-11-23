module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.SerreDim

theorem finrank_tensor_of_algebra (O M k B L : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [CommRing B] [Algebra O B] [Algebra k B]
    [Module.Finite k B] [AddCommGroup L] [Module k L] [Module O L] [Module B L] [IsScalarTower k B L]
    [IsScalarTower O B L] [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B (B ⊗[O] M) (Module.finrank O M) fun P => by
    letI : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O B (B ⧸ P.asIdeal) (B ⧸ P.asIdeal) M).finrank_eq]
    exact TenDim.finrank_fibre O M _
  let e : L ⊗[O] M ≃ₗ[B] (Fin (Module.finrank O M) → L) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O B B L M).symm ≪≫ₗ
      (b.equivFun.lTensor L) ≪≫ₗ TensorProduct.piScalarRight B B L _
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_tensor (O M k L : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [AddCommGroup L] [Module k L] [Module O L]
    [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : SMulCommClass k O L := SMulCommClass.symm _ _ _
  letI : Module (k ⊗[ℤ] O) L := TensorProduct.Algebra.module
  letI : Algebra O (k ⊗[ℤ] O) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change (r ⊗ₜ[ℤ] (1 : O)) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  have : IsScalarTower O (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change ((1 : k) ⊗ₜ[ℤ] r) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  exact finrank_tensor_of_algebra O M k (k ⊗[ℤ] O) L

theorem dim_eq_of_isPullback {X Y S T X' S' : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ T} {f' : X' ⟶ S'} {a : X' ⟶ X}
    {b : S' ⟶ S} {c : X' ⟶ Y} {d : S' ⟶ T} (h : IsPullback a f' f b) (h' : IsPullback c f' g d)
    {n m : ℕ} {W : X.Opens} {V : Y.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f))
    (hV : SmoothOfRelativeDimension m (V.ι ≫ g)) (x : X') (hx : a x ∈ W) (hx' : c x ∈ V) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension m ((c ⁻¹ᵁ V).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback
      ((isPullback_morphismRestrict c V).paste_vert h') hV
  have e₁ : SmoothOfRelativeDimension (0 + n) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ a ⁻¹ᵁ W), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ c ⁻¹ᵁ V), Category.assoc]; infer_instance
  simpa using H1.dim_unique _ e₁ e₂ ⟨x, hx, hx'⟩

theorem isPullback_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    IsPullback (fst G G * snd G G).left (snd G G).left G.hom G.hom := by
  let e : G ⊗ G ≅ G ⊗ G :=
    { hom := lift (fst G G * snd G G) (snd G G)
      inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  refine h.of_iso ((Over.forget S).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change (fst G G ≫ 𝟙 _).left = (e.inv ≫ (fst G G * snd G G)).left
    congr 1
    simp [e, MonObj.comp_mul]
  · change (snd G G ≫ 𝟙 _).left = (e.inv ≫ snd G G).left
    congr 1
    simp [e]

theorem exists_dim_of_grpObj {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [Smooth G.hom] :
    ∃ n, SmoothOfRelativeDimension n G.hom := by
  choose n W hW hd using H1.exists_dim G.hom
  let x₀ : G.left := η[G].left (default : PrimeSpectrum k)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_⟩
  let p : G ⟶ G ⊗ G := lift 1 (𝟙 G)
  have p₁ : p ≫ fst G G = toUnit G ≫ η[G] := lift_fst _ _
  have p₂ : p ≫ (fst G G * snd G G) = 𝟙 G := by simp [p, MonObj.comp_mul]
  have q₁ : (fst G G).left (p.left y) = x₀ :=
    (congrArg (fun q : G ⟶ G => q.left y) p₁).trans
      (congrArg η[G].left (Subsingleton.elim (α := PrimeSpectrum k) _ _))
  have q₂ : (fst G G * snd G G).left (p.left y) = y := congrArg (fun q : G ⟶ G => q.left y) p₂
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  rw [dim_eq_of_isPullback h (isPullback_mul G) (hd x₀) (hd y) (p.left y) (q₁ ▸ hW x₀) (by rw [q₂]; exact hW y)]
  exact hd y

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M) {g : ℕ}
    (hG : SmoothOfRelativeDimension g G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M * g := by
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := TenDim.exists_isLieBasis A hA
  have := Module.Finite.of_basis (Serre.Lie.basis a hv)
  have h := finrank_tensor O M k (Serre.Lie a)
  rwa [(t.lieEquivBase b).finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Module.finrank_eq_card_basis (Serre.Lie.basis a hv), Fintype.card_fin, Fintype.card_fin] at h

theorem smoothOfRelativeDimension_tensor :
    ∀ (S : Scheme.{0}) (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (g : ℕ), Nonempty (Serre.IsTensor A b G a M) → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (Module.finrank O M * g) A.hom := by
  rintro S O _ _ _ M _ _ _ _ G A _ _ _ _ a b g ⟨t⟩ hG
  have : Smooth G.hom := hG.smooth
  have : Smooth A.hom := t.smooth
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M * g)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M * g)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have : Smooth ((Over.pullback x).obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom x))
  obtain ⟨m, hm⟩ := exists_dim_of_grpObj ((Over.pullback x).obj A)
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback A.hom x) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension g (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  rw [← dim_eq_field (t.pullback x) hG' hm, ← e₁]
  exact hd y

end GlobalTheory.SerreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.WtSizes

theorem extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  unfold Formalism.L2.Pj.ext0
  split_ifs with hi
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i, hi⟩ : Fin p))
  · exact Nat.zero_le _

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  have h1 : ∑ k, f k = ∑ i : Fin p, Formalism.L2.Pj.ext0 f i :=
    Finset.sum_congr rfl fun i _ => by simp [Formalism.L2.Pj.ext0, i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) m,
    Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) p]
  refine Finset.sum_le_sum_of_ne_zero fun i _ hi => ?_
  rw [Finset.mem_range]
  by_contra hp
  exact hi (by simp [Formalism.L2.Pj.ext0, hp])

variable {D : D7} {j : ℕ}


open Classical in
def tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if b = DV.tauEmb D t then ∑ i, w.aP t i else 0) +
    if b = conjEmb (DV.tauEmb D t) then ∑ i, w.aM t i else 0)

theorem wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (i : ℕ) : wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl

theorem sum_wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (m : ℕ) :
    ∑ i : Fin m, wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp

theorem sum_tot (w : WeightFamilies.Wt D j) :
    ∑ b, tot w b = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  unfold tot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem tot_le_size (w : WeightFamilies.Wt D j) :
    ((∑ b, tot w b : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  rw [sum_tot]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem spread_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

theorem invFun_relab (T : Core D) (τ : D.host.E →+* ℂ) : Function.invFun (relab T.Q.c T.σ₀) τ = τ := by
  have h : ∀ τ : D.host.E →+* ℂ, relab T.Q.c T.σ₀ τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab T.Q.c T.σ₀ (Function.invFun (relab T.Q.c T.σ₀) τ) = τ := Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem spread_laU_le (T : Core D) (hr : 0 < D.R.r) (w : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp)
    (τ : ((T.U j T.σ₀).X k).Ψ) :
    ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ ≤
      (tot w τ.1 : ℝ) + tot w (conjEmb τ.1) + w.n := by
  have hn : ((w.n / 2 : ℕ) : ℝ) + ((w.n / 2 : ℕ) : ℝ) ≤ w.n := by
    have : w.n / 2 + w.n / 2 ≤ w.n := by omega
    exact_mod_cast this
  have key : ∀ i, -((tot w (conjEmb τ.1) : ℤ) + ((w.n / 2 : ℕ) : ℤ)) ≤ laU (T.U j T.σ₀) (wtA w) w.n k τ i ∧
      laU (T.U j T.σ₀) (wtA w) w.n k τ i ≤ (tot w τ.1 : ℤ) + ((w.n / 2 : ℕ) : ℤ) := by
    intro i
    unfold laU
    rw [invFun_relab, invFun_relab]
    have a1 := wtA_le_tot w τ.1 ((i : ℕ) - ((T.U j T.σ₀).X k).p0)
    have a2 := wtA_le_tot w (conjEmb τ.1) (((T.U j T.σ₀).X k).p0 - 1 - (i : ℕ))
    split_ifs <;> constructor <;> omega
  refine (spread_le hr _ ((tot w τ.1 : ℝ) + ((w.n / 2 : ℕ) : ℝ))
    ((tot w (conjEmb τ.1) : ℝ) + ((w.n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_cm_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (B : (E →+* ℂ) → ℕ) : ∑ τ : X.Ψ, (B τ.1 + B (conjEmb τ.1)) ≤ ∑ b, B b := by
  classical
  have hcc : ∀ τ : E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => RingHom.ext fun x => by simp [conjEmb]
  have hinj : Function.Injective (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := Function.LeftInverse.injective hcc
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort X.Ψ B, Finset.sum_coe_sort X.Ψ (fun τ => B (conjEmb τ)),
    ← Finset.sum_image (f := B) (g := conjEmb) (s := X.Ψ) hinj.injOn, ← Finset.sum_add_sum_compl X.Ψ B]
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun b hb => ?_) _
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.mem_compl]
  exact (X.cmType τ).1 hτ

theorem fdeg_eq (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

theorem one_le_dE (D : D7) : 1 ≤ dE D.host.E := by
  unfold dE
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero _)
  exact_mod_cast h

theorem sqrt_le_dE (D : D7) : Real.sqrt D.host.d ≤ dE D.host.E := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have h2 : Real.sqrt D.host.d ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_left (Nat.cast_nonneg _) hq)
  have h4 : D.host.rdE ≤ dE D.host.E := by
    have h5 : (1 : ℝ) ≤ (Module.finrank ℚ D.host.E : ℝ) := by
      have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
      exact_mod_cast this
    exact Real.rpow_le_self_of_one_le (one_le_dE D) ((div_le_one (by linarith)).2 h5)
  linarith

theorem sizes : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, 0 < D.R.r ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ fdeg D.host.E = D.R.f ∧ Real.sqrt D.host.d ≤ dE D.host.E ∧ 1 ≤ dE D.host.E ∧ Real.log (dE D.host.E) = logdE D ∧ (∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size) ∧ ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  intro D T h j hj w
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hts := tot_le_size w
  refine ⟨hr, (h.unf j hj T.σ₀ T.good_σ₀).1.symm, fdeg_eq D, sqrt_le_dE D, one_le_dE D, rfl, fun k => ?_, ?_⟩
  · refine (Finset.sum_le_sum fun τ _ => spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast sum_cm_le ((T.U j T.σ₀).X k) (tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), fdeg_eq, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  · refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => sum_wtA_le_tot w b _

end GlobalTheory.WtSizes
end
end

