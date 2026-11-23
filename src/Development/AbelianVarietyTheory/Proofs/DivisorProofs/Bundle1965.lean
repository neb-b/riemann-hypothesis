module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)

def pc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)

variable (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_pow_left {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP (x ^ k) y = k • pc hP x y := by
  have one : pc hP (1 : T ⟶ A) y = 0 := by
    have := hB T 1 1 y
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]

include hB' in
theorem pc_pow_right {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP x (y ^ k) = k • pc hP x y := by
  have one : pc hP x (1 : T ⟶ A) = 0 := by
    have := hB' T x 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]


include hB hB' in
theorem exists_theta_diag {k : ℕ} {T : Over S} (x : T ⟶ A) (hx : x ^ k = 1) :
    ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : k • pc hP (fst T A ≫ x) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (fst T A ≫ x)
    rwa [_root_.mul_one, left_eq_add] at this
  have h2 : k • pc hP (fst T A ≫ x) (snd T A) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (snd T A)
    rwa [_root_.mul_one, left_eq_add] at this
  have h3 : k • pc hP (snd T A) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_right hP hB', ha]
    have := hB' (T ⊗ A) (snd T A) 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
    abel
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Classes

section Mul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]


open WeilMul in
theorem weilIs_mul_left (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {x x' y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c)
    (h' : Out.WeilIs A L k x' y c') : Out.WeilIs A L k (x * x') y (c * c') := by
  intro p
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le hL (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le hL (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul hL (hc'.congr hG hA hL rfl (py.trans py'.symm))
  have q : θ.pt = Out.overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff hL _ _ _ _).2 (hθ.congr hG hA hL (p₁.trans q.symm) (p₂.trans py.symm))

end Mul

end GlobalTheory.DiagPairing

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

theorem exists_weilIs_diag_root : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N →
    IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := by
  intro h n B _ ζ S s c N T x y hamp hN _ hx hy
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ c.A), pc c.isLB (x * x') y = pc c.isLB x y + pc c.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ c.A), pc c.isLB x (y * y') = pc c.isLB x y + pc c.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ c.A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp c.A c.diag N (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag c.isLB hB hB' (k := N) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := weilIs_mul_left hG c.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG c.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs c.A c.diag N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact weilIs_mul_left hG c.ab hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG c.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.DiagPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SpecFibreProduct

theorem point_factors (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁)
    (hg₂ : Function.Surjective g₂) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P) :
    (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨
      (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hinj : ∀ a b : P, f₁.hom a = f₁.hom b → f₂.hom a = f₂.hom b → a = b :=
    fun a b h₁ h₂ ↦ H.2.1 a b ⟨h₁, h₂⟩
  have hex : ∀ (b : R₁) (c : R₂), g₁.hom b = g₂.hom c → ∃ a : P, f₁.hom a = b ∧ f₂.hom a = c :=
    fun b c h ↦ H.2.2 b c h
  have hs₁ : Function.Surjective f₁.hom := by
    intro b
    obtain ⟨c, hc⟩ := hg₂ (g₁.hom b)
    obtain ⟨a, ha, -⟩ := hex b c hc.symm
    exact ⟨a, ha⟩
  have hs₂ : Function.Surjective f₂.hom := by
    intro c
    obtain ⟨b, hb⟩ := hg₁ (g₂.hom c)
    obtain ⟨a, -, ha⟩ := hex b c hb
    exact ⟨a, ha⟩
  set χ : P ⟶ CommRingCat.of k := Spec.preimage x with hχ
  have hx : Spec.map χ = x := Spec.map_preimage x
  by_cases h : RingHom.ker f₁.hom ≤ RingHom.ker χ.hom
  · left
    let ψ : R₁ →+* k := f₁.hom.liftOfRightInverse (Function.surjInv hs₁)
      (Function.rightInverse_surjInv hs₁) ⟨χ.hom, h⟩
    have hψ : ∀ a, ψ (f₁.hom a) = χ.hom a := fun a ↦
      f₁.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h⟩ a
    have he : f₁ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩
  · right
    have h₂ : RingHom.ker f₂.hom ≤ RingHom.ker χ.hom := by
      intro b hb
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h
      rw [RingHom.mem_ker] at ha hb ⊢
      rw [RingHom.mem_ker] at ha'
      have hab : a * b = 0 := hinj _ _ (by rw [map_mul, ha, zero_mul, map_zero])
        (by rw [map_mul, hb, mul_zero, map_zero])
      have : χ.hom a * χ.hom b = 0 := by rw [← map_mul, hab, map_zero]
      exact (mul_eq_zero.1 this).resolve_left ha'
    let ψ : R₂ →+* k := f₂.hom.liftOfRightInverse (Function.surjInv hs₂)
      (Function.rightInverse_surjInv hs₂) ⟨χ.hom, h₂⟩
    have hψ : ∀ a, ψ (f₂.hom a) = χ.hom a := fun a ↦
      f₂.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h₂⟩ a
    have he : f₂ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩

end GlobalTheory.SpecFibreProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldOfEtaleOnOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FunctionFieldEtale

theorem finiteDimensional_fractionRing_of_etale {R S K L : Type} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] (φ : R →+* S) (hφ : φ.Etale) (ψ : K →+* L)
    (h : ∀ r, ψ (algebraMap R K r) = algebraMap S L (φ r)) :
    letI := ψ.toAlgebra; FiniteDimensional K L := by
  letI : Algebra K L := ψ.toAlgebra
  letI : Algebra R S := φ.toAlgebra
  haveI : Algebra.Etale R S := hφ
  letI : Algebra R L := (ψ.comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (fun r => h r)
  haveI : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  let g : K ⊗[R] S →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K g.range :=
    Module.Finite.of_surjective g.rangeRestrict.toLinearMap g.rangeRestrict_surjective
  have hS : ∀ s : S, algebraMap S L s ∈ g.range := fun s => ⟨1 ⊗ₜ s, by simp [g]⟩
  have hinv : ∀ x ∈ g.range, x⁻¹ ∈ g.range := fun x hx =>
    Subalgebra.inv_mem_of_algebraic (A := g.range) (x := ⟨x, hx⟩)
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨x, hx⟩ : g.range)).algHom g.range.val)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) y
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ (hS a) (hinv _ (hS b))
  exact Module.Finite.of_surjective g.toLinearMap hsurj

theorem finiteDimensional_functionField_of_etale_on_open : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty →
    letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  intro M W _ _ f _ U hf hU
  have hξU : genericPoint M ∈ U :=
    ((genericPoint_spec M).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨V, hV, hfξV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f (genericPoint M))
    (U := ⊤) trivial
  let x : U := ⟨genericPoint M, hξU⟩
  have hx : x ∈ (U.ι ≫ f) ⁻¹ᵁ V := hfξV
  obtain ⟨V', hV', hxV', hV'sub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V' ≤ (U.ι ≫ f) ⁻¹ᵁ V := fun _ h => hV'sub h
  let U' : M.Opens := U.ι ''ᵁ V'
  have hU' : IsAffineOpen U' := hV'.image_of_isOpenImmersion U.ι
  have hξU' : genericPoint M ∈ U' := ⟨x, hxV', rfl⟩
  have e' : U' ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hV'sub hy
  haveI : Nonempty V := ⟨⟨_, hfξV⟩⟩
  haveI : Nonempty U' := ⟨⟨_, hξU'⟩⟩
  have het0 := HasRingHomProperty.appLE (P := @Etale) (f := U.ι ≫ f) hf ⟨V, hV⟩ ⟨V', hV'⟩ hle
  have key : (U.ι ≫ f).appLE V V' hle = f.appLE V U' e' := by
    rw [Scheme.Hom.comp_appLE]
    erw [Scheme.Opens.ι_appLE]
    rfl
  have het : (f.appLE V U' e').hom.Etale := by
    rw [← key]; exact het0
  haveI := functionField_isFractionRing_of_isAffineOpen W V hV
  haveI := functionField_isFractionRing_of_isAffineOpen M U' hU'
  refine finiteDimensional_fractionRing_of_etale (f.appLE V U' e').hom het (functionFieldMap f) ?_
  intro r
  have := functionFieldMap_algebraMap f (genericPoint M) (W.presheaf.germ V _ hfξV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  refine this.trans ?_
  rw [Scheme.Hom.germ_stalkMap_apply]
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hfξV⟩⟩
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]
  show M.presheaf.germ _ _ _ (f.app V r) =
    M.presheaf.germ U' _ hξU' (M.presheaf.map (homOfLE e').op (f.app V r))
  rw [TopCat.Presheaf.germ_res_apply]

end GlobalTheory.FunctionFieldEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FullLevel

theorem finE_mem_lev_of_isKM : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  intro D V β Λ L hΛ hr hP h hK
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hk : GlobalTheory.Member.FinCong V 1 h := by
    intro z hz
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
    exact hK.2.1 z hz
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V 1 a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (1 : ℕ) • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ 1 _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, -⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Formalism.IndefR.Lev.finE V h)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) 1 hfr (hc h hk) hc'
  have hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β := ⟨y, hy⟩
  have hU : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := GlobalTheory.LevSplit.finE_mem_UA V h
  have hb : ∀ a : Fin V.rank, a.val < L.r := fun a => lt_of_lt_of_le a.2 hr
  refine Formalism.L2.DIV.mem_lev.2 ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hU, hS, fun PP _ => ?_, fun PP _ => ?_⟩, ?_⟩
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blkOf, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blk2, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · rw [hP]; exact Subgroup.mem_top _

end GlobalTheory.CovTop.VolUp.FullLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.CoverHt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem isPreimmersion_j : IsPreimmersion V.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h


end GlobalTheory.Mean4O.CoverHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_mulVec_submatrix_mul_iff {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix m n R) (e : Equiv.Perm n) (C : Matrix n n R) (hC : IsUnit C.det) (cv : m → R) :
    (∃ a, (U.submatrix id e * C).mulVec a = cv) ↔ ∃ a, U.mulVec a = cv := by
  have hs : ∀ b, (U.submatrix id e).mulVec b = U.mulVec (b ∘ e.symm) := fun b => by
    have := Matrix.submatrix_mulVec_equiv U b (Equiv.refl m) e
    simpa using this
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(C.mulVec a) ∘ e.symm, by rw [← Matrix.mulVec_mulVec, hs]⟩
  · rintro ⟨a, rfl⟩
    have hC' : ∀ x, C.mulVec (C⁻¹.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
    refine ⟨C⁻¹.mulVec (a ∘ e), ?_⟩
    rw [← Matrix.mulVec_mulVec, hC', hs]
    congr 1
    funext i
    simp

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem cellFrames_topEigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht
  intro S _ _ y hy z hx k hz σ
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ev z _ hz).comp (cellθ κ k).toRingHom := ⟨_, rfl⟩
  have hzφ : spMap φ ≫ κ k.1 k.2 = z := hφ ▸ eq_spMap_ev k z hz
  have hxφ : y ≫ Y.j = spMap (φ.comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
    rw [← hx, ← hzφ, Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp']
    rfl
  have hV : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).V := hxφ ▸ le_preimage_comp _ (tau_le (A.V k.1).2 le_rfl)
  have hev : ev (y ≫ Y.j) (A.k k.1).V hV = φ.comp (cC A k.1) := by
    rw [ev_congr hxφ _ hV (hxφ ▸ hV)]
    exact ev_spMap_tau (A.V k.1).2 _ _
  have hM : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).M.U := (cellFrames hZ ht).inM hz hx
  have huAt : (cellFrames hZ ht).uAt k z hz σ = ((((A.k k.1).u σ).map (ev (y ≫ Y.j) _ hV)).submatrix id (k.2 σ)) *
      (cellMat (A.V k.1) σ).map φ := by
    refine Matrix.ext fun i j => ?_
    show (ev z _ hz) ((cellθ κ k) (uC A k.1 k.2 σ i j)) = _
    have e2 : ∀ x, (ev z _ hz) ((cellθ κ k) x) = φ x := fun x => by rw [hφ]; rfl
    rw [hev, e2, uC]
    exact RingHom.map_matrix_mul _ _ i j φ
  have hdet : IsUnit ((cellMat (A.V k.1) σ).map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_cellMat, map_one]
    exact isUnit_one
  refine SetLike.ext fun v => ?_
  obtain ⟨cv, rfl⟩ := (vec (A.k k.1).M.toMChart _ hM).surjective v
  refine Iff.trans ?_ ((vec_mem_eigLie _ _ hM σ cv).trans (((LowRank.pm_gen p (A.k k.1).M.toMChart σ hy hM).1 cv).trans
    ((A.k k.1).fix_iff σ _ hV hM cv))).symm
  rw [mem_initSpan, ← exists_mulVec_submatrix_mul_iff _ (k.2 σ) _ hdet, ← huAt]
  exact ⟨fun ⟨a, _, e⟩ => ⟨a, (vec (A.k k.1).M.toMChart _ hM).injective
      (((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).symm.trans e)⟩,
    fun ⟨a, e⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj),
      ((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).trans (congrArg (vec (A.k k.1).M.toMChart _ hM) e)⟩⟩

end GlobalTheory.FlagMod.FieldFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProductStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_duality_characters_fock_tensor_product : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  first | exact @GlobalTheory.howeAlg_fock_tensor | exact GlobalTheory.howeAlg_fock_tensor | (intros; apply GlobalTheory.howeAlg_fock_tensor <;> assumption)
end

