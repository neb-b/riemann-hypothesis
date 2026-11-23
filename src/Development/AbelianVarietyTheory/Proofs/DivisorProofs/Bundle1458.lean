module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTDim

theorem card_torsion_of_ev {La Q : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] [Group Q]
    (ev : La → Q) (ℓ : ℕ) (hℓ : 0 < ℓ) (hadd : ∀ x y, ev (x + y) = ev x * ev y)
    (hker : ∀ x, ev x = 1 ↔ ∃ y, x = ℓ • y) (honto : ∀ q, q ^ ℓ = 1 ↔ ∃ x, ev x = q) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ La := by
  haveI : NeZero ℓ := ⟨by omega⟩
  let f : La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (ev x)) fun x y => by
    rw [hadd]; rfl
  let r := Module.finrank ℤ La
  let b := Module.finBasis ℤ La
  let g : La →+ (Fin r → ZMod ℓ) := AddMonoidHom.mk' (fun x i => ((b.repr x i : ℤ) : ZMod ℓ)) fun x y => by
    ext i; simp
  have hg : Function.Surjective g := by
    intro v
    choose w hw using fun i => ZMod.intCast_surjective (v i)
    refine ⟨b.equivFun.symm w, funext fun i => ?_⟩
    show ((b.repr (b.equivFun.symm w) i : ℤ) : ZMod ℓ) = v i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hw]
  have hk : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    change Additive.ofMul (ev x) = 0 ↔ _
    rw [ofMul_eq_zero, hker]
    constructor
    · rintro ⟨y, rfl⟩
      ext i
      simp [g]
    · intro h
      have hd : ∀ i, (ℓ : ℤ) ∣ b.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun h i
      choose c hc using hd
      refine ⟨b.equivFun.symm c, b.ext_elem fun i => ?_⟩
      have hcy : b.repr (b.equivFun.symm c) i = c i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [map_nsmul, Finsupp.smul_apply, hcy, hc i, nsmul_eq_mul]
  have e1 : Nat.card {q : Q // q ^ ℓ = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun q => ?_)
    rw [honto, AddMonoidHom.mem_range]
    rfl
  rw [e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hk).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_eq_fintype_card, r]

variable {p : ℕ} [Fact p.Prime]

theorem relDim {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) : SmoothOfRelativeDimension D.g o.A.hom := by
  have := o.ab.smooth
  choose n W hW hd using H1.exists_dim o.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension D.g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := AlgebraicClosure (o.A.left.residueField y)
  let z : Sp k ⟶ o.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (o.A.left.residueField y) k)) ≫ o.A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ o.A.hom
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let B := (Over.pullback x).obj o.A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj x o.A o.ab
  obtain ⟨m, hm⟩ := GlobalTheory.AbVarRelDim.exists_relDim k B hB
  let z' : Sp k ⟶ pullback o.A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst o.A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ o.A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hℓp : (p + 1).Coprime p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have hℓk : ((p + 1 : ℕ) : k) ≠ 0 := by
    intro h0
    have := (b.unit (p + 1) hℓp).map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨I, -⟩ := o.geom k x β hβ
  have c1 := card_torsion_of_ev (I.ev (p + 1)) (p + 1) (by omega) (I.add (p + 1)) (I.ker (p + 1) (by omega) hℓp)
    (I.onto (p + 1) (by omega) hℓp)
  have c2 := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B m (p + 1) hB hm hℓk
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback o.A x) (𝟙 (Sp k)) x
    (Category.id_comp x).symm
  have c3 : Nat.card {q : 𝟙_ (Over (Sp k)) ⟶ B // q ^ (p + 1) = 1} =
      Nat.card {q : Over.mk x ⟶ o.A // q ^ (p + 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun q => by
      change q ^ (p + 1) = 1 ↔ e q ^ (p + 1) = 1
      rw [← map_pow, map_eq_one_iff e e.injective])
  have hr := D.rankLa
  have h2 : 2 * m = Module.finrank ℤ D.La :=
    Nat.pow_right_injective (by have := (Fact.out : p.Prime).two_le; omega : 2 ≤ p + 1) (by
      show (p + 1) ^ (2 * m) = (p + 1) ^ Module.finrank ℤ D.La
      rw [← c2, c3, c1])
  have hg : D.g = m := by
    show D.m * D.n * Module.finrank ℚ D.F / 2 = m
    omega
  rw [hg, ← e₁]
  exact hd y

theorem relDim_and_isLB : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
  fun _ _ _ _ _ _ _ _ _ o => ⟨relDim o, LB.isLB_pull o.isLB _⟩

end GlobalTheory.HTDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
section
open NumberField GlobalTheory.CuspRep

noncomputable section

section LieGrowth

open MeasureTheory Topology Matrix GroundTheory.Automorphic

namespace GlobalTheory.CuspStab.LieGrowth

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

end GlobalTheory.CuspStab.LieGrowth

end LieGrowth

namespace GlobalTheory.CuspStab

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := by
  let S := Subalgebra.centralizer ℂ ({finRep E a k} : Set (Module.End ℂ (Sm E a)))
  have hL : ∀ X, lie E a X ∈ S := fun X T hT => by
    rw [Set.mem_singleton_iff.1 hT]; exact (lie_rt_fin X k).symm
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have hS : Zalg E a ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hS hz (finRep E a k) rfl).symm

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖, by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_mul {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := height_mul_le c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

end GlobalTheory.CuspStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfUnramifiedAbelianSchemeModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodDescW
set_option autoImplicit false

section Sq2
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}

noncomputable def sq2 (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left

theorem grpSchemeSquareProductMap_comp_fst (w : φ ≫ G.hom = G'.hom ≫ f) : sq2 w ≫ (fst G G).left = (fst G' G').left ≫ φ := by
  rw [sq2, ← Over.comp_left, lift_fst]; rfl

theorem grpSchemeSquareProductMap_comp_snd (w : φ ≫ G.hom = G'.hom ≫ f) : sq2 w ≫ (snd G G).left = (snd G' G').left ≫ φ := by
  rw [sq2, ← Over.comp_left, lift_snd]; rfl

theorem grpSchemeSquareProductMap_eq_tensorHom (w : φ ≫ G.hom = G'.hom ≫ f) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq2 w :=
  Over.tensorObj_ext _ _ (h.1.trans (grpSchemeSquareProductMap_comp_fst w).symm) (h.2.trans (grpSchemeSquareProductMap_comp_snd w).symm)

theorem isPullback_squareMapOfCompatibleMorphism (w : φ ≫ G.hom = G'.hom ≫ f) (h : IsPullback φ G'.hom G.hom f) :
    IsPullback (sq2 w) (G' ⊗ G').hom (G ⊗ G).hom f :=
  CM.TripleModel.isPullback_tensor h h (grpSchemeSquareProductMap_comp_fst w) (grpSchemeSquareProductMap_comp_snd w)

theorem grpSchemeSquareProductMap_comp {T V : Scheme.{0}} {t : S' ⟶ T} {u : T ⟶ V} {v : S ⟶ V} {H : Over T} {X : Over V}
    {ψ : G'.left ⟶ H.left} {α : H.left ⟶ X.left} {β : G.left ⟶ X.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) (w₁ : ψ ≫ H.hom = G'.hom ≫ t) (w₂ : α ≫ X.hom = H.hom ≫ u)
    (w₃ : β ≫ X.hom = G.hom ≫ v) (h : ψ ≫ α = φ ≫ β) : sq2 w₁ ≫ sq2 w₂ = sq2 w ≫ sq2 w₃ := by
  apply Over.tensorObj_ext
  · change sq2 w₁ ≫ sq2 w₂ ≫ (fst X X).left = sq2 w ≫ sq2 w₃ ≫ (fst X X).left
    rw [grpSchemeSquareProductMap_comp_fst, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, grpSchemeSquareProductMap_comp_fst,
      Category.assoc, Category.assoc, h]
  · change sq2 w₁ ≫ sq2 w₂ ≫ (snd X X).left = sq2 w ≫ sq2 w₃ ≫ (snd X X).left
    rw [grpSchemeSquareProductMap_comp_snd, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, grpSchemeSquareProductMap_comp_snd,
      Category.assoc, Category.assoc, h]
end Sq2

section Sq
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem mul_sq (h : IsGrpPullback G' G f φ) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h₁ : φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ) (h₂ : φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    φ₂ ≫ μ[G].left = μ[G'].left ≫ φ := by
  have e := h.2 _ (fst G' G') (snd G' G') (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) rfl rfl
  have e' : (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left = φ₂ :=
    Over.tensorObj_ext _ _
      (by change (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ fst G G).left = φ₂ ≫ (fst G G).left
          rw [lift_fst]; exact h₁.symm)
      (by change (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ snd G G).left = φ₂ ≫ (snd G G).left
          rw [lift_snd]; exact h₂.symm)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left, e'] at e
  exact e

theorem inv_sq (h : IsGrpPullback G' G f φ) : φ ≫ ι[G].left = ι[G'].left ≫ φ := by
  have e : (pushPt h.1.w ((𝟙 G')⁻¹)).left = ((pushPt h.1.w (𝟙 G'))⁻¹).left :=
    congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Over.comp_left] at e
  change (𝟙 G' ≫ ι[G']).left ≫ φ = (𝟙 G'.left ≫ φ) ≫ ι[G].left at e
  simpa using e.symm

theorem one_sq (h : IsGrpPullback G' G f φ) : f ≫ η[G].left = η[G'].left ≫ φ := by
  have e : (pushPt h.1.w (1 : 𝟙_ (Over S') ⟶ G')).left = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  rw [Hom.one_def, Hom.one_def, Over.comp_left] at e
  change (toUnit (𝟙_ (Over S')) ≫ η[G']).left ≫ φ = _ at e
  simp only [Over.comp_left, Over.toUnit_left] at e
  simpa using e.symm
end Sq

theorem hasGoodReduction_of_model : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∀ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) → IsPullback g G.hom X.hom (spMap (algebraMap R W)) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g → HasGoodReduction R K A := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax A _ _ hA G _ hG eI he X a g ha hg hcomp
  have : IsMonHom eI.hom := he
  obtain ⟨hfl, hsu⟩ := _root_.GlobalTheory.flat_surjective_spMap_of_dvr R K W K' hmax
  have hsq := _root_.GlobalTheory.spec_fraction_field_isPullback_of_unramified R K W K' hmax
  have : QuasiCompact (spMap (algebraMap R W)) := inferInstance
  have : QuasiCompact (spMap (algebraMap R K)) := inferInstance
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := schemeTheoreticallyDominant_fractionField R K
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap (algebraMap R W)) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hXs : Smooth X.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) hg.flip hj hG.smooth
  have hXp : IsProper X.hom := GrpFlatDesc.isProper_of_isPullback hg
  have hXc : GeometricallyConnected X.hom := GrpFlatDesc.geometricallyConnected_of_isPullback hg
  have hX2 : Flat (X ⊗ X).hom := inferInstanceAs (Flat (pullback.fst X.hom X.hom ≫ X.hom))

  have hρ : IsGrpPullback ((Over.pullback (spMap (algebraMap W K'))).obj G) G (spMap (algebraMap W K')) (pullback.fst G.hom (spMap (algebraMap W K'))) := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have hψ : IsGrpPullback ((Over.pullback (spMap (algebraMap W K'))).obj G) A (spMap (algebraMap K K')) (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) :=
    ((isGrpPullback_of_iso eI).comp (isGrpPullback_pullback A (spMap (algebraMap K K')))).congr (Category.id_comp _) rfl
  have hc : (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
    rw [Category.assoc]; exact hcomp

  obtain ⟨hm, hm1, hm2, hm3⟩ := _root_.GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom (X ⊗ X).hom (G ⊗ G).hom (sq2 hg.w)
    (isPullback_squareMapOfCompatibleMorphism hg.w hg) (A ⊗ A).hom (sq2 ha.w) (isPullback_squareMapOfCompatibleMorphism ha.w ha)
    ((Over.pullback (spMap (algebraMap W K'))).obj G ⊗ (Over.pullback (spMap (algebraMap W K'))).obj G).hom (sq2 hρ.1.w) (sq2 hψ.1.w)
    (isPullback_squareMapOfCompatibleMorphism hρ.1.w hρ.1) (isPullback_squareMapOfCompatibleMorphism hψ.1.w hψ.1)
    (grpSchemeSquareProductMap_comp hρ.1.w hψ.1.w ha.w hg.w hc) (μ[G].left ≫ g) (μ[A].left ≫ a)
    (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]) (by
      rw [← Category.assoc, mul_sq hρ _ (grpSchemeSquareProductMap_comp_fst _) (grpSchemeSquareProductMap_comp_snd _), Category.assoc, ← hc, ← Category.assoc,
        ← mul_sq hψ _ (grpSchemeSquareProductMap_comp_fst _) (grpSchemeSquareProductMap_comp_snd _), Category.assoc])

  obtain ⟨hi, hi1, hi2, hi3⟩ := _root_.GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom X.hom G.hom g hg A.hom a ha
    ((Over.pullback (spMap (algebraMap W K'))).obj G).hom (pullback.fst G.hom (spMap (algebraMap W K'))) (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) hρ.1 hψ.1 hc
    (ι[G].left ≫ g) (ι[A].left ≫ a) (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]) (by
      rw [← Category.assoc, inv_sq hρ, Category.assoc, ← hc, ← Category.assoc, ← inv_sq hψ, Category.assoc])

  obtain ⟨hu, hu1, hu2, hu3⟩ := _root_.GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom (𝟙 (Sp R)) (𝟙 (Sp W)) (spMap (algebraMap R W))
    (IsPullback.of_vert_isIso ⟨by simp⟩) (𝟙 (Sp K)) (spMap (algebraMap R K)) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (𝟙 (Sp K')) (spMap (algebraMap W K')) (spMap (algebraMap K K')) (IsPullback.of_vert_isIso ⟨by simp⟩) (IsPullback.of_vert_isIso ⟨by simp⟩) hsq.w.symm
    (η[G].left ≫ g) (η[A].left ≫ a) (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]; rfl) (by
      rw [← Category.assoc, one_sq hρ, Category.assoc, ← hc, ← Category.assoc, ← one_sq hψ, Category.assoc])

  let m : X ⊗ X ⟶ X := Over.homMk hm hm3
  let i : X ⟶ X := Over.homMk hi hi3
  let e₀ : 𝟙_ (Over (Sp R)) ⟶ X := Over.homMk hu hu3
  obtain ⟨_, hμ, -, -, hcX, -⟩ := GrpFlatDesc.grpObj_of_flat_cover (spMap (algebraMap R W)) X G g hg m i e₀
    (fun φ₂ h₂ => by rw [grpSchemeSquareProductMap_eq_tensorHom hg.w h₂]; exact hm1) hi1 hu1
  have hXab : IsAbelianScheme X := ⟨hcX, hXs, hXp, hXc⟩
  have hAX : IsGrpPullback A X (spMap (algebraMap R K)) a := by
    refine ⟨ha, fun T x y x₀ y₀ hx hy => ?_⟩
    obtain rfl : x₀ = pushPt ha.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt ha.w y := Over.OverMorphism.ext hy
    have := GrpDense.pushPt_mul ha.w (m := μ[X]) (fun φ₂ h₂ => by rw [grpSchemeSquareProductMap_eq_tensorHom ha.w h₂, hμ]; exact hm2) x y
    rw [Hom.mul_def, this]
    rfl
  obtain ⟨e', he', -⟩ := grpPullback_iso (isGrpPullback_pullback X (spMap (algebraMap R K))) hAX
  exact ⟨X, inferInstance, hXab, e', he'⟩

end GlobalTheory.GoodDescW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensor
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_fin_add_add {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin (n + n) → M) :
    ∑ d, f d = ∑ d, f (finSumFinEquiv (Sum.inl d)) + ∑ d, f (finSumFinEquiv (Sum.inr d)) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]

theorem hOF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (botR x) (botR y) := by
  simp only [hOF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sum_fin_add_add (n := nT), dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, dbl,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    mul_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, topR, botR, Function.comp_apply, id, Finset.sum_sub_distrib]
  ring

theorem hOF_neg_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp only [hOF, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOHF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y =
      symplOHF σ JS JT ξ₀ (topR x) (topR y) - symplOHF σ JS JT ξ₀ (-botR x) (-botR y) := by
  simp only [symplOHF, symplOF, hOF_dblG, hOF_neg_neg, mul_sub, map_sub]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (h : ∀ x, ‖ψ x‖ = 1) (s : AF F) : conj (ψ s) = ψ (-s) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h s]
  simp

theorem heisOF_dblG_deltaT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn : ∀ x, ‖B.ψ x‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.DblHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelForm

theorem coefwise_del_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {v : V n} (g : ι → V n → ℂ) (Q : ι → V n → Alt n)
    (hg : ∀ k, DifferentiableAt ℝ (g k) v) (hQ : ∀ k S, DifferentiableAt ℝ (fun w => (bas n).repr (Q k w) S) v)
    (ξ : V n) :
    coefwise (fun f => del f v ξ) (fun w => ∑ k, g k w • Q k w) =
      ∑ k, (del (g k) v ξ • Q k v + g k v • coefwise (fun f => del f v ξ) (Q k)) := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (∑ k, g k x • Q k x) S) = fun x => ∑ k, g k x * (bas n).repr (Q k x) S :=
    funext fun x => by simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [FormMul.repr_coefwise, e,
    del_sum (A := fun k x => g k x * (bas n).repr (Q k x) S) (fun k _ => (hg k).mul (hQ k S)),
    ContinuousLinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [del_mul (hg k) (hQ k S), map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    FormMul.repr_coefwise, smul_eq_mul, smul_eq_mul, add_comm]

theorem delAt_sum_smul : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) →
    (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) →
    GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v =
      ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  intro n ι _ v g Q hg hQ
  simp only [delAt, dOne, coefwise_del_sum_smul g Q hg hQ, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_add,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  exact Finset.sum_comm

end GlobalTheory.CxForm.DelForm
end
end

