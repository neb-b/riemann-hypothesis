module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfThinBasisCocycle
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThinGlue

variable {X : Scheme.{0}}

theorem res_res {U W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {W : X.Opens} (x y : Γ(X, W)ˣ)
    (h : ∀ p ∈ W, ∃ (W' : X.Opens) (hW : W' ≤ W), p ∈ W' ∧ res hW x = res hW y) : x = y := by
  choose W' hW hp hxy using h
  ext
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => W' p.1 p.2) W (fun p => homOfLE (hW p.1 p.2)) ?_ _ _ ?_
  · intro p hpW
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hpW⟩, hp _ hpW⟩
  · intro p
    have := congrArg Units.val (hxy p.1 p.2)
    exact this

end GlobalTheory.ThinGlue

namespace GlobalTheory.ThinGlue

theorem exists_lb_frame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  intro X C _ V hV _ u hB hC
  have hE := fun T₁ T₂ => GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis X C V hV u hB hC T₁ T₂
  choose g hg using fun T₁ T₂ => (hE T₁ T₂).exists
  have key : ∀ (T₁ T₂ S : C) (a : T₁ ⟶ S) (b : T₂ ⟶ S) (h : V S ≤ V T₁ ⊓ V T₂),
      res h (g T₁ T₂) * u T₁ S a = u T₂ S b := fun T₁ T₂ S a b _ => hg T₁ T₂ S a b
  have bas2 : ∀ (i j : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S, ⟨a⟩, ⟨b⟩, hpS, hSW⟩ := hB.2 i j p W hp (hW hp).1 (hW hp).2
    exact ⟨V S, hSW, hpS, h S a b hSW⟩
  have bas3 : ∀ (i j k : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j ⊓ V k) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (_ : k ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j k W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S₀, ⟨a⟩, ⟨b⟩, hpS₀, hS₀W⟩ := hB.2 i j p W hp (hW hp).1.1 (hW hp).1.2
    obtain ⟨S, ⟨c⟩, ⟨d⟩, hpS, hSW⟩ := hB.2 S₀ k p W hp hpS₀ (hW hp).2
    exact ⟨V S, hSW, hpS, h S (a ≫ c) (b ≫ c) d hSW⟩
  have gself : ∀ T, g T T = 1 := fun T =>
    (hE T T).unique (hg T T) (fun S a b => by rw [Subsingleton.elim a b, map_one, _root_.one_mul])
  let L : LB X := ⟨C, V, g⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨t, hp, _⟩ := hB.1 p ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hp⟩
  · intro T
    show res _ (g T T) = 1
    rw [gself, map_one]
  · intro i j k
    refine bas3 i j k _ le_rfl _ _ fun S a b c hS => ?_
    show res hS (res _ (g i j) * res _ (g j k)) = res hS (res _ (g i k))
    simp only [map_mul, res_res]
    have e1 := key i j S a b (hS.trans inf_le_left)
    have e2 := key j k S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    have e3 := key i k S a c (hS.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    apply mul_right_cancel (b := u i S a)
    rw [e3, mul_comm (res _ (g i j)), _root_.mul_assoc, e1, e2]
  · refine ⟨fun T m => res (le_of_eq (inf_comm _ _)) (g m T), fun T => ?_, ?_⟩
    · intro m m'
      refine bas3 T m m' _ le_rfl _ _ fun S a b c hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (g m m') * res _ (res _ (g m' T)))
      simp only [map_mul, res_res]
      have e1 := key m T S b a (hS.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
      have e2 := key m m' S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      have e3 := key m' T S c a (hS.trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)))
      apply mul_right_cancel (b := u m S b)
      rw [e1, mul_comm (res _ (g m m')), _root_.mul_assoc, e2, e3]
    · intro T T' a m
      refine bas2 T' m _ le_rfl _ _ fun S c d hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (u T T' a) * res _ (g m T'))
      simp only [map_mul, res_res]
      have e1 := key m T S d (a ≫ c) (hS.trans (le_inf inf_le_right ((inf_le_left.trans (hV a)))))
      have e2 := key m T' S d c (hS.trans (le_inf inf_le_right inf_le_left))
      have e3 := hC a c
      apply mul_right_cancel (b := u m S d)
      rw [e1, _root_.mul_assoc, e2, e3]

end GlobalTheory.ThinGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimT
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LinearCodimTwo

open GlobalTheory.ProjSpace GlobalTheory.Adelic

theorem exists_linear_closedImmersion_two_le_ringKrullDim_stalk :
    ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧
      ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧
      ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  intro F _ N
  have h1 : Function.Injective (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := Fin.castSucc_injective _
  have h2 : Function.Injective (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := Fin.castSucc_injective _
  let ℓ₁ : PSpace F N ⟶ PSpace F (N + 1) := linearι F h1
  let ℓ₂ : PSpace F (N + 1) ⟶ PSpace F (N + 2) := linearι F h2
  have linear_str (A B : ℕ) {e : Fin (A + 1) → Fin (B + 1)}
      (he : Function.Injective e) : linearι F he ≫ PSpace.str F B = PSpace.str F A := by
    refine (Proj.mapAffineOpenCover (killHom F he)
      (irrelevant_le_map_of_surjective _ (killHom_surjective F he))).openCover.hom_ext _ _ fun s => ?_
    have key : ∀ (d : ℕ) (hd : 0 < d) (s : MvPolynomial (Fin (B + 1)) F) (hs : s ∈ grading F B d),
        Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ linearι F he ≫ PSpace.str F B =
          Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ PSpace.str F A := by
      intro d hd s hs
      rw [linearι, Proj.awayι_comp_map_assoc _ _ hd s hs, PSpace.str, PSpace.str, Proj.awayι_toSpecZero_assoc,
        Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
      refine (congrArg HomogeneousLocalization.val (HomogeneousLocalization.Away.map_mk (killHom F he) s hs 0 (MvPolynomial.C r)
        ((zero_smul ℕ d).symm ▸ MvPolynomial.isHomogeneous_C _ r))).trans ?_
      rw [HomogeneousLocalization.Away.val_mk]
      exact congrArg (Localization.mk · _) (MvPolynomial.killCompl_C he r)
    exact key _ s.1.2 _ s.2.2
  refine ⟨ℓ₁ ≫ ℓ₂, inferInstance, by rw [Category.assoc, linear_str _ _ h2, linear_str _ _ h1], fun y => ?_⟩
  have last1 : Fin.last (N + 1) ∉ Set.range (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have last2 : Fin.last (N + 2) ∉ Set.range (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have n1 : ℓ₁ y ∉ chart F (N + 1) (Fin.last (N + 1)) := fun h => by
    have : y ∈ ℓ₁ ⁻¹ᵁ chart F (N + 1) (Fin.last (N + 1)) := h
    rw [linearι_preimage_chart_of_notMem F h1 last1] at this
    exact this
  have n2 (z : PSpace F (N + 1)) : ℓ₂ z ∉ chart F (N + 2) (Fin.last (N + 2)) := fun h => by
    have : z ∈ ℓ₂ ⁻¹ᵁ chart F (N + 2) (Fin.last (N + 2)) := h
    rw [linearι_preimage_chart_of_notMem F h2 last2] at this
    exact this
  have s1 : projSys.gen F (N + 1) ⤳ ℓ₁ y :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₁ y).asHomogeneousIdeal from bot_le))
  have s2 : projSys.gen F (N + 2) ⤳ ℓ₂ (projSys.gen F (N + 1)) :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₂ (projSys.gen F (N + 1))).asHomogeneousIdeal from bot_le))
  have lt1 : ℓ₂ (ℓ₁ y) < ℓ₂ (projSys.gen F (N + 1)) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 (s1.map ℓ₂.continuous)) fun h => ?_
    have := ℓ₂.isClosedEmbedding.injective ((Scheme.le_iff_specializes.1 h).antisymm (s1.map ℓ₂.continuous)).eq
    exact n1 (this ▸ projSys.gen_mem F (N + 1) (Fin.last (N + 1)))
  have lt2 : ℓ₂ (projSys.gen F (N + 1)) < projSys.gen F (N + 2) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 s2) fun h => ?_
    have e : ℓ₂ (projSys.gen F (N + 1)) = projSys.gen F (N + 2) := ((Scheme.le_iff_specializes.1 h).antisymm s2).eq
    exact n2 _ (by rw [e]; exact projSys.gen_mem F (N + 2) (Fin.last (N + 2)))
  have hc : (2 : ℕ∞) ≤ Order.coheight (ℓ₂ (ℓ₁ y)) := by
    have a := Order.coheight_add_one_le lt1
    have b := Order.coheight_add_one_le lt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (projSys.gen F (N + 2)) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight (ℓ₂ (projSys.gen F (N + 1))) + 1 := by gcongr
      _ ≤ _ := a
  rw [Scheme.Hom.comp_apply, ringKrullDim_stalk_eq_coheight]
  have := WithBot.coe_le_coe.2 hc
  simpa using this

end GlobalTheory.LinearCodimTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulNormLeOne
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem isOpen_of_padicLattice {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    (A : AddSubgroup V) (hA : ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ v ∈ A, c • v ∈ A)
    (hN : ∀ v : V, ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ A) : IsOpen (A : Set V) := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[p] V
  let b := Module.finBasis ℚ_[p] V
  choose N hN' using fun i => hN (b i)
  set M := ∑ i, N i with hMdef
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := Padic.norm_p_lt_one.le
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hb : ∀ i, (p : ℚ_[p]) ^ M • b i ∈ A := by
    intro i
    have hle : N i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact hA _ (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1) _ (hN' i)
  have hpos : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  let U : Set V := ⋂ i, (fun v => b.coord i v) ⁻¹' Metric.closedBall 0 ‖(p : ℚ_[p]) ^ M‖
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hpos.ne').preimage
      (IsModuleTopology.continuous_of_linearMap (b.coord i))
  have hUA : U ⊆ A := by
    intro v hv
    simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hv
    rw [← b.sum_repr v]
    refine A.sum_mem fun i _ => ?_
    have : b.repr v i • b i = (b.repr v i / (p : ℚ_[p]) ^ M) • ((p : ℚ_[p]) ^ M • b i) := by
      rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    rw [this]
    refine hA _ ?_ _ (hb i)
    rw [norm_div, div_le_one hpos]
    exact hv i
  have h0 : (0 : V) ∈ U := by
    simp [U, hpos.le]
  exact AddSubgroup.isOpen_of_mem_nhds A (Filter.mem_of_superset (hU.mem_nhds h0) hUA)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_pow_smul_norm_le_one (z : PadicAlgCl p) : ∃ N : ℕ, ‖(p : ℚ_[p]) ^ N • z‖ ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hz') (Padic.norm_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [Algebra.smul_def, norm_mul, map_pow, norm_pow, PadicAlgCl.norm_extends]
  calc ‖(p : ℚ_[p])‖ ^ N * ‖z‖ ≤ ‖z‖⁻¹ * ‖z‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ hz'.ne'

theorem algebraMap_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) :
    algebraMap ℚ_[p] (KQ p K r) c ∈ intKQ p K r := by
  have hK : algebraMap ℚ_[p] K c ∈ GlobalTheory.LKLoc.intK p K := by
    show algebraMap K (PadicAlgCl p) (algebraMap ℚ_[p] K c) ∈ Obar p
    rw [← IsScalarTower.algebraMap_apply, mem_Obar_iff]
    exact (PadicAlgCl.norm_extends (p := p) c).le.trans hc
  exact Subring.subset_closure (Or.inl ⟨⟨_, hK⟩, rfl⟩)

theorem smul_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) (v : KQ p K r) (hv : v ∈ intKQ p K r) :
    c • v ∈ intKQ p K r := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intKQ p K r c hc) hv

theorem exists_pow_smul_mem_intKQ (r : ℕ) (v : KQ p K r) :
    ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ intKQ p K r := by
  have hp1 : ∀ k : ℕ, ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
  induction (v : K ⊗[ℚ_[p]] Qr p r) using TensorProduct.induction_on with
  | zero => exact ⟨0, by show (p : ℚ_[p]) ^ 0 • (0 : KQ p K r) ∈ intKQ p K r; rw [smul_zero]; exact zero_mem _⟩
  | tmul x y =>
    obtain ⟨N₁, h₁⟩ := exists_pow_smul_norm_le_one p (x : PadicAlgCl p)
    obtain ⟨N₂, h₂⟩ := exists_pow_smul_norm_le_one p (y : PadicAlgCl p)
    have hx : (p : ℚ_[p]) ^ N₁ • x ∈ GlobalTheory.LKLoc.intK p K := by
      show (((p : ℚ_[p]) ^ N₁ • x : K) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₁
    have hy : (p : ℚ_[p]) ^ N₂ • y ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
      show (((p : ℚ_[p]) ^ N₂ • y : Qr p r) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₂
    refine ⟨N₁ + N₂, ?_⟩
    have key : ((p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y) : K ⊗[ℚ_[p]] Qr p r) =
        (((p : ℚ_[p]) ^ N₁ • x) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : ℚ_[p]) ^ N₂ • y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul_smul, pow_add]
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) =
        inclK p K r ((p : ℚ_[p]) ^ N₁ • x) * inclQ p K r ((p : ℚ_[p]) ^ N₂ • y) := key
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hx⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, hy⟩, rfl⟩))
  | add a b ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b) =
        (p : ℚ_[p]) ^ N₂ • ((p : ℚ_[p]) ^ N₁ • a) + (p : ℚ_[p]) ^ N₁ • ((p : ℚ_[p]) ^ N₂ • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm N₂ N₁]
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact add_mem (smul_mem_intKQ p K r _ (hp1 _) _ h₁) (smul_mem_intKQ p K r _ (hp1 _) _ h₂)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intKQ (hK : FiniteDimensional ℚ_[p] K) (r : ℕ) (hr : 0 < r) :
    IsOpen (intKQ p K r : Set (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact isOpen_of_padicLattice (intKQ p K r).toAddSubgroup
    (fun c hc v hv => smul_mem_intKQ p K r c hc v hv) (exists_pow_smul_mem_intKQ p K r)

theorem mem_Kres_iff (n r : ℕ) (g : GL (Fin n) (KQ p K r)) :
    g ∈ Kres p K n r ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r ∧
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    exact ⟨((h : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2,
      (((h⁻¹ : GL (Fin n) (intKQ p K r)) : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2⟩
  · intro H
    let A : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).1⟩
    let B : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).2⟩
    have hA : A.map (intKQ p K r).subtype = (g : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hB : B.map (intKQ p K r).subtype =
        ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intKQ p K r) => M.map (intKQ p K r).subtype :=
      Matrix.map_injective Subtype.val_injective
    have h1 : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.mul_inv g)
    have h2 : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, h1, h2⟩, Units.ext hA⟩

theorem isOpen_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → IsOpen (Kres p K n r : Set (GL (Fin n) (KQ p K r))) := by
  intro p _ K hK n r hr
  have hS := isOpen_intKQ p K hK r hr
  have e : (Kres p K n r : Set (GL (Fin n) (KQ p K r))) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin n) (KQ p K r) => (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _) ∩
       (fun g : GL (Fin n) (KQ p K r) =>
          ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact mem_Kres_iff p K n r g
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (hS.preimage (Units.continuous_val.matrix_elem i j)).inter
    (hS.preimage (Units.continuous_coe_inv.matrix_elem i j))

end GlobalTheory.LKRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbelianQuotientField

open AffineQuotient AbelianQuotient


set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → ∃ (A' : Over (Sp K)) (_ : GrpObj A'), IsAbelianScheme A' ∧ ∃ q : A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit H) q η[A'] := by
  intro K _ _ A _ hA H _ i hi hmono hfin
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have hflat : Flat H.hom := inferInstance
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main K H hfin hflat
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsFinite (𝟙 A ^ N : A ⟶ A).left := _root_.GlobalTheory.MulFinite.isFinite_mul K A hA N hN
  have : IsFinite H.hom := hfin
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra K H
  have hi' : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal)
    (e.hom ≫ i) (𝟙 A ^ N) (by
      rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
        ← comp_pow i, hi', comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  have : Flat q.left := h₃
  have : Surjective q.left := h₄
  have : IsFinite q.left := h₂
  have : IsFinite π.left := h₁
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h₂, h₃, h₄, hker⟩
  have hπ : π.left ≫ A.hom = Q.hom := Over.w π
  have : IsSeparated Q.hom := by rw [← hπ]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← hπ]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbelianQuotientField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalOfZariskiSheafOpenCharts
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_universal_of_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) := by
  intro F hsep hglue Ix U x inj hW cov
  have hF : Presieve.IsSheaf Scheme.zariskiTopology F := _root_.GlobalTheory.isSheaf_of_local_glue F hsep hglue
  let W : ∀ (_ : Ix) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens :=
    fun i Z y => Classical.choose (hW i Z y)
  have hWs : ∀ i (Z : Scheme.{0}) (y : F.obj (op Z)) (Y : Scheme.{0}) (a : Y ⟶ Z),
      (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W i Z y :=
    fun i Z y => Classical.choose_spec (hW i Z y)
  have hrep : F.IsRepresentable := by
    refine GeneratorFunctor.isRepresentable_of_charts F hF U x W ?_ ?_ ?_
    · intro j Z y Z' a
      rw [Set.range_subset_iff]
      refine ((hWs j Z y Z' a).symm.trans ?_)
      exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩
    · intro j Z g g' h
      exact inj j Z g g' h
    · intro Z y z
      obtain ⟨i, Y, a, u, ⟨q, rfl⟩, h⟩ := cov Z y z
      exact ⟨i, (hWs i Z y Y a).1 ⟨u, h⟩ q⟩
  refine ⟨F.reprX, F.reprx, fun T y => ?_⟩
  refine ⟨F.representableBy.homEquiv.symm y, ?_, ?_⟩
  · have := F.representableBy.homEquiv_eq (F.representableBy.homEquiv.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro g hg
    apply F.representableBy.homEquiv.injective
    rw [Equiv.apply_symm_apply, F.representableBy.homEquiv_eq, ← hg]
    rfl

end GlobalTheory
end

