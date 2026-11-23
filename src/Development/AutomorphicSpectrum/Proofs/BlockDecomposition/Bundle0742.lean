module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineIdealLocusCriterionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_ideal_locus_criterion : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g)) →
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.Glue.exists_closed_subscheme | exact GlobalTheory.CompanionTheory.TrivLoc.Glue.exists_closed_subscheme | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.Glue.exists_closed_subscheme <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapComposition
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_bc_comp (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') :
    ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  obtain ⟨α, hα₁, hα₂, hα₃⟩ := m
  obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := n
  refine ⟨⟨fun T => (β T).comp (α T), ?_, ?_, ?_⟩, fun T b => rfl⟩
  · intro T T' φ b
    simp only [RingHom.comp_apply, hα₁, hβ₁]
  · intro T r b
    simp only [RingHom.comp_apply, hα₂, hβ₂, ← IsScalarTower.algebraMap_apply]
  · intro T
    obtain ⟨e₁, he₁⟩ := hα₃ T
    obtain ⟨e₂, he₂⟩ := hβ₃ T
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' (F.obj T)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S' S') e₁).trans e₂), fun b => ?_⟩
    simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, he₁, he₂,
      RingHom.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

theorem bc_self (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    ∃ l : BC F F, ∀ T b, l.α T b = b :=
  ⟨⟨fun _ => RingHom.id _, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ => ⟨TensorProduct.lid R _, fun b => by simp [TensorProduct.lid_tmul]⟩⟩, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem coboundary_cup0 {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {n : ℕ}
    (f : Cn F 0) (z : Cn F n) :
    dn F n (cup0 F f z) = cup1 F (dn F 0 f) z + cup0 F f (dn F n z) := by
  have hs : ∀ i : Fin (n + 1),
      (Fin.succAboveOrderEmb i.succ).toOrderHom.comp (vert0 n) = vert0 (n + 1) := by
    intro i
    ext j
    exact congrArg Fin.val (Fin.succ_succAbove_zero i)
  have h0 : (Fin.succAboveOrderEmb (0 : Fin (n + 2))).toOrderHom.comp (vert0 n) =
      (front n).comp (Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom := by
    ext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have h1 : (front n).comp (Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom = vert0 (n + 1) := by
    ext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have hL : dn F n (cup0 F f z) =
      act F (front n) (cof F 0 0 f) * cof F n 0 z +
        ∑ i : Fin (n + 1), ((-1 : R) ^ ((i : ℕ) + 1)) •
          (act F (vert0 (n + 1)) f * cof F n i.succ z) := by
    simp only [dn, cup0, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_succ]
    simp only [cof_eq, act_mul, ← act_comp, hs, h0, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hd0 : dn F 0 f = cof F 0 0 f - cof F 0 1 f := by
    simp [dn, Fin.sum_univ_two, sub_eq_add_neg]
  have hR : dn F n z = cof F n 0 z +
      ∑ i : Fin (n + 1), ((-1 : R) ^ ((i : ℕ) + 1)) • cof F n i.succ z := by
    simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hf1 : act F (front n) (cof F 0 1 f) = act F (vert0 (n + 1)) f := by
    rw [cof_eq, ← h1, act_comp]
  have hb : act F (back n) z = cof F n 0 z := rfl
  rw [hL, cup1, hd0, map_sub, hf1, hb, cup0, hR, sub_mul, mul_add, Finset.mul_sum]
  simp only [mul_smul_comm]
  abel

end GlobalTheory.CompanionTheory.HopfLe
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe.DnCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

abbrev dl (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) →o Fin (n + 2) := (Fin.succAboveOrderEmb i).toOrderHom

def incl (n : ℕ) : Fin 3 →o Fin (n + 3) := ⟨Fin.castLE (by omega), fun _ _ h ↦ h⟩

private theorem sum_fin_add_two_eq_zero_add_sum_succ {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M) :
    ∑ i, f i = f 0 + ∑ k : Fin (m + 1), f k.succ :=
  Fin.sum_univ_succ f

private theorem sum_fin_add_two_eq_zero_add_one_add_sum {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M) :
    ∑ i, f i = f 0 + f 1 + ∑ k : Fin m, f k.succ.succ :=
  ((Fin.sum_univ_succ f).trans
    (congrArg _ (Fin.sum_univ_succ fun i : Fin (m + 1) => f i.succ))).trans (add_assoc _ _ _).symm

theorem dl_spec (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((j : ℕ) < i ∧ (dl n i j : ℕ) = j) ∨ ((i : ℕ) ≤ j ∧ (dl n i j : ℕ) = j + 1) := by
  have hv : GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n i j = i.succAbove j := by
    simp only [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [hv]
  rcases Nat.lt_or_ge (j : ℕ) i with h | h
  · left
    refine ⟨h, ?_⟩
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h),
      Fin.coe_castSucc]
  · right
    refine ⟨h, ?_⟩
    rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.coe_castSucc]; exact h),
      Fin.val_succ]

theorem front_val (n : ℕ) (j : Fin 2) : (front n j : ℕ) = j := rfl

theorem back_val (n : ℕ) (j : Fin (n + 1)) : (back n j : ℕ) = j + 1 := by
  have hv : GlobalTheory.CompanionTheory.HopfLe.back n j = Fin.succAbove 0 j := by
    simp only [GlobalTheory.CompanionTheory.HopfLe.back, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [hv, Fin.succAbove_of_le_castSucc _ _ (by simp), Fin.val_succ]

theorem incl_val (n : ℕ) (j : Fin 3) : (incl n j : ℕ) = j := rfl

theorem dl_front_high (n : ℕ) (k : Fin (n + 1)) : (dl (n + 1) k.succ.succ).comp (front n) = front (n + 1) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have hj := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *
  omega

theorem dl_back_high (n : ℕ) (k : Fin (n + 1)) :
    (dl (n + 1) k.succ.succ).comp (back n) = (back (n + 1)).comp (dl n k.succ) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n k.succ j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *
  omega

theorem dl_back_zero (n : ℕ) : (dl (n + 1) 0).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *
  omega

theorem dl_back_one (n : ℕ) : (dl (n + 1) 1).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero, Fin.val_one] at *
  omega

theorem dl_front_zero (n : ℕ) : (dl (n + 1) 0).comp (front n) = (incl n).comp (dl 1 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *
  omega

theorem dl_front_one (n : ℕ) : (dl (n + 1) 1).comp (front n) = (incl n).comp (dl 1 1) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 1 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_one] at *
  omega

theorem front_eq_incl (n : ℕ) : front (n + 1) = (incl n).comp (dl 1 2) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 2 j
  have h5 : ((2 : Fin (1 + 2)) : ℕ) = 2 := rfl
  have hj := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply] at *
  omega

theorem bracket (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (y : Cn F 1) (hy : dn F 1 y = 0) :
    act F ((dl (n + 1) 0).comp (front n)) y - act F ((dl (n + 1) 1).comp (front n)) y
      + act F (front (n + 1)) y = 0 := by
  have hface : ∀ (m : ℕ) (j : Fin (m + 2)),
      MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j) :=
    fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j
  have hd : MainStatements.Hodge.dn F 1 y =
      GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0) y - GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1) y
        + GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2) y := by
    rw [MainStatements.Hodge.dn, LinearMap.sum_apply, Fin.sum_univ_three]
    simp only [LinearMap.smul_apply, hface, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
      pow_one, neg_one_sq, one_smul, neg_smul, sub_eq_add_neg]
    first | done | rfl
  rw [GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_zero, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_one, GlobalTheory.CompanionTheory.HopfLe.DnCup.front_eq_incl,
    GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp,
    ← map_sub, ← map_add, ← hd, hy, map_zero]

theorem coboundary_cup1 (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (y : Cn F 1) (z : Cn F n) (hy : dn F 1 y = 0) :
    dn F (n + 1) (cup1 F y z) = - cup1 F y (dn F n z) := by
  have hface : ∀ (m : ℕ) (j : Fin (m + 2)),
      MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j) :=
    fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j
  have hcup : ∀ i : Fin (n + 1 + 2), MainStatements.Hodge.cof F (n + 1) i (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.back n)) z := by
    intro i
    rw [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, GlobalTheory.CompanionTheory.HopfLe.act_mul,
      GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.front n),
      GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.back n)]
  have hback : ∀ {k : ℕ} (θ : Fin (k + 1) →o Fin (n + 1 + 1)) (w : MainStatements.Hodge.Cn F k),
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.back (n + 1)).comp θ) w =
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F θ w) :=
    fun θ w => GlobalTheory.CompanionTheory.HodgeCx.act_comp F θ (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) w
  have h' := eq_neg_iff_add_eq_zero.mpr (GlobalTheory.CompanionTheory.HopfLe.DnCup.bracket F n y hy)
  have key : GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) +
      -(GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z)) := by
    rw [← neg_mul, ← add_mul, ← h']
    congr 1
    abel
  have h0 : MainStatements.Hodge.cof F (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) := by
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_zero, hback]
  have h1 : MainStatements.Hodge.cof F (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) := by
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_one, hback]
  have hk : ∀ k : Fin (n + 1), MainStatements.Hodge.cof F (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1))
          (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ) z) := by
    intro k
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_high, hback]
    congr 1
    exact congrArg (fun θ : Fin 2 →o Fin (n + 1 + 2) => GlobalTheory.CompanionTheory.HodgeCx.act F θ y)
      (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_high n k)
  simp only [MainStatements.Hodge.dn, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [sum_fin_add_two_eq_zero_add_one_add_sum (m := n + 1), sum_fin_add_two_eq_zero_add_sum_succ (m := n), h0, h1]
  simp only [hk]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, map_add (f := _), map_neg, map_sum, map_smul, map_zsmul,
    mul_add, Finset.mul_sum, mul_smul_comm, Fin.val_zero, Fin.val_one, Fin.val_succ, pow_zero,
    pow_one, pow_succ, one_smul, neg_smul, mul_neg, mul_one, neg_neg, Finset.sum_neg_distrib]
  rw [key]
  abel

end GlobalTheory.CompanionTheory.HopfLe.DnCup
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem gr_pull_g {X Y Z : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j)
    (hm : r z ∈ (M.pull F).U (fun _ => i) ⊓ (M.pull F).U (fun _ => j)) :
    gr r z _ hm ((M.pull F).g (fun _ => i) (fun _ => j)).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val := by
  refine (congrArg (fun u => gr r z _ hm (Units.val u))
    ((Fintype.prod_unique (fun _ : PUnit => _ ^ (1 : ℤ))).trans (zpow_one _))).trans ?_
  exact gr_res r z _ hm _

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    (U : X.Opens) {a : Γ(X, U)} (ha : a ∈ ext s J U) :
    ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom a = 0 := by
  have hle : ext s J U ≤
      RingHom.ker ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker,
      app_cst (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))).w U r,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  exact hle ha

theorem triv_of_compatible_mod (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R)
    (M : LB X) (hM : M.IsLB) (A : Type) (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (hV : ⨆ a, V a = ⊤) (y z : ∀ a, Γ(X, V a))
    (hyz : ∀ a, y a * z a - 1 ∈ ext s J (V a))
    (hc : ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
      ext s J (V a ⊓ V b)) :
    GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  set π := pullback.fst s (spMap (Ideal.Quotient.mk J)) with hπ
  have cov : ⨆ a, π ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]; rfl
  refine gen_of_refine (pull_isLB hM π) (fun a => π ⁻¹ᵁ V a) cov (fun a _ => j a)
    (fun a => pull_le M π (j a) (hj a)) (fun a => (π.app (V a)).hom (y a))
    (fun a => IsUnit.of_mul_eq_one ((π.app (V a)).hom (z a)) ?_) fun a b x ha hb => ?_
  · have h := app_eq_zero_of_mem_ext s J (V a) (hyz a)
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h
    exact h
  · have hab : (𝟙 _ : pullback s (spMap (Ideal.Quotient.mk J)) ⟶ _) x ∈ π ⁻¹ᵁ (V a ⊓ V b) :=
      ⟨ha, hb⟩
    have h := congrArg (gr (𝟙 _) x (π ⁻¹ᵁ (V a ⊓ V b)) hab)
      (app_eq_zero_of_mem_ext s J (V a ⊓ V b) (hc a b))
    rw [map_zero, gr_app, map_sub, map_mul, tr, gr_res, gr_res, gr_res, sub_eq_zero] at h
    refine (gr_app _ _ _ _ _ _).trans (h.trans ?_)
    rw [gr_app]
    exact congrArg (· * _) (gr_pull_g M π (𝟙 _) x (hj a ha) (hj b hb) _).symm

end GlobalTheory.CompanionTheory.FewEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tower (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') (l : BC F F'')
    (h : ∀ T b, l.α T b = n.α T (m.α T b)) (x : S ⊗[R] C1 F) :
    th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  have hcomp : ∀ f : GlobalTheory.CatCoh.C1 F,
      GlobalTheory.CompanionTheory.PerfVB.c1 l f =
        GlobalTheory.CompanionTheory.PerfVB.c1 n (GlobalTheory.CompanionTheory.PerfVB.c1 m f) := by
    intro f
    simp only [GlobalTheory.CompanionTheory.PerfVB.c1, LinearMap.coe_mk, AddHom.coe_mk, h]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s f =>
    simp only [GlobalTheory.CompanionTheory.PerfVB.th1, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', GlobalTheory.CompanionTheory.PerfVB.liftSemi_tmul, LinearMap.map_smulₛₗ, hcomp]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRank
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rankAtStalk_eq_of_finrank_fibres :
    ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K]
      [Module.Projective R K] (g : ℕ),
      (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  intro R K _ _ _ _ _ g hg p
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] K) :=
    Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_tensorProduct,
    ← Module.finrank_baseChange (R := IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K).finrank_eq]
  exact hg _

end GlobalTheory.CompanionTheory.PerfVB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent
section
open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem exists_dual_functionals_of_linearIndependent :
    ∀ {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V] [DecidableEq ι], IsField R →
      ∀ x : ι → V, LinearIndependent R x →
        ∃ l : ι → V →ₗ[R] R, ∀ i j, l i (x j) = if i = j then 1 else 0 := by
  intro R V ι _ _ _ _ hR x hx
  letI : Field R := hR.toField
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis ι R (Submodule.span R (Set.range x)),
      ∀ k, (b k : V) = x k := ⟨Module.Basis.span hx, fun k => by rw [Module.Basis.span_apply hx k]⟩
  have hext : ∀ i : ι, ∃ g : V →ₗ[R] R,
      g ∘ₗ (Submodule.span R (Set.range x)).subtype = b.coord i :=
    fun i => LinearMap.exists_extend _
  choose l hl using hext
  refine ⟨l, fun i j => ?_⟩
  have h : l i (b j : V) = b.coord i (b j) := LinearMap.congr_fun (hl i) (b j)
  rw [hb j] at h
  rw [h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end GlobalTheory.CompanionTheory.HopfLe
end

