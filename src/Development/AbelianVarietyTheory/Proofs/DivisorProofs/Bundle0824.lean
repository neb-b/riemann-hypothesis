module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalMirabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorScalarUniformizer
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellScalarTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cell

variable {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem cellFunctor_central (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m → ℂˣ) (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v)
    (x : Levi k m') (hx : x ∈ relParab k g) (hcomm : ∀ y, y * x = x * y) (w) :
    cellFunctor f g ρ x w =
      ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w := by
  apply Subtype.ext; apply Subtype.ext; funext y
  show w.1.1 (y * x) = _
  rw [hcomm y]
  have h2 : w.1.1 (x * y) = _ := w.1.2 ⟨x, hx⟩ y
  rw [h2]
  show _ = ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w.1.1 y
  generalize w.1.1 y = u
  induction u using Submodule.Quotient.induction_on with
  | H v =>
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, hρ]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, smul_smul, ← Submodule.Quotient.mk_smul]
  rw [mul_assoc]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] in
theorem scalar_comm (s : β → kˣ) (x : Levi k m') (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j))
    (y : Levi k m') : y * x = x * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, hx]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in
theorem scalar_mem (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) : x ∈ relParab k g := by
  intro j _
  rw [hx]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in
theorem det_relProj (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) (h : x ∈ relParab k g) (j : β) (i : α) :
    GeneralLinearGroup.det (relProj k g ⟨x, h⟩ j i) = s j ^ Fintype.card (c i j) := by
  have e : relProj k g ⟨x, h⟩ j i = GeneralLinearGroup.scalar _ (s j) := by
    ext a a'
    refine (leviProj_apply k (g j) ⟨x j, h j trivial⟩ i a a').trans ?_
    show ((x j : GL (m' j) k) : Matrix (m' j) (m' j) k) _ _ = _
    rw [hx]
    by_cases h : a = a'
    · subst h; simp [Matrix.GeneralLinearGroup.scalar]
    · have h' : g j ⟨i, a⟩ ≠ g j ⟨i, a'⟩ := by simpa using h
      simp [Matrix.GeneralLinearGroup.scalar, h, h']
  rw [e]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end Cell

theorem modExp_false (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m false = Fintype.card (m true) := by
  simp [modExp, Finset.sum_filter]

theorem modExp_true (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m true = -(Fintype.card (m false) : ℤ) := by
  simp [modExp, Finset.sum_filter]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem extTensor_detRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (y : Levi k (Two a b)) (t : TensorProduct ℂ ℂ ℂ) :
    ((extTensor (detRep a χ₁) (detRep b χ₂)).comp (leviTwo k a b).symm.toMonoidHom) y t =
      ((χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)) : ℂˣ) : ℂ) • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => rw [map_add (f := _), hs, ht, smul_add]
  | tmul s t =>
    refine (extTensor_tmul (detRep a χ₁) (detRep b χ₂) (y false, y true) s t).trans ?_
    rw [detRep, detRep, ofChar_apply, ofChar_apply, ← smul_eq_mul, ← smul_eq_mul,
      TensorProduct.smul_tmul_smul]
    rfl

theorem cellFunctor_scalar_action {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ)
    (x : Levi k (Two (Fin (u + v)) (Fin 1)))
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j)) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      x w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hm := scalar_mem (c := fun i j => Fin (b.1 i j)) g _ x hx
  have hd := det_relProj (c := fun i j => Fin (b.1 i j)) g _ x hx hm
  have h11 : b.1 true true = 0 := by
    have := b.2.2 true
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    omega
  have h00 : (b.1 false false : ℂ) = u - 1 := by
    have := b.2.1 false
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    have h3 : b.1 false false + 1 = u := by omega
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h3
  refine (cellFunctor_central (c := fun i j => Fin (b.1 i j)) f g _
    (fun y => χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)))
    (extTensor_detRep_apply χ₁ χ₂ (Fin u) (Fin (v + 1))) x hm (scalar_comm _ x hx) w).trans ?_
  refine congrArg (fun s : ℂˣ => (s : ℂ) • w) ?_
  have hd' : ∀ i j, GeneralLinearGroup.det
      (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨x, hm⟩) i j) = _ := fun i j => hd j i
  simp only [relDeltaHalf_apply, deltaHalf_apply, relEmb_apply, det_leviEmb, Fintype.prod_bool, hd, hd',
    modExp_false, modExp_true, Fintype.card_fin, hb, h11]
  have hz : absPow k (-(b.1 false false : ℂ) / 2) = (absPow k (((u : ℂ) - 1) / 2))⁻¹ := by
    rw [h00, neg_div, absPow_neg]
  simp [hz, mul_comm]

theorem cellFunctor_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      (leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hx : ∀ j, leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) j =
      GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j) := by
    intro j
    cases j
    · exact (map_one (GeneralLinearGroup.scalar (R := k) (Fin (u + v)))).symm
    · rfl
  exact cellFunctor_scalar_action χ₁ χ₂ u v b hb f g ϖ _ hx w

end GlobalTheory.CellScalarTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory

theorem charpoly_smul_inv_of_charpoly_eq_prod (n : ℕ) (M : GL (Fin n) ℂ) (t : ℂ) (s : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun a => X - C a).prod) :
    (t • ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)).charpoly
      = (s.map fun a => X - C (t * a⁻¹)).prod := by
  set A : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) ℂ) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hB
  have hAB : A * B = 1 := by simp [hA, hB]
  have hcard : Multiset.card s = n := by
    have h1 := Matrix.charpoly_natDegree_eq_dim A
    rw [h, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1
  have hev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - A).det = (s.map fun a => y - a).prod := by
    intro y
    rw [← Matrix.eval_charpoly, h, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hneg : (-A).det = (s.map fun a => -a).prod := by simpa using hev 0
  have hne : (-A).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (left_ne_zero_of_mul_eq_one hdet)
  have hs : ∀ a ∈ s, a ≠ 0 := by
    intro a ha h0
    apply hne
    rw [hneg]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp [h0]⟩)
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ (Set.finite_singleton _).infinite_compl
  intro x hx
  have hx0 : x ≠ 0 := hx
  simp only [Set.mem_setOf_eq]
  rw [Matrix.eval_charpoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have key : (-A) * (Matrix.scalar (Fin n) x - t • B)
      = x • (Matrix.scalar (Fin n) (t / x) - A) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.smul_one_eq_diagonal, mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, hAB, mul_one,
      smul_sub, smul_smul, mul_div_cancel₀ _ hx0, smul_neg, smul_neg]
    abel
  rw [← Matrix.det_mul, key, Matrix.det_smul, hev, hneg, ← Multiset.prod_map_mul, Fintype.card_fin,
    ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have := hs a ha
  simp only [Function.comp, eval_sub, eval_X, eval_C]
  field_simp
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsRepresentedFunctorOpenCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem charts_represented_open_cover : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1) (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) → ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F Ix U x hinj hW hcov B x₀ hrep
  have uniq : ∀ (T : Scheme.{0}) (g g' : T ⟶ B), F.map g.op x₀ = F.map g'.op x₀ → g = g' :=
    fun T g g' h => (hrep T (F.map g'.op x₀)).unique h rfl
  choose j hj using fun i => (hrep (U i) (x i)).exists
  refine ⟨j, fun i => ?_, fun p => ?_, hj⟩
  · obtain ⟨W, hWi⟩ := hW i B x₀

    have hjW : Set.range (j i) ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact ((hWi (U i) (j i)).1 ⟨𝟙 _, by rw [hj i]; simp⟩) q
    obtain ⟨u, hu⟩ := (hWi W.toScheme W.ι).2 (fun q => by
      have : W.ι q ∈ Set.range W.ι := ⟨q, rfl⟩
      rwa [Scheme.Opens.range_ι] at this)
    set l := IsOpenImmersion.lift W.ι (j i) hjW with hldef
    have hl : l ≫ W.ι = j i := IsOpenImmersion.lift_fac _ _ _
    have huj : u ≫ j i = W.ι := by
      apply uniq
      rw [op_comp, Functor.map_comp_apply, hj i, hu]
    have hlu : l ≫ u = 𝟙 _ := by
      apply hinj i
      rw [op_comp, Functor.map_comp_apply, ← hu, ← Functor.map_comp_apply, ← op_comp, hl, hj i]
      simp
    have hul : u ≫ l = 𝟙 _ := by
      rw [← cancel_mono W.ι, Category.assoc, hl, huj, Category.id_comp]
    haveI : IsIso l := ⟨⟨u, hlu, hul⟩⟩
    rw [← hl]
    infer_instance
  · obtain ⟨i, Y, a, u, ⟨q, rfl⟩, ha⟩ := hcov B x₀ p
    refine ⟨i, u q, ?_⟩
    have : a = u ≫ j i := by
      apply uniq
      rw [ha, op_comp, Functor.map_comp_apply, hj i]
    rw [this]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.ClassInvAny


open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates in
theorem classInv_of_unit_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E), HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ u = 1) → ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ), (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y' → IsLatSum φ (2 * s) κ (lattice c y) S → IsLatSum φ (2 * s) κ (lattice c y') S' → ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹ * S' 0 := by
  intro E _ _ _ I _ φ hφ s κ c χ hχ hunit y y' S S' hq hS hS'
  classical
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := GlobalTheory.ClassInv.lattice_princ_mul_unit (c := c) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 :=
    (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := hunit u hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, GlobalTheory.ClassInv.lamInf_eq hφ hχ α]
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInvAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
section
noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem map_eq_sum (j : V →ₛₗ[σ] H) (b : Module.Basis ι K V) (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ]

theorem exists_cx (hli : LinearIndependent ℂ fun i => j (b i)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (f : Module.End K V) : ∃ U : Module.End ℂ H, ∀ v, U (j v) = j (f v) := by
  have h2 : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [map_eq_sum j b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i)), fun v => ?_⟩
  have h3 : ∀ i, ((Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i))) (j (b i)) = j (f (b i)) := fun i => by
    have := (Module.Basis.mk hli h2).constr_basis ℂ (fun i => j (f (b i))) i
    rwa [Module.Basis.mk_apply] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_eq_sum j b v, map_sum]
  conv_rhs => rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, h3]

theorem ext_of_span {X : Type} [AddCommGroup X] [Module ℂ X] (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    {f g : H →ₗ[ℂ] X} (h : ∀ v, f (j v) = g (j v)) : f = g :=
  LinearMap.ext_on_range hsp h

theorem sum_selfAdj {G : Type} [Group G] [Fintype G] (r : Representation K G V) (a : G → K)
    (ha : ∀ g, starRingEnd ℂ (σ (a g)) = σ (a g⁻¹))
    (hr : ∀ g v w, inner ℂ (j (r g v)) (j (r g w)) = inner ℂ (j v) (j w)) (v w : V) :
    inner ℂ (j ((∑ g, a g • r g) v)) (j w) = inner ℂ (j v) (j ((∑ g, a g • r g) w)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, ha]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [Equiv.inv_apply, ← hr g v, ← Module.End.mul_apply (r g) (r g⁻¹), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

end Linear

section Poly

end Poly

section Core

variable {K V H E Pl : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

end Core

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_form : (LinearIndependent ℂ fun i => j (S.basis i)) ∧ Submodule.span ℂ (Set.range j) = ⊤ ∧
    ∀ x y, inner ℂ (j x) (j y) = σ (S.csum (x : S.Cl → S.V) (y : S.Cl → S.V)) := by
  obtain ⟨-, h2, ⟨h3, h4⟩, -⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨LinearIndependent.of_comp M.e (by simpa only [Function.comp_def, hj] using h3), ?_, fun x y => ?_⟩
  · refine Submodule.map_injective_of_injective hM.1 ?_
    rw [Submodule.map_top, hM.2.1, ← h4, Submodule.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hj]
  · rw [hM.2.2, hj, hj]
    exact h2 x y

end Pres

theorem idem_idem {K G E : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {X : Finset (G → K)} (hX : ∀ c ∈ X, IsAbsIrrChar c) (ρ : Representation ℂ G E) (z : E) :
    ∑ g, σ ((idemOf X).coeff g) • ρ g (∑ h, σ ((idemOf X).coeff h) • ρ h z) = ∑ h, σ ((idemOf X).coeff h) • ρ h z := by
  conv_rhs => rw [← idemOf_mul_self X hX]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_mul_fin, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm (f := fun h x => (σ ((idemOf X).coeff x) * σ ((idemOf X).coeff (x⁻¹ * h))) • ρ h z)]
  refine Finset.sum_congr rfl fun g _ => Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  simp [mul_smul]

theorem mem_range_adjoint_tw {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (s : Bool) (f : E →ₗ[ℂ] E') (y : E) :
    Tw.mk s y ∈ LinearMap.range (LinearMap.adjoint (Tw.map s f)) ↔ y ∈ LinearMap.range (LinearMap.adjoint f) := by
  have : Tw.map s (LinearMap.adjoint f) = LinearMap.adjoint (Tw.map s f) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [Tw.inner_eq, Tw.inner_eq]
    exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))
  rw [← this]
  exact Iff.rfl

end GlobalTheory.AdjBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMirabolicHolds
section
namespace GlobalTheory

theorem cuspidalMirabolic_holds : GlobalTheory.Published.CuspidalMirabolic :=
  CompanionTheory.Mirab.cuspidalMirabolic

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomainStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain : ∀ (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (O : Type) [CommRing O] (n a : ℕ) (A : O →+* Matrix (Fin n) (Fin n) W) (ω : O) (tr nm : ℤ) (ρ : W) (t : Fin a → (O →+* W)), ω ^ 2 - tr * ω + nm = 0 → ρ ^ 2 - tr * ρ + nm = 0 → (∀ i, t i ω = ρ) → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((tr ^ 2 - 4 * nm : ℤ) : W) → (∀ v : Fin n → L, ((A ω).map (algebraMap W L)).mulVec v = algebraMap W L ρ • v → ∃ w : Fin a → Fin n → L, (∀ i c, ((A c).map (algebraMap W L)).mulVec (w i) = algebraMap W L (t i c) • w i) ∧ v = ∑ i, w i) → ∃ Q : Fin a → Matrix (Fin n) (Fin n) W, (∀ i, Q i * Q i = Q i) ∧ (∀ i c, A c * Q i = t i c • Q i) ∧ (∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β).mulVec v = β ρ • v → v = ∑ i, ((Q i).map β).mulVec v) ∧ ∀ (R' : Type) [CommRing R'] (β : W →+* R') (i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β).mulVec v = β (t i c) • v) → ((Q i).map β).mulVec v = v := by
  first | (exact @GlobalTheory.LieExtProj.rhoPart_splits_by_idempotents) | (exact GlobalTheory.LieExtProj.rhoPart_splits_by_idempotents) | (intros; apply GlobalTheory.LieExtProj.rhoPart_splits_by_idempotents  <;> assumption)
end

