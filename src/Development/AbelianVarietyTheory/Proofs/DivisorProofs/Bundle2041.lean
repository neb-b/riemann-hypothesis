module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensors
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv

theorem blockRow_eq_sum {ι R : Type} [CommRing R] {m : ι → ℕ} {n n' : ℕ} (e : (Σ τ : ι, Fin (m τ)) ≃ Fin n)
    (e' : (Σ τ : ι, Fin (m τ)) ≃ Fin n') (B : Matrix (Fin n) (Fin n') R)
    (hB : ∀ (τ σ : ι) (i : Fin (m τ)) (k : Fin (m σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0)
    (τ : ι) (i : Fin (m τ)) (c : Fin n') :
    B (e ⟨τ, i⟩) c = ∑ j : Fin (m τ), B (e ⟨τ, i⟩) (e' ⟨τ, j⟩) * (if c = e' ⟨τ, j⟩ then 1 else 0) := by
  obtain ⟨⟨σ, k⟩, rfl⟩ := e'.surjective c
  by_cases h : τ = σ
  · subst h
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj (eq_of_heq (Sigma.mk.inj (e'.injective h)).2).symm
    · simp
  · rw [hB _ _ _ _ h]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    intro h'
    exact h (Sigma.mk.inj (e'.injective h')).1.symm

theorem transpose_mul_symm_mul_apply {R : Type} [CommRing R] {n n' : ℕ} (B : Matrix (Fin n) (Fin n') R) (a b : Fin n)
    (c d : Fin n') :
    (_root_.Matrix.transpose B * (Matrix.of fun x y : Fin n =>
      ((if x = a ∧ y = b then 1 else 0) + (if x = b ∧ y = a then 1 else 0) : R)) * B) c d =
      B a c * B b d + B b c * B a d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib, add_mul,
    ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]

theorem transpose_mul_symPair_mul_mem_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  intro E _ _ _ H Dw R _ n n' e e' ε' B hB P
  have key : _root_.Matrix.transpose B * symPair (R := R) e P * B =
      ∑ j : Fin (Dw.mult P.1.1), ∑ k : Fin (Dw.mult ((starRingEnd ℂ).comp P.1.1)),
        (B (e ⟨P.1.1, P.2.1⟩) (e' ⟨P.1.1, j⟩) *
          B (e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩) (e' ⟨(starRingEnd ℂ).comp P.1.1, k⟩)) •
          symPair (R := R) e' (⟨P.1, (j, k)⟩ : PairIx H Dw) := by
    ext c d
    unfold symPair
    rw [transpose_mul_symm_mul_apply, blockRow_eq_sum e e' B hB _ _ c, blockRow_eq_sum e e' B hB _ P.2.2 d,
      blockRow_eq_sum e e' B hB _ P.2.2 c, blockRow_eq_sum e e' B hB _ P.2.1 d, mul_comm (Finset.sum _ _) (∑ j : Fin (Dw.mult P.1.1), _ * (if d = _ then _ else _)),
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [ite_and]
    split_ifs <;> ring
  have hmem : _root_.Matrix.transpose B * symPair (R := R) e P * B ∈
      Submodule.span R (Set.range fun k => symPair (R := R) e' (ε' k)) := by
    rw [key]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨ε'.symm ⟨P.1, (j, k)⟩, by simp⟩
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  exact ⟨cf, hcf.symm⟩

end GlobalTheory.LogKSDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.UnitAboveOpen

theorem exists_extend (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T]
    (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T) (U : T.Opens) (hU : (U : Set T).Nonempty)
    (p : H ⟶ T) (e : T ⟶ H) (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (F : Γ(H, p ⁻¹ᵁ U)ˣ) (hF : ∀ y : U.toScheme, gm (U.ι ≫ e) y (p ⁻¹ᵁ U) F = 1) :
    ∃ G : Γ(H, ⊤)ˣ, F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G := by
  have : Nonempty U.toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : IsIntegral H := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have hP : IsPullback (p ⁻¹ᵁ U).ι (p ∣_ U) p U.ι := (isPullback_morphismRestrict p U).flip
  let eU : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := hP.lift (U.ι ≫ e) (𝟙 _) (by simp [he])
  have heU : eU ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ e := hP.lift_fst _ _ _
  have : Nonempty (p ⁻¹ᵁ U).toScheme := ⟨eU (Nonempty.some inferInstance)⟩
  let L : LB H := ⟨PUnit, fun _ ↦ ⊤, fun _ _ ↦ 1⟩
  have hL : L.IsLB := ⟨by simp [L], fun _ ↦ map_one _, fun _ _ _ ↦ by simp [L]⟩
  let φ : PEmpty → (H ⟶ H) := PEmpty.elim
  let ε : PEmpty → ℤ := PEmpty.elim
  have hw {Y : Scheme.{0}} (ψ : PEmpty → (Y ⟶ H)) (a) (y : Y) : y ∈ LB.wchart L ψ a :=
    Set.mem_iInter.2 fun k ↦ k.elim
  have hm (y : (p ⁻¹ᵁ U).toScheme) : (p ⁻¹ᵁ U).ι y ∈ p ⁻¹ᵁ U := y.2
  let t : LB.Gen (LB.LinComb L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) ε) :=
    ⟨fun a ↦ res (fun y _ ↦ hm y) (pullU (p ⁻¹ᵁ U).ι _ F)⟩
  have htg {Z : Scheme.{0}} (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (z : Z) (a) :
      gm r z (LB.wchart L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) a) (t.s a) =
        gm (r ≫ (p ⁻¹ᵁ U).ι) z (p ⁻¹ᵁ U) F :=
    (gm_res r z _ (hw _ _ _) _).trans (gm_pull r _ z _ (hm _) F)
  let ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε) := ⟨fun a ↦ 1⟩
  have ht : t.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hρ : ρ.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ U.ι) := by
    intro a b _ _ _
    refine unit_ext fun y hy ↦ ?_
    rw [gm_res _ y _ hy, gm_res _ y _ hy]
    refine Eq.trans (b := 1) ((gm_res _ y _ (hw _ _ _) _).trans
      ((gm_pull _ _ y _ (hw _ _ _) _).trans ((htg _ _ _).trans ?_))) ?_
    · rw [Category.id_comp, heU, hF]
    · refine Eq.symm ((gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans ?_))
      exact map_one _
  obtain ⟨c, ⟨-, hc'⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend T hT U.toScheme H
    (p ⁻¹ᵁ U).toScheme H U.ι p e (p ⁻¹ᵁ U).ι (p ∣_ U) eU hs hg he hP heU L hL PEmpty φ ε t ρ
    ht hρ hc
  let a : PEmpty → L.ι := PEmpty.elim
  refine ⟨res (fun y _ ↦ hw φ a y : (⊤ : H.Opens) ≤ LB.wchart L φ a) (c.s a),
    GlobalTheory.GenExtendNormal.unit_ext_of_isOpenImmersion (p ⁻¹ᵁ U).ι fun y hy ↦ ?_⟩
  rw [gm_res _ y _ hy, gm_res (p ⁻¹ᵁ U).ι y (V := ⊤) _ trivial]
  have h₁ := htg (𝟙 _) y a
  rw [← hc', Category.id_comp] at h₁
  rw [← h₁]
  exact (gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans
    (by rw [Category.id_comp]))

theorem exists_eq_res_mul_pullU :
    ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  intro T H _ _ hT U hU p e hs hg he F
  have hle : U ≤ e ⁻¹ᵁ p ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, he]; rfl
  let w : Γ(T, U)ˣ := res hle (pullU e _ F)
  obtain ⟨G, hG⟩ := exists_extend T H hT U hU p e hs hg he (F * (pullU p U w)⁻¹) fun y ↦ by
    have hy : U.ι y ∈ U := y.2
    have hy' : p ((U.ι ≫ e) y) ∈ U := hle hy
    rw [map_mul, map_inv, gm_pull _ p y U hy', Category.assoc, he, Category.comp_id,
      gm_res _ y hle hy, gm_pull _ e y _ (hle hy), mul_inv_cancel]
  exact ⟨G, w, by rw [← hG, inv_mul_cancel_right]⟩

end GlobalTheory.UnitAboveOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

def Cond {X X' Z : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) : Prop :=
  ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W) ∧
    ∀ x : Γ(X, W), i.app W x = 0 → ∀ r : Γ(X', p ⁻¹ᵁ W), ∃ y : Γ(X, W), i.app W y = 0 ∧ p.app W y = p.app W x * r

def UnitsPatch {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ W : X.Opens, Function.Injective (pullU p W) ∧
    ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) → ∃ u : Γ(X, W)ˣ, pullU p W u = u'

def LocGen {Y : Scheme.{0}} (L : LB Y) (V : Y.Opens) (a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ) : Prop :=
  ∀ (y : Y) (k k' : L.ι), y ∈ V → y ∈ L.U k → y ∈ L.U k' →
    gm (𝟙 Y) y (V ⊓ L.U k) (a k) = gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) y (V ⊓ L.U k') (a k')

def Matches {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) {L' : LB X'} {N : LB Z}
    (w : LB.Iso (L'.pull i') (N.pull p')) {V' : X'.Opens} {V : Z.Opens} (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ)
    (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ) : Prop :=
  ∀ (z : Z') (k : L'.ι) (l : N.ι), i' z ∈ V' → p' z ∈ V → i' z ∈ L'.U k → p' z ∈ N.U l →
    gm p' z (V ⊓ N.U l) (b l) =
      gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) *
        gm i' z (V' ⊓ L'.U k) (a k)

def Pinched (g : ℕ) {S S' Z B' C Y : Scheme.{0}} (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z)
    (i : Y ⟶ B') (q : Y ⟶ C) (x : B') : Prop :=
  ∃ (U U' V : Scheme.{0}) (u : U ⟶ S) (p : U' ⟶ U) (j : U' ⟶ B') (n : V ⟶ U) (k : V ⟶ C),
    SmoothOfRelativeDimension g u ∧ IsPullback p (j ≫ b') u s' ∧ IsOpenImmersion j ∧ x ∈ Set.range j ∧
    IsPullback n (k ≫ e) u z ∧
    ∀ (T : Scheme.{0}) (a : T ⟶ U') (a' : T ⟶ V), a ≫ p = a' ≫ n → ∃ y : T ⟶ Y, y ≫ i = a ≫ j ∧ y ≫ q = a' ≫ k

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterLocalGL
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinBarChar

open Matrix

theorem boxFun_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem fromBlocks_diag_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A - 1 = Matrix.fromBlocks (A - 1) 0 0 (A - 1) := by
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

theorem fromBlocks_diag_mul_diagCols {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A * (diagCols n : Matrix (n ⊕ n) n R) = (diagCols n : Matrix (n ⊕ n) n R) * A := by
  ext (i | i) j <;> simp [diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply]

theorem unif_pow_ne_real : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hχ t K hK S hS ν α ι hι hint m hm r hr
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw

  haveI : Nonempty (Fin a') := ⟨⟨0, by have := hT.geo.aBig; omega⟩⟩
  obtain ⟨g₀, hg₀⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a') (R := Fv F v) (unifAt v)

  set k := K g₀ with hk
  have hkU : (mat k)ᵀ * incM F G.V'.J * (mat k).map (cA σ) = incM F G.V'.J := k.2
  set mi : Matrix (Fin a') (Fin a') (AE F E) := ((k : GL (Fin a') (AE F E))⁻¹).1
  have h1 : mat k * mi = 1 := Units.mul_inv (k : GL (Fin a') (AE F E))
  have h2 : mi * mat k = 1 := Units.inv_mul (k : GL (Fin a') (AE F E))
  let P₀ : GL (Fin a' ⊕ Fin a') (AE F E) := ⟨Matrix.fromBlocks (mat k) 0 0 (mat k), Matrix.fromBlocks mi 0 0 mi,
    by rw [Matrix.fromBlocks_multiply, h1]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply, h2]; simp [Matrix.fromBlocks_one]⟩
  have hP₀ : P₀ ∈ UG (cA σ) (dbl (incM F G.V'.J)) := by
    show (Matrix.fromBlocks (mat k) 0 0 (mat k))ᵀ * dbl (incM F G.V'.J) * (Matrix.fromBlocks (mat k) 0 0 (mat k)).map (cA σ) = _
    have hn : (mat k)ᵀ * (-incM F G.V'.J) * (mat k).map (cA σ) = -incM F G.V'.J := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hkU]
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.map_zero _ (map_zero (cA σ))]
    rw [hkU, hn]
  let p : UG (cA σ) (dbl (incM F G.V'.J)) := ⟨P₀, hP₀⟩
  have hpm : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 (mat k) := rfl
  have hAt : At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g₀).1 u hu
    rw [hpm, fromBlocks_diag_sub_one, Matrix.fromBlocks_smul]
    simp [hk1]
  have hpt : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) *
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) =
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) *
        (((k : UA σ G.V'.J) : GL (Fin a') (AE F E)) : Matrix (Fin a') (Fin a') (AE F E)) := by
    rw [hpm]
    exact fromBlocks_diag_mul_diagCols _

  obtain ⟨l, hl, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hlφ, φ₀, hφ₀, hI⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  have hbox := boxFun_mem_SB hφ₀ hφ₀
  obtain ⟨φ'', hφ'', hact⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hAt _ hbox
  have h4 := GlobalTheory.T.triple_local_gl_embedding_integral hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl
    (fun g gd hgd φ₁ h₁ φ₂ h₂ => hres g gd hgd φ₁ h₁ φ₂ h₂) g₀ p hpm φ₀ hφ₀ φ₀ hφ₀ φ'' hφ'' hact μ hμ
  have hs := hsieg l hl hinv p _ hpt _ (hr₀ _ hbox).2
  have hs' := (congrArg l (hact r₀ (hr₀ _ hbox))).symm.trans hs
  rw [hlφ _ hφ'', hlφ _ hbox, h4] at hs'
  have hbd : (∫ x, boxFun φ₀ φ₀ (Sum.elim x x) ∂μ) = ∫ x, φ₀ x * φ₀ x ∂μ := rfl
  rw [hbd] at hs'
  set I := ∫ x, φ₀ x * φ₀ x ∂μ
  set val := ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) with hval
  set u : ℂ := (ν (GlobalTheory.SplitFlip.gdet g₀) : ℂ) with hu
  have hratio : u / starRingEnd ℂ u = val := by
    have : c₀ * I * (u / starRingEnd ℂ u) = c₀ * I * val := by linear_combination hs'
    exact mul_left_cancel₀ (mul_ne_zero hc₀ hI) this
  have h6 := GlobalTheory.T.triple_local_gl_embedding_equivariant F E σ B a a' G X om om' hT v hv t K hK g₀

  have hgd : GlobalTheory.SplitFlip.gdet g₀ = unifAt v := hg₀
  rw [hgd] at hu h6
  have hu0 : u ≠ 0 := by rw [hu]; exact Units.ne_zero _
  have hr' : u ^ m = (r : ℂ) := by rw [hu]; exact hr
  have hrc : starRingEnd ℂ u ^ m = (r : ℂ) := by rw [← map_pow, hr', Complex.conj_ofReal]
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr']; exact pow_ne_zero _ hu0
  have hone : val ^ m = 1 := by
    rw [← hratio, div_pow, hr', hrc, div_self hr0]
  set z := chrW X.ν t (unifAt v) with hz
  rcases h6 with h | h
  · have e1 : ((z ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (((2 * m : ℕ) : ℤ)) (by omega)
    rw [zpow_natCast]
    exact Units.ext e1
  · have e1 : (((z⁻¹) ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (-((2 * m : ℕ) : ℤ)) (by omega)
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact Units.ext e1

end GlobalTheory.LinBarChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHS.BridgeValue

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (P P' : FrPt Xo c S) (e : P'.x = P.x) : ∃ u : Sˣ, ∀ i, (e ▸ P'.s).f i = scal P.x (u : S) i * P.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  exact gen_unit P.s s' P.gen t4'

end GlobalTheory.CompHS.BridgeValue

namespace GlobalTheory.CompHS.BridgeValue

theorem val_sec₀_eq_evR : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ W hW i φ x hx hz fr hfr ψ y hψ hm g hO hi
  let k := i PUnit.unit
  let ψ' : Γ(Y₀ TF.X Z, W) →+* CAt σ := ψ
  let q : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.X.YY := (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z
  let z' : Sp (CAt σ) ⟶ TF.X.YY := spMap ψ' ≫ q
  have hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hO' : ⊤ ≤ z' ⁻¹ᵁ flagOpen TF.X := fun s hs => hO hs
  have hpt : AllWt.ptF y = GlobalTheory.FlagMod.frX y := rfl
  have ex : spMap ψ' ≫ (x ≫ genι TF.Y) = z' ≫ TF.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ TF.Y.j = z' ≫ TF.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ TF.Y.j = (AllWt.ptF y ≫ TF.Y.jQ) ≫ genι TF.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ' ≫ (x ≫ genι TF.Y) := by rw [hm.1, Category.assoc]
    _ = z' ≫ TF.X.π := ex
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec TF.Y y hxy τ j = GlobalTheory.FlagMod.frVec TF.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← TF.X.F.tanPull_vecAt k ψ' q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := TF.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q y eQ
  let t : Ix Dw → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  have ht : FrBor t Q y := GlobalTheory.FlagMod.frBor_of_frVec (TF.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => by
      rw [hv τ j]
      refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j' j • _ = 0
        rw [Matrix.one_apply_ne hj', zero_smul]
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j j • _ = _
        rw [Matrix.one_apply_eq, one_smul]) (fun _ => hu0)
  have he := evR_eq_val_secOf (X := TF.X) g hO' hQ ht
  have hprod : (∏ ix, t ix ^ AllWt.exOf Dw la 0 ix) = 1 := by
    rw [Fintype.prod_option, GlobalTheory.FlagMod.exOf_none, zpow_zero, _root_.one_mul]
    exact Finset.prod_eq_one fun _ _ => one_zpow _
  rw [hprod, Units.val_one, _root_.one_mul] at he
  have key : ∀ (a b : Sp (CAt σ) ⟶ TF.X.YY), a = b → ∀ hOa hia hOb hib,
      H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) a k hOa hia (secOf TF.X _ g) =
        H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) b k hOb hib (secOf TF.X _ g) := by
    intro a b hab; subst hab; intros; rfl
  refine (H0.val_pull (inc₀ TF.X Z) le_rfl _ i hO hi (fun s hs => hO' hs) (fun s hs => hz' hs) _).trans ?_
  refine (key _ _ (Category.assoc _ _ _) _ _ hO' hz').trans ?_
  exact he.symm

end GlobalTheory.CompHS.BridgeValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem zariski_descent_heart : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hA : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring
  have hB : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L) [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) → R ≤ (V.comap φ).toSubring → ∀ t : Finset L, (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) → ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := _root_.GlobalTheory.ZariskiDescent.height_le_one_of_going_down
  have hC : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) → ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) → ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := _root_.GlobalTheory.exists_div_of_center_height_le_one
  have hD : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := _root_.GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div
  intro K L _ _ φ c hfin V _ hc t ht htV
  obtain ⟨R, hcR, hft, hRE, hnoeth, hic, hfr, htR⟩ := hA K L φ c hfin V hc t ht htV
  have hB' := hB K L φ c V R hcR hRE t (fun x hx => ⟨(ht x hx).1, htR x hx⟩) htV
  have hC' := hC K R (V.comap φ) hRE hB'
  exact hD K c R hcR (V.comap φ) hc hRE hft hC'
end GlobalTheory
end

