module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinateSumDifferenceAdditionFactor
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMapsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  first | exact @GlobalTheory.AbPackage.abelian_cp | exact GlobalTheory.AbPackage.abelian_cp | (intros; apply GlobalTheory.AbPackage.abelian_cp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIrred

theorem irreducible_of_ringEquiv (F : Type) [Field F] [IsAlgClosed F] (R : Type) [CommRing R] (σ : F ≃+* R)
    (A : Type) [CommGroup A] (V : Type) [AddCommGroup V] [Module R V] (E : Type) [AddCommGroup E] [Module F E]
    (j : V ≃+ E) (hj : ∀ (c : F) v, j (σ c • v) = c • j v) (e : A → A → Rˣ) (Φ : A → (V ≃ₗ[R] V))
    (hcard : (Nat.card A : F) ≠ 0) (hdim : Module.finrank R V ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Rˣ, ∀ v, Φ (a * b) v = (c : R) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : R) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    (U : Submodule F E) (hU : ∀ a v, j v ∈ U → j (Φ a v) ∈ U) : U = ⊥ ∨ U = ⊤ := by
  letI := (MulEquiv.isField (Field.toIsField F) σ.symm.toMulEquiv).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R σ
  have h0 : Nat.card A ≠ 0 := fun h => hcard (by rw [h, Nat.cast_zero])
  haveI : Finite A := Nat.finite_of_card_ne_zero h0
  haveI : Module.Finite R V := Module.finite_of_finrank_pos
    (Nat.pos_of_ne_zero fun h => h0 (by rw [← hdim, h]; rfl))
  have hc : (Nat.card A : R) ≠ 0 := fun h => hcard (σ.injective (by rw [map_natCast, h, map_zero]))
  let W : Submodule R V :=
    { carrier := {v | j v ∈ U}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ U
        rw [map_add (f := _)]; exact U.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ U
        rw [map_zero]; exact U.zero_mem
      smul_mem' := fun c v hv => by
        show j (c • v) ∈ U
        rw [← σ.apply_symm_apply c, hj]; exact U.smul_mem _ hv }
  have hone : ∃ c : Rˣ, ∀ v, (1 : V ≃ₗ[R] V) v = (c : R) • Φ 1 v := by
    obtain ⟨c, hc⟩ := hmul 1 1
    refine ⟨c, fun v => (Φ 1).injective ?_⟩
    rw [map_smul, ← hc, _root_.mul_one]; rfl
  have key := GlobalTheory.heisenberg_weightSpace_irreducible R A V e Φ hc hdim hmul hcomm hnd ⊥ 1
    (fun t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      exact hone)
    (fun _ => ⊤)
    (fun χ v => ⟨fun _ t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      rw [map_one, map_one, Units.val_one, one_smul]; rfl, fun _ => trivial⟩)
    1 W le_top (fun h _ v hv => hU h v hv)
  refine key.imp (fun h => ?_) (fun h => ?_)
  · refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    have hv : v ∈ W := hx
    rw [h, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · refine Submodule.eq_top_iff'.2 fun x => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    exact (h ▸ Submodule.mem_top : v ∈ W)

theorem main : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro hL hL2 S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  obtain ⟨Φ, e, hdim, hact, hmul, hcomm, hnd⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 S P F p N hN
  refine ⟨fun x hx => (hact ⟨x, hx⟩).imp fun θ h => h.1, fun U hU => ?_⟩
  let G : Subgroup (Over.mk p ⟶ P.A) := (powMonoidHom N).ker
  have hcard : Nat.card G = N ^ (2 * P.g) := (hL.mulN _ P N hN1).2.2.2.2 F p hN
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine irreducible_of_ringEquiv F Γ((Over.mk p).left, ⊤)
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv G _ _ j (fun c v => rfl)
    (fun a b => e ⟨a.1, a.2⟩ ⟨b.1, b.2⟩) (fun a => Φ ⟨a.1, a.2⟩) ?_ ?_ (fun a b => hmul _ _ _ rfl)
    (fun a b => (hcomm _ _).2) (fun a h => Subtype.ext (hnd ⟨a.1, a.2⟩ fun b => h ⟨b.1, b.2⟩)) U fun a v hv => ?_
  · rw [hcard, Nat.cast_pow]; exact pow_ne_zero _ hN
  · rw [hdim, hcard, ← pow_mul, mul_comm]
  · obtain ⟨θ, h₁, h₂⟩ := hact ⟨a.1, a.2⟩
    exact hU θ (by rw [h₁]; exact a.2) (j v) _ (h₂ v) hv

end GlobalTheory.ThetaIrred
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaCoefficientsAbelianSquare
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddCoeff
open ReciprocityTheory.ChartRestriction.G.DVR

theorem sum_diff_inj {X : Type} [AddCommGroup X] [Module.Free ℤ X] {a b a' b' : X} (h₁ : a + b = a' + b')
    (h₂ : a - b = a' - b') : a = a' ∧ b = b' := by
  have e : (2 : ℤ) • a = (2 : ℤ) • a' := by
    rw [two_smul, two_smul]
    calc a + a = (a + b) + (a - b) := by abel
      _ = a' + a' := by rw [h₁, h₂]; abel
  have ha : a = a' := smul_right_injective X two_ne_zero e
  subst ha
  exact ⟨rfl, add_left_cancel h₁⟩

theorem reindex {X R : Type} [AddCommGroup X] [Module.Free ℤ X] [CommRing R] (s₀ s : Finset X)
    (hs : ∀ a ∈ s₀, ∀ b ∈ s₀, a + b ∈ s ∧ a - b ∈ s) (F g c : X → X → R)
    (hF : ∀ a b, a ∉ s₀ ∨ b ∉ s₀ → F a b = 0) (g₁ : ∀ a b, g (a + b) (a - b) = F a b)
    (g₀ : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → g α β = 0) :
    ∑ α ∈ s, ∑ β ∈ s, g α β * c α β = ∑ a ∈ s₀, ∑ b ∈ s₀, F a b * c (a + b) (a - b) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  symm
  refine Finset.sum_of_injOn (fun p : X × X => (p.1 + p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
  · intro p _ q _ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (sum_diff_inj h₁ h₂).1 (sum_diff_inj h₁ h₂).2
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    exact Finset.mem_product.2 (hs _ h₁ _ h₂)
  · rintro ⟨α, β⟩ _ hp
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, rfl, rfl⟩ := h
      have : a ∉ s₀ ∨ b ∉ s₀ := by
        by_contra hc
        push Not at hc
        exact hp ⟨(a, b), Finset.mem_coe.2 (Finset.mem_product.2 hc), rfl⟩
      simp only [g₁, hF a b this, zero_mul]
    · simp only [g₀ α β h, zero_mul]
  · intro p _
    simp only [g₁]

section
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_zero_of (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_sub_scale (s t : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  refine ⟨SecOps.secAdd s (SecOps.secNeg (SecOps.secScale c t)), fun Z r z J hJ => ?_⟩
  have hm := hJ.mem φ r
  have e : sval (SecOps.secScale c t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  have e' : ∀ u : LB.Sec (LB.LinComb L φ ε), sval (SecOps.secNeg u) r z J = - sval u r z J := fun u =>
    (gs_eq r z _ hm _).trans (((congrArg _ (map_neg _ _)).trans (map_neg _ _)).trans
      (congrArg Neg.neg (gs_eq r z _ hm _).symm))
  refine (gs_add r z _ hm _ _).trans ?_
  rw [sub_eq_add_neg, ← e, ← e']
  rfl
end

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  classical
  intro hGF V _ _ _ hV D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ
  have hlev := GlobalTheory.addition_formula_expanded_at_level hGF V hV D A G U θ f₀ r n σ σ' f f' hA hθ hσ
  have hbox := GlobalTheory.UU.BoxSec.main V D (𝟙_ _) (toUnit _)
  have hd : ∀ p : D.X × D.X, ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))),
      ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        (∀ a b, p.1 = a + b → p.2 = a - b → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J -
          gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
            (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J)) ∧
        ((¬ ∃ a b, p.1 = a + b ∧ p.2 = a - b) → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J) := by
    rintro ⟨α, β⟩
    obtain ⟨d₁, h₁⟩ := (hbox α β).1 n (fun i => f i α) (fun i => f' i β)
    simp only [comp_toUnit] at h₁
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, ha, hb⟩ := h
      obtain ⟨d₂, h₂⟩ := (hbox α β).2 a b (f₀ a) (f₀ b) ha hb
      simp only [comp_toUnit] at h₂
      obtain ⟨d, hd⟩ := exists_sub_scale d₁ d₂ (scal (D.P.A ⊗ D.P.A).hom r)
      refine ⟨d, fun T x y z J hJ => ⟨fun a' b' ha' hb' => ?_, fun h => absurd ⟨a, b, ha, hb⟩ h⟩⟩
      obtain ⟨rfl, rfl⟩ := sum_diff_inj (ha.symm.trans ha') (hb.symm.trans hb')
      rw [hd _ _ z J hJ, h₁ T x y z J hJ, h₂ T x y z J hJ, gs_scal, Over.w, _root_.mul_assoc]
    · exact ⟨d₁, fun T x y z J hJ => ⟨fun a b ha hb => absurd ⟨a, b, ha, hb⟩ h, fun _ => h₁ T x y z J hJ⟩⟩
  choose d hd using hd
  have h0 := GlobalTheory.WeightTwo.main V hV D A G U 2 2 d (fun e => by
    obtain ⟨s₀, H⟩ := hlev e
    refine ⟨s₀ ∪ Finset.image₂ (· + ·) s₀ s₀ ∪ Finset.image₂ (· - ·) s₀ s₀,
      fun s hs T x y xe ye hx hy hxy z J hJ => ?_⟩
    obtain ⟨H₁, H₂⟩ := H T x y xe ye hx hy hxy z J hJ
    have hs₀ : s₀ ⊆ s := (Finset.subset_union_left.trans Finset.subset_union_left).trans hs
    have R := reindex s₀ s (fun a ha b hb =>
        ⟨hs (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))),
          hs (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))⟩)
      (fun a b => gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J))
      (fun α β => ∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J -
        sval (d (α, β)) (lift x y).left z J)
      (fun α β => (val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val)
      (by
        rintro a b (h | h)
        · rw [(H₁ a h).1, zero_mul, mul_zero]
        · rw [(H₁ b h).2, mul_zero, mul_zero])
      (fun a b => by rw [(hd (a + b, a - b) T x y z J hJ).1 a b rfl rfl, sub_sub_cancel])
      (fun α β h => by rw [(hd (α, β) T x y z J hJ).2 h, sub_self])
    rw [← H₂ s hs₀] at R
    simp only [sub_mul, Finset.sum_sub_distrib] at R
    exact sub_eq_self.1 R)
  intro T ρ x y z J hJ
  obtain rfl : ρ = toUnit T := toUnit_unique _ _
  refine ⟨fun a b α β hα hβ => ?_, fun α β h => ?_⟩
  · exact sub_eq_zero.1 (((hd (α, β) T x y z J hJ).1 a b hα hβ).symm.trans (sval_zero_of _ (h0 _) _ z hJ))
  · exact ((hd (α, β) T x y z J hJ).2 h).symm.trans (sval_zero_of _ (h0 _) _ z hJ)

end GlobalTheory.AddCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIffStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  first | exact @GlobalTheory.addB_tensor_ne_zero_iff | exact GlobalTheory.addB_tensor_ne_zero_iff | (intros; apply GlobalTheory.addB_tensor_ne_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwo
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.AddEig

theorem gen_ratio {F : Type} [CommRing F] {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (q : Y ⟶ Spec (CommRingCat.of F)) (hq : Function.Surjective q.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : F, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ (scal q c) * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hq (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (scal q c) := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem surj_fst_sq {S : Scheme.{0}} (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (T : Over S) : Function.Surjective (fst T (A ⊗ A)).left.appTop.hom := by
  let m : T ⊗ (A ⊗ A) ⟶ A ⊗ (A ⊗ T) := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  let n : A ⊗ (A ⊗ T) ⟶ T ⊗ (A ⊗ A) := lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _))
  have e₀ : m ≫ snd _ _ ≫ snd _ _ = fst T (A ⊗ A) := by simp [m]
  have e₁ : m ≫ n = 𝟙 _ := by ext <;> simp [m, n]
  rw [← e₀, Over.comp_left, Over.comp_left]
  refine surj_comp (fun a => ⟨n.left.appTop.hom a, ?_⟩) (surj_comp (surj_snd hG hA _) (surj_snd hG hA T))
  have e : m.left ≫ n.left = 𝟙 _ := by rw [← Over.comp_left, e₁]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this

theorem kappa_translate (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F]
    (p : Spec (CommRingCat.of F) ⟶ S)
    (κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd (Over.mk p) (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd (Over.mk p) (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1])) (hκ : κ.IsGen)
    (c : Over.mk p ⟶ P.A) (hc : c ^ 2 = 1)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk p) P.A).left, (translPt P.A c).left] ![2, -2]))
    (hα : α.IsGen) :
    ∃ r : F, ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      (val α (lift ρ x).left z J * val α (lift ρ y).left z J *
        val κ (lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y))).left z J).val =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) * (val κ (lift ρ (lift x y)).left z J).val := by
  have := P.isAb.comm
  let a : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ fst _ _
  let b : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ snd _ _
  let d : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := fst _ _ ≫ c
  have hd : d * d = 1 := by
    rw [← MonObj.comp_mul, ← pow_two, hc, MonObj.comp_one]
  have tp : translPt P.A c = (fst _ P.A ≫ c) * snd _ P.A := rfl
  obtain ⟨r, hr⟩ := gen_ratio (F := F) P.isLB (fun U _ h => by
      have e₁ : lift (fst _ _) a ≫ translPt P.A c = d * a := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₂ : lift (fst _ _) b ≫ translPt P.A c = d * b := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₃ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, _root_.mul_mul_mul_comm, hd,
          _root_.one_mul]
      have e₄ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, MonObj.comp_mul, GrpObj.comp_inv,
          _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ← Over.comp_left, e₁, e₂, e₃, e₄, lift_snd,
        lift_snd_assoc, lift_fst]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      abel)
    (fst (Over.mk p) (P.A ⊗ P.A)).left (surj_fst_sq hG P.isAb _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) a).left) (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) b).left))
      (DVR.pullGen_isGen _ _ _ _ hκ (lift (fst _ _) (lift (d * a) (d * b))).left)) hκ
  refine ⟨r, fun T ρ x y z J hJ => ?_⟩
  have := hr _ (lift ρ (lift x y)).left z J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ThetaLin.gs_scal_comp] at this
  simp only [← Over.comp_left] at this
  have f₁ : lift ρ (lift x y) ≫ lift (fst _ _) a = lift ρ x := by simp [a]
  have f₂ : lift ρ (lift x y) ≫ lift (fst _ _) b = lift ρ y := by simp [b]
  have f₃ : lift ρ (lift x y) ≫ lift (fst _ _) (lift (d * a) (d * b)) =
      lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y)) := by simp [a, b, d, MonObj.comp_mul]
  rw [f₁, f₂, f₃, lift_fst] at this
  exact this

theorem tensor_eq_smul {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) [QuasiCompact q] [IsSeparated q] {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} (u u' t t' : Fin n → SecMod q (LB.LinComb L φ ε)) (r : F)
    (H : ∀ (Z : Scheme.{0}) (r₁ r₂ : Z ⟶ Y), r₁ ≫ q = r₂ ≫ q → ∀ (z : Z) (J), Good L z J →
      ∑ i, sval (u i).sec r₁ z J * sval (u' i).sec r₂ z J =
        gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) * ∑ i, sval (t i).sec r₁ z J * sval (t' i).sec r₂ z J) :
    ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  have key := (GlobalTheory.tensor_sections_eq_zero_iff F _ L hL _ _ q q K K φ ε φ ε (n + n) (Fin.append u (fun i => (-r) • t i))
    (Fin.append u' t')).2 (by
      intro Z r₁ r₂ h z J hJ
      have ng : gs r₁ z ⊤ (scal q (-r)) = - gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) := by
        rw [ThetaLin.gs_scal_comp, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, scal, scal, map_neg, map_neg, map_neg,
          map_neg]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      simp only [SecMod.sval_smul hJ, ng, _root_.mul_assoc, neg_mul]
      rw [H Z r₁ r₂ h z J hJ, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel])
  rw [Fin.sum_univ_add] at key
  simp only [Fin.append_left, Fin.append_right, ← TensorProduct.smul_tmul', neg_smul, TensorProduct.neg_tmul,
    Finset.sum_neg_distrib] at key
  rw [Finset.smul_sum]
  exact add_neg_eq_zero.1 key

theorem main : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  intro hG S P F _ p th n t t' u u' ⟨κ, hκ, hA⟩ θ hθ hact
  have := P.isAb.comm
  obtain ⟨r, hr⟩ := kappa_translate hG P p κ hκ θ.pt hθ θ.φ θ.isGen
  refine ⟨r, ?_⟩
  have pt : ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u' i).sec (lift ρ y).left z J =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) *
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i).sec (lift ρ y).left z J := by
    intro T ρ x y z J hJ
    have hd : (ρ ≫ θ.pt) * (ρ ≫ θ.pt) = 1 := by
      rw [← MonObj.comp_mul, ← pow_two, hθ, MonObj.comp_one]
    have a₁ := hA T ρ x y z J hJ
    have a₂ := hA T ρ ((ρ ≫ θ.pt) * x) ((ρ ≫ θ.pt) * y) z J hJ
    rw [_root_.mul_mul_mul_comm (ρ ≫ θ.pt), hd, _root_.one_mul, _root_.mul_inv, _root_.mul_mul_mul_comm (ρ ≫ θ.pt),
      mul_inv_cancel, _root_.one_mul] at a₂
    have b := hr T ρ x y z J hJ
    have act : ∀ (v w : EA P p 2) (x : T ⟶ P.A), IsActOf P.A P.L ((2 : ℕ) : ℤ) θ v.sec w.sec →
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) w.sec (lift ρ x).left z J =
        (val (L := P.L) (K := Fin 2) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![2, -2])
          θ.φ (lift ρ x).left z J).val *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := fun v w x h => by
      refine (ThetaLin.sval_of_isTwistPull P.A h (lift ρ x).left z hJ).trans ?_
      rw [← Over.comp_left, ThetaLin.lift_translT]
    rw [a₁, ← _root_.mul_assoc, ← b, Units.val_mul, _root_.mul_assoc, ← a₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act _ _ x (hact i).1, act _ _ y (hact i).2, Units.val_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _
  have : IsProper (fst (Over.mk p) P.A).left := by
    have := P.isAb.proper
    show IsProper (pullback.fst _ _)
    infer_instance
  refine tensor_eq_smul P.isLB (fst (Over.mk p) P.A).left (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left)
    (ε := fun _ => ((2 : ℕ) : ℤ)) u u' t t' r fun Z r₁ r₂ h z J hJ => ?_
  let T : Over S := Over.mk (r₁ ≫ (Over.mk p ⊗ P.A).hom)
  let R₁ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₁ rfl
  let R₂ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₂ (by
    show r₂ ≫ (Over.mk p ⊗ P.A).hom = r₁ ≫ (Over.mk p ⊗ P.A).hom
    rw [← Over.w (fst (Over.mk p) P.A), ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ p) h.symm)
  have hR : R₂ ≫ fst _ _ = R₁ ≫ fst _ _ := Over.OverMorphism.ext h.symm
  have q := pt T (R₁ ≫ fst _ _) (R₁ ≫ snd _ _) (R₂ ≫ snd _ _) z J hJ
  rw [lift_comp_fst_snd, show lift (R₁ ≫ fst _ _) (R₂ ≫ snd _ _) = R₂ by rw [← hR, lift_comp_fst_snd]] at q
  exact q

end GlobalTheory.AddEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnitsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psiScalars_relations_up_to_baseUnits : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) := by
  first | exact @GlobalTheory.PsiScalUnit.main | exact GlobalTheory.PsiScalUnit.main | (intros; apply GlobalTheory.PsiScalUnit.main <;> assumption)
end

