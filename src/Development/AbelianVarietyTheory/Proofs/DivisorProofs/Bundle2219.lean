module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLiftTorsionPointClassicalAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryCubicalBundleOfDenseAbelianNormalBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base : ∀ {S U : Scheme.{0}} [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (F : A.left ⟶ G.left), IsGrpPullback A G j F → GlobalFnsSt → IsAbelianScheme A → ∀ (L : RigLB G) (c : CubicalStr G L) (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), sym.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J = cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J := by
  first | exact @GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | exact GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | (intros; apply GlobalTheory.SymCubDense.sym_cub_of_dense_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitude
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem reduceMod_eq_zero_iff {h : ℕ} (M : ℕ) (u : Fin h ⊕ Fin h → ℤ) :
    reduceMod M u = 0 ↔ ∃ c, u = M • c := by
  constructor
  · intro hu
    refine ⟨fun i => u i / M, ?_⟩
    funext i
    have hi : ((u i : ℤ) : ZMod M) = 0 := congrFun hu i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (u v : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd u v : ℤ) : ZMod M) = omegaMod M (reduceMod M u) (reduceMod M v) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem sympCond_twist : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  intro p _ D R _ b N h M hM S t o T t₁ lv hlv a n σ hn hσ
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlv

  let φ : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (T ⟶ o.A) :=
    MonoidHom.mk' (fun u => lv (Multiplicative.toAdd u)) (fun u v => hadd _ _)
  have hsm : ∀ (k : ℕ) (w : Fin h ⊕ Fin h → ℤ), lv (k • w) = lv w ^ k := by
    intro k w
    have := map_pow φ (Multiplicative.ofAdd w) k
    simpa [φ, ← ofAdd_nsmul] using this
  have per : ∀ {u v : Fin h ⊕ Fin h → ℤ}, reduceMod M u = reduceMod M v → lv u = lv v := by
    intro u v huv
    have h0 : reduceMod M (u - v) = 0 := by
      funext i
      have := congrFun huv i
      simp only [reduceMod, Pi.sub_apply, Pi.zero_apply, Int.cast_sub] at this ⊢
      rw [this, sub_self]
    obtain ⟨w, hw⟩ := (reduceMod_eq_zero_iff M _).1 h0
    have : u = v + M • w := by rw [← hw]; abel
    rw [this, hadd, hsm, htor, _root_.mul_one]
  let g := (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
  have tw : ∀ u, sympTwist a lv u = lv (liftMod (g (reduceMod M u))) := fun u => rfl
  have redAdd : ∀ u v : Fin h ⊕ Fin h → ℤ, reduceMod M (u + v) = reduceMod M u + reduceMod M v := by
    intro u v; funext i; simp [reduceMod]
  refine ⟨fun u c => ?_, fun u => ?_, fun k _ _ x β' z' hx' hz' => ?_⟩
  · rw [tw, tw, tw, ← hadd]
    apply per
    rw [reduceMod_liftMod, redAdd, redAdd, reduceMod_liftMod, reduceMod_liftMod, map_add (f := _)]
  · rw [tw]; exact htor _
  ·
    set β : cycAway M →+* k := (Spec.preimage (x ≫ t₁)).hom with hβdef
    have hβ : x ≫ t₁ = spMap β := by
      simp only [spMap, hβdef, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ' : β' = β.comp σ := by
      have e : spMap β' = spMap (β.comp σ) := by
        rw [spMap_comp, ← hx', ← hβ, Category.assoc]
      have := Spec.map_injective e
      exact congrArg CommRingCat.Hom.hom this
    have hζM : β (zetaAway M) ^ M = 1 := by
      rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
    have hne : β (zetaAway M) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM.ne'] at hζM
      exact zero_ne_one hζM
    set z : kˣ := Units.mk0 (β (zetaAway M)) hne with hzdef
    have hz : (z : k) = β (zetaAway M) := rfl
    have hzz : z' = z ^ n := by
      ext
      rw [hz', hβ', RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val, hz]
    have hzM : z ^ (M : ℤ) = 1 := by
      rw [zpow_natCast]; ext; rw [Units.val_pow_eq_pow_val, hz, hζM]; rfl
    obtain ⟨hK, hS, hW⟩ := hgeo k x β z hβ hz
    refine ⟨fun u => ?_, fun g' hg' => ?_, fun u c => ?_⟩
    · rw [tw, hK]
      constructor
      · rintro ⟨c, hc⟩
        apply (reduceMod_eq_zero_iff M u).1
        have : g (reduceMod M u) = 0 := by
          rw [← reduceMod_liftMod (g (reduceMod M u)), hc]
          exact (reduceMod_eq_zero_iff M _).2 ⟨c, rfl⟩
        exact (LinearEquiv.map_eq_zero_iff _).1 this
      · intro hu
        apply (reduceMod_eq_zero_iff M _).1
        rw [reduceMod_liftMod, (reduceMod_eq_zero_iff M u).2 hu, map_zero]
    · obtain ⟨u₀, hu₀⟩ := hS g' hg'
      refine ⟨liftMod (g.symm (reduceMod M u₀)), ?_⟩
      rw [tw, reduceMod_liftMod, LinearEquiv.apply_symm_apply, per (reduceMod_liftMod _)]
      exact hu₀
    · rw [tw, tw]
      set u' := liftMod (g (reduceMod M u))
      set c' := liftMod (g (reduceMod M c))
      have hcast : ((2 * omegaStd u' c' : ℤ) : ZMod M) = (((n : ℤ) * (2 * omegaStd u c) : ℤ) : ZMod M) := by
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod]
        rw [show omegaMod M (g (reduceMod M u)) (g (reduceMod M c)) = n * omegaMod M (reduceMod M u) (reduceMod M c)
          from hn _ _]
        ring
      have e : z' ^ (2 * omegaStd u c) = z ^ (2 * omegaStd u' c') := by
        rw [hzz, ← zpow_natCast z, ← zpow_mul, zpow_eq_zpow_emod _ hzM, zpow_eq_zpow_emod (2 * omegaStd u' c') hzM]
        congr 1
        exact ((ZMod.intCast_eq_intCast_iff' _ _ _).1 hcast).symm
      rw [e]
      exact hW u' c'

end GlobalTheory.HTSympCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TauCoordQuot

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance

theorem gm_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
    (ξ : Spec (CommRingCat.of (FractionRing R))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit)) (x : (FractionRing R)ˣ) (hx : IsPsiCoord D χ x) :
    ∃ u : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) =
      Units.map (kst ξ).toMonoidHom (Units.map (algebraMap R (FractionRing R)).toMonoidHom u * x) := by
  have h : ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
    fun y _ => Set.mem_iInter.2 fun _ => hj (Set.mem_univ (jK R y))
  obtain ⟨u, hu⟩ := IsPsiCoord.unique (⟨j, h, hj, rfl⟩ : IsPsiCoord D χ (genVal (D.psi χ) j h)) hx
  refine ⟨u, ?_⟩
  rw [← hu]
  exact Units.ext (gm_genVal ξ (D.psi χ) j h)

theorem alg_quot {A B C : Type} [CommGroup A] [CommGroup B] [CommGroup C] (k : B →* C) (f : A →* B)
    (c1 c2 c3 c4 : A) (x₁ x₂ x₃ : B) :
    k (f c1 * x₁) * (k (f c2 * x₂))⁻¹ * (k (f c3 * x₃))⁻¹ * (k (f c4))⁻¹ =
      k (f (c1 * c2⁻¹ * c3⁻¹ * c4⁻¹) * x₁ * x₂⁻¹ * x₃⁻¹) := by
  simp only [map_mul, map_inv, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  intro R _ _ _ D a b x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  let aU : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := gm_psi D ξ (a + b) (((j ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) i1 x₁ h₁
  obtain ⟨c2, g2⟩ := gm_psi D ξ a (((j ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inr) i2 x₂ h₂
  obtain ⟨c3, g3⟩ := gm_psi D ξ b ((j ∘ Sum.inl) ∘ Sum.inr) i3 x₃ h₃
  obtain ⟨c4, g4⟩ := gm_rigK D ξ (j ∘ Sum.inr) i4 (mem_inr hm)
  have g4' : gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) (j ∘ Sum.inr))
      (D.rigK.s (j ∘ Sum.inr)) = kU (aU c4) := g4
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      kU (genVal (D.tau a b) j h) := Units.ext eT
  have key : kU (genVal (D.tau a b) j h) =
      kU (aU c1 * x₁) * (kU (aU c2 * x₂))⁻¹ * (kU (aU c3 * x₃))⁻¹ * (kU (aU c4))⁻¹ :=
    eT'.symm.trans (dT.trans (by rw [g1, g2, g3, g4']))
  have key2 : genVal (D.tau a b) j h = aU (c1 * c2⁻¹ * c3⁻¹ * c4⁻¹) * x₁ * x₂⁻¹ * x₃⁻¹ := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    exact key.trans (alg_quot kU aU c1 c2 c3 c4 x₁ x₂ x₃)
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4⁻¹, ?_⟩
  rw [key2, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory.TauCoordQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorEqZeroOfForallDualPairing
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_dual_pairing {R : Type} [CommRing R] {M N : Type 1}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Projective R N] (u : M ⊗[R] N)
    (h : ∀ (x : Module.Dual R M) (y : Module.Dual R N),
      TensorProduct.lift ((LinearMap.mul R R).compl₁₂ x y) u = 0) : u = 0 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
  obtain ⟨s', hs'⟩ := Module.Projective.out (R := R) (P := N)
  have key : ∀ (w : M ⊗[R] N) (c : M) (c' : N),
      finsuppTensorFinsupp' R M N (TensorProduct.map s s' w) (c, c') =
        TensorProduct.lift ((LinearMap.mul R R).compl₁₂ ((Finsupp.lapply c).comp s)
          ((Finsupp.lapply c').comp s')) w := by
    intro w c c'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply]
    | add v w hv hw => simp only [map_add (f := _), Finsupp.add_apply, hv, hw]
  have h0 : TensorProduct.map s s' u = 0 := by
    apply (finsuppTensorFinsupp' R M N).injective
    rw [map_zero]
    ext ⟨c, c'⟩
    rw [key]
    exact h _ _
  have hl : (Finsupp.linearCombination R id).comp s = LinearMap.id := LinearMap.ext hs
  have hl' : (Finsupp.linearCombination R id).comp s' = LinearMap.id := LinearMap.ext hs'
  have : u = TensorProduct.map (Finsupp.linearCombination R id) (Finsupp.linearCombination R id)
      (TensorProduct.map s s' u) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hl, hl', TensorProduct.map_id,
      LinearMap.id_apply]
  rw [this, h0, map_zero]

theorem tensor_mem_of_dualAnnihilator : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R M] [Module.Projective R N] (F : Submodule R M) (F' : Submodule R N), (∃ C, IsCompl F C) → (∃ C, IsCompl F' C) → (∀ c : M, (∀ h ∈ F.dualAnnihilator, h c = 0) → c ∈ F) ∧ ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N), (∀ x ∈ F.dualAnnihilator, ∀ y ∈ F'.dualAnnihilator, ∑ k, x (a k) * y (b k) = 0) → ∃ (a₁ : Fin n → M) (b₁ : Fin n → N), (∀ k, a₁ k ∈ F) ∧ (∀ k, b₁ k ∈ F') ∧ ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0 := by
  intro R _ M N _ _ _ _ _ _ F F' ⟨C, hC⟩ ⟨C', hC'⟩
  set e : M →ₗ[R] M := C.subtype.comp (C.linearProjOfIsCompl F hC.symm) with he
  set e' : N →ₗ[R] N := C'.subtype.comp (C'.linearProjOfIsCompl F' hC'.symm) with he'
  have eF : ∀ f ∈ F, e f = 0 := fun f hf => by
    rw [he, LinearMap.comp_apply, show C.linearProjOfIsCompl F hC.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC.symm ⟨f, hf⟩, map_zero]
  have eF' : ∀ f ∈ F', e' f = 0 := fun f hf => by
    rw [he', LinearMap.comp_apply, show C'.linearProjOfIsCompl F' hC'.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC'.symm ⟨f, hf⟩, map_zero]
  have sub : ∀ m, m - e m ∈ F := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC.symm, LinearMap.mem_ker, map_sub, he,
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have sub' : ∀ m, m - e' m ∈ F' := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC'.symm, LinearMap.mem_ker, map_sub, he',
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have ann : ∀ x : Module.Dual R M, x.comp e ∈ F.dualAnnihilator := fun x => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF f hf]
  have ann' : ∀ y : Module.Dual R N, y.comp e' ∈ F'.dualAnnihilator := fun y => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF' f hf]
  refine ⟨fun c hc => ?_, fun n a b hab => ?_⟩
  · have : e c = 0 := (Module.forall_dual_apply_eq_zero_iff R (e c)).mp fun x => hc _ (ann x)
    simpa [this] using sub c
  · refine ⟨fun k => a k - e (a k), fun k => b k - e' (b k), fun k => sub _, fun k => sub' _, ?_⟩
    simp only [sub_sub_cancel]
    apply tensor_eq_zero_of_forall_dual_pairing
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    exact hab _ (ann x) _ (ann' y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanish
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_kaehler_eq_zero_of_derivations_vanish :
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  intro R B C _ _ _ _ _ hP z hz
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := C) (P := Ω[C⁄R])).1 hP
  let π : (Ω[C⁄R] →₀ C) →ₗ[C] Ω[C⁄R] := Finsupp.linearCombination C id
  have hcomp : (LinearMap.lTensor B (π.restrictScalars R)) ∘ₗ (LinearMap.lTensor B (s.restrictScalars R))
      = LinearMap.id := by
    rw [← LinearMap.lTensor_comp]
    have : (π.restrictScalars R) ∘ₗ (s.restrictScalars R) = LinearMap.id := by
      exact LinearMap.ext fun x => LinearMap.congr_fun hs x
    rw [this, LinearMap.lTensor_id]
  have key : LinearMap.lTensor B (s.restrictScalars R) z = 0 := by
    apply (TensorProduct.finsuppRight R R B C Ω[C⁄R]).injective
    rw [map_zero]
    ext i
    let θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C :=
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toLinearMap ∘ₗ
        ((Finsupp.lapply (R := C) (M := C) i).restrictScalars R ∘ₗ s.restrictScalars R)
    have hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x := by
      intro c x
      simp [θ, Algebra.TensorProduct.tmul_mul_tmul]
    have h1 := hz θ hθ
    have heq : ∀ w : B ⊗[R] Ω[C⁄R], (TensorProduct.finsuppRight R R B C Ω[C⁄R]
        (LinearMap.lTensor B (s.restrictScalars R) w)) i = LinearMap.liftBaseChange B θ w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [θ, TensorProduct.finsuppRight_apply_tmul_apply, LinearMap.liftBaseChange_tmul,
          TensorProduct.smul_tmul']
      | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
    rw [heq, h1]; rfl
  have := congrArg (fun f => f z) hcomp
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← this, key, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThJetOfNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_chart_origin (P : PolAV (Sp ℂ)) : ∃ i : P.L.ι, ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i := by
  have hc := P.isLB.cover
  let p : (Sp ℂ) := default
  have hp : (eSec P.A) p ∈ (⨆ i, P.L.U i) := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim (α := Sp ℂ) _ _
  rw [this]; exact hi

theorem differentiable_trF {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ)
    (h : Differentiable ℂ (thetaChar τ a b)) : Differentiable ℂ (trF τ a b m M N) := by
  unfold trF trFac
  refine Differentiable.mul ?_ (h.comp (by fun_prop))
  refine Differentiable.cexp ?_
  simp only [dotProduct]
  fun_prop

theorem thJet_of_normalForm : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ m : ℕ, Odd m → ∀ (I : Type) (M N : I → Fin g → ℤ) (pt : I → ((baseOver (Sp ℂ)) ⟶ x.P.A)), (∀ i, (pt i).left = (u.ex (((m : ℂ) ^ 2)⁻¹ • perV τ (M i) (N i))).left) → ∀ e : Fin g → ℂ, ThJet x hg m pt (fun i => c * trF τ a b m (M i) (N i) 0) (fun i j => c * fderiv ℂ (trF τ a b m (M i) (N i)) 0 (W j) + e j * (c * trF τ a b m (M i) (N i) 0)) := by
  intro g x hg u τ a b c W hNF m hm I M N pt hpt e
  obtain ⟨⟨th, hth⟩, hfn, -⟩ := _root_.GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique g x hg u τ a b c W hNF
  obtain ⟨α, s₁, hα, hcorr, htw, hs₁⟩ := GlobalTheory.T.exists_normalised_multiplicationPullback_function g x hg u τ a b c W hNF m th _ (hfn th hth)
  have hU := fun i => _root_.GlobalTheory.MBLow.Cl.exists_symLift_act_classical g x hg u τ a b c W hNF m hm (M i) (N i) (pt i) (hpt i)
  choose U hUs hUa using hU
  have ht := fun i => hUa i s₁ _ hs₁
  choose t hta htf using ht
  obtain ⟨hsy, hpos, ha, hb, hc, hΛ, hrig, hFn, hdiff⟩ := hNF
  obtain ⟨i₀, hi₀⟩ := exists_chart_origin x.P
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  have hθ := (thetaChar_entire_ne_zero_automorphy g τ a b hsy hpos ha hb).1
  have hF : ∀ i, (fun z => trFac τ a b m (M i) (N i) z * (c * thetaChar τ a b
      ((m : ℂ) • (z + ((m : ℂ) ^ 2)⁻¹ • perV τ (M i) (N i))))) = fun z => c * trF τ a b m (M i) (N i) z := by
    intro i
    funext z
    have : (m : ℂ) * ((m : ℂ) ^ 2)⁻¹ = (m : ℂ)⁻¹ := by field_simp
    rw [smul_add, smul_smul, this, trF]
    ring
  refine ⟨th, hth, U, t, i₀, fun j => ((m ^ 2 : ℕ) : ℂ) * fderiv ℂ (u.fr i₀) 0 (W j) / u.fr i₀ 0 - e j,
    fun i => ⟨hUs i, α, s₁, hα, hcorr, htw, hta i⟩, ?_, fun i j => ?_⟩
  · simpa using hi₀
  · have hd := differentiable_trF τ a b m (M i) (N i) hθ
    have hf : FnT u (m ^ 2) (t i) fun z => c * trF τ a b m (M i) (N i) z := by
      rw [← hF i]; exact htf i
    have h1 := _root_.GlobalTheory.MBLow.EpsVal.valR_epsLift g x.P u (m ^ 2) (t i) _ (x.v (j.cast hg.symm)) (W j) i₀ hf (hd.const_mul c)
      (x.basis.1 _) (hdiff j) hi₀
    have h2 : u.fr i₀ 0 = valR (𝟙 (Sp ℂ)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val := by
      refine hrig (fun _ => i₀) ?_
      intro q hq
      exact Set.mem_iInter.2 fun _ => hi₀ hq
    refine h1.trans ?_
    rw [← h2, fderiv_const_mul (hd 0)]
    congr 3
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtPlaceProductStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_trivial_at_place_product : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (f₂ : SInf F (Fin a' × Fin (a + a'))) (φ₂ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ᶠ w in Filter.cofinite, φ₂ w = G.M'.vac w) ∧ φ₂ v = φ v ∧
      om' (g, h) (pure f φ) = pure f₂ φ₂ := by
  first | exact @GlobalTheory.PureAway.pure_away | exact GlobalTheory.PureAway.pure_away | (intros; apply GlobalTheory.PureAway.pure_away <;> assumption)
end

