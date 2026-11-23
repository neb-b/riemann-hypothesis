module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionMulDifference
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecMul

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (f : T' ⟶ T)
    (x : T ⟶ A) (n : ℕ) : f ≫ x ^ n = (f ≫ x) ^ n :=
  MonObj.comp_pow x n f

end GlobalTheory.SecMul

namespace GlobalTheory

theorem sec_mul_diff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D)
    (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D,
    ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  intro R _ A _ _ n hR b hb D _ _ x y s s' s'' hs hs' hs''
  have hroot : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (p : Pt A D) (z : Pt A E), z ^ n = spOver φ ≫ p →
      (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ p := by
    intro E _ _ E' _ _ φ ψ p z hz
    rw [← SecMul.comp_pow_pt, hz, ← Category.assoc, spOver_comp]
  have hmul : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z w : Pt A E), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → (z * w) ^ n = spOver φ ≫ (x * y) := by
    intro E _ _ φ z w hz hw
    rw [mul_pow, hz, hw, comp_mul]
  have hinv : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z z' w w' : Pt A E),
      z ^ n = spOver φ ≫ x → z' ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → w' ^ n = spOver φ ≫ y →
      s'' E φ (z' * w') - s E φ z' - s' E φ w' = s'' E φ (z * w) - s E φ z - s' E φ w := by
    intro E _ _ φ z z' w w' hz hz' hw hw'
    obtain ⟨t, rfl⟩ : ∃ t, z' = z * t := ⟨z⁻¹ * z', (mul_inv_cancel_left z z').symm⟩
    obtain ⟨u, rfl⟩ : ∃ u, w' = w * u := ⟨w⁻¹ * w', (mul_inv_cancel_left w w').symm⟩
    have ht : t ^ n = 1 := by rw [mul_pow, hz] at hz'; exact mul_eq_left.mp hz'
    have hu : u ^ n = 1 := by rw [mul_pow, hw] at hw'; exact mul_eq_left.mp hw'
    rw [_root_.mul_mul_mul_comm, hs''.2 E φ _ _ (hmul E φ z w hz hw) (by rw [mul_pow, ht, hu, _root_.one_mul]),
      hb.2 E t u ht hu, hs.2 E φ z t hz ht, hs'.2 E φ w u hw hu]
    ring
  have hnat : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (z w : Pt A E), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y →
      s'' E' (ψ.comp φ) (spOver ψ ≫ z * spOver ψ ≫ w) - s E' (ψ.comp φ) (spOver ψ ≫ z) -
        s' E' (ψ.comp φ) (spOver ψ ≫ w) = ψ (s'' E φ (z * w) - s E φ z - s' E φ w) := by
    intro E _ _ E' _ _ φ ψ z w hz hw
    rw [← comp_mul, hs''.1 E E' φ ψ _ (hmul E φ z w hz hw), hs.1 E E' φ ψ z hz, hs'.1 E E' φ ψ w hw,
      map_sub, map_sub]
  obtain ⟨D2, _, _, ψ, z0, w0, hf, hz0, hw0⟩ : ∃ (D2 : Type) (_ : CommRing D2) (_ : Algebra R D2)
      (ψ : D →ₐ[R] D2) (z0 w0 : Pt A D2), (ψ : D →+* D2).FaithfullyFlat ∧ z0 ^ n = spOver ψ ≫ x ∧
      w0 ^ n = spOver ψ ≫ y := by
    obtain ⟨D1, _, _, ψ1, z1, hf1, hz1⟩ := hR D x
    obtain ⟨D2, _, _, ψ2, w2, hf2, hw2⟩ := hR D1 (spOver ψ1 ≫ y)
    refine ⟨D2, inferInstance, inferInstance, ψ2.comp ψ1, spOver ψ2 ≫ z1, w2,
      RingHom.FaithfullyFlat.stableUnderComposition ψ1.toRingHom ψ2.toRingHom hf1 hf2,
      hroot D1 D2 ψ1 ψ2 x z1 hz1, ?_⟩
    rw [hw2, ← Category.assoc, spOver_comp]
  have hinjψ : Function.Injective ψ := RingHom.FaithfullyFlat.injective hf
  obtain ⟨e, he, -⟩ := ff_descent_pairs R D D2 ψ hf
    (s'' D2 ψ (z0 * w0) - s D2 ψ z0 - s' D2 ψ w0) (fun E _ _ α β hαβ ↦ by
      rw [← hnat D2 E ψ α z0 w0 hz0 hw0, ← hnat D2 E ψ β z0 w0 hz0 hw0]
      have h1 := hroot D2 E ψ α x z0 hz0
      have h2 := hroot D2 E ψ α y w0 hw0
      rw [hαβ] at h1 h2 ⊢
      exact hinv E (β.comp ψ) _ _ _ _ (hroot D2 E ψ β x z0 hz0) h1 (hroot D2 E ψ β y w0 hw0) h2)
  refine ⟨e, fun E _ _ φ z w hz hw ↦ ?_, fun e' he' ↦ hinjψ ((he' D2 ψ z0 w0 hz0 hw0).symm.trans he.symm)⟩
  obtain ⟨E', _, _, ψ', φ', hf', hcomm⟩ := exists_pushout_faithfullyFlat R D D2 E ψ φ hf
  apply RingHom.FaithfullyFlat.injective hf'
  have hR2 : ψ' (φ e) = s'' E' (φ'.comp ψ) (spOver φ' ≫ z0 * spOver φ' ≫ w0) - s E' (φ'.comp ψ) (spOver φ' ≫ z0) -
      s' E' (φ'.comp ψ) (spOver φ' ≫ w0) := by
    rw [hnat D2 E' ψ φ' z0 w0 hz0 hw0, ← he]
    change (ψ'.comp φ) e = (φ'.comp ψ) e
    rw [hcomm]
  change ψ' (s'' E φ (z * w) - s E φ z - s' E φ w) = ψ' (φ e)
  rw [← hnat E E' φ ψ' z w hz hw, hR2]
  have h1 := hroot E E' φ ψ' x z hz
  have h2 := hroot E E' φ ψ' y w hw
  rw [hcomm] at h1 h2 ⊢
  exact hinv E' (φ'.comp ψ) _ _ _ _ (hroot D2 E' ψ φ' x z0 hz0) h1 (hroot D2 E' ψ φ' y w0 hw0) h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSymplecticLevelLiftClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevLift

theorem exists_eq_val_add {J : Type} {n : ℕ} [NeZero n] (a : J → ℤ) :
    ∃ b : J → ℤ, a = (fun i => (((a i : ZMod n)).val : ℤ)) + n • b :=
  ⟨fun i => a i / n, funext fun i => by
    rw [Pi.add_apply, Pi.smul_apply, ZMod.val_intCast, nsmul_eq_mul]
    exact (Int.emod_add_mul_ediv (a i) n).symm⟩

section Count

variable {G : Type} [CommGroup G] {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} [NeZero n] (f : (J → ℤ) → G)
  (hadd : ∀ a b, f (a + b) = f a * f b) (hker : ∀ a, f a = 1 ↔ ∃ b, a = n • b)
include hadd hker

theorem eq_val (a : J → ℤ) : f a = f (fun i => (((a i : ZMod n)).val : ℤ)) := by
  obtain ⟨b, hb⟩ := exists_eq_val_add (n := n) a
  conv_lhs => rw [hb]
  rw [hadd, (hker (n • b)).2 ⟨b, rfl⟩, _root_.mul_one]

theorem inj : Function.Injective (fun c : J → ZMod n => f (fun i => ((c i).val : ℤ))) := by
  intro c c' h
  simp only at h
  have h1 : f ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) = 1 := by
    have e := hadd ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) (fun i => ((c' i).val : ℤ))
    rw [sub_add_cancel, h] at e
    exact mul_eq_right.1 e.symm
  obtain ⟨b, hb⟩ := (hker _).1 h1
  funext i
  have e := congrFun hb i
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e
  have e2 := congrArg (fun z : ℤ => (z : ZMod n)) e
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul] at e2
  exact sub_eq_zero.1 e2

theorem card_eq (htors : ∀ a, f a ^ n = 1) (hsurj : ∀ x : G, x ^ n = 1 → ∃ a, f a = x) :
    Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J := by
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hF : Function.Bijective F := ⟨fun c c' e => inj f hadd hker (congrArg Subtype.val e), fun x => by
    obtain ⟨a, ha⟩ := hsurj x.1 x.2
    exact ⟨fun i => (a i : ZMod n), Subtype.ext (by rw [← ha, eq_val f hadd hker a])⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem surj (htors : ∀ a, f a ^ n = 1) (hcard : Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J) :
    ∀ x : G, x ^ n = 1 → ∃ a, f a = x := by
  intro x hx
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hFi : Function.Injective F := fun c c' e => inj f hadd hker (congrArg Subtype.val e)
  have hne : Nat.card {x : G // x ^ n = 1} ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (NeZero.ne n)
  haveI : Finite {x : G // x ^ n = 1} := Nat.finite_of_card_ne_zero hne
  have hle : Nat.card {x : G // x ^ n = 1} ≤ Nat.card (J → ZMod n) := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  obtain ⟨c, hc⟩ := (hFi.bijective_of_nat_card_le hle).2 ⟨x, hx⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end Count

end GlobalTheory.LevLift

namespace GlobalTheory.LevLift

theorem exists_level_lift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (βV : cycAway n →+* V) (π : V →+* K), Function.Surjective π → ∀ (c : SiegPre g n (zetaAway n) (spMap (π.comp βV))), c.Principal → ∀ (AV : Over (Sp V)) [GrpObj AV] [IsCommMonObj AV] (φ : c.A.left ⟶ AV.left) (φ₂ : (G2 c.A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV → IsGrpPullback c.A AV (spMap π) φ → IsSquare φ φ₂ → PV.IsLB → (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) → (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) → LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) → Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) → (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) → LBIso c.P (PV.pull φ₂) → ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp V)) ⟶ AV), (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ n = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp V) (β : cycAway n →+* k) (z : kˣ), x ≫ spMap βV = spMap β → (z : k) = β (zetaAway n) → (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ g' : Over.mk x ⟶ AV, g' ^ n = 1 → ∃ a, toUnit _ ≫ lev a = g') ∧ ∀ a b, Out.WeilIs AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b)))) ∧ ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (lev a).left := by
  intro g n hn3 hnodd K _ _ V _ _ _ _ hcV βV π hπ c hcP AV _ _ φ φ₂ PV hAV hφ hsq hPV hr₁ hr₂ hsym hamp hkerV hiso
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  have hnR : IsUnit (n : V) := by simpa using (isUnit_natCast hn0).map βV
  have hnΓ : IsUnit (n : Γ(Sp V, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    rwa [map_natCast] at this
  have hP : GlobalTheory.TChart.IsPPol AV PV := ⟨⟨hPV, hr₁, hr₂, hsym⟩, hamp, hkerV⟩

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  let ζR : Vˣ := Units.map βV.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (GlobalTheory.LevSpread.prim_map hn0 βV)

  have hdiag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((PV.pull (lift (𝟙 AV) (𝟙 AV)).left).pull φ) := by
    have ext2 : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 AV).left), u ≫ (fst AV AV).left = v ≫ (fst AV AV).left →
        u ≫ (snd AV AV).left = v ≫ (snd AV AV).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
    have d1 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (fst c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (snd c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have d1' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (fst AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (snd AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have hd : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 AV) (𝟙 AV)).left := by
      apply ext2
      · rw [Category.assoc, hsq.1, ← Category.assoc, d1, Category.id_comp, Category.assoc, d1', Category.comp_id]
      · rw [Category.assoc, hsq.2, ← Category.assoc, d2, Category.id_comp, Category.assoc, d2', Category.comp_id]
    have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hiso (lift (𝟙 c.A) (𝟙 c.A)).left
    rw [hd] at h3
    have hΔ := pull_isLB hPV (lift (𝟙 AV) (𝟙 AV)).left
    exact h3.trans (pull_isLB c.isLB _) (pull_isLB hPV _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ)
            (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) φ).symm

  have hL := fun a => GlobalTheory.TorsLiftComplete.existsUnique_torsion_lift V K n hcV hnR π hπ c.A AV φ hAV hφ (c.lev a)
    (c.lev_tors a)
  choose σ hσ using fun a => (hL a).exists
  have hσn : ∀ a, σ a ^ n = 1 := fun a => (hσ a).1
  have hcomp : ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (σ a).left := fun a => (hσ a).2
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  let T₁ : Over (Sp V) := Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap π)
  have hσx : ∀ a, toUnit T₁ ≫ σ a = E (c.lev a) := fun a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.pushEquiv_left, hcomp]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp V))).left := inferInstanceAs (PreconnectedSpace (Sp V))
  have inj : ∀ (T : Over (Sp V)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp V)) ⟶ AV), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    GlobalTheory.LevSpread.eq_of_comp_eq AV hAV hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty T₁.left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj T₁ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩

  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c.geom (AlgebraicClosure K) x₀ ((iK.comp π).comp βV)
    (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp V) := Over.mk ((Over.mk x₀).hom ≫ spMap π)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  have hker : ∀ a, σ a = 1 ↔ ∃ b, a = n • b := fun a => by
    rw [← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a

  haveI : ConnectedSpace (Sp V) := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing V
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected AV hAV
  have kerAt : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ ∃ b, a = n • b := fun T _ a => by
    rw [one_iff T]; exact hker a
  have addAt : ∀ (T : Over (Sp V)) a a', toUnit T ≫ σ (a + a') = (toUnit T ≫ σ a) * (toUnit T ≫ σ a') :=
    fun T a a' => by rw [hadd, MonObj.comp_mul]
  have torsAt : ∀ (T : Over (Sp V)) a, (toUnit T ≫ σ a) ^ n = 1 := fun T a => by
    rw [← MonObj.comp_pow, hσn, MonObj.comp_one]
  have surj₀ : ∀ gg : T₀ ⟶ AV, gg ^ n = 1 → ∃ a, toUnit T₀ ≫ σ a = gg := fun gg hg => by
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm gg)
      (by rw [← map_pow, hg, map_one])
    exact ⟨a, by rw [← push, ha, MulEquiv.apply_symm_apply]⟩
  have card₀ := card_eq (fun a => toUnit T₀ ≫ σ a) (addAt T₀) (kerAt T₀) (torsAt T₀) surj₀
  have cardd := GlobalTheory.TorsionCover.card_torsion AV hAV hd ((Over.mk x₀).hom ≫ spMap π)
    (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ ((Over.mk x₀).hom ≫ spMap π))
  have hdg : d = g := by
    have e : n ^ (2 * d) = n ^ (2 * g) := by
      rw [← cardd, show 2 * g = Fintype.card (Fin g ⊕ Fin g) by simp [two_mul]]
      exact card₀
    have := Nat.pow_right_injective (show 2 ≤ n by omega) e
    omega
  subst hdg
  refine ⟨σ, hadd, hσn, fun k _ _ x β z hxβ hz => ?_, hcomp⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ : V →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp βV := by
    have e : spMap (ρ.comp βV) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  refine ⟨fun a => kerAt _ a, fun gg hg => ?_, fun a a' => ?_⟩
  · have cardk := GlobalTheory.TorsionCover.card_torsion AV hAV hd (spMap ρ) (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ (spMap ρ))
    exact surj (fun a => toUnit (Over.mk (spMap ρ)) ≫ σ a) (addAt _) (kerAt _) (torsAt _)
      (by rw [cardk]; simp [two_mul]) gg hg
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp V) (Sp K) AV c.A (spMap π) φ
      (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) (pull_isLB hPV _)
      (pull_isLB c.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap π = spMap (iK.comp π) := by
      show x₀ ≫ spMap π = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp π).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := GlobalTheory.LevSpread.l3 V AV hAV PV hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR
      (2 * omegaStd a a') (AlgebraicClosure K) (iK.comp π) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FieldVA

variable {X : Scheme.{0}}

theorem nonzeroLocus_pullPow (L : LB X) (N : ℕ) (t : (lbPow L N).Sec) :
    nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 X) t) = nonzeroLocus t := by
  apply le_antisymm
  · refine iSup_le fun j y hy => ?_
    have hy' : y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _ (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) j)).hom
        (t.f (fun _ => j 0))) := hy
    rw [Scheme.basicOpen_appLE] at hy'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hy'.2⟩
  · refine iSup_le fun j y hy => ?_
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j PUnit.unit, ?_⟩
    have hc : y ∈ (lbPow L N).U j := X.basicOpen_le (t.f j) hy
    show y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _
      (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) (fun _ => j PUnit.unit))).hom (t.f (fun _ => j PUnit.unit)))
    rw [Scheme.basicOpen_appLE]
    exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc PUnit.unit, hy⟩

end GlobalTheory.Mum.FieldVA

namespace GlobalTheory.Mum


open GlobalTheory.Mum.FieldVA in
theorem veryAmpleAlong_field (hA : AmpleSt) (K : Type) [Field K] (P : PolAV (Sp K)) :
    ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  obtain ⟨m, t, hcov, hs⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow hA K P 4 le_rfl
  have hb : ∀ i, nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) :=
    fun i => nonzeroLocus_pullPow P.L 4 (t i)
  refine ⟨m, fun i => GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i), ?_, fun i => ?_⟩
  · refine _root_.top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i ∈ Set.univ, nonzeroLocus (t i) by rw [hcov]; trivial)
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, show y ∈ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) by
      rw [hb]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i (Set.mem_univ i)
  have hW : (𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) := by
    rw [← hb i]; exact le_antisymm (fun y hy => hy) (fun y hy => hy)
  have le1 := hW.le
  have le2 := hW.ge
  have hconst : ∀ a, resG P.A.left le1 (constFn P.A.hom (nonzeroLocus (t i)) a) =
      AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := by
    intro a
    have h2 : constFn P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a =
        AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := rfl
    refine (fn_ext fun x hx => ?_).trans h2
    rw [gs_res _ x le1 hx, gs_constFn _ _ _ _ (le1 hx), gs_constFn _ _ _ _ hx]
  refine ⟨by rw [hW]; exact haff, fun j => resG P.A.left le1 (r j), fun j c a ha hc => ?_, ?_⟩
  · have hc' : a ∈ (lbPow P.L 4).U (fun _ => c 0) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc 0
    have key : ∀ s : (lbPow P.L 4).Sec, secGerm (𝟙 P.A.left) a (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) s) c =
        gs (𝟙 P.A.left) a ((lbPow P.L 4).U (fun _ => c 0)) (s.f (fun _ => c 0)) := fun s =>
      (gs_appLE (𝟙 P.A.left) _ _ _ (𝟙 P.A.left) a hc _).trans
        (congrArg (fun q => gs q a _ (s.f (fun _ => c 0))) (Category.id_comp _))
    have hm : (𝟙 P.A.left) a ∈ nonzeroLocus (t i) ⊓ (lbPow P.L 4).U (fun _ => c 0) := ⟨le1 ha, hc'⟩
    have e := congrArg (gs (𝟙 P.A.left) a _) (hr j (fun _ => c 0))
    rw [gs_res _ a _ hm, gs_mul _ a _ hm, gs_res _ a _ hm, gs_res _ a _ hm] at e
    rw [key, key, gs_res _ a le1 ha]
    exact e
  · have hρ : ∀ f, resG P.A.left le1 (resG P.A.left le2 f) = f := fun f => fn_ext fun x hx => by
      rw [gs_res _ x le1 hx, gs_res _ x le2 (le1 hx)]
    have hcl : Subring.closure (Set.range (constFn P.A.hom (nonzeroLocus (t i))) ∪ Set.range r) ≤
        (MvPolynomial.eval₂Hom (AbLaw.cst P.A.hom
          ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))))
          (fun j => resG P.A.left le1 (r j))).range.comap (resG P.A.left le1) := by
      refine Subring.closure_le.2 ?_
      rintro g (⟨a, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.C a, by
          rw [MvPolynomial.eval₂Hom_C]; exact (hconst a).symm⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.X j, by rw [MvPolynomial.eval₂Hom_X']⟩)
    intro f
    obtain ⟨p, hp⟩ := RingHom.mem_range.1 (Subring.mem_comap.1
      (hcl (hsurj ▸ Subring.mem_top (resG P.A.left le2 f))))
    exact ⟨p, hp.trans (hρ f)⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendCompletion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ClassicalPt

theorem extend_completion : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), y (cPt p) = x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ev₀ : R →+* V) (i : V →+* OO p), IsAdicComplete (maximalIdeal V) V ∧ IsLocalHom ev₀ ∧ IsLocalHom i ∧ Function.Injective i ∧ spMap (i.comp ev₀) ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y ∧ ∀ ev : R →+* OO p, spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ev = i.comp ev₀ := by
  intro o' Ω _ _ _ _ M x R _ j hj p _ y hy
  obtain ⟨φ, hφl, hφ, hφu⟩ := _root_.GlobalTheory.ValPt.exists_unique_stalk_hom M.Z x p y hy
  obtain ⟨U, hU, hxU, hft⟩ := _root_.GlobalTheory.RatModel.exists_affineOpen_finiteType_int o' Ω M x
  obtain ⟨hN, K, hK, hφK⟩ := _root_.GlobalTheory.stalk_noetherian_and_finite_image M.Z U hU x hxU hft p φ
  obtain ⟨hdvr, hcpl, -⟩ := GlobalTheory.intRing_complete_dvr p K hK
  obtain ⟨e, he⟩ := hj
  let i : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K →+* OO p :=
    RingHom.codRestrict ((algebraMap K (PadicAlgCl p)).comp (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K).subtype) (OO p) (fun v => v.2)
  let ψK : M.Z.presheaf.stalk x →+* K :=
    RingHom.codRestrict ((OO p).subtype.comp φ) K (fun a => hφK a)
  let ψ : M.Z.presheaf.stalk x →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    RingHom.codRestrict ψK (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (fun a => (φ a).2)
  have hiψ : ∀ a, i (ψ a) = φ a := fun a => rfl
  have hil : IsLocalHom i := ⟨fun v hv => by
    obtain ⟨w, hw⟩ := hv.exists_right_inv
    have hw' : algebraMap K (PadicAlgCl p) (v : K) * (w : PadicAlgCl p) = 1 :=
      congrArg Subtype.val hw
    have h0 : (v : K) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hw'
      exact zero_ne_one hw'
    refine isUnit_iff_exists_inv.2 ⟨⟨(v : K)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    show algebraMap K (PadicAlgCl p) (v : K)⁻¹ ∈ OO p
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hw']
    exact w.2⟩
  have hψl : IsLocalHom ψ := ⟨fun a ha => hφl.map_nonunit a (by rw [← hiψ]; exact ha.map i)⟩
  haveI := hN
  haveI := hcpl
  obtain ⟨ev', hev'l, hev'⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply (M.Z.presheaf.stalk x) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ψ hψl
  have hej : ∀ a, e.symm (j a) = algebraMap _ _ a := fun a => by rw [← he a, e.symm_apply_apply]
  let ev₀ : R →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K := ev'.comp e.symm.toRingHom
  have hcomp : (i.comp ev₀).comp j = φ := RingHom.ext fun a => by
    show i (ev' (e.symm (j a))) = φ a
    rw [hej, hev', hiψ]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K, inferInstance, inferInstance, hdvr, ev₀, i, hcpl, ?_, hil, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have h1 := hev'l.map_nonunit _ hr
    have h2 := h1.map e.toRingHom
    simpa using h2
  · intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext ((algebraMap K (PadicAlgCl p)).injective h)
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp, hφ]
  · intro ev hev
    have h1 : ev.comp j = φ := hφu _ (by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hf : (ev.comp e.toRingHom).comp (algebraMap _ _) = φ := RingHom.ext fun a => by
      rw [← h1]; simp [he]
    have h2 := _root_.GlobalTheory.AdicExt.completion_ringHom_ext (M.Z.presheaf.stalk x) p (ev.comp e.toRingHom) ((i.comp ev₀).comp e.toRingHom)
      (by rw [hf]; exact hφl) (fun a => by
        have := congrArg (fun F => F a) hf
        have h3 := congrArg (fun F => F a) hcomp
        simp only [RingHom.comp_apply] at this h3
        change ev (e (algebraMap _ _ a)) = i (ev₀ (e (algebraMap _ _ a)))
        rw [he, h3, ← h1]
        rfl)
    refine RingHom.ext fun r => ?_
    have := congrArg (fun F => F (e.symm r)) h2
    simpa using this

end GlobalTheory.ClassicalPt
end

