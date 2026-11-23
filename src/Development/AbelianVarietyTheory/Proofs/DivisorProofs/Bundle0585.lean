module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerIsoReindexedCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.PowIsoRe

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (e1 : W ≤ V) (e2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res e1 (res e2 x) = res (e1.trans e2) x := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem preimage_comp_le {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) : h ⁻¹ᵁ V ≤ (h ≫ φ) ⁻¹ᵁ W := by
  intro x hx
  exact e hx

theorem pullU_res_pullU {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) (u : Γ(Z, W)ˣ) :
    pullU h V (res e (pullU φ W u)) = res (preimage_comp_le h φ e) (pullU (h ≫ φ) W u) := by
  have key : φ.app W ≫ Y.presheaf.map (homOfLE e).op ≫ h.app V =
      (h ≫ φ).app W ≫ X.presheaf.map (homOfLE (preimage_comp_le h φ e)).op := by
    rw [Scheme.Hom.naturality, Scheme.Hom.comp_app]
    rfl
  ext1
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem res_pull_comp {X Y Z : Scheme.{0}} (h : X ⟶ Y) (m : Y ⟶ Z) {W : Z.Opens} {V1 : Y.Opens}
    {V2 V3 T : X.Opens} (u : Γ(Z, W)ˣ) (e1 : V1 ≤ m ⁻¹ᵁ W) (e2 : V2 ≤ h ⁻¹ᵁ V1) (e3 : T ≤ V2)
    (e4 : V3 ≤ (h ≫ m) ⁻¹ᵁ W) (e5 : T ≤ V3) :
    res e3 (res e2 (pullU h V1 (res e1 (pullU m W u)))) = res e5 (res e4 (pullU (h ≫ m) W u)) := by
  rw [pullU_res_pullU, res_res, res_res, res_res]

theorem res_res' {X : Scheme.{0}} {U V V' W : X.Opens} (x : Γ(X, U)ˣ) (e1 : W ≤ V) (e2 : V ≤ U)
    (e3 : W ≤ V') (e4 : V' ≤ U) : res e1 (res e2 x) = res e3 (res e4 x) := by
  rw [res_res, res_res]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem wchart_le_M {X Y Z : Scheme.{0}} (M : LB Z) (h : X ⟶ Y) (m : Y ⟶ Z) (j : Fin 1 → M.ι) :
    LB.wchart M (fun _ : Fin 1 => h ≫ m) j ≤
      LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => j 0) := by
  intro x hx
  have hx0 := Set.mem_iInter.1 hx 0
  refine Set.mem_iInter.2 fun _ => ?_
  refine Set.mem_iInter.2 fun _ => ?_
  simpa using hx0

theorem wchart_le_L {X Z : Scheme.{0}} (L : LB Z) (f : X ⟶ Z) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f) j ≤ LB.wchart L (fun _ : PUnit => f) (fun _ => j 0) := by
  intro x hx
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem exists_powIso {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂)
    (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  dsimp only [LB.Gen.IsGen, LB.div, LB.LinComb, LB.pull, powPull] at w hw ⊢
  have hle : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      LB.wchart M (fun _ : Fin 1 => h ≫ m) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤
        LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => p.1 0) ⊓
          LB.wchart L (fun _ : PUnit => f) (fun _ => p.2 0) := fun p =>
    inf_le_inf (wchart_le_M M h m p.1) (wchart_le_L L f p.2)
  dsimp only [LB.pull, LB.LinComb] at hle
  refine ⟨⟨fun p => (res (hle p) (w.s (fun _ _ => p.1 0, fun _ => p.2 0))) ^ k⟩, ?_⟩
  dsimp only
  intro p p'
  have e := congrArg (fun x => (res (inf_le_inf (hle p) (hle p')) x) ^ k)
    (hw (fun _ _ => p.1 0, fun _ => p.2 0) (fun _ _ => p'.1 0, fun _ => p'.2 0))
  simp only [map_mul, map_inv, map_pow, map_zpow, map_prod, res_res, pullU_res_pullU,
    Fin.prod_univ_one, Fintype.prod_unique, Fin.default_eq_zero, zpow_one, zpow_natCast, mul_pow, inv_pow] at e ⊢
  convert e using 5
  · exact (res_pull_comp h m (W := M.U (p.1 0) ⊓ M.U (p'.1 0))
      (V1 := LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p'.1 0))
      (M.g (p.1 0) (p'.1 0)) _ _ _ _ _).symm
  · exact res_res' (U := f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (p'.2 0))) (pullU f _ (L.g (p.2 0) (p'.2 0))) _ _ _ _

end GlobalTheory.PowIsoRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerPullbackSectionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
noncomputable section

namespace GlobalTheory.HomFixMat

theorem appLE_res_pull {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (h : X ⟶ Y) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ φ ⁻¹ᵁ U) (e₂ : W ≤ h ⁻¹ᵁ V) (e₃ : W ≤ (h ≫ φ) ⁻¹ᵁ U) (u : Γ(Z, U)) :
    (h.appLE V W e₂).hom ((Y.presheaf.map (homOfLE e₁).op).hom ((φ.app U).hom u)) =
      (X.presheaf.map (homOfLE e₃).op).hom (((h ≫ φ).app U).hom u) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_comp_appLE]

theorem appLE_restrict {X Y : Scheme.{0}} (h : X ⟶ Y) (V V' : Y.Opens) (W W' : X.Opens) (eV : V' ≤ V)
    (eW : W' ≤ W) (e : W ≤ h ⁻¹ᵁ V) (e' : W' ≤ h ⁻¹ᵁ V') (x : Γ(Y, V)) :
    (X.presheaf.map (homOfLE eW).op).hom ((h.appLE V W e).hom x) =
      (h.appLE V' W' e').hom ((Y.presheaf.map (homOfLE eV).op).hom x) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem pullSec_exists : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ)
    (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι,
      s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q)
        (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  intro X Y Z L φ h a s
  refine ⟨⟨fun q => (h.appLE _ _ (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q), ?_⟩, fun q => rfl⟩
  intro (q : Fin 1 → L.ι) (q' : Fin 1 → L.ι)
  have e0 : LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q' ≤
      h ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q') :=
    fun x hx => ⟨GlobalTheory.HomFixMat.wchart_comp_le L h φ q hx.1, GlobalTheory.HomFixMat.wchart_comp_le L h φ q' hx.2⟩
  refine (appLE_restrict h _ _ _ _ inf_le_left inf_le_left _ e0 _).trans ?_
  refine (congrArg _ (s.compat q q')).trans ?_
  refine (map_mul _ _ _).trans ?_
  congr 1
  · have hg : ((powPull L (h ≫ φ) a).g q q') =
        Units.map (h.appLE _ _ e0).hom.toMonoidHom ((powPull L φ a).g q q') := by
      show (∏ k : Fin 1, _) = Units.map _ (∏ k : Fin 1, _)
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_zpow]
      congr 1
      ext
      exact (appLE_res_pull φ h (L.U (q 0) ⊓ L.U (q' 0))
        (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q')
        (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q') _ e0 _
        (L.g (q 0) (q' 0) : Γ(Z, L.U (q 0) ⊓ L.U (q' 0)))).symm
    rw [hg]
    rfl
  · exact (appLE_restrict h _ _ _ _ inf_le_right inf_le_right _ e0 _).symm

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivOfAdjointSkewPairings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.SkewPairingCmp

theorem map_add_right {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (x y y' : M) : B x (y + y') = B x y * B x y' := by
  have h : ∀ a b, B a b = (B b a)⁻¹ := fun a b => eq_inv_of_mul_eq_one_left (hsk a b)
  rw [h x (y + y'), hadd, mul_inv, ← h, ← h]

theorem map_zero_left {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (y : M) : B 0 y = 1 := by
  have h := hadd 0 0 y
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem map_zero_right {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (x : M) : B x 0 = 1 := by
  have h := hsk x 0
  rwa [map_zero_left B hadd, _root_.mul_one] at h

theorem ext_right {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (hnd : ∀ x, (∀ y, B x y = 1) → x = 0) {y y' : M} (h : ∀ x, B x y = B x y') : y = y' := by
  have h' : ∀ a b, B a b = (B b a)⁻¹ := fun a b => eq_inv_of_mul_eq_one_left (hsk a b)
  refine sub_eq_zero.mp (hnd _ fun x => ?_)
  have h1 := hadd (y - y') y' x
  rw [sub_add_cancel, h' y x, h x, ← h'] at h1
  exact (right_eq_mul.mp h1)

theorem exists_repr {M : Type} [AddCommGroup M] [Finite M] {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (B : M → M → kˣ)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (hnd : ∀ x, (∀ y, B x y = 1) → x = 0) (f : M → kˣ) (hf : ∀ x x', f (x + x') = f x * f x') :
    ∃ z, ∀ x, f x = B x z := by
  let φ : M → (Multiplicative M →* kˣ) := fun y =>
    MonoidHom.mk' (fun x => B x.toAdd y) (fun a b => hadd _ _ _)
  have hinj : Function.Injective φ := fun y y' h =>
    ext_right B hadd hsk hnd fun x => DFunLike.congr_fun h (Multiplicative.ofAdd x)
  haveI : NeZero (Monoid.exponent (Multiplicative M)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card (Multiplicative M →* kˣ) = Nat.card (Multiplicative M) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative M) k
  have hpos : 0 < Nat.card (Multiplicative M) := Nat.card_pos
  haveI : Finite (Multiplicative M →* kˣ) := Nat.finite_of_card_ne_zero (by omega)
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hcard]; exact le_of_eq rfl)
  obtain ⟨z, hz⟩ := hbij.2 (MonoidHom.mk' (fun x => f x.toAdd) (fun a b => hf _ _))
  exact ⟨z, fun x => (DFunLike.congr_fun hz (Multiplicative.ofAdd x)).symm⟩

theorem exists_linearEquiv : ∀ (O : Type) [Ring O] (st : O → O) (M : Type) [AddCommGroup M] [Module O M] [Finite M] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B E : M → M → kˣ) (e : O), (∀ c, st (st c) = c) → (∀ c, e * c = c * e) → (∀ c, st e * c = c * st e) → (∀ x : M, e • x + st e • x = x) → (∀ x : M, e • st e • x = 0) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, B x y * B y x = 1) → (∀ (c : O) x y, B (c • x) y = B x (st c • y)) → (∀ x, (∀ y, B x y = 1) → x = 0) → (∀ x x' y, E (x + x') y = E x y * E x' y) → (∀ x y, E x y * E y x = 1) → (∀ (c : O) x y, E (c • x) y = E x (st c • y)) → (∀ x, (∀ y, E x y = 1) → x = 0) → ∃ g : M ≃ₗ[O] M, ∀ x y, B (g x) (g y) = E x y := by
  intro O _ st M _ _ _ k _ _ _ B E e hst hce hcs hsum hzero Badd Bsk Badj Bnd Eadd Esk Eadj End
  choose h hh using fun y => exists_repr B Badd Bsk Bnd (fun x => E x y) (fun x x' => Eadd x x' y)
  have hh : ∀ x y, E x y = B x (h y) := fun x y => hh y x
  have hadd : ∀ y y', h (y + y') = h y + h y' := fun y y' =>
    ext_right B Badd Bsk Bnd fun x => by
      rw [← hh, map_add_right B Badd Bsk, map_add_right E Eadd Esk, hh, hh]
  have hsmul : ∀ (c : O) y, h (c • y) = c • h y := fun c y =>
    ext_right B Badd Bsk Bnd fun x => by
      have h1 := Eadj (st c) x y
      have h2 := Badj (st c) x (h y)
      rw [hst] at h1 h2
      rw [← hh, ← h1, ← h2, hh]
  have hzero' : ∀ x : M, st e • e • x = 0 := fun x => by
    rw [smul_smul, ← hce, ← smul_smul, hzero]
  have hss : ∀ x : M, st e • st e • x = st e • x := fun x => by
    have := hsum (st e • x)
    rwa [hzero, zero_add] at this
  have hee : ∀ x : M, e • e • x = e • x := fun x => by
    have := hsum (e • x)
    rwa [hzero', add_zero] at this
  let g : M →ₗ[O] M :=
    { toFun := fun x => e • x + st e • h x
      map_add' := fun x y => by rw [hadd, smul_add, smul_add]; abel
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, hsmul, smul_add, smul_smul, hce c, hcs c] }
  have hg : ∀ x y, B (g x) (g y) = E x y := fun x y => by
    change B (e • x + st e • h x) (e • y + st e • h y) = E x y
    have h1 : B (e • x) (e • y) = 1 := by rw [Badj, hzero', map_zero_right B Badd Bsk]
    have h4 : B (st e • h x) (st e • h y) = 1 := by
      rw [Badj, hst, hzero, map_zero_right B Badd Bsk]
    have h2 : B (e • x) (st e • h y) = E x (st e • y) := by
      rw [Badj, hss, ← hsmul, ← hh]
    have h3 : B (st e • h x) (e • y) = E x (e • y) := by
      have a1 := Bsk (e • y) (st e • h x)
      have a2 := Esk (e • y) (st e • x)
      rw [Eadj (st e), hst, hee, hh (e • y), hsmul] at a2
      exact mul_left_cancel (a1.trans a2.symm)
    rw [Badd, map_add_right B Badd Bsk, map_add_right B Badd Bsk, h1, h2, h3, h4, _root_.one_mul,
      _root_.mul_one, _root_.mul_comm, ← map_add_right E Eadd Esk, hsum]
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx =>
    End x fun y => by rw [← hg, hx, map_zero_left B Badd]
  exact ⟨LinearEquiv.ofBijective g ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hg⟩

end GlobalTheory.SkewPairingCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomain
section
open NumberField

namespace GlobalTheory.OrthoFrame

theorem exists_orthoFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  intro E _ _ _ r X
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.OrthoFrame.exists_frm_mem_dom E r X
  obtain ⟨v, ho, hv⟩ := _root_.GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm E r X u hu
  have hs := GlobalTheory.OrthoFrame.sign_of_mem X v ho hv
  choose d hd0 hdΛ using fun j => ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.exists_smul_mem X.Λ (x := v j)
    (by rw [X.Λ_span]; exact Submodule.mem_top)
  have hd0' : ∀ j, ((d j : 𝓞 E) : E) ≠ 0 := fun j h => hd0 j (by exact_mod_cast h)
  set lam : Fin r → Fin r → E := fun j => ((d j : 𝓞 E) : E) • v j with hlam
  have hlamΛ : ∀ j, lam j ∈ X.Λ := fun j => by
    have e : (d j) • v j = ((d j : 𝓞 E) : E) • v j := by
      ext a; simp [Algebra.smul_def]
    rw [hlam]; dsimp only; rw [← e]; exact hdΛ j
  have hlo : ∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0 := by
    intro j k h
    simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, ho j k h,
      mul_zero]
  have hsl : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
      (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re := by
    intro τ j
    have hn : 0 < Complex.normSq (τ.1 (d j : E)) := Complex.normSq_pos.2 ((map_ne_zero τ.1).2 (hd0' j))
    have e : τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j)) =
        (Complex.normSq (τ.1 (d j : E)) : ℂ) * τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j)) := by
      simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, map_mul,
        GlobalTheory.OrthoFrame.emb_cc, ← Complex.mul_conj]
      ring
    rw [e, Complex.re_ofReal_mul]
    have := hs τ j
    calc (0 : ℝ) < Complex.normSq (τ.1 (d j : E)) * (ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
        (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j))).re) := mul_pos hn this
      _ = _ := by ring
  have hΨ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, ?_⟩
      by_contra h'
      exact h ((X.cmType τ0).2 h')
  obtain ⟨τ0, hτ0⟩ := hΨ
  have hdv : (Matrix.of v).det ≠ 0 := by
    have h := (hv ⟨τ0, hτ0⟩).1
    have e : ReciprocityTheory.ChartRestriction.G.FD.mat (GlobalTheory.OrthoFrame.frm X.Ψ v) ⟨τ0, hτ0⟩ = τ0.mapMatrix (Matrix.of v).transpose := by
      ext k a; rfl
    rw [e, ← RingHom.map_det, Matrix.det_transpose] at h
    intro h0; exact h (by rw [h0, map_zero])
  have hdl : (Matrix.of lam).det ≠ 0 := by
    have e : Matrix.of lam = Matrix.diagonal (fun j => ((d j : 𝓞 E) : E)) * Matrix.of v := by
      ext j k; simp only [hlam, Matrix.of_apply, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd0' j) hdv
  refine ⟨GlobalTheory.OrthoFrame.frm X.Ψ lam, GlobalTheory.OrthoFrame.mem_of_sign X lam hlo hdl hsl, lam, hlamΛ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_of_det_ne_zero hdl
  · intro j k hj hk
    exact hlo j k (by intro h; subst h; omega)
  · intro j hj τ
    have := hsl τ j
    simpa [ReciprocityTheory.ChartRestriction.G.FD.sgn, hj] using this
  · intro j hj τ
    have := hsl τ j
    simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg (not_lt.2 hj)] at this
    linarith
  · intro τ
    rfl

end GlobalTheory.OrthoFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModP
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.AugNil

theorem aeval_mem_span {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {d : ℕ}
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) (h0 : MvPolynomial.constantCoeff P = 0) :
    MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) (by rwa [MvPolynomial.constantCoeff_eq] at h0)
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (Finsupp.ext h)
  refine Ideal.mul_mem_left _ _ ?_
  have hdvd : x i ∣ ∏ j ∈ m.support, x j ^ m j :=
    (dvd_pow_self (x i) hi).trans (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.2 hi))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem dvd_pow_of_mem_span {A : Type} [CommRing A] {d : ℕ} (x : Fin d → A) (p : A) (N₀ : ℕ)
    (hx : ∀ i, p ∣ x i ^ N₀) (a : A) (ha : a ∈ Ideal.span (Set.range x)) :
    p ∣ a ^ (d * N₀ + 1) := by
  obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  have h := Ideal.sum_pow_mem_span_pow Finset.univ (fun i => r i • x i) N₀
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← Ideal.mem_span_singleton]
  refine Ideal.span_le.2 ?_ h
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  simp only [smul_eq_mul, mul_pow]
  exact Dvd.dvd.mul_left ((hx i).trans (pow_dvd_pow _ (Nat.le_succ _))) _

theorem aug_nil : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 →
      (p : G.A 1) ∣ c.ev 1 f ^ N := by
  intro p O _ G d c
  classical
  choose Ni hNi using c.nil 1
  let N₀ := Finset.univ.sup Ni
  have hx : ∀ i, (p : G.A 1) ∣ c.x 1 i ^ N₀ := fun i =>
    (hNi i).trans (pow_dvd_pow _ (Finset.le_sup (Finset.mem_univ i)))
  obtain ⟨N₁, hN₁⟩ := (c.isEval 1).2 1
  refine ⟨d * N₀ + 1, fun f hf => ?_⟩
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N₁) f with hPdef
  have hR : (p : G.A 1) ∣ c.ev 1 (f - (P : MvPowerSeries (Fin d) O)) := by
    have h := hN₁ (f - P) (fun α hα => ?_)
    · simpa using h
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro i
    have : α i ≤ α.degree := by
      rw [Finsupp.degree]
      by_cases hi : α i = 0
      · rw [hi]; exact Nat.zero_le _
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hi)
    simpa using this.trans hα.le
  have hP : c.ev 1 (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x 1) P := by
    have : (c.ev 1).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (c.x 1) :=
      MvPolynomial.algHom_ext fun i => by simp [(c.isEval 1).1 i]
    exact congrArg (fun φ => φ P) this
  have hP0 : MvPolynomial.constantCoeff P = 0 := by
    rw [MvPolynomial.constantCoeff_eq, hPdef, coeff_trunc', if_pos (zero_le')]
    simpa using hf
  have ha := dvd_pow_of_mem_span (c.x 1) (p : G.A 1) N₀ hx _ (aeval_mem_span (c.x 1) P hP0)
  rw [← hP] at ha
  have hsub := sub_dvd_pow_sub_pow (c.ev 1 f) (c.ev 1 P) (d * N₀ + 1)
  rw [← map_sub] at hsub
  simpa using dvd_add (hR.trans hsub) ha

end GlobalTheory.AugNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
section
open IsLocalRing

namespace GlobalTheory

theorem exists_strictHenselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ hΩ
  obtain ⟨H, _, _, _, _, hflat, hmax, hbij, hind⟩ := _root_.GlobalTheory.Henselisation.exists_henselisation R
  let e : ResidueField R ≃+* ResidueField H := RingEquiv.ofBijective _ hbij
  letI algH : Algebra (ResidueField H) Ω :=
    ((algebraMap (ResidueField R) Ω).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (ResidueField H) Ω).comp e.toRingHom =
      (RingEquiv.refl Ω : Ω →+* Ω).comp (algebraMap (ResidueField R) Ω) := by
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  haveI : IsSepClosure (ResidueField H) Ω :=
    ⟨hΩ.sep_closed, Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl Ω) he⟩
  obtain ⟨T, _, _, _, _, hsc, hflat2, hmax2, ⟨e2⟩, hind2⟩ := _root_.GlobalTheory.exists_strictHenselisation_of_henselian H Ω
  letI algRT : Algebra R T := ((algebraMap H T).comp (algebraMap R H)).toAlgebra
  haveI : IsScalarTower R H T := IsScalarTower.of_algebraMap_eq' rfl
  haveI hloc : IsLocalHom (algebraMap R T) := by
    change IsLocalHom ((algebraMap H T).comp (algebraMap R H))
    infer_instance
  refine ⟨T, inferInstance, algRT, inferInstance, hloc, hsc, ?_, ?_, ?_, ?_⟩
  · haveI := hflat; haveI := hflat2
    exact Module.Flat.trans R H T
  · rw [IsScalarTower.algebraMap_eq R H T, ← Ideal.map_map, hmax, hmax2]
  · refine ⟨{ e2 with commutes' := ?_ }⟩
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    have h1 : algebraMap (ResidueField R) (ResidueField T) (residue R x) =
        algebraMap (ResidueField H) (ResidueField T) (residue H (algebraMap R H x)) := by
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue]; rfl
    have h2 : algebraMap (ResidueField H) Ω (residue H (algebraMap R H x)) =
        algebraMap (ResidueField R) Ω (residue R x) := by
      rw [RingHom.algebraMap_toAlgebra]
      simp only [RingHom.comp_apply]
      congr 1
      apply e.symm_apply_eq.mpr
      rfl
    show e2 (algebraMap (ResidueField R) (ResidueField T) (residue R x)) = _
    rw [h1, AlgEquiv.commutes, h2]
  · exact _root_.GlobalTheory.indEtale_localPieces_trans R H T hind hind2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLeStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  first | exact @GlobalTheory.TjCount.tj_cosets_finite_card_le | exact GlobalTheory.TjCount.tj_cosets_finite_card_le | (intros; apply GlobalTheory.TjCount.tj_cosets_finite_card_le <;> assumption)
end

