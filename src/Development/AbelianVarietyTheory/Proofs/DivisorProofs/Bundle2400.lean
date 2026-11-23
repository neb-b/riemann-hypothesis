module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem frame_coords_lift {W K₀ K₁ : Type} [CommRing W] [IsDomain W] [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁)
    (hi₀ : Function.Injective i₀) (hi₁ : ∀ a, i₁ a ≠ 0 → IsUnit a) {I : Type} {g : ℕ} (ϑ ϑ' : I → W)
    (J J' : I → Fin g → W)
    (hind : ∀ (c₀ : K₁) (c : Fin g → K₁), (∀ i, c₀ * i₁ (ϑ' i) + ∑ j, c j * i₁ (J' i j) = 0) → c₀ = 0 ∧ c = 0)
    (a₀ : K₀) (M₀ : Matrix (Fin g) (Fin g) K₀) (c₀ : Fin g → K₀)
    (h0ϑ : ∀ i, i₀ (ϑ i) = a₀ * i₀ (ϑ' i))
    (h0J : ∀ i j, i₀ (J i j) = a₀ * ∑ l, M₀ j l * i₀ (J' i l) + c₀ j * i₀ (ϑ' i))
    (a₁ : K₁) (M₁ : Matrix (Fin g) (Fin g) K₁) (c₁ : Fin g → K₁) (ha₁ : a₁ ≠ 0)
    (h1ϑ : ∀ i, i₁ (ϑ i) = a₁ * i₁ (ϑ' i))
    (h1J : ∀ i j, i₁ (J i j) = a₁ * ∑ l, M₁ j l * i₁ (J' i l) + c₁ j * i₁ (ϑ' i)) :
    ∃ (a : W) (M : Matrix (Fin g) (Fin g) W), i₀ a = a₀ ∧ i₁ a = a₁ ∧ i₀.mapMatrix M = M₀ ∧
      i₁.mapMatrix M = M₁ := by
  let u : I → Option (Fin g) → W := fun i o => Option.elim o (ϑ' i) (J' i)
  have hind' : ∀ c : Option (Fin g) → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0 := by
    intro c hc
    obtain ⟨h1, h2⟩ := hind (c none) (fun j => c (some j)) (fun i => by simpa [Fintype.sum_option, u] using hc i)
    funext o
    cases o with
    | none => exact h1
    | some j => exact congrFun h2 j
  obtain ⟨z, hz, hϑz⟩ := _root_.GlobalTheory.MBLow.coords_integral_of_closed_indep W K₀ K₁ i₀ i₁ hi₀ hi₁ I (Option (Fin g)) u hind' ϑ
    (fun o => Option.elim o a₀ 0) (fun i => by simp [Fintype.sum_option, u, h0ϑ])
  have hz0 : ∀ j, z (some j) = 0 := fun j => hi₀ (by simpa using hz (some j))
  have ha₀ : i₀ (z none) = a₀ := by simpa using hz none
  have ha : i₁ (z none) = a₁ := by
    have := hind (i₁ (z none) - a₁) 0 (fun i => by
      have e := congrArg i₁ (hϑz i)
      simp only [Fintype.sum_option, hz0, zero_mul, Finset.sum_const_zero, add_zero, map_mul, h1ϑ, u,
        Option.elim_none] at e
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      linear_combination -e)
    exact sub_eq_zero.1 this.1
  have hN : ∀ j, ∃ N : Option (Fin g) → W, (∀ o, i₀ (N o) = Option.elim o (c₀ j) (fun l => a₀ * M₀ j l)) ∧
      ∀ i, J i j = ∑ o, N o * u i o := by
    intro j
    exact _root_.GlobalTheory.MBLow.coords_integral_of_closed_indep W K₀ K₁ i₀ i₁ hi₀ hi₁ I (Option (Fin g)) u hind' (fun i => J i j) _ (fun i => by
      simp [Fintype.sum_option, u, h0J, Finset.mul_sum, _root_.mul_assoc]; ring)
  choose N hN0 hNJ using hN
  have hN1 : ∀ j l, i₁ (N j (some l)) = a₁ * M₁ j l := by
    intro j
    have := hind (i₁ (N j none) - c₁ j) (fun l => i₁ (N j (some l)) - a₁ * M₁ j l) (fun i => by
      have e := congrArg i₁ (hNJ j i)
      rw [h1J] at e
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_option, u, Option.elim_none, Option.elim_some, map_add (f := _), map_sum, map_mul, Finset.mul_sum] at e
      simp only [sub_mul, Finset.sum_sub_distrib, _root_.mul_assoc]
      linear_combination -e)
    intro l
    exact sub_eq_zero.1 (congrFun this.2 l)
  obtain ⟨v, hv⟩ := hi₁ (z none) (by rw [ha]; exact ha₁)
  have hne₀ : a₀ ≠ 0 := by rw [← ha₀, ← hv]; exact (v.map i₀.toMonoidHom).ne_zero
  refine ⟨z none, Matrix.of fun j l => ↑v⁻¹ * N j (some l), ha₀, ha, ?_, ?_⟩
  · ext j l
    have h1 : i₀ (↑v⁻¹ : W) = a₀⁻¹ := by
      rw [← ha₀, ← hv]; exact map_units_inv i₀ v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_mul, h1, Option.elim_some, hN0]
    field_simp
  · ext j l
    have h1 : i₁ (↑v⁻¹ : W) = a₁⁻¹ := by
      rw [← ha, ← hv]; exact map_units_inv i₁ v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_mul, h1, Option.elim_some, hN1]
    field_simp

theorem thJet_frameChange_castDim {K : Type} [Field K] [CharZero K] (x : KeyIn K) (th : x.P.L.Sec) (hth) (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv)
    (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K)
    (hth' : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ a * LB.Sec.f th i) (hv' : ∀ i, IsLieComb (M i) v (x.v i))
    {g : ℕ} (hg : x.P.g = g) (m : ℕ) (hm : Odd m) {I : Type} (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ ϑ' : I → K)
    (J J' : I → Fin g → K)
    (h1 : ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ hg m pt ϑ J) (h2 : ThJet x hg m pt ϑ' J') :
    (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin g → K, ∀ i j,
      J' i j = a * ∑ l, M.reindex (finCongr hg) (finCongr hg) j l * J i l + c j * ϑ i := by
  cases x
  subst hg
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; exact (Nat.not_odd_zero hm))
  simpa using _root_.GlobalTheory.MBLow.JetUniq.thJet_change K _ _ _ _ th hth v hv _ _ _ _ a M hth' hv' m hm hm0 I pt ϑ ϑ' J J' h1 h2

theorem keyValue_twoFibres : ∀ κ : Rule, Rule4 κ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] [IsIntegrallyClosed W] [CharZero W] (K₀ K₁ : Type) [Field K₀] [CharZero K₀] [Field K₁] [IsAlgClosed K₁] [CharZero K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (P : PolAV (Sp W)) (x₀ : KeyIn K₀) (x₁ : KeyIn K₁) (g : ℕ) (h₀ : x₀.P.g = g) (h₁ : x₁.P.g = g) (m : ℕ), P.g = g → Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ P.A)) (p₀ : I → (baseOver (Sp K₀) ⟶ x₀.P.A)) (p₁ : I → (baseOver (Sp K₁) ⟶ x₁.P.A)) (φ₀ : x₀.P.A.left ⟶ P.A.left) (φ₁ : x₁.P.A.left ⟶ P.A.left), (∀ a, pt a ^ (m ^ 2) = 1) → IsGrpPullback x₀.P.A P.A (spMap i₀) φ₀ → IsGrpPullback x₁.P.A P.A (spMap i₁) φ₁ → LBIso x₀.P.L (P.L.pull φ₀) → LBIso x₁.P.L (P.L.pull φ₁) → (∀ a, (p₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) → (∀ a, (p₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left) → (∀ z : baseOver (Sp K₁) ⟶ x₁.P.A, z ^ (m ^ 2) = 1 → ∃ a, p₁ a = z) → ∀ (ϑ : I → W) (J : I → Fin g → W) (k : W), ThJet x₀ h₀ m p₀ (fun a => i₀ (ϑ a)) (fun a j => i₀ (J a j)) → ThJet x₁ h₁ m p₁ (fun a => i₁ (ϑ a)) (fun a j => i₁ (J a j)) → (κ K₀ x₀ : K₀) = i₀ k → (κ K₁ x₁ : K₁) = i₁ k := by
  intro κ hκ W _ _ _ _ _ _ K₀ K₁ _ _ _ _ _ i₀ i₁ hi₀ hi₁ P x₀ x₁ g h₀ h₁ m hP hm hm3 I pt p₀ p₁ φ₀ φ₁ hpt hpb₀ hpb₁
    hL₀ hL₁ hc₀ hc₁ hsurj ϑ J k hJ₀ hJ₁ hk
  obtain ⟨hHom, -, -, hFam⟩ := hκ
  have hPg : 1 ≤ P.g := hP ▸ h₀ ▸ x₀.g_pos
  obtain ⟨y, rfl⟩ := _root_.GlobalTheory.MBLow.exists_keyIn_local W P hPg
  have hmu : IsUnit (m : W) := hi₁ _ (by rw [map_natCast]; exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨ϑ', J', hy⟩ := _root_.GlobalTheory.MBLow.exists_thJet_local W y g hP m hm hmu I pt hpt
  obtain ⟨th₀, hth₀, v₀, hv₀, hA₀⟩ := _root_.GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback W K₀ i₀ y x₀.P φ₀ x₀.g_pos x₀.rig x₀.rig_gen (h₀.trans hP.symm) hpb₀ hL₀
  obtain ⟨th₁, hth₁, v₁, hv₁, hA₁⟩ := _root_.GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback W K₁ i₁ y x₁.P φ₁ x₁.g_pos x₁.rig x₁.rig_gen (h₁.trans hP.symm) hpb₁ hL₁
  have hJy₀ := _root_.GlobalTheory.MBLow.thJet_of_keyAtMap W K₀ i₀ y ⟨x₀.P, x₀.g_pos, x₀.rig, x₀.rig_gen, th₀, hth₀, v₀, hv₀⟩ φ₀ hA₀ g hP h₀ m I pt p₀ ϑ' J' hc₀ hy
  have hJy₁ := _root_.GlobalTheory.MBLow.thJet_of_keyAtMap W K₁ i₁ y ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ φ₁ hA₁ g hP h₁ m I pt p₁ ϑ' J' hc₁ hy
  obtain ⟨a₀, M₀, ha₀, hth0, hv0⟩ := _root_.GlobalTheory.MBLow.TwoData.exists_scalar_matrix K₀ x₀.P th₀ x₀.th v₀ x₀.v hth₀ x₀.th_ne hv₀ x₀.basis
  obtain ⟨a₁, M₁, ha₁, hth1, hv1⟩ := _root_.GlobalTheory.MBLow.TwoData.exists_scalar_matrix K₁ x₁.P th₁ x₁.th v₁ x₁.v hth₁ x₁.th_ne hv₁ x₁.basis
  obtain ⟨hu0ϑ, c₀, hu0J⟩ := thJet_frameChange_castDim x₀ th₀ hth₀ v₀ hv₀ a₀ M₀ hth0 hv0 h₀ m hm p₀ _ _ _ _ hJy₀ hJ₀
  obtain ⟨hu1ϑ, c₁, hu1J⟩ := thJet_frameChange_castDim x₁ th₁ hth₁ v₁ hv₁ a₁ M₁ hth1 hv1 h₁ m hm p₁ _ _ _ _ hJy₁ hJ₁
  have hind := _root_.GlobalTheory.MBLow.TRank.main K₁ ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ g h₁ m hm hm3 I p₁ hsurj _ _ hJy₁
  obtain ⟨u, hu⟩ := hFam W y
  have hκy₀ := hu K₀ i₀ ⟨x₀.P, x₀.g_pos, x₀.rig, x₀.rig_gen, th₀, hth₀, v₀, hv₀⟩ ⟨φ₀, hA₀⟩
  have hκy₁ := hu K₁ i₁ ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ ⟨φ₁, hA₁⟩
  have hH₀ := hHom K₀ x₀.P x₀.g_pos x₀.rig x₀.rig_gen th₀ hth₀ v₀ hv₀ x₀.th x₀.th_ne x₀.v x₀.basis a₀ M₀ hth0 hv0
  have hH₁ := hHom K₁ x₁.P x₁.g_pos x₁.rig x₁.rig_gen th₁ hth₁ v₁ hv₁ x₁.th x₁.th_ne x₁.v x₁.basis a₁ M₁ hth1 hv1
  obtain ⟨a, M, ha0, ha1, hM0, hM1⟩ := frame_coords_lift i₀ i₁ hi₀ hi₁ ϑ ϑ' J J' hind a₀ _ c₀ hu0ϑ hu0J a₁ _ c₁ ha₁ hu1ϑ hu1J
  have H₀ : a₀ ^ 8 * (κ K₀ x₀ : K₀) = M₀.det ^ 4 * i₀ u := by rw [← hκy₀]; simpa using hH₀
  have H₁ : a₁ ^ 8 * (κ K₁ x₁ : K₁) = M₁.det ^ 4 * i₁ u := by rw [← hκy₁]; simpa using hH₁
  have e0 : a ^ 8 * k = M.det ^ 4 * u := by
    apply hi₀
    rw [map_mul, map_mul, map_pow, map_pow, ha0, RingHom.map_det, hM0, Matrix.det_reindex_self, ← hk, H₀]
  have e1 := congrArg i₁ e0
  rw [map_mul, map_mul, map_pow, map_pow, ha1, RingHom.map_det, hM1, Matrix.det_reindex_self, ← H₁] at e1
  exact (mul_left_cancel₀ (pow_ne_zero 8 ha₁) e1).symm

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPer

theorem prod_psum_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {U : Type} [CommGroup U]
    (H : ((G ⊗ G).left ⟶ G.left) → U) :
    ∏ K : ULift.{0} (Finset (Fin 2)), H (psum G (x2 G) K.down).left ^ ((-1 : ℤ) ^ (2 - K.down.card)) =
      H (psum G (x2 G) {0, 1}).left * (H (psum G (x2 G) {0}).left)⁻¹ * (H (psum G (x2 G) {1}).left)⁻¹ *
        H (psum G (x2 G) ∅).left := by
  refine (Fintype.prod_equiv Equiv.ulift _
    (fun I => H (psum G (x2 G) I).left ^ ((-1 : ℤ) ^ (2 - I.card))) fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q₂ : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₂, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem periods_alg {U : Type} [CommGroup U] {X : Type} [AddCommGroup X] {P : Type} [Mul P] (c : X → P)
    (c_add : ∀ x y, c (x + y) = c x * c y) (t : X → X → U) (θ : P → P → P → U) (symm : ∀ x y, t x y = t y x)
    (add : ∀ x x' y, t (x + x') y * θ (c x) (c x') (c y) = t x y * t x' y) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (a b : Fin r → X) :
    (∏ i, ∏ j, t (a i + b i) (a j + b j) ^ W i j) * (∏ i, ∏ j, t (a i) (a j) ^ W i j)⁻¹ *
        (∏ i, ∏ j, t (b i) (b j) ^ W i j)⁻¹ =
      (∏ i, ∏ j, (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j)) * ∏ i, ∏ j, t (a i) (b j) ^ ((W + W.transpose) i j) := by
  have base : ∀ x x' y y' : X, t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ =
      (θ (c x) (c x') (c y * c y') * θ (c y) (c y') (c x) * θ (c y) (c y') (c x'))⁻¹ * (t x y' * t y x') := by
    intro x x' y y'
    have e₁ := add x x' (y + y')
    have e₂ := add y y' x
    have e₃ := add y y' x'
    rw [c_add] at e₁
    have s₁ := symm x (y + y')
    have s₂ := symm x' (y + y')
    have s₃ := symm y x
    have s₄ := symm y' x
    have s₅ := symm y' x'
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃
    have b₁ := E s₁; have b₂ := E s₂; have b₃ := E s₃; have b₄ := E s₄; have b₅ := E s₅
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ b₃ b₄ b₅ ⊢
    linear_combination (norm := abel) a₁ + a₂ + a₃ + b₁ + b₂ + b₃ + b₄ + b₅
  have hij : ∀ i j, t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ * (t (b i) (b j) ^ W i j)⁻¹ =
      (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j) * (t (a i) (b j) ^ W i j * t (a j) (b i) ^ W i j) := by
    intro i j
    rw [← inv_zpow, ← inv_zpow, ← mul_zpow, ← mul_zpow, base, zpow_neg, ← inv_zpow, ← mul_zpow, mul_zpow]
  have hc : ∏ i, ∏ j, t (a j) (b i) ^ W i j = ∏ i, ∏ j, t (a i) (b j) ^ W j i := Finset.prod_comm
  calc _ = ∏ i, ∏ j, (t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ *
        (t (b i) (b j) ^ W i j)⁻¹) := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = _ := Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hij i j
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Matrix.add_apply, Matrix.transpose_apply, zpow_add]
      rw [hc]

end GlobalTheory.Mum.TensPer

namespace GlobalTheory.Mum.TensPer
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem groupSchemePartialSum_twoPoints_empty : psum G (x2 G) ∅ = 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_first : psum G (x2 G) {0} = fst G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_second : psum G (x2 G) {1} = snd G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_both : psum G (x2 G) {0, 1} = fst G G * (snd G G * 1) := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] by decide]
  rfl

end GlobalTheory.Mum.TensPer


open GlobalTheory.Mum.TensPer in
theorem GlobalTheory.Mum.Tens.tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : D.toPre.X, val (D.toPre.tau (x + x') y) (𝟙 _) z J *
      cubV D.toPre.cub z J (cP D.toPre (TK R) x) (cP D.toPre (TK R) x') (cP D.toPre (TK R) y) =
      val (D.toPre.tau x y) (𝟙 _) z J * val (D.toPre.tau x' y) (𝟙 _) z J :=
    fun x x' y => GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ D.tau_bimult x x' y
  have hsym : ∀ x y : D.toPre.X, val (D.toPre.tau x y) (𝟙 _) z J = val (D.toPre.tau y x) (𝟙 _) z J :=
    fun x y => GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ x y
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (T.w.s (fun k => J (D'.toPre.xK y ≫ tensφ T.pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (T.w.s j) = gm m' z _ (T.w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, T.c_pr]; rfl
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, T.c_pr]; rfl
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, T.psi (a + b) z J J' hJ hJ', T.psi a z J J' hJ hJ', T.psi b z J J' hJ hJ', T.psi 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (D.toPre.tau (T.xe 0 i) (T.xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show T.xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (twist_vector_at_zero D J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (D.toPre.tau (T.xe (a + b) i) (T.xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (D.toPre.tau (T.xe a i + T.xe b i) (T.xe a j + T.xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add (f := _)]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cP D.toPre (TK R)) (cPoint_add D.toPre (TK R))
    (fun x y => val (D.toPre.tau x y) (𝟙 _) z J) (cubV D.toPre.cub z J) hsym hadd W (T.xe a) (T.xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharacters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare

theorem q_comm_of_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a : D.P.A ⟶ D.P.A) (F : thickObj R I e G ⟶ thickObj R I e G)
    (hF : F.left ≫ g.pG.left = g.pG.left ≫ a.left) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    have := hF
    simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left] at this
    simpa [Category.assoc] using this
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
    have h1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w g.q
    have h2 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [h1, h2]

theorem torus_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  intro R _ _ I D e G _ _ g a a' _ _ h' u hu h₀ F hF
  have hb : IsMonHom ((Over.pullback (thick R I e)).map a) := inferInstance
  have hq := q_comm_of_isCoordEnd g a F hF.1
  have hd : (g.i ≫ F) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g.isKernel.w, Category.assoc, IsMonHom.one_hom]
  obtain ⟨t, ht⟩ : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X,
      t ≫ g.i = g.i ≫ F :=
    ⟨g.isKernel.lift _ _ hd, g.isKernel.lift_fst _ _ hd⟩
  refine ⟨t, fun χ => unit_ext fun y hy => ?_, ht.symm⟩
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB y
  have hJ : Good D.P.L y J := hJ
  have := g.q_hom
  have v₁ := val_torus g χ hJ t 1
  have v₂ := val_torus g (h' χ) hJ (𝟙 _) 1
  rw [_root_.mul_one, val_unit g _ hJ, _root_.mul_one] at v₁ v₂
  rw [ht] at v₁
  rw [Category.id_comp] at v₂
  have e1 : TorusCoord.im g g.i = 1 := (im_congr g (x' := 1) (by
    rw [g.isKernel.w, MonObj.one_comp, Hom.one_def])).trans (im_one g)
  have v₃ : val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) g.i.left y J = 1 :=
    (val_pull_lift u χ g.pG ((Over.map (thick R I e)).map g.i) hJ).trans
      ((congrArg _ e1).trans (val₂_axis D.P.isAb D.P.isLB a' a u hu h₀ hJ _))
  have v₄ := (hF.2 χ _ g.i.left y J hJ).trans ((congrArg₂ (· * ·) v₂ v₃).trans (_root_.mul_one _))
  refine (gm_res _ y (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans
    ((gm_pull (𝟙 _) t.left y ⊤ trivial _).trans ?_)
  rw [Category.id_comp]
  rw [Over.comp_left] at v₁
  exact v₁.symm.trans v₄

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem isCoordEnd_thickMap_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  intro R _ _ I D A G _ _ U e a a' h' u F F' hF hF'
  have hq := U.gt_q e
  have hO : GlobalTheory.LevelCompat.thickMapOver I e G ≫ (U.gt (e + 1)).pG = (U.gt e).pG := Over.OverMorphism.ext hq
  have hL : ∀ χ, thickMap R I e G ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
    intro χ
    have : GlobalTheory.LevelCompat.thickMapOver I e G ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG =
        lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
      simp only [comp_lift, comp_toUnit_assoc, hO]
    exact congrArg (·.left) this
  refine GlobalTheory.TorusCoord.ext_of_val (U.gt (e + 1)) _ _ ?_ ?_
  · calc (thickMap R I e G ≫ F'.left) ≫ (U.gt (e + 1)).pG.left
          = thickMap R I e G ≫ ((U.gt (e + 1)).pG.left ≫ a.left) := by rw [Category.assoc, hF'.1]
      _ = (U.gt e).pG.left ≫ a.left := by rw [← Category.assoc, hq]
      _ = F.left ≫ (U.gt e).pG.left := hF.1.symm
      _ = (F.left ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left := by rw [Category.assoc, hq]
  · intro χ w J hJ
    have e1 := hF'.2 χ _ (thickMap R I e G) w J hJ
    have e2 := hF.2 χ _ (𝟙 _) w J hJ
    rw [Category.id_comp] at e2
    rw [e1, ← val_pull hJ, val_corr hJ (U.gt_t e χ), e2]
    congr 1
    · have e3 := val_pull hJ ((U.gt (e + 1)).t (h' χ)) (thickMap R I e G) (𝟙 _)
      rw [Category.id_comp] at e3
      rw [← e3, val_corr hJ (U.gt_t e _)]
    · rw [val_pull hJ, val_pull hJ, hL, Category.id_comp]

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffProdOneOneForms
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

open GlobalTheory.GoodMetric.LinSubst

theorem sum_det_rowSel_mul {n : ℕ} (F : (Fin n → Fin n) → ℂ) :
    ∑ c : Fin n → Fin n, (rowSel c).det * F c =
      ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * F u := by
  classical
  symm
  refine Finset.sum_of_injOn (fun u : Equiv.Perm (Fin n) => (u : Fin n → Fin n))
    (fun u _ v _ h => DFunLike.coe_injective h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro c _ hc
    rw [det_rowSel_of_not_injective, zero_mul]
    intro hinj
    exact hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  · intro u _
    rw [det_rowSel_perm]

theorem topCoeff_prod_forms {n : ℕ} (k : Fin n → Fin n → Fin n → ℂ) :
    topCoeff (∏ i, ∑ a, ∑ b, MvPolynomial.C (k i a b) * MvPolynomial.X (a, b)) =
      ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i b => k i (u i) b).det := by
  classical
  rw [← sum_det_rowSel_mul (fun c => (Matrix.of fun i b => k i (c i) b).det)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum,
    ← sum_prod_mul_det_rowSel (Matrix.of fun i b => k i (c i) b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, topCoeff_prod_X_pair]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.GoodTop
end
end

