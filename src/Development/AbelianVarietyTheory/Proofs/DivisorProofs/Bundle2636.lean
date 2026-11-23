module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveSecondVariable
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOfMumfordBundleIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem cubN_cmp {T : Over S} (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂]
    [IsMonHom g₂] {U : Type} [CommGroup U] (v : (T ⟶ P₀.A) → (T ⟶ P₀.A) → U)
    {θ₁ : (T ⟶ P₁.A) → (T ⟶ P₁.A) → (T ⟶ P₁.A) → U} {θ₂ : (T ⟶ P₂.A) → (T ⟶ P₂.A) → (T ⟶ P₂.A) → U}
    (h₁ : IsCub θ₁) (h₂ : IsCub θ₂)
    (a₁ : ∀ x x' y, v (x * x') y * θ₁ (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) =
      θ₂ (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (v x y * v x' y))
    (a₂ : ∀ x y y', v x (y * y') * θ₁ (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) =
      θ₂ (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (v x y * v x y'))
    {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN θ₁ k 1 (x ≫ f₁) (y ≫ g₁) = cubN θ₂ k 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ k ∧
      cubN θ₁ k 1 (y ≫ g₁) (x ≫ f₁) = cubN θ₂ k 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ k := by
  have first : ∀ n : ℕ, v (x ^ n) y * cubN θ₁ n 1 (x ≫ f₁) (y ≫ g₁) =
      v 1 y * (cubN θ₂ n 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₁ (x ^ n) x y
      rw [MonObj.pow_comp, MonObj.pow_comp] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have second : ∀ n : ℕ, v x (y ^ n) * cubN θ₁ n 1 (y ≫ g₁) (x ≫ f₁) =
      v x 1 * (cubN θ₂ n 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₂ x (y ^ n) y
      rw [MonObj.pow_comp, MonObj.pow_comp, h₁.s01 (x ≫ f₁), h₁.s12 _ (x ≫ f₁), h₂.s01 (x ≫ f₂),
        h₂.s12 _ (x ≫ f₂)] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have a := first k
  have b := second k
  rw [hx] at a
  rw [hy] at b
  exact ⟨mul_left_cancel a, mul_left_cancel b⟩

theorem isRatio_cmp (hG : GlobalFnsSt) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A)
    (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    {r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))} {hr₁ : r₁.IsGen} (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩)
    {r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))} {hr₂ : r₂.IsGen} (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩)
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1)
    {T : Over S} {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : WeilCube.IsRatio c₁ k (x ≫ f₁) (y ≫ g₁) e) : WeilCube.IsRatio c₂ k (x ≫ f₂) (y ≫ g₂) e := by
  intro T' ρ z J₂ hJ₂
  obtain ⟨J₁, hJ₁, -⟩ := exists_good P₁.L P₁.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  obtain ⟨J, hJ, e₁, e₂⟩ := exists_good_join P₁.isLB P₂.isLB hJ₁ hJ₂
  have hx' : (ρ ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have hy' : (ρ ≫ y) ^ k = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have q₁ : Good P₁.L z (rl J) := (isPart_inl P₁.L P₂.L).good hJ
  have q₂ : Good P₂.L z (rr J) := (isPart_inr P₁.L P₂.L).good hJ
  obtain ⟨a, b⟩ := cubN_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (fun a b => val u (lift a b).left z J) (isCub_cubV c₁ q₁)
    (isCub_cubV c₂ q₂) (fun x x' y => _root_.GlobalTheory.Mum.Two.WeilCmp.AddFst.cmp_add_fst hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x x' y)
    (fun x y y' => _root_.GlobalTheory.Mum.Two.WeilCmp.add_snd hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x y y') hx' hy'
  rw [e₁, e₂] at a b
  simp only [Category.assoc] at a b
  have h := he T' ρ z J₁ hJ₁
  rw [a, b, ← _root_.mul_assoc] at h
  exact mul_right_cancel h

end GlobalTheory.Mum.Two.WeilCmp


open GlobalTheory.Mum.Two.WeilCmp in
theorem GlobalTheory.Mum.Two.weilIs_iff_of_lbIso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), IsMonHom f₁ → IsMonHom g₁ → IsMonHom f₂ → IsMonHom g₂ → LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∀ (F : Type) [Field F] (p : Sp F ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P₀.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P₁.A P₁.L k (x ≫ f₁) (y ≫ g₁) c ↔ WeilIs P₂.A P₂.L k (x ≫ f₂) (y ≫ g₂) c := by
  intro S _ P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ _ _ hw F _ p k x y hx hy c
  have hL := GlobalTheory.allSixLaws.1
  haveI : Nonempty P₁.A.left := ⟨(x ≫ f₁).left (⊥ : PrimeSpectrum F)⟩
  haveI : Nonempty P₂.A.left := ⟨(x ≫ f₂).left (⊥ : PrimeSpectrum F)⟩
  obtain ⟨r₁, hr₁, ⟨c₁⟩⟩ := PolAV_exists_cubical hL.cube P₁
  obtain ⟨r₂, hr₂, ⟨c₂⟩⟩ := PolAV_exists_cubical hL.cube P₂
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso S P₀ P₁ P₂ f₁ g₁ f₂ g₂ hw
  obtain ⟨u, hu, hn⟩ := GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection S P₀ P₁ P₂ f₁ g₁ f₂ g₂ u₀ hu₀
  have hx₁ : (x ≫ f₁) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₁ : (y ≫ g₁) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx₂ : (x ≫ f₂) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₂ : (y ≫ g₂) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨e₀, he₀⟩ := WeilCube.exists_isRatio c₁ k (x ≫ f₁) (y ≫ g₁) hx₁ hy₁
  have he₂ := isRatio_cmp P₀ P₁ P₂ hL.globalFns f₁ g₁ f₂ g₂ c₁ c₂ u hu hn hx hy he₀
  exact (WeilCube.weilIs_iff c₁ hL.globalFns P₁.isAb hx₁ hy₁ he₀ c).trans
    (WeilCube.weilIs_iff c₂ hL.globalFns P₂.isAb hx₂ hy₂ he₂ c).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatBox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

theorem compat_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {T' T₁' T₂' : Scheme.{0}} {p' : T' ⟶ B} {f' : T' ⟶ G} {p₁' : T₁' ⟶ B₁} {f₁' : T₁' ⟶ G₁} {p₂' : T₂' ⟶ B₂} {f₂' : T₂' ⟶ G₂} {h₁' : T' ⟶ T₁'} {h₂' : T' ⟶ T₂'} (we' : LB.Iso (L.pull f') (M.pull p')) (we₁' : LB.Iso (L₁.pull f₁') (M₁.pull p₁')) (we₂' : LB.Iso (L₂.pull f₂') (M₂.pull p₂')), BoxSq wM wL we' we₁' we₂' h₁' h₂' → ∀ (m : T ⟶ T') (m₁ : T₁ ⟶ T₁') (m₂ : T₂ ⟶ T₂'), m ≫ h₁' = h₁ ≫ m₁ → m ≫ h₂' = h₂ ≫ m₂ → m ≫ f' = f → m ≫ p' = p → m₁ ≫ f₁' = f₁ → m₁ ≫ p₁' = p₁ → m₂ ≫ f₂' = f₂ → m₂ ≫ p₂' = p₂ → GlobalTheory.UnifPullRig.CompatAlong we₁' we₁ m₁ → GlobalTheory.UnifPullRig.CompatAlong we₂' we₂ m₂ → GlobalTheory.UnifPullRig.CompatAlong we' we m := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂ hL hL₁ hL₂
    ep₁ ep₂ ef₁ ef₂ we Q T' T₁' T₂' p' f' p₁' f₁' p₂' f₂' h₁' h₂' we' we₁' we₂' Q' m m₁ m₂ hm₁ hm₂ hmf hmp hm₁f hm₁p
    hm₂f hm₂p H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  have bM : p y ∈ M.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f y ∈ L.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => p) (fun _ => qM ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bM)
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => f) (fun _ => qL ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bL)
  obtain ⟨J₁, hJ₁⟩ := exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := exists_good_at hL₂ y
  have e₀ := Q T (𝟙 T) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have e₁ := Q' T m y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have c₁ := H₁.stalk hm₁f hm₁p h₁ y (J₁ (p ≫ b₁)) (N₁ (f ≫ g₁))
    ((pt_of_eq ep₁ y) ▸ hJ₁ (p ≫ b₁)) ((pt_of_eq ef₁ y) ▸ hN₁ (f ≫ g₁))
  have c₂ := H₂.stalk hm₂f hm₂p h₂ y (J₂ (p ≫ b₂)) (N₂ (f ≫ g₂))
    ((pt_of_eq ep₂ y) ▸ hJ₂ (p ≫ b₂)) ((pt_of_eq ef₂ y) ▸ hN₂ (f ≫ g₂))
  simp only [Category.id_comp] at e₀
  rw [hmp, hmf, hm₁, hm₂, c₁, c₂, ← e₀] at e₁
  have e := mul_left_cancel e₁
  rw [eJ ⟨⟩, eN ⟨⟩] at e
  exact (gm_res_pull _ m y a₁ hy _).trans ((Category.id_comp m).symm ▸ e.trans (gm_res _ y a₂ hy _).symm)

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeOneDifferCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem compatibleForms_cocycles_differ_by_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z1) (k' : (KK κ' t').Z1) (f : Z1 (O κ t)) (f' : Z1 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H1.mk _ f' = m.pull1 (H1.mk _ f) → ∃ g, (KK κ' t').D0 g = (morMap m).p1 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H1.mk _ (m.coef.pullbackOneCocycle f) = H1.mk _ f' := h.symm
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h'
  have hinj := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.1.injective
  have hz : (morMap m).p1 k.1 - k'.1 ∈ (KK κ' t').Z1 :=
    sub_mem ((morMap m).z1 k).2 k'.2
  have h0 : (KK κ' t').fnMap.h1 (QuotientAddGroup.mk ⟨_, hz⟩ : (KK κ' t').H1) = 0 := by
    change (QuotientAddGroup.mk ((KK κ' t').fnMap.z1 ⟨_, hz⟩) : Cx.H1 _) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨g, ?_⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ
      have e := congrFun (congrFun (congrFun hg T) T') φ
      have e1 := congrFun (congrFun (congrFun hk (m.obj T)) (m.obj T')) (m.functor.map φ)
      have e2 := congrFun (congrFun (congrFun hk' T) T') φ
      refine e.trans ?_
      exact congrArg₂ (fun u v : T'.B ↦ u - v) e1.symm e2.symm
    · funext T
      rfl
  have h1 := hinj (h0.trans (map_zero (KK κ' t').fnMap.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeTwoDifferCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.ClsTwo

universe u

theorem cob_of_fn_cob {C : Type u} [Category.{0} C] (K : Cx C) (h : Function.Injective K.fnMap.h2)
    (z : K.T2) (hz : z ∈ K.Z2) (e : K.M0.c1)
    (he : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (e T T' φ) - e T T'' (φ ≫ ψ) + e T' T'' ψ = z.1 T T' T'' φ ψ) :
    ∃ g, K.D1 g = z := by
  have h0 : K.fnMap.h2 (QuotientAddGroup.mk ⟨z, hz⟩) = 0 := by
    change (QuotientAddGroup.mk (K.fnMap.z2 ⟨z, hz⟩) : (Cx.single K.M0).H2) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(e, 0), ?_⟩
    refine Prod.ext ?_ rfl
    funext T T' T'' φ ψ
    exact he T T' T'' φ ψ
  have h1 : (QuotientAddGroup.mk ⟨z, hz⟩ : K.H2) = 0 := h (h0.trans (map_zero _).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem cob_of_class_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H2.mk _ (m.coef.pullbackTwoCocycle f) = H2.mk _ f' := h.symm
  obtain ⟨e, he⟩ := H2.mk_eq_mk.1 h'
  refine cob_of_fn_cob (KK κ' t') (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.2.injective _
    (AddSubgroup.sub_mem _ ((morMap m).p2_mem_Z2_of_mem_Z2 k.2) k'.2) e ?_
  intro T T' T'' φ ψ
  have h1 := congrFun (congrFun (congrFun (congrFun (congrFun he T) T') T'') φ) ψ
  refine h1.trans ?_
  have h2 : (m.coef.pullbackTwoCocycle f).1 T T' T'' φ ψ = ((morMap m).p2 k.1).1 T T' T'' φ ψ :=
    (congrFun (congrFun (congrFun (congrFun (congrFun hk _) _) _) (m.functor.map φ)) (m.functor.map ψ)).symm
  have h3 := congrFun (congrFun (congrFun (congrFun (congrFun hk' T) T') T'') φ) ψ
  exact congrArg₂ (fun a b : (O κ' t').obj T'' ↦ a - b) h2 h3.symm

end GlobalTheory.PDForm.ClsTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLength
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem cInfAt_ratVal_on {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {κ : Type} [Fintype κ] {f : κ → X.Fn}
    {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a)) {G : (κ → ℂ) → ℝ} {O : Set (κ → ℂ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ G O) (hy : (fun a => ratVal (f a) y) ∈ O) :
    CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hyU g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hyU)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  have hev (z : CxPts X.str σ) (hz : z ∈ ptsIn X.str σ W) :
      (fun a => ev X.str σ W (resG X.X (hle a) (g a)) z) = fun a => ratVal (f a) z := by
    funext a
    rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, O, hW, hO, ?_, hG, ?_⟩
  · rw [hev y hW]; exact hy
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
    rw [hev z hz]

theorem cInfAt_neg_log_normSq_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : CxPts X.str σ} {u : X.Fn}
    (hu : UnitAt (under y) u) : CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2)) y := by
  have hO : IsOpen {w : Unit → ℂ | w () ≠ 0} := isOpen_ne_fun (continuous_apply ()) continuous_const
  have hG : ContDiffOn ℝ ∞ (fun w : Unit → ℂ => -Real.log (‖w ()‖ ^ 2)) {w | w () ≠ 0} := by
    intro w hw
    have h1 : ContDiffAt ℝ ∞ (fun w : Unit → ℂ => ‖w ()‖ ^ 2) w :=
      ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffAt
    have h2 : ‖w ()‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hw)
    exact (h1.log h2).neg.contDiffWithinAt
  exact cInfAt_ratVal_on (κ := Unit) (f := fun _ => u) (fun _ => hu.regAt) hO hG (ratVal_ne_zero hu)

end GlobalTheory.ChernCalc

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChernCalc.cInfAt_logUnit_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i
  refine (GlobalTheory.ChernCalc.cInfAt_neg_log_normSq_ratVal hu).add ?_ |>.congr (Eventually.of_forall fun z => sub_eq_add_neg _ _)
  have := X.smooth_str
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
  have hev := ((_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m k E H hH y A hA τ).2 c hc)
  obtain ⟨O, hOP, hOo, hyO⟩ := eventually_nhds_iff.1 hev
  have hS : IsOpen (c.e.source ∩ c.e ⁻¹' O) := c.e.isOpen_inter_preimage hOo
  refine cInfAt_of_chart hS c ?_ hc ⟨hc, hyO⟩
  intro v hv
  have hvO : v ∈ O := by
    have := hv.2.2
    rwa [Set.mem_preimage, c.e.right_inv hv.1] at this
  obtain ⟨hsm, hpd⟩ := hOP v hvO
  have hd := (ldPart_grD_smooth _ _ _ v hsm hpd).2 i
  have hpos := ((_root_.GlobalTheory.ChernCalc.ldPart_posDef_spec _ _ hpd).2.1 i).1
  exact (hd.log hpos.ne').neg.contDiffWithinAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegree
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_mul_topDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H hM ρ hρ
  refine ⟨?_, ?_⟩
  · intro c c' y hy hc hc'
    have hA := (E.nonempty (under y)).choose_spec
    simp only [topDens]
    rw [chernTop_frame_chart_trans E O H hM _ hy c c' hc hc' hA hA]
    ring
  · intro c
    refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density c.e (d := fun z => ρ z * topDens E H c z) (isOpen_ptsIn O) ?_
    intro y hy hc
    have hA := (E.nonempty (under y)).choose_spec
    refine ⟨fun v => ρ (c.e.symm v) * chernTop (MvPolynomial.X ((), X.dim))
      (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v, ?_, ?_⟩
    · have h1 : ContinuousAt (fun v => ρ (c.e.symm v)) (c.e y) :=
        hρ.continuousAt.comp (c.e.continuousAt_symm (c.e.map_source hc))
      have hsm := hM.mContDiffAt_chart hy c hc hA ()
      have hu := hM.isUnit_det_chart hy c hc hA ()
      have h2 : ContinuousAt (fun v => chernTop (MvPolynomial.X ((), X.dim))
          (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v) (c.e y) := by
        simp only [_root_.GlobalTheory.GoodTop.chernTop_eq_mixTop]
        refine continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_)
        refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (fun i a b p q => ?_)
        exact ((MContDiffAt.curv (j := 0) hsm hu (by norm_num) (coordVec a) (coordVec b)) p q).continuousAt
      exact h1.mul h2
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, c.e.open_source.mem_nhds hc,
        GlobalTheory.FrameLift.eventually_mem hA] with z hz hzc hzA
      simp only [topDens, c.e.left_inv hzc]
      rw [hM.chernTop_frame _ hz c hzc (E.nonempty (under z)).choose_spec hzA]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem powAt_coe_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    ((powAt G x k : Ev n) : Alt n) = ∑ i, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) := by
  simp [powAt, Matrix.trace]

theorem transAt_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    transAt G G' x k = ∑ a, ∑ i ∈ Finset.range k, ∑ p, ∑ q,
      (conn G x (coordVec a) - conn G' x (coordVec a)) p q •
        ((((curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i) q p : Ev n) : Alt n) * dz a) := by
  unfold transAt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def, mul_assoc]

theorem powAt_transAt_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  intro n r _ _ G G' v hG hGu hG' hG'u k
  obtain ⟨hconst, hsum, hsmul, hmul⟩ := _root_.GlobalTheory.ChernCalc.smooth_coeff_closure n v
  obtain ⟨_, hdsum, _, _, _⟩ := _root_.GlobalTheory.CxForm.dbarAt_local_calculus n v
  have hpe : ∀ i, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr
      (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) S) v) ∧
      dbarAt (fun x => (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n)) v = 0 :=
    fun i => _root_.GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar n r G G' v hG hGu hG' hG'u k 0 i i
  have hpf : (fun x => ((powAt G x k : Ev n) : Alt n)) =
      fun x => ∑ i ∈ Finset.univ, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) :=
    funext fun x => powAt_coe_eq_sum G G' x k
  refine ⟨?_, ?_, ?_⟩
  · simp only [powAt_coe_eq_sum G G']
    exact hsum r Finset.univ _ fun i _ => (hpe i).1
  · rw [hpf, hdsum r Finset.univ _ fun i _ S => ((hpe i).1 S).differentiableAt (by simp)]
    exact Finset.sum_eq_zero fun i _ => (hpe i).2
  · have hη : ∀ a p q, ContDiffAt ℝ ∞
        (fun x => (conn G x (coordVec a) - conn G' x (coordVec a)) p q) v := fun a p q =>
      ((hG.conn hGu (j := ∞) (by simp) (coordVec a)).sub
        (hG'.conn hG'u (j := ∞) (by simp) (coordVec a))) p q
    simp only [transAt_eq_sum]
    refine hsum _ Finset.univ _ fun a _ => hsum _ _ _ fun i _ => hsum _ Finset.univ _ fun p _ =>
      hsum _ Finset.univ _ fun q _ => hsmul _ _ (hη a p q) ?_
    exact hmul _ _ (_root_.GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1 (hconst (dz a))

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem term_eq_const_psi_theta : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ : FractionRing V, ∀ (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → w.IsGen → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ a : V, l * coef s g' w mu = κ * algebraMap V (FractionRing V) (r * a) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit a) := by
  intro V _ _ _ D θ hθ s
  obtain ⟨c₀, hc₀, hc⟩ := GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero V D
  obtain ⟨κ₀, hκ⟩ := GlobalTheory.T.degreeOneFamily_term_eq_psi_thetaValue_character V D θ hθ s
  refine ⟨κ₀ / c₀, fun g g' w l hpull hw hint mu r hr => ?_⟩
  obtain ⟨gam, hgam, vgam⟩ := GlobalTheory.T.exists_integralGenerator_of_psiCoordinate V D mu r hr
  obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_base_element_theta_term_integralPoint V D θ g g' w l hpull hint mu gam hgam
  refine ⟨a, ?_, fun h => _root_.GlobalTheory.unit_of_isUnit_cst_closedPoint V a (hu h)⟩
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have e₁ := hκ g' w hw mu z J hJ
  have e₂ := hc z J hJ
  have e₃ := vgam z J hJ
  have e₄ := ha z J hJ
  rw [_root_.mul_assoc (GlobalTheory.UT.cst _ z _), mul_comm (rigV D _ z J).val, e₂, e₃] at e₁
  have e₅ : GlobalTheory.UT.cst (FractionRing V) z (l * coef s g' w mu * c₀) =
      GlobalTheory.UT.cst (FractionRing V) z (κ₀ * (algebraMap V (FractionRing V) r * algebraMap V (FractionRing V) a)) := by
    simp only [CoefBasic.cst_eq, map_mul] at e₁ e₄ ⊢
    rw [← e₄]
    linear_combination CoefBasic.cstH z l * e₁
  have e₆ := CoefBasic.cstH_inj z ((CoefBasic.cst_eq _ _).symm.trans (e₅.trans (CoefBasic.cst_eq _ _)))
  rw [map_mul]
  field_simp
  linear_combination e₆

end GlobalTheory.Poinc.IntTerm
end
end

