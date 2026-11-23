module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AbPackage

theorem exists_unit_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val u r z J * (val u' r z J)⁻¹ :=
    (gm_res r z le trivial _).trans ((val_of t r z J PEmpty.elim (fun k => k.elim)).symm.trans
      ((hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ (val_inv _ _)))))
  exact (inv_mul_cancel_right _ _).symm.trans (congrArg (· * val u' r z J) e.symm)

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]


omit [IsCommMonObj B] in
theorem exists_rigidified_sym {L : LB B.left} (hL : L.IsLB)
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec B)) (LB.oneGen L) := by
  have he : eSec B ≫ (ι[B]).left = eSec B :=
    congrArg (fun q => q.left) (show η[B] ≫ GrpObj.inv = η[B] by simp)
  let n : B.left ⟶ B.left := (toUnit B).left ≫ eSec B
  have hn : eSec B ≫ n = eSec B := by
    rw [← Category.assoc, show eSec B ≫ (toUnit B).left = 𝟙 _ from
      congrArg (fun q => q.left) (show η[B] ≫ toUnit B = 𝟙 _ by simp), Category.id_comp]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(ι[B]).left, 𝟙 _]) (ε' := ![1, -1])
    (fun V _ k => by
      have e : n ≫ (ι[B]).left = n := by rw [Category.assoc, he]
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, e])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, hn, mul_inv_cancel, val_one]

theorem exists_cp (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (L : RigLB B)
    (h₁ : ∃ t : LB.Gen (Theta B L.L), t.IsGen)
    (h₂ : ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) :
    ∃ M : CP B, M.L = L := by
  obtain ⟨t, ht⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised L.isLB t ht
  obtain ⟨u, hu, hr⟩ := exists_rigidified_sym L.isLB s hs
  exact ⟨CP.ofSurjective (surjective_cube hG hB) L (GlobalTheory.AbLaw.Cube.cubicalOfNormalised hG hB L t' ht' hn) u hu hr, rfl⟩

theorem exists_isCPMap_of_iso (hG : GlobalFnsSt) {S' : Scheme.{0}} {f : S' ⟶ S} {B' : Over S'} [GrpObj B']
    [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B') {β : B'.left ⟶ B.left}
    {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen) : ∃ v, IsCPMap M' M f β hw v := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) hr M'.L.rigGen
  let b : Γ(B'.left, ⊤)ˣ := pullU B'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ B') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ β)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull β).U (fun _ => J (x.left ≫ β)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ β)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left B'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ β) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

theorem abelian_cp : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  intro hG S B _ _ hB
  refine ⟨exists_cp hG hB, fun S' f B' _ _ hB' M M' β h _ ⟨w, hg⟩ => ⟨h, ?_⟩⟩
  exact exists_isCPMap_of_iso hG hB' M M'
    (fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm) w hg

end GlobalTheory.AbPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AdditionTensor

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} {K : Type} [Fintype K]

noncomputable def svalHom (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) : SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalHom_smul (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    svalHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) (scal p c)).trans (gs_pull r p z ⊤ trivial _)))

end

theorem sum_sval_mul_eq_zero {F : Type} [CommRing F] {Z Y₁ Y₂ T : Scheme.{0}} {L : LB Z}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂))
    (h : ∑ i, TensorProduct.tmul F (a i) (b i) = 0) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂) (e : r₁ ≫ p₁ = r₂ ≫ p₂) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  let f : SecMod p₁ (LB.LinComb L φ₁ ε₁) →+ SecMod p₂ (LB.LinComb L φ₂ ε₂) →+ T.presheaf.stalk z :=
    (((AddMonoidHom.mul (R := T.presheaf.stalk z)).comp (svalHom p₁ φ₁ ε₁ r₁ z hJ)).flip.comp
      (svalHom p₂ φ₂ ε₂ r₂ z hJ)).flip
  have hf : ∀ s t, f s t = svalHom p₁ φ₁ ε₁ r₁ z hJ s * svalHom p₂ φ₂ ε₂ r₂ z hJ t := fun _ _ => rfl
  have hb : ∀ (c : F) s t, f (c • s) t = f s (c • t) := fun c s t => by
    rw [hf, hf, svalHom_smul, svalHom_smul, e]; ring
  have := congrArg (TensorProduct.liftAddHom f hb) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at this
  simp only [TensorProduct.liftAddHom_tmul] at this
  exact this

end GlobalTheory.AdditionTensor

namespace GlobalTheory

theorem addition_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  intro S P F _ p th n t t' hadd hth h0
  obtain ⟨κ, -, hκ⟩ := hadd
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hI : IsIntegral (Over.mk p ⊗ P.A).left := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  obtain ⟨z⟩ : Nonempty (Over.mk p ⊗ P.A).left := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB z (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim) (fun k => k.elim)
  have hne : ∃ j, th.sec.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hth (DVR.SecOps.sec_ext hc)
  have hv := sval_ne_zero_of_isIso P.A.left (Over.mk p ⊗ P.A).left P.L P.isLB (Fin 1)
    (fun _ => (snd (Over.mk p) P.A).left) (fun _ => ((1 : ℕ) : ℤ)) th.sec hne _ (𝟙 _) z J hJ
  have h1 := hκ (Over.mk p ⊗ P.A) (fst _ _) (snd _ _) 1 z J hJ
  have h2 := AdditionTensor.sum_sval_mul_eq_zero (fst (Over.mk p) P.A).left (fst (Over.mk p) P.A).left
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ))
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ)) t t' h0
    (lift (fst (Over.mk p) P.A) (snd (Over.mk p) P.A)).left (lift (fst (Over.mk p) P.A) (1 : Over.mk p ⊗ P.A ⟶ P.A)).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z hJ
  have h3 := h1.symm.trans h2
  rw [inv_one, _root_.mul_one, lift_fst_snd, Units.mul_right_eq_zero, mul_self_eq_zero] at h3
  exact hv h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIff
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isUnit_scal_comp_specMap {R F : Type} [CommRing R] [CommRing F] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (r : R) (h : IsUnit (φ r)) :
    IsUnit (scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r) := by
  have e : scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
    have := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    unfold scal
    rw [this]
    rfl
  rw [e]
  exact (h.map _).map _

theorem sval_eq_zero_of_forall_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_lift_pair {S : Scheme.{0}} (T₀ B : Over S) {T : Scheme.{0}} (r₁ r₂ : T ⟶ (T₀ ⊗ B).left)
    (h : r₁ ≫ (fst T₀ B).left = r₂ ≫ (fst T₀ B).left) :
    ∃ (q : T ⟶ S) (ρ : Over.mk q ⟶ T₀) (x y : Over.mk q ⟶ B), (lift ρ x).left = r₁ ∧ (lift ρ y).left = r₂ := by
  have w : r₂ ≫ (T₀ ⊗ B).hom = r₁ ≫ (T₀ ⊗ B).hom := by
    rw [← Over.w (fst T₀ B), ← Category.assoc, ← Category.assoc, h]
  let u₁ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₁ rfl
  let u₂ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₂ w
  have e : u₁ ≫ fst T₀ B = u₂ ≫ fst T₀ B := Over.OverMorphism.ext h
  refine ⟨_, u₁ ≫ fst T₀ B, u₁ ≫ snd T₀ B, u₂ ≫ snd T₀ B, ?_, ?_⟩
  · rw [lift_comp_fst_snd]; rfl
  · rw [e, lift_comp_fst_snd]; rfl

theorem addB_tensor_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA
  have := D.P.isAb.proper
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsProper (fst (TF (R := R) F) D.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (TF (R := R) F ⊗ D.P.A).left := isIntegral_tensor_left_of_smooth_grpObj _ _ _
  have key := fun α β : D.X => GlobalTheory.tensor_sections_eq_zero_iff F _ D.P.L D.P.isLB _ _ (fst (TF (R := R) F) D.P.A).left
    (fst (TF (R := R) F) D.P.A).left _ _ (DegPre.famφ D F α) (DegPre.famε 2) (DegPre.famφ D F β) (DegPre.famε 2) n
    (fun i => SecMod.mk _ (s i α)) (fun i => SecMod.mk _ (s' i β))
  refine ⟨fun a b => ⟨fun hne => ?_, fun ⟨ha, hb⟩ h0 => ?_⟩, fun α β hαβ => ?_⟩
  · by_contra hc
    refine hne ((key _ _).2 fun T r₁ r₂ h z J hJ => ?_)
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    refine ((hA (Over.mk q) ρ x y z J hJ).1 a b _ _ rfl rfl).trans ?_
    rcases not_and_or.1 hc with hc | hc
    · have := sval_eq_zero_of_forall_eq_zero (s₀ a) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y)).left z J
      exact (congrArg (_ * ·) ((congrArg (· * _) this).trans (zero_mul _))).trans (mul_zero _)
    · have := sval_eq_zero_of_forall_eq_zero (s₀ b) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y⁻¹)).left z J
      exact (congrArg (_ * ·) ((congrArg (_ * ·) this).trans (mul_zero _))).trans (mul_zero _)
  · let z := genericPoint (TF (R := R) F ⊗ D.P.A).left
    choose J hJ using fun χ : (TF (R := R) F ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have hG : Good D.P.L z J := hJ
    have h1 := (key _ _).1 h0 _ (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left
      (lift (fst (TF (R := R) F) D.P.A) (1 : _ ⟶ D.P.A)).left
      (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z J hG
    have h2 := ((hA (TF (R := R) F ⊗ D.P.A) (fst _ _) (snd _ _) 1 z J hG).1 a b _ _ rfl rfl).symm.trans h1
    rw [inv_one, _root_.mul_one, lift_fst_snd] at h2
    have hu : IsUnit (scal (TF (R := R) F ⊗ D.P.A).hom r) := by
      have e : (TF (R := R) F ⊗ D.P.A).hom = (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
        rw [← Over.w (fst (TF (R := R) F) D.P.A), CommRingCat.ofHom_comp, Spec.map_comp]; rfl
      rw [e]
      refine isUnit_scal_comp_specMap _ _ r (IsUnit.mk0 _ ?_)
      exact (map_ne_zero (algebraMap (FractionRing R) F)).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have hu' : IsUnit (gs (𝟙 _) z ⊤ (scal (TF (R := R) F ⊗ D.P.A).hom r)) := by
      rw [gs_eq _ z ⊤ trivial]
      exact (hu.map _).map _
    exact mul_ne_zero (mul_ne_zero hu'.ne_zero (Units.ne_zero _))
      (mul_ne_zero ((exists_ne_zero_iff_sval_ne_zero (s₀ a) hG).1 ha)
        ((exists_ne_zero_iff_sval_ne_zero (s₀ b) hG).1 hb)) h2
  · refine (key _ _).2 fun T r₁ r₂ h z J hJ => ?_
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    exact (hA (Over.mk q) ρ x y z J hJ).2 α β hαβ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BijectiveOfIso
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.GenericFibreSections

variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}

theorem exists_transfer (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (φ₁ : Y ⟶ X₁) (φ₂ : Y ⟶ X₂) (k : ℤ)
    (V : L₁.ι → L₂.ι → Y.Opens) (hV : ∀ i j y, φ₁ y ∈ L₁.U i → φ₂ y ∈ L₂.U j → y ∈ V i j)
    (u : ∀ i j, Γ(Y, V i j)ˣ)
    (hu : ∀ (y : Y) i i' j j', φ₁ y ∈ L₁.U i → φ₁ y ∈ L₁.U i' → φ₂ y ∈ L₂.U j → φ₂ y ∈ L₂.U j' →
      gm (𝟙 Y) y _ (u i j) * gm (𝟙 Y ≫ φ₁) y _ (L₁.g i i') ^ k =
        gm (𝟙 Y ≫ φ₂) y _ (L₂.g j j') ^ k * gm (𝟙 Y) y _ (u i' j'))
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ₁) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => φ₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval s' r z J₂ = (gm r z _ (u (J₁ (r ≫ φ₁)) (J₂ (r ≫ φ₂)))).val * sval s r z J₁ := by
  have glue : ∀ j : Fin 1 → L₂.ι, ∃ a : Γ(Y, LB.wchart L₂ (fun _ : Fin 1 => φ₂) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L₁.ι),
      r z ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j → φ₁ (r z) ∈ L₁.U i →
      gs r z _ a = (gm r z _ (u i (j 0))).val *
        gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) := by
    intro j
    let W : L₁.ι → Y.Opens := fun i =>
      LB.wchart L₂ (fun _ : Fin 1 => φ₂) j ⊓ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)
    have l : ∀ i, W i ≤ V i (j 0) := fun i y hy =>
      hV i (j 0) y (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.1 0)
    obtain ⟨b, hb⟩ : ∃ b : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (b i) = (gm r z _ (u i (j 0))).val *
          gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (l i)).op).hom (u i (j 0)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i))).op).hom
            (s.f (fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (l i hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, Set.mem_iInter.2 fun _ => hi⟩) b
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have m : φ₂ y ∈ L₂.U (j 0) := Set.mem_iInter.1 hy.1.1 0
        have e := hu y i i' (j 0) (j 0) (Set.mem_iInter.1 hy.1.2 0) (Set.mem_iInter.1 hy.2.2 0) m m
        rw [gm_self hL₂ (𝟙 Y ≫ φ₂) y m, _root_.one_zpow, _root_.one_mul] at e
        rw [hb _ _ y i hy.1, hb _ _ y i' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          ← e, trF, Fintype.prod_unique])
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₁, Set.mem_iInter.2 fun _ => h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W i)) (ha i)).trans (hb Z r z i hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L₂ _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y i hy.2 hi)).symm)
    have e := hu y i i (j 0) (j' 0) hi hi (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0)
    rw [gm_self hL₁ (𝟙 Y ≫ φ₁) y hi, _root_.one_zpow, _root_.mul_one] at e
    rw [e, Fintype.prod_unique, Units.val_mul, _root_.mul_assoc]
    rfl
  · exact ha _ Z r z (J₁ (r ≫ φ₁)) (hJ₂.mem (fun _ : Fin 1 => φ₂) r) (hJ₁ (r ≫ φ₁))

theorem exists_pull (h : Y' ⟶ Y) (φ : Y ⟶ X₁) (φ' : Y' ⟶ X₁) (e : φ' = h ≫ φ) (k : ℤ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ') (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L₁ z J → sval s' r z J = sval s (r ≫ h) z J := by
  subst e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem sec_ext {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := funext h
  rfl

theorem gw_trans {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (y : Y)
    {i i' : L₁.ι} {j j' : L₂.ι} (hi : f₁ y ∈ L₁.U i) (hi' : f₁ y ∈ L₁.U i') (hj : f₂ y ∈ L₂.U j) (hj' : f₂ y ∈ L₂.U j') :
    gw w (𝟙 Y) y j (fun _ => i) * gm (𝟙 Y ≫ f₁) y _ (L₁.g i i') =
      gm (𝟙 Y ≫ f₂) y _ (L₂.g j j') * gw w (𝟙 Y) y j' (fun _ => i') := by
  have e := (isGen_iff w).1 hw Y (𝟙 Y) y j j' (fun _ => i) (fun _ => i') hj hj' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ f₁ (𝟙 Y) y _ _ (mem_pull.2 hi) (mem_pull.2 hi')] at e
  rw [e, _root_.mul_right_comm, inv_mul_cancel_right]

theorem bijective_of_iso (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (p : Y' ⟶ X₁) [IsIso f₁] [IsIso p]
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (Rel : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))) →
      LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))) → Prop)
    (hRel : ∀ σ t, Rel σ t ↔ ∀ (Z : Scheme.{0}) (rA : Z ⟶ Y') (y : Z ⟶ Y), rA ≫ p = y ≫ f₁ → ∀ (z : Z) J₁ J₂,
      Good L₁ z J₁ → Good L₂ z J₂ →
      (gw w y z (J₂ (y ≫ f₂)) (fun _ => J₁ (y ≫ f₁))).val ^ k * sval t rA z J₁ = sval σ y z J₂) :
    (∀ σ, ∃! t, Rel σ t) ∧ ∀ t, ∃! σ, Rel σ t := by
  have hV : ∀ i j (y : Y), f₁ y ∈ L₁.U i → f₂ y ∈ L₂.U j →
      y ∈ (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i) := fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩
  refine ⟨fun σ => ?_, fun t => ?_⟩
  · obtain ⟨s, hs⟩ := exists_transfer hL₂ hL₁ f₂ f₁ k
      (fun j i => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) (fun j i y hj hi => hV i j y hi hj)
      (fun j i => ((show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k)⁻¹) (fun y j j' i i' hj hj' hi hi' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_inv, map_inv, map_pow, map_pow, zpow_natCast, zpow_natCast]
        change (gw w (𝟙 Y) y j (fun _ => i) ^ k)⁻¹ * _ = _ * (gw w (𝟙 Y) y j' (fun _ => i') ^ k)⁻¹
        rw [inv_mul_eq_iff_eq_mul, ← _root_.mul_assoc, ← mul_pow, e, mul_pow, mul_inv_cancel_right]) σ
    obtain ⟨t, ht⟩ := exists_pull (p ≫ inv f₁) f₁ p (by simp) k s
    refine ⟨t, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun t' H' => ?_⟩
    · have e' : rA ≫ p ≫ inv f₁ = y := by rw [← Category.assoc, e]; simp
      rw [ht Z rA z J₁ h₁, e', hs Z y z J₂ J₁ h₂ h₁, map_inv, map_pow, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv_cancel_left _ _
    · refine sec_ext (sec_ext_val hL₁ fun y J₁ h₁ => ?_)
      choose J₂ h₂ using fun χ : Y' ⟶ X₂ => exists_chart hL₂ (χ y)
      have e := (hRel _ _).1 H' Y' (𝟙 _) (p ≫ inv f₁) (by simp) y J₁ J₂ h₁ h₂
      rw [ht _ _ y J₁ h₁, Category.id_comp, hs _ _ y J₂ J₁ h₂ h₁, map_inv, map_pow, ← e, ← Units.val_pow_eq_pow_val]
      exact (Units.inv_mul_cancel_left _ _).symm
  · obtain ⟨s, hs⟩ := exists_pull (f₁ ≫ inv p) p f₁ (by simp) k t
    obtain ⟨σ, hσ⟩ := exists_transfer hL₁ hL₂ f₁ f₂ k
      (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) hV
      (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
        exact congrArg (· ^ k) e) s
    refine ⟨σ, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun σ' H' => ?_⟩
    · have e' : y ≫ f₁ ≫ inv p = rA := by rw [← Category.assoc, ← e]; simp
      rw [hσ Z y z J₁ J₂ h₁ h₂, hs Z y z J₁ h₁, e', map_pow, Units.val_pow_eq_pow_val]
      rfl
    · refine sec_ext (sec_ext_val hL₂ fun y J₂ h₂ => ?_)
      choose J₁ h₁ using fun χ : Y ⟶ X₁ => exists_chart hL₁ (χ y)
      have e := (hRel _ _).1 H' Y (𝟙 Y ≫ f₁ ≫ inv p) (𝟙 _) (by simp) y J₁ J₂ h₁ h₂
      rw [← e, hσ _ _ y J₁ J₂ h₁ h₂, hs _ _ y J₁ h₁, map_pow, Units.val_pow_eq_pow_val]
      rfl

theorem sameK_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ), (∀ σ, ∃! t, U.SameK (k := k) σ t) ∧ ∀ t, ∃! σ, U.SameK (k := k) σ t := by
  intro R _ _ I D A G _ _ U k
  have h₀ : IsIso (TFK (R := R) (FractionRing R)).hom := by
    show IsIso (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have h₁ : IsIso (snd (TFK (R := R) (FractionRing R)) A.A).left :=
    inferInstanceAs (IsIso (pullback.snd (TFK (R := R) (FractionRing R)).hom A.A.hom))
  have h₂ : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact bijective_of_iso A.isLB U.P.L.isLB U.gen.hom.left (pullback.fst G.hom (jK R))
    (snd (TFK (R := R) (FractionRing R)) A.A).left U.wA U.wA_gen k (fun σ t => U.SameK (k := k) σ t)
    (fun _ _ => Iff.rfl)

end GlobalTheory.GenericFibreSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevelStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_polarisations_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') := by
  first | exact @GlobalTheory.polarisations_agree_at_level | exact GlobalTheory.polarisations_agree_at_level | (intros; apply GlobalTheory.polarisations_agree_at_level <;> assumption)
end

