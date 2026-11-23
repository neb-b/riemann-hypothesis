module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DlogPol

section Germs
variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {O₀ O : Y.Opens} (h : O ≤ O₀) (hz : r z ∈ O) (s : Γ(Y, O₀)) :
    gs r z O (rsT s O) = gs r z O₀ s := by
  rw [rsT, dif_pos h]
  exact gs_res r z h hz s

theorem gs_pbT (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {O₀ : X.Opens} {O : Y.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (hz : r z ∈ O)
    (s : Γ(X, O₀)) : gs r z O (pbT f s O) = gs (r ≫ f) z O₀ s := by
  rw [pbT, dif_pos h]
  exact (gs_res r z h hz ((f.app O₀).hom s)).trans (gs_pull r f z O₀ (h hz) s)

theorem gs_one (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) : gs r z O 1 = 1 := by
  simp only [gs_eq r z O hz, map_one]

theorem gs_sub (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a b : Γ(Y, O)) :
    gs r z O (a - b) = gs r z O a - gs r z O b := by
  simp only [gs_eq r z O hz, map_sub]

theorem gs_constFn {R : Type} [CommRing R] (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a : R) :
    gs r z O (constFn p O a) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) hz ((p.app ⊤).hom _)).trans (gs_pull r p z ⊤ trivial _)

theorem eps_sq {K : Type} [Field K] (p : X ⟶ Sp (DualNumber K)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

end Germs

theorem exists_gen {K : Type} [Field K] {X Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber K)) (τ ρ : Y' ⟶ Y)
    (hτ : ∀ (y : Y') (W : Y.Opens), τ y ∈ W → ρ y ∈ W) (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (k : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hk : ∀ i j (y : Y'), m (τ y) ∈ L.U i → m (τ y) ∈ L.U j →
      gs (τ ≫ m) y _ (L.g i j).val = gs (ρ ≫ m) y _ (L.g i j).val *
        (1 + gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) *
          gs ρ y _ (k i j)))
    (hc : IsCob _ k) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) (fun n => ![τ, ρ] n ≫ m) ![1, -1]), t.IsGen := by
  obtain ⟨b, hb⟩ := hc
  let φ : Fin 2 → (Y' ⟶ X) := fun n => ![τ, ρ] n ≫ m
  have h₀ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (τ y) ∈ L.U (J 0) := fun J y hy =>
    Set.mem_iInter.1 hy 0
  have h₀' : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 0) := fun J y hy =>
    hτ y (m ⁻¹ᵁ L.U (J 0)) (h₀ J y hy)
  have h₁ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 1) := fun J y hy =>
    Set.mem_iInter.1 hy 1
  have le : ∀ J : Fin 2 → L.ι, LB.wchart L φ J ≤ (ρ ≫ m) ⁻¹ᵁ (L.U (J 0) ⊓ L.U (J 1)) := fun J y hy =>
    ⟨h₀' J y hy, h₁ J y hy⟩
  let u : ∀ J : Fin 2 → L.ι, Γ(Y', LB.wchart L φ J)ˣ := fun J =>
    ⟨1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _, 1 + constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _,
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J),
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J)⟩
  refine ⟨⟨fun J => res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J⟩, isGen_of_gm _ fun y J J' hJ hJ' => ?_⟩
  set e := gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) with he
  have ee : e * e = 0 := by
    rw [he, ← gs_mul π y ⊤ trivial, ← map_mul, DualNumber.eps_mul_eps, map_zero, gs_eq π y ⊤ trivial, map_zero, map_zero]
  have val : ∀ J : Fin 2 → L.ι, y ∈ LB.wchart L φ J →
      (gm (𝟙 Y') y (LB.wchart L φ J) (res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J)).val =
        (gm (ρ ≫ m) y _ (L.g (J 0) (J 1))).val * (1 - e * gs ρ y _ (b (J 0))) := fun J hJ => by
    rw [map_mul, Units.val_mul, gm_res (𝟙 Y') y (le J) hJ, gm_pull (𝟙 Y') (ρ ≫ m) y _ (le J hJ), Category.id_comp,
      ← gs_unit (𝟙 Y') y _ hJ]
    congr 1
    change gs (𝟙 Y') y _ (1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _) = _
    rw [gs_sub _ _ _ hJ, gs_one _ _ _ hJ, gs_mul _ _ _ hJ, gs_constFn _ _ _ _ hJ,
      gs_pbT (𝟙 Y') ρ y (O₀ := m ⁻¹ᵁ L.U (J 0)) (fun y hy => h₀' J y hy) hJ, Category.id_comp, Category.id_comp]
  have tr : trF φ ![1, -1] (𝟙 Y') y J J' =
      gm (τ ≫ m) y _ (L.g (J 0) (J' 0)) * (gm (ρ ≫ m) y _ (L.g (J 1) (J' 1)))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    simp only [Category.id_comp]
    simp [φ]
  have c₁ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₀' J' y hJ') (h₁ J' y hJ')
  have c₂ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₁ J y hJ) (h₁ J' y hJ')
  have k₁ := hk _ _ y (h₀ J y hJ) (h₀ J' y hJ')
  have m₀ : ρ y ∈ m ⁻¹ᵁ L.U (J 0) ⊓ m ⁻¹ᵁ L.U (J' 0) := ⟨h₀' J y hJ, h₀' J' y hJ'⟩
  rw [hb, gs_sub _ _ _ m₀, gs_rsT _ _ inf_le_right m₀, gs_rsT _ _ inf_le_left m₀,
    gs_unit (τ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) ⟨h₀ J y hJ, h₀ J' y hJ'⟩, gs_unit (ρ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) m₀, ← he] at k₁
  change gm (𝟙 Y') y (LB.wchart L φ J) _ = trF φ ![1, -1] (𝟙 Y') y J J' * gm (𝟙 Y') y (LB.wchart L φ J') _
  rw [tr, _root_.mul_assoc, mul_left_comm, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val J hJ, val J' hJ', k₁]
  have d := congrArg Units.val (c₁.trans c₂.symm)
  rw [Units.val_mul, Units.val_mul] at d
  linear_combination (-(1 - e * gs ρ y _ (b (J 0)))) * d +
    ((gm (ρ ≫ m) y _ (L.g (J 0) (J' 0))).val * (gm (ρ ≫ m) y _ (L.g (J' 0) (J' 1))).val *
      (gs ρ y _ (b (J' 0)) - gs ρ y _ (b (J 0))) * gs ρ y _ (b (J' 0))) * ee

theorem isUnit_pbT {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (i j : L.ι) :
    IsUnit (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) := by
  rw [pbT, dif_pos (show m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j) from fun _ h => h)]
  exact (L.g i j).isUnit.map _

theorem isCoc_dlog {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (d : ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (hmul : ∀ W f f', d W (f * f') = f * d W f' + f' * d W f)
    (hres : ∀ W W' (f : Γ(Y, W)), W' ≤ W → d W' (rsT f W') = rsT (d W f) W')
    (φ : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hφ : ∀ i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ i j =
      d _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))) : IsCoc _ φ := by
  intro i j k
  set O : Y.Opens := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k with hO
  let G : L.ι → L.ι → Γ(Y, O) := fun a b => rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) O
  have hd : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → d O (G a b) = G a b * rsT (φ a b) O := fun a b h => by
    rw [hres _ _ _ h, ← hφ]
    simp only [G, rsT, dif_pos h, map_mul]
  have hg : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → ∀ y ∈ O,
      gs (𝟙 Y) y O (G a b) = (gm m y _ (L.g a b)).val := fun a b h y hy => by
    rw [gs_rsT _ _ h hy, gs_pbT (𝟙 Y) m y (O₀ := L.U a ⊓ L.U b) (O := m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) (fun _ h => h) (h hy), Category.id_comp,
      gs_unit m y (L.U a ⊓ L.U b) (h hy)]
  have l₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j := inf_le_left
  have l₂ : O ≤ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.2, h.2⟩
  have l₃ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.1, h.2⟩
  have co : G i j * G j k = G i k := fn_ext fun y hy => by
    rw [gs_mul _ _ _ hy, hg _ _ l₁ y hy, hg _ _ l₂ y hy, hg _ _ l₃ y hy, ← Units.val_mul,
      gm_cocycle hL m y hy.1.1 hy.1.2 hy.2]
  have un : IsUnit (G i k) := by
    simp only [G, rsT, dif_pos l₃]
    exact (isUnit_pbT m L i k).map _
  have e := hmul O (G i j) (G j k)
  rw [co, hd _ _ l₁, hd _ _ l₂, hd _ _ l₃] at e
  refine un.mul_left_cancel ?_
  change G i k * (rsT (φ i j) O + rsT (φ j k) O) = G i k * rsT (φ i k) O
  linear_combination (-1 : Γ(Y, O)) * e - (rsT (φ i j) O + rsT (φ j k) O) * co

theorem preimage_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (w : epsR K ⟶ A) (hw : IsTangent w)
    (W : A.left.Opens) :
    ((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  let z : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hz : z ≫ w = η[A] := Over.OverMorphism.ext hw
  let j : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ z) (𝟙 A)
  have j₁ : j ≫ snd (epsR K) A = 𝟙 A := lift_snd _ _
  have j₂ : j ≫ ((fst (epsR K) A ≫ w) * snd (epsR K) A) = 𝟙 A := by
    rw [MonObj.comp_mul, j₁, lift_fst_assoc, Category.assoc, hz, ← Hom.one_def, _root_.one_mul]
  have j₃ : j.left ≫ (fst (epsR K) A).left = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    have := congrArg (fun q => q.left) (lift_fst (toUnit A ≫ z) (𝟙 A))
    refine this.trans ?_
    change (toUnit A).left ≫ _ = _
    congr 1
  have h := (GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left j.left
    (IsPullback.of_hasPullback (epsR K).hom A.hom).flip (congrArg (fun q => q.left) j₁) j₃).1
    (((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W)
  rw [← h, ← Scheme.Hom.comp_preimage j.left, ← Over.comp_left, j₂]
  rfl

theorem dlog_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  intro K _ P g v dd hv hdd X m L hL ⟨u, hu⟩
  refine ⟨⟨fun a i j => ((isUnit_pbT m L i j).unit⁻¹ : _ˣ).val * dd a _ (pbT m (L.g i j).val _), fun a i j => ?_⟩,
    fun φ hφ => ⟨fun a => ?_, fun c hc => ?_⟩⟩
  · rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
  · obtain ⟨-, h₁, h₂, -⟩ := (GlobalTheory.KS.InvField.main K P.A (v a) (hv.1 a)).2 _ (hdd a)
    exact isCoc_dlog m L hL (dd a) h₁ h₂ (φ a) (hφ a)
  have := P.isAb.comm
  obtain ⟨a₁, a₂, a₃, -⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A g v hv.1
  obtain ⟨w, hw, -⟩ := a₁ c
  have tw := a₂ c w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.KS.InvField.main K P.A w tw).1
  have hsum : ∀ (W : P.A.left.Opens) (h : Γ(P.A.left, W)), dw W h = ∑ a, constFn P.A.hom _ (c a) * dd a W h :=
    GlobalTheory.KS.InvHom.invDer_along_hom K P.A P.A (𝟙 _) g v dd w dw c inferInstance hv.1 tw hdd hdw (by rwa [Category.comp_id])
  have pre := preimage_transl w tw
  set τ := ((fst (epsR K) P.A ≫ w) * snd (epsR K) P.A).left with hτ
  set ρ := (snd (epsR K) P.A).left with hρ
  obtain ⟨t, ht⟩ := exists_gen (fst (epsR K) P.A).left τ ρ (fun y W hy => (pre W).le hy) m L hL _ (fun i j y hi hj => by
    have hy : y ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := (pre _).le ⟨hi, hj⟩
    have e := congrArg (gs (𝟙 _) y _) (hdw (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (pbT m (L.g i j).val _))
    have e₂ : dw _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) =
        pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * lc P.A.hom c φ i j := by
      rw [hsum, lc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [← hφ a i j, mul_left_comm]
    rw [e₂, gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy, gs_pbT _ _ _ (pre _).ge hy,
      gs_pbT _ _ _ le_rfl hy, gs_pbT _ _ _ le_rfl hy, Category.id_comp, Category.id_comp, Category.id_comp,
      gs_mul _ _ _ hy, gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) ⟨hi, hj⟩,
      gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) hy] at e
    refine e.trans ?_
    ring) hc
  obtain ⟨s, hs⟩ := exists_down ((isGen_iff u).1 hu) hL P.isLB t ht
  have w1 : w = 1 := P.ktriv (DualNumber K) _ w fun p =>
    ⟨⊤, trivial, gen_chartPull (chartPullPull (Out.translDiff P.A P.L w) _ _ rfl) s hs⟩
  have h0 : IsLieComb 0 v w := by
    have := a₃ 0 Fin.elim0 Fin.elim0 Fin.elim0 w (fun i => i.elim0) ⟨Fin.elim0, fun i => i.elim0, by rw [w1]; rfl⟩
    simpa using this
  exact (hv.2 w tw).unique hw h0

end GlobalTheory.KS.DlogPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolDescent

theorem exists_gen_of_unique {Y : Scheme.{0}} [Subsingleton Y] (y₀ : Y) {M : LB Y} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  obtain ⟨i₀, hi₀⟩ := exists_chart hM y₀
  have h : ∀ y, y ∈ M.U i₀ := fun y => by rwa [Subsingleton.elim y y₀]
  have le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg _ ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _))).trans ?_
  exact gm_cocycle hM _ y hy.1 hy.2 (h y)

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem kTriv_of_pullback [Flat f] [Surjective f] [IsAffineHom f] (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let R' : Type := Γ(pullback t f, ⊤)
  let e : Spec (CommRingCat.of R') ⟶ pullback t f := (pullback t f).isoSpec.inv
  have : IsIso e := inferInstanceAs (IsIso (pullback t f).isoSpec.inv)
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  obtain ⟨q, t', hq, sq⟩ : ∃ (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
      (t' : Spec (CommRingCat.of R') ⟶ S'), Epi q ∧ q ≫ t = t' ≫ f :=
    ⟨e ≫ pullback.fst t f, e ≫ pullback.snd t f, inferInstance, by
      rw [Category.assoc, Category.assoc, pullback.condition]⟩
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have sx : (q ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sx) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = q ≫ x.left := h.1.lift_fst _ _ _
  have main : x' = toUnit _ ≫ η[A'] := by
    refine hK R' t' x' fun p => ?_
    obtain ⟨V, hV, c, hc⟩ := hx (q p)
    refine ⟨q ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ q)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ q :=
      congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (snd T' A').left ≫ φ = (lift a b).left ≫ (snd T A).left :=
      (congrArg (fun q => q.left) (lift_snd a b)).symm
    have k₃ : ((fst T' A' ≫ x') * snd T' A').left ≫ φ = (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left := by
      have e₀ : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₁ := h.2 (T' ⊗ A') (fst T' A' ≫ x') (snd T' A') (a ≫ x) b
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)) rfl
      rw [← e₀] at e₁
      exact e₁.symm
    obtain ⟨n, hn⟩ : ∃ n : ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
        n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left :=
      ⟨IsOpenImmersion.lift _ (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    let ψ : Fin 2 → (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ A'.left) := fun k =>
      ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
        ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k => ψ k ≫ φ) _ _ n fun k => by
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
      fin_cases k
      exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ ψ fun _ => rfl) c₃ h₃
  let a : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk q sq
  have e₁ : pushPt h.1.w x' = 1 := (congrArg _ main).trans (map_one (pushHom h T'))
  have e₂ : a ≫ x = a ≫ (1 : T ⟶ A) :=
    (Over.OverMorphism.ext hx'.symm : a ≫ x = pushPt h.1.w x').trans (e₁.trans (MonObj.comp_one a).symm)
  exact Over.OverMorphism.ext ((cancel_epi q).1 (congrArg (fun z => z.left) e₂))

theorem sym_of_pullback [Subsingleton S'] (s' : S') (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (desc : ∀ M : LB A.left, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (hS : Out.Sym A' L') : Out.Sym A L := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨U, hU, c, hc⟩ := hS s'
  obtain ⟨e, he⟩ : ∃ e : A'.left ⟶ (A'.hom ⁻¹ᵁ U).toScheme, e ≫ (A'.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show A'.hom y ∈ U
      rwa [Subsingleton.elim (A'.hom y) s']), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![(GrpObj.inv : A' ⟶ A').left, 𝟙 _] _ _ e fun k => by
    fin_cases k
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he).trans (Category.id_comp _))).symm
    · exact he.symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  obtain ⟨c₃, h₃⟩ := desc _ (DVR.linComb_isLB L hL ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1])
    (gen_chartPull (chartPullOut L _ _ φ _ fun k => by
      fin_cases k
      · exact inv_left_comp h
      · exact (Category.id_comp φ).trans (Category.comp_id φ).symm) c₂ h₂)
  intro s
  refine ⟨⊤, trivial, gen_chartPull (chartPullSame L _ _ _ (A.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c₃ h₃⟩
  fin_cases k
  · rfl
  · exact (Category.comp_id _).symm

theorem rigidified_sym_kTriv_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hA h hL₀ hL hw
  refine ⟨fun _ => ?_, fun hS => ?_, fun hK => ?_⟩
  · have : Subsingleton (𝟙_ (Over (Sp K₀))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
    exact exists_gen_of_unique (default : PrimeSpectrum K₀) (pull_isLB hL₀ _)
  · have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact sym_of_pullback (default : PrimeSpectrum K) h hL₀ hL hw
      (_root_.GlobalTheory.lb_gen_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).1 hS
  · have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    exact kTriv_of_pullback h hL₀ hL hw hK

end GlobalTheory.PolDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.CoordMove
open GlobalTheory.ZM.RepBC

theorem isUnit_cst_id {R : Type} [CommRing R] (p : Sp R) (a : R) : IsUnit (cst (𝟙 (Sp R)) p a) ↔ a ∉ p.asIdeal := by
  rw [cst, gs_eq _ _ ⊤ trivial]
  refine ((Sp R).mem_basicOpen (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) p trivial).symm.trans ?_
  have := basicOpen_eq_of_affine (R := CommRingCat.of R) a
  exact (congrArg (fun U : (Sp R).Opens => p ∈ U) this).to_iff

theorem secCoord_iff {X : Scheme.{0}} (M : LB X) {I : Type} (th : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : I → R) : SecCoord M th x v ↔ ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (p : Sp R),
      p ∈ (M.pull x).U j → gs x p _ ((th i).f (j PUnit.unit)) =
        cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := by
  refine exists_congr fun τ => and_congr_right fun _ => forall₂_congr fun i j => ?_
  have l : ∀ (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)) (p : Sp R), p ∈ (M.pull x).U j →
      gs (𝟙 (Sp R)) p ((M.pull x).U j) ((x.appLE _ _ h).hom ((th i).f (j PUnit.unit))) =
        gs x p _ ((th i).f (j PUnit.unit)) := fun h p hp =>
    (gs_appLE x _ _ h (𝟙 _) p hp _).trans (by rw [Category.id_comp])
  have r : ∀ (p : Sp R), p ∈ (M.pull x).U j → gs (𝟙 (Sp R)) p ((M.pull x).U j)
      (resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) *
        (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)) =
      cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := fun p hp =>
    (gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ p le_top hp _) (gs_unit _ p _ hp _))
  exact ⟨fun h p hp => (l (pull_le M x j) p hp).symm.trans ((congrArg _ (h _)).trans (r p hp)),
    fun h e => fn_ext fun p hp => (l e p hp).trans ((h p hp).trans (r p hp).symm)⟩

theorem secCoord_down {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (H : LBIso L' (L.pull F)) {I : Type} (th : I → L.Sec) :
    ∃ th' : I → L'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R),
      SecCoord L' th' x v ↔ SecCoord L th (x ≫ F) v := by
  obtain ⟨w, hw⟩ := H
  have hw' := (isGen_iff w).1 hw
  choose th' h' using fun i => sec_pull_down hw' hL hL' (th i)
  refine ⟨th', fun R _ x v => ?_⟩
  have e : ∀ (p : Sp R) (j : PUnit → L.ι) (k : PUnit → L'.ι),
      pw w (fun _ : PUnit => x) (fun _ => 1) (𝟙 _) p j k = gw w x p (j PUnit.unit) (k PUnit.unit) := fun p j k => by
    rw [pw, Fintype.prod_unique, zpow_one, Category.id_comp]
  rw [secCoord_iff, secCoord_iff]
  constructor
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := exists_up hw' hL hL' τ hτ
    refine ⟨t, ht, fun i j p hp => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hL' (x p)
    have hk' : p ∈ (L'.pull x).U (fun _ => k) := mem_pull.2 hk
    have h₁ := h' i _ x p (j PUnit.unit) k (mem_pull₂.1 hp) hk
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p j (fun _ => k) hp hk')
    rw [e, Units.val_mul] at h₂
    refine h₁.trans ((congrArg (_ * ·) (h i (fun _ => k) p hk')).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₂.symm)
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := CubTransport.exists_down_units hw' hL hL' (φ' := fun _ : PUnit => x) τ hτ
    refine ⟨t, ht, fun i k p hp => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart hL (F (x p))
    have hj' : p ∈ (L.pull (x ≫ F)).U (fun _ => j) := mem_pull₂.2 hj
    have h₁ := h' i _ x p j (k PUnit.unit) hj (mem_pull.1 hp)
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p (fun _ => j) k hj' hp)
    rw [e, Units.val_mul] at h₂
    refine (Units.mul_right_inj (gw w x p j (k PUnit.unit))).1 (h₁.symm.trans ((h i (fun _ => j) p hj').trans ?_))
    exact (congrArg (_ * ·) h₂).trans (mul_left_comm _ _ _)

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ X} {v : I → R} (i : I) (p : Sp R) (h : SecCoord M th x v) :
    x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal := by
  obtain ⟨τ, -, h⟩ := (secCoord_iff M th x v).1 h
  have key : ∀ k, x p ∈ M.U k → (IsUnit (gs (𝟙 X) (x p) _ ((th i).f k)) ↔ v i ∉ p.asIdeal) := fun k hk => by
    have e := h i (fun _ => k) p (mem_pull.2 hk)
    rw [gs_stalkMap x p _ hk] at e
    rw [← isUnit_cst_id, ← isUnit_map_iff (x.stalkMap p).hom]
    exact (congrArg IsUnit e).to_iff.trans (Units.isUnit_mul_units _ _)
  rw [mem_nonzeroLocus]
  refine ⟨fun ⟨k, hk, u⟩ => (key k hk).1 u, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  exact ⟨k, hk, (key k hk).2 u⟩

theorem secCoord_pull_iso_locus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  intro X M I th hM
  refine ⟨fun X' π => ⟨fun i => secPull M π (th i), fun R _ x v => secCoord_pull M th π x v⟩, fun M' hM' H => ?_,
    fun R _ x v i p h => mem_nonzeroLocus_iff hM i p h⟩
  obtain ⟨th', h⟩ := secCoord_down hM hM'
    (LBIso.chartPull (chartPullId M') (chartPullPull M (𝟙 X) (𝟙 X) rfl) (LBIso.symm H)) th
  refine ⟨th', fun R _ x v => ?_⟩
  have := h R x v
  rwa [Category.comp_id] at this

end GlobalTheory.ZM.CoordMove
end
end

