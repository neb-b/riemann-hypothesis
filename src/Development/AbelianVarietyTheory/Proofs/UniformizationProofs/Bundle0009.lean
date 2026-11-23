module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourthSide
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FourthSide

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j')) ((L.pull F).g (fun _ => j) (fun _ => j')) =
      gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}

def germ (pG' : Ge' ⟶ B') (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι)
    (jL' : L'.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw w (r ≫ pG') z jM jM')⁻¹ * (gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL')

theorem germ_change (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : Φ (pG' (r z)) ∈ M.U jM) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : Ψ (fG' (r z)) ∈ L.U jL)
    (a₄ : fG' (r z) ∈ L'.U jL') (b₁ : Φ (pG' (r z)) ∈ M.U kM) (b₂ : pG' (r z) ∈ M'.U kM')
    (b₃ : Ψ (fG' (r z)) ∈ L.U kL) (b₄ : fG' (r z) ∈ L'.U kL') :
    germ pG' fG' h w wL we r z jM jM' jL jL' =
      gm (r ≫ pG') z _ (M'.g jM' kM') * (gm (r ≫ fG') z _ (L'.g jL' kL'))⁻¹ *
        germ pG' fG' h w wL we r z kM kM' kL kL' := by
  have p₁ : pG (h (r z)) = Φ (pG' (r z)) := congrArg (fun g => g (r z)) e₁.symm
  have p₂ : fG (h (r z)) = Ψ (fG' (r z)) := congrArg (fun g => g (r z)) e₂
  have c₃ : fG (h (r z)) ∈ L.U jL := p₂ ▸ a₃
  have d₃ : fG (h (r z)) ∈ L.U kL := p₂ ▸ b₃
  have c₁ : pG (h (r z)) ∈ M.U jM := p₁ ▸ a₁
  have d₁ : pG (h (r z)) ∈ M.U kM := p₁ ▸ b₁
  have a := hw Z (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have b := hwL Z (r ≫ fG') z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hwe Z (r ≫ h) z jM kM (fun _ => jL) (fun _ => kL) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
  rw [gm_pull_g L fG (r ≫ h) z jL kL c₃ d₃, Category.assoc, Category.assoc, ← e₁, e₂] at c
  rw [Category.assoc] at a b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ pG' ≫ Φ) z _ (M.g jM kM) = A
  generalize gm (r ≫ fG' ≫ Ψ) z _ (L.g jL kL) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ fG') z _ (L'.g jL' kL') = C'
  generalize gw w (r ≫ pG') z kM kM' = P
  generalize gw wL (r ≫ fG') z kL kL' = Q
  generalize gw we (r ≫ h) z kM (fun _ => kL) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    (jM' : M'.ι) (jL' : L'.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jL : L.ι), Φ (pG' (r z)) ∈ M.U jM →
        pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gm r z _ s = germ pG' fG' h w wL we r z jM jM' jL jL' := by
  have p₁ : ∀ x, pG (h x) = Φ (pG' x) := fun x => congrArg (fun g => g x) e₁.symm
  have p₂ : ∀ x, fG (h x) = Ψ (fG' x) := fun x => congrArg (fun g => g x) e₂
  obtain ⟨W, hW⟩ : ∃ W : M.ι × L.ι → Ge'.Opens, ∀ i x, x ∈ W i ↔
      Φ (pG' x) ∈ M.U i.1 ∧ pG' x ∈ M'.U jM' ∧ Ψ (fG' x) ∈ L.U i.2 ∧ fG' x ∈ L'.U jL' :=
    ⟨fun i => pG' ⁻¹ᵁ (Φ ⁻¹ᵁ M.U i.1) ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ (fG' ⁻¹ᵁ (Ψ ⁻¹ᵁ L.U i.2) ⊓ fG' ⁻¹ᵁ L'.U jL')),
      fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  have l₁ : ∀ i, W i ≤ pG' ⁻¹ᵁ ((M.pull Φ).U (fun _ => i.1) ⊓ M'.U jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
  have l₂ : ∀ i, W i ≤ h ⁻¹ᵁ ((M.pull pG).U (fun _ => i.1) ⊓ (L.pull fG).U (fun _ => i.2)) := fun i x hx =>
    ⟨mem_pull.2 ((p₁ x).symm ▸ ((hW i x).1 hx).1), mem_pull.2 ((p₂ x).symm ▸ ((hW i x).1 hx).2.2.1)⟩
  have l₃ : ∀ i, W i ≤ fG' ⁻¹ᵁ ((L.pull Ψ).U (fun _ => i.2) ⊓ L'.U jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Ge', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (i : M.ι × L.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ pG' fG' h w wL we r z i.1 jM' i.2 jL' :=
    ⟨fun i => (res (l₁ i) (pullU pG' _ (w.s (fun _ => i.1, jM'))))⁻¹ *
        (res (l₂ i) (pullU h _ (we.s (fun _ => i.1, fun _ => i.2))) *
          res (l₃ i) (pullU fG' _ (wL.s (fun _ => i.2, jL')))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ i) hz _).trans (gm_pull r pG' z _ (l₁ i hz) _)))) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r h z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r fG' z _ (l₃ i hz) _)))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' x))
      obtain ⟨j, hj⟩ := exists_chart hL (Ψ (fG' x))
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨hi, mem_pull.1 hx.1, hj, mem_pull.1 hx.2⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwL hwe (𝟙 Ge') x i.1 i'.1 jM' jM' i.2 i'.2 jL' jL' h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, gm_self hL' (𝟙 Ge' ≫ fG') x h₁.2.2.2, inv_one, one_mul, one_mul] at k
      exact (hu _ (𝟙 Ge') x i hx.1).trans (k.trans (hu _ (𝟙 Ge') x i' hx.2).symm))
  refine ⟨s, fun Z r z jM jL a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jM, jL) (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jM, jL)) hz s).symm.trans
    ((congrArg (gm r z (W (jM, jL))) (hs (jM, jL))).trans (hu Z r z (jM, jL) hz))

theorem exists_fourth_side (B B' G G' Ge Ge' : Scheme.{0}) (M : LB B) (M' : LB B') (L : LB G) (L' : LB G')
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) (Φ : B' ⟶ B) (Ψ : G' ⟶ G) (pG : Ge ⟶ B)
    (pG' : Ge' ⟶ B') (fG : Ge ⟶ G) (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (e₁ : pG' ≫ Φ = h ≫ pG)
    (e₂ : h ≫ fG = fG' ≫ Ψ) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen) (hwL : wL.IsGen) (hwe : we.IsGen) :
    ∃ we' : LB.Iso (L'.pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gw w (r ≫ pG') z jM jM' * gw we' r z jM' (fun _ => jL') =
          gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL' := by
  rw [isGen_iff] at hw hwL hwe
  choose s hs using exists_unit hM hM' hL hL' e₁ e₂ hw hwL hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₂ b₂ a₄ b₄
    obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' (r z)))
    obtain ⟨l, hl⟩ := exists_chart hL (Ψ (fG' (r z)))
    have a₄' := mem_pull.1 a₄
    have b₄' := mem_pull.1 b₄
    have c := germ_change e₁ e₂ hw hwL hwe r z i i j j' l l _ _ hi a₂ hl a₄' hi b₂ hl b₄'
    rw [← hs j _ Z r z i l hi a₂ hl a₄', ← hs j' _ Z r z i l hi b₂ hl b₄',
      ← gm_pull_g L' fG' r z _ _ a₄' b₄'] at c
    exact c
  · exact (congrArg (gw w (r ≫ pG') z jM jM' * ·) (hs jM' jL' Z r z jM jL a₁ a₂ a₃ a₄)).trans
      (mul_inv_cancel_left _ _)

end GlobalTheory.FourthSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gm_mul_eq_of_res_mul_eq {Y Z : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) :
    gm r z U₁ a * gm r z U₂ b = gm r z U₃ c * gm r z U₄ d := by
  have e := congrArg (gm r z V) H
  rwa [map_mul, map_mul, gm_res r z h₁ hz, gm_res r z h₂ hz, gm_res r z h₃ hz, gm_res r z h₄ hz] at e

theorem res_mul_eq_of_gm_mul_eq {Y : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a * gm (𝟙 Y) y U₂ b = gm (𝟙 Y) y U₃ c * gm (𝟙 Y) y U₄ d) :
    res h₁ a * res h₂ b = res h₃ c * res h₄ d := by
  apply unit_ext
  intro y hy
  rw [map_mul, map_mul, gm_res (𝟙 Y) y h₁ hy, gm_res (𝟙 Y) y h₂ hy, gm_res (𝟙 Y) y h₃ hy,
    gm_res (𝟙 Y) y h₄ hy]
  exact H y hy

theorem square_res_iff_gw {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} {h : Y' ⟶ Y}
    (hf : h ≫ f = f' ≫ B) (hp : p' ≫ F = h ≫ p)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) :
    (∀ (jM : PUnit → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jL : PUnit → L.ι),
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM') ⊓
            (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
            h ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (jM, jL) ⊓
            f' ⁻¹ᵁ (LB.div (L.pull B) L').U (jL, jL') ≤
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM'))
        (pullU p' _ (wM.s (jM, jM'))) *
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (w'.s (fun _ => jM', fun _ => jL')) =
      res (X := Y') (inf_le_left.trans inf_le_right) (pullU h _ (w.s (jM, jL))) *
      res (X := Y') inf_le_right (pullU f' _ (wL.s (jL, jL')))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL' := by
  have ef : ∀ y : Y', f (h y) = B (f' y) := fun y => congrArg (fun g => g y) hf
  have ep : ∀ y : Y', p (h y) = F (p' y) := fun y => congrArg (fun g => g y) hp.symm
  constructor
  · intro H Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have m₁ : p' (r z) ∈ (LB.div (M.pull F) M').U (fun _ => jM, jM') := ⟨mem_pull.2 h₁, h₂⟩
    have m₂ : r z ∈ (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') :=
      ⟨mem_pull.2 h₂, mem_pull.2 h₄⟩
    have m₃ : h (r z) ∈ (LB.div (M.pull p) (L.pull f)).U (fun _ => jM, fun _ => jL) :=
      ⟨mem_pull.2 (by rw [ep]; exact h₁), mem_pull.2 (by rw [ef]; exact h₃)⟩
    have m₄ : f' (r z) ∈ (LB.div (L.pull B) L').U (fun _ => jL, jL') := ⟨mem_pull.2 h₃, h₄⟩
    have e := gm_mul_eq_of_res_mul_eq (H (fun _ => jM) jM' jL' (fun _ => jL)) r z ⟨⟨⟨m₁, m₂⟩, m₃⟩, m₄⟩
    rw [gm_pull r p' z _ m₁, gm_pull r h z _ m₃, gm_pull r f' z _ m₄] at e
    exact e
  · intro H jM jM' jL' jL
    refine res_mul_eq_of_gm_mul_eq fun y hy => ?_
    have e := H Y' (𝟙 Y') y (jM PUnit.unit) jM' (jL PUnit.unit) jL' (mem_pull.1 hy.1.1.1.1) hy.1.1.1.2
      (mem_pull.1 hy.2.1) hy.2.2
    rw [gm_pull (𝟙 Y') p' y _ hy.1.1.1, gm_pull (𝟙 Y') h y _ hy.1.2, gm_pull (𝟙 Y') f' y _ hy.2]
    exact e

theorem isPullUnif_iff_stalks : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' ↔ ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wL.IsGen ∧ ∃ he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G, LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL') := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc U U'
  constructor
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, hp, ht, hw⟩ := H e
    refine ⟨h, hf, ⟨hp, fun x => ?_⟩, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).1 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
    refine ⟨h, hf, hp, fun x => ?_, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).2 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelCompat

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem thickMap_fstG {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem mono_fstG {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

noncomputable def thickMapOver {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
      (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    rw [← Over.w (fstG I (e + 1) G), ← Over.w (fstG I e G), ← thickMap_fstG I e G]
    exact (Category.assoc _ _ _).symm)

theorem thickMap_Oφ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g₀ : GtCoord I D e G)
    (g₁ : GtCoord I D (e + 1) G) (hq : thickMap R I e G ≫ g₁.pG.left = g₀.pG.left) (χ : D.X) (k : Fin 4) :
    thickMap R I e G ≫ D.Oφ g₁.pG χ k = D.Oφ g₀.pG χ k := by
  have h : thickMapOver I e G ≫ g₁.pG = g₀.pG := Over.OverMorphism.ext hq
  rw [← h]
  exact WeightPf.Oφ_comp (thickMapOver I e G) g₁.pG χ k

theorem corr_of_pmaps {X X' Y₀ Y₁ Y₀' Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ₀ : K → (Y₀ ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₀' : K → (Y₀' ⟶ X')} {φ₁' : K → (Y₁' ⟶ X')}
    {t₀ : LB.Gen (LB.LinComb L φ₀ ε)} {t₁ : LB.Gen (LB.LinComb L φ₁ ε)}
    {t₀' : LB.Gen (LB.LinComb L' φ₀' ε)} {t₁' : LB.Gen (LB.LinComb L' φ₁' ε)}
    {h₀ : Y₀' ⟶ Y₀} {h₁ : Y₁' ⟶ Y₁} {m : Y₀ ⟶ Y₁} {m' : Y₀' ⟶ Y₁'} (hm : m' ≫ h₁ = h₀ ≫ m)
    (c₀ : ∀ k, φ₀' k ≫ F = h₀ ≫ φ₀ k) (c₁ : ∀ k, φ₁' k ≫ F = h₁ ≫ φ₁ k) (c' : ∀ k, m' ≫ φ₁' k = φ₀' k)
    (H₀ : PMaps w φ₀' φ₀ ε t₀' t₀ h₀) (H₁ : PMaps w φ₁' φ₁ ε t₁' t₁ h₁)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t₁ m) t₀) :
    LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ t₁' m') t₀' := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  choose J hJ using fun χ : Y₀' ⟶ X => exists_chart hL (χ y)
  have hJ : Good L y J := hJ
  rw [val_pull hJ', Category.id_comp]
  have a₀ := H₀ _ (𝟙 _) y (fun k => J (φ₀' k ≫ F)) (fun k => J' (φ₀' k)) (fun k => hJ (φ₀' k ≫ F))
    (fun k => hJ' (φ₀' k))
  have a₁ := H₁ _ m' y (fun k => J (φ₀' k ≫ F)) (fun k => J' (φ₀' k))
    (fun k => (congrArg (fun g => F (g y) ∈ L.U (J (φ₀' k ≫ F))) (c' k)).mpr (hJ (φ₀' k ≫ F)))
    (fun k => (congrArg (fun g => g y ∈ L'.U (J' (φ₀' k))) (c' k)).mpr (hJ' (φ₀' k)))
  rw [← val_of t₀ _ y J _ (fun k => by rw [Category.id_comp, c₀]),
    ← val_of t₀' _ y J' _ (fun k => by rw [Category.id_comp]), Category.id_comp] at a₀
  rw [← val_of t₁ _ y J _ (fun k => by rw [Category.assoc, ← c₁, ← Category.assoc, c']),
    ← val_of t₁' _ y J' _ (fun k => by rw [c']), hm, ← val_pull hJ, val_corr hJ H, a₀] at a₁
  simp only [Category.id_comp, c'] at a₁
  exact (mul_left_cancel a₁).symm

end LevelCompat


open LevelCompat in
theorem gtCoord_compat_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (e : ℕ) (g₀ : GtCoord I D e G) (g₁ : GtCoord I D (e + 1) G) (g₀' : GtCoord I' D' e G') (g₁' : GtCoord I' D' (e + 1) G') (h₀ : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (h₁ : (thickObj R' I' (e + 1) G').left ⟶ (thickObj R I (e + 1) G).left), h₀ ≫ (fstG I e G).left = (fstG I' e G').left ≫ Ψ → h₁ ≫ (fstG I (e + 1) G).left = (fstG I' (e + 1) G').left ≫ Ψ → ((g₀').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ (g₀).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₀').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ D.Oφ (g₀).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₀').pG x) (D.Oφ (g₀).pG (hD.xe x)) Oinvε ((g₀').t x) ((g₀).t (hD.xe x)) h₀) → ((g₁').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ (g₁).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₁').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ D.Oφ (g₁).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₁').pG x) (D.Oφ (g₁).pG (hD.xe x)) Oinvε ((g₁').t x) ((g₁).t (hD.xe x)) h₁) → thickMap R I e G ≫ g₁.pG.left = g₀.pG.left → (∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g₁.t χ) (thickMap R I e G)) (g₀.t χ)) → thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left ∧ ∀ χ : D'.X, LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ (g₁'.t χ) (thickMap R' I' e G')) (g₀'.t χ) := by
  intro R R' _ _ _ _ φ D D' hD I I' G _ _ G' _ _ Ψ e g₀ g₁ g₀' g₁' h₀ h₁ hh₀ hh₁ ⟨p₀, H₀⟩ ⟨p₁, H₁⟩ hq ht
  have hm : thickMap R' I' e G' ≫ h₁ = h₀ ≫ thickMap R I e G := by
    have := mono_fstG I (e + 1) G
    rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hh₁, thickMap_fstG, hh₀,
      ← thickMap_fstG I' e G']
    exact (Category.assoc _ _ _).symm
  have hq' : thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left := by
    have h : (thickMapOver I' e G' ≫ g₁'.pG) ≫ hD.e.hom = g₀'.pG ≫ hD.e.hom := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · show ((thickMap R' I' e G' ≫ g₁'.pG.left) ≫ hD.e.hom.left) ≫ _ = (g₀'.pG.left ≫ hD.e.hom.left) ≫ _
        simp only [Category.assoc]
        exact (congrArg (thickMap R' I' e G' ≫ ·) p₁).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ g₁.pG.left) hm).trans ((Category.assoc _ _ _).trans
          ((congrArg (h₀ ≫ ·) hq).trans p₀.symm))))
      · exact (Over.w _).trans (Over.w _).symm
    exact congrArg (fun z => z.left) ((cancel_mono hD.e.hom).1 h)
  exact ⟨hq', fun χ => corr_of_pmaps D.P.isLB D'.P.isLB hD.w hm (H₀ χ).1 (H₁ χ).1
    (thickMap_Oφ g₀' g₁' hq' χ) (H₀ χ).2 (H₁ χ).2 (ht _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineAndGeneratedOfWideProduct
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineProduct

noncomputable def subringLift {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤)) (f : Y ⟶ X)
    (h : ∀ a, f.appTop.hom a ∈ B) : Spec (CommRingCat.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom (f.appTop.hom.codRestrict B h)) ≫ X.isoSpec.inv

noncomputable def toSpecSubring {Y : Scheme.{0}} (B : Subring Γ(Y, ⊤)) :
    Y ⟶ Spec (CommRingCat.of B) :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.subtype)

theorem toSpecSubring_subringLift {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) :
    toSpecSubring B ≫ subringLift B f h = f := by
  have e : CommRingCat.ofHom (f.appTop.hom.codRestrict B h) ≫ CommRingCat.ofHom B.subtype
      = f.appTop := by
    ext a; rfl
  simp only [toSpecSubring, subringLift, Category.assoc]
  rw [← Spec.map_comp_assoc, e, ← Scheme.toSpecΓ_naturality_assoc]
  simp [← Scheme.isoSpec_hom]

theorem subringLift_comp {Y X X' : Scheme.{0}} [IsAffine X] [IsAffine X'] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) (e : X ⟶ X') (g : Y ⟶ X') (w : f ≫ e = g)
    (h' : ∀ a, g.appTop.hom a ∈ B) :
    subringLift B f h ≫ e = subringLift B g h' := by
  subst w
  have e' : CommRingCat.ofHom ((f ≫ e).appTop.hom.codRestrict B h')
      = e.appTop ≫ CommRingCat.ofHom (f.appTop.hom.codRestrict B h) := by
    ext a; rfl
  simp only [subringLift, Category.assoc]
  rw [e', Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality]

end GlobalTheory.AffineProduct

namespace GlobalTheory
open AffineProduct

theorem isAffine_and_generated_of_wide_product : ∀ (R : CommRingCat.{0}) (j : ℕ) (Y : Scheme.{0}) (D : Fin j → Scheme.{0}) (s : Y ⟶ Spec R) (d : ∀ i, D i ⟶ Spec R) (pr : ∀ i, Y ⟶ D i) (w : ∀ i, pr i ≫ d i = s), (∀ (Z : Scheme.{0}) (z : Z ⟶ Spec R) (f : ∀ i, Z ⟶ D i), (∀ i, f i ≫ d i = z) → ∃! g : Z ⟶ Y, g ≫ s = z ∧ ∀ i, g ≫ pr i = f i) → (∀ i, IsAffine (D i)) → IsAffine Y ∧ ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) → (∀ i a, (pr i).appTop.hom a ∈ B) → B = ⊤ := by
  intro R j Y D s d pr w U hD
  have key : ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) →
      (∀ i a, (pr i).appTop.hom a ∈ B) →
      ∃ g : Spec (CommRingCat.of B) ⟶ Y, toSpecSubring B ≫ g = 𝟙 Y := by
    intro B hs hp
    obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := U _ (subringLift B s hs) (fun i => subringLift B (pr i) (hp i))
      (fun i => subringLift_comp B _ _ _ _ (w i) hs)
    refine ⟨g, (U Y s pr w).unique ⟨?_, fun i => ?_⟩ ⟨by simp, by simp⟩⟩
    · rw [Category.assoc, hg1, toSpecSubring_subringLift]
    · rw [Category.assoc, hg2, toSpecSubring_subringLift]
  constructor
  · obtain ⟨g, hg⟩ := key ⊤ (fun _ => trivial) (fun _ _ => trivial)
    rw [toSpecSubring, Category.assoc] at hg
    set g' := Spec.map (CommRingCat.ofHom (⊤ : Subring Γ(Y, ⊤)).subtype) ≫ g with hg'
    have h1 : g' ≫ Y.toSpecΓ = 𝟙 _ := by
      apply ext_of_isAffine
      have h2 : Y.toSpecΓ ≫ g' ≫ Y.toSpecΓ = Y.toSpecΓ := by
        rw [← Category.assoc, hg, Category.id_comp]
      have h3 := congrArg Scheme.Hom.appTop h2
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h3
      rw [← cancel_mono (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, h3]
      exact (Category.id_comp _).symm
    exact ⟨⟨g', hg, h1⟩⟩
  · intro B hs hp
    obtain ⟨g, hg⟩ := key B hs hp
    have h3 := congrArg Scheme.Hom.appTop hg
    rw [toSpecSubring, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Scheme.Hom.id_appTop] at h3
    rw [eq_top_iff]
    intro a _
    have h4 := congrArg (fun φ => φ.hom a) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      CommRingCat.hom_id, RingHom.id_apply] at h4
    rw [← h4]
    exact Subtype.property _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreAbelianPartIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

lemma gtCoord_i_comp_q {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    g'.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have := g.q_hom
  have := g'.i_hom
  exact splitTorus_hom_proper_trivial_local _ D'.X _ _ inferInstance

theorem unifPre_abelianPart_iso :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
      ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
        (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
        ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (e : ℕ),
          ∃ (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A),
            IsMonHom β.hom ∧ (U'.gt e).q ≫ β.hom = (U.gt e).q := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' e
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have := (U.gt e).q_affine
  have := (U'.gt e).q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ (U.gt e).q (U.gt e).i (U'.gt e).q (U'.gt e).i
    (U.gt e).q_hom (U.gt e).i_hom (U.gt e).q_flat (U.gt e).q_surj inferInstance (U.gt e).isKernel
    (U'.gt e).q_hom (U'.gt e).i_hom (U'.gt e).q_flat (U'.gt e).q_surj inferInstance
    (U'.gt e).isKernel (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)

end GlobalTheory
end

