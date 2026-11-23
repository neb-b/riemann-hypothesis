module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem isLocalHom_of_test {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p)
    (hj : ∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) :
    IsLocalHom jV := by
  refine ⟨fun x hx => ?_⟩
  have h1 : ‖(jV x : PadicAlgCl p)‖ = 1 :=
    le_antisymm ((mem_OO_iff _).1 (jV x).2) (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hx)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by
    rw [hj, h, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) x)⁻¹).1 (by
    rw [map_inv₀, ← hj, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hv, mul_inv_cancel₀ h0, map_one]

end GlobalTheory.ZH.ZHPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPurePullbackSectionMulWeightGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem pure_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ α hw b φ hr
  rintro χ ⟨l, hl⟩
  by_contra hne
  refine hl ((_root_.GlobalTheory.ZH.PureWt.hasWt_iff_weight k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).1 ?_ χ hne)
  intro Z τ g z hz
  have := Φ.D.q_hom
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
    (fun _ _ _ => rfl) (fun _ => c.le l hz)
  have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
    congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
  have h₁ := hr _ g.left z J hJ l hz (e ())
  have h₂ := hr _ ((τ ≫ Φ.D.i) * g).left z J hJ l
    (GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz)
    (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
  rw [hq, hw Z τ g z J hJ, Units.val_mul, mul_left_comm, ← h₁] at h₂
  exact h₂

end GlobalTheory.ZH.UFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitOfVal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {X Y : Scheme.{0}} {K : Type} [Field K]

theorem le_inf' {g : Sp K ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ g ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem le_wchart {I : Type} [Fintype I] (L : LB X) (φ : Y ⟶ X) (j : I → L.ι) {g : Sp K ⟶ Y}
    (h : ∀ i, ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i)) : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j :=
  fun _ hz => Set.mem_iInter.2 fun i => h i hz

theorem of_le_wchart {I : Type} [Fintype I] {L : LB X} {φ : Y ⟶ X} {j : I → L.ι} {g : Sp K ⟶ Y}
    (h : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j) (i : I) : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i) :=
  fun _ hz => Set.mem_iInter.1 (h hz) i

noncomputable def vU (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) : Γ(X, U)ˣ →* Kˣ :=
  Units.map (valMap g U h).hom.toMonoidHom

theorem vU_val (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valF g U u.val = (vU g U h u).val := valR_eq g U h _

theorem val_unit_ne (g : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : valF g U u.val ≠ 0 := by
  rw [vU_val g U h]; exact Units.ne_zero _

theorem val_junk (g : Sp K ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) : valF g U f = 0 := dif_neg h

theorem val_linComb_g {I : Type} [Fintype I] [Unique I] (L : LB X) (φ : Y ⟶ X) (n : ℤ) (a b : L.ι) (g : Sp K ⟶ Y)
    (ha : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U a) (hb : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U b) :
    valF g _ ((LB.LinComb L (K := I) (fun _ => φ) (fun _ => n)).g (fun _ => a) (fun _ => b)).val =
      valF (g ≫ φ) _ (L.g a b).val ^ n := by
  have h := le_inf' (le_wchart L φ (fun _ : I => a) fun _ => ha) (le_wchart L φ (fun _ : I => b) fun _ => hb)
  have key : ∀ (W : Y.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ φ ⁻¹ᵁ (L.U a ⊓ L.U b)),
      valF g W (∏ _k : I, res e (pullU φ _ (L.g a b)) ^ n).val = valF (g ≫ φ) _ (L.g a b).val ^ n := fun W h e => by
    rw [vU_val g _ h, Fintype.prod_unique, map_zpow, Units.val_zpow_eq_zpow_val, ← vU_val]
    rw [GlobalTheory.NormGlue.val_res_pullU]
    exact congrArg (· ^ n) (valR_appLE g φ e h _)
  exact key (LB.wchart L (fun _ : I => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : I => φ) (fun _ => b)) h
    (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => a) default))
      (inf_le_right.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => b) default)))

theorem val_div_g (M L : LB X) (a b : (LB.div M L).ι) (g : Sp K ⟶ X)
    (ha : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U a) (hb : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U b) :
    valF g _ ((LB.div M L).g a b).val = valF g _ (M.g a.1 b.1).val * (valF g _ (L.g a.2 b.2).val)⁻¹ := by
  have h := le_inf' ha hb
  have key : ∀ (W A B : X.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ A) (e' : W ≤ B) (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ),
      valF g W (res e u * (res e' v)⁻¹).val = valF g A u.val * (valF g B v.val)⁻¹ := fun W A B h e e' u v => by
    rw [vU_val g _ h, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ← vU_val, ← vU_val]
    exact congrArg₂ (fun x y => x * y⁻¹) (valR_res g e h _) (valR_res g e' h _)
  exact key _ _ _ h _ _ _ _

theorem val_sec {H : LB X} (s : LB.Sec H) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.f j) = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.f k) := by
  have h := le_inf' hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem val_gen {H : LB X} {s : LB.Gen H} (hs : s.IsGen) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.s j).val = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.s k).val :=
  val_sec ⟨fun i => (s.s i).val, fun i j => congrArg Units.val (hs i j)⟩ x hj hk

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp K ⟶ X) {k : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valF x _ (L.g k k).val = 1 :=
  (valR_res x _ h _).symm.trans ((congrArg (fun u : Γ(X, L.U k)ˣ => valR x _ u.val) (hL.g_self k)).trans
    (valR_one x _ h))

theorem isUnit_of_val {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (g : Sp K ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valF g U f ≠ 0) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (X.mem_basicOpen f x hx).1 ?_
  let g : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => Scheme.fromSpecResidueField_apply _ _
  have h1 : ⊤ ≤ g ⁻¹ᵁ U := fun w _ => show g w ∈ U by rw [hg]; exact hx
  have := (le_preimage_basicOpen_iff g h1 f).2 (h _ g h1).isUnit (x := IsLocalRing.closedPoint _) trivial
  exact Set.mem_of_eq_of_mem (hg _).symm this

def Reg (y : Y) (F : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K) : Prop :=
  ∃ (V : Y.Opens) (f : Γ(Y, V)), y ∈ V ∧ ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → valF g V f = F K g

section
variable {y : Y} {F F' : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}

theorem Reg.val (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ U) : Reg y fun _ _ g => valF (g ≫ m) U s :=
  ⟨m ⁻¹ᵁ U, (m.app U).hom s, h, fun _ _ g _ => (valR_comp g m U s).symm⟩

theorem Reg.inv (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ X.basicOpen s) :
    Reg y fun _ _ g => (valF (g ≫ m) U s)⁻¹ := by
  obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  refine ⟨m ⁻¹ᵁ X.basicOpen s, (m.app _).hom (u⁻¹).val, h, fun _ _ g hg => (valR_comp g m _ _).symm.trans ?_⟩
  replace hg : ⊤ ≤ (g ≫ m) ⁻¹ᵁ X.basicOpen s := hg
  refine (vU_val (g ≫ m) _ hg _).trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val, ← vU_val, hu]
  exact congrArg (·⁻¹) (valR_res _ _ hg _)

theorem Reg.mul (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g * F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f * resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_mul g _ hg _ _).trans (congrArg₂ (· * ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.add (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g + F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f + resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_add g _ hg _ _).trans (congrArg₂ (· + ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.pow (h : Reg y F) (n : ℕ) : Reg y fun K _ g => F K g ^ n := by
  obtain ⟨V, f, hy, hf⟩ := h
  exact ⟨V, f ^ n, hy, fun K _ g hg => (valR_pow g _ hg _ _).trans (congrArg (· ^ n) (hf K g hg))⟩

theorem Reg.sum {I : Type} (s : Finset I) {F : I → ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}
    (h : ∀ i, Reg y (F i)) : Reg y fun K _ g => ∑ i ∈ s, F i K g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, 0, trivial, fun K _ g hg => valR_zero g _ hg⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

end

theorem exists_glue [IsIntegral Y] (V : Y.Opens) (R : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K → Prop)
    {F : Type} [Field F] (ξ : Sp F ⟶ Y) (hξ : ∀ w, ξ w = genericPoint Y)
    (hu : ⊤ ≤ ξ ⁻¹ᵁ V → ∀ v v', R F ξ v → R F ξ v' → v = v')
    (hl : ∀ y ∈ V, ∃ (W : Y.Opens) (f : Γ(Y, W)), y ∈ W ∧
      ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ W → ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g W f)) :
    ∃ f : Γ(Y, V), ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g V f) := by
  choose W f hy hf using fun y : V => hl y.1 y.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun y : V => V ⊓ W y) V (fun y => homOfLE inf_le_left)
    (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hy _⟩) (fun y => resG Y inf_le_right (f y))
    (fun a b => eq_of_valF_generic ξ hξ (U := (V ⊓ W a) ⊓ (V ⊓ W b)) fun h => by
      have h1 := le_preimage_mono ξ inf_le_left h
      have h2 := le_preimage_mono ξ inf_le_right h
      have h3 := le_preimage_mono ξ inf_le_left h1
      exact ((valR_res ξ inf_le_left h _).trans (valR_res ξ _ h1 _)).trans ((hu h3 _ _
        (hf a F ξ (le_preimage_mono ξ inf_le_right h1) h3) (hf b F ξ (le_preimage_mono ξ inf_le_right h2) h3)).trans
        ((valR_res ξ inf_le_right h _).trans (valR_res ξ _ h2 _)).symm))
  refine ⟨s, fun K _ g hg => ?_⟩
  let y : V := ⟨g (IsLocalRing.closedPoint K), hg trivial⟩
  have h1 : ⊤ ≤ g ⁻¹ᵁ W y := (le_preimage_iff g _).2 (hy y)
  have h2 := le_inf' hg h1
  have e : valF g V s = valF g (W y) (f y) := (valR_res g inf_le_left h2 s).symm.trans
    ((congrArg (valR g _) (hs y)).trans (valR_res g _ h2 _))
  exact e ▸ hf y K g h1 hg

theorem exists_generic (Y : Scheme.{0}) [IsIntegral Y] :
    ∃ (F : Type) (_ : Field F) (ξ : Sp F ⟶ Y), ∀ w, ξ w = genericPoint Y :=
  ⟨Y.residueField (genericPoint Y), inferInstance, Y.fromSpecResidueField _,
    fun _ => Scheme.fromSpecResidueField_apply _ _⟩

end GlobalTheory.ZH.PowSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestCrit

theorem exists_ne_zero_iff {O K k J : Type} [CommRing O] [Field K] [Algebra O K] [Field k] [Fintype J]
    [DecidableEq J] (hinj : Function.Injective (algebraMap O K)) (φ : O →+* k) (n A : Matrix J J O)
    (b : Matrix J J K) (hn : n.map (algebraMap O K) * b = 1) (I : Set J)
    (hs : Submodule.span O (b '' I) = Submodule.span O (Set.range fun i j => algebraMap O K (A i j)))
    (w : J → k) :
    (∃ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j ≠ 0) ↔ ∃ i, i ∈ I ∧ w i ≠ 0 := by
  have hn' : b * n.map (algebraMap O K) = 1 := mul_eq_one_comm.1 hn
  have hb : ∀ i i', ∑ j, b i j * algebraMap O K (n j i') = (1 : Matrix J J K) i i' := fun i i' => by
    rw [← hn', Matrix.mul_apply]
    rfl
  have hsum : ∀ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j = ∑ i', φ ((A * n) i i') * w i' := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    exact Finset.sum_comm
  have hA : ∀ i i', algebraMap O K ((A * n) i i') = ∑ j, algebraMap O K (A i j) * algebraMap O K (n j i') :=
    fun i i' => by simp only [Matrix.mul_apply, map_sum, map_mul]
  simp only [hsum]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    refine ⟨i', ?_, right_ne_zero_of_mul hi'⟩
    by_contra hI
    have h0 : ∀ a ∈ Submodule.span O (b '' I), ∑ j, a j * algebraMap O K (n j i') = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨i₀, hi₀, rfl⟩ := h
        rw [hb, Matrix.one_apply_ne]
        rintro rfl
        exact hI hi₀
      | zero => simp
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, ha', add_zero]
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_mul_assoc]
        rw [← Finset.smul_sum, ha, smul_zero]
    have h1 := h0 (fun j => algebraMap O K (A i j)) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [← hA, map_eq_zero_iff _ hinj] at h1
    exact hi' (by rw [h1, map_zero, zero_mul])
  · rintro ⟨i, hI, hw⟩
    by_contra hz
    push_neg at hz
    have hm : b i ∈ Submodule.span O (Set.range fun i j => algebraMap O K (A i j)) :=
      hs ▸ Submodule.subset_span ⟨i, hI, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
    have h1 : ∀ i', (1 : Matrix J J O) i i' = ∑ a, c a * (A * n) a i' := fun i' => hinj (by
      have : algebraMap O K ((1 : Matrix J J O) i i') = (1 : Matrix J J K) i i' := by
        simp only [Matrix.one_apply, apply_ite (algebraMap O K), map_one, map_zero]
      have hc' : ∀ j, b i j = ∑ a, algebraMap O K (c a) * algebraMap O K (A a j) := fun j => by
        rw [← hc]
        simp only [Finset.sum_apply, Pi.smul_apply]
        simp only [Algebra.smul_def]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, ← hb, map_sum]
      simp only [map_mul, hA, hc', Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
      exact Finset.sum_comm)
    apply hw
    calc w i = ∑ i', φ ((1 : Matrix J J O) i i') * w i' := by
          simp [Matrix.one_apply, apply_ite φ]
      _ = ∑ a, φ (c a) * ∑ i', φ ((A * n) a i') * w i' := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
          exact Finset.sum_comm
      _ = 0 := by simp only [hz, mul_zero, Finset.sum_const_zero]

theorem le_preimage_G_iff_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (x : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme) (w : S.J → kb p), x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) x ((tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w) → (⊤ ≤ (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G ↔ ∃ i, t.cls i = 0 ∧ w i ≠ 0) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y y₀ t c tm _ x w hx hw
  have := hA.ft
  obtain ⟨ψ, hψ⟩ : ∃ ψ : o →+* OO p, y ≫ M.s = spMap ψ :=
    ⟨(Spec.preimage (y ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hg : (gPt p ≫ y) ≫ M.s = spMap ((OO p).subtype.comp ψ) := by
    rw [Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hy₀ : ∀ a : o, y₀ (algebraMap o S.R a) = (ψ a : PadicAlgCl p) := fun a =>
    (c.at_ _).trans (RatModel.val_algebraMap hg a)
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    refine (congrArg (gPt p ≫ ·) c.fac.symm).trans ?_
    beta_reduce
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom (algebraMap t.u.V (FractionRing t.u.V)))
      (CommRingCat.ofHom (algebraMap (FractionRing t.u.V) (PadicAlgCl p)))
  have hU : Set.range (gPt p ≫ y) ⊆ U₀ := by
    rw [hgy]
    rintro _ ⟨a, rfl⟩
    exact ((spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) a).2
  have hcen : M.Cen U₀ (y (cPt p)) y := ⟨rfl, hU⟩
  have hcl := GlobalTheory.ZH.isClosed_centre o Ω M U₀ _ p y hcen
  obtain ⟨hker, -, hspan⟩ := _root_.GlobalTheory.ZH.span_rows_class_zero o Ω S ρ p y₀ t fun a => by
    rw [hy₀]
    exact (mem_OO_iff _).1 (ψ a).2
  have hT : S.TT M (y (cPt p)) = S.perp t.l.yy.ker := by
    rw [ThetaSys.TT, hB.atTest _ p y y₀ t.τ hcen c.at_, hker]
  have hW : ⊤ ≤ y ⁻¹ᵁ Q.W tm.l := (CrdCalc.top_le_iff y _).2 tm.mem
  have hrange : Set.range ((x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom) = {y (cPt p)} := by
    rw [Category.assoc, hx, RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    congr 1
    exact congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  have hs : (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom ≫ M.s =
      spMap ((IsLocalRing.residue (OO p)).comp ψ) := by
    rw [← Category.assoc, Category.assoc x, hx, Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hcrd := Q.rel tm.l _ x _ hw
  rw [OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ _ _ _ _ hrange (Or.inl hcl) hs hcrd, hT, hx,
    Matrix.mulVec_mulVec]
  set C : Matrix S.J S.J (OO p) := (Q.c tm.l).map (valR y (Q.W tm.l)) with hC
  have hn : (Q.c tm.l).map (valR (rPt p ≫ y) (Q.W tm.l)) *
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)) =
      (C * tm.m.map t.u.j).map (IsLocalRing.residue (OO p)) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    exact (CrdCalc.valR_spMap _ y _ hW).2 _
  rw [hn]
  obtain ⟨hWg, hvg⟩ := CrdCalc.valR_spMap (OO p).subtype y _ hW
  have hWg' : Set.range (gPt p ≫ y) ⊆ Q.W tm.l := (top_le_preimage_iff _ _).1 hWg
  set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _) with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ _
  have hξW : ξ ∈ Q.W tm.l := hWg' ⟨_, rfl⟩
  have hξU : ξ ∈ U₀ := hU ⟨_, rfl⟩
  have hBm : ∀ i j, Q.B tm.l i j ∈ M.O ξ := fun i => by
    have h1 : Q.B tm.l i ∈ EE.E ξ := by
      rw [Q.basis _ _ hξW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hξU] at h1
    exact (RatModel.Lat.mem_const_iff M).1 h1
  have hinv : C.map (algebraMap (OO p) (PadicAlgCl p)) * (Q.B tm.l).map (M.val (gPt p ≫ y)) = 1 := by
    let c' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, RatModel.valF_mem_O hξW (Q.c tm.l i j)⟩
    let B' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, hBm i j⟩
    have h1 : c' * B' = 1 := by
      apply Matrix.map_injective (f := (M.O ξ).val.toRingHom) Subtype.val_injective
      beta_reduce
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact Q.c_inv tm.l
    have h2 := congrArg (fun N => N.map (RatModel.valHom _ _ hr)) h1
    beta_reduce at h2
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [← h2]
    congr 1
    ext i j
    exact ((RatModel.val_valF hWg' _).trans (hvg _)).symm
  refine exists_ne_zero_iff Subtype.val_injective (IsLocalRing.residue (OO p)) _
    (fun i j => ψ (S.proj (S.perp t.l.yy.ker) 0 j i)) (t.b.map (algebraMap _ (PadicAlgCl p))) ?_
    {i | t.cls i = 0} ?_ w
  · rw [Matrix.map_mul, Matrix.mul_assoc, ← hinv, tm.m_eq]
    rfl
  · rw [hspan]
    simp only [hy₀]
    rfl

end GlobalTheory.ZH.TestCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarEqExpansionCoefRatioStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_eq_expansionCoef_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  first | exact @GlobalTheory.psiScal_eq_ratio | exact GlobalTheory.psiScal_eq_ratio | (intros; apply GlobalTheory.psiScal_eq_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultiple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.resG_eq_of_thMul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N N' σ σ' c hσ hσ' j O h h'
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hO.ne
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N : Q.G.left.Opens) := fun y hy => (h (hm' hy)).1
  have hV' : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N' : Q.G.left.Opens) := fun y hy => (h' (hm' hy)).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (h (hm' hy)).2 0
  have e := (hσ K β g r jP jL h1 h2 h3 hL hV).symm.trans (hσ' K β g r jP jL h1 h2 h3 hL hV')
  refine (valR_res _ h hm _).trans (Eq.trans ?_ (valR_res _ h' hm _).symm)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end

