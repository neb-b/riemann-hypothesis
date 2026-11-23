module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.PIsogExt

theorem comp_pow_pt {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp_of_isGrpPullback {Y₀ Y : Scheme.{0}} {i : Y₀ ⟶ Y} {A₀ : Over Y₀} {A : Over Y}
    [GrpObj A₀] [GrpObj A] {φ : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A i φ) (k : ℕ) (hk : 0 < k) :
    (𝟙 A₀ ^ k).left ≫ φ = φ ≫ (𝟙 A ^ k).left := by
  let φ₀ : Over.mk (A₀.hom ≫ i) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (φ₀ ^ (n + 1)).left = (𝟙 A₀ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, pow_one]; rfl
    | succ n ih =>
      rw [pow_succ φ₀, pow_succ (𝟙 A₀)]
      exact h.2 A₀ _ _ _ _ ih rfl
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add, ← key n]
  have : φ₀ ^ (n + 1) = φ₀ ≫ 𝟙 A ^ (n + 1) := by rw [comp_pow_pt, Category.comp_id]
  rw [this]; rfl

theorem isSquare_square_compatible_homs {Y₀ Y : Scheme.{0}} {A₀ A₀' : Over Y₀} {A A' : Over Y}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₀'] [IsCommMonObj A₀'] [GrpObj A] [IsCommMonObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A₀.left ⟶ A.left} {φ' : A₀'.left ⟶ A'.left}
    {φ₂ : (G2 A₀).left ⟶ (G2 A).left} {φ₂' : (G2 A₀').left ⟶ (G2 A').left}
    (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') {ψ₀ : A₀ ⟶ A₀'} {ψ : A ⟶ A'}
    (e : φ ≫ ψ.left = ψ₀.left ≫ φ') : φ₂ ≫ sq2 ψ = sq2 ψ₀ ≫ φ₂' := by
  have f1 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (fst B' B').left = (fst B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have f2 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (snd B' B').left = (snd B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  have g1 : sq2 ψ₀ ≫ (fst A₀' A₀').left = (fst A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have g2 : sq2 ψ₀ ≫ (snd A₀' A₀').left = (snd A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  apply pullback.hom_ext
  · change _ ≫ (fst A' A').left = _ ≫ (fst A' A').left
    rw [Category.assoc, Category.assoc, f1, h'.1, ← Category.assoc, h.1, Category.assoc, e, reassoc_of% g1]
  · change _ ≫ (snd A' A').left = _ ≫ (snd A' A').left
    rw [Category.assoc, Category.assoc, f2, h'.2, ← Category.assoc, h.2, Category.assoc, e, reassoc_of% g2]


open GlobalTheory.CechPic in
theorem lbIso_extend {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {Y₀ Y : Scheme.{0}} [IsLocallyNoetherian Y] (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    [IsDominant i] {σ₀ : Y₀ ⟶ Sp R} {σ : Y ⟶ Sp R} (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀)
    (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) (c : ℕ) (h₀ : LBIso (Hecke.lbPow o₀.P c) (o₀'.P.pull (sq2 ψ₀))) :
    LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ)) := by
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI := o.ab.smooth
  haveI := o.ab.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom o.A o.A
  haveI := GlobalTheory.geometricallyConnected_tensorObj_hom o.A o.A
  have hpb : IsPullback m.φ₂ (G2 o₀.A).hom (G2 o.A).hom i := GlobalTheory.SiegDesc.isPullback_of_isSquare m.cart.1 m.sq
  have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hM : (o'.P.pull (sq2 ψ)).IsLB := pull_isLB o'.isLB _
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  let s : Y ⟶ (G2 o.A).left := (η[o.A] ≫ lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left
  have hs : s ≫ (G2 o.A).hom = 𝟙 Y := Over.w _
  have hss : s ≫ sq2 ψ = (η[o'.A] ≫ lift (1 : o'.A ⟶ o'.A) (𝟙 o'.A)).left := by
    rw [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [Hom.one_def, IsMonHom.one_hom]
  have r0 : ∀ (A : Over Y) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (hP : P.IsLB),
      (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
      pull (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0 := by
    intro A _ _ P hP ht
    rw [Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff _).2 ht, map_zero]
  have eq_zero_of_pull_densePart_of_pull_section : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S]
      [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S)
      [IsOpenImmersion j] (ρ : YU ⟶ Y) (fU : YU ⟶ U), Dense (Set.range j) → IsPullback ρ fU f j →
      ∀ σ : S ⟶ Y, σ ≫ f = 𝟙 S → ∀ δ : GlobalTheory.CechPic.Pic Y, pull ρ δ = 0 →
        pull σ δ = 0 → δ = 0 := by
    intro S Y U YU _ _ f _ _ j _ ρ fU hd hpb σ hσ δ hρ hσδ
    obtain ⟨N, hN, rfl⟩ := cls_surj δ
    have hdom : IsDominant j := ⟨hd⟩
    have hgi : GeometricallyIntegral f :=
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected Y S f inferInstance inferInstance
    have hfst : pullback.fst f j = hpb.isoPullback.inv ≫ ρ := (IsPullback.isoPullback_inv_fst hpb).symm
    have h1 : cls (N.pull σ) (pull_isLB hN σ) = 0 := by rw [cls_pull hN]; exact hσδ
    have h2 : cls (N.pull (pullback.fst f j)) (pull_isLB hN _) = 0 := by
      rw [cls_pull hN, hfst, pull_comp, hρ, map_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.GenericExtend.exists_isGen_of_densePart S U j (GlobalTheory.IsNormalScheme.pred S)
      inferInstance inferInstance hdom inferInstance (Over.mk f) σ N hσ (show Smooth f from inferInstance) hgi hN
      ((cls_eq_zero_iff _).1 h1) ((cls_eq_zero_iff _).1 h2)
    exact (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  have key := eq_zero_of_pull_densePart_of_pull_section (G2 o.A).hom i m.φ₂ (G2 o₀.A).hom i.denseRange hpb s hs
    (cls _ hM - cls _ hL) ?_ ?_
  · exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 key).symm
  · have hsq := PIsogExt.isSquare_square_compatible_homs m.sq m'.sq e
    have e1 := (cls_eq_iff o₀'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have e2 := (cls_eq_iff o₀.isLB (pull_isLB o.isLB _)).2 m.pol
    have e3 : cls (Hecke.lbPow o₀.P c) (LB.isLB_linComb o₀.isLB _ _) = cls _ (pull_isLB o₀'.isLB (sq2 ψ₀)) :=
      (cls_eq_iff _ _).2 h₀
    rw [map_sub, sub_eq_zero, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hsq, pull_comp,
      ← cls_pull o'.isLB _ (pull_isLB o'.isLB _), ← e1, ← cls_pull o₀'.isLB _ (pull_isLB o₀'.isLB _), ← e3]
    refine (hcL (X := (G2 o₀.A).left) o₀.P o₀.isLB _).trans ?_
    rw [e2, cls_pull o.isLB]
  · rw [map_sub, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hss, r0 _ _ _ o'.rig₁, r0 _ _ _ o.rig₁,
      smul_zero, sub_zero]

theorem exists_isPIsog_extend : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → ∀ (j c : ℕ), (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) →
    ∀ (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R), IsOpenImmersion i → IsDominant i →
    IsLocallyNoetherian Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) →
    (∀ y : Y, IsDomain (Y.presheaf.stalk y)) →
    ∀ (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A),
    IsPIsog c o₀ o₀' ψ₀ → ∃ ψ : o.A ⟶ o'.A, IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N _ _ j c _ Y₀ Y i σ₀ σ _ _ _ hic hdom o o' o₀ o₀' m m' ψ₀ hψ₀
  have hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := fun y => ⟨hdom y, hic y⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI : IsReduced Y := by
    haveI := hdom
    exact isReduced_of_isReduced_stalk Y
  have hcpos : 0 < c := hψ₀.pos
  obtain ⟨hk, hmon₀, hlin₀, heta₀, ⟨hP₀⟩, ψ₀', hmon₀', h₁, h₂⟩ := hψ₀
  haveI := hmon₀
  haveI := hmon₀'
  have hA := GlobalTheory.isSemiAbelian_of_isAbelianScheme o.A o.ab
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme o'.A o'.ab
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion i
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o.A hA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o'.A hA'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o.A o'.A hA hA' o₀.A o₀'.A m.φ m'.φ
    m.cart m'.cart ψ₀ hmon₀
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o'.A o.A hA' hA o₀'.A o₀.A m'.φ m.φ
    m'.cart m.cart ψ₀' hmon₀'
  haveI hψm : IsMonHom ψ := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m.cart m'.cart ψ₀ ψ hψ
  haveI hψm' : IsMonHom ψ' := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m'.cart m.cart ψ₀' ψ' hψ'
  have e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := hψ.symm
  have e' : m'.φ ≫ ψ'.left = ψ₀'.left ≫ m.φ := hψ'.symm
  refine ⟨ψ, ⟨hk, hψm, fun c' => ?_, fun x => ?_, ⟨lbIso_extend hY i o o' o₀ o₀' m m' ψ₀ ψ e c hP₀⟩, ψ', hψm', ?_, ?_⟩, e⟩
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m.act c', Category.assoc, e, ← Category.assoc,
      ← Over.comp_left, hlin₀ c', Over.comp_left, Category.assoc, m'.act c', ← Category.assoc, ← e, Category.assoc]
  · refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant o'.A.hom (by rw [Over.w, Over.w]) i ?_)
    have h1 := m'.eta x
    have h2 := m.eta x
    rw [heta₀ x, Over.comp_left, Category.assoc] at h1
    rw [← h1, ← e, Over.comp_left, ← Category.assoc, h2, Category.assoc]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e, Category.assoc, e', ← Category.assoc, ← Over.comp_left, h₁,
      PIsogExt.pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m'.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e', Category.assoc, e, ← Category.assoc, ← Over.comp_left, h₂,
      PIsogExt.pow_comp_of_isGrpPullback m'.cart c hcpos]

end GlobalTheory.UPel.HT.ES.PIsogExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag
open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.AnForm.R.FinalTheorems (Snc)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal)
open GlobalTheory.CompHS (Y₀ inc₀ str₀ barComp U₀ IsVariety₀ TorFlag dense_U₀ flagStr flagOpen)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem Rel.over (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] {z : Sp K ⟶ X.YY} {p : Sp K ⟶ C.Y.X}
    (h : Rel X.F C z p) : z ≫ X.π = p ≫ C.π ≫ genι Y := by
  obtain ⟨φ, k, hz, g, -, -, y, ψ, φ₁, f, t, t', hp, -, hT⟩ := h
  rw [hT.1, hp]
  simp only [Category.assoc]

theorem barComp_iff (Z : Formalism.L2.Pj.Comp Xo c) (B : Formalism.L2.Pj.Comp Xo c → GlobalTheory.ProjVar.Var c.F) (j : ∀ i, (B i).X ⟶ gen Y)
    (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, ∀ p ∈ i.1, Y.jQ p ∈ Set.range (j i))
    (h3 : ∀ z : gen Y, ∃! i, z ∈ Set.range (j i)) (w : gen Y) :
    genι Y w ∈ barComp Y Z ↔ w ∈ Set.range (j Z) := by
  have hY : ∀ p : Xo.XF c, Y.j p = genι Y (Y.jQ p) := fun p => rfl
  have hc : ∀ p : Xo.XF c, ∃ i : Formalism.L2.Pj.Comp Xo c, p ∈ i.1 := fun p => by
    obtain ⟨u, hu, hs⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := p))
    exact ⟨⟨u, hu⟩, hs rfl⟩
  have key : ∀ p : Xo.XF c, Y.jQ p ∈ Set.range (j Z) → p ∈ Z.1 := fun p hp => by
    obtain ⟨i, hi⟩ := hc p
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    have e : i = Z := (hu' i (h2 i p hi)).trans (hu' Z hp).symm
    exact e ▸ hi
  obtain ⟨i, hi, -⟩ := h3 w
  constructor
  · intro hw
    by_contra hn
    have hiZ : i ≠ Z := fun e => hn (e ▸ hi)
    apply hw
    rw [mem_closure_iff]
    intro O hO hwO
    have := h1 i
    obtain ⟨_, hp, ⟨p, rfl⟩⟩ := Y.jQ_dense.inter_open_nonempty _
      ((hO.preimage (genι Y).continuous).inter (j i).isOpenEmbedding.isOpen_range) ⟨w, hwO, hi⟩
    refine ⟨Y.j p, hp.1, p, fun hpZ => ?_, rfl⟩
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    exact hiZ ((hu' i hp.2).trans (hu' Z (h2 Z p hpZ)).symm)
  · rintro ⟨b, rfl⟩ hw
    have := h1 Z
    rw [mem_closure_iff] at hw
    obtain ⟨_, ⟨w', hw', he⟩, ⟨p, hpZ, hp⟩⟩ := hw (genι Y '' Set.range (j Z))
      ((genι Y).isOpenEmbedding.isOpenMap _ (j Z).isOpenEmbedding.isOpen_range) ⟨_, ⟨b, rfl⟩, rfl⟩
    have e : w' = Y.jQ p := (genι Y).isOpenEmbedding.injective (he.trans (hp.symm.trans (hY p)))
    exact hpZ (key p (e ▸ hw'))

theorem genStr_eq : genStr Y = genι Y ≫ Y.s := by
  have h : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  exact ((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm

theorem smooth_iso {A B S : Scheme.{0}} (e : A ⟶ B) [IsIso e] (g : B ⟶ S) {d : ℕ} (h : SmoothOfRelativeDimension d g) :
    SmoothOfRelativeDimension d (e ≫ g) := by
  have := smoothOfRelativeDimension_comp 0 d e g
  rwa [Nat.zero_add] at this

theorem smooth_gen {d : ℕ} (h : SmoothOfRelativeDimension d Y.s) : SmoothOfRelativeDimension d (genStr Y) := by
  rw [genStr_eq]
  exact smooth_iso _ _ h

theorem isVariety_of_iso (X : FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c) (C : FlagCpt Y (RingEquiv.refl c.F))
    (e : Y₀ X Z ⟶ C.Y.X) [IsIso e] (he : e ≫ C.Y.str = str₀ X Z) (hd : C.Y.dim = GlobalTheory.FlagTan.dimFlag Dw) : IsVariety₀ X Z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hd]
    exact smooth_iso _ _ inferInstance
  · obtain ⟨N, i, hi, hs⟩ := C.Y.isProjOver
    exact ⟨N, e ≫ i, inferInstance, by rw [Category.assoc, hs, he]⟩
  · rw [← he]
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ C.Y.str) C.Y.str (𝟙 _)) inferInstance

theorem dim_eq (Dw : Datum H) : Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = GlobalTheory.FlagTan.dimFlag Dw := by
  rw [GlobalTheory.FlagDimSum.dim_add_sum_choose, GlobalTheory.FlagTan.dimFlag, Nat.choose_two_right]

theorem isVariety₀_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ T.X Z := by
  intro E _ _ _ H Dw l Xo c T Z hF
  have hsm := smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, hdim, hl⟩ := GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (_root_.GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  have hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z) :=
    barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have hX := GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X
  have hC := _root_.GlobalTheory.VarFlag.carriesTri C

  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  have hCs : C.π ≫ genStr T.Y = C.Y.str := by
    have := C.π_str
    rwa [hspid, Category.comp_id] at this
  have hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str := by rw [Category.assoc, ← genStr_eq, hCs]
  have : IsProper T.Y.s := projProper _ _ _ T.Y.proj
  have : IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s) := by rw [hps]; infer_instance
  have : IsProper (C.π ≫ genι T.Y) := IsProper.of_comp _ T.Y.s

  have hcl : IsClosed (barComp T.Y Z : Set T.Y.X) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨w, rfl⟩ : ∃ w, genι T.Y w = y :=
      ⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨i, hi, -⟩ := hcov w
    have := (hB i).1
    refine ⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩
    · rintro _ ⟨w', hw', rfl⟩ hb
      obtain ⟨i', -, hu'⟩ := hcov w'
      have e : i = Z := (hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm
      subst e
      exact hy ((hJ w).2 hi)
    · exact (genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range
  have : IsClosedImmersion (inc₀ T.X Z) := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hcl.preimage T.X.π.continuous)
  have : IsProper T.X.π := T.X.proper
  have : IsNormalScheme T.X.YY := GlobalTheory.IsNormalScheme.of_pred T.X.normal
  have : IsLocallyNoetherian T.X.YY := LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)
  have : CompactSpace T.Y.X := QuasiCompact.compactSpace_of_compactSpace T.Y.s
  have : CompactSpace T.X.YY := QuasiCompact.compactSpace_of_compactSpace T.X.π
  have : CompactSpace (Y₀ T.X Z) := QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)
  have : IsNoetherian (Y₀ T.X Z) := {}
  have hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p :=
    _root_.GlobalTheory.VarFlag.uniq_rel T.X Z hX C hC (B Z) (j Z) f hπ hl hJ
  obtain ⟨h, hh, hR⟩ := _root_.GlobalTheory.FieldPointGraph.exists_hom_of_rel (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y)
    (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w)
    (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw)
    (fun K _ z => hU K z)
    (fun K K' _ _ ι z w hw => by
      have := _root_.GlobalTheory.VarFlag.rel_baseChange T.X hX C K K' ι _ _ hw
      rwa [← Category.assoc] at this)
    (fun A _ _ _ u v huv hr => by
      have := _root_.GlobalTheory.VarFlag.rel_specialise T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv)
        (by simpa only [Category.assoc] using hr)
      simpa only [Category.assoc] using this)
  have : IsProper (inc₀ T.X Z ≫ T.X.π) := inferInstance
  have : IsProper (h ≫ C.π ≫ genι T.Y) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (C.π ≫ genι T.Y)
  have := _root_.GlobalTheory.VarFlag.locallyQuasiFinite_flag T.flag C hC Z h hR
  have hiso := _root_.GlobalTheory.VarFlag.isIso_restrict_Vo T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR
  have hVo : Nonempty (Vo C) := by
    refine ⟨⟨genericPoint C.Y.X, ?_⟩⟩
    show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ
    letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra
    have e1 := Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)
    have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)
    rw [C.y0_x] at e2
    have h1 := e1.symm.trans e2
    have h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X :=
      Scheme.fromSpecStalk_closedPoint
    rw [h2] at h1
    exact ⟨_, h1.symm⟩
  have hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C := by
    intro y hy
    show C.π (h y) ∈ Set.range T.Y.jQ
    have e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    obtain ⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j := hy
    refine ⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩
    rw [e, ← hx, Model.j, Scheme.Hom.comp_apply]
  have : Nonempty (h ⁻¹ᵁ Vo C) := by
    obtain ⟨v⟩ := hVo
    exact ⟨inv (h ∣_ Vo C) v⟩
  have : IsIntegral (h ⁻¹ᵁ Vo C).toScheme := isIntegral_of_isOpenImmersion (h ∣_ Vo C)
  have hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn
  have hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ :=
    ((dense_U₀ T.X Z).mono hpre).closure_eq
  have : IrreducibleSpace (Y₀ T.X Z) := (irreducibleSpace_def _).2 (by
    have := hirr.closure
    rw [hdense] at this
    exact this)
  have : IsIntegral (Y₀ T.X Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have := C.Y.isNormalScheme
  have : IsIso h := GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h
    (fun y => inferInstance) (Vo C) hVo
  refine isVariety_of_iso T.X Z C h ?_ (by rw [hdim, (hB Z).2.1, dim_eq])
  rw [← hps, ← Category.assoc, hh, Category.assoc]

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorGaloisInjectiveInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

open TensorProduct

def galDiff (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] :
    R' →ₗ[R] (GlobalTheory.Mum.Gal (algebraMap R R') → R') :=
  LinearMap.pi fun σ => (galAlg σ).toLinearMap - LinearMap.id

theorem galDiff_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (x : R')
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : galDiff R R' x σ = σ.1 x - x := rfl

theorem flat_tensor_invariants (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O]
    [Module.Flat R O] :
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  intro hinj hgal
  classical
  haveI : Finite (GlobalTheory.Mum.Gal (algebraMap R R')) := hgal.1
  haveI : Fintype (GlobalTheory.Mum.Gal (algebraMap R R')) := Fintype.ofFinite _
  let incl : R →ₗ[R] R' := Algebra.linearMap R R'
  have hex : Function.Exact incl (galDiff R R') := by
    intro y
    constructor
    · intro hy
      obtain ⟨r, hr⟩ := hgal.2 y (fun σ hσ => by
        have := congrFun hy ⟨σ, hσ⟩
        rw [galDiff_apply] at this
        simpa [sub_eq_zero] using this)
      exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      funext σ
      simp [incl, galDiff_apply, σ.2 r]
  have hmap : ∀ x : O, LinearMap.lTensor O incl ((TensorProduct.rid R O).symm x) =
      algebraMap O (TensorProduct R O R') x := by
    intro x
    simp [incl, Algebra.TensorProduct.algebraMap_apply]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [← hmap, ← hmap] at hab
    exact (TensorProduct.rid R O).symm.injective
      (Module.Flat.lTensor_preserves_injective_linearMap incl hinj hab)
  · intro t ht
    have hcomp : ∀ u : TensorProduct R O R', ∀ σ,
        TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')
          (LinearMap.lTensor O (galDiff R R') u) σ = galTensor O σ u - u := by
      intro u σ
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
        show x ⊗ₜ[R] galDiff R R' y σ = _
        rw [galDiff_apply, galTensor_tmul, TensorProduct.tmul_sub]
      | add u v hu hv =>
        rw [map_add (f := _), map_add (f := _), Pi.add_apply, hu, hv, map_add (f := _)]
        abel
    have h0 : LinearMap.lTensor O (galDiff R R') t = 0 := by
      apply (TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')).injective
      funext σ
      rw [hcomp, ht σ, sub_self, map_zero, Pi.zero_apply]
    obtain ⟨y, hy⟩ := (Module.Flat.lTensor_exact O hex t).1 h0
    refine ⟨TensorProduct.rid R O y, ?_⟩
    rw [← hmap, LinearEquiv.symm_apply_apply, hy]

end GlobalTheory.InvAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodge
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem frobDR_eq_zero_mem_F1prim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ c : primDR A, frobDR p k hk A c = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ k _ _ hk A _ hA c hc
  have hI : IsIntegral A.left := GlobalTheory.PrimVan.isIntegral_left hA
  have hS : Smooth (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact hA.smooth
  exact _root_.GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero p k hk A.left (A.hom ≫ 𝟙 _) (cast_left p k hk A)
    (frobMor p k hk A (cast_left p k hk A)).isMor c.1 (congrArg Subtype.val hc)

end GlobalTheory
end

